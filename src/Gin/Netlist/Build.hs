-- | Normal form ("Gin.Core.Normal") to netlist ("Gin.Netlist.Types").
--
-- 'buildNetlist' emits at most one declaration per normal-form bind, in
-- bind order, and establishes every invariant listed in
-- "Gin.Netlist.Types":
--
-- [Names] The top name and the port names are a public interface and are
--   never renamed: they must already be legal identifiers
--   ('isLegalIdent') and pairwise distinct, case-insensitively (VHDL),
--   also from the clock @clk@ and the reset @rst@ that every module gets
--   (see @docs/semantics.md@). Bind names are then made legal and fresh
--   with 'sanitize', in bind order.
--
-- [Folding] A shift by at least the operand width becomes the zero
--   constant, and an extract of a literal becomes a literal. Declarations
--   that folding leaves unread are then dropped, repeatedly, until every
--   declared net is read by a declaration or an output.
--
-- [Header] 'modHeader' puts provenance and the certificate (theorem name,
--   statement and axioms) in front of every reviewer of the generated
--   files. Every line starts with a fixed tag, so text from the IR can
--   never begin a comment and be read as a tool directive (such as
--   @verilator lint_off@), and every character in the Unicode categories
--   Cc, Cf, Zl, Zp, Cs, Co and Cn becomes @?@, so it can neither break
--   out of its line nor hide or reorder text (bidirectional overrides).
--   Lines may still contain comment delimiters such as @*/@: emit each one
--   as a line comment.
module Gin.Netlist.Build
  ( buildNetlist
  , sanitize
  ) where

import Control.Monad (foldM, when)
import Data.Char
  ( GeneralCategory (..)
  , generalCategory
  , isAsciiLower
  , isAsciiUpper
  , isDigit
  , toLower
  )
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Normal (Atom (..), NBind (..), NModule (..), NOutput (..), NRhs (..))
import Gin.Core.Syntax
  ( Certificate (..)
  , Name (..)
  , PrimOp (..)
  , Ty (..)
  , Value (..)
  , isCombinational
  , isScalar
  , primArity
  , primName
  , validValue
  , valueTy
  )
import Gin.Error (GinError, Stage (..), ginError, withContext)
import Gin.Limits (maxNormalBinds)
import Gin.Netlist.Types
  ( BinOp (..)
  , Decl (..)
  , HExpr (..)
  , HLit (..)
  , HwType (..)
  , Ident (..)
  , Module (..)
  , Net (..)
  , Operand (..)
  , Output (..)
  , UnOp (..)
  , declNet
  , isLegalIdent
  , reservedWords
  )
import Numeric.Natural (Natural)

-- | Precondition: 'Gin.Normalize.checkNormal' succeeded. Errors use
-- 'StNetlist': an illegal or colliding top or port name, and any breach
-- of the precondition the builder trips over (an unknown variable, a
-- non-scalar type, an invalid literal, an unsaturated or
-- non-combinational primitive) instead of crashing.
buildNetlist :: NModule -> Either GinError Module
buildNetlist m = do
  when (length (nmBinds m) > maxNormalBinds) . Left . netlistError $
    "more than " <> tshow maxNormalBinds <> " binds"
  taken <- reserveInterface m
  inputs <- traverse lowerInput (nmInputs m)
  env <- nameBinds taken (nmInputs m) (nmBinds m)
  decls <- traverse (lowerBind env) (nmBinds m)
  outputs <- traverse (lowerOutput env) (nmOutputs m)
  pure
    Module
      { modName = Ident (nmName m)
      , modHeader = certificateHeader m
      , modClock = clockName
      , modReset = resetName
      , modInputs = inputs
      , modOutputs = outputs
      , modDecls = dropUnread outputs decls
      }

clockName :: Ident
clockName = Ident "clk"

resetName :: Ident
resetName = Ident "rst"

----------------------------------------------------------------------
-- Names

-- | Reserve the top name, the clock, the reset, the input ports and the
-- output ports, in that order. Each must be a legal identifier distinct
-- from every name reserved before it. Returns the reserved names,
-- lowercased.
reserveInterface :: NModule -> Either GinError (Set Text)
reserveInterface m = Map.keysSet <$> foldM reserve Map.empty interface
  where
    interface =
      [ ("top name", nmName m)
      , ("clock port", unIdent clockName)
      , ("reset port", unIdent resetName)
      ]
        <> [("input port", unName n) | (n, _) <- nmInputs m]
        <> [("output port", noName o) | o <- nmOutputs m]
    -- Lowercased name -> what holds it, for the error message.
    reserve :: Map Text Text -> (Text, Text) -> Either GinError (Map Text Text)
    reserve held (what, name)
      | not (isLegalIdent name) =
          Left . netlistError $
            what <> " " <> quote name <> " is not a legal identifier: " <> legalRule
      | Just holder <- Map.lookup (Text.toLower name) held =
          Left . netlistError $ what <> " " <> quote name <> " collides with the " <> holder
      | otherwise = Right (Map.insert (Text.toLower name) (what <> " " <> quote name) held)
    legalRule =
      "it must match [a-z][a-z0-9_]*, have at most 64 characters, contain no \"__\", \
      \not end in \"_\", not start with \"gin_\" and not be a reserved word of \
      \Verilog, SystemVerilog, VHDL or the supported tools"

-- | What each normal-form variable is called in the netlist, and its type.
type Env = Map Name (Ident, Ty)

-- | Inputs keep their (port) names; binds are named with 'sanitize', in
-- order, against the reserved names and the binds named before them.
nameBinds :: Set Text -> [(Name, Ty)] -> [NBind] -> Either GinError Env
nameBinds reserved inputs binds = snd <$> foldM step (Taken reserved Map.empty, inputEnv) binds
  where
    inputEnv = Map.fromList [(n, (Ident (unName n), t)) | (n, t) <- inputs]
    step (taken, env) b
      | nbName b `Map.member` env =
          Left . netlistError $
            "bind name " <> quote (unName (nbName b)) <> " is already an input or a bind"
      | otherwise =
          let (i, taken') = claimName taken (unName (nbName b))
           in taken' `seq` Right (taken', Map.insert (nbName b) (Ident i, nbTy b) env)

-- | @sanitize taken name@ turns @name@ into a legal identifier
-- ('isLegalIdent') that differs, case-insensitively, from every name in
-- @taken@:
--
--   1. lowercase ASCII letters, keep @[a-z0-9]@ and map every other
--      character to @_@;
--   2. collapse runs of @_@ to one and strip leading and trailing @_@;
--   3. use @n@ if nothing is left; prepend @n_@ if the result does not
--      start with a letter, is a reserved word ('reservedWords'), is @gin@
--      or starts with @gin_@;
--   4. truncate to 56 characters and strip a trailing @_@;
--   5. if the result is taken, append @_k@ for the least @k >= 1@ that
--      gives a free, legal identifier.
--
-- Steps 1–4 make a legal identifier of at most 56 characters, so the
-- suffix of step 5 fits within the 64-character limit while fewer than
-- 9999999 names are taken.
sanitize :: Set Text -> Text -> Text
sanitize taken = fst . claimName (Taken (Set.map Text.toLower taken) Map.empty)

-- | The names taken so far, lowercased, and for each base name (steps 1–4
-- of 'sanitize') whose suffix search has run, the suffix to resume it at.
data Taken = Taken !(Set Text) !(Map Text Int)

-- | 'sanitize' a name and take the result.
--
-- Names are only ever added, so every suffix a search for a base name
-- has passed, or returned, stays unusable, and the next search for that
-- base resumes after it with the same result as one starting at 1.
-- Naming n binds that share a base therefore costs O(n) lookups, not
-- O(n^2).
claimName :: Taken -> Text -> (Text, Taken)
claimName (Taken names resume) name
  | base `Set.notMember` names = (base, Taken (Set.insert base names) resume)
  | otherwise =
      let k = search (Map.findWithDefault 1 base resume)
          candidate = suffixed k
       in (candidate, Taken (Set.insert candidate names) (Map.insert base (k + 1) resume))
  where
    base = baseName name
    suffixed k = base <> "_" <> tshow k
    search :: Int -> Int
    search k
      | suffixed k `Set.notMember` names && isLegalIdent (suffixed k) = k
      | otherwise = search (k + 1)

-- | Steps 1–4 of 'sanitize'.
baseName :: Text -> Text
baseName =
  Text.dropWhileEnd (== '_')
    . Text.take 56
    . avoidReserved
    . Text.intercalate "_"
    . filter (not . Text.null)
    . Text.splitOn "_"
    . Text.map legalChar
  where
    legalChar c
      | isAsciiUpper c = toLower c
      | isAsciiLower c || isDigit c = c
      | otherwise = '_'
    avoidReserved t
      | needsPrefix nonEmpty = "n_" <> nonEmpty
      | otherwise = nonEmpty
      where
        nonEmpty = if Text.null t then "n" else t
    needsPrefix t =
      not (startsWithLetter t)
        || t `Set.member` reservedWords
        || t == "gin"
        || "gin_" `Text.isPrefixOf` t
    startsWithLetter = maybe False (isAsciiLower . fst) . Text.uncons

----------------------------------------------------------------------
-- Declarations

lowerInput :: (Name, Ty) -> Either GinError Net
lowerInput (n, t) =
  withContext ("in input port " <> quote (unName n)) $
    Net (Ident (unName n)) <$> hwType t

lowerOutput :: Env -> NOutput -> Either GinError Output
lowerOutput env o =
  withContext ("in output port " <> quote (noName o)) $
    Output <$> (Net (Ident (noName o)) <$> hwType (noTy o)) <*> operand env (noAtom o)

lowerBind :: Env -> NBind -> Either GinError Decl
lowerBind env b = withContext ("in bind " <> quote (unName (nbName b))) $ do
  net <- Net <$> (fst <$> resolve env (nbName b)) <*> hwType (nbTy b)
  case nbRhs b of
    NPrim op args -> DAssign net <$> lowerPrim env op args
    NMux c t e -> DAssign net <$> (HMux <$> operand env c <*> operand env t <*> operand env e)
    NReg v a -> DReg net <$> literal v <*> operand env a
    NAtom a -> DAssign net . HOperand <$> operand env a

-- | Lower a saturated combinational primitive, folding shifts by at least
-- the operand width (to zero) and extracts of literals (to literals).
lowerPrim :: Env -> PrimOp -> [Atom] -> Either GinError HExpr
lowerPrim env op args = case (op, args) of
  (BoolAnd, [a, b]) -> bin BAnd a b
  (BoolOr, [a, b]) -> bin BOr a b
  (BoolXor, [a, b]) -> bin BXor a b
  (BoolNot, [a]) -> un UNot a
  (BoolEq, [a, b]) -> bin BEq a b
  (BvAdd, [a, b]) -> bin BAdd a b
  (BvSub, [a, b]) -> bin BSub a b
  (BvMul, [a, b]) -> bin BMul a b
  (BvNeg, [a]) -> un UNeg a
  (BvAnd, [a, b]) -> bin BAnd a b
  (BvOr, [a, b]) -> bin BOr a b
  (BvXor, [a, b]) -> bin BXor a b
  (BvNot, [a]) -> un UNot a
  (BvShl k, [a]) -> shift HShl k a
  (BvLshr k, [a]) -> shift HLshr k a
  (BvEq, [a, b]) -> bin BEq a b
  (BvUlt, [a, b]) -> bin BUlt a b
  (BvUle, [a, b]) -> bin BUle a b
  (BvConcat, [a, b]) -> HConcat <$> opnd a <*> opnd b
  (BvExtract hi lo, [a]) -> extract hi lo a
  (BvZext w, [a]) -> HZext w <$> opnd a
  (BvOfBool, [a]) -> HBitToVec <$> opnd a
  _
    | isCombinational op ->
        Left . netlistError $
          primName op <> " takes " <> operands (primArity op) <> ", got " <> tshow (length args)
    | otherwise -> Left (netlistError (primName op <> " is not a combinational primitive"))
  where
    opnd = operand env
    operands = \case
      1 -> "1 operand"
      k -> tshow k <> " operands"
    bin o a b = HBin o <$> opnd a <*> opnd b
    un o a = HUn o <$> opnd a
    shift mk k a = do
      w <- vectorWidth env a
      if k < w then mk k <$> opnd a else Right (HOperand (OConst (HLitVec w 0)))
    extract hi lo a = do
      w <- vectorWidth env a
      when (hi < lo || hi >= w) . Left . netlistError $
        "bv.extract " <> tshow hi <> " " <> tshow lo <> " of a " <> tshow w <> "-bit operand"
      let width = hi - lo + 1
      case a of
        ALit (VBV _ v) ->
          Right (HOperand (OConst (HLitVec width ((v `div` 2 ^ lo) `mod` 2 ^ width))))
        _ -> HSlice hi lo <$> opnd a

operand :: Env -> Atom -> Either GinError Operand
operand env = \case
  AVar n -> ORef . fst <$> resolve env n
  ALit v -> OConst <$> literal v

-- | The width of a bit-vector atom.
vectorWidth :: Env -> Atom -> Either GinError Natural
vectorWidth env a =
  atomTy >>= \case
    TBitVec w -> Right w
    t -> Left (netlistError ("expected a bit-vector operand, got " <> tshow t))
  where
    atomTy = case a of
      AVar n -> snd <$> resolve env n
      ALit v -> Right (valueTy v)

resolve :: Env -> Name -> Either GinError (Ident, Ty)
resolve env n =
  maybe (Left (netlistError ("unknown variable " <> quote (unName n)))) Right (Map.lookup n env)

literal :: Value -> Either GinError HLit
literal v
  | not (validValue v) = Left (netlistError ("invalid literal " <> tshow v))
  | otherwise = case v of
      VBool b -> Right (HLitBit b)
      VBV w x -> Right (HLitVec w x)
      VTuple _ -> Left (netlistError ("non-scalar literal " <> tshow v))

hwType :: Ty -> Either GinError HwType
hwType t = case t of
  TBool -> Right HBit
  TBitVec w | isScalar t -> Right (HVec w)
  _ -> Left (netlistError ("non-scalar type " <> tshow t))

-- | Drop every declaration whose net neither an output nor a remaining
-- declaration reads, until there is none. Only folding leaves nets unread
-- (normal form has no dead binds). Nets that only read each other, such
-- as a register loop only a folded shift observed, are all still read and
-- are kept.
dropUnread :: [Output] -> [Decl] -> [Decl]
dropUnread outputs decls = filter ((`Set.notMember` dead) . netName . declNet) decls
  where
    byName = Map.fromList [(netName (declNet d), d) | d <- decls]
    -- How often each net is read, by outputs and by declarations.
    reads0 =
      Map.fromListWith
        (+)
        [(i, 1 :: Int) | i <- concatMap (refs . outDriver) outputs <> concatMap declReads decls]
    unread counts i = Map.findWithDefault 0 i counts == 0
    dead = sweep reads0 Set.empty (filter (unread reads0) (Map.keys byName))
    sweep counts done = \case
      [] -> done
      i : rest
        | i `Set.member` done -> sweep counts done rest
        | otherwise ->
            let rs = maybe [] declReads (Map.lookup i byName)
                counts' = foldl' (flip (Map.adjust (subtract 1))) counts rs
                next = filter (\r -> Map.member r byName && unread counts' r) rs
             in sweep counts' (Set.insert i done) (next <> rest)

declReads :: Decl -> [Ident]
declReads = \case
  DAssign _ e -> concatMap refs (exprOperands e)
  DReg _ _ o -> refs o

exprOperands :: HExpr -> [Operand]
exprOperands = \case
  HOperand o -> [o]
  HUn _ o -> [o]
  HBin _ a b -> [a, b]
  HMux c t e -> [c, t, e]
  HShl _ o -> [o]
  HLshr _ o -> [o]
  HSlice _ _ o -> [o]
  HConcat a b -> [a, b]
  HZext _ o -> [o]
  HBitToVec o -> [o]

refs :: Operand -> [Ident]
refs = \case
  ORef i -> [i]
  OConst _ -> []

----------------------------------------------------------------------
-- Header

-- | In order: provenance, the top name, the theorem, one line per line of
-- the statement, the axioms of the proof and of the implementation.
certificateHeader :: NModule -> [Text]
certificateHeader m =
  fmap
    neutralise
    ( [ "generated by gin " <> ginVersion
      , "top: " <> nmName m
      , "theorem: " <> certTheorem cert
      ]
        <> fmap ("statement: " <>) (Text.lines (certStatement cert))
        <> [ "axioms: " <> Text.intercalate ", " (certAxioms cert)
           , "impl axioms: " <> Text.intercalate ", " (certImplAxioms cert)
           ]
    )
  where
    cert = nmCertificate m

-- | The package version, as in @gin.cabal@.
ginVersion :: Text
ginVersion = "0.1.0.0"

-- | Replace every character that could end the comment line, or hide or
-- reorder its text, by @?@.
neutralise :: Text -> Text
neutralise = Text.map (\c -> if unsafe (generalCategory c) then '?' else c)
  where
    unsafe = \case
      Control -> True
      Format -> True
      LineSeparator -> True
      ParagraphSeparator -> True
      Surrogate -> True
      PrivateUse -> True
      NotAssigned -> True
      _ -> False

----------------------------------------------------------------------
-- Helpers

netlistError :: Text -> GinError
netlistError = ginError StNetlist

-- | Quote and escape a name from the IR for an error message.
quote :: Text -> Text
quote = tshow

tshow :: (Show a) => a -> Text
tshow = Text.pack . show
