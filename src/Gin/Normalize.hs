-- | Normalization: core IR to normal form ("Gin.Core.Normal").
module Gin.Normalize
  ( normalize
  , checkNormal
  ) where

import Control.Monad (foldM, foldM_, unless, when)
import Data.Foldable (for_)
import Data.List (genericLength)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Normal (Atom (..), NBind (..), NModule (..), NOutput (..), NRhs (..))
import Gin.Core.Syntax
  ( Name (..)
  , Program
  , Ty (..)
  , isCombinational
  , isScalar
  , primArity
  , primName
  , validValue
  , valueTy
  )
import Gin.Error (GinError, Stage (..), ginError, withContext)
import Gin.Limits (maxNormalBinds)
import Gin.Normalize.Internal (buildModule, primResultTy)

-- | Precondition: 'Gin.Core.Check.checkProgram' succeeded. Inlines
-- globals, beta-reduces, erases signals, lowers @sig.mealy@ to registers,
-- flattens tuples and A-normalizes. Errors use 'StNormalize' (e.g. a
-- lambda that cannot be eliminated, or a combinational loop).
--
-- Also an 'StNormalize' error: inlining that emits more than
-- 'Gin.Limits.maxNormalBinds' binds (counted as they are emitted, so the
-- error comes before the term is built), evaluation that exceeds
-- 'Gin.Normalize.Internal.maxEvalSteps' steps, a recursive @let@ that
-- binds a function, and an @if@ whose branches carry functions. The
-- result is validated with 'checkNormal' before it is returned.
normalize :: Program -> Either GinError NModule
normalize prog = do
  m <- buildModule prog
  withContext "while validating the normal form" (checkNormal m)
  pure m

-- | Validate every invariant listed in "Gin.Core.Normal".
checkNormal :: NModule -> Either GinError ()
checkNormal m = do
  let inputs = nmInputs m
      binds = nmBinds m
      outputs = nmOutputs m
  -- 8: size, first, so the remaining checks run on bounded input.
  let count = length binds
  when (count > maxNormalBinds) $
    bad ("too many binds: " <> showT count <> " exceeds the limit " <> showT maxNormalBinds)
  -- 1: scalar types.
  for_ inputs $ \(n, t) -> scalar ("input " <> unName n) t
  for_ binds $ \b -> scalar ("bind " <> unName (nbName b)) (nbTy b)
  for_ outputs $ \o -> scalar ("output " <> noName o) (noTy o)
  -- 2: unique names.
  inputNames <- foldM (fresh "duplicate input name ") Set.empty (fmap fst inputs)
  foldM_ (fresh "duplicate bound name (already an input or a bind) ") inputNames (fmap nbName binds)
  let env = Map.fromList (inputs <> [(nbName b, nbTy b) | b <- binds])
  -- 4: scoping, before typing so atom types can be looked up.
  for_ binds $ \b ->
    for_ (rhsVars (nbRhs b)) $ \n ->
      unless (Map.member n env) $
        bad ("undefined variable " <> unName n <> " in bind " <> unName (nbName b))
  for_ outputs $ \o ->
    for_ (atomVars (noAtom o)) $ \n ->
      unless (Map.member n env) $
        bad ("undefined variable " <> unName n <> " in output " <> noName o)
  -- 3 and 6: typing.
  for_ binds (checkBind env)
  for_ outputs $ \o -> do
    t <- atomTy env (noAtom o)
    unless (t == noTy o) $
      bad ("ill-typed output " <> noName o <> ": " <> showT t <> " instead of " <> showT (noTy o))
  -- 5: topological order of the combinational dependency graph.
  let step defined b = do
        for_ (combinationalVars (nbRhs b)) $ \n ->
          unless (Set.member n defined) $
            bad
              ( "bind "
                  <> unName (nbName b)
                  <> " reads "
                  <> unName n
                  <> " before it is bound (binds must be in topological order, free of"
                  <> " combinational loops)"
              )
        pure (Set.insert (nbName b) defined)
  foldM_ step inputNames binds
  -- 7: no copies, no dead binds.
  for_ binds $ \b -> case nbRhs b of
    NAtom _ -> bad ("copy bind " <> unName (nbName b) <> " (copies must be propagated)")
    _ -> pure ()
  let live =
        reachable
          (Map.fromList [(nbName b, nbRhs b) | b <- binds])
          (concatMap (atomVars . noAtom) outputs)
  for_ binds $ \b ->
    unless (Set.member (nbName b) live) $
      bad ("bind " <> unName (nbName b) <> " is unreachable from every output (dead bind)")
  where
    scalar what t =
      unless (isScalar t) $ bad ("type of " <> what <> " is not scalar: " <> showT t)
    fresh msg seen n
      | Set.member n seen = bad (msg <> unName n)
      | otherwise = Right (Set.insert n seen)

checkBind :: Map Name Ty -> NBind -> Either GinError ()
checkBind env (NBind n t rhs) = case rhs of
  NPrim op as -> do
    unless (isCombinational op) $
      illTyped (primName op <> " is not a combinational prim")
    let arity = primArity op
    unless (genericLength as == arity) $
      illTyped (primName op <> " takes " <> showT arity <> " arguments, not " <> showT (length as))
    ts <- traverse (atomTy env) as
    case primResultTy op ts of
      Just r | r == t -> pure ()
      Just r -> illTyped (primName op <> " yields " <> showT r)
      Nothing -> illTyped (primName op <> " is applied to " <> showT ts)
  NMux c a b -> do
    tc <- atomTy env c
    ta <- atomTy env a
    tb <- atomTy env b
    unless (tc == TBool) $ illTyped ("mux condition has type " <> showT tc)
    unless (ta == t && tb == t) $ illTyped ("mux branches have types " <> showT [ta, tb])
  NReg v a -> do
    unless (validValue v && valueTy v == t) $
      bad ("register " <> unName n <> " has an initial value of the wrong type: " <> showT v)
    ta <- atomTy env a
    unless (ta == t) $ illTyped ("register argument has type " <> showT ta)
  NAtom a -> do
    ta <- atomTy env a
    unless (ta == t) $ illTyped ("copied atom has type " <> showT ta)
  where
    illTyped msg = bad ("ill-typed bind " <> unName n <> " of type " <> showT t <> ": " <> msg)

-- | Type of an atom whose variable, if any, is in scope.
atomTy :: Map Name Ty -> Atom -> Either GinError Ty
atomTy env = \case
  AVar n -> maybe (bad ("undefined variable " <> unName n)) Right (Map.lookup n env)
  ALit v
    | validValue v && isScalar (valueTy v) -> Right (valueTy v)
    | otherwise -> bad ("ill-typed literal " <> showT v <> " (literals are valid scalars)")

atomVars :: Atom -> [Name]
atomVars = \case
  AVar n -> [n]
  ALit _ -> []

rhsAtoms :: NRhs -> [Atom]
rhsAtoms = \case
  NPrim _ as -> as
  NMux c a b -> [c, a, b]
  NReg _ a -> [a]
  NAtom a -> [a]

rhsVars :: NRhs -> [Name]
rhsVars = concatMap atomVars . rhsAtoms

-- | Variables read within the cycle: all but a register's argument.
combinationalVars :: NRhs -> [Name]
combinationalVars = \case
  NReg _ _ -> []
  r -> rhsVars r

reachable :: Map Name NRhs -> [Name] -> Set Name
reachable rhss = go Set.empty
  where
    go seen = \case
      [] -> seen
      n : rest
        | Set.member n seen -> go seen rest
        | Just r <- Map.lookup n rhss -> go (Set.insert n seen) (rhsVars r <> rest)
        | otherwise -> go seen rest

bad :: Text -> Either GinError a
bad = Left . ginError StNormalize

showT :: (Show a) => a -> Text
showT = Text.pack . show
