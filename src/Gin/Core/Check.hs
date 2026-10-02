-- | Type checker for the core IR.
--
-- The IR is fully annotated (lambda binders, let binds and primitives
-- carry their types), so checking is syntax-directed: every expression's
-- type is computed bottom-up and compared with the annotations around it.
--
-- Besides the rules listed on 'checkProgram', every type annotation must
-- be well formed: bit-vector widths within @1..'maxWidth'@, products of
-- two or more components, and signals only over data (Bool, bit vectors
-- and products of data) in the top entity's domain.
module Gin.Core.Check
  ( checkProgram
  ) where

import Control.Monad (foldM, foldM_, unless, when)
import Data.Bifunctor (first)
import Data.Foldable (for_, traverse_)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Syntax
import Gin.Error (GinError, Stage (..), ginError, withContext)
import Gin.Netlist.Types (isLegalIdent)
import Numeric.Natural (Natural)

-- | Full static check. Errors use 'StCheck'. Enforces: unique def names;
-- every 'EGlobal' resolves; no recursion among globals (direct or
-- mutual); lexical scoping as documented on 'ELet'; binder names within
-- one 'ELam' binder list, and within one 'ELet' bind list, are pairwise
-- distinct; prim instantiated types match the rules in "Gin.Core.Prim",
-- including value/type agreement for register and mealy initial values;
-- application argument types match; an 'EIf' condition is 'TBool' and its
-- branches agree and are neither signals nor functions; projections are
-- in range; every 'Value' is valid ('validValue'); and the 'TopEntity'
-- rules, including scalar ports, unique port names, a legal top name, and
-- every signal in the top entity's domain.
checkProgram :: Program -> Either GinError ()
checkProgram p = do
  let top = progTop p
  checkPorts top
  globals <- defTypes (progDefs p)
  for_ (progDefs p) $ \d ->
    inDef d $ for_ (globalRefs (defBody d)) $ \g ->
      unless (Map.member g globals) (failCheck ("unknown global " <> unName g))
  checkAcyclic (progDefs p)
  let env = Env{envDomain = domainName (topDomain top), envGlobals = globals, envLocals = Map.empty}
  traverse_ (checkDef env) (progDefs p)
  checkTopDef globals top

failCheck :: Text -> Either GinError a
failCheck = Left . ginError StCheck

showT :: (Show a) => a -> Text
showT = Text.pack . show

inDef :: Def -> Either GinError a -> Either GinError a
inDef d = withContext ("in def " <> unName (defName d))

----------------------------------------------------------------------
-- Top entity

-- | Name and port rules, checked before any definition so that a bad
-- port is reported as such rather than through the top definition's type.
checkPorts :: TopEntity -> Either GinError ()
checkPorts top = withContext "in top entity" $ do
  unless (isLegalIdent (topName top)) $
    failCheck
      ( "illegal top name "
          <> showT (topName top)
          <> ": it must be a legal HDL identifier (lowercase ASCII letter first, then lowercase \
             \letters, digits and single underscores; at most 64 characters; no gin_ prefix; \
             \not a reserved word)"
      )
  when (null (topOutputs top)) $ failCheck "the top entity has no outputs"
  for_ (topInputs top <> topOutputs top) $ \port ->
    unless (isScalar (portTy port)) $
      failCheck
        ("port " <> portName port <> " has non-scalar type " <> renderTy (portTy port))
  foldM_ unique Set.empty (fmap portName (topInputs top <> topOutputs top))
  where
    unique seen n
      | Set.member n seen = failCheck ("duplicate port name " <> n)
      | otherwise = Right (Set.insert n seen)

-- | The top definition's type must be
-- @Signal d i1 -> .. -> Signal d ik -> Signal d o@ with @o@ the single
-- output type or the right-nested product of the output types.
checkTopDef :: Map Name Ty -> TopEntity -> Either GinError ()
checkTopDef globals top = withContext "in top entity" $
  case (Map.lookup (topDef top) globals, fmap portTy (topOutputs top)) of
    (Nothing, _) -> failCheck ("top definition " <> unName (topDef top) <> " is not defined")
    (_, []) -> failCheck "the top entity has no outputs"
    (Just actual, o : os) -> do
      let d = domainName (topDomain top)
          expected = tFuns (fmap (TSignal d . portTy) (topInputs top)) (TSignal d (nest o os))
      unless (actual == expected) $
        failCheck
          ( "top definition "
              <> unName (topDef top)
              <> " has type "
              <> renderTy actual
              <> ", but the ports require "
              <> renderTy expected
          )
  where
    nest o = \case
      [] -> o
      o' : os -> TProd [o, nest o' os]

----------------------------------------------------------------------
-- Definitions

defTypes :: [Def] -> Either GinError (Map Name Ty)
defTypes = foldM insert Map.empty
  where
    insert m d
      | Map.member (defName d) m = failCheck ("duplicate definition " <> unName (defName d))
      | otherwise = Right (Map.insert (defName d) (defTy d) m)

-- | Globals an expression refers to.
globalRefs :: Expr -> Set Name
globalRefs = \case
  EVar _ -> Set.empty
  EGlobal n -> Set.singleton n
  ELit _ -> Set.empty
  EPrim _ _ -> Set.empty
  EApp f args -> foldMap globalRefs (f : args)
  ELam _ body -> globalRefs body
  ELet _ binds body -> foldMap (globalRefs . bindExpr) binds <> globalRefs body
  ETuple es -> foldMap globalRefs es
  EProj _ e -> globalRefs e
  EIf c t e -> globalRefs c <> globalRefs t <> globalRefs e

-- | Depth-first search of the reference graph; a reference back to a
-- definition still being visited closes a cycle, which is reported in
-- reference order.
checkAcyclic :: [Def] -> Either GinError ()
checkAcyclic defs = case foldM (visit [] Set.empty) Set.empty (fmap defName defs) of
  Right _ -> Right ()
  Left cycle' ->
    failCheck
      ("recursive definitions are not allowed: " <> Text.intercalate " -> " (fmap unName cycle'))
  where
    graph = Map.fromList [(defName d, Set.toList (globalRefs (defBody d))) | d <- defs]
    visit :: [Name] -> Set Name -> Set Name -> Name -> Either [Name] (Set Name)
    visit path onPath done n
      | Set.member n onPath = Left (n : reverse (takeWhile (/= n) path) <> [n])
      | Set.member n done = Right done
      | otherwise =
          Set.insert n
            <$> foldM (visit (n : path) (Set.insert n onPath)) done (Map.findWithDefault [] n graph)

data Env = Env
  { envDomain :: !Text
  , envGlobals :: !(Map Name Ty)
  , envLocals :: !(Map Name Ty)
  }

bindLocals :: [(Name, Ty)] -> Env -> Env
bindLocals xs env = env{envLocals = Map.union (Map.fromList xs) (envLocals env)}

checkDef :: Env -> Def -> Either GinError ()
checkDef env d = inDef d $ do
  checkTy env (defTy d)
  actual <- infer env (defBody d)
  unless (actual == defTy d) $
    failCheck
      ( "the body has type "
          <> renderTy actual
          <> ", but the definition is declared "
          <> renderTy (defTy d)
      )

----------------------------------------------------------------------
-- Types

-- | Bool, bit vectors and products of them: what a signal carries and an
-- 'EIf' chooses between.
isData :: Ty -> Bool
isData = \case
  TBool -> True
  TBitVec _ -> True
  TProd ts -> all isData ts
  TFun _ _ -> False
  TSignal _ _ -> False

-- | Well-formedness of a type annotation.
checkTy :: Env -> Ty -> Either GinError ()
checkTy env = go
  where
    go t = case t of
      TBool -> Right ()
      TBitVec w ->
        unless (w >= 1 && w <= maxWidth) $
          failCheck ("bit-vector width " <> showT w <> " outside 1.." <> showT maxWidth)
      TProd ts -> case ts of
        _ : _ : _ -> traverse_ go ts
        _ -> failCheck ("product type " <> renderTy t <> " has fewer than two components")
      TFun a r -> go a >> go r
      TSignal d e -> do
        unless (d == envDomain env) $
          failCheck
            ( "signal in domain "
                <> d
                <> ", but every signal must be in the top entity's domain "
                <> envDomain env
            )
        unless (isData e) $
          failCheck
            ("a signal must carry data (no signals or functions), got " <> renderTy t)
        go e

----------------------------------------------------------------------
-- Expressions

infer :: Env -> Expr -> Either GinError Ty
infer env = \case
  EVar n -> lookupIn "unbound variable " n (envLocals env)
  EGlobal n -> lookupIn "unknown global " n (envGlobals env)
  ELit v -> do
    unless (validValue v) $ failCheck ("invalid value " <> renderValue v)
    pure (valueTy v)
  EPrim op t -> do
    checkTy env t
    checkPrim op t
    pure t
  EApp f args -> do
    when (null args) $ failCheck "application with no arguments"
    ft <- infer env f
    foldM apply ft (zip [1 :: Int ..] args)
  ELam binders body -> do
    when (null binders) $ failCheck "lambda with no binders"
    distinct (fmap fst binders)
    traverse_ (checkTy env . snd) binders
    res <- infer (bindLocals binders env) body
    pure (tFuns (fmap snd binders) res)
  ELet isRec binds body -> do
    distinct (fmap bindName binds)
    traverse_ (checkTy env . bindTy) binds
    let local b = (bindName b, bindTy b)
    env' <-
      if isRec
        then do
          let recEnv = bindLocals (fmap local binds) env
          traverse_ (checkBind recEnv) binds
          pure recEnv
        else foldM (\e b -> bindLocals [local b] e <$ checkBind e b) env binds
    infer env' body
  ETuple es -> case es of
    _ : _ : _ -> TProd <$> traverse (infer env) es
    _ -> failCheck "tuple with fewer than two components"
  EProj i e ->
    infer env e >>= \case
      t@(TProd ts) -> case lookup i (zip [0 :: Natural ..] ts) of
        Just c -> pure c
        Nothing -> failCheck ("projection index " <> showT i <> " out of range for " <> renderTy t)
      t -> failCheck ("projection from non-product type " <> renderTy t)
  EIf c t e -> do
    ct <- infer env c
    unless (ct == TBool) $ failCheck ("if condition must be Bool, got " <> renderTy ct)
    tt <- infer env t
    et <- infer env e
    unless (tt == et) $
      failCheck ("if branches have different types: " <> renderTy tt <> " and " <> renderTy et)
    unless (isData tt) $
      failCheck ("if branches must be data (no signals or functions), got " <> renderTy tt)
    pure tt
  where
    lookupIn what n scope = maybe (failCheck (what <> unName n)) Right (Map.lookup n scope)
    apply ft (i, arg) = case ft of
      TFun expected res -> do
        actual <- infer env arg
        unless (actual == expected) $
          failCheck
            ( "argument "
                <> showT i
                <> ": expected "
                <> renderTy expected
                <> ", got "
                <> renderTy actual
            )
        pure res
      other ->
        failCheck ("cannot apply a term of type " <> renderTy other <> " to argument " <> showT i)

checkBind :: Env -> Bind -> Either GinError ()
checkBind env b = withContext ("in bind " <> unName (bindName b)) $ do
  actual <- infer env (bindExpr b)
  unless (actual == bindTy b) $
    failCheck
      ( "the value has type "
          <> renderTy actual
          <> ", but the bind is declared "
          <> renderTy (bindTy b)
      )

distinct :: [Name] -> Either GinError ()
distinct = go Set.empty
  where
    go _ [] = Right ()
    go seen (n : ns)
      | Set.member n seen = failCheck ("duplicate binder " <> unName n)
      | otherwise = go (Set.insert n seen) ns

----------------------------------------------------------------------
-- Primitives

-- | The typing rules documented in "Gin.Core.Prim", for an annotation
-- that is already well formed.
checkPrim :: PrimOp -> Ty -> Either GinError ()
checkPrim op t = case op of
  BoolAnd -> boolBinary
  BoolOr -> boolBinary
  BoolXor -> boolBinary
  BoolEq -> boolBinary
  BoolNot -> exactly (tFuns [TBool] TBool)
  BvAdd -> bvBinary
  BvSub -> bvBinary
  BvMul -> bvBinary
  BvAnd -> bvBinary
  BvOr -> bvBinary
  BvXor -> bvBinary
  BvNeg -> bvUnary
  BvNot -> bvUnary
  BvShl _ -> bvUnary
  BvLshr _ -> bvUnary
  BvEq -> bvCompare
  BvUlt -> bvCompare
  BvUle -> bvCompare
  BvConcat -> case t of
    TFun (TBitVec a) (TFun (TBitVec b) _) ->
      exactly (tFuns [TBitVec a, TBitVec b] (TBitVec (a + b)))
    _ -> shape "BitVec a -> BitVec b -> BitVec (a + b)"
  BvExtract hi lo -> withWidth "BitVec n -> BitVec (hi - lo + 1)" $ \n -> do
    unless (hi < n) $
      bad ("hi = " <> showT hi <> " must be below the operand width " <> showT n)
    unless (lo <= hi) $ bad ("lo = " <> showT lo <> " must not exceed hi = " <> showT hi)
    exactly (tFuns [TBitVec n] (TBitVec (hi - lo + 1)))
  BvZext m -> withWidth "BitVec n -> BitVec m" $ \n -> do
    unless (m >= n) $
      bad ("cannot zero-extend BitVec " <> showT n <> " to the narrower BitVec " <> showT m)
    exactly (tFuns [TBitVec n] (TBitVec m))
  BvOfBool -> exactly (tFuns [TBool] (TBitVec 1))
  SigPure -> case t of
    TFun a (TSignal d _) -> do
      unless (isData a) $ bad ("cannot make a signal of " <> renderTy a <> ", which is not data")
      exactly (TFun a (TSignal d a))
    _ -> shape "t -> Signal d t"
  SigLift k -> do
    when (k < 1) $ bad "the arity must be at least 1"
    case peel (k + 1) t of
      Just (f : _, TSignal d r) -> case peel k f of
        Just (ts, _) -> exactly (tFuns (tFuns ts r : fmap (TSignal d) ts) (TSignal d r))
        Nothing -> shape liftShape
      _ -> shape liftShape
  SigRegister v -> do
    initial v
    case t of
      TFun (TSignal d a) _ -> do
        stateType v a
        exactly (TFun (TSignal d a) (TSignal d a))
      _ -> shape "Signal d t -> Signal d t"
  SigMealy v -> do
    initial v
    case t of
      TFun (TFun s (TFun i (TProd [_, o]))) (TFun (TSignal d _) _) -> do
        stateType v s
        exactly (tFuns [tFuns [s, i] (TProd [s, o]), TSignal d i] (TSignal d o))
      _ -> shape "(s -> i -> (s, o)) -> Signal d i -> Signal d o"
  where
    bad msg = failCheck ("prim " <> primName op <> ": " <> msg)
    exactly expected =
      unless (t == expected) $
        bad ("expected type " <> renderTy expected <> ", got " <> renderTy t)
    shape s = bad ("expected a type of the form " <> s <> ", got " <> renderTy t)
    withWidth s k = case t of
      TFun (TBitVec n) _ -> k n
      _ -> shape s
    boolBinary = exactly (tFuns [TBool, TBool] TBool)
    bvUnary = withWidth "BitVec n -> BitVec n" $ \n -> exactly (tFuns [TBitVec n] (TBitVec n))
    bvBinary =
      withWidth "BitVec n -> BitVec n -> BitVec n" $ \n ->
        exactly (tFuns [TBitVec n, TBitVec n] (TBitVec n))
    bvCompare =
      withWidth "BitVec n -> BitVec n -> Bool" $ \n ->
        exactly (tFuns [TBitVec n, TBitVec n] TBool)
    liftShape = "(t1 -> .. -> tk -> r) -> Signal d t1 -> .. -> Signal d tk -> Signal d r"
    initial v = unless (validValue v) $ bad ("invalid initial value " <> renderValue v)
    stateType v s =
      unless (valueTy v == s) $
        bad
          ( "the initial value has type "
              <> renderTy (valueTy v)
              <> ", but the state has type "
              <> renderTy s
          )

-- | Split off exactly @n@ argument types.
peel :: Natural -> Ty -> Maybe ([Ty], Ty)
peel 0 t = Just ([], t)
peel n (TFun a r) = first (a :) <$> peel (n - 1) r
peel _ _ = Nothing

----------------------------------------------------------------------
-- Rendering

renderTy :: Ty -> Text
renderTy = go (0 :: Int)
  where
    go prec = \case
      TBool -> "Bool"
      TBitVec w -> parensIf (prec >= 2) ("BitVec " <> showT w)
      TProd ts -> "(" <> Text.intercalate ", " (fmap (go 0) ts) <> ")"
      TFun a r -> parensIf (prec >= 1) (go 1 a <> " -> " <> go 0 r)
      TSignal d e -> parensIf (prec >= 2) ("Signal " <> d <> " " <> go 2 e)
    parensIf b s = if b then "(" <> s <> ")" else s

renderValue :: Value -> Text
renderValue = \case
  VBool b -> if b then "true" else "false"
  VBV w n -> showT n <> " : BitVec " <> showT w
  VTuple vs -> "(" <> Text.intercalate ", " (fmap renderValue vs) <> ")"
