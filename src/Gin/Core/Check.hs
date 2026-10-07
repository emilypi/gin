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
--
-- Checking takes time and memory close to linear in the size of the
-- program as written (its JSON encoding), even for hostile input: I want
-- to be able to check the IR of a design you did not write. An inferred
-- type can be far larger than the expression it comes from: a tuple of
-- @k@ copies of a variable whose type has @m@ components has a type of
-- @k * m@ components. The checker therefore never walks an inferred
-- type. It hash-conses types ('TyRef'), so that comparing two
-- types, or asking whether one is data, takes constant time; and an error
-- message shows at most 'renderBudget' characters of any type or value.
module Gin.Core.Check
  ( checkProgram
  ) where

import Control.Monad (foldM, foldM_, unless, when, zipWithM_)
import Control.Monad.State.Strict (StateT (..), evalStateT, get, lift, put)
import Data.Bifunctor (first)
import Data.Foldable (foldrM, for_, toList, traverse_)
import Data.List (intercalate)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Sequence (Seq)
import Data.Sequence qualified as Seq
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Syntax
import Gin.Error (GinError, Stage (..), ginError, withContext)
import Gin.Netlist.Types (isLegalIdent)
import Gin.Core.Utils (showT)
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
-- rules, including scalar ports, a legal top name, port names that are
-- legal identifiers ('isLegalIdent'), pairwise distinct and different from
-- @clk@, @rst@ and the top name, and every signal in the top entity's
-- domain.
checkProgram :: Program -> Either GinError ()
checkProgram p = do
  let top = progTop p
      defs = progDefs p
  checkPorts top
  declared <- defTypes defs
  for_ defs $ \d ->
    inDef d $ for_ (globalRefs (defBody d)) $ \g ->
      unless (Map.member g declared) (failCheck ("unknown global " <> unName g))
  checkAcyclic defs
  flip evalStateT emptyTable $ do
    refs <- traverse (intern . defTy) defs
    let env =
          Env
            { envDomain = domainName (topDomain top)
            , envGlobals = Map.fromList (zip (fmap defName defs) refs)
            , envLocals = Map.empty
            }
    zipWithM_ (checkDef env) defs refs
  checkTopDef declared top

failCheck :: Text -> Either GinError a
failCheck = Left . ginError StCheck

inDef :: Def -> Either GinError a -> Either GinError a
inDef d = withContext ("in def " <> unName (defName d))

----------------------------------------------------------------------
-- Top entity

-- | Name and port rules, checked before any definition so that a bad
-- port is reported as such rather than through the top definition's type.
-- The top name and the port names are the generated hardware interface,
-- which the netlist builder never renames, so they are held to its rules
-- here: legal identifiers, pairwise distinct, and distinct from the clock
-- @clk@ and the reset @rst@ every module gets (the top name included).
checkPorts :: TopEntity -> Either GinError ()
checkPorts top = withContext "in top entity" $ do
  unless (isLegalIdent (topName top)) $
    failCheck ("illegal top name " <> showT (topName top) <> ": " <> identRule)
  when (topName top == "clk") $
    failCheck "top name clk is reserved for the clock every module gets"
  when (topName top == "rst") $
    failCheck "top name rst is reserved for the reset every module gets"
  when (null (topOutputs top)) $ failCheck "the top entity has no outputs"
  for_ (topInputs top <> topOutputs top) $ \port -> do
    checkPortName (topName top) (portName port)
    unless (isScalar (portTy port)) $
      failCheck
        ("port " <> portName port <> " has non-scalar type " <> renderTy (portTy port))
  foldM_ unique Set.empty (fmap portName (topInputs top <> topOutputs top))
  where
    unique seen n
      | Set.member n seen = failCheck ("duplicate port name " <> n)
      | otherwise = Right (Set.insert n seen)

-- | A port name is a legal identifier other than the clock, the reset and
-- the top name. Legal identifiers are lowercase, so comparing them exactly
-- is comparing them case-insensitively.
checkPortName :: Text -> Text -> Either GinError ()
checkPortName top n
  | not (isLegalIdent n) = failCheck ("illegal port name " <> showT n <> ": " <> identRule)
  | n == "clk" = failCheck "port name clk is reserved for the clock every module gets"
  | n == "rst" = failCheck "port name rst is reserved for the reset every module gets"
  | n == top = failCheck ("port name " <> n <> " equals the top name")
  | otherwise = Right ()

identRule :: Text
identRule =
  "it must be a legal HDL identifier (lowercase ASCII letter first, then lowercase letters, \
  \digits and single underscores; at most 64 characters; no gin_ prefix; not a reserved word)"

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
  , envGlobals :: !(Map Name TyRef)
  , envLocals :: !(Map Name TyRef)
  }

bindLocals :: [(Name, TyRef)] -> Env -> Env
bindLocals xs env = env{envLocals = Map.union (Map.fromList xs) (envLocals env)}

-- | Check a definition against its declared type, already interned.
checkDef :: Env -> Def -> TyRef -> Check ()
checkDef env d declared = inContext ("in def " <> unName (defName d)) $ do
  lift (checkTy env (defTy d))
  actual <- infer env (defBody d)
  unless (sameTy actual declared) $
    refuse
      ( "the body has type "
          <> renderRef actual
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
-- Hash-consed types

-- | One layer of a type, with its components left abstract.
data TyF a
  = FBool
  | FBitVec !Natural
  | FProd !(Seq a)
  | FFun !a !a
  | FSignal !Text !a
  deriving stock (Eq, Ord, Functor, Foldable, Traversable)

-- | The outermost layer of a type.
layerOf :: Ty -> TyF Ty
layerOf = \case
  TBool -> FBool
  TBitVec w -> FBitVec w
  TProd ts -> FProd (Seq.fromList ts)
  TFun a r -> FFun a r
  TSignal d e -> FSignal d e

-- | A hash-consed type. Every type the checker infers is made of these,
-- and the nodes are shared: within one run of the checker, two 'TyRef's
-- denote the same type exactly when their 'refId's are equal.
data TyRef = TyRef
  { refId :: !Int
  , refIsData :: !Bool
  -- ^ 'isData' of the type, computed once when the node is made.
  , refLayer :: !(TyF TyRef)
  }

-- | Type equality, in constant time.
sameTy :: TyRef -> TyRef -> Bool
sameTy a b = refId a == refId b

-- | Every node made so far, keyed by its layer over the components' ids.
newtype Table = Table (Map (TyF Int) TyRef)

emptyTable :: Table
emptyTable = Table Map.empty

-- | Checking state is the hash-consing table.
type Check = StateT Table (Either GinError)

refuse :: Text -> Check a
refuse = lift . failCheck

inContext :: Text -> Check a -> Check a
inContext ctx m = StateT (withContext ctx . runStateT m)

-- | The node for a layer whose components are already nodes. Costs time
-- proportional to the number of components (times the logarithm of the
-- table size), never to the sizes of the components.
mkTy :: TyF TyRef -> Check TyRef
mkTy layer = do
  Table nodes <- get
  let key = fmap refId layer
  case Map.lookup key nodes of
    Just ref -> pure ref
    Nothing -> do
      let ref = TyRef{refId = Map.size nodes, refIsData = dataLayer, refLayer = layer}
      put $! Table (Map.insert key ref nodes)
      pure ref
  where
    dataLayer = case layer of
      FBool -> True
      FBitVec _ -> True
      FProd cs -> all refIsData cs
      FFun _ _ -> False
      FSignal _ _ -> False

-- | The node for a type annotation. Walks the annotation once, so the cost
-- is linear in its size as written.
intern :: Ty -> Check TyRef
intern t = mkTy =<< traverse intern (layerOf t)

----------------------------------------------------------------------
-- Expressions

infer :: Env -> Expr -> Check TyRef
infer env = \case
  EVar n -> lookupIn "unbound variable " n (envLocals env)
  EGlobal n -> lookupIn "unknown global " n (envGlobals env)
  ELit v -> do
    unless (validValue v) $ refuse ("invalid value " <> renderValue v)
    intern (valueTy v)
  EPrim op t -> do
    lift (checkTy env t >> checkPrim op t)
    intern t
  EApp f args -> do
    when (null args) $ refuse "application with no arguments"
    ft <- infer env f
    foldM apply ft (zip [1 :: Int ..] args)
  ELam binders body -> do
    when (null binders) $ refuse "lambda with no binders"
    lift (distinct (fmap fst binders))
    lift (traverse_ (checkTy env . snd) binders)
    refs <- traverse (intern . snd) binders
    res <- infer (bindLocals (zip (fmap fst binders) refs) env) body
    foldrM (\a r -> mkTy (FFun a r)) res refs
  ELet isRec binds body -> do
    lift (distinct (fmap bindName binds))
    lift (traverse_ (checkTy env . bindTy) binds)
    refs <- traverse (intern . bindTy) binds
    let locals = zip (fmap bindName binds) refs
    env' <-
      if isRec
        then do
          let recEnv = bindLocals locals env
          zipWithM_ (checkBind recEnv) binds refs
          pure recEnv
        else
          foldM
            (\e (b, local) -> bindLocals [local] e <$ checkBind e b (snd local))
            env
            (zip binds locals)
    infer env' body
  ETuple es -> case es of
    _ : _ : _ -> mkTy . FProd . Seq.fromList =<< traverse (infer env) es
    _ -> refuse "tuple with fewer than two components"
  EProj i e -> do
    t <- infer env e
    case refLayer t of
      FProd cs -> case component i cs of
        Just c -> pure c
        Nothing -> refuse ("projection index " <> showT i <> " out of range for " <> renderRef t)
      _ -> refuse ("projection from non-product type " <> renderRef t)
  EIf c t e -> do
    ct <- infer env c
    case refLayer ct of
      FBool -> pure ()
      _ -> refuse ("if condition must be Bool, got " <> renderRef ct)
    tt <- infer env t
    et <- infer env e
    unless (sameTy tt et) $
      refuse ("if branches have different types: " <> renderRef tt <> " and " <> renderRef et)
    unless (refIsData tt) $
      refuse ("if branches must be data (no signals or functions), got " <> renderRef tt)
    pure tt
  where
    lookupIn what n scope = maybe (refuse (what <> unName n)) pure (Map.lookup n scope)
    apply ft (i, arg) = case refLayer ft of
      FFun expected res -> do
        actual <- infer env arg
        unless (sameTy actual expected) $
          refuse
            ( "argument "
                <> showT i
                <> ": expected "
                <> renderRef expected
                <> ", got "
                <> renderRef actual
            )
        pure res
      _ -> refuse ("cannot apply a term of type " <> renderRef ft <> " to argument " <> showT i)
    -- In time logarithmic in the index, however wide the product.
    component i cs
      | i < fromIntegral (Seq.length cs) = Seq.lookup (fromIntegral i) cs
      | otherwise = Nothing

-- | Check a bind's value against its declared type, already interned.
checkBind :: Env -> Bind -> TyRef -> Check ()
checkBind env b declared = inContext ("in bind " <> unName (bindName b)) $ do
  actual <- infer env (bindExpr b)
  unless (sameTy actual declared) $
    refuse
      ( "the value has type "
          <> renderRef actual
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
-- that is already well formed. Linear in the annotation.
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

-- | Most characters of a type or value an error message shows; the rest
-- is elided as @...@. An inferred type can be far larger than the input
-- that produces it, so it is never rendered whole.
renderBudget :: Int
renderBudget = 240

-- | Most components of a product or tuple an error message lists; the
-- others are counted (@... 31992 more@), so a clipped type keeps its shape.
shownComponents :: Int
shownComponents = 8

-- | The chunks of a product or tuple with @total@ components, given the
-- lazily produced chunks of its components, of which only the first
-- 'shownComponents' are used.
componentChunks :: Int -> [[Text]] -> [Text]
componentChunks total shown =
  "(" : intercalate [", "] (take shownComponents shown <> more) <> [")"]
  where
    more = [["... ", showT (total - shownComponents), " more"] | total > shownComponents]

-- | Join lazily produced chunks, keeping at most 'renderBudget'
-- characters, so that only the part that is shown is ever built.
clip :: [Text] -> Text
clip = go [] renderBudget
  where
    finish = Text.concat . reverse
    go acc room = \case
      [] -> finish acc
      c : cs
        | Text.compareLength c room /= GT -> go (c : acc) (room - Text.length c) cs
        | otherwise -> finish ("..." : Text.take room c : acc)

-- | The chunks of a type, given a view of its outermost layer.
tyChunks :: (a -> TyF a) -> a -> [Text]
tyChunks view = go (0 :: Int)
  where
    go prec t = case view t of
      FBool -> ["Bool"]
      FBitVec w -> parensIf (prec >= 2) ["BitVec ", showT w]
      FProd ts -> componentChunks (Seq.length ts) (fmap (go 0) (toList ts))
      FFun a r -> parensIf (prec >= 1) (go 1 a <> [" -> "] <> go 0 r)
      FSignal d e -> parensIf (prec >= 2) (["Signal ", d, " "] <> go 2 e)
    parensIf b cs = if b then "(" : cs <> [")"] else cs

renderTy :: Ty -> Text
renderTy = clip . tyChunks layerOf

renderRef :: TyRef -> Text
renderRef = clip . tyChunks refLayer

renderValue :: Value -> Text
renderValue = clip . go
  where
    go = \case
      VBool b -> [if b then "true" else "false"]
      VBV w n -> [showT n, " : BitVec ", showT w]
      VTuple vs -> componentChunks (length vs) (fmap go vs)
