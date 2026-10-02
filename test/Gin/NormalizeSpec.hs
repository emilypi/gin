-- | Tests for the normalizer and for the normal-form invariant checker.
--
-- Semantic equivalence with the reference simulators is tested end to
-- end elsewhere; here every result is checked against the invariants of
-- "Gin.Core.Normal" and, where a hand-written normal form exists,
-- compared with it up to bind names and bind order.
module Gin.NormalizeSpec (spec) where

import Control.Exception (evaluate)
import Data.Foldable (for_)
import Data.List (sortOn)
import Data.Map.Strict qualified as Map
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Normal
import Gin.Core.Syntax
import Gin.Error (GinError (..), Stage (..))
import Gin.Examples
import Gin.Limits (maxNormalBinds)
import Gin.Normalize (checkNormal, normalize)
import System.Timeout (timeout)
import Test.Hspec

----------------------------------------------------------------------
-- Building programs

prim :: PrimOp -> [Ty] -> Ty -> Expr
prim op args res = EPrim op (tFuns args res)

var :: Text -> Expr
var = EVar . Name

lit8 :: Integer -> Expr
lit8 = ELit . VBV 8

bin8 :: PrimOp -> Expr -> Expr -> Expr
bin8 op a b = EApp (prim op [bv 8, bv 8] (bv 8)) [a, b]

not8 :: Expr -> Expr
not8 a = EApp (prim BvNot [bv 8] (bv 8)) [a]

eq8 :: Expr -> Expr -> Expr
eq8 a b = EApp (prim BvEq [bv 8, bv 8] TBool) [a, b]

-- | @\\z -> z + k@ on 8-bit vectors.
addK :: Integer -> Expr
addK k = ELam [("z", bv 8)] (bin8 BvAdd (var "z") (lit8 k))

-- | @sig.lift k f s1 .. sk@ for argument types @as@ and result type @r@.
lift :: [Ty] -> Ty -> Expr -> [Expr] -> Expr
lift as r f ss =
  EApp (prim (SigLift (fromIntegral (length as))) (tFuns as r : fmap sig as) (sig r)) (f : ss)

register :: Value -> Expr -> Expr
register v s = EApp (prim (SigRegister v) [sig (valueTy v)] (sig (valueTy v))) [s]

-- | A program whose top entity is the definition @Test.top@.
program :: Text -> [Port] -> [Port] -> [Def] -> Program
program name ins outs defs =
  Program
    { progProducer = Producer "gin-test" "n/a"
    , progTop =
        TopEntity
          { topName = name
          , topDomain = sysDomain
          , topInputs = ins
          , topOutputs = outs
          , topDef = "Test.top"
          }
    , progDefs = defs
    , progCertificate = testCertificate "Test.top_correct"
    }

-- | @Test.top@ as a lambda over input signals named like the ports.
mkTop :: [(Text, Ty)] -> Ty -> Expr -> Def
mkTop ins out body = Def "Test.top" (tFuns (fmap (sig . snd) ins) (sig out)) lams
  where
    lams = case ins of
      [] -> body
      _ -> ELam [(Name n, sig t) | (n, t) <- ins] body

-- | A normal form for a program built with 'program'.
normalForm :: Text -> [(Name, Ty)] -> [NOutput] -> [NBind] -> NModule
normalForm name ins outs binds =
  NModule
    { nmName = name
    , nmDomain = sysDomain
    , nmInputs = ins
    , nmOutputs = outs
    , nmBinds = binds
    , nmCertificate = testCertificate "Test.top_correct"
    }

----------------------------------------------------------------------
-- Example programs

-- > counter en = let rec c = register 0 (lift2 (\e v -> if e then v + 1 else v) en c) in c
--
-- Without the register, @c@ depends on itself within the cycle.
recCounter :: Bool -> Program
recCounter withRegister =
  program "counter" [Port "en" TBool] [Port "count" (bv 8)] [mkTop [("en", TBool)] (bv 8) body]
  where
    step = ELam [("e", TBool), ("v", bv 8)] (EIf (var "e") (EApp (addK 1) [var "v"]) (var "v"))
    lifted = lift [TBool, bv 8] (bv 8) step [var "en", var "c"]
    next = if withRegister then register (VBV 8 0) lifted else lifted
    body = ELet True [Bind "c" (sig (bv 8)) next] (var "c")

-- | 'counterNormal' as produced from a program built with 'program'.
recCounterNormal :: NModule
recCounterNormal = counterNormal {nmCertificate = testCertificate "Test.top_correct"}

-- > a = lift (+ 1) b; b = lift (+ 1) a   (or b = register 0 a)
mutualRec :: Bool -> Program
mutualRec withRegister =
  program "mutual" [Port "x" (bv 8)] [Port "y" (bv 8)] [mkTop [("x", bv 8)] (bv 8) body]
  where
    a = lift [bv 8] (bv 8) (addK 1) [var "b"]
    b = if withRegister then register (VBV 8 0) (var "a") else lift [bv 8] (bv 8) (addK 1) [var "a"]
    body = ELet True [Bind "a" (sig (bv 8)) a, Bind "b" (sig (bv 8)) b] (var "a")

-- > free = let rec c = register 0 (lift (+ 1) c) in c   -- no inputs at all
freeCounter :: Program
freeCounter =
  program "free" [] [Port "count" (bv 8)] [Def "Test.top" (sig (bv 8)) body]
  where
    body =
      ELet
        True
        [Bind "c" (sig (bv 8)) (register (VBV 8 0) (lift [bv 8] (bv 8) (addK 1) [var "c"]))]
        (var "c")

-- > fib _ = mealy (\st _ -> ((st.1, st.0 + st.1), st.0)) (0, 1)
fibProgram :: Program
fibProgram = program "fib" [Port "en" TBool] [Port "f" (bv 8)] [mkTop [("en", TBool)] (bv 8) body]
  where
    stTy = TProd [bv 8, bv 8]
    st i = EProj i (var "st")
    step =
      ELam [("st", stTy), ("e", TBool)] $
        ETuple [ETuple [st 1, bin8 BvAdd (st 0) (st 1)], st 0]
    mealyTy = [tFuns [stTy, TBool] (TProd [stTy, bv 8]), sig TBool]
    body = EApp (prim (SigMealy (VTuple [VBV 8 0, VBV 8 1])) mealyTy (sig (bv 8))) [step, var "en"]

fibNormal :: NModule
fibNormal =
  normalForm
    "fib"
    [("en", TBool)]
    [NOutput "f" (bv 8) (AVar "a")]
    [ NBind "a" (bv 8) (NReg (VBV 8 0) (AVar "b"))
    , NBind "b" (bv 8) (NReg (VBV 8 1) (AVar "sum"))
    , NBind "sum" (bv 8) (NPrim BvAdd [AVar "a", AVar "b"])
    ]

-- > pairReg x b = register (0, true) (lift2 (,) x b)
pairRegister :: Program
pairRegister =
  program
    "pairreg"
    [Port "x" (bv 8), Port "b" TBool]
    [Port "xq" (bv 8), Port "bq" TBool]
    [mkTop [("x", bv 8), ("b", TBool)] pairTy body]
  where
    pairTy = TProd [bv 8, TBool]
    pair = ELam [("u", bv 8), ("c", TBool)] (ETuple [var "u", var "c"])
    paired = lift [bv 8, TBool] pairTy pair [var "x", var "b"]
    body = register (VTuple [VBV 8 0, VBool True]) paired

pairRegisterNormal :: NModule
pairRegisterNormal =
  normalForm
    "pairreg"
    [("x", bv 8), ("b", TBool)]
    [NOutput "xq" (bv 8) (AVar "xr"), NOutput "bq" TBool (AVar "br")]
    [ NBind "xr" (bv 8) (NReg (VBV 8 0) (AVar "x"))
    , NBind "br" TBool (NReg (VBool True) (AVar "b"))
    ]

-- | A program from 8-bit input @x@ to 8-bit output @y@ whose top
-- definition has the given type and body.
withTop :: Text -> Ty -> Expr -> Program
withTop name ty body = program name [Port "x" (bv 8)] [Port "y" (bv 8)] [Def "Test.top" ty body]

-- | Like 'withTop', with the body under a lambda binding the input signal @x@.
withBody :: Text -> Expr -> Program
withBody name body = withTop name sigFun8 (ELam [("x", sig (bv 8))] body)

sigFun8 :: Ty
sigFun8 = TFun (sig (bv 8)) (sig (bv 8))

-- | A one-input, one-output program applying @f@ pointwise.
pointwise :: Text -> Expr -> Program
pointwise name f =
  program
    name
    [Port "x" (bv 8)]
    [Port "y" (bv 8)]
    [mkTop [("x", bv 8)] (bv 8) (lift [bv 8] (bv 8) f [var "x"])]

-- > lift2 (\a b -> (a + b, a - b)) x y
twoOutputs :: Program
twoOutputs =
  program
    "two"
    [Port "x" (bv 8), Port "y" (bv 8)]
    [Port "sum" (bv 8), Port "diff" (bv 8)]
    [mkTop [("x", bv 8), ("y", bv 8)] resTy body]
  where
    resTy = TProd [bv 8, bv 8]
    f =
      ELam
        [("a", bv 8), ("b", bv 8)]
        (ETuple [bin8 BvAdd (var "a") (var "b"), bin8 BvSub (var "a") (var "b")])
    body = lift [bv 8, bv 8] resTy f [var "x", var "y"]

-- > lift2 (\a b -> (a + b, (a == b, a))) x y
--
-- With @flat@, the result is the (ill-formed) flat triple @(a + b, a == b, a)@.
threeOutputs :: Bool -> Program
threeOutputs flat =
  program
    "three"
    [Port "x" (bv 8), Port "y" (bv 8)]
    [Port "sum" (bv 8), Port "same" TBool, Port "first" (bv 8)]
    [mkTop [("x", bv 8), ("y", bv 8)] resTy body]
  where
    s = bin8 BvAdd (var "a") (var "b")
    e = eq8 (var "a") (var "b")
    (resTy, result)
      | flat = (TProd [bv 8, TBool, bv 8], ETuple [s, e, var "a"])
      | otherwise = (TProd [bv 8, TProd [TBool, bv 8]], ETuple [s, ETuple [e, var "a"]])
    body = lift [bv 8, bv 8] resTy (ELam [("a", bv 8), ("b", bv 8)] result) [var "x", var "y"]

-- | Definitions @Chain.g0 = base@ and @Chain.g(i+1) = \\x -> step Chain.gi x@
-- over 8-bit vectors, and a top entity applying @Chain.gn@ pointwise to its
-- input.
chainProgram :: Int -> Expr -> (Expr -> Expr -> Expr) -> Program
chainProgram = chainProgramOf (bv 8)

chainProgramOf :: Ty -> Int -> Expr -> (Expr -> Expr -> Expr) -> Program
chainProgramOf ty n base step =
  program "chain" [Port "x" ty] [Port "y" ty] (top : Def (g 0) fTy base : defs)
  where
    g :: Int -> Name
    g i = Name ("Chain.g" <> Text.pack (show i))
    fTy = TFun ty ty
    level i = Def (g (i + 1)) fTy (ELam [("x", ty)] (step (EGlobal (g i)) (var "x")))
    defs = fmap level [0 .. n - 1]
    top = mkTop [("x", ty)] ty (lift [ty] ty (EGlobal (g n)) [var "x"])

-- | @g(i+1) x = g i (g i x)@ from @g0 x = not x@: @2^n@ distinct binds.
nestedChain :: Int -> Program
nestedChain n = chainProgram n (ELam [("x", bv 8)] (not8 (var "x"))) twice

-- | @g(i+1) x = g i x + g i x@ from @g0 x = x + x@: the two calls build the
-- same binds, so the result is small but the inlining work doubles per level.
sharedChain :: Int -> Program
sharedChain n =
  chainProgram n (ELam [("x", bv 8)] (bin8 BvAdd (var "x") (var "x"))) $ \g x ->
    bin8 BvAdd (EApp g [x]) (EApp g [x])

-- | @g(i+1) x = g i (g i x)@ from @g0 x = x@: exponential work, no binds.
identityChain :: Int -> Program
identityChain n = chainProgram n (ELam [("x", bv 8)] (var "x")) twice

-- | @g(i+1) x = g i (g i x)@ from
-- @g0 x = (if x then (x, wide) else (x, wide)).0@ with a 10000-component
-- literal @wide@: every call does work proportional to the width of @wide@
-- but emits no binds, since both branches agree.
wideChain :: Int -> Program
wideChain n = chainProgramOf TBool n base twice
  where
    wide = ELit (VTuple (replicate 10000 (VBool False)))
    both = ETuple [var "x", wide]
    base = ELam [("x", TBool)] (EProj 0 (EIf (var "x") both both))

twice :: Expr -> Expr -> Expr
twice g x = EApp g [EApp g [x]]

-- | The right-nested tuple value @(false, (false, .. false))@ with @d@
-- levels of nesting.
deepState :: Int -> Value
deepState d = foldr (\_ v -> VTuple [VBool False, v]) (VBool False) [1 .. d]

-- > deep b = mealy (\st i -> (st, i)) (deepState d) b
--
-- The state never changes and the output is the input, so every state
-- register is dead.
deepMealy :: Int -> Program
deepMealy d = program "deep" [Port "b" TBool] [Port "o" TBool] [mkTop [("b", TBool)] TBool body]
  where
    v = deepState d
    st = valueTy v
    stepTy = tFuns [st, TBool] (TProd [st, TBool])
    step = ELam [("st", st), ("i", TBool)] (ETuple [var "st", var "i"])
    body = EApp (prim (SigMealy v) [stepTy, sig TBool] (sig TBool)) [step, var "b"]

-- > deepReg x = let r = register (deepState d) (lift nest x) in lift deepest r
--
-- @nest b@ is @(b, (b, .. b))@ with @d@ levels of nesting and @deepest@
-- projects out its innermost component, so one register is live.
deepRegister :: Int -> Program
deepRegister d =
  program "deepreg" [Port "x" TBool] [Port "y" TBool] [mkTop [("x", TBool)] TBool body]
  where
    v = deepState d
    t = valueTy v
    nest = ELam [("b", TBool)] (foldr (\_ e -> ETuple [var "b", e]) (var "b") [1 .. d])
    deepest = ELam [("t", t)] (foldr (\_ e -> EProj 1 e) (var "t") [1 .. d])
    reg = register v (lift [TBool] t nest [var "x"])
    body = ELet False [Bind "r" (sig t) reg] (lift [t] TBool deepest [var "r"])

-- | @TBool@ paired with itself @k@ times. Each level is shared, so the type
-- takes @k@ steps to build although it has @2^k@ components.
doubledTy :: Int -> Ty
doubledTy k = foldr (\_ t -> TProd [t, t]) TBool [1 .. k]

-- | @name0 = base; name(i+1) = (namei, namei)@ for @i < k@: @k + 1@ binds
-- whose last value is a tuple of @2^k@ Bools, shared at every level.
doublings :: Text -> Expr -> Int -> [Bind]
doublings name base k = [Bind (n i) (doubledTy i) (rhs i) | i <- [0 .. k]]
  where
    n i = Name (name <> Text.pack (show i))
    rhs i = if i == 0 then base else ETuple [EVar (n (i - 1)), EVar (n (i - 1))]

-- | Component 0, @k@ times over.
firsts :: Int -> Expr -> Expr
firsts k e = foldr (\_ -> EProj 0) e [1 .. k]

-- > shared b = lift (\c -> let t0 = c; t(i+1) = (ti, ti) in tk.0 .. .0) b
--
-- The value of @tk@ written out as a tree has @2^(k+1) - 1@ nodes, but
-- evaluating the program takes time linear in @k@.
sharedTuple :: Int -> Program
sharedTuple k =
  program "shared" [Port "b" TBool] [Port "o" TBool] [mkTop [("b", TBool)] TBool body]
  where
    tk = var ("t" <> Text.pack (show k))
    f = ELam [("c", TBool)] (ELet False (doublings "t" (var "c") k) (firsts k tk))
    body = lift [TBool] TBool f [var "b"]

-- > long x = let f1 = \v -> v; f(i+1) = \v -> fi (fi v) in lift fk x
--
-- Exponential work without binds, with every binder name @len@ characters
-- long and sharing a prefix, so that comparing two names costs @len@.
longNames :: Int -> Int -> Program
longNames len k = withBody "long" (ELet False (bind1 : fmap bindI [2 .. k]) applied)
  where
    prefix = Text.replicate len "p"
    f i = Name (prefix <> "f" <> Text.pack (show i))
    x = Name (prefix <> "x")
    fTy = TFun (bv 8) (bv 8)
    bind1 = Bind (f (1 :: Int)) fTy (ELam [(x, bv 8)] (EVar x))
    call i e = EApp (EVar (f (i - 1))) [e]
    bindI i = Bind (f i) fTy (ELam [(x, bv 8)] (call i (call i (EVar x))))
    applied = lift [bv 8] (bv 8) (EVar (f k)) [var "x"]

-- | @g(i+1) x = g i (g i x)@ from @g0 x = let v = not x in v@, with @v@
-- named by @len@ repetitions of the letter: @2^k@ binds bound to @v@.
longBinder :: Int -> Int -> Program
longBinder len k = chainProgram k base twice
  where
    v = Name (Text.replicate len "v")
    base = ELam [("x", bv 8)] (ELet False [Bind v (bv 8) (not8 (var "x"))] (EVar v))

-- | A module of @k@ chained @bool.not@ binds, valid for @k <= maxNormalBinds@.
notChain :: Int -> NModule
notChain k =
  NModule
    { nmName = "chain"
    , nmDomain = sysDomain
    , nmInputs = [("en", TBool)]
    , nmOutputs = [NOutput "out" TBool (AVar (b (k - 1)))]
    , nmBinds = [NBind (b i) TBool (NPrim BoolNot [AVar (prev i)]) | i <- [0 .. k - 1]]
    , nmCertificate = testCertificate "Chain.chain_correct"
    }
  where
    b :: Int -> Name
    b i = Name ("b" <> Text.pack (show i))
    prev i = if i == 0 then "en" else b (i - 1)

----------------------------------------------------------------------
-- Inspecting results

normalized :: Program -> IO NModule
normalized p = case normalize p of
  Left e -> fail ("normalize failed: " <> show e)
  Right m -> pure m

shouldFailWith :: (Show a) => Either GinError a -> Text -> Expectation
shouldFailWith r needle = case r of
  Right a -> expectationFailure ("expected an error mentioning " <> show needle <> ": " <> show a)
  Left e -> do
    errStage e `shouldBe` StNormalize
    Text.unpack (errMessage e) `shouldContain` Text.unpack needle

rhsAtoms :: NRhs -> [Atom]
rhsAtoms = \case
  NPrim _ as -> as
  NMux c a b -> [c, a, b]
  NReg _ a -> [a]
  NAtom a -> [a]

-- | Rename binds by first visit in a depth-first walk from the outputs (in
-- port order, operands left to right) and sort them, so modules that differ
-- only in bind names and bind order become equal. Binds the walk does not
-- reach keep their names.
canonical :: NModule -> NModule
canonical m =
  m
    { nmOutputs = [o {noAtom = renameAtom (noAtom o)} | o <- nmOutputs m]
    , nmBinds = sortOn nbName [NBind (rename n) t (renameRhs r) | NBind n t r <- nmBinds m]
    }
  where
    rhss = Map.fromList [(nbName b, nbRhs b) | b <- nmBinds m]
    labels = foldl' visit Map.empty [n | AVar n <- fmap noAtom (nmOutputs m)]
    visit seen n
      | Map.member n seen = seen
      | Just r <- Map.lookup n rhss =
          foldl' visit (Map.insert n (Map.size seen) seen) [x | AVar x <- rhsAtoms r]
      | otherwise = seen
    rename n = maybe n label (Map.lookup n labels)
    label k = Name ("#" <> Text.justifyRight 6 '0' (Text.pack (show (k :: Int))))
    renameAtom = \case
      AVar n -> AVar (rename n)
      a -> a
    renameRhs = \case
      NPrim op as -> NPrim op (fmap renameAtom as)
      NMux c a b -> NMux (renameAtom c) (renameAtom a) (renameAtom b)
      NReg v a -> NReg v (renameAtom a)
      NAtom a -> NAtom (renameAtom a)

-- | @m@ satisfies the normal-form invariants and equals @expected@ up to
-- bind names and bind order.
shouldNormalizeLike :: NModule -> NModule -> Expectation
shouldNormalizeLike m expected = do
  checkNormal m `shouldBe` Right ()
  length (nmBinds m) `shouldBe` length (nmBinds expected)
  canonical m `shouldBe` canonical expected

-- | What drives each output: the right-hand side of its bind, or the atom
-- itself when it is an input or a literal.
drivers :: NModule -> [Either Atom NRhs]
drivers m = fmap (driver . noAtom) (nmOutputs m)
  where
    rhss = Map.fromList [(nbName b, nbRhs b) | b <- nmBinds m]
    driver a = case a of
      AVar n | Just r <- Map.lookup n rhss -> Right r
      _ -> Left a

isReg :: NRhs -> Bool
isReg = \case
  NReg _ _ -> True
  _ -> False

isMux :: NRhs -> Bool
isMux = \case
  NMux {} -> True
  _ -> False

-- | Evaluate the outcome of a normalization within a time limit: 'Nothing'
-- on timeout, otherwise the stage and message of the error, if any.
outcomeWithin :: Int -> Either GinError a -> IO (Maybe (Maybe (Stage, Text)))
outcomeWithin seconds r =
  timeout
    (seconds * 1000000)
    (evaluate (either (\e -> Just (errStage e, errMessage e)) (const Nothing) r))

-- | 'normalized', failing unless normalization finishes within the given
-- number of seconds.
normalizedWithin :: Int -> Program -> IO NModule
normalizedWithin seconds p = do
  r <- timeout (seconds * 1000000) (evaluate (normalize p))
  case r of
    Nothing -> fail ("normalize did not finish within " <> show seconds <> " s")
    Just result -> either (fail . show) pure result

shouldTripLimit :: Program -> Text -> Expectation
shouldTripLimit p needle = do
  outcome <- outcomeWithin 20 (normalize p)
  case outcome of
    Nothing -> expectationFailure "normalize did not finish within 20 s"
    Just Nothing -> expectationFailure "normalize succeeded"
    Just (Just (stage, msg)) -> do
      stage `shouldBe` StNormalize
      Text.unpack msg `shouldContain` Text.unpack needle

----------------------------------------------------------------------
-- checkNormal mutants

setRhs :: Name -> NRhs -> NModule -> NModule
setRhs n r m = m {nmBinds = [if nbName b == n then b {nbRhs = r} else b | b <- nmBinds m]}

-- | One or more mutants of 'counterNormal' per invariant of
-- "Gin.Core.Normal", each violating only that invariant, with a fragment of
-- the expected error message.
mutants :: [(String, Text, NModule)]
mutants =
  [
    ( "1: an input of product type"
    , "not scalar"
    , c {nmInputs = nmInputs c <> [("pad", TProd [TBool, TBool])]}
    )
  , ("1: an input of width zero", "not scalar", c {nmInputs = nmInputs c <> [("pad", bv 0)]})
  , ("2: two inputs with the same name", "duplicate", c {nmInputs = [("en", TBool), ("en", TBool)]})
  , ("2: a bind named like an input", "duplicate", c {nmInputs = [("en", TBool), ("inc", bv 8)]})
  , ("2: two binds with the same name", "duplicate", c {nmBinds = [s, inc, inc, sNext]})
  ,
    ( "3: operands of different widths"
    , "ill-typed"
    , setRhs "inc" (NPrim BvAdd [AVar "s", ALit (VBV 4 1)]) c
    )
  , ("3: a signal prim in a bind", "ill-typed", setRhs "inc" (NPrim SigPure [AVar "s"]) c)
  , ("3: an unsaturated prim", "ill-typed", setRhs "inc" (NPrim BvAdd [AVar "s"]) c)
  ,
    ( "3: a tuple literal"
    , "ill-typed"
    , setRhs "inc" (NPrim BvAdd [AVar "s", ALit (VTuple [VBV 4 0, VBV 4 1])]) c
    )
  ,
    ( "3: a mux condition that is not Bool"
    , "ill-typed"
    , setRhs "s_next" (NMux (AVar "inc") (AVar "inc") (AVar "s")) c
    )
  ,
    ( "3: an output atom of another type"
    , "ill-typed"
    , c {nmOutputs = nmOutputs c <> [NOutput "flag" (bv 8) (AVar "en")]}
    )
  ,
    ( "4: a reference to an unbound name"
    , "undefined variable"
    , setRhs "s_next" (NMux (AVar "en") (AVar "inc") (AVar "ghost")) c
    )
  , ("5: a combinational forward reference", "topological", c {nmBinds = [s, sNext, inc]})
  ,
    ( "5: a combinational cycle"
    , "topological"
    , setRhs "inc" (NPrim BvAdd [AVar "s_next", ALit (VBV 8 1)]) c
    )
  ,
    ( "6: a register initial value of another width"
    , "initial value"
    , setRhs "s" (NReg (VBV 16 0) (AVar "s_next")) c
    )
  ,
    ( "6: an out-of-range register initial value"
    , "initial value"
    , setRhs "s" (NReg (VBV 8 256) (AVar "s_next")) c
    )
  ,
    ( "7: a dead bind"
    , "unreachable"
    , c {nmBinds = nmBinds c <> [NBind "dead" TBool (NPrim BoolNot [AVar "en"])]}
    )
  ,
    ( "7: a copy bind"
    , "copy"
    , c
        { nmOutputs = [NOutput "count" (bv 8) (AVar "cp")]
        , nmBinds = nmBinds c <> [NBind "cp" (bv 8) (NAtom (AVar "s"))]
        }
    )
  , ("8: one bind over the limit", "too many binds", notChain (maxNormalBinds + 1))
  ]
  where
    c = counterNormal
    s = NBind "s" (bv 8) (NReg (VBV 8 0) (AVar "s_next"))
    inc = NBind "inc" (bv 8) (NPrim BvAdd [AVar "s", ALit (VBV 8 1)])
    sNext = NBind "s_next" (bv 8) (NMux (AVar "en") (AVar "inc") (AVar "s"))

----------------------------------------------------------------------

examples :: [(String, Program, NModule)]
examples =
  [ ("counter", counterProgram, counterNormal)
  , ("mac", macProgram, macNormal)
  , ("detector", detectorProgram, detectorNormal)
  ]

spec :: Spec
spec = do
  describe "normalize" $ do
    describe "examples" $ do
      it "[norm-counter] lowers the counter to the hand-written normal form" $ do
        m <- normalized counterProgram
        m `shouldNormalizeLike` counterNormal
      it "[norm-counter] names the state register after the step function's state binder" $ do
        m <- normalized counterProgram
        [nbName b | b <- nmBinds m, isReg (nbRhs b)] `shouldBe` ["s"]
      it "[norm-mac] lowers mac to the hand-written normal form" $ do
        m <- normalized macProgram
        m `shouldNormalizeLike` macNormal
      it "[norm-mac] names binds after the let and lambda binders they come from" $ do
        m <- normalized macProgram
        fmap nbName (nmBinds m) `shouldContain` ["acc"]
        fmap nbName (nmBinds m) `shouldContain` ["acc'"]
      it "[norm-detector] inlines the step helper into one mux per tuple component" $ do
        m <- normalized detectorProgram
        checkNormal m `shouldBe` Right ()
        length (filter (isReg . nbRhs) (nmBinds m)) `shouldBe` 1
        length (filter (isMux . nbRhs) (nmBinds m)) `shouldBe` 6
        m `shouldNormalizeLike` detectorNormal

    describe "recursive let" $ do
      it "[norm-loop] rejects a feedback path without a register as a combinational loop" $
        normalize (recCounter False) `shouldFailWith` "combinational loop"
      it "[norm-loop] rejects a binding defined as itself" $ do
        let selfLoop = ELet True [Bind "c" (sig (bv 8)) (var "c")] (var "c")
        normalize (withBody "self" selfLoop) `shouldFailWith` "combinational loop"
      it "[norm-loop] rejects mutual recursion without a register" $
        normalize (mutualRec False) `shouldFailWith` "combinational loop"
      it "[norm-loop] accepts feedback broken by sig.register" $ do
        m <- normalized (recCounter True)
        m `shouldNormalizeLike` recCounterNormal
      it "[norm-loop] accepts mutual recursion broken by sig.register" $ do
        m <- normalized (mutualRec True)
        checkNormal m `shouldBe` Right ()
        fmap nbRhs (nmBinds m) `shouldSatisfy` any isReg
        length (nmBinds m) `shouldBe` 2
      it "[norm-loop] rejects a recursive let that binds a function" $ do
        let f = ELam [("z", bv 8)] (EApp (var "f") [var "z"])
            applied = lift [bv 8] (bv 8) (var "f") [var "x"]
            body = ELet True [Bind "f" (TFun (bv 8) (bv 8)) f] applied
        normalize (withBody "recfun" body) `shouldFailWith` "function"
      it "[norm-loop] handles a top entity with no inputs" $ do
        m <- normalized freeCounter
        let c = AVar "c"
        m
          `shouldNormalizeLike` normalForm
            "free"
            []
            [NOutput "count" (bv 8) c]
            [ NBind "c" (bv 8) (NReg (VBV 8 0) (AVar "n"))
            , NBind "n" (bv 8) (NPrim BvAdd [c, ALit (VBV 8 1)])
            ]

    describe "lowering" $ do
      it "lowers a tuple-valued mealy state to one register per component" $ do
        m <- normalized fibProgram
        m `shouldNormalizeLike` fibNormal
      it "lowers a tuple-valued register to one register per component" $ do
        m <- normalized pairRegister
        m `shouldNormalizeLike` pairRegisterNormal
      it "selects the branch of an if with a literal condition without a mux" $ do
        let add k = bin8 BvAdd (var "a") (lit8 k)
            f = ELam [("a", bv 8)] (EIf (ELit (VBool True)) (add 1) (add 2))
        m <- normalized (pointwise "litif" f)
        fmap nbRhs (nmBinds m) `shouldBe` [NPrim BvAdd [AVar "x", ALit (VBV 8 1)]]
      it "saturates a partially applied prim" $ do
        m <- normalized (pointwise "partial" (EApp (prim BvAdd [bv 8, bv 8] (bv 8)) [lit8 1]))
        checkNormal m `shouldBe` Right ()
        drivers m `shouldBe` [Right (NPrim BvAdd [ALit (VBV 8 1), AVar "x"])]
      it "keeps bound names distinct from input names that source binders reuse" $ do
        let inc = lift [bv 8] (bv 8) (addK 1) [var "y"]
            body = ELam [("y", sig (bv 8))] (ELet False [Bind "x" (sig (bv 8)) inc] (var "x"))
        m <- normalized (withTop "names" sigFun8 body)
        checkNormal m `shouldBe` Right ()
        nmInputs m `shouldBe` [("x", bv 8)]
        fmap nbName (nmBinds m) `shouldNotContain` ["x"]
        drivers m `shouldBe` [Right (NPrim BvAdd [AVar "x", ALit (VBV 8 1)])]
      it "names tuple components after their binder, with bounded names for deep nesting" $ do
        shallow <- normalized (deepRegister 2)
        nmBinds shallow `shouldBe` [NBind "r_1_1" TBool (NReg (VBool False) (AVar "x"))]
        deep <- normalized (deepRegister 200)
        checkNormal deep `shouldBe` Right ()
        fmap nbRhs (nmBinds deep) `shouldBe` [NReg (VBool False) (AVar "x")]
        fmap (Text.length . unName . nbName) (nmBinds deep) `shouldSatisfy` all (<= 80)
      it "names binds after long source binders with a bounded prefix of the binder" $ do
        m <- normalized (longBinder 1000 4)
        checkNormal m `shouldBe` Right ()
        length (nmBinds m) `shouldBe` 16
        fmap (Text.take 8 . unName . nbName) (nmBinds m) `shouldSatisfy` all (== "vvvvvvvv")
        fmap (Text.length . unName . nbName) (nmBinds m) `shouldSatisfy` all (<= 80)

    describe "unsupported programs" $ do
      it "rejects an if whose branches carry functions" $ do
        let branch k = ETuple [addK k, lit8 k]
            pairIf = EIf (eq8 (var "a") (lit8 0)) (branch 1) (branch 2)
            f = ELam [("a", bv 8)] (EApp (EProj 0 pairIf) [var "a"])
        normalize (pointwise "fnif" f) `shouldFailWith` "function"
      it "rejects a function where an output port expects a scalar" $ do
        let adder = ELam [("a", bv 8)] (ELam [("b", bv 8)] (bin8 BvAdd (var "a") (var "b")))
            fnTy = TFun (bv 8) (bv 8)
            body = ELam [("x", sig (bv 8))] (lift [bv 8] fnTy adder [var "x"])
        normalize (withTop "fnout" (TFun (sig (bv 8)) (sig fnTy)) body) `shouldFailWith` "output"
      it "rejects a reference to an unknown global" $
        normalize (pointwise "unknown" (EGlobal "Test.missing")) `shouldFailWith` "unknown global"
      it "rejects a recursive global instead of looping" $ do
        normalize (withTop "recglobal" sigFun8 (EGlobal "Test.top")) `shouldFailWith` "recursive"
      it "reports the binding and the definitions an error comes from, innermost first" $ do
        let branch k = ETuple [addK k, lit8 k]
            bad = EIf (eq8 (var "a") (lit8 0)) (branch 1) (branch 2)
            badTy = TProd [TFun (bv 8) (bv 8), bv 8]
            helper = ELam [("a", bv 8)] (ELet False [Bind "bad" badTy bad] (var "a"))
            p = pointwise "where" (EGlobal "Test.helper")
            r = normalize p {progDefs = Def "Test.helper" (TFun (bv 8) (bv 8)) helper : progDefs p}
        r `shouldFailWith` "function"
        either (Just . errContext) (const Nothing) r
          `shouldBe` Just
            ["in bind bad", "in def Test.helper", "in def Test.top", "in top entity where"]

    describe "determinism" $ do
      it "[norm-determinism] gives identical output for equal programs" $
        for_ (twoOutputs : fibProgram : [p | (_, p, _) <- examples]) $ \p -> do
          let rebuilt = p {progDefs = [Def (defName d) (defTy d) (defBody d) | d <- progDefs p]}
          normalize rebuilt `shouldBe` normalize p
      it "[norm-determinism] does not depend on the order of definitions" $ do
        let p = detectorProgram
        normalize p {progDefs = reverse (progDefs p)} `shouldBe` normalize p

    describe "limits" $ do
      it "[norm-limit] stops exponential inlining once it exceeds maxNormalBinds" $
        shouldTripLimit (nestedChain 40) (Text.pack (show maxNormalBinds))
      it "[norm-limit] counts binds that duplicate earlier ones while inlining" $
        shouldTripLimit (sharedChain 60) (Text.pack (show maxNormalBinds))
      it "[norm-limit] bounds exponential inlining that emits no binds" $
        shouldTripLimit (identityChain 60) "steps"
      it "[norm-limit] charges work on wide tuples to the evaluation budget" $
        shouldTripLimit (wideChain 60) "steps"
      it "[norm-limit] accepts a program with exactly maxNormalBinds binds" $ do
        m <- normalized (nestedChain 16)
        length (nmBinds m) `shouldBe` maxNormalBinds
        checkNormal m `shouldBe` Right ()
      it "[norm-limit] rejects a program with one level more" $
        shouldTripLimit (nestedChain 17) (Text.pack (show maxNormalBinds))
      it "[norm-limit] charges evaluation steps at a cost independent of name length" $
        shouldTripLimit (longNames 100000 24) "steps"
      it "[norm-limit] lowers a deeply nested mealy state in time linear in its depth" $ do
        r <- timeout (10 * 1000000) (evaluate (normalize (deepMealy 50000)))
        case r of
          Nothing -> expectationFailure "normalize did not finish within 10 s"
          Just result -> do
            m <- either (fail . show) pure result
            nmBinds m `shouldBe` []
            nmOutputs m `shouldBe` [NOutput "o" TBool (AVar "b")]
      it "[norm-limit] names a tuple shared at every level in time linear in its depth" $ do
        m <- normalizedWithin 10 (sharedTuple 40)
        nmBinds m `shouldBe` []
        nmOutputs m `shouldBe` [NOutput "o" TBool (AVar "b")]

    describe "multiple outputs" $ do
      it "[norm-multi-output] reads two outputs in port order" $ do
        m <- normalized twoOutputs
        checkNormal m `shouldBe` Right ()
        fmap noName (nmOutputs m) `shouldBe` ["sum", "diff"]
        drivers m
          `shouldBe` [ Right (NPrim BvAdd [AVar "x", AVar "y"])
                     , Right (NPrim BvSub [AVar "x", AVar "y"])
                     ]
      it "[norm-multi-output] reads three outputs along the right-nested product" $ do
        m <- normalized (threeOutputs False)
        checkNormal m `shouldBe` Right ()
        fmap noName (nmOutputs m) `shouldBe` ["sum", "same", "first"]
        fmap noTy (nmOutputs m) `shouldBe` [bv 8, TBool, bv 8]
        drivers m
          `shouldBe` [ Right (NPrim BvAdd [AVar "x", AVar "y"])
                     , Right (NPrim BvEq [AVar "x", AVar "y"])
                     , Left (AVar "x")
                     ]
      it "[norm-multi-output] rejects a flat triple for three outputs" $
        normalize (threeOutputs True) `shouldFailWith` "output"

  describe "checkNormal" $ do
    for_ examples $ \(name, _, nm) ->
      it ("accepts the " <> name <> " fixture") $
        checkNormal nm `shouldBe` Right ()
    it "accepts exactly maxNormalBinds binds" $
      checkNormal (notChain maxNormalBinds) `shouldBe` Right ()
    for_ mutants $ \(name, needle, m) ->
      it ("[norm-mutants] rejects invariant " <> name) $
        checkNormal m `shouldFailWith` needle
