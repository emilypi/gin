module Gin.Core.JsonSpec (spec) where

import Control.Monad (void)
import Data.Aeson qualified as A
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap qualified as KeyMap
import Data.ByteString.Lazy qualified as LBS
import Data.ByteString.Lazy.Char8 qualified as LBS8
import Data.Char (isSpace)
import Data.Foldable (for_, toList)
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Core.Json
import Gin.Core.Syntax
import Gin.Error
import Gin.Examples
import Gin.Limits
import Gin.Vectors
import Numeric.Natural (Natural)
import System.Timeout (timeout)
import Test.Hspec
import Test.QuickCheck

----------------------------------------------------------------------
-- Generators: syntactically valid programs and vectors. They need not
-- type-check; the codec does not look at typing.

genText :: Gen Text
genText =
  frequency
    [ (4, Text.pack <$> listOf (elements "abcxyz_.019"))
    , (2, Text.pack <$> arbitrary)
    , (1, elements ["", "\"", "\\", "\n\t", "\0", "é", "日本", "\x1F600", "</script>"])
    ]

genName :: Gen Name
genName = Name <$> genText

-- | A natural number that fits the JSON number bound.
genNat :: Gen Natural
genNat =
  fromInteger
    <$> frequency
      [(6, chooseInteger (0, 16)), (1, pure maxJsonNumber), (1, chooseInteger (0, maxJsonNumber))]

genWidth :: Gen Natural
genWidth =
  fromInteger
    <$> frequency
      [(6, chooseInteger (1, 64)), (1, pure 1), (1, pure 4096), (1, chooseInteger (1, 4096))]

listAtLeast :: Int -> Gen a -> Gen [a]
listAtLeast n g = sized $ \s -> do
  k <- chooseInt (n, n + min 3 s)
  vectorOf k g

genTy :: Int -> Gen Ty
genTy depth
  | depth <= 0 = scalar
  | otherwise =
      frequency
        [ (3, scalar)
        , (1, TProd <$> listAtLeast 2 sub)
        , (1, TFun <$> sub <*> sub)
        , (1, TSignal <$> genText <*> sub)
        ]
  where
    scalar = oneof [pure TBool, TBitVec <$> genWidth]
    sub = genTy (depth `div` 2)

-- | A valid value of the given data type.
genValueOf :: Ty -> Gen Value
genValueOf = \case
  TBitVec w -> do
    let top = 2 ^ w - 1
    VBV w <$> frequency [(1, pure 0), (1, pure top), (4, chooseInteger (0, top))]
  TProd ts -> VTuple <$> traverse genValueOf ts
  _ -> VBool <$> arbitrary

genDataTy :: Int -> Gen Ty
genDataTy depth
  | depth <= 0 = scalar
  | otherwise = frequency [(3, scalar), (1, TProd <$> listAtLeast 2 (genDataTy (depth `div` 2)))]
  where
    scalar = oneof [pure TBool, TBitVec <$> genWidth]

genValue :: Gen Value
genValue = genDataTy 4 >>= genValueOf

genPrimOp :: Gen PrimOp
genPrimOp =
  oneof
    [ elements
        [ BoolAnd
        , BoolOr
        , BoolXor
        , BoolNot
        , BoolEq
        , BvAdd
        , BvSub
        , BvMul
        , BvNeg
        , BvAnd
        , BvOr
        , BvXor
        , BvNot
        , BvEq
        , BvUlt
        , BvUle
        , BvConcat
        , BvOfBool
        , SigPure
        ]
    , BvShl <$> genNat
    , BvLshr <$> genNat
    , BvExtract <$> genNat <*> genNat
    , BvZext <$> genWidth
    , SigLift <$> genNat
    , SigRegister <$> genValue
    , SigMealy <$> genValue
    ]

genExpr :: Int -> Gen Expr
genExpr depth
  | depth <= 0 = leaf
  | otherwise =
      frequency
        [ (3, leaf)
        , (2, EApp <$> sub <*> listAtLeast 1 sub)
        , (1, ELam <$> listAtLeast 1 ((,) <$> genName <*> ty) <*> sub)
        , (1, ELet <$> arbitrary <*> listAtLeast 0 (Bind <$> genName <*> ty <*> sub) <*> sub)
        , (1, ETuple <$> listAtLeast 2 sub)
        , (1, EProj <$> genNat <*> sub)
        , (1, EIf <$> sub <*> sub <*> sub)
        ]
  where
    sub = genExpr (depth `div` 2)
    ty = genTy 3
    leaf =
      oneof
        [ EVar <$> genName
        , EGlobal <$> genName
        , ELit <$> genValue
        , EPrim <$> genPrimOp <*> genTy 4
        ]

genPort :: Gen Port
genPort = Port <$> genText <*> genTy 3

genProgram :: Gen Program
genProgram = do
  producer <- Producer <$> genText <*> genText
  top <-
    TopEntity
      <$> genText
      <*> (Domain <$> genText <*> genNat)
      <*> listOf genPort
      <*> listOf genPort
      <*> genName
  defs <- listOf (Def <$> genName <*> genTy 4 <*> genExpr 12)
  certificate <-
    Certificate <$> genText <*> genText <*> listOf genText <*> listOf genText
  pure (Program producer top defs certificate)

-- | Vectors within the payload bound (cycles times summed port widths).
genVectors :: Gen Vectors
genVectors = gen `suchThat` withinPayload
  where
    gen = do
      ins <- resize 6 (listOf (Port <$> genText <*> genDataTy 1))
      outs <- resize 6 (listOf (Port <$> genText <*> genDataTy 1))
      let row = traverse (genValueOf . portTy)
      n <- chooseInt (1, 12)
      cycles <- vectorOf n (Cycle <$> row ins <*> row outs)
      top <- genText
      pure (Vectors top ins outs cycles)
    withinPayload vs =
      toInteger (length (vecCycles vs)) * sum (fmap (bits . portTy) (vecInputs vs <> vecOutputs vs))
        <= maxVectorBits
    bits = \case
      TBitVec w -> toInteger w
      TProd ts -> sum (fmap bits ts)
      _ -> 1

----------------------------------------------------------------------
-- JSON surgery on encoded documents

data Step = K Text | I Int

modifyAt :: [Step] -> (A.Value -> A.Value) -> A.Value -> A.Value
modifyAt path f = case path of
  [] -> f
  K k : rest -> \case
    A.Object o ->
      let key = Key.fromText k
       in A.Object (maybe o (\x -> KeyMap.insert key (modifyAt rest f x) o) (KeyMap.lookup key o))
    other -> other
  I i : rest -> \case
    A.Array a ->
      A.toJSON [if j == i then modifyAt rest f x else x | (j, x) <- zip [0 ..] (toList a)]
    other -> other

setAt :: [Step] -> A.Value -> A.Value -> A.Value
setAt path new = modifyAt path (const new)

-- | Insert or replace a key in the object at the path.
insertAt :: [Step] -> Text -> A.Value -> A.Value -> A.Value
insertAt path k new = modifyAt path $ \case
  A.Object o -> A.Object (KeyMap.insert (Key.fromText k) new o)
  other -> other

deleteAt :: [Step] -> Text -> A.Value -> A.Value
deleteAt path k = modifyAt path $ \case
  A.Object o -> A.Object (KeyMap.delete (Key.fromText k) o)
  other -> other

asJson :: LBS.ByteString -> A.Value
asJson = fromMaybe A.Null . A.decode

counterJson :: A.Value
counterJson = asJson (encodeProgram counterProgram)

counterVectorsJson :: A.Value
counterVectorsJson = asJson (encodeVectors counterVectors)

-- Paths into counterJson.
bodyPath, mealyApp, mealyPrim, stepLam, ifExpr, addApp, addPrim, oneLit, outType :: [Step]
bodyPath = [K "defs", I 0, K "body"]
mealyApp = bodyPath <> [K "body"]
mealyPrim = mealyApp <> [K "fun"]
stepLam = mealyApp <> [K "args", I 0]
ifExpr = stepLam <> [K "body", K "elems", I 0]
addApp = ifExpr <> [K "then"]
addPrim = addApp <> [K "fun"]
oneLit = addApp <> [K "args", I 1]
outType = [K "top", K "outputs", I 0, K "type"]

-- | The first output value of a cycle in counterVectorsJson.
cycleOut :: Int -> [Step]
cycleOut t = [K "cycles", I t, K "out", I 0]

noValues :: [A.Value]
noValues = []

spaces :: Int -> LBS.ByteString
spaces n = LBS8.replicate (fromIntegral n) ' '

bvValue :: Integer -> Text -> A.Value
bvValue w s = A.object ["bv" A..= w, "val" A..= s]

----------------------------------------------------------------------
-- Expectations

-- | A decode error whose rendering (message and location) mentions the
-- fragment, ignoring case.
decodeErrorWith :: Text -> Either GinError a -> Expectation
decodeErrorWith fragment = \case
  Left e -> do
    errStage e `shouldBe` StDecode
    Text.unpack (Text.toLower (renderError e)) `shouldContain` Text.unpack (Text.toLower fragment)
  Right _ -> expectationFailure "expected a decode error, but decoding succeeded"

rejectsProgram :: Text -> A.Value -> Expectation
rejectsProgram fragment = decodeErrorWith fragment . decodeProgram . A.encode

rejectsVectors :: Text -> A.Value -> Expectation
rejectsVectors fragment = decodeErrorWith fragment . decodeVectors . A.encode

-- | The limit is checked before the work it guards: the decoder answers
-- in well under the time the guarded work would take.
promptly :: Expectation -> Expectation
promptly act =
  timeout 5000000 act >>= \case
    Just () -> pure ()
    Nothing -> expectationFailure "decoding took longer than 5 s"

-- | Nest a value inside @n@ singleton arrays.
nested :: Int -> LBS.ByteString -> LBS.ByteString
nested n inner = LBS8.replicate (fromIntegral n) '[' <> inner <> LBS8.replicate (fromIntegral n) ']'

-- | The counter program with raw JSON text spliced in as the value of an
-- extra, ignored key. Bypasses aeson so the text can be anything.
withRawKey :: LBS.ByteString -> LBS.ByteString
withRawKey raw = case LBS8.uncons (encodeProgram counterProgram) of
  Just ('{', rest) -> "{\"x-extra\":" <> raw <> "," <> rest
  _ -> ""

-- | Vectors with a single @bv 4096@ input and no outputs.
wideVectors :: Int -> LBS.ByteString
wideVectors n =
  A.encode $
    A.object
      [ "format" A..= ("gin-vectors/1" :: Text)
      , "top" A..= ("wide" :: Text)
      , "inputs" A..= [A.object ["name" A..= ("x" :: Text), "type" A..= wideTy]]
      , "outputs" A..= noValues
      , "cycles" A..= replicate n (A.object ["in" A..= [bvValue 4096 "0"], "out" A..= noValues])
      ]
  where
    wideTy = A.object ["t" A..= ("bv" :: Text), "width" A..= (4096 :: Int)]

-- | Vectors with no ports and @n@ empty rows.
emptyRows :: Int -> LBS.ByteString
emptyRows n =
  "{\"format\":\"gin-vectors/1\",\"top\":\"t\",\"inputs\":[],\"outputs\":[],\"cycles\":["
    <> LBS.intercalate "," (replicate n "{\"in\":[],\"out\":[]}")
    <> "]}"

----------------------------------------------------------------------

spec :: Spec
spec = do
  describe "round trip" $ do
    it "[json-roundtrip] decodeProgram . encodeProgram is Right on generated programs" $
      forAll genProgram $
        \p -> decodeProgram (encodeProgram p) === Right p
    it "[json-roundtrip] decodeVectors . encodeVectors is Right on generated vectors" $
      forAll genVectors $
        \vs -> decodeVectors (encodeVectors vs) === Right vs
    for_ [("counter", counterProgram), ("mac", macProgram), ("detector", detectorProgram)] $
      \(name, p) ->
        it ("[json-roundtrip] round-trips the " <> name <> " program") $
          decodeProgram (encodeProgram p) `shouldBe` Right p
    for_ [("counter", counterVectors), ("mac", macVectors), ("detector", detectorVectors)] $
      \(name, vs) ->
        it ("[json-roundtrip] round-trips the " <> name <> " vectors") $
          decodeVectors (encodeVectors vs) `shouldBe` Right vs
    it "[json-roundtrip] re-encoding a decoded document reproduces the canonical encoding" $
      forAll genProgram $ \p ->
        let bytes = encodeProgram p in fmap encodeProgram (decodeProgram bytes) === Right bytes
    it "[json-roundtrip] encodes the counter program canonically" $ do
      expected <- LBS.readFile "test/fixtures/ir/counter.canonical.json"
      encodeProgram counterProgram `shouldBe` LBS8.dropWhileEnd isSpace expected
    it "[json-roundtrip] encodes the counter vectors canonically" $ do
      expected <- LBS.readFile "test/fixtures/ir/counter.vectors.canonical.json"
      encodeVectors counterVectors `shouldBe` LBS8.dropWhileEnd isSpace expected

  describe "counter fixture" $ do
    it "[json-counter-fixture] decodes to counterProgram" $ do
      bytes <- LBS.readFile "test/fixtures/ir/counter.gin.json"
      decodeProgram bytes `shouldBe` Right counterProgram
    it "[json-counter-fixture] re-encodes to the canonical counter encoding" $ do
      bytes <- LBS.readFile "test/fixtures/ir/counter.gin.json"
      fmap encodeProgram (decodeProgram bytes) `shouldBe` Right (encodeProgram counterProgram)

  describe "decoding rules" $ do
    it "[json-reject] accepts the unmodified counter document" $
      decodeProgram (A.encode counterJson) `shouldBe` Right counterProgram
    it "[json-reject] ignores unknown keys at every level" $ do
      let extra = A.String "ignored"
          doc =
            insertAt [] "comment" extra
              . insertAt [K "top"] "x" extra
              . insertAt outType "x" extra
              . insertAt addPrim "x" extra
              . insertAt (oneLit <> [K "value"]) "x" extra
              . insertAt [K "certificate"] "x" extra
              $ counterJson
      decodeProgram (A.encode doc) `shouldBe` Right counterProgram
    it "[json-reject] accepts omitted params on a primitive without parameters" $
      decodeProgram (A.encode (deleteAt addPrim "params" counterJson))
        `shouldBe` Right counterProgram
    it "[json-reject] rejects a format tag other than gin-ir/1" $ do
      rejectsProgram "gin-ir/1" (setAt [K "format"] (A.String "gin-ir/2") counterJson)
      rejectsProgram "gin-ir/1" (setAt [K "format"] (A.String "gin-vectors/1") counterJson)
    for_
      [ ("format", [])
      , ("producer", [])
      , ("leanVersion", [K "producer"])
      , ("top", [])
      , ("name", [K "top"])
      , ("periodPs", [K "top", K "domain"])
      , ("inputs", [K "top"])
      , ("def", [K "top"])
      , ("defs", [])
      , ("body", [K "defs", I 0])
      , ("certificate", [])
      , ("implAxioms", [K "certificate"])
      , ("width", outType)
      , ("binders", bodyPath)
      , ("args", mealyApp)
      , ("type", mealyPrim)
      , ("val", oneLit <> [K "value"])
      ]
      $ \(key, path) ->
        it ("[json-reject] rejects a missing required key " <> show key) $
          rejectsProgram key (deleteAt path key counterJson)
    for_
      [ ("a string width", outType <> [K "width"], A.String "8")
      , ("a numeric name", [K "top", K "name"], A.Number 7)
      , ("an object for a list", [K "defs"], A.object [])
      , ("null for an expression", oneLit, A.Null)
      , ("an array for the top entity", [K "top"], A.toJSON [A.Null])
      , ("a non-object for params", addPrim <> [K "params"], A.toJSON [A.Null])
      , ("a non-string axiom", [K "certificate", K "axioms"], A.toJSON [A.Bool True])
      ]
      $ \(name, path, new) ->
        it ("[json-reject] rejects " <> name) $
          rejectsProgram "expected" (setAt path new counterJson)
    it "[json-reject] rejects a string flag for let rec" $
      rejectsProgram "rec" $
        setAt
          bodyPath
          ( A.object
              [ "e" A..= ("let" :: Text)
              , "rec" A..= ("yes" :: Text)
              , "binds" A..= noValues
              , "body" A..= varS
              ]
          )
          counterJson
    it "[json-reject] rejects an unknown type tag" $
      rejectsProgram "bits" (setAt (outType <> [K "t"]) (A.String "bits") counterJson)
    it "[json-reject] rejects an unknown expression tag" $
      rejectsProgram "lambda" (setAt (bodyPath <> [K "e"]) (A.String "lambda") counterJson)
    it "[json-reject] rejects an unknown primitive" $
      rejectsProgram "bv.div" (setAt (addPrim <> [K "op"]) (A.String "bv.div") counterJson)
    it "[json-reject] rejects an unknown value shape" $
      rejectsProgram
        "value"
        (setAt (oneLit <> [K "value"]) (A.object ["bits" A..= (3 :: Int)]) counterJson)
    for_ [0, 4097 :: Integer] $ \w -> do
      it ("[json-reject] rejects a type of width " <> show w) $
        rejectsProgram "width" (setAt (outType <> [K "width"]) (A.toJSON w) counterJson)
      it ("[json-reject] rejects a value of width " <> show w) $
        rejectsProgram "width" (setAt (oneLit <> [K "value"]) (bvValue w "0") counterJson)
      it ("[json-reject] rejects bv.zext to width " <> show w) $
        rejectsProgram "width" (setAt addPrim (zextPrim w) counterJson)
    it "[json-reject] accepts the width bounds 1 and 4096" $
      for_ [1, 4096 :: Integer] $ \w ->
        decodeProgram (A.encode (setAt (outType <> [K "width"]) (A.toJSON w) counterJson))
          `shouldSatisfy` either (const False) (const True)
    it "[json-reject] rejects a negative number" $ do
      rejectsProgram "negative" (setAt (outType <> [K "width"]) (A.Number (-1)) counterJson)
      decodeErrorWith "negative" (decodeProgram (withRawKey "-0"))
    it "[json-reject] rejects a non-integral number" $ do
      rejectsProgram "integral" (setAt (outType <> [K "width"]) (A.Number 8.5) counterJson)
      decodeErrorWith "integral" (decodeProgram (withRawKey "1e-1"))
    it "[json-reject] accepts an integral number written with a fraction or exponent" $
      decodeProgram (LBS8.pack (substitute "\"periodPs\":10000" "\"periodPs\":1.0e4" counterText))
        `shouldBe` Right counterProgram
    for_ ["", "01", "00", "+1", "-1", "1.0", " 1", "1 ", "1e2", "0x10", "١", "1_000"] $ \s ->
      it ("[json-reject] rejects the non-canonical decimal " <> show s) $
        rejectsProgram "decimal" (setAt (oneLit <> [K "value"]) (bvValue 8 s) counterJson)
    it "[json-reject] rejects a value out of range for its width" $ do
      rejectsProgram "range" (setAt (oneLit <> [K "value"]) (bvValue 8 "256") counterJson)
      rejectsProgram "range" (setAt (oneLit <> [K "value"]) (bvValue 1 "2") counterJson)
    it "[json-reject] accepts the largest value for a width" $
      decodeProgram (A.encode (setAt (oneLit <> [K "value"]) (bvValue 8 "255") counterJson))
        `shouldSatisfy` either (const False) (const True)
    it "[json-reject] rejects a one-component product type" $
      rejectsProgram "elems" $
        setAt outType (A.object ["t" A..= ("prod" :: Text), "elems" A..= [boolTy]]) counterJson
    it "[json-reject] rejects an empty product type" $
      rejectsProgram "elems" $
        setAt outType (A.object ["t" A..= ("prod" :: Text), "elems" A..= noValues]) counterJson
    it "[json-reject] rejects a one-component tuple value" $
      rejectsProgram "tuple" $
        setAt (oneLit <> [K "value"]) (A.object ["tuple" A..= [A.Bool True]]) counterJson
    it "[json-reject] rejects a one-component tuple expression" $
      rejectsProgram "elems" $
        modifyAt (stepLam <> [K "body", K "elems"]) (const (A.toJSON [varS])) counterJson
    it "[json-reject] rejects an application with no arguments" $
      rejectsProgram "args" (setAt (mealyApp <> [K "args"]) (A.toJSON noValues) counterJson)
    it "[json-reject] rejects a lambda with no binders" $
      rejectsProgram
        "binders"
        (setAt (bodyPath <> [K "binders"]) (A.toJSON noValues) counterJson)
    it "[json-reject] rejects a primitive missing a required parameter" $ do
      rejectsProgram "init" (deleteAt mealyPrim "params" counterJson)
      rejectsProgram "lo" $
        setAt
          addPrim
          ( A.object
              [ "e" A..= ("prim" :: Text)
              , "op" A..= ("bv.extract" :: Text)
              , "type" A..= boolTy
              , "params" A..= A.object ["hi" A..= (3 :: Int)]
              ]
          )
          counterJson
    it "[json-reject] rejects malformed JSON" $ do
      decodeErrorWith "invalid JSON" (decodeProgram "")
      decodeErrorWith "invalid JSON" (decodeProgram "{")
      decodeErrorWith "invalid JSON" (decodeProgram "{\"format\": }")
      decodeErrorWith "invalid JSON" (decodeProgram "{'format': 'gin-ir/1'}")
      decodeErrorWith "invalid JSON" (decodeVectors "[1,]")
    it "[json-reject] rejects invalid UTF-8 in a string" $
      decodeErrorWith "invalid JSON" (decodeProgram (withRawKey "\"\xff\xfe\""))
    it "[json-reject] rejects trailing data after the document" $
      decodeErrorWith "trailing" (decodeProgram (encodeProgram counterProgram <> " {}"))
    it "[json-reject] rejects a top-level value that is not an object" $ do
      decodeErrorWith "expected Object" (decodeProgram "[]")
      decodeErrorWith "expected Object" (decodeProgram "\"gin-ir/1\"")
    it "[json-reject] reports where in the document decoding failed" $
      case decodeProgram (A.encode (setAt (outType <> [K "width"]) (A.Number 0) counterJson)) of
        Left e -> errContext e `shouldBe` ["at $.top.outputs[0].type.width"]
        Right _ -> expectationFailure "expected a decode error"
    it "[json-reject] never crashes on truncated or corrupted documents" $
      forAll (corrupt (encodeProgram counterProgram)) $ \bytes ->
        let rendered = either (Text.unpack . renderError) show (decodeProgram bytes)
         in length rendered `seq` True

  describe "resource limits" $ do
    it "[json-limits] rejects a program larger than 16 MiB" $
      promptly $
        decodeErrorWith "16777216" $
          decodeProgram (encodeProgram counterProgram <> spaces maxInputBytes)
    it "[json-limits] rejects vectors larger than 16 MiB" $
      promptly $
        decodeErrorWith "16777216" $
          decodeVectors (encodeVectors counterVectors <> spaces maxInputBytes)
    it "[json-limits] accepts a program of exactly 16 MiB" $ promptly $ do
      let bytes = encodeProgram counterProgram
          padding = fromIntegral maxInputBytes - LBS.length bytes
      decodeProgram (bytes <> LBS8.replicate padding ' ') `shouldBe` Right counterProgram
    it "[json-limits] rejects nesting deeper than 4096" $ promptly $ do
      decodeErrorWith "depth" (decodeProgram (withRawKey (nested 4096 "0")))
      decodeErrorWith "depth" (decodeProgram (nested 4097 ""))
      decodeErrorWith "depth" (decodeVectors (nested 4097 ""))
    it "[json-limits] rejects a deeply nested document without parsing it" $
      promptly $
        decodeErrorWith "depth" (decodeProgram (nested 1000000 ""))
    it "[json-limits] accepts nesting of exactly 4096" $
      decodeProgram (withRawKey (nested 4095 "0")) `shouldBe` Right counterProgram
    it "[json-limits] rejects a number above 2^31 - 1" $ promptly $ do
      rejectsProgram
        "2147483647"
        (setAt [K "top", K "domain", K "periodPs"] (A.Number 2147483648) counterJson)
      decodeErrorWith "2147483647" (decodeProgram (withRawKey "2147483648"))
    it "[json-limits] accepts the number 2^31 - 1" $
      fmap
        (domainPeriodPs . topDomain . progTop)
        ( decodeProgram
            (A.encode (setAt [K "top", K "domain", K "periodPs"] (A.Number 2147483647) counterJson))
        )
        `shouldBe` Right 2147483647
    it "[json-limits] rejects a number with a huge exponent without expanding it" $ promptly $ do
      decodeErrorWith "number" (decodeProgram (withRawKey "1e1000000000"))
      decodeErrorWith "number" (decodeProgram (withRawKey "1e999999999"))
      decodeErrorWith "number" (decodeProgram (withRawKey "1E+18446744073709551616"))
      decodeErrorWith "number" (decodeProgram (withRawKey "1e-1000000000"))
    -- Unguarded, aeson's tokenizer spends seconds converting such literals.
    it "[json-limits] rejects a number with a huge mantissa without parsing it" $ promptly $ do
      let digits = 16000000
      decodeErrorWith "number" (decodeProgram (withRawKey ("1" <> LBS8.replicate digits '0')))
      decodeErrorWith "number" (decodeProgram (withRawKey ("1." <> LBS8.replicate digits '7')))
      let tiny = "0." <> LBS8.replicate digits '0' <> "1"
      decodeErrorWith "number" (decodeProgram (withRawKey tiny))
    it "[json-limits] rejects a decimal string longer than 1234 digits" $ promptly $ do
      let long = Text.cons '1' (Text.replicate 1234 "0")
      rejectsProgram "1234" (setAt (oneLit <> [K "value"]) (bvValue 4096 long) counterJson)
      let huge = Text.cons '1' (Text.replicate 1000000 "0")
      rejectsProgram "1234" (setAt (oneLit <> [K "value"]) (bvValue 4096 huge) counterJson)
    it "[json-limits] accepts the largest 4096-bit value (1234 digits)" $ do
      let largest = 2 ^ (4096 :: Int) - 1 :: Integer
          digits = Text.pack (show largest)
      Text.length digits `shouldBe` maxDecimalDigits
      let doc = setAt (oneLit <> [K "value"]) (bvValue 4096 digits) counterJson
      void (decodeProgram (A.encode doc)) `shouldBe` Right ()
    it "[json-limits] rejects a duplicate key" $ promptly $ do
      decodeErrorWith "duplicate key \"format\"" $
        decodeProgram ("{\"format\":\"gin-ir/1\"," <> LBS.drop 1 (encodeProgram counterProgram))
      decodeErrorWith "duplicate key \"width\"" $
        decodeProgram (LBS8.pack (substitute "\"width\":8}" "\"width\":8,\"width\":0}" counterText))
      decodeErrorWith "duplicate key \"width\"" $
        decodeProgram (LBS8.pack (substitute "\"width\":8}" "\"width\":0,\"width\":8}" counterText))
      decodeErrorWith "duplicate key \"x\"" (decodeProgram (withRawKey "{\"x\":1,\"y\":2,\"x\":1}"))
    it "[json-limits] rejects a vector payload above 2^18 bits before decoding rows" $
      promptly $ do
        decodeErrorWith "262144" (decodeVectors (wideVectors 65))
        decodeErrorWith "262144" (decodeVectors (wideVectors maxCycles))
    it "[json-limits] accepts a vector payload of exactly 2^18 bits" $
      fmap (length . vecCycles) (decodeVectors (wideVectors 64)) `shouldBe` Right 64

  describe "vector decoding" $ do
    it "[vectors-reject] accepts the unmodified counter vectors" $
      decodeVectors (A.encode counterVectorsJson) `shouldBe` Right counterVectors
    it "[vectors-reject] rejects a format tag other than gin-vectors/1" $
      rejectsVectors "gin-vectors/1" (setAt [K "format"] (A.String "gin-ir/1") counterVectorsJson)
    it "[vectors-reject] rejects zero cycles" $
      rejectsVectors "cycle" (setAt [K "cycles"] (A.toJSON noValues) counterVectorsJson)
    it "[vectors-reject] rejects more than 100000 cycles" $
      promptly $
        decodeErrorWith "100000" (decodeVectors (emptyRows (maxCycles + 1)))
    it "[vectors-reject] accepts exactly 100000 cycles" $
      fmap (length . vecCycles) (decodeVectors (emptyRows maxCycles)) `shouldBe` Right maxCycles
    it "[vectors-reject] rejects a row with too many inputs" $
      rejectsVectors "row" $
        setAt [K "cycles", I 3, K "in"] (A.toJSON [A.Bool True, A.Bool False]) counterVectorsJson
    it "[vectors-reject] rejects a row with too few outputs" $
      rejectsVectors
        "row"
        (setAt [K "cycles", I 0, K "out"] (A.toJSON noValues) counterVectorsJson)
    it "[vectors-reject] rejects a Bool where the port is a bit vector" $
      rejectsVectors "count" (setAt (cycleOut 2) (A.Bool True) counterVectorsJson)
    it "[vectors-reject] rejects a bit vector of the wrong width" $
      rejectsVectors "count" (setAt (cycleOut 2) (bvValue 7 "2") counterVectorsJson)
    it "[vectors-reject] rejects a tuple where the port is a Bool" $
      rejectsVectors "en" $
        setAt
          [K "cycles", I 0, K "in", I 0]
          (A.object ["tuple" A..= [A.Bool True, A.Bool False]])
          counterVectorsJson
    it "[vectors-reject] rejects an invalid value in a row" $
      rejectsVectors "range" (setAt (cycleOut 1) (bvValue 8 "256") counterVectorsJson)
    it "[vectors-reject] rejects a missing cycles key" $
      rejectsVectors "cycles" (deleteAt [] "cycles" counterVectorsJson)
  where
    boolTy = A.object ["t" A..= ("bool" :: Text)]
    varS = A.object ["e" A..= ("var" :: Text), "name" A..= ("s" :: Text)]
    bv8Ty = A.object ["t" A..= ("bv" :: Text), "width" A..= (8 :: Int)]
    zextPrim :: Integer -> A.Value
    zextPrim w =
      A.object
        [ "e" A..= ("prim" :: Text)
        , "op" A..= ("bv.zext" :: Text)
        , "type" A..= A.object ["t" A..= ("fun" :: Text), "arg" A..= bv8Ty, "res" A..= bv8Ty]
        , "params" A..= A.object ["width" A..= w]
        ]
    counterText = LBS8.unpack (encodeProgram counterProgram)

-- | Replace the first occurrence of a substring.
substitute :: String -> String -> String -> String
substitute old new = go
  where
    go s = case splitPrefix s of
      Just rest -> new <> rest
      Nothing -> case s of
        c : cs -> c : go cs
        [] -> []
    splitPrefix s =
      let (pre, rest) = splitAt (length old) s in if pre == old then Just rest else Nothing

-- | Truncations and single-byte corruptions of a document.
corrupt :: LBS.ByteString -> Gen LBS.ByteString
corrupt bytes = do
  let n = LBS.length bytes
  i <- choose (0, n - 1)
  oneof
    [ pure (LBS.take i bytes)
    , do
        b <- elements (LBS.unpack "{}[]\",:-0123456789eE.tfn \\")
        pure (LBS.take i bytes <> LBS.singleton b <> LBS.drop (i + 1) bytes)
    , pure (LBS.take i bytes <> LBS.drop (i + 1) bytes)
    ]
