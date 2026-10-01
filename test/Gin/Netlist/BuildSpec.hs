-- | Tests for "Gin.Netlist.Build".
module Gin.Netlist.BuildSpec (spec) where

import Data.Char (isAsciiLower, toUpper)
import Data.Foldable (for_)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Gin.Netlist.Build (sanitize)
import Gin.Netlist.Types (isLegalIdent, reservedWords)
import Test.Hspec (Spec, describe, it, shouldBe, shouldSatisfy)
import Test.Hspec.QuickCheck (modifyMaxSuccess, prop)
import Test.QuickCheck
  ( Gen
  , Property
  , arbitrary
  , arbitraryUnicodeChar
  , checkCoverage
  , chooseInt
  , conjoin
  , counterexample
  , cover
  , elements
  , forAll
  , frequency
  , listOf
  , sublistOf
  , vectorOf
  , (===)
  )
import Text.Read (readMaybe)

spec :: Spec
spec =
  describe "sanitize" sanitizeSpec

----------------------------------------------------------------------
-- sanitize

sanitizeSpec :: Spec
sanitizeSpec = do
  describe "without collisions" $ for_ sanitizeCases $ \(raw, expected) ->
    it ("[nl-sanitize] " <> show raw <> " becomes " <> show expected) $ do
      sanitize Set.empty raw `shouldBe` expected
      expected `shouldSatisfy` isLegalIdent
  describe "with collisions" $ for_ collisionCases $ \(label, taken, raw, expected) ->
    it ("[nl-sanitize] " <> label) $ do
      sanitize (Set.fromList taken) raw `shouldBe` expected
      expected `shouldSatisfy` isLegalIdent
  modifyMaxSuccess (const 2000) $ do
    prop "[nl-sanitize] always returns a legal identifier" $
      forAll genSanitizeInput $ \(taken, raw) ->
        let r = sanitize taken raw in counterexample (show r) (isLegalIdent r)
    prop "[nl-sanitize] never returns a taken name, compared case-insensitively" $
      forAll genSanitizeInput $ \(taken, raw) ->
        let r = sanitize taken raw
         in counterexample (show r) (Text.toLower r `Set.notMember` Set.map Text.toLower taken)
    prop "[nl-sanitize] is deterministic: the base name when free, else its least free suffix" $
      checkCoverage . forAll genSanitizeInput $ \(taken, raw) ->
        let collided = sanitize taken raw /= sanitize Set.empty raw
         in cover 40 collided "collision" . cover 10 (not collided) "no collision" $
              leastFreeSuffix taken raw
    prop "[nl-sanitize] ignores the ASCII case of taken names" $
      forAll genSanitizeInput $ \(taken, raw) ->
        sanitize (Set.map asciiUpper taken) raw === sanitize taken raw
    prop "[nl-sanitize] keeps legal names of at most 56 characters other than gin" $
      forAll genShortLegal $ \raw -> sanitize Set.empty raw === raw

-- | Inputs and their sanitized forms when nothing is taken.
sanitizeCases :: [(Text, Text)]
sanitizeCases =
  [ ("x", "x")
  , ("_x", "x")
  , ("x_", "x")
  , ("", "n")
  , ("___", "n")
  , ("\252", "n")
  , ("\220nit", "nit")
  , ("Counter.counter", "counter_counter")
  , ("acc'", "acc")
  , ("s.next", "s_next")
  , ("a__b", "a_b")
  , ("a-.-b", "a_b")
  , ("MiXeD", "mixed")
  , ("x_1", "x_1")
  , ("1x", "n_1x")
  , ("9", "n_9")
  , ("gin", "n_gin")
  , ("gin_x", "n_gin_x")
  , ("GIN_X", "n_gin_x")
  , ("gin.x", "n_gin_x")
  , ("ginx", "ginx")
  , ("module", "n_module")
  , ("Module", "n_module")
  , ("entity", "n_entity")
  , ("logic", "n_logic")
  , ("std_logic_1164", "n_std_logic_1164")
  , ("SIGNAL", "n_signal")
  , ("n", "n")
  , ("n_module", "n_module")
  , (Text.replicate 70 "a", Text.replicate 56 "a")
  , (Text.replicate 55 "a" <> "_" <> Text.replicate 14 "b", Text.replicate 55 "a")
  , ("1" <> Text.replicate 69 "a", "n_1" <> Text.replicate 53 "a")
  ]

-- | Collisions: label, taken names, input, result.
collisionCases :: [(String, [Text], Text, Text)]
collisionCases =
  [ ("a taken name gets the suffix _1", ["x"], "x", "x_1")
  , ("the suffix counts up past taken suffixes", ["x", "x_1", "x_2"], "x", "x_3")
  , ("the least free suffix is used", ["x", "x_2"], "x", "x_1")
  , ("collisions are case-insensitive", ["X"], "x", "x_1")
  , ("the sanitized name is what collides", ["x"], "X'", "x_1")
  , ("a free base name ignores taken suffixed names", ["x_1", "x_2"], "x", "x")
  , ("the clock name is avoided", ["clk"], "CLK", "clk_1")
  , ("the empty name collides as n", ["n"], "", "n_1")
  , ("a prefixed reserved word collides too", ["n_module"], "module", "n_module_1")
  , ("a 70-character name collides after truncation", [long56], Text.replicate 70 "a", long56 <> "_1")
  , ("suffixes go past one digit", "y" : ["y_" <> tshow k | k <- [1 .. 10 :: Int]], "y", "y_11")
  ]
  where
    long56 = Text.replicate 56 "a"

-- | The result is the base name ('sanitize' with nothing taken) when that
-- is free; otherwise it is the base name with the least suffix @_k@ that
-- is free and legal.
leastFreeSuffix :: Set Text -> Text -> Property
leastFreeSuffix taken raw =
  counterexample ("result: " <> show r) $
    if free base
      then r === base
      else case Text.stripPrefix (base <> "_") r >>= readSuffix of
        Just k ->
          conjoin
            [ counterexample "suffix below 1" (k >= 1)
            , counterexample "result not free" (free r)
            , counterexample "a smaller suffix was free" $
                not (any (free . suffixed) [1 .. k - 1])
            ]
        Nothing -> counterexample "not the base name with a numeric suffix" False
  where
    r = sanitize taken raw
    base = sanitize Set.empty raw
    lowered = Set.map Text.toLower taken
    free c = Text.toLower c `Set.notMember` lowered && isLegalIdent c
    suffixed k = base <> "_" <> tshow k
    readSuffix ks = case readMaybe (Text.unpack ks) of
      Just k | tshow k == ks -> Just (k :: Int)
      _ -> Nothing

genSanitizeInput :: Gen (Set Text, Text)
genSanitizeInput = do
  raw <- genRawName
  taken <- genTaken raw
  pure (taken, raw)

-- | Names of every shape the IR may carry: arbitrary Unicode, ASCII
-- punctuation, reserved words, @gin@ prefixes and long names.
genRawName :: Gen Text
genRawName =
  frequency
    [ (3, Text.pack <$> listOf arbitraryUnicodeChar)
    , (4, Text.pack <$> listOf (elements "aAzZ09_-.'$ \220\x202E"))
    , (2, elements (Set.toList reservedWords))
    , (1, Text.toUpper <$> elements (Set.toList reservedWords))
    , (1, ("gin" <>) . Text.pack <$> listOf (elements "_xG."))
    , (1, Text.pack <$> (chooseInt (50, 80) >>= \n -> vectorOf n (elements "ab_.")))
    ]

-- | Taken names, biased towards collisions with @raw@'s base name and its
-- suffixed variants.
genTaken :: Text -> Gen (Set Text)
genTaken raw = do
  let base = sanitize Set.empty raw
  upper <- arbitrary
  k <- frequency [(1, pure 0), (3, chooseInt (1, 12))]
  ks <- sublistOf [1 .. k]
  unrelated <- listOf genRawName
  let related = [base | k > 0] <> [base <> "_" <> tshow i | i <- ks]
  pure (Set.fromList (fmap (if upper then asciiUpper else id) related <> unrelated))

-- | Legal identifiers of at most 56 characters, other than @gin@.
genShortLegal :: Gen Text
genShortLegal = do
  first <- elements ['a' .. 'z']
  rest <- listOf (elements "abgin019_")
  let t = Text.pack (first : take 55 rest)
  if isLegalIdent t && t /= "gin" then pure t else genShortLegal

asciiUpper :: Text -> Text
asciiUpper = Text.map (\c -> if isAsciiLower c then toUpper c else c)

tshow :: (Show a) => a -> Text
tshow = Text.pack . show
