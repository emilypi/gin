-- | JSON encoding of the core IR and test vectors, as specified in
-- @docs/file-formats.md@. Explicit functions rather than instances, so
-- the core types carry no aeson dependency and no orphan instances.
--
-- Input is untrusted, so decoding is staged so that each step bounds the
-- work of the next (the bounds are in "Gin.Limits"):
--
--   1. The input size is checked by reading at most @'maxInputBytes' + 1@
--      bytes.
--   2. A byte scan bounds the nesting depth and the length of every number
--      literal before aeson's tokenizer sees them. The tokenizer converts a
--      literal's digits to an 'Integer' and its exponent to an 'Int' with
--      wrap-around, so an unchecked literal costs time proportional to its
--      length and a huge exponent can silently become a small one.
--   3. aeson's token stream is turned into a JSON value, rejecting duplicate
--      object keys (aeson's own decoder keeps one silently) and any number
--      that is not an integer from 0 to 'maxJsonNumber'. Numbers are
--      converted only through 'Sci.toBoundedInteger', which refuses huge
--      magnitudes without computing them.
--   4. Explicit parsers turn that value into the core types, checking
--      widths before computing @2^width@, decimal string lengths before
--      parsing them, and the vector payload before decoding any row.
module Gin.Core.Json
  ( decodeProgram
  , encodeProgram
  , decodeVectors
  , encodeVectors
  ) where

import Control.Monad (unless, when, zipWithM)
import Data.Aeson.Decoding.ByteString.Lazy (lbsToTokens)
import Data.Aeson.Decoding.Tokens (Lit (..), Number (..), TkArray (..), TkRecord (..), Tokens (..))
import Data.Aeson.Encoding (Encoding, Series)
import Data.Aeson.Encoding qualified as E
import Data.Aeson.Key (Key)
import Data.Aeson.Key qualified as Key
import Data.Aeson.KeyMap qualified as KeyMap
import Data.Aeson.Types (JSONPathElement (..), Object, Parser, (<?>))
import Data.Aeson.Types qualified as A
import Data.ByteString qualified as BS
import Data.ByteString.Lazy (LazyByteString)
import Data.ByteString.Lazy qualified as LBS
import Data.Char (isDigit, ord)
import Data.Int (Int64)
import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Maybe (fromMaybe)
import Data.Scientific qualified as Sci
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Vector qualified as Vector
import Data.Word (Word8)
import Gin.Core.Syntax
import Gin.Error (GinError, Stage (..), ginError, withContext)
import Gin.Limits (maxDecimalDigits, maxInputBytes, maxJsonDepth, maxJsonNumber, maxVectorBits)
import Gin.Vectors (Cycle (..), Vectors (..), maxCycles)
import Numeric.Natural (Natural)

-- | Decode and structurally validate (format tag, value invariants, width
-- and size bounds). Type checking is 'Gin.Core.Check.checkProgram'.
decodeProgram :: LazyByteString -> Either GinError Program
decodeProgram = decodeWith program

-- | Canonical encoding: keys in the order of @docs/file-formats.md@,
-- @params@ always present, no insignificant whitespace.
encodeProgram :: Program -> LazyByteString
encodeProgram = E.encodingToLazyByteString . programE

-- | Decode and validate test vectors: format tag, 1 to 'maxCycles' cycles,
-- the payload bound, row lengths, and every value against its port's type.
-- Comparing the ports with a program's top entity is the caller's job.
decodeVectors :: LazyByteString -> Either GinError Vectors
decodeVectors = decodeWith vectors

-- | Canonical encoding, in the same style as 'encodeProgram'.
encodeVectors :: Vectors -> LazyByteString
encodeVectors = E.encodingToLazyByteString . vectorsE

----------------------------------------------------------------------
-- Reading JSON under the resource limits

decodeWith :: (A.Value -> Parser a) -> LazyByteString -> Either GinError a
decodeWith parser bytes = do
  json <- readJson bytes
  case A.iparseEither parser json of
    Right a -> Right a
    Left (path, msg) ->
      withContext ("at " <> Text.pack (A.formatPath path)) (decodeError (Text.pack msg))

decodeError :: Text -> Either GinError a
decodeError = Left . ginError StDecode

showT :: (Show a) => a -> Text
showT = Text.pack . show

numberBound :: Text
numberBound = "numbers must be integers from 0 to " <> showT maxJsonNumber

readJson :: LazyByteString -> Either GinError A.Value
readJson bytes = do
  let limit = fromIntegral maxInputBytes :: Int64
  when (LBS.length (LBS.take (limit + 1) bytes) > limit) $
    decodeError ("input exceeds " <> showT maxInputBytes <> " bytes")
  scanBytes bytes
  (json, rest) <- tokenValue (lbsToTokens bytes)
  unless (LBS.all isJsonSpace rest) $
    decodeError "invalid JSON: trailing data after the document"
  pure json

isJsonSpace :: Word8 -> Bool
isJsonSpace w = w == 0x20 || w == 0x0a || w == 0x0d || w == 0x09

-- | Longest number literal accepted. No integer up to 'maxJsonNumber'
-- needs more than ten characters; the slack admits forms such as @1.0e4@.
maxNumberLength :: Int
maxNumberLength = 32

-- | Most significant digits accepted in a number's exponent. Larger
-- exponents can never give an in-range integer, and would overflow the
-- tokenizer's 'Int' exponent.
maxExponentDigits :: Int
maxExponentDigits = 9

data Mode
  = -- | Between tokens.
    Outside
  | InString
  | -- | Just after a backslash inside a string.
    InEscape
  | -- | Just after a minus sign outside a string.
    AfterMinus
  | -- | In a number literal, before any exponent.
    InNumber
  | -- | In a number literal's exponent.
    InExponent

data Scan = Scan
  { scanOffset :: !Int
  , scanDepth :: !Int
  , scanMode :: !Mode
  , scanNumberLength :: !Int
  , scanExponentDigits :: !Int
  -- ^ Significant (non-leading-zero) exponent digits so far.
  }

-- | Bound nesting depth and number literals in one pass over the bytes,
-- stopping at the first violation. Malformed JSON is left to the
-- tokenizer; this pass only needs to find strings, brackets and numbers.
scanBytes :: LazyByteString -> Either GinError ()
scanBytes = go (Scan 0 0 Outside 0 0) . LBS.toChunks
  where
    go _ [] = Right ()
    go s (chunk : chunks) = scanChunk s chunk >>= \s' -> go s' chunks

scanChunk :: Scan -> BS.ByteString -> Either GinError Scan
scanChunk s0 chunk = loop s0 0
  where
    loop !s !i = case BS.indexMaybe chunk i of
      Nothing -> Right s
      Just w -> case scanByte s w of
        Left e -> Left e
        Right s' -> loop s' (i + 1)

scanByte :: Scan -> Word8 -> Either GinError Scan
scanByte s w = case scanMode s of
  InString
    | w == quote -> next Outside
    | w == backslash -> next InEscape
    | otherwise -> next InString
  InEscape -> next InString
  AfterMinus
    | isDigitByte w -> failAt (offset - 1) "negative number"
    | otherwise -> outside
  InNumber
    | w == lowerE || w == upperE -> numberByte InExponent 0
    | isDigitByte w || w == dot || w == plus || w == minus -> numberByte InNumber 0
    | otherwise -> outside
  InExponent
    | isDigitByte w ->
        let digits
              | w == zero && scanExponentDigits s == 0 = 0
              | otherwise = scanExponentDigits s + 1
         in if digits > maxExponentDigits
              then
                failAt offset $
                  "number with an exponent of more than " <> showT maxExponentDigits <> " digits"
              else numberByte InExponent digits
    | w == plus || w == minus -> numberByte InExponent (scanExponentDigits s)
    | otherwise -> outside
  Outside -> outside
  where
    offset = scanOffset s
    next mode = Right s{scanOffset = offset + 1, scanMode = mode}
    failAt at msg = decodeError (msg <> " at byte " <> showT at <> " (" <> numberBound <> ")")
    numberByte mode digits
      | scanNumberLength s >= maxNumberLength =
          failAt offset ("number literal longer than " <> showT maxNumberLength <> " characters")
      | otherwise =
          Right
            s
              { scanOffset = offset + 1
              , scanMode = mode
              , scanNumberLength = scanNumberLength s + 1
              , scanExponentDigits = digits
              }
    outside
      | w == quote = next InString
      | w == openBracket || w == openBrace =
          if scanDepth s >= maxJsonDepth
            then
              decodeError
                ("JSON nesting depth exceeds " <> showT maxJsonDepth <> " at byte " <> showT offset)
            else Right s{scanOffset = offset + 1, scanMode = Outside, scanDepth = scanDepth s + 1}
      | w == closeBracket || w == closeBrace =
          Right s{scanOffset = offset + 1, scanMode = Outside, scanDepth = max 0 (scanDepth s - 1)}
      | w == minus = next AfterMinus
      | isDigitByte w =
          Right
            s
              { scanOffset = offset + 1
              , scanMode = InNumber
              , scanNumberLength = 1
              , scanExponentDigits = 0
              }
      | otherwise = next Outside
{-# INLINE scanByte #-}

isDigitByte :: Word8 -> Bool
isDigitByte w = w >= zero && w <= zero + 9

quote, backslash, openBracket, closeBracket, openBrace, closeBrace :: Word8
quote = 0x22
backslash = 0x5c
openBracket = 0x5b
closeBracket = 0x5d
openBrace = 0x7b
closeBrace = 0x7d

zero, dot, plus, minus, lowerE, upperE :: Word8
zero = 0x30
dot = 0x2e
plus = 0x2b
minus = 0x2d
lowerE = 0x65
upperE = 0x45

-- | Build a JSON value from aeson's token stream, returning the input
-- that follows it. Depth is already bounded by 'scanBytes', so the
-- recursion is too.
--
-- Memory grows linearly with the input, but by a large factor for inputs
-- made of tiny values: 'maxInputBytes' of @[0,0,...]@ or @[[],[],...]@
-- peaks at about 140 MB of live heap, and of nested singleton arrays
-- (@[[[[]]]],...@) at about 550 MB. Empty strings, arrays and objects and
-- small numbers are shared, and arrays are built at their final size, to
-- keep that factor down.
tokenValue :: Tokens k String -> Either GinError (A.Value, k)
tokenValue = \case
  TkLit l k -> Right (literal l, k)
  TkText t k -> Right (if Text.null t then emptyString else A.String t, k)
  TkNumber n k -> (,k) <$> jsonNumber n
  TkArrayOpen items -> arrayValue 0 [] items
  TkRecordOpen fields -> objectValue KeyMap.empty fields
  TkErr e -> invalidJson e
  where
    literal = \case
      LitNull -> A.Null
      LitTrue -> A.Bool True
      LitFalse -> A.Bool False

-- | Elements are accumulated in reverse and counted, so the vector is
-- allocated once at its final size.
arrayValue :: Int -> [A.Value] -> TkArray k String -> Either GinError (A.Value, k)
arrayValue !n acc = \case
  TkItem toks -> do
    (!x, rest) <- tokenValue toks
    arrayValue (n + 1) (x : acc) rest
  TkArrayEnd k
    | n == 0 -> Right (emptyArray, k)
    | otherwise -> Right (A.Array (Vector.reverse (Vector.fromListN n acc)), k)
  TkArrayErr e -> invalidJson e

objectValue :: A.Object -> TkRecord k String -> Either GinError (A.Value, k)
objectValue acc = \case
  TkPair key toks
    | KeyMap.member key acc -> decodeError ("duplicate key \"" <> Key.toText key <> "\"")
    | otherwise -> do
        (!x, rest) <- tokenValue toks
        objectValue (KeyMap.insert key x acc) rest
  TkRecordEnd k
    | KeyMap.null acc -> Right (emptyObject, k)
    | otherwise -> Right (A.Object acc, k)
  TkRecordErr e -> invalidJson e

emptyString, emptyArray, emptyObject :: A.Value
emptyString = A.String Text.empty
emptyArray = A.Array Vector.empty
emptyObject = A.Object KeyMap.empty
{-# NOINLINE emptyString #-}
{-# NOINLINE emptyArray #-}
{-# NOINLINE emptyObject #-}

-- | Shared values for the numbers that recur most (widths, indices).
smallNumbers :: Vector.Vector A.Value
smallNumbers = Vector.generate 4097 (A.Number . fromIntegral)
{-# NOINLINE smallNumbers #-}

invalidJson :: String -> Either GinError a
invalidJson e = decodeError ("invalid JSON: " <> Text.pack e)

-- | Every JSON number must be an integer from 0 to 'maxJsonNumber'.
jsonNumber :: Number -> Either GinError A.Value
jsonNumber n = case Sci.toBoundedInteger s :: Maybe Int64 of
  Just i
    | i >= 0 && toInteger i <= maxJsonNumber ->
        Right $! fromMaybe (A.Number (fromIntegral i)) (smallNumbers Vector.!? fromIntegral i)
  _
    | not (Sci.isInteger s) -> decodeError ("non-integral number (" <> numberBound <> ")")
    | otherwise -> decodeError ("number out of range (" <> numberBound <> ")")
  where
    s = case n of
      NumInteger i -> fromInteger i
      NumDecimal d -> d
      NumScientific d -> d

----------------------------------------------------------------------
-- Parsers

field :: Object -> Key -> (A.Value -> Parser a) -> Parser a
field o k p = A.explicitParseField p o k

-- | An optional field; unlike aeson's variants, @null@ is not absence.
optionalField :: Object -> Key -> (A.Value -> Parser a) -> Parser (Maybe a)
optionalField o k p = traverse (\x -> p x <?> Key k) (KeyMap.lookup k o)

text :: A.Value -> Parser Text
text = A.withText "String" pure

name :: A.Value -> Parser Name
name = fmap Name . text

bool :: A.Value -> Parser Bool
bool = A.withBool "Bool" pure

nat :: A.Value -> Parser Natural
nat = A.withScientific "Nat" $ \s -> case Sci.toBoundedInteger s :: Maybe Int64 of
  Just i | i >= 0 && toInteger i <= maxJsonNumber -> pure (fromIntegral i)
  _ -> fail ("expected a natural number (" <> Text.unpack numberBound <> ")")

width :: A.Value -> Parser Natural
width x = do
  w <- nat x
  unless (w >= 1 && w <= maxWidth) $
    fail ("width " <> show w <> " outside 1.." <> show maxWidth)
  pure w

list :: (A.Value -> Parser a) -> A.Value -> Parser [a]
list = listOfAtLeast 0 ""

-- | A list with at least @n@ elements; @what@ names it in the error.
listOfAtLeast :: Int -> String -> (A.Value -> Parser a) -> A.Value -> Parser [a]
listOfAtLeast n what p = A.withArray "Array" $ \xs -> do
  when (Vector.length xs < n) $
    fail
      (what <> " needs at least " <> show n <> " elements, got " <> show (Vector.length xs))
  zipWithM (\i x -> p x <?> Index i) [0 ..] (Vector.toList xs)

formatTag :: Text -> Object -> Parser ()
formatTag expected o = do
  tag <- field o "format" text
  unless (tag == expected)
    $ fail ("unsupported format " <> show tag <> ", expected " <> show expected)
    <?> Key "format"

unknownTag :: String -> Text -> Parser a
unknownTag what t = fail ("unknown " <> what <> " " <> show t)

program :: A.Value -> Parser Program
program = A.withObject "Program" $ \o -> do
  formatTag "gin-ir/1" o
  Program
    <$> field o "producer" producer
    <*> field o "top" topEntity
    <*> field o "defs" (list def)
    <*> field o "certificate" certificate

producer :: A.Value -> Parser Producer
producer = A.withObject "Producer" $ \o ->
  Producer <$> field o "tool" text <*> field o "leanVersion" text

topEntity :: A.Value -> Parser TopEntity
topEntity = A.withObject "TopEntity" $ \o ->
  TopEntity
    <$> field o "name" text
    <*> field o "domain" domain
    <*> field o "inputs" (list port)
    <*> field o "outputs" (list port)
    <*> field o "def" name

domain :: A.Value -> Parser Domain
domain = A.withObject "Domain" $ \o -> Domain <$> field o "name" text <*> field o "periodPs" nat

port :: A.Value -> Parser Port
port = A.withObject "Port" $ \o -> Port <$> field o "name" text <*> field o "type" ty

def :: A.Value -> Parser Def
def = A.withObject "Def" $ \o ->
  Def <$> field o "name" name <*> field o "type" ty <*> field o "body" expr

certificate :: A.Value -> Parser Certificate
certificate = A.withObject "Certificate" $ \o ->
  Certificate
    <$> field o "theorem" text
    <*> field o "statement" text
    <*> field o "axioms" (list text)
    <*> field o "implAxioms" (list text)

ty :: A.Value -> Parser Ty
ty = A.withObject "Type" $ \o ->
  field o "t" text >>= \case
    "bool" -> pure TBool
    "bv" -> TBitVec <$> field o "width" width
    "prod" -> TProd <$> field o "elems" (listOfAtLeast 2 "a product type" ty)
    "fun" -> TFun <$> field o "arg" ty <*> field o "res" ty
    "signal" -> TSignal <$> field o "domain" text <*> field o "elem" ty
    t -> unknownTag "type tag" t <?> Key "t"

value :: A.Value -> Parser Value
value = \case
  A.Bool b -> pure (VBool b)
  A.Object o
    | KeyMap.member "bv" o -> do
        w <- field o "bv" width
        VBV w <$> field o "val" (decimal w)
    | KeyMap.member "tuple" o ->
        VTuple <$> field o "tuple" (listOfAtLeast 2 "a tuple value" value)
  other -> A.typeMismatch "a value (true, false, {\"bv\", \"val\"} or {\"tuple\"})" other

-- | A canonical decimal below @2^w@, for a width already within bounds.
decimal :: Natural -> A.Value -> Parser Integer
decimal w = A.withText "DecimalString" $ \s -> do
  when (Text.compareLength s maxDecimalDigits == GT) $
    fail ("decimal string longer than " <> show maxDecimalDigits <> " digits")
  unless (canonical s) $
    fail ("not a canonical decimal string: " <> show s)
  let n = Text.foldl' (\acc c -> acc * 10 + toInteger (ord c - ord '0')) 0 s
  unless (n < 2 ^ w) $
    fail ("value out of range for width " <> show w)
  pure n
  where
    canonical s = case Text.uncons s of
      Just ('0', rest) -> Text.null rest
      Just _ -> Text.all isDigit s
      Nothing -> False

expr :: A.Value -> Parser Expr
expr = A.withObject "Expr" $ \o ->
  field o "e" text >>= \case
    "var" -> EVar <$> field o "name" name
    "global" -> EGlobal <$> field o "name" name
    "lit" -> ELit <$> field o "value" value
    "prim" -> do
      opName <- field o "op" text
      t <- field o "type" ty
      params <- fromMaybe KeyMap.empty <$> optionalField o "params" (A.withObject "Params" pure)
      op <- primOp opName params
      pure (EPrim op t)
    "app" -> EApp <$> field o "fun" expr <*> field o "args" (listOfAtLeast 1 "an application" expr)
    "lam" -> ELam <$> field o "binders" (listOfAtLeast 1 "a lambda" binder) <*> field o "body" expr
    "let" -> ELet <$> field o "rec" bool <*> field o "binds" (list bind) <*> field o "body" expr
    "tuple" -> ETuple <$> field o "elems" (listOfAtLeast 2 "a tuple" expr)
    "proj" -> EProj <$> field o "index" nat <*> field o "of" expr
    "if" -> EIf <$> field o "cond" expr <*> field o "then" expr <*> field o "else" expr
    e -> unknownTag "expression tag" e <?> Key "e"
  where
    binder = A.withObject "Binder" $ \b -> (,) <$> field b "name" name <*> field b "type" ty
    bind = A.withObject "Bind" $ \b ->
      Bind <$> field b "name" name <*> field b "type" ty <*> field b "value" expr

-- | Resolve a primitive name and read its parameters. Parameters of
-- primitives that take none are ignored, like any unknown key.
primOp :: Text -> Object -> Parser PrimOp
primOp opName params = case Map.lookup opName parameterless of
  Just op -> pure op
  Nothing -> case opName of
    "bv.shl" -> BvShl <$> param "amount" nat
    "bv.lshr" -> BvLshr <$> param "amount" nat
    "bv.extract" -> BvExtract <$> param "hi" nat <*> param "lo" nat
    "bv.zext" -> BvZext <$> param "width" width
    "sig.lift" -> SigLift <$> param "arity" nat
    "sig.register" -> SigRegister <$> param "init" value
    "sig.mealy" -> SigMealy <$> param "init" value
    _ -> unknownTag "primitive" opName <?> Key "op"
  where
    param :: Key -> (A.Value -> Parser a) -> Parser a
    param k p = field params k p <?> Key "params"

parameterless :: Map Text PrimOp
parameterless =
  Map.fromList
    [ (primName op, op)
    | op <-
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
    ]

vectors :: A.Value -> Parser Vectors
vectors = A.withObject "Vectors" $ \o -> do
  formatTag "gin-vectors/1" o
  top <- field o "top" text
  ins <- field o "inputs" (list port)
  outs <- field o "outputs" (list port)
  Vectors top ins outs <$> field o "cycles" (cycles ins outs)

-- | Count and payload are checked on the array before any row is decoded.
cycles :: [Port] -> [Port] -> A.Value -> Parser [Cycle]
cycles ins outs = A.withArray "Array" $ \rows -> do
  let n = Vector.length rows
      payload = toInteger n * sum (fmap (portBits . portTy) (ins <> outs))
  when (n < 1 || n > maxCycles) $
    fail ("expected 1 to " <> show maxCycles <> " cycles, got " <> show n)
  when (payload > maxVectorBits) $
    fail
      ( "vector payload of "
          <> show payload
          <> " bits (cycles times summed port widths) exceeds "
          <> show maxVectorBits
          <> " bits"
      )
  zipWithM (\i r -> cycleRow r <?> Index i) [0 ..] (Vector.toList rows)
  where
    cycleRow = A.withObject "Cycle" $ \r ->
      Cycle <$> field r "in" (row ins) <*> field r "out" (row outs)

-- | Bits one value of the type occupies. No value has a function type, so
-- a function-typed port fails on its first row whatever it counts for.
portBits :: Ty -> Integer
portBits = \case
  TBool -> 1
  TBitVec w -> toInteger w
  TProd ts -> sum (fmap portBits ts)
  TFun _ _ -> 0
  TSignal _ t -> portBits t

row :: [Port] -> A.Value -> Parser [Value]
row ports = A.withArray "Array" $ \xs -> do
  unless (Vector.length xs == length ports) $
    fail
      ( "row has "
          <> show (Vector.length xs)
          <> " values, expected "
          <> show (length ports)
          <> " (one per port)"
      )
  zipWithM (\i (p, x) -> portValue p x <?> Index i) [0 ..] (zip ports (Vector.toList xs))

portValue :: Port -> A.Value -> Parser Value
portValue p x = do
  v <- value x
  unless (valueTy v == portTy p) $
    fail
      ( "value of type "
          <> renderTy (valueTy v)
          <> " for port "
          <> show (portName p)
          <> " of type "
          <> renderTy (portTy p)
      )
  pure v
  where
    renderTy =
      Text.unpack . Text.decodeUtf8Lenient . LBS.toStrict . E.encodingToLazyByteString . tyE

----------------------------------------------------------------------
-- Encoders

natE :: Natural -> Encoding
natE = E.integer . toInteger

obj :: [Series] -> Encoding
obj = E.pairs . mconcat

programE :: Program -> Encoding
programE p =
  obj
    [ E.pair "format" (E.text "gin-ir/1")
    , E.pair "producer" (producerE (progProducer p))
    , E.pair "top" (topE (progTop p))
    , E.pair "defs" (E.list defE (progDefs p))
    , E.pair "certificate" (certificateE (progCertificate p))
    ]

producerE :: Producer -> Encoding
producerE (Producer tool leanVersion) =
  obj [E.pair "tool" (E.text tool), E.pair "leanVersion" (E.text leanVersion)]

topE :: TopEntity -> Encoding
topE t =
  obj
    [ E.pair "name" (E.text (topName t))
    , E.pair "domain" (domainE (topDomain t))
    , E.pair "inputs" (E.list portE (topInputs t))
    , E.pair "outputs" (E.list portE (topOutputs t))
    , E.pair "def" (nameE (topDef t))
    ]

domainE :: Domain -> Encoding
domainE (Domain n period) = obj [E.pair "name" (E.text n), E.pair "periodPs" (natE period)]

portE :: Port -> Encoding
portE (Port n t) = obj [E.pair "name" (E.text n), E.pair "type" (tyE t)]

nameE :: Name -> Encoding
nameE = E.text . unName

defE :: Def -> Encoding
defE (Def n t body) =
  obj [E.pair "name" (nameE n), E.pair "type" (tyE t), E.pair "body" (exprE body)]

certificateE :: Certificate -> Encoding
certificateE c =
  obj
    [ E.pair "theorem" (E.text (certTheorem c))
    , E.pair "statement" (E.text (certStatement c))
    , E.pair "axioms" (E.list E.text (certAxioms c))
    , E.pair "implAxioms" (E.list E.text (certImplAxioms c))
    ]

tyE :: Ty -> Encoding
tyE = \case
  TBool -> tagged "bool" []
  TBitVec w -> tagged "bv" [E.pair "width" (natE w)]
  TProd ts -> tagged "prod" [E.pair "elems" (E.list tyE ts)]
  TFun a r -> tagged "fun" [E.pair "arg" (tyE a), E.pair "res" (tyE r)]
  TSignal d t -> tagged "signal" [E.pair "domain" (E.text d), E.pair "elem" (tyE t)]
  where
    tagged t rest = obj (E.pair "t" (E.text t) : rest)

valueE :: Value -> Encoding
valueE = \case
  VBool b -> E.bool b
  VBV w n -> obj [E.pair "bv" (natE w), E.pair "val" (E.string (show n))]
  VTuple vs -> obj [E.pair "tuple" (E.list valueE vs)]

exprE :: Expr -> Encoding
exprE = \case
  EVar n -> tagged "var" [E.pair "name" (nameE n)]
  EGlobal n -> tagged "global" [E.pair "name" (nameE n)]
  ELit v -> tagged "lit" [E.pair "value" (valueE v)]
  EPrim op t ->
    tagged
      "prim"
      [E.pair "op" (E.text (primName op)), E.pair "type" (tyE t), E.pair "params" (paramsE op)]
  EApp f args -> tagged "app" [E.pair "fun" (exprE f), E.pair "args" (E.list exprE args)]
  ELam binders body ->
    tagged "lam" [E.pair "binders" (E.list binderE binders), E.pair "body" (exprE body)]
  ELet isRec binds body ->
    tagged
      "let"
      [E.pair "rec" (E.bool isRec), E.pair "binds" (E.list bindE binds), E.pair "body" (exprE body)]
  ETuple es -> tagged "tuple" [E.pair "elems" (E.list exprE es)]
  EProj i e -> tagged "proj" [E.pair "index" (natE i), E.pair "of" (exprE e)]
  EIf c t e ->
    tagged "if" [E.pair "cond" (exprE c), E.pair "then" (exprE t), E.pair "else" (exprE e)]
  where
    tagged t rest = obj (E.pair "e" (E.text t) : rest)
    binderE (n, t) = obj [E.pair "name" (nameE n), E.pair "type" (tyE t)]
    bindE (Bind n t e) =
      obj [E.pair "name" (nameE n), E.pair "type" (tyE t), E.pair "value" (exprE e)]

paramsE :: PrimOp -> Encoding
paramsE = \case
  BvShl k -> obj [E.pair "amount" (natE k)]
  BvLshr k -> obj [E.pair "amount" (natE k)]
  BvExtract hi lo -> obj [E.pair "hi" (natE hi), E.pair "lo" (natE lo)]
  BvZext m -> obj [E.pair "width" (natE m)]
  SigLift k -> obj [E.pair "arity" (natE k)]
  SigRegister v -> obj [E.pair "init" (valueE v)]
  SigMealy v -> obj [E.pair "init" (valueE v)]
  _ -> E.emptyObject_

vectorsE :: Vectors -> Encoding
vectorsE vs =
  obj
    [ E.pair "format" (E.text "gin-vectors/1")
    , E.pair "top" (E.text (vecTop vs))
    , E.pair "inputs" (E.list portE (vecInputs vs))
    , E.pair "outputs" (E.list portE (vecOutputs vs))
    , E.pair "cycles" (E.list cycleE (vecCycles vs))
    ]
  where
    cycleE c =
      obj [E.pair "in" (E.list valueE (cycInputs c)), E.pair "out" (E.list valueE (cycOutputs c))]
