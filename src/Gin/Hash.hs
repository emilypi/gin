-- | SHA-256 (FIPS 180-4), used to give a reviewed specification a stable
-- identity ('Gin.Certificate.certificateSpecHash'): once you have answered
-- "does the specification say what I want?", you pin it with
-- @--spec-hash@. I use a small pure implementation to keep the
-- dependency footprint unchanged; inputs are a few kilobytes of trace
-- text (@Certificate@ in the code, @"certificate"@ in the JSON).
module Gin.Hash
  ( sha256
  , sha256Hex
  ) where

import Data.Bits (complement, rotateR, shiftL, shiftR, xor, (.&.), (.|.))
import Data.ByteString (StrictByteString)
import Data.ByteString qualified as BS
import Data.ByteString.Builder qualified as B
import Data.ByteString.Lazy qualified as BL
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Word (Word32, Word64, Word8)
import Numeric (showHex)

-- | The 32-byte digest.
sha256 :: StrictByteString -> StrictByteString
sha256 msg =
  BL.toStrict . B.toLazyByteString . foldMap B.word32BE $
    foldl' compress initial (blocks (pad msg))

-- | The digest as 64 lowercase hexadecimal digits.
sha256Hex :: StrictByteString -> Text
sha256Hex = Text.pack . concatMap hex2 . BS.unpack . sha256
  where
    hex2 :: Word8 -> String
    hex2 w = let s = showHex w "" in if length s == 1 then '0' : s else s

initial :: [Word32]
initial =
  [ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a
  , 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19
  ]

roundConstants :: [Word32]
roundConstants =
  [ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5
  , 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174
  , 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da
  , 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967
  , 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85
  , 0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070
  , 0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3
  , 0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2
  ]

-- | Append the 0x80 marker, zero bytes, and the 64-bit big-endian bit
-- length, to a multiple of 64 bytes.
pad :: StrictByteString -> StrictByteString
pad msg = BS.concat [msg, BS.singleton 0x80, BS.replicate zeros 0, lenBytes]
  where
    len = BS.length msg
    zeros = (55 - len) `mod` 64
    lenBytes = BL.toStrict (B.toLazyByteString (B.word64BE (fromIntegral len * 8 :: Word64)))

blocks :: StrictByteString -> [[Word32]]
blocks bs
  | BS.null bs = []
  | otherwise = let (b, rest) = BS.splitAt 64 bs in words32 b : blocks rest
  where
    words32 b
      | BS.null b = []
      | otherwise = let (w, r) = BS.splitAt 4 b in be32 w : words32 r
    be32 = BS.foldl' (\acc x -> (acc `shiftL` 8) .|. fromIntegral x) 0

compress :: [Word32] -> [Word32] -> [Word32]
compress hs block = zipWith (+) hs (foldl' step hs (zip roundConstants schedule))
  where
    schedule = take 64 (expand block)
    expand ws = ws <> go ws
      where
        go w = case w of
          (w0 : w1 : rest) | length w >= 16 ->
            let w9 = w !! 9
                w14 = w !! 14
                new = sigma1 w14 + w9 + sigma0 w1 + w0
             in new : go (w1 : rest <> [new])
          _ -> []
    sigma0 x = rotateR x 7 `xor` rotateR x 18 `xor` shiftR x 3
    sigma1 x = rotateR x 17 `xor` rotateR x 19 `xor` shiftR x 10
    step state (k, w) = case state of
      [a, b, c, d, e, f, g, h] ->
        let s1 = rotateR e 6 `xor` rotateR e 11 `xor` rotateR e 25
            ch = (e .&. f) `xor` (complement e .&. g)
            t1 = h + s1 + ch + k + w
            s0 = rotateR a 2 `xor` rotateR a 13 `xor` rotateR a 22
            maj = (a .&. b) `xor` (a .&. c) `xor` (b .&. c)
            t2 = s0 + maj
         in [t1 + t2, a, b, c, d + t1, e, f, g]
      _ -> state
