-- | Resource bounds on untrusted input. I check every bound before the
-- work it guards, so hostile files fail fast with a decode or normalize
-- error instead of exhausting memory or time.
module Gin.Limits
  ( maxInputBytes
  , maxJsonDepth
  , maxJsonNumber
  , maxDecimalDigits
  , maxVectorBits
  , maxNormalBinds
  , defaultToolTimeoutSeconds
  , defaultSimTimeoutSeconds
  ) where

-- | Largest IR or vectors file gin reads (16 MiB).
maxInputBytes :: Int
maxInputBytes = 16 * 1024 * 1024

-- | Deepest JSON nesting accepted (arrays and objects).
maxJsonDepth :: Int
maxJsonDepth = 4096

-- | Largest JSON number accepted anywhere (widths, indices, shift
-- amounts, arities, periods). Checked before any conversion.
maxJsonNumber :: Integer
maxJsonNumber = 2 ^ (31 :: Int) - 1

-- | Longest decimal string accepted for a bit-vector value; @2^4096@ has
-- 1234 digits. Checked before parsing.
maxDecimalDigits :: Int
maxDecimalDigits = 1234

-- | Largest vector payload: cycles times the summed widths of all ports.
maxVectorBits :: Integer
maxVectorBits = 2 ^ (18 :: Int)

-- | Largest normal form the normalizer produces; checked while inlining.
maxNormalBinds :: Int
maxNormalBinds = 65536

-- | Default wall-clock limit for each external tool run.
defaultToolTimeoutSeconds :: Int
defaultToolTimeoutSeconds = 300

-- | Default wall-clock limit for reference simulation in @gin sim@ and
-- @gin validate@.
defaultSimTimeoutSeconds :: Int
defaultSimTimeoutSeconds = 600
