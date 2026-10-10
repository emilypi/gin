{-# LANGUAGE TemplateHaskell #-}

-- | Primitive operations of the gin core IR.
--
-- Semantics are specified in @docs/semantics.md@.
--
-- Typing rules (n, m, a, b range over widths >= 1; d over domains). A
-- prim node in the IR carries its full instantiated type ('EPrim'), and
-- the checker verifies it against these rules:
--
-- > bool.and, bool.or, bool.xor, bool.eq : Bool -> Bool -> Bool
-- > bool.not                              : Bool -> Bool
-- > bv.add, bv.sub, bv.mul                : bv n -> bv n -> bv n
-- > bv.and, bv.or, bv.xor                 : bv n -> bv n -> bv n
-- > bv.neg, bv.not                        : bv n -> bv n
-- > bv.shl k, bv.lshr k                   : bv n -> bv n          (any k >= 0)
-- > bv.eq, bv.ult, bv.ule                 : bv n -> bv n -> Bool
-- > bv.concat                             : bv a -> bv b -> bv (a + b)
-- > bv.extract hi lo                      : bv n -> bv (hi - lo + 1)   (n > hi >= lo)
-- > bv.zext m                             : bv n -> bv m          (m >= n)
-- > bv.ofBool                             : Bool -> bv 1
-- > sig.pure                              : t -> Signal d t       (t not a function or signal)
-- > sig.lift k                            : (t1 -> .. -> tk -> r) -> Signal d t1 -> .. -> Signal d tk -> Signal d r   (k >= 1)
-- > sig.register v                        : Signal d t -> Signal d t      (valueTy v == t)
-- > sig.mealy v                           : (s -> i -> (s, o)) -> Signal d i -> Signal d o   (valueTy v == s)
module Gin.Core.Prim
  ( PrimOp (..)
  , primName
  , primArity
  , isCombinational

    -- * Optics
  , _BoolAnd
  , _BoolOr
  , _BoolXor
  , _BoolNot
  , _BoolEq
  , _BvAdd
  , _BvSub
  , _BvMul
  , _BvNeg
  , _BvAnd
  , _BvOr
  , _BvXor
  , _BvNot
  , _BvShl
  , _BvLshr
  , _BvEq
  , _BvUlt
  , _BvUle
  , _BvConcat
  , _BvExtract
  , _BvZext
  , _BvOfBool
  , _SigPure
  , _SigLift
  , _SigRegister
  , _SigMealy
  ) where

import Control.Lens (makePrisms)
import Data.Text (Text)
import Gin.Core.Value (Value)
import Numeric.Natural (Natural)

data PrimOp
  = BoolAnd
  | BoolOr
  | BoolXor
  | BoolNot
  | BoolEq
  | BvAdd
  | BvSub
  | BvMul
  | BvNeg
  | BvAnd
  | BvOr
  | BvXor
  | BvNot
  | -- | Shift left by a constant amount.
    BvShl !Natural
  | -- | Logical shift right by a constant amount.
    BvLshr !Natural
  | BvEq
  | BvUlt
  | BvUle
  | -- | First argument supplies the most significant bits.
    BvConcat
  | -- | @BvExtract hi lo@, both inclusive.
    BvExtract !Natural !Natural
  | -- | Zero-extend to the given total width.
    BvZext !Natural
  | BvOfBool
  | SigPure
  | -- | Lift a k-ary combinational function pointwise over k signals.
    SigLift !Natural
  | -- | Delay by one cycle; the value is the output at cycle 0.
    SigRegister !Value
  | -- | Mealy machine with the given initial state.
    SigMealy !Value
  deriving stock (Eq, Ord, Show)

-- | The @op@ string used in the IR JSON (@docs/file-formats.md@).
primName :: PrimOp -> Text
primName = \case
  BoolAnd -> "bool.and"
  BoolOr -> "bool.or"
  BoolXor -> "bool.xor"
  BoolNot -> "bool.not"
  BoolEq -> "bool.eq"
  BvAdd -> "bv.add"
  BvSub -> "bv.sub"
  BvMul -> "bv.mul"
  BvNeg -> "bv.neg"
  BvAnd -> "bv.and"
  BvOr -> "bv.or"
  BvXor -> "bv.xor"
  BvNot -> "bv.not"
  BvShl _ -> "bv.shl"
  BvLshr _ -> "bv.lshr"
  BvEq -> "bv.eq"
  BvUlt -> "bv.ult"
  BvUle -> "bv.ule"
  BvConcat -> "bv.concat"
  BvExtract _ _ -> "bv.extract"
  BvZext _ -> "bv.zext"
  BvOfBool -> "bv.ofBool"
  SigPure -> "sig.pure"
  SigLift _ -> "sig.lift"
  SigRegister _ -> "sig.register"
  SigMealy _ -> "sig.mealy"

-- | Number of value arguments a saturated application takes.
primArity :: PrimOp -> Natural
primArity = \case
  BoolNot -> 1
  BvNeg -> 1
  BvNot -> 1
  BvShl _ -> 1
  BvLshr _ -> 1
  BvExtract _ _ -> 1
  BvZext _ -> 1
  BvOfBool -> 1
  SigPure -> 1
  SigLift k -> k + 1
  SigRegister _ -> 1
  SigMealy _ -> 2
  _ -> 2

-- | Combinational prims operate on plain values; the rest construct signals.
isCombinational :: PrimOp -> Bool
isCombinational = \case
  SigPure -> False
  SigLift _ -> False
  SigRegister _ -> False
  SigMealy _ -> False
  _ -> True

----------------------------------------------------------------------
-- Optics

makePrisms ''PrimOp
