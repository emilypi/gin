import Gin.Signal

/-! A small circuit with competing adder and multiplexer implementations. -/

open Gin

namespace MuxAdd

/-- Select two packed 2-bit operands and add them modulo four. -/
def muxadd (flag : Signal System Bool) (lanes : Signal System (BitVec 8)) :
    Signal System (BitVec 2) :=
  lift2 (fun s p =>
    (if s then p.extractLsb' 0 2 else p.extractLsb' 2 2) +
    (if s then p.extractLsb' 4 2 else p.extractLsb' 6 2)) flag lanes

/-- The selected sum of the two lanes in the packed input. -/
def spec (flag : Signal System Bool) (lanes : Signal System (BitVec 8))
    (t : Nat) : BitVec 2 :=
  if flag t then
    (lanes t).extractLsb' 0 2 + (lanes t).extractLsb' 4 2
  else
    (lanes t).extractLsb' 2 2 + (lanes t).extractLsb' 6 2

/-- The source implementation meets its specification on every cycle. -/
theorem muxadd_correct : ∀ flag lanes t, muxadd flag lanes t = spec flag lanes t := by
  intro flag lanes t
  cases h : flag t <;> simp [muxadd, spec, lift2, h]

end MuxAdd
