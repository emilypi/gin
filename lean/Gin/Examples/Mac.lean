import Gin.Signal

/-!
# Multiply-accumulate

Two 8-bit inputs are multiplied (as unsigned 16-bit numbers) and added into
a 16-bit accumulator every cycle. The output during cycle `t` is the
accumulator before cycle `t`'s product is added.
-/

open Gin

namespace Mac

/-- The implementation: the inputs are paired up and fed to a Mealy machine
whose state is the accumulator. -/
def mac (x y : Signal System (BitVec 8)) : Signal System (BitVec 16) :=
  mealy (fun (acc : BitVec 16) (p : BitVec 8 × BitVec 8) =>
      let acc' := acc + p.1.setWidth 16 * p.2.setWidth 16
      (acc', acc))
    0 (lift2 (·, ·) x y)

/-- The specification: the sum of the products of all strictly earlier
input pairs, modulo 2^16. -/
def spec (x y : Signal System (BitVec 8)) (t : Nat) : BitVec 16 :=
  BitVec.ofNat 16 ((List.range t).map (fun i => (x i).toNat * (y i).toNat)).sum

theorem step_eq (S : Nat) (a b : BitVec 8) :
    BitVec.ofNat 16 S + a.setWidth 16 * b.setWidth 16
      = BitVec.ofNat 16 (S + a.toNat * b.toNat) := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := a.toNat) (by omega), Nat.mod_eq_of_lt (a := b.toNat) (by omega)]
  omega

theorem state_eq (x y : Signal System (BitVec 8)) (t : Nat) :
    mealyState (fun (acc : BitVec 16) (p : BitVec 8 × BitVec 8) =>
      let acc' := acc + p.1.setWidth 16 * p.2.setWidth 16
      (acc', acc)) 0 (lift2 (·, ·) x y) t
      = BitVec.ofNat 16 ((List.range t).map (fun i => (x i).toNat * (y i).toNat)).sum := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [mealyState_succ, ih, List.range_succ, List.map_append, List.sum_append]
    simp only [lift2, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    exact step_eq _ _ _

/-- The refinement theorem: the accumulator meets its specification at every
cycle, for every pair of input streams. -/
theorem mac_correct : ∀ x y t, mac x y t = spec x y t := by
  intro x y t
  simp only [mac, spec, mealy_apply, state_eq]

end Mac
