import Gin.Signal

/-!
# Reject fixture: a proof by `native_decide`

Not part of the default build. `native_decide` trusts the compiler rather
than the kernel: the proof rests on a generated `._native.` axiom, which the
exporter must refuse and name. `scripts/export-examples.sh --check-rejects`
checks that it does and that nothing is written.
-/

open Gin

namespace BadNative

/-- The enable counter of `Gin.Examples.Counter`. -/
def bad (en : Signal System Bool) : Signal System (BitVec 8) :=
  mealy (fun s e => (if e then s + 1 else s, s)) 0 en

/-- A true statement about the first eight cycles, proved by evaluating
compiled code. -/
theorem bad_correct :
    (List.range 8).map (bad (Signal.pure true)) = (List.range 8).map (BitVec.ofNat 8) := by
  native_decide

end BadNative
