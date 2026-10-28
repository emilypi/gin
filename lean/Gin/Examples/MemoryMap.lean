import Gin.Signal

/-! A stateless word transform for the generated memory accelerator showcase. -/

open Gin

namespace MemoryMap

/-- Double each 8-bit word and add one, with modular overflow. -/
def memorymap (words : Signal System (BitVec 8)) : Signal System (BitVec 8) :=
  lift (fun word => word + word + 1) words

/-- The per-word memory transform, independent of request scheduling. -/
def spec (words : Signal System (BitVec 8)) (t : Nat) : BitVec 8 :=
  words t + words t + 1

/-- Source-cycle correctness of the pure word kernel. -/
theorem memorymap_correct : ∀ words t, memorymap words t = spec words t := by
  intro words t
  rfl

end MemoryMap
