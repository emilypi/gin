import Gin.Signal
import Gin.Export.Ir

/-!
# Test vectors

Vectors are computed by running the Lean definition of a circuit on
pseudo-random inputs from a fixed seed. They are the reference every later
stage of gin is checked against, so they come from the definition the
theorem is about, never from the exported IR.
-/

namespace Gin.Export

/-- SplitMix64, a small deterministic generator with well-mixed output. -/
structure Rng where
  /-- Generator state. -/
  state : UInt64
  deriving Repr, Inhabited

/-- The next 64 pseudo-random bits. -/
def Rng.next (g : Rng) : UInt64 × Rng :=
  let s := g.state + 0x9E3779B97F4A7C15
  let z := (s ^^^ (s >>> 30)) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  (z ^^^ (z >>> 31), ⟨s⟩)

/-- `n` pseudo-random bits, as a natural number below `2^n`. -/
def Rng.bits (g : Rng) (n : Nat) : Nat × Rng := Id.run do
  let mut g := g
  let mut v := 0
  for i in [0:(n + 63) / 64] do
    let (w, g') := g.next
    g := g'
    v := v + w.toNat * 2 ^ (64 * i)
  return (v % 2 ^ n, g)

/-- A scalar type that can sit on a top-entity port. -/
class PortValue (α : Type) where
  /-- The IR type of the port. -/
  ty : Ty
  /-- The IR value of a sample. -/
  toValue : α → Value
  /-- A uniformly distributed sample. -/
  draw : Rng → α × Rng

instance : PortValue Bool where
  ty := .bool
  toValue := .bool
  draw g := let (w, g) := g.next; (w &&& 1 == 1, g)

instance {n : Nat} : PortValue (BitVec n) where
  ty := .bv n
  toValue x := .bv n x.toNat
  draw g := let (v, g) := g.bits n; (BitVec.ofNat n v, g)

/-- The output of a top definition: one scalar, or the right-nested product
`o₁ × (o₂ × … × oₙ)` of several. -/
class OutputValues (α : Type) where
  /-- Port types, in order. -/
  tys : List Ty
  /-- Port values, in order. -/
  values : α → List Value

instance {α : Type} [PortValue α] : OutputValues α where
  tys := [PortValue.ty α]
  values x := [PortValue.toValue x]

instance {α β : Type} [PortValue α] [OutputValues β] : OutputValues (α × β) where
  tys := PortValue.ty α :: OutputValues.tys β
  values p := PortValue.toValue p.1 :: OutputValues.values p.2

/-- How to compute the vectors of a circuit. -/
structure VectorSource where
  /-- Input port types the source produces, in order. -/
  inputs : List Ty
  /-- Output port types the source produces, in order. -/
  outputs : List Ty
  /-- `rows seed n`: the first `n` cycles for inputs drawn from `seed`. -/
  rows : UInt64 → Nat → Array Cycle

/-- The signal carrying `xs[t]` at cycle `t`. -/
def ofArray {dom : Domain} {α : Type} [Inhabited α] (xs : Array α) : Signal dom α := fun t => xs[t]!

/-- `n` samples, one per cycle. -/
def drawSamples {α : Type} [PortValue α] (n : Nat) (g : Rng) : Array α × Rng := Id.run do
  let mut g := g
  let mut xs := #[]
  for _ in [0:n] do
    let (x, g') := PortValue.draw g
    g := g'
    xs := xs.push x
  return (xs, g)

/-- Vectors of a one-input circuit. -/
def VectorSource.of1 {dom : Domain} {α ο : Type} [PortValue α] [Inhabited α] [OutputValues ο]
    (f : Signal dom α → Signal dom ο) : VectorSource where
  inputs := [PortValue.ty α]
  outputs := OutputValues.tys ο
  rows seed n :=
    let (xs, _) := drawSamples (α := α) n ⟨seed⟩
    let out := f (ofArray xs)
    (List.range n).toArray.map fun t =>
      { inputs := [PortValue.toValue xs[t]!], outputs := OutputValues.values (out t) }

/-- Vectors of a two-input circuit. Each cycle draws the first input, then
the second. -/
def VectorSource.of2 {dom : Domain} {α β ο : Type} [PortValue α] [Inhabited α] [PortValue β]
    [Inhabited β] [OutputValues ο] (f : Signal dom α → Signal dom β → Signal dom ο) :
    VectorSource where
  inputs := [PortValue.ty α, PortValue.ty β]
  outputs := OutputValues.tys ο
  rows seed n := Id.run do
    let mut g : Rng := ⟨seed⟩
    let mut xs : Array α := #[]
    let mut ys : Array β := #[]
    for _ in [0:n] do
      let (x, g') := PortValue.draw g
      let (y, g'') := PortValue.draw g'
      g := g''
      xs := xs.push x
      ys := ys.push y
    let out := f (ofArray xs) (ofArray ys)
    return (List.range n).toArray.map fun t =>
      { inputs := [PortValue.toValue xs[t]!, PortValue.toValue ys[t]!],
        outputs := OutputValues.values (out t) }

end Gin.Export
