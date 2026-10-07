import Gin.Signal
import Gin.Export.Ir

/-!
# Test vectors

Vectors are computed by running the Lean definition of a circuit on
pseudo-random inputs from a fixed seed. They are the reference every later
stage of gin is checked against, so they come from the definition the
theorem is about, never from the exported IR. They are how we validate the
translation: they answer "does the generated hardware still implement the
functionality described by Lean?"
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

/-- `n` pairs of samples, one per cycle; each cycle draws the first
component, then the second. -/
def drawPairs {α β : Type} [PortValue α] [PortValue β] (n : Nat) (g : Rng) :
    Array (α × β) × Rng := Id.run do
  let mut g := g
  let mut xs := #[]
  for _ in [0:n] do
    let (x, g') := PortValue.draw g
    let (y, g'') := PortValue.draw g'
    g := g''
    xs := xs.push (x, y)
  return (xs, g)

/-- Vectors of a circuit without inputs: its output on each cycle. -/
def VectorSource.of0 {dom : Domain} {ο : Type} [OutputValues ο] (f : Signal dom ο) :
    VectorSource where
  inputs := []
  outputs := OutputValues.tys ο
  rows _ n := (List.range n).toArray.map fun t => { inputs := [], outputs := OutputValues.values (f t) }

/-- Vectors of a one-input circuit. `gen n g` draws the `n` inputs; by
default they are uniformly distributed. -/
def VectorSource.of1 {dom : Domain} {α ο : Type} [PortValue α] [Inhabited α] [OutputValues ο]
    (f : Signal dom α → Signal dom ο) (gen : Nat → Rng → Array α × Rng := drawSamples) :
    VectorSource where
  inputs := [PortValue.ty α]
  outputs := OutputValues.tys ο
  rows seed n :=
    let (xs, _) := gen n ⟨seed⟩
    let out := f (ofArray xs)
    (List.range n).toArray.map fun t =>
      { inputs := [PortValue.toValue xs[t]!], outputs := OutputValues.values (out t) }

/-- Vectors of a two-input circuit. `gen n g` draws the `n` input pairs; by
default each cycle draws the first input, then the second, uniformly. -/
def VectorSource.of2 {dom : Domain} {α β ο : Type} [PortValue α] [Inhabited α] [PortValue β]
    [Inhabited β] [OutputValues ο] (f : Signal dom α → Signal dom β → Signal dom ο)
    (gen : Nat → Rng → Array (α × β) × Rng := drawPairs) : VectorSource where
  inputs := [PortValue.ty α, PortValue.ty β]
  outputs := OutputValues.tys ο
  rows seed n :=
    let (ps, _) := gen n ⟨seed⟩
    let xs := ps.map (·.1)
    let ys := ps.map (·.2)
    let out := f (ofArray xs) (ofArray ys)
    (List.range n).toArray.map fun t =>
      { inputs := [PortValue.toValue xs[t]!, PortValue.toValue ys[t]!],
        outputs := OutputValues.values (out t) }

/-- `n` triples of samples, one per cycle; each cycle draws the first
component, then the second, then the third. -/
def drawTriples {α β γ : Type} [PortValue α] [PortValue β] [PortValue γ] (n : Nat) (g : Rng) :
    Array (α × β × γ) × Rng := Id.run do
  let mut g := g
  let mut xs := #[]
  for _ in [0:n] do
    let (x, g') := PortValue.draw g
    let (y, g'') := PortValue.draw g'
    let (z, g''') := PortValue.draw g''
    g := g'''
    xs := xs.push (x, y, z)
  return (xs, g)

/-- Vectors of a three-input circuit. `gen n g` draws the `n` input
triples; by default each cycle draws the inputs in order, uniformly. -/
def VectorSource.of3 {dom : Domain} {α β γ ο : Type} [PortValue α] [Inhabited α] [PortValue β]
    [Inhabited β] [PortValue γ] [Inhabited γ] [OutputValues ο]
    (f : Signal dom α → Signal dom β → Signal dom γ → Signal dom ο)
    (gen : Nat → Rng → Array (α × β × γ) × Rng := drawTriples) : VectorSource where
  inputs := [PortValue.ty α, PortValue.ty β, PortValue.ty γ]
  outputs := OutputValues.tys ο
  rows seed n :=
    let (ts, _) := gen n ⟨seed⟩
    let xs := ts.map (·.1)
    let ys := ts.map (·.2.1)
    let zs := ts.map (·.2.2)
    let out := f (ofArray xs) (ofArray ys) (ofArray zs)
    (List.range n).toArray.map fun t =>
      { inputs := [PortValue.toValue xs[t]!, PortValue.toValue ys[t]!, PortValue.toValue zs[t]!],
        outputs := OutputValues.values (out t) }

/-! ## Biased generators

Uniform inputs rarely reach the corners of the examples: an 8-bit counter
with a fair enable needs about 512 cycles to wrap, and small products keep an
accumulator far from overflow. I bias the inputs towards that behaviour with
these generators, which stay reproducible from the seed. -/

/-- Enable inputs in runs: a high run of 1 to 512 cycles, then a low run of
1 to 8 cycles, repeated. Long high runs wrap an 8-bit counter. -/
def enableRuns (n : Nat) (g : Rng) : Array Bool × Rng := Id.run do
  let mut g := g
  let mut xs := #[]
  while xs.size < n do
    let (hi, g') := g.bits 9
    let (lo, g'') := g'.bits 3
    g := g''
    for _ in [0:hi + 1] do xs := xs.push true
    for _ in [0:lo + 1] do xs := xs.push false
  return (xs.extract 0 n, g)

/-- Bit-stream pieces for `patternBits`: an isolated `101`, an overlapping
`10101`, and filler. -/
def patternPieces : Array (List Bool) :=
  #[[true, false, true, false, false], [true, false, true, false, true], [false], [true, true],
    [false, false], [true], [false, true, true, false], [false, false, false]]

/-- A bit stream assembled from `patternPieces`, chosen uniformly, so that
`101` occurs both isolated and overlapping. -/
def patternBits (n : Nat) (g : Rng) : Array Bool × Rng := Id.run do
  let mut g := g
  let mut xs := #[]
  while xs.size < n do
    let (i, g') := g.bits 3
    g := g'
    xs := xs ++ (patternPieces[i]!).toArray
  return (xs.extract 0 n, g)

/-- A `w`-bit operand that is large three times in four (top bit set) and
uniform otherwise. -/
def largeOperand (w : Nat) (g : Rng) : BitVec w × Rng :=
  let (k, g) := g.bits 2
  let (v, g) := g.bits w
  (BitVec.ofNat w (if k == 0 || w == 0 then v else v ||| 2 ^ (w - 1)), g)

/-- Operand pairs from `largeOperand`; large products overflow an
accumulator within a few cycles. -/
def largeOperands {w v : Nat} (n : Nat) (g : Rng) : Array (BitVec w × BitVec v) × Rng := Id.run do
  let mut g := g
  let mut xs := #[]
  for _ in [0:n] do
    let (x, g') := largeOperand w g
    let (y, g'') := largeOperand v g'
    g := g''
    xs := xs.push (x, y)
  return (xs, g)

end Gin.Export
