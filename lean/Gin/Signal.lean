/-!
# Signals

A shallow embedding of synchronous circuits. A `Signal dom α` is the stream
of values a wire carries at clock cycles `0, 1, 2, …` of the clock domain
`dom`; circuits are ordinary Lean functions between signals, built from the
combinators below. The definitions transcribe `docs/semantics.md` directly,
so a theorem about a circuit is a theorem about the cycle semantics every
later stage of gin must preserve.

Only the combinators in this file, plus combinational functions on `Bool`,
`BitVec n` and products, are understood by the exporter (`Gin.Export`).
-/

namespace Gin

/-- A synchronous clock domain: one clock (rising edge) and one synchronous,
active-high reset. The period is informational and is carried into the
generated hardware. -/
structure Domain where
  /-- Name of the domain, as it appears in the core IR. -/
  name : String
  /-- Clock period in picoseconds. -/
  periodPs : Nat

/-- The default clock domain: 100 MHz. -/
def System : Domain := ⟨"System", 10000⟩

/-- The values a wire in domain `dom` carries at cycles `0, 1, 2, …`.

This is a plain definition rather than an abbreviation on purpose: the
exporter recognises it by name and must never see it unfolded to a function
type. -/
def Signal (_dom : Domain) (α : Type) := Nat → α

variable {dom : Domain} {α β γ δ σ ι ο : Type}

/-- The signal that carries `x` at every cycle. -/
def Signal.pure (x : α) : Signal dom α := fun _ => x

/-- Apply a combinational function at every cycle. -/
def lift (f : α → β) (s : Signal dom α) : Signal dom β := fun t => f (s t)

/-- Apply a two-argument combinational function at every cycle. -/
def lift2 (f : α → β → γ) (a : Signal dom α) (b : Signal dom β) : Signal dom γ :=
  fun t => f (a t) (b t)

/-- Apply a three-argument combinational function at every cycle. -/
def lift3 (f : α → β → γ → δ) (a : Signal dom α) (b : Signal dom β) (c : Signal dom γ) :
    Signal dom δ :=
  fun t => f (a t) (b t) (c t)

/-- A register with initial value `v`: it outputs `v` at cycle 0 and the
previous cycle's input afterwards (`reg(0) = v`, `reg(t+1) = s(t)`).
The initial value must be a literal for the design to be exportable. -/
def register (v : α) (s : Signal dom α) : Signal dom α :=
  fun t => if t = 0 then v else s (t - 1)

/-- The state sequence of the Mealy machine `mealy f v i`:
`st(0) = v` and `st(t+1) = (f (st t) (i t)).1`. -/
def mealyState (f : σ → ι → σ × ο) (v : σ) (i : Signal dom ι) : Nat → σ
  | 0 => v
  | t + 1 => (f (mealyState f v i t) (i t)).1

/-- A Mealy machine with step function `f` and initial state `v`. At cycle
`t` it outputs `(f (st t) (i t)).2`, where `st` is `mealyState f v i`.
The initial state must be a literal for the design to be exportable. -/
def mealy (f : σ → ι → σ × ο) (v : σ) (i : Signal dom ι) : Signal dom ο :=
  fun t => (f (mealyState f v i t) (i t)).2

@[simp] theorem pure_apply (x : α) (t : Nat) : (Signal.pure x : Signal dom α) t = x := rfl

@[simp] theorem lift_apply (f : α → β) (s : Signal dom α) (t : Nat) :
    lift f s t = f (s t) := rfl

@[simp] theorem lift2_apply (f : α → β → γ) (a : Signal dom α) (b : Signal dom β) (t : Nat) :
    lift2 f a b t = f (a t) (b t) := rfl

@[simp] theorem lift3_apply (f : α → β → γ → δ) (a : Signal dom α) (b : Signal dom β)
    (c : Signal dom γ) (t : Nat) : lift3 f a b c t = f (a t) (b t) (c t) := rfl

@[simp] theorem register_zero (v : α) (s : Signal dom α) : register v s 0 = v := rfl

@[simp] theorem register_succ (v : α) (s : Signal dom α) (t : Nat) :
    register v s (t + 1) = s t := rfl

@[simp] theorem mealyState_zero (f : σ → ι → σ × ο) (v : σ) (i : Signal dom ι) :
    mealyState f v i 0 = v := rfl

@[simp] theorem mealyState_succ (f : σ → ι → σ × ο) (v : σ) (i : Signal dom ι) (t : Nat) :
    mealyState f v i (t + 1) = (f (mealyState f v i t) (i t)).1 := rfl

theorem mealy_apply (f : σ → ι → σ × ο) (v : σ) (i : Signal dom ι) (t : Nat) :
    mealy f v i t = (f (mealyState f v i t) (i t)).2 := rfl

/-- The defining equation of `mealy` in `docs/semantics.md`: the next state
and the current output are the two halves of one step. -/
theorem mealy_step (f : σ → ι → σ × ο) (v : σ) (i : Signal dom ι) (t : Nat) :
    (mealyState f v i (t + 1), mealy f v i t) = f (mealyState f v i t) (i t) := rfl

end Gin
