import Gin.Signal
import GinTest.Agree
import GinTest.Util

/-!
Everything outside the supported fragment is an error that names the
offending constant, type or term. None of these may translate silently.
-/

open Lean Meta Gin Gin.Export GinTest

namespace GinTest.Unsupported

/-- Natural-number arithmetic is not hardware. -/
def natArith (x : Signal System Nat) : Signal System Nat := lift (· + 1) x

/-- Converting to `Nat` and back is not hardware either. -/
def viaNat (x : Signal System (BitVec 8)) : Signal System (BitVec 8) :=
  lift (fun a => BitVec.ofNat 8 (a.toNat + 1)) x

/-- `+` at a non-standard instance must not be read as `bv.add`. -/
def oddAdd (x y : Signal System (BitVec 8)) : Signal System (BitVec 8) :=
  lift2 (fun a b => @HAdd.hAdd _ _ _ (@instHAdd _ ⟨BitVec.sub⟩) a b) x y

/-- `==` at a hand-written `BEq` instance must not be read as `bv.eq`. -/
def oddBeq (x y : Signal System (BitVec 8)) : Signal System Bool :=
  lift2 (fun a b => @BEq.beq _ ⟨fun _ _ => true⟩ a b) x y

/-- `<` at a hand-written order must not be read as `bv.ult`. -/
def oddLt (x y : Signal System (BitVec 8)) : Signal System Bool :=
  lift2 (fun a b => @decide (@LT.lt _ ⟨fun a b => b.toNat < a.toNat⟩ a b) (Nat.decLt _ _)) x y

/-- A shift by a signal amount. -/
def variableShift (x y : Signal System (BitVec 8)) : Signal System (BitVec 8) :=
  lift2 (fun a b => a <<< b) x y

/-- A structurally recursive helper. -/
def repeatInc : Nat → BitVec 8 → BitVec 8
  | 0, x => x
  | n + 1, x => repeatInc n (x + 1)

/-- Uses the recursive helper. -/
def usesRecursion (x : Signal System (BitVec 8)) : Signal System (BitVec 8) := lift (repeatInc 3) x

/-- A helper defined by well-founded recursion. -/
def incLog (n : Nat) (x : BitVec 8) : BitVec 8 := if n < 2 then x else incLog (n / 2) (x + 1)
termination_by n
decreasing_by omega

/-- Uses the well-founded helper. -/
def usesWf (x : Signal System (BitVec 8)) : Signal System (BitVec 8) := lift (incLog 8) x

/-- A width computed by a function the exporter cannot evaluate. -/
def log2 (n : Nat) : Nat := if n < 2 then 0 else log2 (n / 2) + 1

/-- Shifts by a computed amount. -/
def computedShift (x : Signal System (BitVec 8)) : Signal System (BitVec 8) :=
  lift (fun (a : BitVec 8) => a <<< log2 8) x

/-- A pattern match with two alternatives. -/
def boolMatch (x : Signal System Bool) : Signal System (BitVec 8) :=
  lift (fun b => match b with | true => 1 | false => 0) x

/-- A nested pair pattern. -/
def nestedPattern (x : Signal System (BitVec 8 × BitVec 8 × BitVec 8)) : Signal System (BitVec 8) :=
  lift (fun p => let (a, b, c) := p; a + b + c) x

/-- A register whose initial value is computed. -/
def computedInit (x : Signal System (BitVec 8)) : Signal System (BitVec 8) :=
  register (BitVec.ofNat 8 3 + 1) x

/-- A dependent if-then-else. -/
def dependentIf (x : Signal System (BitVec 8)) : Signal System (BitVec 8) :=
  lift (fun a => if _h : a = 0 then 1 else a) x

/-- Increments a byte. -/
def incByte (a : BitVec 8) : BitVec 8 := a + 1

/-- A function-valued `if` that is never applied: there is no IR value of
function type to choose. -/
def unappliedFunIf (x : Signal System (BitVec 8)) : Signal System (BitVec 8) :=
  lift (if (2 : BitVec 8) < 3 then incByte else id) x

/-- An `if` choosing between signals. -/
def signalIf (x : Signal System (BitVec 8)) : Signal System (BitVec 8) :=
  bif (1 : BitVec 8) == 1 then x else register 0 x

/-- An opaque constant has no definition to translate. -/
opaque mystery : BitVec 8 → BitVec 8

/-- Uses the opaque constant. -/
def usesOpaque (x : Signal System (BitVec 8)) : Signal System (BitVec 8) := lift mystery x

/-- Too wide. -/
def tooWide (x : Signal System (BitVec 5000)) : Signal System (BitVec 5000) := x

/-- Zero bits wide. -/
def zeroWide (x : Signal System (BitVec 0)) : Signal System (BitVec 0) := x

/-- A type outside the fragment. -/
def withOption (x : Signal System (Option Bool)) : Signal System (Option Bool) := x

/-- An extract reaching past the top bit. -/
def badExtract (x : Signal System (BitVec 8)) : Signal System (BitVec 4) :=
  lift (fun a => a.extractLsb 9 6) x

/-- A structure literal (the constructor has no definition). -/
def ofFin (x : Signal System (BitVec 8)) : Signal System (BitVec 8) :=
  lift (fun a => BitVec.ofFin (a.toFin + 1)) x

/-- A second domain with the same name but another period. -/
def Fast : Domain := ⟨"System", 5000⟩

/-- Mixes two clock domains. -/
def mixedDomains (x : Signal System Bool) (_y : Signal Fast Bool) : Signal System Bool := x

/-- A 100 Hz clock: its period in picoseconds is larger than any number gin
reads. -/
def Slow : Domain := ⟨"Slow", 10000000000⟩

/-- A circuit in the slow domain. -/
def slowClock (x : Signal Slow Bool) : Signal Slow Bool := x

/-- The slowest clock gin reads, 2^31 - 1 ps. -/
def Slowest : Domain := ⟨"Slowest", 2147483647⟩

/-- A circuit in the slowest domain. -/
def slowestClock (x : Signal Slowest Bool) : Signal Slowest Bool := x

end GinTest.Unsupported

open GinTest.Unsupported in
run_meta do
  let tr (n : Name) := translateDef n {}
  expectError (tr ``natArith) ["GinTest.Unsupported.natArith", "unsupported type Nat"]
  expectError (tr ``viaNat) ["BitVec.ofNat"]
  expectError (tr ``oddAdd) ["HAdd.hAdd", "standard instance"]
  expectError (tr ``oddBeq) ["BEq.beq", "DecidableEq"]
  expectError (tr ``oddLt) ["standard order"]
  expectError (tr ``variableShift) ["HShiftLeft.hShiftLeft"]
  expectError (tr ``usesRecursion) ["repeatInc"]
  expectError (tr ``usesWf) ["incLog"]
  expectError (tr ``computedShift) ["shift amount GinTest.Unsupported.log2 8 is not a numeral"]
  expectError (tr ``boolMatch) ["pattern match", "boolMatch.match_1"]
  expectError (tr ``nestedPattern) ["pattern match", "nestedPattern.match_1"]
  expectError (tr ``computedInit) ["must be literals"]
  expectError (tr ``dependentIf) ["dependent if-then-else"]
  expectError (tr ``unappliedFunIf) ["unappliedFunIf", "if-then-else", "incByte", "only Bool, BitVec"]
  expectError (tr ``signalIf) ["if-then-else", "Signal", "between signals"]
  expectError (tr ``usesOpaque) ["GinTest.Unsupported.mystery", "no definition"]
  expectError (tr ``tooWide) ["width 5000"]
  expectError (tr ``zeroWide) ["width 0"]
  expectError (tr ``withOption) ["unsupported type Option"]
  expectError (tr ``badExtract) ["extractLsb 9 6"]
  expectError (tr ``ofFin) ["BitVec.ofFin"]
  expectError (translateTop (testEntry ``mixedDomains ["x", "y"] ["o"] (.of2 mixedDomains)))
    ["mixes clock domains"]
  expectError (translateTop (testEntry ``slowClock ["x"] ["o"] (.of1 slowClock)))
    ["GinTest.Unsupported.Slow", "\"Slow\"", "period of 10000000000 ps", "at most 2147483647 ps"]
  -- the bound itself is accepted
  let (top, _) ← translateTop (testEntry ``slowestClock ["x"] ["o"] (.of1 slowestClock))
  unless top.domain == { name := "Slowest", periodPs := 2147483647 } do
    throwError "the slowest domain was exported as {repr top.domain}"
