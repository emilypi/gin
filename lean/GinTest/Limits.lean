import Gin.Signal
import GinTest.Agree
import GinTest.Util

/-!
The resource limits of the IR at their boundaries: the largest width, the
largest vector payload and the widest concatenation are accepted, and one
step past each is refused.
-/

open Lean Meta Gin Gin.Export GinTest

namespace GinTest.Limits

/-- The widest ports the IR admits. -/
def widest (x : Signal System (BitVec 4096)) : Signal System (BitVec 4096) :=
  lift (fun a => ~~~a + 1) x

/-- A concatenation exactly `maxWidth` bits wide. -/
def concatAtMax (x : Signal System (BitVec 4000)) (y : Signal System (BitVec 96)) :
    Signal System (BitVec 4096) :=
  lift2 (fun a b => a ++ b) x y

/-- A concatenation one bit wider than `maxWidth`, narrowed again so that
every port is in range. -/
def concatOverMax (x : Signal System (BitVec 4000)) (y : Signal System (BitVec 97)) :
    Signal System (BitVec 8) :=
  lift2 (fun a b => (a ++ b).setWidth 8) x y

/-- 545 bits of ports: 481 cycles carry `2^18 + 1` bits. -/
def ports545 (x : Signal System (BitVec 544)) : Signal System Bool :=
  lift (fun a => a == 0) x

end GinTest.Limits

open GinTest.Limits in
run_meta do
  -- 32 cycles of a 4096-bit input and a 4096-bit output carry exactly 2^18 bits
  unless 32 * (4096 + 4096) == maxVectorPayloadBits do throwError "payload arithmetic"
  checkAgrees { testEntry ``widest ["x"] ["y"] (.of1 widest) with cycles := 32 }
  checkAgrees { testEntry ``concatAtMax ["x", "y"] ["o"] (.of2 concatAtMax) with cycles := 16 }
  expectError (translateDef ``concatOverMax {}) ["concatOverMax", "width 4097", "4096"]
  -- one bit over the payload bound
  unless 481 * (544 + 1) == maxVectorPayloadBits + 1 do throwError "payload arithmetic"
  let over := { testEntry ``ports545 ["x"] ["z"] (.of1 ports545) with cycles := 481 }
  let (top, _) ← translateTop over
  match exportVectors over top with
  | .ok _ => throwError "a payload of 2^18 + 1 bits was accepted"
  | .error msg =>
    unless containsStr msg "carry 262145 bits, more than 262144" do throwError msg
  -- and one cycle fewer is accepted
  checkAgrees { over with cycles := 480 }
