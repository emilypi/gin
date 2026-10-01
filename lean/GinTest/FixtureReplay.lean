import Gin

/-!
The shipped examples reproduce the hand-written vectors of the Haskell test
fixtures (`test/Gin/Examples.hs`) when their inputs are replayed.
-/

open Gin

namespace GinTest.FixtureReplay

/-- The signal that carries `xs[t]` at cycle `t` and `default` afterwards. -/
def ofList {α : Type} [Inhabited α] (xs : List α) : Signal System α := fun t => xs[t]!

-- [lean-fixture-replay] counter: en = 1 1 0 1 0 0 1 1; count = 0 1 2 2 3 3 3 4.
#guard (List.range 8).map (fun t =>
    (Counter.counter (ofList [true, true, false, true, false, false, true, true]) t).toNat)
  == [0, 1, 2, 2, 3, 3, 3, 4]

-- [lean-fixture-replay] mac: includes the wrap-around (65067 + 65025) mod 2^16 = 64556.
#guard (List.range 5).map (fun t =>
    (Mac.mac (ofList [3, 5, 255, 255, 0]) (ofList [4, 6, 255, 255, 0]) t).toNat)
  == [0, 12, 42, 65067, 64556]

-- [lean-fixture-replay] detector: b = 1 0 1 0 1 1 0 1; hit = 0 0 1 0 1 0 0 1.
#guard (List.range 8).map
    (Detector.detector (ofList [true, false, true, false, true, true, false, true]))
  == [false, false, true, false, true, false, false, true]

end GinTest.FixtureReplay
