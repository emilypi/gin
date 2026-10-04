import Lean
import Gin.Export.Certificate
import GinReject.BadUnexpander

/-!
# The certificate of `GinReject.BadUnexpander` shows the real claim

Lean's pretty printer, fooled by the fixture's `app_unexpander`, shows the
specification as `BadUnexpander.spec`. The certificate's fixed printer
names `BadUnexpander.specR` and lists its definition. Built by
`scripts/export-examples.sh --check-rejects`; the build fails if a check
does.
-/

open Lean Meta

-- [lean-printer] The unexpander fools the pretty printer, but not the
-- certificate: its statement names specR and its definitions show specR's
-- body.
run_meta do
  let thm := ``BadUnexpander.bad_correct
  let pp := toString (← ppExpr (← getConstInfo thm).type)
  unless (pp.splitOn "BadUnexpander.spec ").length > 1 && (pp.splitOn "specR").length == 1 do
    throwError "the unexpander did not take effect: {pp}"
  let c ← Gin.Export.certify thm ``BadUnexpander.bad [``BadUnexpander.bad]
  let statement := "∀ (en : Gin.Signal Gin.System Bool) (t : Nat), \
    BadUnexpander.bad en t = BadUnexpander.specR en t"
  unless c.statement == statement do
    throwError "statement {c.statement}, expected {statement}"
  let body := "BadUnexpander.specR : Gin.Signal Gin.System Bool → Nat → BitVec 8 := \
    fun (_en : Gin.Signal Gin.System Bool) (_t : Nat) => (0 : BitVec 8)"
  unless c.specDefinitions.map (fun d => (d.name, d.body)) == [("BadUnexpander.specR", body)] do
    throwError "spec definitions {c.specDefinitions.map (fun d => (d.name, d.body))}"
