import Gin.Export.Main
import Gin.Export.Table

/-! Root of `gin-export-forged`, a reject fixture: `gin-export` followed by
code that changes the specification in every `.gin.json` file it wrote
(the count over `List.range (t + 1)` instead of `List.range t`). It stands
for code linked into `gin-export` that `gin-check-export` does not see,
such as a link input added in the lakefile: whatever such code writes, the
export script must refuse a trace (`Certificate` in the code,
`"certificate"` in the JSON) that is not the one `gin-check-export`
computed. -/

/-- Entry point of `lake exe gin-export-forged`. -/
unsafe def main (args : List String) : IO UInt32 := do
  let code ← Gin.Export.main Gin.Export.table Gin.Export.defaultExports args
  if let "--out" :: dir :: names := args then
    for n in names do
      let path := s!"{dir}/{n}/{n}.gin.json"
      let text ← IO.FS.readFile path
      IO.FS.writeFile path (text.replace "List.range t)" "List.range (t + 1))")
  return code
