import SVG
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

open L4Factoidal.JSON

/-- Admission only: render the unchanged original SVG through the Lean SVG
frontend. A compiled scene is not a visual-conformance pass. -/
def main (paths : List String) : IO UInt32 := do
  for path in paths do
    let source : Except String String ← try pure (.ok (← IO.FS.readFile path))
      catch error => pure (.error (toString error))
    let .ok source := source | do
      IO.println (Json.object [
        ("file", .string ((System.FilePath.mk path).fileName.getD path)),
        ("admission", .string "UNAVAILABLE"),
        ("error", .string "Input cannot enter the UTF-8 String API; XML byte decoding is not wired"),
        ("visualConformance", .string "NOT_RUN")]).toString
      continue
    let .ok result := parseJson (NativeSVG.compile source 480 360)
      | throw (IO.userError "SVG compiler returned invalid JSON")
    let error := result.field? "error"
    IO.println (Json.object [
      ("file", .string ((System.FilePath.mk path).fileName.getD path)),
      ("admission", .string (if error.isSome then "UNSUPPORTED" else "ADMITTED")),
      ("error", error.getD .null),
      ("visualConformance", .string "NOT_RUN")]).toString
  return 0
