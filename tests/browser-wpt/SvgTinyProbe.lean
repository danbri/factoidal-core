import SVG
import SVGText
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

open L4Factoidal.JSON

/-- Admission only: render the unchanged original SVG through the Lean SVG
frontend. A compiled scene is not a visual-conformance pass.

The first argument is the SFNT font file that draws SVG text (the font of HTML text in
the engine; CSS Fonts 4 §5 fallback for `font-family` names the probe does not hold).
SVG text is lowered to glyph paths with it, strictly: any approximation in the lowering
refuses the file (`NativeSVGText.parseWithFonts`). The other arguments are SVG files. -/
def main (args : List String) : IO UInt32 := do
  let fontPath :: paths := args | throw (IO.userError "usage: SvgTinyProbe FONT SVG...")
  let fontBytes ← IO.FS.readBinFile fontPath
  let font ← match L4Factoidal.Rendering.SfntProfile.Font.read fontBytes "sans-serif" "" with
    | .ok font => pure font
    | .error error => throw (IO.userError s!"font {fontPath}: {error}")
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
    let .ok result := parseJson (NativeSVGText.compileWithFonts #[font] source 480 360)
      | throw (IO.userError "SVG compiler returned invalid JSON")
    let error := result.field? "error"
    IO.println (Json.object [
      ("file", .string ((System.FilePath.mk path).fileName.getD path)),
      ("admission", .string (if error.isSome then "UNSUPPORTED" else "ADMITTED")),
      ("error", error.getD .null),
      ("visualConformance", .string "NOT_RUN")]).toString
  return 0
