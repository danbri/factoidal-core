import SVG
import SVGText
import SVGScript
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

open L4Factoidal.JSON

/-- Acceptance only: render the unchanged original SVG through the Lean SVG
frontend. A compiled scene is not a visual-conformance pass.

The first argument is the SFNT font file that draws SVG text (the font of HTML text in
the engine; CSS Fonts 4 §5 fallback for `font-family` names the probe does not hold).
SVG text is lowered to glyph paths with it, strictly: any approximation in the lowering
refuses the file (`NativeSVGText.parseWithFonts`). The other arguments are SVG files.

A file with `script`, `handler` or XML Events `listener` elements is first run by
`NativeSVGScript.run` (BubblePopJS on the document's DOM; SVG Tiny 1.2 chapter 15), and the
document after its scripts and `load` events is what is compiled. A refusal of that step
refuses the file, with its reason. An external script (`xlink:href`) is read from the file's
directory's parent and below only (the acceptance runner puts the suite's `images/` there),
as UTF-8; any other reference is not read. -/
/-- The text of external script `href` of the SVG file `path`: the file the reference names
relative to the file's directory, only when its real path is under the directory above it. -/
def scriptText (path href : String) : IO (Option String) := do
  if href.contains ':' || href.startsWith "/" then return none
  let dir := (System.FilePath.mk path).parent.getD "."
  let rootDir := dir.parent.getD dir
  let candidate := dir / ((href.splitOn "#").headD "")
  if !(← candidate.pathExists) then return none
  let real ← IO.FS.realPath candidate
  let root ← IO.FS.realPath rootDir
  if !real.toString.startsWith (root.toString ++ "/") then return none
  return String.fromUTF8? (← IO.FS.readBinFile real)

def main (args : List String) : IO UInt32 := do
  let fontPath :: paths := args | throw (IO.userError "usage: SvgTinyProbe FONT SVG...")
  let fontBytes ← IO.FS.readBinFile fontPath
  let font ← match L4Factoidal.Rendering.SfntProfile.Font.read fontBytes "sans-serif" "" with
    | .ok font => pure font
    | .error error => throw (IO.userError s!"font {fontPath}: {error}")
  -- one realm for every file: each run starts its own page session on it
  let realm := L4Factoidal.WasmVM.Hosts.LeanJS.prepareSource
  for path in paths do
    let source : Except String String ← try pure (.ok (← IO.FS.readFile path))
      catch error => pure (.error (toString error))
    let .ok source := source | do
      IO.println (Json.object [
        ("file", .string ((System.FilePath.mk path).fileName.getD path)),
        ("acceptance", .string "UNAVAILABLE"),
        ("error", .string "Input cannot enter the UTF-8 String API; XML byte decoding is not wired"),
        ("visualConformance", .string "NOT_RUN")]).toString
      continue
    let mut texts : List (String × String) := []
    if NativeSVGScript.hasScripting source then
      for (href, _) in NativeSVGScript.scriptRequests source "file:///probe/svg/x.svg" do
        if let some text ← scriptText path href then texts := (href, text) :: texts
    let fetch := fun (h : String) => (texts.find? (·.1 == h)).map (·.2)
    let scripted : Except String String :=
      if NativeSVGScript.hasScripting source then do
        let base ← realm
        NativeSVGScript.run base source "about:svg" fetch
      else .ok source
    let .ok source := scripted | do
      IO.println (Json.object [
        ("file", .string ((System.FilePath.mk path).fileName.getD path)),
        ("acceptance", .string "REFUSED"),
        ("error", .string (match scripted with | .error e => e | .ok _ => "")),
        ("visualConformance", .string "NOT_RUN")]).toString
      continue
    let .ok result := parseJson (NativeSVGText.compileWithFonts #[font] source 480 360)
      | throw (IO.userError "SVG compiler returned invalid JSON")
    let error := result.field? "error"
    IO.println (Json.object [
      ("file", .string ((System.FilePath.mk path).fileName.getD path)),
      ("acceptance", .string (if error.isSome then "REFUSED" else "ACCEPTED")),
      ("error", error.getD .null),
      ("visualConformance", .string "NOT_RUN")]).toString
  return 0
