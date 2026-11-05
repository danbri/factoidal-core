import L4Factoidal.Rendering.SfntShape

/-!
# `l4font-shape`: the font adapter with Lean shaping

Same arguments as `labs/demos/foafnaut/tools/font-shape.c`: FONT TEXT PX
[FACE [FEATURES]]. FEATURES is HarfBuzz whole-text feature syntax (`-liga,+test`). Lean reads the font, applies the font policy, and shapes the text.
It then runs the FreeType-only mode of `font-shape` (path in
`FACTOIDAL_FONT_SHAPE`) with the glyphs Lean chose, which adds outlines and
rasters and writes the `factoidal-font-data-v1` record with
`harfbuzzVersion` = "none (Lean shaper)". HarfBuzz does not run.
https://github.com/danbri/factoidal/issues/1233
-/
open L4Factoidal.Rendering

def main (args : List String) : IO UInt32 := do
  let (path, text, px, faceArg, featureArg) ← match args with
    | [p, t, s] => pure (p, t, s, "0", "")
    | [p, t, s, f] => pure (p, t, s, f, "")
    | [p, t, s, f, fs] => pure (p, t, s, f, fs)
    | _ => do IO.eprintln "usage: l4font-shape FONT_FILE UTF8_TEXT PIXEL_SIZE [FACE_INDEX [FEATURES]]"; return 2
  let some faceIndex := faceArg.toNat? | do IO.eprintln "l4font-shape: invalid face index"; return 2
  let some helper ← IO.getEnv "FACTOIDAL_FONT_SHAPE" | do IO.eprintln "l4font-shape: set FACTOIDAL_FONT_SHAPE to the font-shape executable"; return 2
  let b ← IO.FS.readBinFile path
  let result : Except String SfntShape.Shaped := do
    let dir ← FontPolicy.readDirectory b faceIndex
    let font : FontPolicy.FontIdentity := ⟨"", path, ""⟩
    let decision := FontPolicy.decide FontPolicy.Policy.standard font dir
    -- Refused tables are not read by the Lean shaper; say so on standard error below.
    let face ← SfntMetrics.Face.read b dir
    let settings ← SfntShape.parseFeatures featureArg
    let shaped ← SfntShape.shape b dir face text {} settings
    if !decision.fontUsed then throw "font.file.refused"
    pure shaped
  match result with
  | .error e => IO.eprintln s!"l4font-shape: {e}"; return 1
  | .ok shaped =>
    let spec := ";".intercalate (shaped.glyphs.toList.zip shaped.clusterBytes.toList |>.map fun (g, c) =>
      s!"{g.id},{c},{g.advance},0,{g.xOffset},{g.yOffset}")
    let out ← IO.Process.output { cmd := helper, args := #[path, text, px, faceArg, "--glyphs", shaped.script, spec] }
    if out.exitCode != 0 then
      IO.eprintln s!"l4font-shape: font-shape --glyphs failed: {out.stderr.trimAscii}"
      return 1
    -- Refusals name the font by the SHA-256 that font-shape already wrote in
    -- the record, so the font is not hashed twice.
    let dir := (FontPolicy.readDirectory b faceIndex).toOption.getD #[]
    let refusals := (FontPolicy.decide FontPolicy.Policy.standard ⟨"", path, ""⟩ dir).refusals
    unless refusals.isEmpty do
      let fileName := (path.splitOn "/").getLast!
      let sha := match (out.stdout.splitOn "\"fontSha256\":\"")[1]? with
        | some rest => (rest.splitOn "\"").head!
        | none => ""
      let font : FontPolicy.FontIdentity := ⟨(fileName.splitOn ".").head!, fileName, sha⟩
      for r in refusals do IO.eprintln { r with font }.render
    IO.print out.stdout
    return 0
