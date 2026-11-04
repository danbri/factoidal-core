import L4Factoidal.Rendering.FontData

/-! Runtime check of actual external font JSON, separate from synthetic guards.
Run from formal/lean4 after building Rendering.FontData. -/
open L4Factoidal.Rendering.FontData
def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: check-font-data.lean FONT_DATA.json")
  let source ← IO.FS.readFile path
  match decode source with
  | .error message =>
    IO.eprintln message
    return 1
  | .ok word =>
    if word.glyphs.any (fun g => g.clusterChar >= g.clusterEndChar || g.clusterEndChar > word.text.length) then
      throw (IO.userError "decoded source cluster span is invalid")
    IO.println s!"font-data PASS: {word.fontSha256}, face{word.faceIndex}, {word.glyphs.size} glyphs, {word.outlines.size} outlines, {word.bitmaps.size} bitmaps, {word.direction}, {word.text.utf8ByteSize} UTF8 bytes"
    IO.println s!"source character spans: {word.glyphs.toList.map fun g => (g.clusterChar,g.clusterEndChar)}"
    return 0
