import WebRenderSVG
import L4Factoidal.Rendering.FontFace
open L4Factoidal

def main (args : List String) : IO Unit := do
  let [input,output] := args | throw (IO.userError "usage: FontProviderAhemProbe FONT_DATA_JSON OUTPUT_ARTIFACT_JSON")
  let source ← IO.FS.readFile input
  let .ok face := Rendering.FontProvider.Face.decode ("[" ++ source ++ "]") | throw (IO.userError "actual Ahem font face rejected data")
  let .ok word := face.lookup "fi A" 20 | throw (IO.userError "actual Ahem shaped word/size unavailable")
  unless word.fontSha256 == "b719ecb31c5b21fc573c03f6421c74ac63c271a5a3ff841e34f9705fb94b8448" &&
      word.advance == 4000 && word.glyphs.size == 4 do
    throw (IO.userError "actual font identity/metrics mismatch")
  let scale := 20/word.unitsPerEm
  let nodes := word.glyphs.toList.flatMap fun glyph => glyph.geometry.map fun geometry =>
    Rendering.Node.paint ⟨none,{geometry,transform := ⟨scale,0,0,scale,glyph.x*scale,glyph.y*scale⟩}⟩
  let scene : Rendering.Scene := ⟨80,20,⟨1,1,0,0,0,0,80,20⟩,nodes,#[],#[]⟩
  let native := WebRenderSVG.toScene scene
  for (x,expected) in [(10,0),(30,0),(50,1),(70,0)] do
    let pixel := native.samplePixel x 10
    unless pixel.r == expected && pixel.g == expected && pixel.b == expected do
      throw (IO.userError s!"actual Ahem geometry mismatch at {x}")
  let .ok artifact := native.artifact | throw (IO.userError "actual Ahem artifact rejected")
  IO.FS.writeFile output artifact
  IO.println s!"ACTUAL_AHEM_PROVIDER_PASS glyphIDs={word.glyphs.toList.map (·.index)} advance={word.advance} paints={native.primitives.length}"
