import WebRender
namespace WebRenderCurveTests
open L4Factoidal
private def source (path : String) := "<style>body{margin:0}svg{display:block;width:32px;height:32px}</style><svg viewBox='0 0 32 32'><path d='" ++ path ++ "' fill='red'/></svg>"
private def quadratic := source "M0 32 Q16 0 32 32Z"
private def cubic := source "M0 32 C0 0 32 0 32 32Z"
private def pixel (html : String) (x y : Nat) : Except String (Float × Float × Float) := do
  let (scene,_) ← WebRender.render html 32 32
  let native ← WebRenderSVG.toScene scene
  let color := native.samplePixel x y
  return (color.r,color.g,color.b)
#guard (pixel quadratic 16 24).toOption == some (1,0,0)
#guard (pixel quadratic 16 8).toOption == some (1,1,1)
#guard (pixel cubic 16 16).toOption == some (1,0,0)
#guard (pixel cubic 16 4).toOption == some (1,1,1)
private def retained : Except String (Float × Float) := do
  let (scene,_) ← WebRender.render quadratic 32 32
  let some item := (Rendering.Node.lowerList Rendering.identity [] scene.tree).head? | throw "missing paint"
  let .path [.path _ (.quadratic control _ :: _) true] := item.primitive.geometry | throw "canonical quadratic was lost"
  return (control.x,control.y)
#guard retained.toOption == some (16,0)
private def overBudget : Rendering.Scene := {
  width := 32,height := 32,mapping := {viewportWidth := 32,viewportHeight := 32},
  tree := [.paint ⟨none,{geometry := .path [.path ⟨0,0⟩ (List.replicate 513 (.line ⟨0,0⟩)) true]}⟩]}
#guard (WebRenderSVG.toScene overBudget).toOption.isNone
end WebRenderCurveTests
