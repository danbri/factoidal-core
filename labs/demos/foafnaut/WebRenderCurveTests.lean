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
  tree := [.paint ⟨none,{geometry := .path [.path ⟨0,0⟩ (List.replicate (NativeSVGPath.maxPathPoints+1) (.line ⟨0,0⟩)) true]}⟩]}
#guard (WebRenderSVG.toScene overBudget).toOption.isNone

-- Original child indices include text/comments, and hidden SVG roots still
-- contribute document-wide fragment targets. href wins over xlink:href.
private def crossRoot := "<style>body{margin:0}svg{display:block}</style><!--before--><svg style='display:none'><circle id='c' cx='16' cy='16' r='16' fill='orange'/><rect id='r' width='32' height='32' fill='red'/></svg>\n<!--between--><svg width='32' height='32' xmlns:xlink='http://www.w3.org/1999/xlink'><use href='#r' xlink:href='#c'/></svg>"
#guard (pixel crossRoot 0 0).toOption == some (1,0,0)
#guard (pixel crossRoot 31 31).toOption == some (1,0,0)
#guard (pixel (crossRoot.replace "href='#r'" "href='#c'") 0 0).toOption == some (1,1,1)
-- Resource and outer-root style boundaries must be explicit failures.
#guard (WebRender.render "<link rel='stylesheet' href='x.css'><svg/>" 32 32).toOption.isNone
#guard (WebRender.render "<base href='https://example.org/'><svg/>" 32 32).toOption.isNone
#guard (WebRender.render "<svg><style>svg{color:red}</style></svg>" 32 32).toOption.isNone
#guard (pixel "<style>body{margin:0}svg{display:block;width:32px;height:32px}</style><svg><style>rect{fill:red}</style><rect width='32' height='32'/></svg>" 0 0).toOption == some (1,0,0)
end WebRenderCurveTests
