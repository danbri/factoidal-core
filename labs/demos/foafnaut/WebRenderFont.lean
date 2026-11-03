import WebRender
import L4Factoidal.Rendering.FontFace

/-! Supplied real-font data frontend. Parsing, CSS, word lookup, line breaking,
baselines and scene construction run in Lean. Only font shaping/data extraction
belongs to the separately vetted HarfBuzz/FreeType adapter. -/
namespace WebRenderFont
open L4Factoidal

def render (html fontData : String) (width height : Nat) :
    Except String (Rendering.Scene × Array Rendering.Layout.Box × Rendering.FontProvider.Face) := do
  if html.length > 1048576 then throw "unsupported HTML input exceeding 1048576 characters"
  let face ← Rendering.FontProvider.Face.decode fontData
  let dom := DOM.parseHtmlDocument html
  let rules ← Rendering.CSS.parse (WebRender.styleSource dom)
  let (scene,boxes) ← Rendering.Layout.render dom rules (.ofFace face) (WebRender.embedding dom) width height
  return (scene,boxes,face)

@[export web_render_font_compile]
def compile (html fontData : String) (width height : UInt32) : String :=
  match render html fontData width.toNat height.toNat with
  | .error message => WebRender.errorJSON message
  | .ok (scene,boxes,face) =>
    match WebRender.artifact scene boxes (some face) with
    | .error message => WebRender.errorJSON message
    | .ok value => value
end WebRenderFont
