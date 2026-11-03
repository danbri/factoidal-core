import WebRender
import L4Factoidal.Rendering.RdfView

namespace WebRenderRDF
open L4Factoidal

def render (source : String) (width height : Nat) : Except String (Rendering.Scene × Array Rendering.Layout.Box × Nat) := do
  let (graph,dom) ← Rendering.RdfView.parse source
  let (scene,boxes) ← WebRender.renderDOM dom width height (← WebRender.makeEmbedding dom)
  return (scene,boxes,graph.length)

@[export web_render_rdf_compile]
def compile (source : String) (width height : UInt32) : String :=
  match render source width.toNat height.toNat with
  | .error message => WebRender.errorJSON message
  | .ok (scene,boxes,count) =>
    match WebRender.artifact scene boxes with
    | .error message => WebRender.errorJSON message
    | .ok value => (value.dropEnd 1).toString ++ ",\"rdf\":{\"syntax\":\"N-Triples 1.1\",\"triples\":" ++ toString count ++ "}}"

end WebRenderRDF
