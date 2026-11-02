import WebRenderSVG
import Font
import L4Factoidal.Rendering.Layout
import L4Factoidal.Rendering.Links

/-! HTML source → existing Lean DOM → computed CSS → layout → common scene.
The bitmap font is an explicit temporary profile, not font-backed shaping. -/
namespace WebRender
open L4Factoidal

private def quote (s : String) : String := "\"" ++ JSON.escapeString s ++ "\""
def errorJSON (message : String) : String := "{\"error\":" ++ quote message ++ "}"

def bitmapOutline (index : Nat) : List Rendering.Geometry := Id.run do
  let rows := NativeFont.bitmap (Char.ofNat index)
  let values := [rows.row0,rows.row1,rows.row2,rows.row3,rows.row4,rows.row5,rows.row6]
  let mut out := []
  for (bits,y) in values.zipIdx do
    for x in [:5] do
      if bits / (2^(4-x)) % 2 == 1 then
        out := .rect (Float.ofNat x) (Float.ofNat y) 1 1 :: out
  return out.reverse

def asciiFont : Rendering.Layout.FontProfile :=
  {family := "factoidal-ascii-bitmap-v1",unitsPerEm := 7,advance := 6, ascent := 7,descent := 0,outline := bitmapOutline, admits := fun n => 32 <= n && n <= 126}

/-- The HTML parser already adjusted element and foreign-attribute names.
This conversion transfers the semantic DOM values directly, without XML text. -/
def namespaceTree (dom : DOM.Dom) : Nat → Nat → Except String XML.NamespaceNode
  | 0, _ => throw "unsupported SVG embedding nesting depth (maximum 64)"
  | fuel+1, id => do
    let n := dom.get id
    if n.type == .element then
      let children ← n.kids.toList.mapM (namespaceTree dom fuel)
      let attrs := (n.attrs.toList.filter (fun a => a.ns != some DOM.xmlnsNS)).map fun a =>
        ({name := ⟨a.ns,a.lname⟩,value := a.value} : XML.NamespaceAttribute)
      return .element ⟨n.ns,n.lname⟩ attrs children
    else if n.type == .text || n.type == .cdata then return .other (.text n.data)
    else if n.type == .comment then return .other (.comment n.data)
    else throw "unsupported node in embedded SVG DOM"

/-- Embedded style sheets are read from their DOM text nodes. No host selector, computed-style or layout API participates in this pipeline. -/
def styleSource (dom : DOM.Dom) : String := Id.run do
  let mut sheets : List String := []
  for n in dom.nodes do
    if DOM.Dom.isHtmlElement n "style" then
      let text := n.kids.foldl (fun s id => s ++ (dom.get id).data) ""
      sheets := text :: sheets
  return String.intercalate "\n" sheets.reverse

/-- SVG embedding is injected only at the frontend adapter boundary. Tests can
supply an independent shape producer without changing CSS/layout semantics. -/
def renderDOM (dom : DOM.Dom) (width height : Nat)
    (embedding : Rendering.Layout.Embedding) : Except String (Rendering.Scene × Array Rendering.Layout.Box) := do
  let rules ← Rendering.CSS.parse (styleSource dom)
  Rendering.Layout.render dom rules asciiFont embedding width height

end WebRender

namespace WebRender
open L4Factoidal

/-- Until the native clip-stack extension lands, embedded viewports admit only
untransformed fill rectangles wholly inside their viewport. Other valid SVG
scenes remain accepted by the standalone shared-scene SVG producer. -/
private def embeddingNeedsNoClip (scene : NativeSVG.Scene) : Bool :=
  scene.primitives.all fun p =>
    let t := p.transform
    let identity := t.a == 1 && t.b == 0 && t.c == 0 && t.d == 1 && t.e == 0 && t.f == 0
    let noStroke := match p.style.stroke with | .none => true | _ => false
    match p.geometry with
    | .rect x y w h => identity && noStroke && x >= 0 && y >= 0 && w >= 0 && h >= 0 &&
      (x-scene.mapping.minX)*scene.mapping.sx+scene.mapping.tx >= 0 &&
      (y-scene.mapping.minY)*scene.mapping.sy+scene.mapping.ty >= 0 &&
      (x+w-scene.mapping.minX)*scene.mapping.sx+scene.mapping.tx <= scene.mapping.viewportWidth &&
      (y+h-scene.mapping.minY)*scene.mapping.sy+scene.mapping.ty <= scene.mapping.viewportHeight
    | _ => false

def embedding (dom : DOM.Dom) (id : Nat) (style : Rendering.CSS.Computed) (width height : Float) : Except String (List Rendering.Node) := do
  if Float.ofNat width.toUInt32.toNat != width || Float.ofNat height.toUInt32.toNat != height then
    throw "unsupported fractional embedded SVG viewport"
  let root ← namespaceTree dom 64 id
  let inherited : NativeSVG.Style := {currentColor := WebRenderSVG.toColor style.color, visible := style.visible}
  let scene ← NativeSVG.parseRoot root width.toUInt32.toNat height.toUInt32.toNat inherited
  if !embeddingNeedsNoClip scene then throw "unsupported embedded SVG requiring viewport clipping (clip extension pending)"
  let m := scene.mapping
  let transform : Rendering.Transform := ⟨m.sx,0,0,m.sy,m.tx-m.minX*m.sx,m.ty-m.minY*m.sy⟩
  return [.group none transform (WebRenderSVG.fromScene scene).tree]

def render (html : String) (width height : Nat) : Except String (Rendering.Scene × Array Rendering.Layout.Box) := do
  if html.length > 1048576 then throw "unsupported HTML input exceeding 1048576 characters"
  let dom := DOM.parseHtmlDocument html
  renderDOM dom width height (embedding dom)

private def array (xs : List String) := "[" ++ String.intercalate "," xs ++ "]"
private def runJSON (r : Rendering.GlyphRun) : String :=
  "{\"source\":" ++ toString r.source ++ ",\"font\":" ++ quote r.font ++ ",\"size\":" ++ toString r.fontSize ++
  ",\"text\":" ++ quote r.text ++ ",\"glyphs\":" ++ array (r.glyphs.toList.map fun g =>
    array [toString g.index,toString g.x,toString g.y,toString g.advance,toString g.clusterStart,toString g.clusterEnd]) ++ "}"
private def layoutJSON (s : Rendering.Scene) (boxes : Array Rendering.Layout.Box) : String :=
  "{\"profile\":\"lean-block-inline-ascii-bitmap-v1\",\"fontScope\":\"ASCII bitmap; no real font shaping\",\"boxes\":" ++
  array (boxes.toList.map fun b => array [toString b.source,toString b.x,toString b.y,toString b.width,toString b.height]) ++
  ",\"glyphRuns\":" ++ array (s.glyphRuns.toList.map runJSON) ++ ",\"links\":" ++ Rendering.Links.encode s.links ++ "}"

@[export web_render_compile]
def compile (html : String) (width height : UInt32) : String :=
  match render html width.toNat height.toNat with
  | .error message => errorJSON message
  | .ok (scene,boxes) =>
    match (WebRenderSVG.toScene scene).artifact with
    | .error message => errorJSON message
    | .ok artifact => (artifact.dropEnd 1).toString ++ ",\"webRender\":" ++ layoutJSON scene boxes ++ "}"

end WebRender
