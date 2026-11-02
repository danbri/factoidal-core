import WebRenderSVG
import Font
import L4Factoidal.Rendering.Layout

/-! HTML source → existing Lean DOM → computed CSS → layout → common scene.
The bitmap font is an explicit temporary profile, not font-backed shaping. -/
namespace WebRender
open L4Factoidal

private def quote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n" |>.replace "\r" "\\r" |>.replace "\t" "\\t") ++ "\""
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
      let attrs := n.attrs.toList.map fun a =>
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
