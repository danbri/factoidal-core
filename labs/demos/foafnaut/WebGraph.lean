import FoafNaut
import WebShell
import WebRender

/-! The interactive FOAF graph as a browser page. The model is a Lean value that the
host keeps as text; each input goes through the app's own transition, and each frame
is the app's own checked SVG inside a small HTML page. -/
namespace WebGraph
open L4Factoidal
open NativeFoafNaut

private def str (j : JSON.Json) (key : String) : String :=
  match j.field? key with | some (.string value) => value | _ => ""
private def int (j : JSON.Json) (key : String) : Int :=
  match j.field? key with | some (.number value) => value.toInt?.getD 0 | _ => 0

private def pageAround (svg : String) : String :=
  "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>FOAF graph</title>" ++
    "<style>body{margin:0;background:white}svg{display:block}</style></head><body>" ++ svg ++ "</body></html>"

/-- The picture of a model as a page, with no margin so app pixels are page pixels.
This text is for view-source and export; a frame uses `skeleton` and `embedding`. -/
def page (wire : String) : Except String String := do
  let some m := Model.decode wire | throw "invalid FOAF graph model"
  -- `keepApart` holds the layout policy on each step, so a frame draws what it is given.
  let svg ← NativeSceneSVG.serialize m.scene
  return pageAround svg

/-! ### The same elements as values

`directPaints` gives, for each shape, the elements of `NativeSceneSVG.shapeElements` as values, with
the same refusals; `directScene` is the scene that the SVG text of
`NativeSceneSVG.serialize` gives. The equality is checked by differential guards
(`WebDocumentTests`) and by the host test, not proved. -/

private def px (n : Nat) : Float := Float.ofNat n
private def solid (c : NativeGraphics.RGB) : NativeSVG.Paint := .solid (NativeSVG.rgbColor c.r c.g c.b)
private def pt (p : NativeGraphics.Point) : L4Factoidal.Rendering.Point := ⟨px p.x,px p.y⟩
private def strokeOf (width : Nat) (c : NativeGraphics.RGB) (g : NativeSVG.Geometry) : NativeSVG.DirectPaint :=
  {geometry := g, fill := .none, stroke := solid c, strokeWidth := px width, lineCap := .round}

def directPaints (s : NativeGraphics.Shape) : Except String (List NativeSVG.DirectPaint) := do
  if !NativeSceneSVG.colorOK s.color then throw "SceneSVG color component exceeds 255"
  match s with
  | .circle p radius c =>
    if radius == 0 then throw "SceneSVG zero-radius circle has no faithful SVG fill"
    return [{geometry := .circle (px p.x) (px p.y) (px radius), fill := solid c}]
  | .rectangle p size c =>
    if size.x == 0 || size.y == 0 then throw "SceneSVG zero-size rectangle has no faithful SVG fill"
    return [{geometry := .rect (px p.x) (px p.y) (px size.x) (px size.y), fill := solid c}]
  | .segment a b width c =>
    if width == 0 then throw "SceneSVG zero-width stroke has no faithful SVG stroke"
    return [strokeOf width c (.line (px a.x) (px a.y) (px b.x) (px b.y))]
  | .quadratic a b c width paint =>
    if width == 0 then throw "SceneSVG zero-width stroke has no faithful SVG stroke"
    return [strokeOf width paint (.path [.path (pt a) [.quadratic (pt b) (pt c)] false])]
  | .cubic a b c d width paint =>
    if width == 0 then throw "SceneSVG zero-width stroke has no faithful SVG stroke"
    return [strokeOf width paint (.path [.path (pt a) [.cubic (pt b) (pt c) (pt d)] false])]
  | .glyph p size bits paint =>
    if (NativeSceneSVG.rows bits).any (· > 31) then throw "SceneSVG glyph rows must contain five bits"
    if size == 0 then return []
    let mut cells : Array L4Factoidal.Rendering.Contour := #[]
    for (bits,row) in (NativeSceneSVG.rows bits).zipIdx do
      for col in List.range 5 do
        if (bits >>> (4-col)) &&& 1 == 1 then
          let x := px (p.x+col*size)
          let y := px (p.y+row*size)
          let s := px size
          cells := cells.push (.path ⟨x,y⟩ [.line ⟨x+s,y⟩,.line ⟨x+s,y+s⟩,.line ⟨x+s+(-s),y+s⟩] true)
    if cells.isEmpty then return []
    return [{geometry := .path cells.toList, fill := solid paint}]

/-- The scene of the SVG text of `serialize s` in an output of `width` by `height`. -/
def directScene (s : NativeGraphics.Scene) (width height : Nat) (inherited : NativeSVG.Style := {}) :
    Except String NativeSVG.Scene := do
  if s.width == 0 || s.height == 0 then throw "SceneSVG viewport must be positive"
  if !NativeSceneSVG.colorOK s.background then throw "SceneSVG background component exceeds 255"
  let elements ← s.shapes.mapM directPaints
  let background : NativeSVG.DirectPaint :=
    {geometry := .rect 0 0 (px s.width) (px s.height), fill := solid s.background}
  NativeSVG.directScene width height s.width s.height inherited (background :: elements.flatten)


/-- The page of a model with an empty `svg` element. The HTML before and around the
`svg` is the same as in `page`, so the layout, the boxes and the node numbers are the
same; `embedding` gives the picture from the model, with no SVG text. -/
def skeleton (m : Model) : String := pageAround (NativeSceneSVG.openTag m.scene ++ "</svg>")

/-- The SVG embedding of the graph page, from the model. It is `WebRender.embedding`
with `directScene` in place of the SVG parse. -/
def embedding (m : Model) : Rendering.Layout.Embedding := fun id style width height => do
  if Float.ofNat width.toUInt32.toNat != width || Float.ofNat height.toUInt32.toNat != height then
    throw "unsupported fractional embedded SVG viewport"
  let inherited : NativeSVG.Style := {currentColor := WebRenderSVG.toColor style.color, visible := style.visible}
  let scene ← directScene m.scene width.toUInt32.toNat height.toUInt32.toNat inherited
  return WebRender.placeSVG scene id style width height

/-- A node may not cover another. The app's layout policy decides what covers: a step
that breaks it keeps the last legal positions, so a dragged node stops at its neighbour.
A layout that already breaks the policy, as after a reveal, may still move. -/
def keepApart (before after : Model) : Model :=
  let legal := fun (m : Model) => L4Factoidal.UI.LayoutPolicy.certify m.policy m.footprints
  if legal after || !legal before then after else {after with positions := before.positions}

private def chrome (request : JSON.Json) : Int :=
  let shell := WebShell.Shell.ofJson ((request.field? "shell").getD .null)
  Int.ofNat (WebShell.height shell (int request "width").toNat)

/-- Sizes and pointer positions arrive in window coordinates; the app starts below
the chrome. Kind 1 is a resize, 2 to 4 are pointer events. -/
private def appY (request : JSON.Json) (kind : Nat) (b : Int) : Int :=
  if kind >= 1 && kind <= 4 then b - chrome request else b

/-- A press at window point (`x`,`y`) acts on a person: a node, or its reveal or hide
control. The pointer is then the pointing hand (issue 1268). -/
def acts (request : JSON.Json) (x y : Int) : Bool :=
  match Model.decode (str request "model") with
  | none => false
  | some m => match (m.pick x (appY request 2 y)).map (fun (part : PaintedPart) => part.target) with
    | some (.person _ _) => true
    | _ => false

/-- `graphStart`, `graphEvent` and `graphPage`. A frame says what the host must do. -/
def op (name : String) (request : JSON.Json) : Except String (Option String) := do
  if name == "graphStart" then
    let width := (int request "width").toNat
    let height := (int request "height" - chrome request).toNat
    return some (initialResponse (str request "rdf") width.toUInt32 height.toUInt32)
  if name == "graphEvent" then
    let kind := (int request "kind").toNat
    let some m := Model.decode (str request "model") | throw "invalid FOAF graph model"
    let result := transitionModel m kind (int request "a") (appY request kind (int request "b"))
    let model := keepApart m result.model
    return some (response model result.commands false result.clipboardWrite result.clipboardRead)
  if name == "graphPage" then
    return some (JSON.Json.object [("source",.string (← page (str request "model")))]).toString
  return none

end WebGraph
