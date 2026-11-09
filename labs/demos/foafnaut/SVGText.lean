import SVG
import L4Factoidal.Rendering.SfntProfile
import Std.Data.HashMap

/-! # SVG text: shared text state, SFNT glyphs and `textPath`

   SVG text lowers to `path` elements, which the strict reader in `SVG.lean` draws.
   Two kinds of font can give the glyphs:

   * an SVG font, whose glyphs are path data (SVG Tiny 1.2 §11). `SVGForgiving`
     lowers text with it;
   * the SFNT fonts that the engine holds for HTML text. `lowerSfnt` here shapes each
     run with the Lean shaper and the same fallback list as HTML text
     (`SfntProfile.wordIn`).

   Both read the text with the same code: `TextState`, `textRuns` and `spaceRuns`.

   `lowerTree` lowers each SVG `text` element of an HTML document in place, so the
   source paths of all other elements stay the same, and it takes the text properties
   off the other SVG elements, which the strict reader does not read.

   `textPath` (SVG 2 §11.8; `startOffset` as in SVG 1.1 §10.13.2) puts each glyph at
   the point of the path at the middle of its advance, turned to the tangent there.
   The path is flattened by `NativeSVGCurves.flatten`; `vertices` gives each point its
   distance along the path, and `placeAt` finds the point at a distance.

   Not done: bidirectional reordering (a right-to-left run shows as the HTML path shows
   it: one glyph for each character, in reverse order), vertical text (drawn
   horizontally, with a log entry), `textLength` and `lengthAdjust`, `method="stretch"`
   (drawn as `align`, with a log entry), `textPath` to a basic shape, and CSS rules from
   style sheets for font properties (presentation attributes and `style` attributes
   are read). -/
namespace NativeSVGText

open L4Factoidal.XML

def svgURI := "http://www.w3.org/2000/svg"
def xmlURI := "http://www.w3.org/XML/1998/namespace"
/-- XML nesting limit of the text passes; the strict reader stops at 32 groups. -/
def maxDepth : Nat := 64

def plainAttr (attrs : List NamespaceAttribute) (key : String) : Option String :=
  (attrs.find? (fun a => a.name.namespace_.isNone && a.name.localPart == key)).map (·.value)
def mkAttr (key value : String) : NamespaceAttribute :=
  {name:={namespace_:=none,localPart:=key},value}
def svgElement (tag : String) (attrs : List NamespaceAttribute) (children : List NamespaceNode) : NamespaceNode :=
  .element {namespace_:=some svgURI,localPart:=tag} attrs children

/-- `xml:id` is an ID (XML ID 1.0); the strict reader reads only `id`. -/
def renameId (attrs : List NamespaceAttribute) : List NamespaceAttribute :=
  attrs.map fun a =>
    if a.name.namespace_ == some xmlURI && a.name.localPart == "id"
    then {a with name:={namespace_:=none,localPart:="id"}} else a

def float (source : Option String) (fallback : Float) : Float :=
  match source with
  | none => fallback
  | some s =>
    let s := s.trimAscii.toString
    let s := if s.endsWith "px" then (s.dropEnd 2).toString else s
    match (NativeSVG.number s) with | .ok value => value | .error _ => fallback

/-! ### Text state -/

/-- Attributes of a text element that the strict reader paints with. -/
def paintKeys := ["fill","stroke","fill-opacity","stroke-opacity","color","display","visibility","opacity",
  "stroke-linejoin","stroke-linecap","stroke-miterlimit"]

structure TextState where
  size : Float := 16
  anchor : String := "start"
  family : String := ""
  variant : String := "normal"
  lang : String := ""
  strokeWidth : Float := 1
  /-- `line-increment`, SVG Tiny 1.2 §10.11.4; `none` is `auto`. -/
  lineIncrement : Option Float := none
  textAlign : String := "start"
  displayAlign : String := "before"
  preserveSpace : Bool := false
  /-- `letter-spacing` and `word-spacing` in user units (CSS Text 3 §8). -/
  letterSpacing : Float := 0
  wordSpacing : Float := 0
  /-- `writing-mode` is vertical. -/
  vertical : Bool := false

/-- A value of a keyword property: only a listed keyword changes it. -/
def keyword (attrs : List NamespaceAttribute) (key : String) (allowed : List String) (old : String) : String :=
  match plainAttr attrs key with
  | some value => let value := value.trimAscii.toString; if allowed.contains value then value else old
  | none => old

def lineIncrementOf (attrs : List NamespaceAttribute) (old : Option Float) : Option Float :=
  match plainAttr attrs "line-increment" with
  | none => old
  | some value =>
    let value := value.trimAscii.toString
    if value == "inherit" then old else if value == "auto" then none else
    match NativeSVG.number value with
    | .ok n => if n >= 0 then some n else old
    | .error _ => old

def spaceOf (attrs : List NamespaceAttribute) (old : Bool) : Bool :=
  match attrs.find? (fun a => a.name.namespace_ == some xmlURI && a.name.localPart == "space") with
  | some a => a.value == "preserve"
  | none => old

/-- `letter-spacing` or `word-spacing`: `normal` is 0, `inherit` and a value that is
    not a length keep the old value. -/
def spacingOf (attrs : List NamespaceAttribute) (key : String) (old : Float) : Float :=
  match plainAttr attrs key with
  | none => old
  | some value =>
    let value := value.trimAscii.toString
    if value == "normal" then 0 else float (some value) old

def verticalOf (attrs : List NamespaceAttribute) (old : Bool) : Bool :=
  match plainAttr attrs "writing-mode" with
  | none => old
  | some value =>
    let value := value.trimAscii.toString
    if value == "inherit" then old else value.startsWith "tb" || value.startsWith "vertical"

def TextState.read (s : TextState) (attrs : List NamespaceAttribute) : TextState :=
  { size := float (plainAttr attrs "font-size") s.size,
    anchor := (plainAttr attrs "text-anchor").getD s.anchor,
    family := (plainAttr attrs "font-family").getD s.family,
    variant := keyword attrs "font-variant" ["normal","small-caps"] s.variant,
    lang := match attrs.find? (fun a => a.name.namespace_ == some xmlURI && a.name.localPart == "lang") with
      | some a => a.value
      | none => s.lang,
    strokeWidth := float (plainAttr attrs "stroke-width") s.strokeWidth,
    lineIncrement := lineIncrementOf attrs s.lineIncrement,
    textAlign := keyword attrs "text-align" ["start","center","end"] s.textAlign,
    -- §10.11.6: for SVG, `auto` is `before`.
    displayAlign := match plainAttr attrs "display-align" with
      | some value => if value.trimAscii.toString == "auto" then "before"
        else keyword attrs "display-align" ["before","center","after"] s.displayAlign
      | none => s.displayAlign,
    preserveSpace := spaceOf attrs s.preserveSpace,
    letterSpacing := spacingOf attrs "letter-spacing" s.letterSpacing,
    wordSpacing := spacingOf attrs "word-spacing" s.wordSpacing,
    vertical := verticalOf attrs s.vertical }

/-- A `textPath`: the path that it names or gives, and how text goes on it. -/
structure PathRef where
  href : Option String := none
  /-- SVG 2 `path` attribute: path data in the `textPath` itself. -/
  data : Option String := none
  startOffset : Option String := none
  side : String := "left"
  method : String := "align"
  deriving BEq, Inhabited

structure Run where
  text : String
  size : Float
  strokeWidth : Float
  paint : List NamespaceAttribute
  xs : List Float := []
  ys : List Float := []
  dx : Float := 0
  dy : Float := 0
  /-- `dx`, `dy` and `rotate` of the `tspan` that starts with this run, all values. -/
  dxs : List Float := []
  dys : List Float := []
  rotates : List Float := []
  /-- A `tbreak`: the text is empty, and the line ends here. -/
  lineBreak : Bool := false
  increment : Option Float := none
  preserveSpace : Bool := false
  anchor : String := "start"
  lang : String := ""
  family : String := ""
  letterSpacing : Float := 0
  wordSpacing : Float := 0
  vertical : Bool := false
  /-- The `textPath` that holds this run. -/
  onPath : Option PathRef := none

instance : Inhabited Run := ⟨{text := "", size := 0, strokeWidth := 0, paint := []}⟩

def paintOf (attrs : List NamespaceAttribute) : List NamespaceAttribute :=
  attrs.filter fun a => a.name.namespace_.isNone && paintKeys.contains a.name.localPart

def numberList (attrs : List NamespaceAttribute) (key : String) : List Float :=
  match plainAttr attrs key with
  | none => []
  | some s => ((s.splitOn " ").flatMap (·.splitOn ",") |>.filter (· != "")).map (fun n => float (some n) 0)

/-- Text runs in order. A later unsupported child is logged and skipped. With
    `paths`, a `textPath` gives runs on its path; without, it is logged and skipped. -/
def textRuns (area paths : Bool) : Nat → TextState → List NamespaceAttribute → NamespaceNode → List Run × List String
  | 0,_,_,_ => ([],[])
  | _,state,paint,.other raw => match raw with
    | .text t | .cdata t => ([{
        text := t, size := state.size, strokeWidth := state.strokeWidth, paint := paint,
        increment := state.lineIncrement, preserveSpace := state.preserveSpace, anchor := state.anchor, lang := state.lang,
        family := state.family, letterSpacing := state.letterSpacing, wordSpacing := state.wordSpacing,
        vertical := state.vertical}],[])
    | _ => ([],[])
  | fuel+1,state,paint,.element name attrs children =>
    if area && name.localPart == "tbreak" then
      ([{text := "", size := state.size, strokeWidth := state.strokeWidth, paint := paint, lineBreak := true, increment := lineIncrementOf attrs state.lineIncrement}],[])
    else if paths && name.localPart == "textPath" then
      let inner := state.read attrs
      -- A `textPath` in a `textPath` is not drawn (SVG 2 §11.8.1): `paths` is off inside.
      let results := children.map (textRuns area false fuel inner (paint ++ paintOf attrs))
      let ref : PathRef := {
        href := NativeSVGReferences.href attrs, data := plainAttr attrs "path",
        startOffset := plainAttr attrs "startOffset",
        side := keyword attrs "side" ["left","right"] "left",
        method := keyword attrs "method" ["align","stretch"] "align"}
      ((results.flatMap (·.1)).map ({· with onPath := some ref}),results.flatMap (·.2))
    else if name.localPart != "tspan" then ([],["element in text: " ++ name.localPart]) else
    let inner := state.read attrs
    let results := children.map (textRuns area paths fuel inner (paint ++ paintOf attrs))
    let runs := results.flatMap (·.1)
    let runs := match runs with
      | run::rest =>
        let placed : Run := { run with
          xs := numberList attrs "x"
          ys := numberList attrs "y"
          dx := (numberList attrs "dx").headD 0
          dy := (numberList attrs "dy").headD 0
          dxs := numberList attrs "dx"
          dys := numberList attrs "dy"
          rotates := numberList attrs "rotate" }
        placed::rest
      | [] => []
    (runs,results.flatMap (·.2))

/-- `xml:space="default"`: newlines go, tabs become spaces, and spaces collapse.
    Leading and trailing spaces of the whole text go in `spaceRuns`. -/
def collapse (s : String) : String :=
  let kept := s.toList.filter (fun c => c != '\n' && c != '\r')
  let spaced := kept.map (fun c => if c == '\t' then ' ' else c)
  String.ofList (spaced.foldr (fun c acc => match acc with
    | ' '::_ => if c == ' ' then acc else c::acc
    | _ => c::acc) [])

/-- `xml:space="preserve"`: newlines and tabs become spaces, and nothing goes. -/
def preserved (s : String) : String :=
  String.ofList (s.toList.map fun c => if c == '\n' || c == '\t' || c == '\r' then ' ' else c)

/-- White space of the runs of one `text` (SVG 1.1 §10.15). With the default
    `xml:space`, the whole text has no leading or trailing space. -/
def spaceRuns (raw : List Run) : List Run :=
  let raw := raw.map (fun r => {r with text:=if r.preserveSpace then preserved r.text else collapse r.text})
  let lastIndex := raw.length-1
  raw.zipIdx.map fun (r,i) =>
    let text := if i == 0 && !r.preserveSpace then r.text.trimAsciiStart.toString else r.text
    {r with text:=if i == lastIndex && !r.preserveSpace then text.trimAsciiEnd.toString else text}

/-- Tell each glyph path of a run the bounding box of the whole text, x0 y0 x1 y1. -/
def markGlyphs (box : Float × Float × Float × Float) : NamespaceNode → NamespaceNode
  | .element name attrs paths =>
    let (x0,y0,x1,y1) := box
    let mark : NamespaceAttribute := {name:={namespace_:=some NativeSVG.internalURI,localPart:=NativeSVG.textBoxAttribute},value:=s!"{x0} {y0} {x1-x0} {y1-y0}"}
    .element name attrs (paths.map fun
      | .element n a c => .element n (a ++ [mark]) c
      | node => node)
  | node => node

def rightToLeftLanguage (lang : String) : Bool :=
  ["ar","he","fa","ur","yi"].contains ((lang.toLower.splitOn "-").headD "")

/-! ### Text properties and the `style` attribute -/

/-- Properties that only text reads. The strict reader refuses each one on any
    element, so a container in an HTML document loses them once they are read. -/
def textProperties : List String :=
  ["font","font-family","font-size","font-style","font-weight","font-variant","font-stretch","font-size-adjust",
   "font-kerning","font-feature-settings","text-anchor","letter-spacing","word-spacing","writing-mode","direction",
   "unicode-bidi","dominant-baseline","alignment-baseline","baseline-shift","text-decoration","text-rendering",
   "glyph-orientation-vertical","glyph-orientation-horizontal","kerning","line-increment","text-align",
   "display-align","text-transform","white-space","lengthAdjust","textLength"]

/-- The declarations of a `style` attribute, as (property, value). -/
def styleDeclarations (source : String) : List (String × String) :=
  (source.splitOn ";").filterMap fun part =>
    match part.splitOn ":" with
    | key::rest@(_::_) =>
      let key := key.trimAscii.toString.toLower
      let value := (":".intercalate rest).trimAscii.toString
      if key.isEmpty then none else some (key,value)
    | _ => none

/-- The declarations of `style` as attributes, in front of the others so that they
    win. Only text properties and paint keys are taken; `style` itself goes. -/
def expandStyle (attrs : List NamespaceAttribute) : List NamespaceAttribute :=
  match plainAttr attrs "style" with
  | none => attrs
  | some source =>
    let wanted := (styleDeclarations source).filter fun (k,_) => textProperties.contains k || paintKeys.contains k ||
      ["stroke-width","fill-rule","stroke-dasharray","stroke-dashoffset"].contains k
    let values := wanted.map fun (k,v) =>
      mkAttr k ((if v.endsWith "!important" then (v.dropEnd 10).toString else v).trimAscii.toString)
    values ++ attrs.filter (fun a => !(a.name.namespace_.isNone && a.name.localPart == "style"))

/-- `expandStyle` on an element and all its descendants. -/
def expandStyleTree : Nat → NamespaceNode → NamespaceNode
  | 0,node => node
  | _,node@(.other _) => node
  | fuel+1,.element name attrs children => .element name (expandStyle attrs) (children.map (expandStyleTree fuel))

/-- The attributes of a container less its text properties, also in `style`. -/
def stripTextProperties (attrs : List NamespaceAttribute) : List NamespaceAttribute :=
  attrs.filterMap fun a =>
    if a.name.namespace_.isSome then some a
    else if textProperties.contains a.name.localPart then none
    else if a.name.localPart == "style" then
      let kept := (styleDeclarations a.value).filter (fun (k,_) => !textProperties.contains k)
      if kept.isEmpty then none else some {a with value := ";".intercalate (kept.map fun (k,v) => k ++ ":" ++ v)}
    else some a

/-! ### Distance along a flattened path

   `vertices` gives each point of a polyline its distance from the start, and
   `placeAt` finds the point at a distance and the direction of the path there.

   Proved: `vertices` keeps the points in order (`vertices_points`), and a point that
   `placeAt` gives is on the line through two neighbouring vertices
   (`placeAt_on_polyline`). Not proved, because Lean has no order lemmas for `Float`:
   that the distances do not decrease (each step adds `max 0` of a square root), and
   that the parameter of the point is between 0 and 1. `#guard`s in `SVGTextTests`
   check both on examples. -/

abbrev Point := L4Factoidal.Rendering.Point

/-- A point of a flattened path, and its distance along the path from the start. -/
structure Vertex where
  point : Point
  length : Float

instance : Inhabited Vertex := ⟨⟨⟨0,0⟩,0⟩⟩

def distance (a b : Point) : Float :=
  let dx := b.x-a.x
  let dy := b.y-a.y
  let d := (dx*dx+dy*dy).sqrt
  if d > 0 then d else 0

/-- Distances of the points, each with a flag that it starts a subpath. A move to a
    new subpath adds no distance (SVG 2 §11.8.2). Tail recursive. -/
def verticesLoop : List (Point × Bool) → Option Point → Float → List Vertex → List Vertex
  | [],_,_,acc => acc.reverse
  | (p,move)::rest,previous,total,acc =>
    let step := match previous,move with
      | some q,false => distance q p
      | _,_ => 0
    verticesLoop rest (some p) (total+step) (⟨p,total+step⟩::acc)

def vertices (points : List (Point × Bool)) : List Vertex := verticesLoop points none 0 []

theorem verticesLoop_points (points : List (Point × Bool)) :
    ∀ (previous : Option Point) (total : Float) (acc : List Vertex),
      (verticesLoop points previous total acc).map (·.point) = acc.reverse.map (·.point) ++ points.map (·.1) := by
  induction points with
  | nil => intro previous total acc; simp [verticesLoop]
  | cons head rest ih =>
    intro previous total acc
    obtain ⟨p,move⟩ := head
    simp only [verticesLoop]
    rw [ih]
    simp

theorem vertices_points (points : List (Point × Bool)) :
    (vertices points).map (·.point) = points.map (·.1) := by
  simp [vertices,verticesLoop_points]

theorem vertices_length (points : List (Point × Bool)) : (vertices points).length = points.length := by
  have h := congrArg List.length (vertices_points points)
  simpa using h

/-- The first pair of neighbouring vertices whose segment has length and reaches `s`.
    Tail recursive. -/
def segmentAt : List Vertex → Float → Option (Vertex × Vertex)
  | a::tail@(b::_),s => if s ≤ b.length && a.length < b.length then some (a,b) else segmentAt tail s
  | _,_ => none

theorem segmentAt_neighbours (vs : List Vertex) (s : Float) (a b : Vertex)
    (h : segmentAt vs s = some (a,b)) : ∃ before after, vs = before ++ a :: b :: after := by
  induction vs with
  | nil => simp [segmentAt] at h
  | cons head tail ih =>
    cases tail with
    | nil => simp [segmentAt] at h
    | cons b' rest =>
      simp only [segmentAt] at h
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl,rfl⟩ := h
        exact ⟨[],rest,rfl⟩
      · obtain ⟨before,after,eq⟩ := ih h
        exact ⟨head::before,after,by simp [eq]⟩

def lerp (a b : Point) (t : Float) : Point := ⟨a.x+(b.x-a.x)*t,a.y+(b.y-a.y)*t⟩

/-- A point on a path and the direction of the path there, in radians. -/
structure Place where
  point : Point
  angle : Float

/-- Length of the path whose vertices are `vs`. -/
def totalLength (vs : List Vertex) : Float := (vs.getLast?.map (·.length)).getD 0

/-- The point at distance `s` along the path, and its tangent direction. `none` when
    `s` is before the start or after the end: such a glyph is not drawn (SVG 2 §11.8.3). -/
def placeAt (vs : List Vertex) (s : Float) : Option Place :=
  if s < 0 || s > totalLength vs then none else
  match segmentAt vs s with
  | some (a,b) =>
    let span := b.length-a.length
    let t := if span > 0 then (s-a.length)/span else 0
    some ⟨lerp a.point b.point t,Float.atan2 (b.point.y-a.point.y) (b.point.x-a.point.x)⟩
  | none => none

theorem placeAt_on_polyline (vs : List Vertex) (s : Float) (place : Place) (h : placeAt vs s = some place) :
    ∃ before after a b t, vs = before ++ a :: b :: after ∧ place.point = lerp a.point b.point t := by
  unfold placeAt at h
  split at h
  · exact absurd h (by simp)
  · split at h
    next a b found =>
      obtain ⟨before,after,eq⟩ := segmentAt_neighbours vs s a b found
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨before,after,a,b,_,eq,rfl⟩
    next => exact absurd h (by simp)

#print axioms vertices_points
#print axioms vertices_length
#print axioms placeAt_on_polyline

/-- `startOffset`: a length, or a percentage of the path length (SVG 1.1 §10.13.2). -/
def startOffsetOf (source : Option String) (total : Float) : Float :=
  match source with
  | none => 0
  | some s =>
    let s := s.trimAscii.toString
    if s.endsWith "%" then float (some (s.dropEnd 1).toString) 0/100*total else float (some s) 0

/-- The vertices of the path of a `textPath`, in the user space of the text: the
    path's own `transform` applies (SVG 1.1 §10.13.1). `side="right"` reverses the
    path (SVG 2 §11.8.1). -/
def pathVertices (lookup : String → Option NamespaceNode) (ref : PathRef) : Except String (List Vertex) := do
  let (data,transform) ← match ref.data,ref.href with
    | some d,_ => pure (d,"")
    | none,some h =>
      let h := h.trimAscii.toString
      if !h.startsWith "#" then throw s!"textPath: reference to another document is not read: {h}"
      match lookup (h.drop 1).toString with
      | some (.element n a _) =>
        if n.localPart == "path" then pure ((plainAttr a "d").getD "",(plainAttr a "transform").getD "")
        else throw s!"textPath: {h} is a {n.localPart}; only a path is read"
      | _ => throw s!"textPath: no element {h}"
    | none,none => throw "textPath: no path"
  let contours ← NativeSVGPath.parse NativeSVG.number data
  let screen ← NativeSVG.transformOf transform
  let lines ← NativeSVGCurves.flatten screen contours 0.05
  let apply := fun (p : Point) =>
    let (x,y) := L4Factoidal.Math.Affine2.applyPoint L4Factoidal.Math.AffineScalarOps.float screen p.x p.y
    (⟨x,y⟩ : Point)
  let parts := lines.filterMap fun c => match c.points with
    | [] => none
    | first::_ => some ((if c.closed then c.points ++ [first] else c.points).map apply)
  let parts := if ref.side == "right" then parts.reverse.map List.reverse else parts
  return vertices (parts.flatMap fun ps => ps.zipIdx.map fun (p,i) => (p,i == 0))

/-! ### Text drawn with SFNT fonts -/

abbrev Font := L4Factoidal.Rendering.SfntProfile.Font

/-- The held fonts with the first family of `family` that one of them has in front
    (CSS Fonts 4 §5); otherwise the list as held, the primary font first. -/
def familyOrder (fonts : Array Font) (family : String) : Array Font :=
  let names := (family.splitOn ",").map fun n => ((n.trimAscii.toString.replace "'" "").replace "\"" "").toLower
  match names.findSome? (fun name => fonts.findIdx? (·.family.toLower == name)) with
  | some i => match fonts[i]? with
    | some f => #[f] ++ fonts.eraseIdxIfInBounds i
    | none => fonts
  | none => fonts

/-- One glyph of a text, shaped, before it is placed. -/
structure GlyphCell where
  geometry : List L4Factoidal.Rendering.Geometry
  /-- Offset of the outline from the pen, in font units, with the baseline at y = 0. -/
  offsetX : Float
  offsetY : Float
  advance : Float
  /-- User units for each font unit. -/
  scale : Float
  ascent : Float
  descent : Float
  /-- Index in the text of the first character of its cluster. -/
  char : Nat
  run : Nat
  /-- It is the first glyph of its cluster: the per-character values go to it. -/
  first : Bool
  deriving Inhabited

/-- Where a glyph is drawn: its origin, its turn in degrees, and if it is drawn. -/
structure Spot where
  x : Float := 0
  y : Float := 0
  rotate : Float := 0
  shown : Bool := true
  deriving Inhabited

/-- A number of path data, to 1/100 of a user unit, as `FloatFormat.format` writes it
(`100`, `1.5`; exponent form for large values). Below 10^7 the digits come
from the integer `round (v*100)` with no general formatter (a glyph outline writes many
numbers per layout); the `#guard`s below check it against `FloatFormat.format`. -/
def fmt (v : Float) : String :=
  if !v.isFinite then "0" else
  let r := (v*100).round
  if r.abs >= 1e9 || r == 0 then L4Factoidal.Rendering.FloatFormat.format (r/100) else
  let n := r.abs.toUInt64.toNat
  let frac := n % 100
  let tail := if frac == 0 then "" else if frac % 10 == 0 then "." ++ toString (frac/10)
    else if frac < 10 then ".0" ++ toString frac else "." ++ toString frac
  (if r < 0 then "-" else "") ++ toString (n/100) ++ tail

/-- The two-decimal digits that `fmt` writes, as `FloatFormat.format` writes them. -/
def fmtReference (v : Float) : String :=
  if !v.isFinite then "0" else L4Factoidal.Rendering.FloatFormat.format ((v*100).round/100)

#guard [0, -0.001, 0.004, 0.005, 0.07, 0.1, 0.2, 0.3, 0.25, 1.5, -1.5, 12.345, -12.355, 99.995, 100, -100,
  3.14159, -2.71828, 1234.5, 123456.789, 1e8+0.25, -1e9-0.75, 1e12+0.01, 9.99e12, 2e13, 1e15, -0.5, 7.1,
  0.0001, 1/0, 0/0].all (fun v => fmt v == fmtReference v)

/-- Path data of a glyph in user units, about its origin. -/
def glyphData (cell : GlyphCell) : String := Id.run do
  let k := cell.scale
  let pt := fun (q : Point) => fmt (k*(q.x+cell.offsetX)) ++ " " ++ fmt (k*(q.y+cell.offsetY))
  let mut out := ""
  for g in cell.geometry do
    if let .path contours := g then
      for c in contours do
        if let .path start segments closed := c then
          out := out ++ "M" ++ pt start
          for seg in segments do
            out := out ++ (match seg with
              | .line p => "L" ++ pt p
              | .quadratic c p => "Q" ++ pt c ++ " " ++ pt p
              | .cubic a b p => "C" ++ pt a ++ " " ++ pt b ++ " " ++ pt p
              | .arc rx ry r large sweep p =>
                "A" ++ fmt (k*rx) ++ " " ++ fmt (k*ry) ++ " " ++ fmt r ++ " " ++ (if large then "1" else "0") ++ " " ++
                  (if sweep then "1" else "0") ++ " " ++ pt p)
          if closed then out := out ++ "Z"
  return out

/-- Words that SVG text has shaped, by the fonts' SHA-256 values, the text and the pixel
size: a layout at another width, or the same labels again, does not shape them again.
Emptied above `keptWordsLimit` entries. -/
initialize keptWordsRef : IO.Ref (Std.HashMap (List String × String × Nat) L4Factoidal.Rendering.FontProvider.Word) ← IO.mkRef {}
def keptWordsLimit : Nat := 8192

set_option compiler.extract_closed false in
private unsafe def wordKeptImpl (fonts : Array Font) (text : String) (px : Nat) :
    Except String L4Factoidal.Rendering.FontProvider.Word :=
  unsafeBaseIO do
    let key := (fonts.toList.map (·.sha256),text,px)
    if let some word := (← keptWordsRef.get).get? key then return .ok word
    let made := L4Factoidal.Rendering.SfntProfile.wordIn fonts text px
    if let .ok word := made then
      keptWordsRef.modify fun m => (if m.size > keptWordsLimit then {} else m).insert key word
    return made

/-- `SfntProfile.wordIn`; the engine gives a word shaped before with the same fonts again. -/
@[implemented_by wordKeptImpl]
def wordKept (fonts : Array Font) (text : String) (px : Nat) : Except String L4Factoidal.Rendering.FontProvider.Word :=
  L4Factoidal.Rendering.SfntProfile.wordIn fonts text px

theorem wordKept_eq (fonts : Array Font) (text : String) (px : Nat) :
    wordKept fonts text px = L4Factoidal.Rendering.SfntProfile.wordIn fonts text px := rfl

/-- Shape each run with the held fonts. A run that does not shape is logged and not
    drawn; the rest of the text is. -/
def shapeRuns (fonts : Array Font) (runs : Array Run) : Array GlyphCell × Array Nat × List String := Id.run do
  let mut cells : Array GlyphCell := #[]
  let mut starts : Array Nat := #[]
  let mut log : List String := []
  let mut start := 0
  for i in [:runs.size] do
    let run : Run := runs[i]!
    starts := starts.push start
    let n := run.text.length
    if run.size > 0 && n > 0 then
      let px := min 512 (max 1 run.size.round.toUInt32.toNat)
      -- SVG text draws outlines: colour glyphs (COLR) have none, so their fonts are left
      -- out and an emoji comes from an outline font, Noto Emoji when held (issue 1276).
      match wordKept ((familyOrder fonts run.family).filter (·.colour.isNone)) run.text px with
      | .error e => log := log ++ [s!"text run not shaped: {e}"]
      | .ok word =>
        let scale := run.size/word.unitsPerEm
        let mut pen : Float := 0
        let mut last : Option Nat := none
        for g in word.glyphs do
          cells := cells.push {
            geometry := g.geometry, offsetX := g.x-pen, offsetY := g.y-word.ascent,
            advance := g.advance, scale, ascent := word.ascent, descent := word.descent,
            char := start+g.clusterStart, run := i, first := last != some g.clusterStart}
          last := some g.clusterStart
          pen := pen+g.advance
    start := start+n
  return (cells,starts,log)

/-- Move the glyphs of a text chunk by its anchor (SVG 1.1 §10.9.1). -/
def anchorChunk (spots : Array Spot) (chunk : Array Nat) (width : Float) (anchor : String) : Array Spot × Float :=
  let shift := match anchor with
    | "middle" => -width/2
    | "end" => -width
    | _ => 0
  (chunk.foldl (fun s k => s.modify k fun p => {p with x := p.x+shift}) spots,shift)

/-- The value of a per-character list for character `c`, which is character `idx`
    of its run: the `tspan` list first, then the `text` list. -/
def listAt (outer inner : List Float) (c idx : Nat) : Option Float :=
  (inner[idx]?).orElse fun _ => outer[c]?

/-- Lower one `text` element to a group of glyph paths, drawn with `fonts`. -/
def lowerSfnt (fonts : Array Font) (lookup : String → Option NamespaceNode) (state : TextState)
    (attrs : List NamespaceAttribute) (children : List NamespaceNode) : NamespaceNode × List String := Id.run do
  let attrs := expandStyle (renameId attrs)
  let children := children.map (expandStyleTree maxDepth)
  let state := state.read attrs
  let results := children.map (textRuns false true maxDepth state [])
  let mut log := results.flatMap (·.2)
  let runs := (spaceRuns (results.flatMap (·.1))).toArray
  if runs.any (·.vertical) then log := log ++ ["text: vertical writing-mode drawn horizontally"]
  if runs.any (fun r => (r.onPath.map (·.method)) == some "stretch") then
    log := log ++ ["textPath: method stretch drawn as align"]
  let chars := (runs.toList.flatMap (·.text.toList)).toArray
  let (cells,starts,shapeLog) := shapeRuns fonts runs
  log := log ++ shapeLog
  let xs := numberList attrs "x"
  let ys := numberList attrs "y"
  let dxs := numberList attrs "dx"
  let dys := numberList attrs "dy"
  let rotations := numberList attrs "rotate"
  -- Per-character values of each glyph: x, y, dx, dy, rotate. A rotate list holds its
  -- last value for the characters after it.
  let values : Array (Option Float × Option Float × Float × Float × Option Float) := cells.map fun cell =>
    let run : Run := runs[cell.run]!
    let idx := cell.char-starts[cell.run]!
    if !cell.first then (none,none,0,0,none) else
    (listAt xs run.xs cell.char idx,listAt ys run.ys cell.char idx,
     (listAt dxs run.dxs cell.char idx).getD 0,(listAt dys run.dys cell.char idx).getD 0,
     (listAt rotations run.rotates cell.char idx).orElse fun _ => run.rotates.getLast?.orElse fun _ => rotations.getLast?)
  let isSpace := fun (c : Nat) => chars[c]? == some ' '
  let mut spots : Array Spot := Array.replicate cells.size {}
  -- Text chunks (SVG 1.1 §10.4): an absolute position starts one.
  let mut x : Float := 0
  let mut y : Float := 0
  let mut chunk : Array Nat := #[]
  let mut chunkX : Float := 0
  let mut anchor := "start"
  for k in [:cells.size] do
    let cell := cells[k]!
    let run : Run := runs[cell.run]!
    let (ax,ay,dx,dy,r) := values[k]!
    if run.onPath.isSome then
      let (moved,shift) := anchorChunk spots chunk (x-chunkX) anchor
      spots := moved
      x := x+shift
      chunk := #[]
      continue
    if ax.isSome || ay.isSome then
      let (moved,shift) := anchorChunk spots chunk (x-chunkX) anchor
      spots := moved
      x := x+shift
      chunk := #[]
    if let some v := ax then x := v
    if let some v := ay then y := v
    if chunk.isEmpty then
      chunkX := x
      anchor := run.anchor
    else if cell.first then x := x+run.letterSpacing
    x := x+dx
    y := y+dy
    spots := spots.set! k {x,y,rotate := r.getD 0}
    chunk := chunk.push k
    x := x+cell.scale*cell.advance
    if cell.first && isSpace cell.char then x := x+run.wordSpacing
  let (moved,_) := anchorChunk spots chunk (x-chunkX) anchor
  spots := moved
  -- Runs on a path: each `textPath` is one chunk along its path.
  let mut k := 0
  for _ in [:cells.size] do
    if k >= cells.size then break
    let onPath := runs[cells[k]!.run]!.onPath
    if onPath.isNone then
      k := k+1
      continue
    let ref := onPath.getD default
    let mut stop := k
    for j in [k:cells.size] do
      if runs[cells[j]!.run]!.onPath == some ref then stop := j+1 else break
    match pathVertices lookup ref with
    | .error e =>
      log := log ++ [e]
      for j in [k:stop] do spots := spots.modify j ({· with shown := false})
    | .ok vs =>
      let total := totalLength vs
      let mut along : Float := 0
      let mut lift : Float := 0
      let mut placed : Array (Float × Float) := #[]
      for j in [k:stop] do
        let cell := cells[j]!
        let run : Run := runs[cell.run]!
        let (_,_,dx,dy,_) := values[j]!
        if j > k && cell.first then along := along+run.letterSpacing
        along := along+dx
        lift := lift+dy
        placed := placed.push (along,lift)
        along := along+cell.scale*cell.advance
        if cell.first && isSpace cell.char then along := along+run.wordSpacing
      let first : Run := runs[cells[k]!.run]!
      let shift := match first.anchor with
        | "middle" => -along/2
        | "end" => -along
        | _ => 0
      let offset := startOffsetOf ref.startOffset total+shift
      for j in [k:stop] do
        let cell := cells[j]!
        let (start,up) := placed[j-k]!
        let (_,_,_,_,r) := values[j]!
        let half := cell.scale*cell.advance/2
        match placeAt vs (offset+start+half) with
        | none => spots := spots.modify j ({· with shown := false})
        | some place =>
          let c := place.angle.cos
          let s := place.angle.sin
          spots := spots.set! j {
            x := place.point.x-half*c-up*s, y := place.point.y-half*s+up*c,
            rotate := place.angle*180/3.141592653589793+r.getD 0}
    k := stop
  -- Paths: one group for each run, as the SVG font path does.
  let opacity := (plainAttr attrs "opacity").toList.map (mkAttr "opacity")
  let groupPaint := fun (a : List NamespaceAttribute) => a.filter (·.name.localPart != "opacity")
  let mut groups : Array NamespaceNode := #[]
  let mut box : Option (Float × Float × Float × Float) := none
  let mut cursor := 0
  for ri in [:runs.size] do
    let run : Run := runs[ri]!
    let mut paths : Array NamespaceNode := #[]
    for i in [cursor:cells.size] do
      let cell := cells[i]!
      if cell.run != ri then break
      cursor := i+1
      let spot := spots[i]!
      if !spot.shown then continue
      let data := glyphData cell
      if !data.isEmpty then
        let turn := if spot.rotate == 0 then "" else " rotate(" ++ fmt spot.rotate ++ ")"
        paths := paths.push (svgElement "path" ([mkAttr "d" data,
          mkAttr "transform" ("translate(" ++ fmt spot.x ++ "," ++ fmt spot.y ++ ")" ++ turn)] ++ opacity) [])
      let top := spot.y-cell.ascent*cell.scale
      let bottom := spot.y+cell.descent*cell.scale
      let right := spot.x+cell.advance*cell.scale
      box := some (match box with
        | none => (spot.x,top,right,bottom)
        | some (x0,y0,x1,y1) => (min x0 spot.x,min y0 top,max x1 right,max y1 bottom))
    groups := groups.push (svgElement "g" (groupPaint run.paint) paths.toList)
  let outer := groupPaint (paintOf attrs) ++ (attrs.filter (fun a => a.name.namespace_.isNone &&
    ["transform","stroke-width","fill-rule","stroke-dasharray","stroke-dashoffset"].contains a.name.localPart))
  let ids := attrs.filter (fun a => a.name.namespace_.isNone && a.name.localPart == "id")
  let marked := match box with
    | none => groups.toList
    | some box => groups.toList.map (markGlyphs box)
  return (svgElement "g" (ids ++ outer) marked,log)

/-! ### Text in an HTML document -/

/-- Most nodes `idIndex` visits; each one is at least one character of input. -/
def maxNodes : Nat := NativeSVG.maxInputChars

/-- The first element with each `id`, in document order. A loop over a work list. -/
def idIndex (root : NamespaceNode) : Std.HashMap String NamespaceNode := Id.run do
  let mut pending := [root]
  let mut found : Std.HashMap String NamespaceNode := {}
  for _ in [:maxNodes] do
    match pending with
    | [] => break
    | node::rest =>
      pending := rest
      if let .element _ attrs children := node then
        if let some id := plainAttr attrs "id" then
          if !found.contains id then found := found.insert id node
        pending := children ++ pending
  return found

/-- Lower each SVG `text` in place with `fonts`. Other SVG elements keep their place
    and lose their text properties, after these are read into the state. With no
    font held, a `text` draws nothing and is logged. The depth is that of the tree,
    at most `fuel`. -/
def lowerTree (fonts : Array Font) (lookup : String → Option NamespaceNode) : Nat → TextState → NamespaceNode →
    NamespaceNode × List String
  | 0,_,node => (node,[])
  | _,_,node@(.other _) => (node,[])
  | fuel+1,state,.element name attrs children =>
    if name.namespace_ == some svgURI && name.localPart == "text" then
      if fonts.isEmpty then
        (svgElement "g" (attrs.filter (fun a => a.name.namespace_.isNone && a.name.localPart == "id")) [],
          ["text: no font is held"])
      else lowerSfnt fonts lookup state attrs children
    else
      let svg := name.namespace_ == some svgURI
      let inner := if svg then state.read (expandStyle attrs) else state
      let results := children.map (lowerTree fonts lookup fuel inner)
      (.element name (if svg then stripTextProperties attrs else attrs) (results.map (·.1)),results.flatMap (·.2))

/-- Depth limit of `lowerDocument`: deeper content stays as it is. -/
def maxTreeDepth : Nat := 256

/-- All SVG text of a document lowered with `fonts`, and the log. -/
def lowerDocument (fonts : Array Font) (root : NamespaceNode) : NamespaceNode × List String :=
  let index := idIndex root
  lowerTree fonts index.get? maxTreeDepth {} root

end NativeSVGText
