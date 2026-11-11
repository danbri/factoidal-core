import WebRender
import WebHit
import L4Factoidal.Rendering.Smil
import L4Factoidal.JSON.Parser

/-! # Paint-only changes: SVG `transform`, and SVG declarative animation

A change of the `transform` attribute of an SVG element moves what is drawn and
nothing else: no box, line or glyph of the page changes (SVG 2 §8.5: a transform
establishes a new user space; it does not take part in CSS layout). So such a change
must not lay the page out again, nor shape text again.

How (issue 1268, `FrameCost.paint_never_layouts`):

* `WebDocument` takes the `setAttribute` commands of `transform` out of the layout key
  (`slotKey`): the key keeps that the attribute was set, not its value. The layout is
  made with those attributes empty (the identity), and keeps a `Plan` of the elements
  whose transform a frame sets.
* A frame takes the kept layout, and `paint` puts each element's transform on its node
  of the scene: the group of a `g` or a `text` (by `id`; an element with none gets an
  id that no page can write, as it is only in the layout's copy of the arena), or the
  primitive of a shape or an image (by its source path). Only the band is drawn again.
* SVG animation (`animateTransform`, and `animate` of `opacity` on a shape), on the
  page clock (`animationTime`, ms) with the clicks of the page (`animationClicks`):
  `Smil` gives each animation's value at the time, and `paint` puts it on the scene
  in the same way. No script runs.

An element is painted this way when it is a `g`, `text` or a shape or `image`, its
SVG ancestors are `svg`, `g` or `a`, and neither it nor an ancestor is named by an
`href` or `url(#...)` of the document (`use`, `textPath`, clip paths and markers draw
another copy of what they name). Other script changes of `transform` are laid out as
before (`Plan.unpaintable`); an animation of another element or attribute is not run,
and the log says so: the element shows its base value. -/
namespace WebPaint
open L4Factoidal L4Factoidal.Rendering

def groupTags : List String := ["g","text"]
def shapeTags : List String := ["path","rect","circle","ellipse","line","polyline","polygon","image"]
/-- SVG animation elements (SVG 1.1 §19.2). They draw nothing; the layout's arena has a
comment in their place, so that the paths of the other elements stay. -/
def animationTags : List String := ["animate","animateTransform","set","animateMotion","animateColor"]

structure Target where
  node : Nat
  /-- The `id` of the scene group of a `g` or `text`; `none` for a shape or image. -/
  group : Option String
  /-- The source path of the element (`Primitive.element`). -/
  path : List Nat
  /-- The `transform` attribute of the element in the page as parsed. -/
  base : String
  baseOpacity : Float := 1
  deriving Inhabited

inductive Kind where
  | transform (type : String)
  | opacity
  deriving Inhabited, BEq

structure Animation where
  target : Nat
  kind : Kind
  begins : List Smil.Begin
  dur : Nat
  active : Option Nat
  freeze : Bool
  values : Array (Array Float)
  keyTimes : Option (Array Float)
  discrete : Bool
  additive : Bool
  deriving Inhabited

structure Plan where
  targets : Std.TreeMap Nat Target := {}
  animations : Array Animation := #[]
  /-- Elements by `id`, for `id.click` begins. -/
  ids : Std.TreeMap String Nat := {}
  /-- Script `transform` slots that this layout can not paint. -/
  unpaintable : List Nat := []
  log : List String := []
  deriving Inhabited

def Plan.empty (p : Plan) : Bool := p.targets.isEmpty

/-- The attributes a script sets that a frame paints with no layout. -/
def slotAttributes : List String := ["transform","opacity"]

/-- The values of a script's slots, by node: `transform` and `opacity`. -/
structure Slots where
  transforms : Std.TreeMap Nat String := {}
  opacities : Std.TreeMap Nat String := {}
  deriving Inhabited

def Slots.isEmpty (s : Slots) : Bool := s.transforms.isEmpty && s.opacities.isEmpty

private def attr (n : DOM.Node) (key : String) : Option String :=
  (n.attrs.find? fun a => a.ns.isNone && a.lname == key).map (·.value)

private def href (n : DOM.Node) : Option String :=
  (n.attrs.find? fun a => a.lname == "href" && (a.ns.isNone || a.ns == some DOM.xlinkNS)).map (·.value)

/-- The ids that an `href` or a `url(#id)` of the document names. -/
def referencedIds (dom : DOM.Dom) : Std.TreeMap String Unit := Id.run do
  let mut out : Std.TreeMap String Unit := {}
  for n in dom.nodes do
    if n.type != .element then continue
    -- An animation names its target by `href`; it draws no copy of it.
    if n.ns == some DOM.svgNS && animationTags.contains n.lname then continue
    for a in n.attrs do
      let v := a.value.trimAscii.toString
      if a.lname == "href" && v.startsWith "#" then out := out.insert (v.drop 1).toString ()
      for part in (v.splitOn "url(").drop 1 do
        let inner := ((part.splitOn ")").headD "").trimAscii.toString
        let inner := (inner.replace "\"" "").replace "'" ""
        if inner.startsWith "#" then out := out.insert (inner.drop 1).toString ()
  return out

private def svgElement (n : DOM.Node) : Bool := n.type == .element && n.ns == some DOM.svgNS

/-- `id` is an element whose transform `paint` can set (see the module doc). -/
def paintable (dom : DOM.Dom) (referenced : Std.TreeMap String Unit) (id : Nat) : Bool := Id.run do
  let n := dom.get id
  if !svgElement n || !(groupTags.contains n.lname || shapeTags.contains n.lname) then return false
  if (attr n "transform").any (·.trimAscii.toString.startsWith "ref") then return false
  let mut at_ := some id
  for _ in [:dom.size+1] do
    let some k := at_ | return false
    let m := dom.get k
    if !svgElement m then return k != id
    if k != id && !["g","svg","a"].contains m.lname then return false
    if (attr m "id").any referenced.contains then return false
    at_ := m.parent
  return false

/-- An id that no page can hold: it starts with U+0001, which CSS can not select and
an `href` of the page does not name (the layout's copy of the arena only). -/
def reservedId (node : Nat) : String := "\x01paint" ++ toString node

private def count (dom : DOM.Dom) (value : String) : Nat :=
  dom.nodes.foldl (fun c n => if n.type == .element && attr n "id" == some value then c+1 else c) 0

private def setAttr (n : DOM.Node) (key value : String) : DOM.Node :=
  if n.attrs.any (fun a => a.ns.isNone && a.lname == key) then
    {n with attrs := n.attrs.map fun a => if a.ns.isNone && a.lname == key then {a with value} else a}
  else {n with attrs := n.attrs.push {lname := key, value}}

/-- The animation of an `animate` or `animateTransform` element, when this profile
runs it; else the reason. -/
def animationOf (dom : DOM.Dom) (id : Nat) (target : Nat) (base : Array Float) : Except String Animation := do
  let n := dom.get id
  let get := attr n
  let kind ← match n.lname, get "attributeName" with
    | "animateTransform", some "transform" => pure (Kind.transform ((get "type").getD "translate"))
    | "animate", some "opacity" => pure Kind.opacity
    | tag, name => throw s!"{tag} of {name.getD "?"} is not run"
  let dur ← match (get "dur").bind Smil.clockValue with
    | some d => if d == 0 then throw "dur 0" else pure d
    | none => throw "dur not a clock value"
  let begins := match get "begin" with
    | some b => Smil.beginList b
    | none => [.offset 0]
  let count : Option (Option Nat) := (get "repeatCount").map fun v =>
    if v.trimAscii.toString == "indefinite" then none
    else ((CSS.number v).toOption.map fun k => (k*1000).round.toUInt64.toNat)
  let repeatDur : Option (Option Nat) := (get "repeatDur").map fun v =>
    if v.trimAscii.toString == "indefinite" then none else Smil.clockValue v
  let values ← match Smil.valueList (get "values") (get "from") (get "to") (get "by") base with
    | some v => pure v
    | none => throw "no values"
  let keyTimes := ((get "keyTimes").map fun v =>
    ((v.splitOn ";").filterMap fun s => (CSS.number s.trimAscii.toString).toOption).toArray)
  return {
    target, kind, begins, dur, active := Smil.activeDuration dur count repeatDur,
    freeze := get "fill" == some "freeze", values, keyTimes,
    discrete := get "calcMode" == some "discrete", additive := get "additive" == some "sum"}

/-- The layout's copy of the arena, and the plan of a frame: animation elements become
comments, paintable targets get a group id, and `slots` (the elements whose
`transform` scripts set) that are not paintable are listed. -/
def prepare (dom : DOM.Dom) (slots : List Nat) : DOM.Dom × Plan := Id.run do
  let animated := (List.range dom.size).filter fun id =>
    let n := dom.get id
    svgElement n && animationTags.contains n.lname
  if animated.isEmpty && slots.isEmpty then return (dom,{})
  let referenced := referencedIds dom
  let mut out := dom
  let mut plan : Plan := {}
  for id in [:dom.size] do
    if let some v := attr (dom.get id) "id" then
      if !plan.ids.contains v then plan := {plan with ids := plan.ids.insert v id}
  let some root := WebHit.rootElement dom | return (dom,{plan with unpaintable := slots})
  let target := fun (out : DOM.Dom) (plan : Plan) (id : Nat) => Id.run do
    if plan.targets.contains id then return some (out,plan)
    if !paintable dom referenced id then return none
    let n := dom.get id
    let some path := (WebRender.sourcePath dom root (dom.size+1) id []).toOption | return none
    let base := (attr n "transform").getD ""
    let opacity := ((attr n "opacity").bind fun v => (CSS.number v).toOption).getD 1
    let (out,group) := if groupTags.contains n.lname then
        match attr n "id" with
        | some v => if count dom v == 1 then (out,some v) else (out,none)
        | none => ({out with nodes := out.nodes.set! id (setAttr n "id" (reservedId id))},some (reservedId id))
      else (out,none)
    if groupTags.contains n.lname && group.isNone then return none
    return some (out,{plan with targets := plan.targets.insert id {node := id, group, path, base, baseOpacity := opacity}})
  for id in slots do
    match target out plan id with
    | some (o,p) => out := o; plan := p
    | none => plan := {plan with unpaintable := id :: plan.unpaintable}
  for id in animated do
    let n := dom.get id
    out := {out with nodes := out.nodes.set! id {n with type := .comment, data := "", lname := "", attrs := #[]}}
    let goal := match href n with
      | some h => if h.startsWith "#" then plan.ids.get? (h.drop 1).toString else none
      | none => n.parent
    let some goal := goal | plan := {plan with log := s!"{n.lname}: no target" :: plan.log}; continue
    match target out plan goal with
    | none => plan := {plan with log := s!"{n.lname}: target {goal} is not painted alone; its base value shows" :: plan.log}
    | some (o,p) =>
      out := o; plan := p
      let base := if n.lname == "animate" then #[((plan.targets.get? goal).map (·.baseOpacity)).getD 1] else #[]
      match animationOf dom id goal base with
      | .ok a => plan := {plan with animations := plan.animations.push a}
      | .error e => plan := {plan with log := s!"{n.lname}: {e}" :: plan.log}
  return (out,plan)

/-- The click times on element `e` (or a node inside it). `clicks` are the hit nodes
with their times. -/
def clicksOn (dom : DOM.Dom) (clicks : List (Nat × Nat)) (e : Nat) : List Nat :=
  clicks.filterMap fun (t,node) =>
    if CSS.inclusiveAncestor dom e (dom.size+1) (some node) then some t else none

/-- What the elements of the plan are at time `now`: their transforms and opacities, and
whether an animation runs or will begin by the clock (the host then draws the next
frame). `values` are the script values of `transform` and `opacity` slots. -/
def state (plan : Plan) (dom : DOM.Dom) (values : Slots) (now : Nat) (clicks : List (Nat × Nat)) :
    Std.TreeMap Nat (Transform × Option Float) × Bool := Id.run do
  let mut out : Std.TreeMap Nat (Transform × Option Float) := {}
  for (id,t) in plan.targets do
    let base := (values.transforms.get? id).getD t.base
    let opacity := (values.opacities.get? id).map fun v => max 0 (min 1 ((CSS.number v).toOption.getD 1))
    out := out.insert id ((NativeSVG.transformOf base).toOption.getD identity,opacity)
  let mut running := false
  for a in plan.animations do
    let clicks := fun (e : Option String) => match e with
      | none => clicksOn dom clicks a.target
      | some name => match plan.ids.get? name with
        | some node => clicksOn dom clicks node
        | none => []
    if a.begins.any (fun b => match b with | .offset ms => now < ms | _ => false) then running := true
    let some start := Smil.beginAt a.begins clicks now | continue
    let ph := Smil.phase start a.dur a.active a.freeze now
    if let .active _ _ := ph then running := true
    let frac : Float := match ph with
      | .active _ t | .frozen _ t => Float.ofNat t/Float.ofNat a.dur
      | _ => 0
    if ph == .before || ph == .removed then continue
    let some v := Smil.valueAt a.values a.keyTimes a.discrete frac | continue
    let (m,o) := (out.get? a.target).getD (identity,none)
    let baseOpacity := ((plan.targets.get? a.target).map (·.baseOpacity)).getD 1
    match a.kind with
    | .transform kind =>
      let some anim := Smil.transformValue kind v | continue
      out := out.insert a.target (if a.additive then Math.Affine2.compose .float m anim else anim,o)
    | .opacity =>
      let x := v.getD 0 1
      out := out.insert a.target (m,some (max 0 (min 1 (if a.additive then o.getD baseOpacity+x else x))))
  return (out,running)

private def patchNodes (groups : Std.TreeMap String (Transform × Option Float))
    (shapeOf : List Nat → Option (Transform × Option Float)) : Nat → Float → List Node → List Node
  | 0, _, nodes => nodes
  | fuel+1, fade, nodes => nodes.map fun
    | .group (some g) t children =>
      let (m,o) := (groups.get? g).getD (t,none)
      .group (some g) m (patchNodes groups shapeOf fuel (fade*o.getD 1) children)
    | .group none t children => .group none t (patchNodes groups shapeOf fuel fade children)
    | .clipped (some g) t clip children =>
      match groups.get? g with
      | some (m,o) => .clipped (some g) m {clip with transform := m} (patchNodes groups shapeOf fuel (fade*o.getD 1) children)
      | none => .clipped (some g) t clip (patchNodes groups shapeOf fuel fade children)
    | .clipped none t clip children => .clipped none t clip (patchNodes groups shapeOf fuel fade children)
    | .paint item =>
      let shape := if item.primitive.element.isEmpty then none else shapeOf item.primitive.element
      let p := match shape with
        | some (m,o) => {item.primitive with transform := m, opacity := o.getD item.primitive.opacity}
        | none => item.primitive
      if fade == 1 && shape.isNone then .paint item else .paint {item with primitive := {p with opacity := p.opacity*fade}}

/-- The scene with the transforms and opacities of `values` (by node) put on the nodes
of their elements. The opacity of a group (a `text`, whose glyphs are its paths) fades
each of its primitives: the same as the group's opacity where they do not overlap. The
depth is that of the SVG reader's groups (at most 64 here). -/
def patch (plan : Plan) (values : Std.TreeMap Nat (Transform × Option Float)) (scene : Scene) : Scene := Id.run do
  let mut groups : Std.TreeMap String (Transform × Option Float) := {}
  let mut shapes : List (List Nat × Transform × Option Float) := []
  for (id,t) in plan.targets do
    let some (m,o) := values.get? id | continue
    match t.group with
    | some g => groups := groups.insert g (m,o)
    | none => shapes := (t.path,m,o) :: shapes
  let shapeOf := fun (p : List Nat) => (shapes.find? (·.1 == p)).map (·.2)
  return {scene with tree := patchNodes groups shapeOf 64 1 scene.tree}

/-! ### `transform` slots of the script commands -/

/-- The value that stands for a script's `transform` or `opacity` in the layout key: it
can not be either, so the layout knows the slot (`unmark`). -/
def slotMark : String := "\x01transform"
def opacityMark : String := "\x01opacity"


private def field (c : JSON.Json) (k : String) : Option JSON.Json := c.field? k
private def nodeOf (c : JSON.Json) (k : String) : Option Nat :=
  match field c k with
  | some (.number n) => n.toNat?
  | _ => none

/-- The script commands (`WebRenderScript`, kept with one command for each node and
attribute) with the value of each `setAttribute` of `transform` replaced by
`slotMark`, and those values by node. A command is a slot only when no later command
could read the value: no `cloneNode`, `importNode` or `adoptNode` after it, and no
other command on the node's `transform` (`removeAttribute`, the `NS` forms). -/
def slots (commands : List JSON.Json) : List JSON.Json × Slots := Id.run do
  let op := fun (c : JSON.Json) => match field c "op" with | some (.string o) => o | _ => ""
  let name := fun (c : JSON.Json) => match field c "name" with | some (.string n) => n | _ => ""
  let arr := commands.toArray
  -- The last command that copies attribute values.
  let lastCopy := (List.range arr.size).foldl (fun acc i =>
    if ["cloneNode","importNode","adoptNode"].contains (op (arr.getD i .null)) then some i else acc) none
  let touched := commands.filterMap fun c =>
    if ["removeAttribute","setAttributeNS","removeAttributeNS"].contains (op c) && slotAttributes.contains (name c)
    then (nodeOf c "nodeId").map ((·,name c)) else none
  let mut out : Array JSON.Json := #[]
  let mut values : Slots := {}
  for i in [:arr.size] do
    let c := arr.getD i .null
    let isSlot := op c == "setAttribute" && slotAttributes.contains (name c) &&
      (match lastCopy with | some j => j < i | none => true) &&
      (match nodeOf c "nodeId" with | some n => !touched.contains (n,name c) | none => false)
    match isSlot, nodeOf c "nodeId", field c "value", c with
    | true, some n, some (.string v), .object fs =>
      let opacity := name c == "opacity"
      values := if opacity then {values with opacities := values.opacities.insert n v}
        else {values with transforms := values.transforms.insert n v}
      let mark := if opacity then opacityMark else slotMark
      out := out.push (.object (fs.map fun (k,x) => if k == "value" then (k,.string mark) else (k,x)))
    | _, _, _, _ => out := out.push c
  return (out.toList,values)

/-- The layout request with the slot values out (`slots`), and those values. -/
def slotKey (request : JSON.Json) : JSON.Json × Slots :=
  match request with
  | .object fields =>
    match fields.find? (·.1 == "commands") with
    | some (_,.array commands) =>
      let (cs,values) := slots commands
      if values.isEmpty then (request,{}) else
      (.object (fields.map fun (k,v) => if k == "commands" then (k,.array cs) else (k,v)),values)
    | _ => (request,{})
  | _ => (request,{})

/-- The arena of a layout with slots: each `transform` that holds `slotMark` is made
empty (the identity), each `opacity` that holds `opacityMark` is taken out (opacity 1),
and their elements are slots. -/
def unmark (dom : DOM.Dom) : DOM.Dom × List Nat := Id.run do
  let mut out := dom
  let mut found : List Nat := []
  for id in [:dom.size] do
    let n := dom.get id
    if n.type != .element then continue
    let t := n.attrs.any (fun a => a.ns.isNone && a.lname == "transform" && a.value == slotMark)
    let o := n.attrs.any (fun a => a.ns.isNone && a.lname == "opacity" && a.value == opacityMark)
    if t || o then
      let n := if t then setAttr n "transform" "" else n
      let n := if o then {n with attrs := n.attrs.filter (fun a => !(a.ns.isNone && a.lname == "opacity"))} else n
      out := {out with nodes := out.nodes.set! id n}
      found := id :: found
  return (out,found.reverse)

/-! ### Curves off the canvas

A zoomed group (scale 40) puts most of each glyph far outside the canvas, and every
curve of it would be cut into lines finer than a sixty-fourth of a pixel by the backend
(`NativeSVGCurves.flatten`), which costs time and edges for ink that is never seen.
`cull` replaces each quadratic or cubic segment whose control points lie, in canvas
pixels, all outside the canvas widened by a margin, by the line to its end point, and
cuts a long curve that crosses the canvas so that the same holds for its pieces. The
region between a curve and its chord lies in the hull of its control points, so no
winding number changes inside the widened canvas: the pixels drawn are the same. The
margin holds the anti-aliasing reach (2 pixels) and, for a stroke, half the stroke
width times the miter limit. A primitive with dashes, a `pathLength`, or paint other
than a colour (a gradient or an image reads the geometry's box) is left as it is. -/

private def segmentEnd : PathSegment → Point
  | .line p | .quadratic _ p | .cubic _ _ p => p
  | .arc _ _ _ _ _ p => p

private def apply (t : Transform) (p : Point) : Point := ⟨t.a*p.x+t.c*p.y+t.e,t.b*p.x+t.d*p.y+t.f⟩

/-- All of `points`, in canvas pixels by `t`, lie outside `[x0,x1]×[y0,y1]` on one side. -/
def outside (t : Transform) (x0 y0 x1 y1 : Float) (points : List Point) : Bool :=
  let ps := points.map (apply t)
  ps.all (·.x < x0) || ps.all (·.x > x1) || ps.all (·.y < y0) || ps.all (·.y > y1)

/-- Most steps of the work on one curve. -/
def maxPieces : Nat := 4096

private def solidPaint : Paint → Bool
  | .none | .solid _ | .current => true
  | _ => false

private def mid (a b : Point) : Point := ⟨(a.x+b.x)/2,(a.y+b.y)/2⟩

private def controls (start : Point) : PathSegment → List Point
  | .quadratic c p => [start,c,p]
  | .cubic a b p => [start,a,b,p]
  | .line p | .arc _ _ _ _ _ p => [start,p]

/-- A curve cut in two at its middle, by de Casteljau: the same curve in two pieces. -/
private def halves (start : Point) : PathSegment → Option ((PathSegment × Point) × PathSegment)
  | .quadratic c p =>
    let l := mid start c; let r := mid c p; let m := mid l r
    some ((.quadratic l m,m),.quadratic r p)
  | .cubic a b p =>
    let ab := mid start a; let bc := mid a b; let cd := mid b p
    let abc := mid ab bc; let bcd := mid bc cd; let m := mid abc bcd
    some ((.cubic ab abc m,m),.cubic bcd cd p)
  | _ => none

/-- The pieces of one curve, in order: a piece whose points are all off the canvas is the
line to its end; a piece larger than half the canvas that crosses it is cut in two, so that
only what is on the canvas keeps its curves (a glyph at scale 200 has one curve as long as
thousands of pixels: flattened whole, it passes the backend's limit of points). At most
12 cuts deep, and at most `maxPieces` steps; the rest stays as it is. -/
def cullCurve (t : Transform) (x0 y0 x1 y1 : Float) (start : Point) (seg : PathSegment) : Array PathSegment := Id.run do
  let reach := max (x1-x0) (y1-y0)/2
  let mut pending : List (Point × PathSegment × Nat) := [(start,seg,0)]
  let mut out : Array PathSegment := #[]
  for _ in [:maxPieces] do
    match pending with
    | [] => return out
    | (a,piece,depth)::rest =>
      let points := controls a piece
      if outside t x0 y0 x1 y1 points then
        out := out.push (.line (segmentEnd piece))
        pending := rest
      else
        let first := apply t a
        let (lx,hx,ly,hy) := points.foldl (fun (b : Float × Float × Float × Float) q =>
          let p := apply t q
          (min b.1 p.x,max b.2.1 p.x,min b.2.2.1 p.y,max b.2.2.2 p.y)) (first.x,first.x,first.y,first.y)
        let span := max (hx-lx) (hy-ly)
        match (if span > reach && depth < 12 then halves a piece else none) with
        | some ((l,m),r) => pending := (a,l,depth+1)::(m,r,depth+1)::rest
        | none =>
          out := out.push piece
          pending := rest
  return out ++ (pending.map (·.2.1)).toArray

/-- One contour with its off-canvas curves made lines. -/
def cullContour (t : Transform) (x0 y0 x1 y1 : Float) : Contour → Contour
  | .empty closed => .empty closed
  | .path start segments closed => Id.run do
    let mut current := start
    let mut out : Array PathSegment := #[]
    for seg in segments do
      match seg with
      | .quadratic .. | .cubic .. => out := out ++ cullCurve t x0 y0 x1 y1 current seg
      | other => out := out.push other
      current := segmentEnd seg
    return .path start out.toList closed

private def cullPrimitive (x0 y0 x1 y1 : Float) (t : Transform) (p : Primitive) : Primitive :=
  if p.dashParts.isSome || p.pathLength.isSome || !p.style.dashArray.isEmpty ||
      !solidPaint p.style.fill || !solidPaint p.style.stroke then p else
  match p.geometry with
  | .path contours =>
    let norm := max (t.a.abs+t.c.abs) (t.b.abs+t.d.abs)
    let stroke := match p.style.stroke with
      | .none => 0
      | _ => p.style.strokeWidth*norm*(max 1 p.style.miterLimit)/2
    let m := 2+stroke
    if !m.isFinite then p else
    {p with geometry := .path (contours.map (cullContour t (x0-m) (y0-m) (x1+m) (y1+m)))}
  | _ => p

/-- The box on the canvas of a clip under `t`, cut by the box `(x0,y0,x1,y1)`; the box as it
was when the clip is turned or skewed there. Nothing is drawn outside a clip, so what lies
outside it counts as off the canvas: an `svg` in a large window flattens only its own box. -/
private def clipBox (t : Transform) (clip : ClipRect) (x0 y0 x1 y1 : Float) : Float × Float × Float × Float :=
  let m := Math.Affine2.compose .float t clip.transform
  if m.b != 0 || m.c != 0 then (x0,y0,x1,y1) else
  let (ax,bx) := (m.a*clip.x+m.e,m.a*(clip.x+clip.width)+m.e)
  let (ay,by_) := (m.d*clip.y+m.f,m.d*(clip.y+clip.height)+m.f)
  (max x0 (min ax bx),max y0 (min ay by_),min x1 (max ax bx),min y1 (max ay by_))

private def cullNodes : Nat → Float → Float → Float → Float → Transform → List Node → List Node
  | 0, _, _, _, _, _, nodes => nodes
  | fuel+1, x0, y0, x1, y1, t, nodes => nodes.map fun
    | .paint item =>
      .paint {item with primitive := cullPrimitive x0 y0 x1 y1 (Math.Affine2.compose .float t item.primitive.transform) item.primitive}
    | .group id g children => .group id g (cullNodes fuel x0 y0 x1 y1 (Math.Affine2.compose .float t g) children)
    | .clipped id c clip children =>
      let (a,b,e,f) := clipBox t clip x0 y0 x1 y1
      .clipped id c clip (cullNodes fuel a b e f (Math.Affine2.compose .float t c) children)

/-- The scene with its off-canvas curves made lines (see above). The canvas is the
scene's `width` by `height` after its mapping, cut by the clips around each primitive. -/
def cull (scene : Scene) : Scene :=
  let m := scene.mapping
  let root : Transform := ⟨m.sx,0,0,m.sy,m.tx-m.minX*m.sx,m.ty-m.minY*m.sy⟩
  {scene with tree := cullNodes 64 0 0 (Float.ofNat scene.width) (Float.ofNat scene.height) root scene.tree}

/-! ### Retained compile of a layer (`NativeSVG.Retained`)

A frame in which few primitives changed: the rest keep their compile. A leaf of the layer's
tree is the leaf of the last frame at the same place when it is the same object of the
layout's scene (`WebDocument` compares the address) in the same context: the transforms
down to it, the cull box and the clips around it. So `cull`, `toScene` and the lowering, which
are pure maps over the leaves, give the same primitive for it. The tree here is walked in the
order of `lowerFromRootList` and with the same `cullNodes` arithmetic; the bytes are checked
against the plain path (`partial_frame_test.ts`). -/

/-- The source of a primitive of a layer and its context. -/
structure LeafKey where
  primitive : Rendering.Primitive
  cull : Float × Float × Float × Float
  t : Transform
  parent : Transform
  clips : List NativeSVG.ClipRect

/-- A leaf: its key, and how to make the primitive that it compiles (`cullPrimitive`, `toPrimitive`,
the lowering of `lower`), as `leavesOf` found it. -/
abbrev Leaf := LeafKey × (Unit → Except String NativeSVG.Primitive)

private def sameFloat (a b : Float) : Bool := a.toBits == b.toBits
private def sameTransform (a b : Transform) : Bool :=
  sameFloat a.a b.a && sameFloat a.b b.b && sameFloat a.c b.c && sameFloat a.d b.d && sameFloat a.e b.e && sameFloat a.f b.f
private def sameClip (a b : NativeSVG.ClipRect) : Bool :=
  sameFloat a.x b.x && sameFloat a.y b.y && sameFloat a.width b.width && sameFloat a.height b.height && sameTransform a.transform b.transform
/-- The context of the two keys is the same (their source object is compared apart). -/
def LeafKey.sameContext (a b : LeafKey) : Bool :=
  sameFloat a.cull.1 b.cull.1 && sameFloat a.cull.2.1 b.cull.2.1 && sameFloat a.cull.2.2.1 b.cull.2.2.1 && sameFloat a.cull.2.2.2 b.cull.2.2.2 &&
  sameTransform a.t b.t && sameTransform a.parent b.parent &&
  a.clips.length == b.clips.length && (a.clips.zip b.clips).all fun (x,y) => sameClip x y

/-- `cullPrimitive` gives this primitive back with its geometry as it was: no curve is off the
canvas on one side, or long enough for `cullCurve` to cut. Then the flattened geometry of one
transform serves another with the same linear part. -/
private def cullFree (k : LeafKey) : Bool :=
  let p := k.primitive
  if p.dashParts.isSome || p.pathLength.isSome || !p.style.dashArray.isEmpty ||
      !solidPaint p.style.fill || !solidPaint p.style.stroke then true else
  match p.geometry with
  | .path contours =>
    let t := Math.Affine2.compose .float k.t p.transform
    let norm := max (t.a.abs+t.c.abs) (t.b.abs+t.d.abs)
    let stroke := match p.style.stroke with
      | .none => 0
      | _ => p.style.strokeWidth*norm*(max 1 p.style.miterLimit)/2
    let m := 2+stroke
    if !m.isFinite then true else
    let (x0,y0,x1,y1) := (k.cull.1-m,k.cull.2.1-m,k.cull.2.2.1+m,k.cull.2.2.2+m)
    let reach := max (x1-x0) (y1-y0)/2
    contours.all fun
      | .empty _ => true
      | .path start segments _ => Id.run do
        let mut current := start
        for seg in segments do
          match seg with
          | .quadratic .. | .cubic .. =>
            let points := controls current seg
            if outside t x0 y0 x1 y1 points then return false
            let first := apply t current
            let (lx,hx,ly,hy) := points.foldl (fun (b : Float × Float × Float × Float) q =>
              let p := apply t q
              (min b.1 p.x,max b.2.1 p.x,min b.2.2.1 p.y,max b.2.2.2 p.y)) (first.x,first.x,first.y,first.y)
            if max (hx-lx) (hy-ly) > reach then return false
          | _ => pure ()
          current := segmentEnd seg
        return true
  | _ => true

/-- Same geometry and style objects (the caller compares their addresses; this is the rest):
the record of `a` serves `b` with `b`'s transform when both have no clips of their own, no
dashes kept in the source, the same clips around and cull box, the same linear part of the
screen transform (so `flatten` and the stroke widening do the same), and `cull` changes
neither. -/
def LeafKey.movedOf (a b : LeafKey) : NativeSVG.Reuse :=
  let ta := Math.Affine2.compose .float a.t a.primitive.transform
  let tb := Math.Affine2.compose .float b.t b.primitive.transform
  let linear := sameFloat ta.a tb.a && sameFloat ta.b tb.b && sameFloat ta.c tb.c && sameFloat ta.d tb.d
  if linear && a.primitive.clips.isEmpty && b.primitive.clips.isEmpty &&
      a.primitive.dashParts.isNone && b.primitive.dashParts.isNone &&
      a.primitive.pathLength.isNone && b.primitive.pathLength.isNone &&
      sameFloat a.cull.1 b.cull.1 && sameFloat a.cull.2.1 b.cull.2.1 && sameFloat a.cull.2.2.1 b.cull.2.2.1 && sameFloat a.cull.2.2.2 b.cull.2.2.2 &&
      a.clips.length == b.clips.length && (a.clips.zip b.clips).all (fun (x,y) => sameClip x y) &&
      cullFree a && cullFree b then
    .moved (Math.Affine2.compose .float b.parent b.primitive.transform) b.primitive.opacity
  else .different

/-- The leaves of `nodes` in paint order, from the same arguments as `cullNodes` and
`lowerList`: the cull box and transform, the transform from the root, the clips around. -/
private def leavesGo : Nat → Float → Float → Float → Float → Transform → Transform →
    List NativeSVG.ClipRect → List Node → Array Leaf → Except String (Array Leaf)
  | 0, _, _, _, _, _, _, _, _, _ => .error "retained compile: tree too deep"
  | fuel+1, x0, y0, x1, y1, t, parent, clips, nodes, acc =>
    nodes.foldlM (m := Except String) (fun acc node =>
      match node with
      | .paint item =>
        let prim := item.primitive
        pure (acc.push (⟨prim,(x0,y0,x1,y1),t,parent,clips⟩, fun (_ : Unit) =>
          let culled := cullPrimitive x0 y0 x1 y1 (Math.Affine2.compose .float t prim.transform) prim
          let lowered := NativeSVG.Primitive.lowerUnder parent [] (WebRenderSVG.toPrimitive culled)
          .ok {lowered with clips := clips ++ lowered.clips}))
      | .group _ g children =>
        leavesGo fuel x0 y0 x1 y1 (Math.Affine2.compose .float t g) (Math.Affine2.compose .float parent g) clips children acc
      | .clipped _ c clip children =>
        let (a,b,e,f) := clipBox t clip x0 y0 x1 y1
        let lowered := NativeSVG.ClipRect.lowerUnder parent (WebRenderSVG.toClip clip)
        leavesGo fuel a b e f (Math.Affine2.compose .float t c) (Math.Affine2.compose .float parent c) (clips ++ [lowered]) children acc) acc

/-- The leaves of a layer's tree (`cull` then `toScene` then `lowerFromRootList`). -/
def leavesOf (scene : Scene) : Except String (Array Leaf) :=
  let m := scene.mapping
  let root : Transform := ⟨m.sx,0,0,m.sy,m.tx-m.minX*m.sx,m.ty-m.minY*m.sy⟩
  leavesGo 64 0 0 (Float.ofNat scene.width) (Float.ofNat scene.height) root Rendering.identity [] scene.tree #[]

abbrev RetainedLayer := NativeSVG.Retained LeafKey

/-- A layer's answer with the compile of the last frame kept where it serves: the new
retained compile, the rectangles of damage (`none`: draw the whole layer), the JSON of the
answer and its sections. `layoutText` is `WebRender.layoutJSON` of the layer when the
caller knows it is the one of the last frame. -/
def retainedAnswer (reuse : LeafKey → LeafKey → NativeSVG.Reuse) (prev : Option RetainedLayer) (layer : Scene)
    (boxes : Array Rendering.Layout.Box) (face : Option Rendering.FontProvider.Face) (first : Nat)
    (layoutText : Option String) : Except String (RetainedLayer × Option (Array NativeSVG.DamageRect) × String × Array ByteArray × String × Nat × Nat) := do
  let leaves ← leavesOf layer
  let (retained,changed,moved) ← NativeSVG.compileRetained reuse prev layer.width layer.height (WebRenderSVG.toMapping layer.mapping) leaves
  let tiles := retained.tileWords
  if tiles.back! > NativeSVG.maxPaintTableWords then throw s!"paint table exceeds {NativeSVG.maxPaintTableWords} words"
  let (head,sections) := retained.json first tiles
  let layout := layoutText.getD (WebRender.layoutJSON layer boxes face)
  let value := (head.dropEnd 1).toString ++ ",\"webRender\":" ++ layout ++ "}"
  let damage := match changed,prev with
    | some idx,some p => NativeSVG.damageRects p.items retained.items idx layer.width layer.height
    | _,_ => none
  return (retained,damage,value,sections,layout,(changed.map (·.size)).getD retained.items.size-moved,moved)

end WebPaint
