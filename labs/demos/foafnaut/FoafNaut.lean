import Font
import Geometry
import SceneSVG
import L4Factoidal.UI.PolicyProtocol
import L4Factoidal.UI.Presentation
import FoafGraph

namespace NativeFoafNaut
open NativeGraphics L4Factoidal.JSON

def graphLimits : FoafGraph.Limits := {maxPeople:=16,maxLinks:=48}
private def clamp (lo hi n : Int) := max lo (min hi n)
private def bound (lo hi n : Nat) := max lo (min hi n)
structure Position where
  x : Int
  y : Int
  deriving DecidableEq, Repr, Inhabited
structure Model where
  graph : FoafGraph.Data
  width : Nat
  height : Nat
  policy : L4Factoidal.UI.LayoutPolicy.Config := L4Factoidal.UI.LayoutPolicy.defaultConfig
  positions : Array Position
  hidden : Array Bool
  pinned : Array Bool
  focus : Nat := 0
  selection : Nat := 0
  dragging : Bool := false
  animating : Bool := true
  closed : Bool := false
  revision : Nat := 0
  accumulator : Nat := 0
  address : String := ""
  cursor : Nat := 0
  anchor : Nat := 0
  editing : Bool := false
  message : String := "Local graph ready"
  deriving DecidableEq, Repr

private def locator (graph : FoafGraph.Data) (i : Nat) : String :=
  match graph.people[i]? with
  | none => ""
  | some p => match p.subject with
    | .iri iri => iri.val
    | .bnode id => "_:" ++ id
private def addressValue (graph : FoafGraph.Data) (i : Nat) : String :=
  String.ofList ((locator graph i).toList.take 512)

-- Sixteen fixed radial directions avoid host geometry and floating-point state.
private def directions : Array (Int × Int) := #[
  (0,-1000),(383,-924),(707,-707),(924,-383),(1000,0),(924,383),(707,707),(383,924),
  (0,1000),(-383,924),(-707,707),(-924,383),(-1000,0),(-924,-383),(-707,-707),(-383,-924)]

def Model.targets (m : Model) : Array Position :=
  (List.range m.graph.people.size).toArray.map fun i =>
    if i == 0 then ⟨500,350⟩ else
      let d := directions[((i-1)*16/max 1 (m.graph.people.size-1))%16]!
      ⟨500+d.1*360/1000,350+d.2*240/1000⟩

-- Visibility and emphasis cannot reflow any person's radial target.
theorem Model.targets_visibility (m : Model) (hidden : Array Bool) :
    ({m with hidden:=hidden} : Model).targets = m.targets := rfl
theorem Model.targets_focus (m : Model) (focus : Nat) :
    ({m with focus:=focus} : Model).targets = m.targets := rfl

def initial (graph : FoafGraph.Data) (width height : Nat)
    (policy : L4Factoidal.UI.LayoutPolicy.Config := L4Factoidal.UI.LayoutPolicy.defaultConfig) : Model := Id.run do
  let m : Model := {
    graph := graph
    policy := policy
    width := bound 16 4096 width
    height := bound 16 4096 height
    positions := Array.replicate graph.people.size ⟨500,350⟩
    hidden := Array.replicate graph.people.size false
    pinned := Array.replicate graph.people.size false
    address := addressValue graph 0}
  return {m with positions:=m.targets}

private def eased (a b : Int) : Int :=
  if (b-a).natAbs <= 5 then b else a+(b-a)/6
def Model.ease (m : Model) : Model :=
  let targets := m.targets
  {m with positions:=m.positions.mapIdx fun i p =>
    if m.hidden[i]! || m.pinned[i]! || (m.dragging && m.selection == i+1) then p
    else ⟨eased p.x targets[i]!.x,eased p.y targets[i]!.y⟩}

private def tick (m : Model) (ms : Nat) : Model := Id.run do
  if !m.animating then return m
  let total := m.accumulator+min 128 ms
  let mut n := {m with accumulator:=total%16}
  for _ in List.range (min 8 (total/16)) do n := n.ease
  return n

private def fontSize (m : Model) : Nat :=
  max 1 (min ((2*m.width+999)/1000) ((2*m.height+699)/700))
private def addressColumns (m : Model) : Nat := min 64 (max 1 ((720*m.width/1000)/(6*fontSize m)))
private def addressScroll (m : Model) : Nat := m.cursor+1-addressColumns m

inductive HitTarget where
  | person (index control : Nat)
  | address
  | blocked
  deriving Repr, BEq, DecidableEq

structure PaintedPart where
  shape : Shape
  target : HitTarget
  visible : Bool := true
  deriving Repr

private def canvas : RGB := ⟨247,249,252⟩
private def slate : RGB := ⟨62,76,95⟩
private def white : RGB := ⟨255,255,255⟩
private def accent : RGB := ⟨105,103,218⟩
private def point (m : Model) (x y : Int) : Point :=
  ⟨x.toNat*m.width/1000,y.toNat*m.height/700⟩
private def scale (m : Model) (n : Nat) : Nat := max 1 (min (n*m.width/1000) (n*m.height/700))
private def offscreen : Position := ⟨100000,100000⟩
private def displayedPosition (m : Model) (i : Nat) : Position := if m.hidden[i]! then offscreen else m.positions[i]!

/-- Keep RDF literal labels as supplied. Only labels explicitly marked as
adapter fallbacks are shortened; exact labels and typed IDs stay in the model. -/
def displayName (m : Model) (i : Nat) : String :=
  match m.graph.people[i]? with
  | none => "PERSON " ++ toString (i+1)
  | some person =>
    if !person.labelIsFallback then person.label else
      match person.subject with
      | .bnode _ => "PERSON " ++ toString (i+1)
      | .iri iri =>
        let fragment := if (iri.val.splitOn "#").length > 1 then
          (iri.val.splitOn "#").getLast?.getD "" else ""
        let beforeFragment := (iri.val.splitOn "#").head!
        let path := ((beforeFragment.splitOn "?").head!).splitOn "/"
        let tail := (path.filter (!·.isEmpty)).getLast?.getD ""
        if !fragment.isEmpty then fragment else
          if !tail.isEmpty && !tail.contains ':' then tail else "PERSON " ++ toString (i+1)

private def edgeShapes (m : Model) (l : FoafGraph.Link) : List Shape :=
  let hidden := m.hidden[l.source]! || m.hidden[l.target]!
  let a := if hidden then offscreen else m.positions[l.source]!
  let b := if hidden then offscreen else m.positions[l.target]!
  let dx := b.x-a.x
  let dy := b.y-a.y
  let norm := max 1 (max dx.natAbs dy.natAbs)
  -- Wide cards need more horizontal clearance than the round person halo.
  let clearance : Int := if dx.natAbs > dy.natAbs*2 then 88 else 54
  let tip : Position := ⟨b.x-dx*clearance/Int.ofNat norm,b.y-dy*clearance/Int.ofNat norm⟩
  let tail : Position := ⟨tip.x-dx*15/Int.ofNat norm,tip.y-dy*15/Int.ofNat norm⟩
  let color := if m.selection == l.source+1 || m.selection == l.target+1 then accent else ⟨130,174,196⟩
  [.segment (point m a.x a.y) (point m tip.x tip.y) (scale m 3) color,
   .segment (point m tip.x tip.y) (point m (tail.x-dy*7/Int.ofNat norm) (tail.y+dx*7/Int.ofNat norm)) (scale m 3) color,
   .segment (point m tip.x tip.y) (point m (tail.x+dy*7/Int.ofNat norm) (tail.y-dx*7/Int.ofNat norm)) (scale m 3) color]

def personPieces (m : Model) (i : Nat) : List PaintedPart :=
  let c := displayedPosition m i
  let p := fun x y => point m (c.x+x) (c.y+y)
  let rect := fun x y w h color => Shape.rectangle (p x y) ⟨scale m w,scale m h⟩ color
  let circle := fun x y r color => Shape.circle (p x y) (scale m r) color
  let line := fun x y x' y' color => Shape.segment (p x y) (p x' y') (scale m 2) color
  let name := displayName m i
  -- Base 2x bitmap cells, rounded up to keep normal desktop labels readable.
  let fontScale := max 1 (min ((2*m.width+999)/1000) ((2*m.height+699)/700))
  let columns := min 12 ((scale m 154 - 8)/(6*fontScale))
  let shown := min columns name.length
  let label := String.ofList (name.toList.take shown ++ List.replicate (12-shown) ' ')
  let anchor := p 0 0
  let textOrigin : Point := ⟨anchor.x-shown*6*fontScale/2,anchor.y+scale m 8-7*fontScale/2⟩
  let halo : RGB := if i%3 == 0 then ⟨222,242,237⟩ else if i%3 == 1 then ⟨237,232,249⟩ else ⟨252,234,222⟩
  let mint : RGB := if i%3 == 1 then ⟨142,195,192⟩ else ⟨130,202,174⟩
  let capsule := fun x y x' y' stroke color => Shape.segment (p x y) (p x' y') (scale m stroke) color
  let part (control : Nat) (shape : Shape) : PaintedPart :=
    {shape, target:=.person i control, visible:=!m.hidden[i]!}
  let drag := part 0
  let reveal := part 1
  let hide := part 2
  [drag (circle 3 5 46 ⟨228,233,241⟩),
   drag (circle 0 0 46 (if m.selection == i+1 then ⟨218,216,250⟩ else halo)),
   drag (rect (-8) 9 16 27 slate),drag (rect (-6) 10 12 25 ⟨234,137,137⟩),
   drag (capsule (-23) (-15) (-23) 6 9 slate),drag (capsule (-23) (-15) (-23) 6 6 ⟨246,193,161⟩),
   drag (capsule 23 (-15) 23 6 9 slate),drag (capsule 23 (-15) 23 6 6 ⟨246,193,161⟩),
   drag (rect (-20) (-23) 40 30 slate),drag (rect (-19) (-22) 38 28 mint),
   reveal (circle 0 (-34) 12 slate),reveal (circle 0 (-34) 10 white),
   drag (capsule (-64) 12 64 12 30 ⟨222,228,237⟩),
   drag (capsule (-64) 8 64 8 30 (if m.selection == i+1 then accent else ⟨210,219,230⟩)),
   drag (capsule (-64) 8 64 8 27 (if i%3 == 2 then ⟨255,250,239⟩ else white)),
   reveal (line (-6) (-34) 6 (-34) slate),reveal (line 0 (-40) 0 (-28) slate),
   hide (circle 0 35 11 slate),hide (circle 0 35 9 white),hide (line (-5) 35 5 35 slate)] ++
   (NativeFont.text textOrigin fontScale label slate).map drag

private def padded (text : String) (slots : Nat) : String :=
  String.ofList (text.toList.take slots ++ List.replicate (slots-min slots text.length) ' ')

def chromePieces (m : Model) : List PaintedPart :=
  let p := fun x y => point m x y
  let size := fontSize m
  let origin := p 246 21
  let columns := addressColumns m
  let scroll := addressScroll m
  let visible := String.ofList (m.address.toList.drop scroll |>.take columns)
  let lo := min columns (min m.anchor m.cursor-scroll)
  let hi := min columns (max m.anchor m.cursor-scroll)
  let selected := m.editing && hi > lo
  let selectOrigin := if selected then Point.mk (origin.x+lo*6*size) (origin.y-1) else ⟨100000,100000⟩
  let caretOrigin := if m.editing then Point.mk (origin.x+(m.cursor-scroll)*6*size) origin.y else ⟨100000,100000⟩
  let blocked (shape : Shape) : PaintedPart := {shape,target:=.blocked}
  let address (shape : Shape) : PaintedPart := {shape,target:=.address}
  [blocked (.rectangle (p 0 0) ⟨m.width,58*m.height/700⟩ ⟨26,36,58⟩),
   blocked (.segment (p 0 57) (p 1000 57) (scale m 1) ⟨76,197,190⟩),
   blocked (.circle (p 20 28) (scale m 4) ⟨96,230,190⟩)] ++
  (NativeFont.text (p 34 21) size (padded "FOAFnaut" 12) ⟨181,244,226⟩).map blocked ++
  [address (.segment (p 238 31) (p 965 31) (scale m 36) ⟨15,24,42⟩),
   address (.segment (p 238 28) (p 965 28) (scale m 34) (if m.editing then ⟨93,225,205⟩ else ⟨81,104,138⟩)),
   address (.segment (p 238 28) (p 965 28) (scale m 31) white),
   address (.rectangle selectOrigin ⟨max 1 ((hi-lo)*6*size),7*size+2⟩ ⟨210,222,255⟩)] ++
  (NativeFont.text origin size (padded visible 64) slate).map address ++
  [address (.rectangle caretOrigin ⟨max 1 (scale m 2),7*size⟩ accent)] ++
  (NativeFont.text (p 24 682) (max 1 (size-1)) (padded ("LOCAL | " ++ m.message) 32) ⟨93,114,143⟩).map blocked

/-- One ordered drawing record feeds rendering and picking. Hidden slots stay
outside the canvas to retain the persistent GPU pipeline, and cannot be picked.
Blocking chrome participates in paint order instead of forwarding clicks. -/
def Model.parts (m : Model) : List PaintedPart :=
  ((m.graph.links.toList.flatMap (edgeShapes m)).map fun shape => {shape,target:=.blocked}) ++
  (List.range m.graph.people.size).flatMap (personPieces m) ++ chromePieces m

def Model.scene (m : Model) : Scene :=
  {width:=m.width,height:=m.height,background:=canvas,shapes:=m.parts.map (·.shape)}

/-- Integer pointer coordinates, not a claim about Float/WGSL raster rounding. -/
def Model.pick (m : Model) (x y : Int) : Option PaintedPart :=
  if x < 0 || y < 0 || x ≥ m.width || y ≥ m.height then none
  else m.parts.reverse.find? fun part => part.visible && NativeGeometry.hit part.shape x y == some true

def Model.visibleDrawings (m : Model) : List (Nat × List Shape) :=
  (List.range m.graph.people.size).filterMap fun i =>
    if m.hidden[i]! then none else some (i,(personPieces m i).map (·.shape))

/-- Conservative configured aggregate box budget. This reports violations;
layout transitions do not yet enforce the budget. No pixel-occlusion claim. -/
def Model.footprints (m : Model) : List (Option NativeGeometry.Box) :=
  let drawings := m.visibleDrawings
  let viewport : NativeGeometry.Box := ⟨0,0,m.width,m.height⟩
  drawings.map fun (_,shapes) => (NativeGeometry.footprint shapes).map (·.intersection viewport)

def Model.layoutChecks (m : Model) : List (Nat × NativeGeometry.NodeCheck) :=
  let drawings := m.visibleDrawings
  let checks := L4Factoidal.UI.LayoutPolicy.checkFootprints m.policy m.footprints
  (drawings.map (·.1)).zip checks

private def logical (m : Model) (x y : Int) : Int × Int :=
  (x*1000/Int.ofNat m.width,y*700/Int.ofNat m.height)
private def hit (m : Model) (x y : Int) : Nat × Nat :=
  match (m.pick x y).map (fun (part : PaintedPart) => part.target) with
  | some (HitTarget.person i control) => (i+1,control)
  | _ => (0,0)

/-- Event kinds match the native transport: resize/down/move/up/key/close/tick.
Head reveals the person's already-loaded direct incoming/outgoing neighbors.
Foot hides only that person and incident links. Neither operation changes
positions or layout targets. No network fetch or automatic recentering.
Dragging pins that position through release and future ticks; R clears pins. -/
private def updateGraph (m : Model) (kind : Nat) (a b : Int) : Model × List String := Id.run do
  if m.closed then return (m,[])
  let mut n := m
  let mut commands : List String := []
  if kind == 1 then n := {m with width:=bound 16 4096 a.toNat,height:=bound 16 4096 b.toNat}
  else if kind == 2 then
    let (selected,control) := hit m a b
    if selected == 0 then n := {m with selection:=0,dragging:=false}
    else if control == 1 then
      let who := selected-1
      let hidden := m.hidden.mapIdx fun i old =>
        if i == who || m.graph.links.any (fun l =>
          (l.source == who && l.target == i) || (l.target == who && l.source == i)) then false else old
      n := {m with hidden,focus:=who,selection:=selected,dragging:=false}
    else if control == 2 then
      let hidden := m.hidden.set! (selected-1) true
      n := {m with hidden,selection:=0,dragging:=false}
    else n := {m with selection:=selected,dragging:=true}
  else if kind == 3 && m.dragging && m.selection > 0 then
    let (x,y) := logical m a b
    n := {m with
      positions := m.positions.set! (m.selection-1) ⟨clamp 85 915 x,clamp 100 635 y⟩
      pinned := m.pinned.set! (m.selection-1) true}
  else if kind == 4 then n := {m with dragging:=false}
  else if kind == 5 && a == 49 then
    n := {m with animating:=!m.animating}
    commands := [if n.animating then "startClock" else "stopClock"]
  else if kind == 5 && a == 15 then
    n := {initial m.graph m.width m.height m.policy with revision:=m.revision}
    commands := ["startClock"]
  else if kind == 6 || (kind == 5 && a == 53) then
    return ({m with closed:=true,dragging:=false,revision:=m.revision+1},["close"])
  else if kind == 7 then n := tick m a.toNat
  if n == m then return (m,[])
  let visible := n.positions != m.positions || n.hidden != m.hidden || n.focus != m.focus ||
    n.selection != m.selection || n.width != m.width || n.height != m.height
  return ({n with revision:=m.revision+1},(if visible then ["render"] else []) ++ commands)

structure Result where
  model : Model
  commands : List String := []
  clipboardWrite : Option String := none
  clipboardRead : Bool := false


def selectedText (m : Model) : String :=
  String.ofList (m.address.toList.drop (min m.anchor m.cursor) |>.take (max m.anchor m.cursor-min m.anchor m.cursor))

private def editorResult (old n : Model) (write : Option String := none) (read : Bool := false) : Result :=
  if n == old then {model:=old,clipboardWrite:=write,clipboardRead:=read}
  else {model:={n with revision:=old.revision+1},commands:=["render"],clipboardWrite:=write,clipboardRead:=read}

/-- One scalar-indexed selection replacement. Clipboard strings are inserted
once, never expanded through a bounded native event queue. Control characters
are ignored. The address is limited to 512 Unicode scalars, with no shaping
or grapheme-aware cursor claim. -/
def insertText (m : Model) (text : String) : Result := Id.run do
  if m.closed || !m.editing || text.length > 65536 then return {model:=m}
  let start := min m.anchor m.cursor
  let stop := max m.anchor m.cursor
  let chars := m.address.toList
  let leading :=  chars.take start
  let suffix := chars.drop stop
  let available := 512-leading.length-suffix.length
  let accepted := text.toList.filter fun c => c.toNat >= 32 && c.toNat != 127
  let inserted := accepted.take available
  let cursor := leading.length+inserted.length
  return editorResult m {m with
    address := String.ofList (leading++inserted++suffix)
    cursor := cursor
    anchor := cursor
    message := if accepted.length > available then "Address truncated to 512 Unicode scalars"
      else if accepted.length != text.length then "Ignored control characters in address"
      else "Local graph - Enter selects loaded RDF identity"}

private def editKey (m : Model) (key mods : Nat) : Result := Id.run do
  let command := mods &&& 2 != 0
  let shift := mods &&& 1 != 0
  if command && key == 0 then
    return editorResult m {m with anchor:=0,cursor:=m.address.length}
  if command && key == 8 then
    let text := selectedText m
    return editorResult m {m with message:="Copied local address selection"} (if text.isEmpty then none else some text)
  if command && key == 7 then
    let text := selectedText m
    let result := insertText m ""
    return {result with clipboardWrite:=if text.isEmpty then none else some text}
  if command && key == 9 then
    return editorResult m {m with message:="Paste into local address"} none true
  if key == 53 || key == 48 then return editorResult m {m with editing:=false}
  if key == 36 || key == 76 then
    let input := m.address.trimAscii.toString
    match (List.range m.graph.people.size).find? (fun i =>
      locator m.graph i == input || ((m.graph.people[i]?).map (·.id)) == some input) with
    | none => return editorResult m {m with message:="Not in loaded graph - no network request"}
    | some i =>
      let address := addressValue m.graph i
      return editorResult m {m with
        hidden := m.hidden.set! i false
        selection := i+1
        focus := i
        dragging := false
        editing := false
        address := address
        cursor := address.length
        anchor := address.length
        message := "Selected loaded RDF identity"}
  if key == 123 || key == 124 || key == 115 || key == 119 then
    let cursor := if key == 115 || (command && key == 123) then 0
      else if key == 119 || (command && key == 124) then m.address.length
      else if !shift && m.cursor != m.anchor then
        if key == 123 then min m.cursor m.anchor else max m.cursor m.anchor
      else if key == 123 then m.cursor-1 else min m.address.length (m.cursor+1)
    return editorResult m {m with cursor,anchor:=if shift then m.anchor else cursor}
  if key == 51 || key == 117 then
    if m.cursor != m.anchor then return insertText m ""
    else if key == 51 && m.cursor > 0 then return insertText {m with anchor:=m.cursor-1} ""
    else if key == 117 && m.cursor < m.address.length then return insertText {m with anchor:=m.cursor+1} ""
  return {model:=m} -- Printable key5 is followed by committed text9, once.

def transitionModel (m : Model) (kind : Nat) (a b : Int) : Result := Id.run do
  if m.closed then return {model:=m}
  if kind == 10 then
    return editorResult m {m with message:=if a == 1 then "Clipboard read unavailable"
      else if a == 2 then "Clipboard write failed" else "Clipboard transport unavailable"}
  if kind == 5 && ((a == 37 && b.toNat &&& 2 != 0) || (a == 48 && !m.editing)) then
    return editorResult m {m with
      editing := true
      dragging := false
      anchor := 0
      cursor := m.address.length
      message := "Local RDF identity - no network fetching"}
  if kind == 2 then
    if (m.pick a b).map (·.target) == some .address then
      let cursor := min m.address.length (addressScroll m+(a-Int.ofNat (246*m.width/1000)).toNat/(6*fontSize m))
      return editorResult m {m with editing:=true,dragging:=false,cursor,anchor:=cursor}
  if m.editing && kind == 5 then return editKey m a.toNat b.toNat
  if kind == 9 then
    if a < 32 || a > 0x10FFFF || (a >= 0xD800 && a <= 0xDFFF) then return {model:=m}
    return insertText m (String.singleton (Char.ofNat a.toNat))
  let (n,commands) := updateGraph (if kind == 2 then {m with editing:=false} else m) kind a b
  let n := if kind == 2 && n.selection > 0 then
    let address := addressValue n.graph (n.selection-1)
    {n with address,cursor:=address.length,anchor:=address.length,message:="Loaded RDF person selected"}
    else n
  let changedFocus := m.editing != n.editing
  return {
    model := if changedFocus && n.revision == m.revision then {n with revision:=m.revision+1} else n
    commands := if changedFocus && !commands.contains "render" then "render"::commands else commands}

-- Preserve the small state-test interface; exported transitions carry effects.
def update (m : Model) (kind : Nat) (a b : Int) : Model × List String :=
  let result := transitionModel m kind a b
  (result.model,result.commands)


private def num (n : Nat) : Json := .number (toString n)
private def int (n : Int) : Json := .number (toString n)

def Model.layoutReport (m : Model) (checked : Bool := false) : Json :=
  let checks := m.layoutChecks
  .object [
    ("metric",.string "viewport-clipped node bounding boxes; sum of pairwise intersections"),
    ("profile",.string L4Factoidal.UI.LayoutPolicy.experimentalGraphBrowserV1.name),
    ("policy",L4Factoidal.UI.PolicyProtocol.configJson m.policy),
    ("thresholdBasisPoints",num m.policy.overlapBps),("enforced",.bool checked),
    ("targetCheckHz",num m.policy.checkHz),
    ("timing",.string (if checked then "checked at export; no scheduling claim"
      else "diagnostic per response; presentation admission not enabled in this view")),
    ("withinBudget",.bool (checks.all fun (_,c) => c.accepted)),
    ("nodes",.array (checks.map fun (i,c) => .object [
      ("person",num i),("area",num c.area),("overlapUpperBound",num c.overlapSum),
      ("withinBudget",.bool c.accepted),
      ("bounds",c.footprint.map (fun b => .array [int b.left,int b.top,int b.right,int b.bottom]) |>.getD .null)]))]

def Model.toJson (m : Model) : Json := .object [
  ("graph",m.graph.toJson),("width",num m.width),("height",num m.height),
  ("policy",L4Factoidal.UI.PolicyProtocol.configJson m.policy),
  ("positions",.array (m.positions.toList.map fun p => .array [int p.x,int p.y])),
  ("hidden",.array (m.hidden.toList.map Json.bool)),("focus",num m.focus),
  ("pinned",.array (m.pinned.toList.map Json.bool)),
  ("selection",num m.selection),("dragging",.bool m.dragging),("animating",.bool m.animating),
  ("closed",.bool m.closed),("revision",num m.revision),("accumulator",num m.accumulator),
  ("address",.string m.address),("cursor",num m.cursor),("anchor",num m.anchor),
  ("editing",.bool m.editing),("message",.string m.message)]
def Model.encode (m : Model) : String := toStringCompact m.toJson

private def natural (j : Json) : Option Nat := do
  let .number s := j | none
  if s.length > 10 || !s.toList.all Char.isDigit then none else s.toNat?
private def integer (j : Json) : Option Int := do
  let .number s := j | none
  if s.length > 7 then none else do
    let n ← s.toInt?
    if toString n == s then some n else none
private def natField (j : Json) (k : String) := (j.field? k).bind natural

def Model.decode (wire : String) : Option Model := do
  if wire.length > 131072 || !L4Factoidal.UI.PolicyProtocol.boundedNesting wire then none else do
    let j ← (parseJson wire).toOption
    let .object fs := j | none
    let names := ["graph","width","height","policy","positions","hidden","pinned","focus","selection","dragging","animating","closed","revision","accumulator",
      "address","cursor","anchor","editing","message"]
    if fs.length != names.length || !names.all (fun name => (fs.filter (·.1 == name)).length == 1) then none else do
      let graph ← (FoafGraph.Data.fromJson (← j.field? "graph") graphLimits).toOption
      let width ← natField j "width"
      let height ← natField j "height"
      let policy ← (L4Factoidal.UI.PolicyProtocol.readConfig (← j.field? "policy")).toOption
      let positions ← (← j.getArray? "positions").mapM fun item => do
        let .array [x,y] := item | none
        let x ← integer x
        let y ← integer y
        if x < 85 || x > 915 || y < 100 || y > 635 then none else some (Position.mk x y)
      let hidden ← (← j.getArray? "hidden").mapM Json.asBool?
      let pinned ← (← j.getArray? "pinned").mapM Json.asBool?
      let focus ← natField j "focus"
      let selection ← natField j "selection"
      let dragging ← j.getBool? "dragging"
      let animating ← j.getBool? "animating"
      let closed ← j.getBool? "closed"
      let revision ← natField j "revision"
      let accumulator ← natField j "accumulator"
      let address ← j.getString? "address"
      let cursor ← natField j "cursor"
      let anchor ← natField j "anchor"
      let editing ← j.getBool? "editing"
      let message ← j.getString? "message"
      if width < 16 || width > 4096 || height < 16 || height > 4096 ||
        positions.length != graph.people.size || hidden.length != graph.people.size || pinned.length != graph.people.size ||
        (graph.people.size > 0 && focus >= graph.people.size) ||
        (graph.people.size == 0 && focus != 0) || selection > graph.people.size ||
        accumulator >= 16 || (dragging && (selection == 0 || closed || editing)) ||
        address.length > 512 || cursor > address.length || anchor > address.length || message.length > 128 ||
        address.toList.any (fun c => c.toNat < 32 || c.toNat == 127) then none else do
        if selection > 0 && hidden[selection-1]! then none else
          some {
            graph := graph
            width := width
            height := height
            policy := policy
            positions := positions.toArray
            hidden := hidden.toArray
            pinned := pinned.toArray
            focus := focus
            selection := selection
            dragging := dragging
            animating := animating
            closed := closed
            revision := revision
            accumulator := accumulator
            address := address
            cursor := cursor
            anchor := anchor
            editing := editing
            message := message}

def response (m : Model) (commands : List String) (shader : Bool := false)
    (clipboardWrite : Option String := none) (clipboardRead : Bool := false) : String :=
  let scene := m.scene
  let selectedLabel := if m.selection == 0 then "" else ((m.graph.people[m.selection-1]?).map (·.label)).getD ""
  let selectedId := if m.selection == 0 then "" else ((m.graph.people[m.selection-1]?).map (·.id)).getD ""
  let fields := [
    ("abi",.string "lean-foafnaut-v1"),("demo",.string "foafnaut"),("model",.string m.encode),
    ("width",num m.width),("height",num m.height),("data",.array (scene.data.map num)),
    ("commands",.array (commands.map Json.string)),("animating",.bool m.animating),
    ("closed",.bool m.closed),("selection",num m.selection),("revision",num m.revision),
    ("dragging",.bool m.dragging),("selectedLabel",.string selectedLabel),
    ("selectedId",.string selectedId),("layout",m.layoutReport),
    ("facts",.object [("people",num m.graph.people.size),("links",num m.graph.links.size),
      ("visiblePeople",num (m.hidden.toList.filter (!·)).length),("focus",num m.focus),
      ("pinnedPeople",num (m.pinned.toList.filter (fun pinned => pinned)).length),
      ("ignoredKnows",num m.graph.ignoredKnows),("shapes",num scene.shapes.length)])]
  toStringCompact (.object (fields ++
    (if shader then [("wgsl",.string scene.wgsl)] else []) ++
    (clipboardWrite.toList.map fun text => ("clipboardWrite",Json.string text)) ++
    (if clipboardRead then [("clipboardRead",Json.bool true)] else [])))

/-- Geometry-directed readback references, including an actual painted font
cell when available. Values come from the same Lean CPU scene semantics;
this checks GPU agreement, not an independent rendering specification. -/
def Model.artifact (m : Model) (checked : Bool := false) : String := Id.run do
  let scene := m.scene
  let mut probes : List Point := [⟨0,0⟩]
  match (List.range m.graph.people.size).find? (fun i => !m.hidden[i]!) with
  | none => pure ()
  | some i =>
    let c := m.positions[i]!
    probes := probes ++ [point m c.x (c.y-15),point m (c.x-6) (c.y-39),
      point m c.x (c.y-34),point m (c.x-73) (c.y+8)]
  match m.graph.links.toList.find? (fun l => !m.hidden[l.source]! && !m.hidden[l.target]!) with
  | none => pure ()
  | some l =>
    let a := m.positions[l.source]!
    let b := m.positions[l.target]!
    probes := probes ++ [point m ((a.x+b.x)/2) ((a.y+b.y)/2)]
  let glyphPixel := scene.shapes.findSome? fun shape => match shape with
    | .glyph origin size rows _ =>
      if origin.x >= m.width || origin.y >= m.height || size == 0 then none else
        let rs := [rows.row0,rows.row1,rows.row2,rows.row3,rows.row4,rows.row5,rows.row6]
        ((List.range 35).find? fun n => rs[n/5]! / 2^(4-n%5) % 2 == 1).map fun n =>
          Point.mk (origin.x+(n%5)*size) (origin.y+(n/5)*size)
    | _ => none
  if let some p := glyphPixel then probes := probes ++ [p]
  let checks := probes.map fun p =>
    let x := min (m.width-1) p.x
    let y := min (m.height-1) p.y
    let c := scene.sample x y
    Json.object [("x",num x),("y",num y),("rgb",.array [num c.r,num c.g,num c.b])]
  return toStringCompact (.object [
    ("abi",.string "lean-graphics-v1"),("width",num m.width),("height",num m.height),
    ("shapeCount",num scene.shapes.length),("data",.array (scene.data.map num)),
    ("wgsl",.string scene.wgsl),("checks",.array checks),("layout",m.layoutReport checked)])

@[export foafnaut_initialize]
def initialResponse (rdf : String) (width height : UInt32) : String :=
  match FoafGraph.fromTurtle rdf none graphLimits with
  | .error e => toStringCompact (.object [("error",.string e)])
  | .ok graph =>
    if graph.people.isEmpty then "{\"error\":\"No FOAF people or resource-valued foaf:knows links found\"}"
    else response (initial graph width.toNat height.toNat) ["render","startClock"] true

@[export foafnaut_initialize_policy]
def initialPolicyResponse (rdf : String) (width height : UInt32) (policy : String) : String :=
  match L4Factoidal.UI.PolicyProtocol.readConfigText policy with
  | .error e => toStringCompact (.object [("error",.string e)])
  | .ok cfg => match FoafGraph.fromTurtle rdf none graphLimits with
    | .error e => toStringCompact (.object [("error",.string e)])
    | .ok graph =>
      if graph.people.isEmpty then "{\"error\":\"No FOAF people or resource-valued foaf:knows links found\"}"
      else response (initial graph width.toNat height.toNat cfg) ["render","startClock"] true

@[export foafnaut_svg]
def svgResponse (wire policy : String) : String :=
  match L4Factoidal.UI.PolicyProtocol.readConfigText policy with
  | .error e => toStringCompact (.object [("error",.string e)])
  | .ok expected =>
    match Model.decode wire with
    | none => "{\"error\":\"invalid FOAFNaut model\"}"
    | some m => if m.policy != expected then "{\"error\":\"model policy differs from application configuration\"}"
      else match L4Factoidal.UI.Presentation.inspect expected Model.footprints m with
      | none => toStringCompact (.object [("error",.string "layout policy rejected this scene"),("layout",m.layoutReport)])
      | some approved => match NativeSceneSVG.serialize approved.scene.scene with
        | .error e => toStringCompact (.object [("error",.string e)])
        | .ok svg => toStringCompact (.object [
          ("svg",.string svg),("width",num m.width),("height",num m.height),
          ("checked",.bool true),("layout",m.layoutReport true)])

@[export foafnaut_checked_picture]
def checkedPictureResponse (wire policy : String) : String :=
  match L4Factoidal.UI.PolicyProtocol.readConfigText policy with
  | .error e => toStringCompact (.object [("error",.string e)])
  | .ok expected =>
    match Model.decode wire with
    | none => "{\"error\":\"invalid FOAFNaut model\"}"
    | some m => if m.policy != expected then "{\"error\":\"model policy differs from application configuration\"}"
      else match L4Factoidal.UI.Presentation.inspect expected Model.footprints m with
      | none => toStringCompact (.object [("error",.string "layout policy rejected this scene"),("layout",m.layoutReport)])
      | some approved => approved.scene.artifact true
@[export foafnaut_transition]
def transition (wire : String) (kind : UInt32) (a b : Int32) : String :=
  match Model.decode wire with
  | none => "{\"error\":\"invalid FOAFNaut model\"}"
  | some m =>
    let result := transitionModel m kind.toNat a.toInt b.toInt
    response result.model result.commands false result.clipboardWrite result.clipboardRead
@[export foafnaut_insert_text]
def insertResponse (wire text : String) : String :=
  match Model.decode wire with
  | none => "{\"error\":\"invalid FOAFNaut model\"}"
  | some m =>
    if text.length > 65536 then
      let result := editorResult m {m with message:="Clipboard too large - limit 65536 Unicode scalars"}
      response result.model result.commands
    else if text.toList.any (fun c => c.toNat == 0) then
      "{\"error\":\"clipboard text contains NUL\"}"
    else let result := insertText m text
         response result.model result.commands
@[export foafnaut_snapshot]
def snapshot (wire : String) : String :=
  match Model.decode wire with
  | none => "{\"error\":\"invalid FOAFNaut model\"}"
  | some m => m.artifact
end NativeFoafNaut
