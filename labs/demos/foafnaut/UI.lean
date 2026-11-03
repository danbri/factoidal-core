import Graphics

namespace NativeUI
open NativeGraphics

inductive Selection where | none | circle | control
  deriving BEq, Repr
structure Model where
  width : Nat := 768
  height : Nat := 512
  circleX : Nat := 104
  circleY : Nat := 104
  controlX : Nat := 94
  controlY : Nat := 32
  selection : Selection := .none
  animating : Bool := false
  phase : Nat := 96
  closed : Bool := false
  revision : Nat := 0
  dragging : Bool := false
  deriving BEq, Repr
inductive Event where
  | resize (width height : Nat)
  | pointerDown (x y : Int)
  | pointerMove (x y : Int)
  | pointerUp
  | toggleAnimation
  | reset
  | tick (milliseconds : Nat)
  | close
  | noop
  deriving Repr
inductive Command where | render | startClock | stopClock | close
  deriving BEq, Repr

private def bound (lo hi n : Nat) : Nat := max lo (min hi n)
private def selectionCode : Selection → Nat
  | .none => 0 | .circle => 1 | .control => 2
private def select (n : Nat) : Selection :=
  if n == 1 then .circle else if n == 2 then .control else .none

def Model.encode (m : Model) : String :=
  String.intercalate "," ([m.width,m.height,m.circleX,m.circleY,m.controlX,m.controlY,
    selectionCode m.selection,if m.animating then 1 else 0,m.phase,
    if m.closed then 1 else 0,m.revision,if m.dragging then 1 else 0].map toString)

def Model.decode (wire : String) : Option Model := do
  if wire.length > 256 then none else do
    let nums ← (wire.splitOn ",").mapM String.toNat?
    match nums with
    | [w,h,cx,cy,bx,controlY,sel,anim,phase,closed,revision,drag] =>
      if w >= 16 && w <= 4096 && h >= 16 && h <= 4096 &&
         cx >= 55 && cx <= 329 && cy >= 55 && cy <= 201 &&
         bx <= 384 && controlY <= 256 && sel <= 2 && anim <= 1 && phase < 2000 && closed <= 1 && drag <= 1 && (drag == 0 || sel > 0) then
        some {
          width:=w, height:=h, circleX:=cx, circleY:=cy, controlX:=bx, controlY:=controlY
          selection:=select sel, animating:=anim == 1, phase, closed:=closed == 1, revision,dragging:=drag == 1 }
      else none
    | _ => none

private def logical (m : Model) (x y : Int) : Nat × Nat :=
  (min 384 (x.toNat*384/m.width), min 256 (y.toNat*256/m.height))
private def near (m : Model) (x y : Int) (cx cy radius : Nat) : Bool :=
  let dx := x - Int.ofNat (cx*m.width/384)
  let dy := y - Int.ofNat (cy*m.height/256)
  let pixelRadius := max 1 (min (radius*m.width/384) (radius*m.height/256))
  dx*dx + dy*dy <= Int.ofNat (pixelRadius*pixelRadius)

-- Pure event/state transition. Host timing, input, and GPU I/O are commands.
def update (m : Model) (event : Event) : Model × List Command := Id.run do
  if m.closed then return (m, [])
  let mut next := m
  let mut extra : List Command := []
  match event with
  | .noop => pure ()
  | .close => return ({m with closed:=true, revision:=m.revision+1}, [.close])
  | .resize w h => next := {m with width:=bound 16 4096 w, height:=bound 16 4096 h}
  | .pointerDown x y =>
    let selection := if near m x y m.controlX m.controlY 12 then Selection.control
      else if near m x y m.circleX m.circleY 55 then Selection.circle else Selection.none
    next := {m with selection,dragging:=selection != .none}
    if selection == .control && m.animating then
      next := {next with animating:=false}
      extra := [.stopClock]
  | .pointerMove x y =>
    let (x,y) := logical m x y
    if m.dragging then
      match m.selection with
      | .none => pure ()
      | .circle => next := {m with circleX:=bound 55 329 x, circleY:=bound 55 201 y}
      | .control => next := {m with controlX:=x, controlY:=y}
  | .pointerUp => next := {m with dragging:=false}
  | .toggleAnimation =>
    next := {m with animating:=!m.animating}
    extra := [if next.animating then .startClock else .stopClock]
  | .reset =>
    next := {width:=m.width,height:=m.height,revision:=m.revision}
    if m.animating then extra := [.stopClock]
  | .tick milliseconds =>
    if m.animating then
      let phase := (m.phase + min 1000 milliseconds) % 2000
      let height := 20 + (if phase <= 1000 then phase else 2000-phase)/8
      next := {m with phase, controlY:=height}
  if next == m then return (m, [])
  return ({next with revision:=m.revision+1}, .render :: extra)

def Model.scene (m : Model) : Scene :=
  let p := fun x y => Point.mk (x*m.width/384) (y*m.height/256)
  let scale := fun n => max 1 (min (n*m.width/384) (n*m.height/256))
  { width:=m.width, height:=m.height, background:=⟨18,24,39⟩, shapes:=[
    .circle (p m.circleX m.circleY) (scale 55)
      (if m.selection == .circle then ⟨109,245,211⟩ else ⟨53,211,167⟩),
    .rectangle (p 209 49) (p 110 110) ⟨92,141,250⟩,
    .quadratic (p 36 213) (p 184 122) (p 348 217) (scale 5) ⟨255,190,79⟩,
    .cubic (p 28 57) (p m.controlX m.controlY) (p 260 12) (p 355 30) (scale 4) ⟨239,110,184⟩,
    .circle (p m.controlX m.controlY) (scale 6)
      (if m.selection == .control then ⟨255,255,255⟩ else ⟨239,110,184⟩)] }

private def quote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n") ++ "\""
private def array (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"
private def Command.name : Command → String
  | .render => "render" | .startClock => "startClock" | .stopClock => "stopClock" | .close => "close"

def response (m : Model) (commands : List Command) (includeShader : Bool := false) : String :=
  "{\"abi\":\"lean-ui-v1\",\"model\":" ++ quote m.encode ++
  ",\"width\":" ++ toString m.width ++ ",\"height\":" ++ toString m.height ++
  ",\"data\":" ++ array (m.scene.data.map toString) ++
  ",\"commands\":" ++ array (commands.map fun c => quote c.name) ++
  ",\"animating\":" ++ toString m.animating ++ ",\"closed\":" ++ toString m.closed ++
  ",\"selection\":" ++ toString (selectionCode m.selection) ++
  ",\"revision\":" ++ toString m.revision ++
  ",\"dragging\":" ++ toString m.dragging ++
  (if includeShader then ",\"wgsl\":" ++ quote m.scene.wgsl else "") ++ "}"

@[export ui_initialize]
def initialResponse (width height : UInt32) : String :=
  response {width:=bound 16 4096 width.toNat, height:=bound 16 4096 height.toNat} [.render] true

def decodeEvent (kind : UInt32) (a b : Int32) : Event :=
  match kind.toNat with
  | 1 => .resize a.toInt.toNat b.toInt.toNat
  | 2 => .pointerDown a.toInt b.toInt
  | 3 => .pointerMove a.toInt b.toInt
  | 4 => .pointerUp
  | 5 => if a.toInt == 49 then .toggleAnimation else if a.toInt == 53 then .close else if a.toInt == 15 then .reset else .noop
  | 6 => .close
  | 7 => .tick a.toInt.toNat
  | _ => .noop

@[export ui_transition]
def transition (wire : String) (kind : UInt32) (a b : Int32) : String :=
  match Model.decode wire with
  | none => "{\"error\":\"invalid UI model\"}"
  | some m => let (next,commands) := update m (decodeEvent kind a b)
              response next commands

-- Kernel checks of selected state rules; event replay tests exercise compiled WASM.
example : (update ({} : Model) .noop).2 = [] := rfl
example : (update ({closed:=true} : Model) (.tick 16)).2 = [] := rfl
example : ({} : Model).scene.shapes.length = 5 := rfl
end NativeUI
