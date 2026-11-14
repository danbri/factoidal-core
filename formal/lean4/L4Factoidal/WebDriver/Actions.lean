/-
L4Factoidal.WebDriver.Actions: the Actions of WebDriver (W3C WebDriver §15) as data and
as a state machine.

A client (a WebDriver session's Perform Actions, or `test_driver.Actions` of the WPT
runner) describes input of the user as input sources (key, pointer, wheel, none), each
with a list of actions. The actions are run by ticks: tick `i` holds action `i` of every
source that has one, in the order of the sources; a tick ends before the next begins.
This module decides everything of that which is not the page:

- `parse`: the JSON of the request as typed sources, or `invalid argument` (§15.3
  "extract an action sequence");
- `ticks`: the sources' actions by tick (§15.4 "actions by tick");
- `State` and `step`: the input state (keys held, modifiers, each pointer's position and
  buttons held; §15.2) and what one action does to it, as low-level events (`Low`): a key
  goes down or up, a pointer moves, presses, releases or is cancelled, a wheel turns. A
  move outside the viewport is `move target out of bounds`; an element origin that is not
  there is `no such element`. The origin of an element is its in-view centre point
  (§12.1), `inViewCentre`;
- `performTicks`: the ticks run over any engine: each action's events are dispatched
  before the next action is read (so an element origin is resolved in the layout that the
  earlier events left), and nothing is dispatched after an error;
- `release`: Release Actions (§15.6): the keys and buttons still held go up, last first.

The engine that dispatches a `Low` (hit testing, focus, default actions, user
activation) is `WasmVM.Hosts.PageEvents`. Nothing here is reachable from page script:
these functions are called with a request of the host only (`WebScripts`, action
`actions`).

Proved: `ticks_length`, `ticks_getElem?` and `mem_tickAt` (tick `i` is exactly the
actions numbered `i`), `performTicks_append` (ticks are dispatched in order: the run of
`a ++ b` is the run of `b` after the run of `a`), `performTick_error` and
`performTicks_error` (after an error nothing more is dispatched), `step_pause`,
`step_keyUp_notHeld`, `step_pointerDown_held`, `step_pointerUp_notHeld` (the no-ops of
§15.4.3), `step_move_out_of_bounds` (a move outside the viewport is refused and changes
no state), `inViewCentre_inside` (the in-view centre of a box that meets the viewport is
in the viewport), `release_clears` (after Release Actions no key or button is held).
Tested: `#guard`s on requests of the WPT tests.
-/
import L4Factoidal.WebDriver.Keys
import L4Factoidal.WebDriver.Errors
import L4Factoidal.JSON.Parser

namespace L4Factoidal.WebDriver.Actions
open L4Factoidal.JSON

/-! ## Data -/

inductive PointerType where | mouse | pen | touch
  deriving DecidableEq, Repr, Inhabited

def PointerType.name : PointerType → String
  | .mouse => "mouse" | .pen => "pen" | .touch => "touch"

def PointerType.ofName : String → Option PointerType
  | "mouse" => some .mouse | "pen" => some .pen | "touch" => some .touch | _ => none

/-- The web element identifier (WebDriver §11): the key of an element reference object. -/
def elementKey : String := "element-6066-11e4-a52e-4f735466cecf"

/-- Where the coordinates of a move or a scroll count from. -/
inductive Origin where
  | viewport
  | pointer
  | element (ref : String)
  deriving DecidableEq, Repr, Inhabited

/-- The pointer properties of an action that has some (width, height, pressure,
tangentialPressure, tiltX, tiltY, twist, altitudeAngle, azimuthAngle): name and JSON
number, checked by `parse`. -/
abbrev Props := List (String × String)

inductive Action where
  | pause (duration : Nat)
  | keyDown (value : String)
  | keyUp (value : String)
  | pointerDown (button : Nat) (props : Props)
  | pointerUp (button : Nat)
  | pointerMove (duration : Nat) (origin : Origin) (x y : Int) (props : Props)
  | pointerCancel
  | scroll (duration : Nat) (origin : Origin) (x y dx dy : Int)
  deriving DecidableEq, Repr, Inhabited

/-- How long the action holds its tick open, in milliseconds (§15.4.1 "tick duration"). -/
def Action.duration : Action → Nat
  | .pause d => d
  | .pointerMove d _ _ _ _ => d
  | .scroll d _ _ _ _ _ => d
  | _ => 0

inductive Kind where
  | none
  | key
  | pointer (type : PointerType)
  | wheel
  deriving DecidableEq, Repr, Inhabited

structure Source where
  id : String
  kind : Kind
  actions : List Action
  deriving DecidableEq, Repr, Inhabited

/-! ## Reading the request (§15.3) -/

def bad (message : String) : Error := { code := .invalidArgument, message }

def digitsNat (ds : List Char) : Nat := ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0

/-- A JSON number with no exponent, in thousandths, truncated toward zero. -/
def milliOf (lexeme : String) : Option Int :=
  let cs := lexeme.toList
  let neg := cs.head? == some '-'
  let cs := if neg then cs.drop 1 else cs
  let whole := cs.takeWhile Char.isDigit
  let frac : Option (List Char) := match cs.dropWhile Char.isDigit with
    | [] => some []
    | '.' :: f => if !f.isEmpty && f.all Char.isDigit then some f else Option.none
    | _ => Option.none
  match whole.isEmpty, frac with
  | false, some f =>
    let m := digitsNat whole * 1000 + digitsNat ((f ++ ['0', '0', '0']).take 3)
    some (if neg then -(Int.ofNat m) else Int.ofNat m)
  | _, _ => Option.none

/-- A JSON number rounded to the nearest integer (a half away from zero). -/
def roundOf (lexeme : String) : Option Int :=
  (milliOf lexeme).map fun m =>
    if m < 0 then -(Int.ofNat ((m.natAbs + 500) / 1000)) else Int.ofNat ((m.natAbs + 500) / 1000)

def natOf : Json → Option Nat
  | .number n => n.toNat?
  | _ => Option.none

def intOf : Json → Option Int
  | .number n => roundOf n
  | _ => Option.none

/-- `duration`: absent is 0; else a non-negative integer. -/
def durationOf (o : Json) : Except Error Nat :=
  match o.field? "duration" with
  | Option.none => .ok 0
  | some j => match natOf j with
    | some n => .ok n
    | Option.none => .error (bad "duration is not a non-negative integer")

/-- A key value: one code point, or one code point followed by combining marks, joiners
or variation selectors (a grapheme cluster of the common kinds). -/
def isKeyValue (v : String) : Bool :=
  match v.toList with
  | [] => false
  | _ :: rest => rest.all fun c =>
    let n := c.toNat
    (0x300 ≤ n && n ≤ 0x36F) || (0x1AB0 ≤ n && n ≤ 0x1AFF) || (0x1DC0 ≤ n && n ≤ 0x1DFF) ||
    (0x20D0 ≤ n && n ≤ 0x20FF) || (0xFE00 ≤ n && n ≤ 0xFE0F) || (0xFE20 ≤ n && n ≤ 0xFE2F) ||
    n == 0x200D || (0x1F3FB ≤ n && n ≤ 0x1F3FF) || (0xE0100 ≤ n && n ≤ 0xE01EF)

/-- The pointer properties and their ranges in thousandths (§15.4.3 "process pointer
parameters"); `whole`: an integer. -/
def propRanges : List (String × Int × Int × Bool) := [
  ("width", 0, 1000000000, false), ("height", 0, 1000000000, false),
  ("pressure", 0, 1000, false), ("tangentialPressure", -1000, 1000, false),
  ("tiltX", -90000, 90000, true), ("tiltY", -90000, 90000, true), ("twist", 0, 359000, true),
  ("altitudeAngle", 0, 1571, false), ("azimuthAngle", 0, 6284, false)]

def propsOf (o : Json) : Except Error Props :=
  propRanges.foldlM (init := []) fun acc (name, lo, hi, whole) =>
    match o.field? name with
    | Option.none => .ok acc
    | some (.number n) =>
      match milliOf n with
      | some m =>
        if lo ≤ m && m ≤ hi && (!whole || m % 1000 == 0) then .ok (acc ++ [(name, n)])
        else .error (bad (name ++ " is out of range"))
      | Option.none => .error (bad (name ++ " is not a number"))
    | some _ => .error (bad (name ++ " is not a number"))

def originOf (o : Json) (pointerOk : Bool) : Except Error Origin :=
  match o.field? "origin" with
  | Option.none => .ok .viewport
  | some (.string "viewport") => .ok .viewport
  | some (.string "pointer") => if pointerOk then .ok .pointer else .error (bad "origin pointer is for pointer moves only")
  | some j => match j.field? elementKey with
    | some (.string ref) => .ok (.element ref)
    | _ => .error (bad "origin is not viewport, pointer or an element")

def coordOf (o : Json) (name : String) : Except Error Int :=
  match (o.field? name).bind intOf with
  | some i => .ok i
  | Option.none => .error (bad (name ++ " is not a number"))

def typeOf (o : Json) : Except Error String :=
  match o.field? "type" with
  | some (.string t) => .ok t
  | _ => .error (bad "an action item needs a type")

def buttonOf (o : Json) : Except Error Nat :=
  match (o.field? "button").bind natOf with
  | some b => .ok b
  | Option.none => .error (bad "button is not a non-negative integer")

/-- One action item of a source of `kind` (§15.3 "process a null action", "process a key
action", "process a pointer action", "process a wheel action"). -/
def actionOf (kind : Kind) (o : Json) : Except Error Action := do
  let t ← typeOf o
  if t == "pause" then return .pause (← durationOf o)
  match kind with
  | .none => throw (bad "a none source only pauses")
  | .key =>
    if t != "keyDown" && t != "keyUp" then throw (bad ("unknown key action " ++ t))
    match o.field? "value" with
    | some (.string v) =>
      if !isKeyValue v then throw (bad "value is not a single key")
      return if t == "keyDown" then .keyDown v else .keyUp v
    | _ => throw (bad "value is not a string")
  | .pointer _ =>
    if t == "pointerDown" then return .pointerDown (← buttonOf o) (← propsOf o)
    else if t == "pointerUp" then return .pointerUp (← buttonOf o)
    else if t == "pointerCancel" then return .pointerCancel
    else if t == "pointerMove" then
      return .pointerMove (← durationOf o) (← originOf o true) (← coordOf o "x") (← coordOf o "y") (← propsOf o)
    else throw (bad ("unknown pointer action " ++ t))
  | .wheel =>
    if t != "scroll" then throw (bad ("unknown wheel action " ++ t))
    return .scroll (← durationOf o) (← originOf o false) (← coordOf o "x") (← coordOf o "y")
      (← coordOf o "deltaX") (← coordOf o "deltaY")

/-- The kind of a source: its `type`, and for a pointer its `parameters.pointerType`
(mouse when absent). -/
def kindOf (o : Json) : Except Error Kind :=
  match o.field? "type" with
  | some (.string "none") => .ok .none
  | some (.string "key") => .ok .key
  | some (.string "wheel") => .ok .wheel
  | some (.string "pointer") =>
    match o.field? "parameters" with
    | Option.none => .ok (.pointer .mouse)
    | some (.object fs) =>
      match (Json.object fs).field? "pointerType" with
      | Option.none => .ok (.pointer .mouse)
      | some (.string p) => match PointerType.ofName p with
        | some t => .ok (.pointer t)
        | Option.none => .error (bad "pointerType is not mouse, pen or touch")
      | some _ => .error (bad "pointerType is not a string")
    | some _ => .error (bad "parameters is not an object")
  | _ => .error (bad "type is not key, pointer, wheel or none")

def sourceOf (o : Json) : Except Error Source := do
  let kind ← kindOf o
  let id ← match o.field? "id" with
    | some (.string s) => pure s
    | _ => throw (bad "id is not a string")
  let items ← match o.field? "actions" with
    | some (.array xs) => pure xs
    | _ => throw (bad "actions is not an array")
  return { id, kind, actions := ← items.mapM (actionOf kind) }

/-- The sources of a Perform Actions request (`{"actions": [...]}`), §15.3. Two sources
with one id must be of one kind. -/
def parse (request : Json) : Except Error (List Source) := do
  let items ← match request.field? "actions" with
    | some (.array xs) => pure xs
    | _ => throw (bad "actions is not an array")
  let sources ← items.mapM sourceOf
  if sources.any fun s => sources.any fun t => s.id == t.id && s.kind != t.kind then
    throw (bad "an id is used for two kinds of source")
  return sources

/-! ## Ticks (§15.4 "actions by tick") -/

/-- One tick: the number of each source that has an action in it, and the action. -/
abbrev Tick := List (Nat × Action)

def tickCount (ss : List Source) : Nat := ss.foldl (fun n s => max n s.actions.length) 0

def tickAt (ss : List Source) (i : Nat) : Tick :=
  ss.zipIdx.filterMap fun (s, k) => (s.actions[i]?).map fun a => (k, a)

def ticks (ss : List Source) : List Tick := (List.range (tickCount ss)).map (tickAt ss)

/-- The tick's duration: the longest of its actions' (§15.4.1). -/
def tickDuration (t : Tick) : Nat := t.foldl (fun n ka => max n ka.2.duration) 0

/-! ## Input state (§15.2) -/

/-- The modifiers held. -/
structure Mods where
  shift : Bool := false
  ctrl : Bool := false
  alt : Bool := false
  cmd : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- One pointer: where it is in the viewport (CSS pixels) and the buttons held. -/
structure Pointer where
  type : PointerType := .mouse
  pointerId : Nat := 1
  x : Int := 0
  y : Int := 0
  pressed : List Nat := []
  deriving DecidableEq, Repr, Inhabited

/-- The input state: every source's kind by id, the key values held with the modifiers,
the pointers by source id, and the actions that undo what is held, last first (the
"input cancel list"). -/
structure State where
  kinds : List (String × Kind) := []
  keys : List String := []
  mods : Mods := {}
  pointers : List (String × Pointer) := []
  cancel : List (String × Kind × Action) := []
  deriving DecidableEq, Repr, Inhabited

def State.pointer (st : State) (id : String) (type : PointerType := .mouse) : Pointer :=
  match st.pointers.find? (·.1 == id) with
  | some p => p.2
  -- the mouse is pointer 1; each other pointer has a number of its own
  | Option.none => { type, pointerId := if type == .mouse then 1 else st.pointers.length + 2 }

def State.setPointer (st : State) (id : String) (p : Pointer) : State :=
  { st with pointers := if st.pointers.any (·.1 == id) then st.pointers.map (fun q => if q.1 == id then (id, p) else q)
                        else st.pointers ++ [(id, p)] }

/-- The sources of a request join the state; an id that the state knows with another kind
is `invalid argument` (§15.3). -/
def State.admit (st : State) (ss : List Source) : Except Error State :=
  ss.foldlM (init := st) fun st s =>
    match st.kinds.find? (·.1 == s.id) with
    | some (_, k) => if k == s.kind then .ok st else .error (bad ("source " ++ s.id ++ " has another type"))
    | Option.none => .ok { st with kinds := st.kinds ++ [(s.id, s.kind)] }

/-- The `buttons` bit of a WebDriver button (UI Events `MouseEvent.buttons`): 0 primary is
1, 1 auxiliary is 4, 2 secondary is 2, then 8, 16 and so on. -/
def buttonBit : Nat → Nat
  | 0 => 1 | 1 => 4 | 2 => 2 | n => 2 ^ n

def buttonsOf (pressed : List Nat) : Nat := (pressed.eraseDups.map buttonBit).foldl (· + ·) 0

/-! ## Low-level events -/

inductive Phase where | down | up | move | cancel
  deriving DecidableEq, Repr, Inhabited

def Phase.name : Phase → String
  | .down => "down" | .up => "up" | .move => "move" | .cancel => "cancel"

/-- What the engine is given to dispatch. -/
inductive Low where
  /-- A key goes down (`down`) or up, with the modifiers held after it; `again`: the key
  was already down (auto-repeat). -/
  | key (down : Bool) (data : Keys.KeyData) (mods : Mods) (again : Bool)
  /-- A pointer event at a viewport point: `button` is the button that changed (-1 for a
  move), `buttons` those held after it. -/
  | pointer (phase : Phase) (type : PointerType) (pointerId : Nat) (x y : Int) (button : Int)
      (buttons : Nat) (mods : Mods) (props : Props)
  /-- A wheel turned at a viewport point. -/
  | wheel (x y dx dy : Int) (mods : Mods)
  deriving DecidableEq, Repr, Inhabited

/-- The key data of a key value: a single code point by `Keys.ofRaw`, a cluster as
itself. -/
def keyDataOf (value : String) : Keys.KeyData :=
  match value.toList with
  | [c] => Keys.ofRaw c
  | _ => { key := value, code := "" }

def Mods.set (m : Mods) (key : String) (on : Bool) : Mods :=
  if key == "Shift" then { m with shift := on }
  else if key == "Control" then { m with ctrl := on }
  else if key == "Alt" then { m with alt := on }
  else if key == "Meta" then { m with cmd := on }
  else m

/-- The in-view centre point of a box `x y w h` in a viewport `vw` by `vh` (WebDriver
§12.1): the centre of the part of the box that is in the viewport. -/
def inViewCentre (vw vh : Nat) (x y w h : Int) : Int × Int :=
  let left := max 0 (min x (x + w))
  let right := min (vw : Int) (max x (x + w))
  let top := max 0 (min y (y + h))
  let bottom := min (vh : Int) (max y (y + h))
  ((left + right) / 2, (top + bottom) / 2)

/-- What a step needs of the page: the viewport, and the in-view centre of an element
reference in the current layout (`none`: no such element). -/
structure Env where
  width : Nat
  height : Nat
  centre : String → Option (Int × Int)

def outOfBounds (env : Env) (x y : Int) : Bool := x < 0 || y < 0 || x > env.width || y > env.height

/-- The viewport point of coordinates from an origin. -/
def pointOf (env : Env) (p : Pointer) (origin : Origin) (x y : Int) : Except Error (Int × Int) :=
  let at_ : Except Error (Int × Int) := match origin with
    | .viewport => .ok (x, y)
    | .pointer => .ok (p.x + x, p.y + y)
    | .element ref => match env.centre ref with
      | some (cx, cy) => .ok (cx + x, cy + y)
      | Option.none => .error { code := .noSuchElement, message := "the origin element is not in the document" }
  match at_ with
  | .ok (tx, ty) =>
    if outOfBounds env tx ty then .error { code := .moveTargetOutOfBounds, message := s!"({tx}, {ty}) is outside the viewport" }
    else .ok (tx, ty)
  | .error e => .error e

/-- One action of the source `id` (§15.4.2 to §15.4.4): the state after it and the events
to dispatch. -/
def step (env : Env) (st : State) (id : String) (kind : Kind) (a : Action) : Except Error (State × List Low) :=
  let type := match kind with | .pointer t => t | _ => PointerType.mouse
  match a with
  | .pause _ => .ok (st, [])
  | .keyDown v =>
    let data := keyDataOf v
    let again := st.keys.contains data.key
    let mods := st.mods.set data.key true
    .ok ({ st with keys := if again then st.keys else st.keys ++ [data.key], mods,
                   cancel := (id, kind, Action.keyUp v) :: st.cancel }, [.key true data mods again])
  | .keyUp v =>
    let data := keyDataOf v
    if !st.keys.contains data.key then .ok (st, []) else
    let mods := st.mods.set data.key false
    .ok ({ st with keys := st.keys.filter (· != data.key), mods }, [.key false data mods false])
  | .pointerDown b props =>
    let p := st.pointer id type
    if p.pressed.contains b then .ok (st, []) else
    let p := { p with pressed := p.pressed ++ [b] }
    .ok ({ (st.setPointer id p) with cancel := (id, kind, Action.pointerUp b) :: st.cancel },
      [.pointer .down p.type p.pointerId p.x p.y b (buttonsOf p.pressed) st.mods props])
  | .pointerUp b =>
    let p := st.pointer id type
    if !p.pressed.contains b then .ok (st, []) else
    let p := { p with pressed := p.pressed.filter (· != b) }
    .ok (st.setPointer id p, [.pointer .up p.type p.pointerId p.x p.y b (buttonsOf p.pressed) st.mods []])
  | .pointerMove _ origin x y props =>
    let p := st.pointer id type
    match pointOf env p origin x y with
    | .error e => .error e
    | .ok (tx, ty) =>
      let p := { p with x := tx, y := ty }
      .ok (st.setPointer id p, [.pointer .move p.type p.pointerId tx ty (-1) (buttonsOf p.pressed) st.mods props])
  | .pointerCancel =>
    let p := st.pointer id type
    let p' := { p with pressed := [] }
    .ok (st.setPointer id p', [.pointer .cancel p.type p.pointerId p.x p.y (-1) 0 st.mods []])
  | .scroll _ origin x y dx dy =>
    match pointOf env {} origin x y with
    | .error e => .error e
    | .ok (tx, ty) => .ok (st, [.wheel tx ty dx dy st.mods])

/-! ## Running ticks over an engine -/

/-- A run: the engine's state, the input state, and the error that stopped it. -/
structure Run (σ : Type) where
  engine : σ
  input : State := {}
  error : Option Error := none

/-- What a run needs of the engine: the page's `Env` now, how to dispatch one low-level
event, and how to let time pass. -/
structure Driver (σ : Type) where
  env : σ → Env
  dispatch : σ → Low → σ
  wait : σ → Nat → σ

variable {σ : Type}

/-- One action of a tick: stepped in the page as it is now, its events dispatched. -/
def performAction (d : Driver σ) (kinds : Nat → String × Kind) (r : Run σ) (ka : Nat × Action) : Run σ :=
  if r.error.isSome then r else
  match step (d.env r.engine) r.input (kinds ka.1).1 (kinds ka.1).2 ka.2 with
  | .ok (st, lows) => { r with input := st, engine := lows.foldl d.dispatch r.engine }
  | .error e => { r with error := some e }

/-- One tick: its actions in source order, then the tick's duration passes. -/
def performTick (d : Driver σ) (kinds : Nat → String × Kind) (r : Run σ) (t : Tick) : Run σ :=
  if r.error.isSome then r else
  let r := t.foldl (performAction d kinds) r
  if r.error.isSome then r else { r with engine := d.wait r.engine (tickDuration t) }

def performTicks (d : Driver σ) (kinds : Nat → String × Kind) (r : Run σ) (ts : List Tick) : Run σ :=
  ts.foldl (performTick d kinds) r

/-- Perform Actions (§15.7): the sources join the input state, then their ticks run. -/
def perform (d : Driver σ) (r : Run σ) (ss : List Source) : Run σ :=
  if r.error.isSome then r else
  match r.input.admit ss with
  | .error e => { r with error := some e }
  | .ok st =>
    let kinds := fun k => match ss[k]? with
      | some s => (s.id, s.kind)
      | Option.none => ("", Kind.none)
    performTicks d kinds { r with input := st } (ticks ss)

/-- The events of Release Actions (§15.6): each held key and button goes up, the last
pressed first. -/
def releaseLows (st : State) : State × List Low :=
  st.cancel.foldl (init := (st, [])) fun (st, lows) (id, kind, a) =>
    match step { width := 0, height := 0, centre := fun _ => Option.none } st id kind a with
    | .ok (st', ls) => (st', lows ++ ls)
    | .error _ => (st, lows)

/-- Release Actions: the events are dispatched, and the input state is new. -/
def release (d : Driver σ) (r : Run σ) : Run σ :=
  let (_, lows) := releaseLows r.input
  { engine := lows.foldl d.dispatch r.engine, input := {}, error := r.error }

/-! ## Theorems -/

/-- Tick count. Says: there are as many ticks as the longest source has actions. Does not
say: that every tick has an action of every source (a shorter source is absent later). -/
theorem ticks_length (ss : List Source) : (ticks ss).length = tickCount ss := by
  simp [ticks]

/-- Tick `i`. Says: the tick at position `i` is `tickAt ss i`: built from the actions
numbered `i` and from nothing else. Does not say: what dispatching it does. -/
theorem ticks_getElem? (ss : List Source) (i : Nat) (h : i < tickCount ss) :
    (ticks ss)[i]? = some (tickAt ss i) := by
  simp [ticks, h]

/-- Membership. Says: action `a` of source number `k` is in tick `i` exactly when it is
that source's action number `i`: no action is dropped, moved to another tick or given to
another source. Does not say: the order inside the tick (source order, by the definition
of `tickAt` as a filter of the sources in order). -/
theorem mem_tickAt (ss : List Source) (i k : Nat) (a : Action) :
    (k, a) ∈ tickAt ss i ↔ ∃ s, ss[k]? = some s ∧ s.actions[i]? = some a := by
  simp only [tickAt, List.mem_filterMap, Option.map_eq_some_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨s, k'⟩, hmem, a', ha, hk, haa⟩
    refine ⟨s, ?_, ?_⟩
    · have := List.mem_zipIdx_iff_getElem?.mp hmem
      simpa [← hk] using this
    · simpa [← haa] using ha
  · rintro ⟨s, hs, ha⟩
    exact ⟨(s, k), List.mem_zipIdx_iff_getElem?.mpr (by simpa using hs), a, ha, rfl, rfl⟩

/-- Tick order. Says: running the ticks `a ++ b` is running `b` from the state that
running `a` left: every event of an earlier tick is dispatched, and its tick's duration
has passed, before the first action of a later tick is read. Does not say: anything about
what the engine's `dispatch` does with an event. -/
theorem performTicks_append (d : Driver σ) (kinds : Nat → String × Kind) (r : Run σ) (a b : List Tick) :
    performTicks d kinds r (a ++ b) = performTicks d kinds (performTicks d kinds r a) b := by
  simp [performTicks, List.foldl_append]

/-- Error stops a tick. Says: a run that has an error is not changed by a tick: no event
is dispatched and no time passes. Does not say: that the events before the error are
undone (they are not; WebDriver does not ask for it). -/
theorem performTick_error (d : Driver σ) (kinds : Nat → String × Kind) (r : Run σ) (t : Tick)
    (h : r.error.isSome = true) : performTick d kinds r t = r := by
  simp [performTick, h]

/-- Error stops the run. Says: after an error no later tick dispatches anything. Does not
say: which action raised it. -/
theorem performTicks_error (d : Driver σ) (kinds : Nat → String × Kind) (r : Run σ) (ts : List Tick)
    (h : r.error.isSome = true) : performTicks d kinds r ts = r := by
  induction ts generalizing r with
  | nil => rfl
  | cons t ts ih =>
    simp only [performTicks, List.foldl_cons]
    rw [performTick_error d kinds r t h]
    exact ih r h

/-- Pause. Says: a pause changes no input state and dispatches nothing. Does not say:
that no time passes (its duration is the tick's). -/
theorem step_pause (env : Env) (st : State) (id : String) (kind : Kind) (n : Nat) :
    step env st id kind (.pause n) = .ok (st, []) := rfl

/-- Key up, not held. Says: releasing a key that is not held dispatches nothing and
changes nothing (§15.4.2 "dispatch a keyUp action", step 4). Does not say: anything of a
key that is held. -/
theorem step_keyUp_notHeld (env : Env) (st : State) (id : String) (kind : Kind) (v : String)
    (h : st.keys.contains (keyDataOf v).key = false) :
    step env st id kind (.keyUp v) = .ok (st, []) := by
  have h' : ¬ (keyDataOf v).key ∈ st.keys := by simpa using h
  simp [step, h']

/-- Button down, held. Says: pressing a button that the pointer already holds dispatches
nothing and changes nothing (§15.4.3 "dispatch a pointerDown action", step 3). Does not
say: anything of another button. -/
theorem step_pointerDown_held (env : Env) (st : State) (id : String) (t : PointerType) (b : Nat) (props : Props)
    (h : (st.pointer id t).pressed.contains b = true) :
    step env st id (.pointer t) (.pointerDown b props) = .ok (st, []) := by
  have h' : b ∈ (st.pointer id t).pressed := by simpa using h
  simp [step, h']

/-- Button up, not held. Says: releasing a button that the pointer does not hold
dispatches nothing and changes nothing (§15.4.3 "dispatch a pointerUp action", step 3).
Does not say: anything of a held button. -/
theorem step_pointerUp_notHeld (env : Env) (st : State) (id : String) (t : PointerType) (b : Nat)
    (h : (st.pointer id t).pressed.contains b = false) :
    step env st id (.pointer t) (.pointerUp b) = .ok (st, []) := by
  have h' : ¬ b ∈ (st.pointer id t).pressed := by simpa using h
  simp [step, h']

/-- Bounds. Says: a pointer move whose target point is outside the viewport is refused
with `move target out of bounds`: no event, no change of the pointer's position. Does
not say: that a point inside the viewport is over any element. -/
theorem step_move_out_of_bounds (env : Env) (st : State) (id : String) (t : PointerType)
    (d : Nat) (x y : Int) (props : Props) (h : outOfBounds env x y = true) :
    ∃ e, step env st id (.pointer t) (.pointerMove d .viewport x y props) = .error e ∧
      e.code = .moveTargetOutOfBounds := by
  simp [step, pointOf, h]

/-- In view. Says: when a box meets the viewport (its clamped edges are in order), its
in-view centre point is inside the viewport, so a move to an element that is in view
with no offset is never out of bounds. Does not say: that the point is not covered by
another element. -/
theorem inViewCentre_inside (vw vh : Nat) (x y w h : Int)
    (hx : max 0 (min x (x + w)) ≤ min (vw : Int) (max x (x + w)))
    (hy : max 0 (min y (y + h)) ≤ min (vh : Int) (max y (y + h))) :
    0 ≤ (inViewCentre vw vh x y w h).1 ∧ (inViewCentre vw vh x y w h).1 ≤ vw ∧
    0 ≤ (inViewCentre vw vh x y w h).2 ∧ (inViewCentre vw vh x y w h).2 ≤ vh := by
  simp only [inViewCentre]
  omega

/-- Release. Says: after Release Actions the input state holds no key, no modifier and no
pointer button: a later session or test starts clean. Does not say: which events were
dispatched (`releaseLows`). -/
theorem release_clears (d : Driver σ) (r : Run σ) :
    (release d r).input.keys = [] ∧ (release d r).input.mods = {} ∧ (release d r).input.pointers = [] := by
  simp [release]

/-! ## Tests -/

private def req (s : String) : Json := (parseJson s).toOption.getD .null
private def envOf (w h : Nat) : Env := { width := w, height := h, centre := fun r => if r == "e1" then some (50, 60) else Option.none }
private def lowsOf (s : String) : String × List Low :=
  match parse (req s) with
  | .error e => (e.code.name, [])
  | .ok ss =>
    let d : Driver (List Low) := { env := fun _ => envOf 800 600, dispatch := fun acc l => acc ++ [l], wait := fun acc _ => acc }
    let r := perform d { engine := [] } ss
    match r.error with
    | some e => (e.code.name, r.engine)
    | Option.none => ("", r.engine)

#guard milliOf "12" == some 12000 && milliOf "-0.5" == some (-500) && milliOf "1.2345" == some 1234 && milliOf "1e3" == Option.none
#guard roundOf "2.5" == some 3 && roundOf "-2.5" == some (-3) && roundOf "2.4" == some 2 && roundOf "7" == some 7
#guard buttonsOf [0] == 1 && buttonsOf [0, 2] == 3 && buttonsOf [1] == 4 && buttonsOf [] == 0
#guard inViewCentre 800 600 10 20 100 50 == (60, 45)
#guard inViewCentre 800 600 (-50) 20 100 50 == (25, 45)

-- a key press and release with Shift held between (key_events tests of perform_actions)
#guard lowsOf "{\"actions\":[{\"type\":\"key\",\"id\":\"k\",\"actions\":[{\"type\":\"keyDown\",\"value\":\"\\uE008\"},{\"type\":\"keyDown\",\"value\":\"a\"},{\"type\":\"keyUp\",\"value\":\"a\"},{\"type\":\"keyUp\",\"value\":\"\\uE008\"}]}]}" ==
  ("", [.key true { key := "Shift", code := "ShiftLeft", location := 1, keyCode := 16 } { shift := true } false,
       .key true { key := "a", code := "KeyA", keyCode := 65 } { shift := true } false,
       .key false { key := "a", code := "KeyA", keyCode := 65 } { shift := true } false,
       .key false { key := "Shift", code := "ShiftLeft", location := 1, keyCode := 16 } {} false])
-- a click at an element: move to its in-view centre, press, release
#guard lowsOf "{\"actions\":[{\"type\":\"pointer\",\"id\":\"m\",\"parameters\":{\"pointerType\":\"mouse\"},\"actions\":[{\"type\":\"pointerMove\",\"x\":0,\"y\":0,\"origin\":{\"element-6066-11e4-a52e-4f735466cecf\":\"e1\"}},{\"type\":\"pointerDown\",\"button\":0},{\"type\":\"pointerUp\",\"button\":0}]}]}" ==
  ("", [.pointer .move .mouse 1 50 60 (-1) 0 {} [], .pointer .down .mouse 1 50 60 0 1 {} [],
       .pointer .up .mouse 1 50 60 0 0 {} []])
-- two sources: tick by tick, in source order
#guard ((lowsOf "{\"actions\":[{\"type\":\"key\",\"id\":\"k\",\"actions\":[{\"type\":\"keyDown\",\"value\":\"\\uE009\"},{\"type\":\"pause\"},{\"type\":\"keyUp\",\"value\":\"\\uE009\"}]},{\"type\":\"pointer\",\"id\":\"m\",\"actions\":[{\"type\":\"pointerMove\",\"x\":5,\"y\":6},{\"type\":\"pointerDown\",\"button\":0},{\"type\":\"pointerUp\",\"button\":0}]}]}").2.map fun
    | .key d k _ _ => (if d then "down " else "up ") ++ k.key
    | .pointer p _ _ _ _ _ _ m _ => p.name ++ (if m.ctrl then " ctrl" else "")
    | .wheel .. => "wheel") ==
  ["down Control", "move ctrl", "down ctrl", "up Control", "up"]
-- refusals
#guard lowsOf "{\"actions\":[{\"type\":\"pointer\",\"id\":\"m\",\"actions\":[{\"type\":\"pointerMove\",\"x\":801,\"y\":0}]}]}" == ("move target out of bounds", [])
#guard lowsOf "{\"actions\":[{\"type\":\"pointer\",\"id\":\"m\",\"actions\":[{\"type\":\"pointerMove\",\"x\":0,\"y\":0,\"origin\":{\"element-6066-11e4-a52e-4f735466cecf\":\"gone\"}}]}]}" == ("no such element", [])
#guard lowsOf "{\"actions\":[{\"type\":\"key\",\"id\":\"k\",\"actions\":[{\"type\":\"keyDown\",\"value\":\"ab\"}]}]}" == ("invalid argument", [])
#guard lowsOf "{\"actions\":[{\"type\":\"wheel\",\"id\":\"w\",\"actions\":[{\"type\":\"scroll\",\"x\":0,\"y\":0,\"deltaX\":5,\"deltaY\":10,\"origin\":\"pointer\"}]}]}" == ("invalid argument", [])
#guard lowsOf "{\"actions\":[{\"type\":\"pointer\",\"id\":\"m\",\"parameters\":{\"pointerType\":\"finger\"},\"actions\":[]}]}" == ("invalid argument", [])
#guard lowsOf "{\"actions\":[{\"type\":\"none\",\"id\":\"n\",\"actions\":[{\"type\":\"keyDown\",\"value\":\"a\"}]}]}" == ("invalid argument", [])
#guard lowsOf "{\"actions\":{}}" == ("invalid argument", [])
#guard lowsOf "{\"actions\":[{\"type\":\"wheel\",\"id\":\"w\",\"actions\":[{\"type\":\"scroll\",\"x\":10,\"y\":20,\"deltaX\":5,\"deltaY\":-10}]}]}" ==
  ("", [.wheel 10 20 5 (-10) {}])
-- a pen with properties; a property out of range
#guard (lowsOf "{\"actions\":[{\"type\":\"pointer\",\"id\":\"p\",\"parameters\":{\"pointerType\":\"pen\"},\"actions\":[{\"type\":\"pointerMove\",\"x\":1,\"y\":2,\"pressure\":0.5,\"tiltX\":-30}]}]}") ==
  ("", [.pointer .move .pen 2 1 2 (-1) 0 {} [("pressure", "0.5"), ("tiltX", "-30")]])
#guard lowsOf "{\"actions\":[{\"type\":\"pointer\",\"id\":\"p\",\"actions\":[{\"type\":\"pointerDown\",\"button\":0,\"pressure\":1.5}]}]}" == ("invalid argument", [])
-- Release Actions: Shift and the primary button go up, last pressed first
private def heldState : State :=
  { keys := ["Shift"], mods := { shift := true }, pointers := [("m", { pressed := [0], x := 3, y := 4 })],
    cancel := [("m", .pointer .mouse, .pointerUp 0), ("k", .key, .keyUp "\uE008")] }
#guard (releaseLows heldState).2.map (fun
    | .key d k _ _ => (if d then "down " else "up ") ++ k.key
    | .pointer p .. => p.name
    | .wheel .. => "wheel") == ["up", "up Shift"]

end L4Factoidal.WebDriver.Actions
