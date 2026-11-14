/-
L4Factoidal.WasmVM.Hosts.PageEvents: the event code of a page session over any script
engine (record: docs/designissues/2026-11-08-lean-js-engine.md, section 11).

`Hosts.Page` holds the session code for QuickJS-NG in WasmVM, as a program of asks
(`Page.Prog`). The same steps for an engine that Lean runs directly (BubblePopJS, the
JavaScript engine written in Lean, `Hosts.LeanJS`) are here, over an `Engine`: the four things a page needs of a
script engine (dispatch an event of the user agent, run a callback, forget a callback,
run the microtask checkpoint). Everything else is the page's `Host` (`Hosts.Page.Host`:
the DOM arena and its commands, the event loop, the listeners, the script clock, the
pointer) and is decided here, with the same functions of `L4Factoidal.EventLoop` and
the same order as `Hosts.Page`:

- a task's steps end (`EventLoop.State.finish`) before its microtask checkpoint
  (HTML §8.1.7.3 steps 6 and 7);
- a timeout's callback is forgotten after it runs, an interval's is kept;
- at most one animation frame batch per advance, at the last frame time it reaches
  (`EventLoop.frameSlot`), through `Page.DriverM`, whose theorems
  (`DriverM.ofDriver_advanceGo`) say it is `EventLoop.Driver.advanceGo`;
- pointer input as Pointer Events 3 and UI Events: a press, a release with its click at
  the common ancestor, at most one move a frame;
- the low-level events of WebDriver's actions (`WebDriver.Actions.Low`: a key, a pointer
  at a viewport point, a wheel) as trusted DOM events: the target of a pointer event is
  the topmost element of the layout's hit test at the point (measure op 35, the answer
  `document.elementFromPoint` gets), with its boundary events (`WebDriver.Input.boundary`),
  the click of a release and its count; every default action of a key or of a press is
  run through `WebDriver.Input.afterCancelable`, so a cancelled event has none
  (`Input.afterCancelable_cancelled`). Only a host's action reaches these functions
  (`WebScripts`, action `actions`): no import of page script calls them.
-/
import L4Factoidal.WasmVM.Hosts.Page
import L4Factoidal.WebDriver.Input

namespace L4Factoidal.WasmVM.Hosts.PageEvents
open L4Factoidal.WasmVM.Hosts.Page
open L4Factoidal.WebDriver

/-- What the event code needs of a script engine's session `σ`. -/
structure Engine (σ : Type) where
  host : σ → Host
  setHost : σ → Host → σ
  /-- Dispatch an event of the user agent at a target, with no microtask checkpoint: the
  session, and whether a listener canceled it. -/
  dispatchOnly : σ → Nat → String → σ × Bool
  /-- Run one callback the page registered: a timer (target -1) or an animation frame
  callback (target -2, `arg` the frame time). -/
  callbackOnly : σ → Nat → Int → Nat → σ
  /-- Forget a callback (a timeout that has run). -/
  release : σ → Nat → σ
  /-- The microtask checkpoint of the engine. -/
  runJobs : σ → σ
  lastFrame : σ → Option Nat
  setLastFrame : σ → Option Nat → σ

namespace Engine
variable {σ : Type} (e : Engine σ)

def loop (s : σ) : Loop := (e.host s).loop
def setLoop (s : σ) (l : Loop) : σ := e.setHost s { e.host s with loop := l }

/-- Queue the `load` event of each new `about:blank` frame (as `Page.Session.blankLoads`). -/
def blankLoads (s : σ) : σ := Id.run do
  let h := e.host s
  let navs := h.dom.navigations
  if navs.all (!·.2.isEmpty) then return s
  let mut loop := h.loop
  for (el, url) in navs do
    if url.isEmpty then loop := loop.queueTask .domManipulation 0 (some { type := "load", target := el })
  return e.setHost s { h with loop, dom := { h.dom with navigations := navs.filter (!·.2.isEmpty) } }

/-- The microtask checkpoint, then the frames it asked for. -/
def checkpoint (s : σ) : σ := e.blankLoads (e.runJobs s)

def dispatch (s : σ) (target : Nat) (type : String) : σ × Bool :=
  let (s, prevented) := e.dispatchOnly s target type
  (e.checkpoint s, prevented)

def callback (s : σ) (cb : Nat) (target : Int) (arg : Nat) : σ :=
  e.checkpoint (e.callbackOnly s cb target arg)

/-- Run what the event loop gave (as `Page.Session.runTaskP`). -/
def runTask (s : σ) (r : L4Factoidal.EventLoop.Run) : σ :=
  let s := e.setHost s (e.host s).tickTimeline
  match r.kind with
  | .task =>
    match r.event with
    | some ev =>
      let s := (e.dispatchOnly s ev.target ev.type).1
      e.checkpoint (e.setLoop s (e.loop s).finish)
    | none =>
      let s := e.callbackOnly s r.callback (-1) 0
      let periodic : Bool := match (e.loop s).current with
        | some t => match t.timer with
          | some tm => tm.periodic
          | none => false
        | none => false
      let s := e.setLoop s (e.loop s).finish
      if periodic then e.checkpoint s else e.checkpoint (e.release s r.callback)
  | .microtask => e.callback s r.callback (-1) 0
  | .frame => e.callback s r.callback (-2) r.now

/-- The next animation frame time: every 16 ms of the virtual clock. -/
def nextFrame (s : σ) : Option Nat :=
  if (e.loop s).frames.isEmpty then none else
  let t := ((e.loop s).clock + 15) / 16 * 16
  some (if e.lastFrame s == some t then t + 16 else t)

def driver : DriverM Id σ := { loop := e.loop, setLoop := e.setLoop, run := fun s r => e.runTask s r }

/-- Run the event loop to `target` (as `Page.Session.advanceP`). -/
def advance (s : σ) (target : Nat) (maxTasks : Nat := 100000) : σ × Bool :=
  let slot := L4Factoidal.EventLoop.frameSlot (e.loop s).clock target (e.lastFrame s)
  let (s, frames, out) := (e.driver.advanceGo target maxTasks slot s 0 : Id _)
  (e.setLastFrame s (if frames == 0 then e.lastFrame s else slot), out)

def quiet (s : σ) : Bool := (e.loop s).idle && (e.loop s).timers.isEmpty && (e.loop s).frames.isEmpty

/-- Run until nothing waits, or the clock has moved `budgetMs` (as `Page.Session.settleP`).
`waits`: the session waits for its embedder (a worker's script, `Hosts.LeanJSWorkers`), so
time stops there as for a frame's navigation. -/
def settle (s : σ) (budgetMs : Nat) (maxTasks : Nat := 100000) (waits : σ → Bool := fun _ => false) : σ × Bool := Id.run do
  let stop := (e.loop s).clock + budgetMs
  let mut s := s
  for _ in [0:maxTasks] do
    s := (e.advance s (e.loop s).clock 1000).1
    if (e.host s).web.net.waiting || (e.host s).web.net.syncWanted.isSome then return (s, false)
    if e.quiet s then return (s, true)
    if (e.host s).dom.navigations.any (!·.2.isEmpty) || waits s then return (s, false)
    let next := match (e.loop s).timers, e.nextFrame s with
      | t :: _, some f => min t.due f
      | t :: _, none => t.due
      | [], some f => f
      | [], none => (e.loop s).clock
    if next > stop then
      let s' := (e.advance s stop 1000).1
      return (s', e.quiet s')
    s := (e.advance s next 1000).1
  return (s, e.quiet s)

/-- A click of the user at `node`; then the loop runs at the current time. -/
def click (s : σ) (node : Nat) : σ :=
  let target := elementOf (e.host s).dom.dom node
  let s := e.setLoop s ((e.loop s).queueTask .userInteraction 0 (some { type := "click", target }))
  (e.advance s (e.loop s).clock).1

def setEvent (s : σ) (init : String) : σ := e.setHost s { e.host s with event := init }

def dispatchWith (s : σ) (target : Nat) (type init : String) : σ × Bool :=
  let (s, prevented) := e.dispatch (e.setEvent s init) target type
  (e.setEvent s "", prevented)

def setPointer (s : σ) (p : PointerState) : σ := e.setHost s { e.host s with pointer := p }

def moveNow (s : σ) (target : Nat) (init : String) : σ :=
  let p := (e.host s).pointer
  let s := (e.dispatchWith s target "pointermove" init).1
  let s := if p.pressed.isSome && p.canceled then s else (e.dispatchWith s target "mousemove" init).1
  e.setPointer s { (e.host s).pointer with moveFrame := some (frameOf (e.loop s).clock), pending := none }

def flushMove (s : σ) : σ :=
  match (e.host s).pointer.pending with
  | some (target, init) => if (e.host s).pointer.moveFrame == some (frameOf (e.loop s).clock) then s else e.moveNow s target init
  | none => s

def moveWake (s : σ) : Option Nat :=
  match (e.host s).pointer.pending, (e.host s).pointer.moveFrame with
  | some _, some f => some ((f + 1) * 16)
  | _, _ => none

/-- Pointer input of the user at `node` (as `Page.Session.pointerP`). -/
def pointer (s : σ) (kind : PointerKind) (node : Nat) (init : String) : σ :=
  let target := elementOf (e.host s).dom.dom node
  let s := (e.advance s (e.loop s).clock).1
  let s := if kind == .move then s else e.flushMove s
  let p := (e.host s).pointer
  let s := match kind with
    | .down =>
      let (s, prevented) := e.dispatchWith s target "pointerdown" init
      let s := if prevented then s else (e.dispatchWith s target "mousedown" init).1
      e.setPointer s { (e.host s).pointer with pressed := some target, canceled := prevented }
    | .up =>
      let s := (e.dispatchWith s target "pointerup" init).1
      let s := if p.pressed.isSome && p.canceled then s else (e.dispatchWith s target "mouseup" init).1
      let s := match p.pressed with
        | some pressed => (e.dispatchWith s (commonAncestor (e.host s).dom.dom pressed target) "click" init).1
        | none => s
      e.setPointer s { (e.host s).pointer with pressed := none, canceled := false }
    | .cancel =>
      let s := (e.dispatchWith s target "pointercancel" init).1
      e.setPointer s { (e.host s).pointer with pressed := none, canceled := false, pending := none }
    | .move =>
      if p.moveFrame == some (frameOf (e.loop s).clock) then e.setPointer s { p with pending := some (target, init) }
      else e.moveNow s target init
  (e.advance s (e.loop s).clock).1

/-- The init of an `InputEvent` as JSON: its `inputType`, `data` and target ranges (each
"start node, start offset, end node, end offset"). -/
def inputInit (inputType : String) (data : Option String) (ranges : List L4Factoidal.DOM.Range.Rng := []) : String :=
  let n := fun (k : Nat) => L4Factoidal.JSON.Json.number (toString k)
  (L4Factoidal.JSON.Json.object [("inputType", .string inputType),
    ("data", match data with
      | some v => .string v
      | none => .null),
    ("ranges", .array (ranges.map fun r => .array [n r.start.node, n r.start.offset, n r.stop.node, n r.stop.offset]))]).toString

/-- A key of the user (`up`: its release). `keydown` is fired at the editing host of the
selection (else the `body`). When no listener canceled it, `keypress` is fired for a key
with a character (`press`: its init; a host that gives none gets no `keypress`); when
that is not canceled and the key edits (`DOM.Editing.keyCommandIn`), `beforeinput` is
fired at the editing host; when that is not canceled the editing command runs and
`input` is fired. ArrowLeft and ArrowRight move the caret. `init` is the JSON init of the
keyboard events. Everything after `keydown` is a default action of the key: it runs
through `Input.afterCancelable`, so a canceled `keydown` has none of it. -/
def key (s : σ) (up : Bool) (init : String) (k : L4Factoidal.DOM.Editing.KeyInput) (press : Option String := none) : σ :=
  let s := (e.advance s (e.loop s).clock).1
  let target := Hosts.Dom.keyTarget (e.host s).dom
  if up then
    let s := (e.dispatchWith s target "keyup" init).1
    (e.advance s (e.loop s).clock).1
  else
    let (s, prevented) := e.dispatchWith s target "keydown" init
    let s := Input.afterCancelable prevented (fun s =>
      let (s, pressPrevented) := match press with
        | some pressInit => e.dispatchWith s target "keypress" pressInit
        | none => (s, false)
      Input.afterCancelable pressPrevented (fun s =>
        match Hosts.Dom.keyCommandOf (e.host s).dom k, Hosts.Dom.keyHost (e.host s).dom with
        | some (command, value), some host =>
          let inputType := L4Factoidal.DOM.Editing.inputTypeOf command
          let data := L4Factoidal.DOM.Editing.inputDataOf command value
          let (h, ix) := (e.host s).editRules
          let s := e.setHost s h
          let ranges := (Hosts.Dom.editTarget h.dom ix command value).toList
          let (s, prevented) := e.dispatchWith s host "beforeinput" (inputInit inputType data ranges)
          Input.afterCancelable prevented (fun s =>
            let h := e.host s
            let ds := h.dom
            let h := { h with dom := emptyDomHost }
            let (dom, ok, ev) := Hosts.Dom.editKey ds ix command value
            let s := e.setHost s { h with dom, reads := h.reads.wrote }
            match ok, ev with
            | true, some (at_, it, d) => (e.dispatchWith s at_ "input" (inputInit it d)).1
            | _, _ => s) s
        | _, _ =>
          let h := e.host s
          e.setHost s { h with dom := Hosts.Dom.caretMove h.dom k }) s) s
    (e.advance s (e.loop s).clock).1

/-! ### Low-level input events (`WebDriver.Actions.Low`) -/

/-- The layout of the page as it is now is made and kept when the kept one is not
current, so the reads of an input event share it with the scripts' reads after it. -/
def keepLayout (s : σ) : σ := e.setHost s (e.host s).measured.1

/-- The element and its ancestor elements, the element first; from a shadow root the
chain goes on at its host. -/
def chainOf (d : Arena) (n : Nat) : List Nat := Id.run do
  let mut out : Array Nat := #[]
  let mut k := n
  for _ in [0:d.size + 1] do
    if k ≥ d.size then break
    let node := d.get k
    if node.type == .element then out := out.push k
    match node.parent with
    | some p => k := p
    | none =>
      match (if d.isShadowRoot k then node.host else none) with
      | some host => k := host
      | none => break
  return out.toList

/-- The element under a viewport point: the topmost element of the layout's hit test
there (measure op 35, the answer of `document.elementFromPoint`; `Input.pointerTarget`
with no capture), else the document element. The page does not scroll, so a viewport
point is a page point. -/
def hitAt (s : σ) (x y : Int) : σ × Nat :=
  let s := e.keepLayout s
  let h := e.host s
  let d := h.dom.dom
  let hit : Option Nat :=
    if x < 0 || y < 0 || x ≥ 65536 || y ≥ 65536 then none
    else match h.reads.kept with
      | some (_, f) => (f (x.toNat * 65536 + y.toNat) 35).bind Input.hitOf
      | none => none
  (s, match Input.pointerTarget none hit with
    | some n => elementOf d n
    | none => (d.documentElement 0).getD 0)

/-- Dispatch the events of a plan (`Input.boundary`), each with the init of its related
target. -/
def firePlanned (s : σ) (init : Option Nat → String) (plan : List Input.Planned) : σ :=
  plan.foldl (fun s ev => (e.dispatchWith s ev.2.1 ev.1 (init ev.2.2)).1) s

/-- A pointer event at a viewport point (Pointer Events 3, UI Events §5): first the
boundary events of the element now under the pointer; then
- a move: `pointermove`, and `mousemove` for a mouse or pen unless its press was canceled;
- a press: `pointerdown` when no button was held (else `pointermove`, Pointer Events 3
  §4.1.1.2 chorded buttons); when that was not canceled, `mousedown`; when that was not
  canceled, the focus moves to the focusable area at the press; `contextmenu` for the
  secondary button;
- a release: `pointerup` when no button stays held (else `pointermove`), `mouseup` unless
  the press was canceled, then `click` (primary button) or `auxclick` at the common
  ancestor of the press and the release, and `dblclick` after the second click of a pair;
  a touch then leaves (`pointerout`, `pointerleave`);
- a cancel: `pointercancel`, and the pointer leaves.
`detail` is the click count. -/
def lowPointer (s : σ) (phase : Actions.Phase) (type : Actions.PointerType) (pointerId : Nat) (x y : Int)
    (button : Int) (buttons : Nat) (mods : Actions.Mods) (props : Actions.Props) : σ :=
  let s := (e.advance s (e.loop s).clock).1
  let (s, hit) := e.hitAt s x y
  let d := (e.host s).dom.dom
  let p := (e.host s).pointer
  let mouse := type != Actions.PointerType.touch
  let init := fun (detail : Nat) (related : Option Nat) =>
    Input.pointerInit type pointerId x y button buttons mods props detail related
  let prev := p.over.map (chainOf d)
  let next := chainOf d hit
  let plan := Input.boundary "pointer" prev (some next) ++ (if mouse then Input.boundary "mouse" prev (some next) else [])
  let s := e.firePlanned s (init 0) plan
  let s := e.setPointer s { (e.host s).pointer with over := some hit }
  let s := match phase with
    | .move =>
      let s := (e.dispatchWith s hit "pointermove" (init 0 none)).1
      if !mouse || (p.pressed.isSome && p.canceled) then s else (e.dispatchWith s hit "mousemove" (init 0 none)).1
    | .down =>
      let b := button.toNat
      let now := (e.loop s).clock
      let count := Input.clickCount p.last now x y b
      let first := p.pressed.isNone
      let (s, canceled) :=
        if first then e.dispatchWith s hit "pointerdown" (init count none)
        else ((e.dispatchWith s hit "pointermove" (init count none)).1, p.canceled)
      let press : Input.LastPress := { time := now, x, y, button := b, count }
      let s := e.setPointer s { (e.host s).pointer with pressed := some hit, canceled := canceled, last := some press }
      let s := if !mouse then s else
        Input.afterCancelable canceled (fun s =>
          let (s, downCanceled) := e.dispatchWith s hit "mousedown" (init count none)
          -- the default action of the press: the focusable area there takes the focus, else
          -- the focused element loses it (`DOM.Focus.pressTarget`; "@focus" is not an event
          -- but the prelude's focus update steps)
          Input.afterCancelable downCanceled (fun s => (e.dispatch s hit "@focus").1) s) s
      if b == 2 then (e.dispatchWith s hit "contextmenu" (init 0 none)).1 else s
    | .up =>
      let b := button.toNat
      let count := match p.last with
        | some l => l.count
        | none => 1
      let last := buttons == 0
      let s := (e.dispatchWith s hit (if last then "pointerup" else "pointermove") (init count none)).1
      let s := if !mouse then s else
        Input.afterCancelable p.canceled (fun s => (e.dispatchWith s hit "mouseup" (init count none)).1) s
      let s := match p.pressed with
        | some pressed =>
          let at_ := commonAncestor (e.host s).dom.dom pressed hit
          let s := (e.dispatchWith s at_ (Input.clickType b) (init count none)).1
          if b == 0 && count % 2 == 0 then (e.dispatchWith s at_ "dblclick" (init count none)).1 else s
        | none => s
      let held : Option Nat := if last then none else p.pressed
      let s := e.setPointer s { (e.host s).pointer with pressed := held, canceled := !last && p.canceled }
      if mouse then s else
        let s := e.firePlanned s (init 0) (Input.boundary "pointer" (some (chainOf (e.host s).dom.dom hit)) none)
        e.setPointer s { (e.host s).pointer with over := none }
    | .cancel =>
      let s := (e.dispatchWith s hit "pointercancel" (init 0 none)).1
      let s := e.firePlanned s (init 0) (Input.boundary "pointer" (some (chainOf (e.host s).dom.dom hit)) none)
      e.setPointer s { (e.host s).pointer with pressed := none, canceled := false, pending := none, over := none }
  (e.advance s (e.loop s).clock).1

/-- A wheel turned at a viewport point: `wheel` at the element there. The page of a
script session does not scroll, so the event has no default action. -/
def lowWheel (s : σ) (x y dx dy : Int) (mods : Actions.Mods) : σ :=
  let s := (e.advance s (e.loop s).clock).1
  let (s, hit) := e.hitAt s x y
  let s := (e.dispatchWith s hit "wheel" (Input.wheelInit x y dx dy mods)).1
  (e.advance s (e.loop s).clock).1

/-- A key goes down or up (`key`), with `keypress` for a key that has a character. -/
def lowKey (s : σ) (down : Bool) (data : Keys.KeyData) (mods : Actions.Mods) (again : Bool) : σ :=
  e.key s (!down) (Input.keyInit data mods again)
    { key := data.key, shift := mods.shift, ctrl := mods.ctrl, alt := mods.alt, cmd := mods.cmd }
    ((Input.keypressChar data.key mods).map fun c => Input.keyInit data mods again (some c))

/-- One low-level input event as the DOM events of the user. -/
def dispatchLow (s : σ) (low : Actions.Low) : σ :=
  match low with
  | .key down data mods again => e.lowKey s down data mods again
  | .pointer phase type pointerId x y button buttons mods props =>
    e.lowPointer s phase type pointerId x y button buttons mods props
  | .wheel x y dx dy mods => e.lowWheel s x y dx dy mods

/-- What a step of WebDriver's actions reads of the page: the viewport, and with
`layout` the in-view centre point of an element reference (`resolve` finds its node)
from its box in the layout (measure op 17), which is then made and kept. -/
def inputEnv (resolve : Arena → String → Option Nat) (s : σ) (layout : Bool) : σ × Actions.Env :=
  let s := if layout then e.keepLayout s else s
  let h := e.host s
  let width := h.reads.width
  let height := h.reads.height
  let boxes : Option (Nat → Nat → Option String) := if layout then h.reads.kept.map (·.2) else none
  let d := h.dom.dom
  let centre : String → Option (Int × Int) := fun ref =>
    match boxes, resolve d ref with
    | some f, some node =>
      ((f node 17).bind Input.boxOf).map fun b => Actions.inViewCentre width height b.1 b.2.1 b.2.2.1 b.2.2.2
    | _, _ => none
  (s, { width := width, height := height, centre := centre })

/-- The engine as the driver of WebDriver's actions (`Actions.perform`): each low-level
event is dispatched as above, and a tick's duration moves the clock. -/
def inputDriver (resolve : Arena → String → Option Nat) : Actions.Driver σ :=
  let wait : σ → Nat → σ := fun s ms => if ms == 0 then s else (e.advance s ((e.loop s).clock + ms)).1
  { env := e.inputEnv resolve, dispatch := e.dispatchLow, wait := wait }

/-- The viewport moved: reads lay out again, and `resize` at the window when it changed. -/
def resize (s : σ) (width height : Nat) : σ :=
  let r := (e.host s).reads
  if r.width == width && r.height == height then s else
  let s := e.setHost s { e.host s with reads := { r with width, height, kept := none } }
  (e.dispatch s windowId "resize").1

end Engine

end L4Factoidal.WasmVM.Hosts.PageEvents
