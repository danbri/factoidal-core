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
  the common ancestor, at most one move a frame.
-/
import L4Factoidal.WasmVM.Hosts.Page

namespace L4Factoidal.WasmVM.Hosts.PageEvents
open L4Factoidal.WasmVM.Hosts.Page

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

/-- The viewport moved: reads lay out again, and `resize` at the window when it changed. -/
def resize (s : σ) (width height : Nat) : σ :=
  let r := (e.host s).reads
  if r.width == width && r.height == height then s else
  let s := e.setHost s { e.host s with reads := { r with width, height, kept := none } }
  (e.dispatch s windowId "resize").1

end Engine

end L4Factoidal.WasmVM.Hosts.PageEvents
