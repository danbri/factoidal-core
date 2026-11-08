/-
L4Factoidal.WasmVM.Hosts.Page: the page scripts of one document, run by Lean.
Record: docs/designissues/2026-11-08-page-scripts.md.

Three parts that existed apart are joined here:

- QuickJS-NG compiled to WebAssembly (`tools/wasmvm/quickjs/`), run by the WasmVM engine
  of this library. No host JavaScript engine runs a page script.
- The DOM host (`Hosts.Dom`): each DOM read or change of a script is one import that Lean
  serves on the page's arena (`DOM.Arena`); each change is a typed `Hosts.Dom.Command`.
- The HTML event loop model (`L4Factoidal.EventLoop`): timers, tasks and animation
  frames are its state, and its `step` decides which callback runs next. Listener order
  of each dispatch is `EventLoop.Dispatch.plan`, computed here from the arena's parents.

A `Session` is a pure value: the WasmVM store (the QuickJS heap), the DOM host's state
and the event loop's state. Each action (`start`, `click`, `advance`, `settle`) is a
function from a session to a session. The WASI clock of the module is the event loop's
virtual clock (`Date.now()` and `performance.now()` read it); nothing else of WASI is
granted.

Microtasks are QuickJS's promise jobs (one queue, first in first out, as HTML's microtask
queue). Lean decides when a microtask checkpoint runs: after each task, frame callback
and script (HTML "clean up after running script"), with `runJobs`. In page mode the
module runs no checkpoint of its own.
-/
import L4Factoidal.WasmVM.Api
import L4Factoidal.WasmVM.Wasi
import L4Factoidal.WasmVM.Hosts.Dom
import L4Factoidal.EventLoop.Model
import L4Factoidal.EventLoop.Dispatch

namespace L4Factoidal.WasmVM.Hosts.Page
open L4Factoidal.WasmVM

abbrev DomHost := L4Factoidal.WasmVM.Hosts.Dom.State
abbrev Arena := L4Factoidal.DOM.Dom
abbrev Loop := L4Factoidal.EventLoop.State

/-- The target number of the window (no arena node has it). -/
def windowId : Nat := 0x0FFFFFFF

/-- A registered event listener: the target (a node, the window, or another
EventTarget's number), the type, the capture flag and the callback number. -/
structure Listener where
  target : Nat
  type : String
  capture : Bool
  callback : Nat
  deriving BEq, Repr, Inhabited

def maxListeners : Nat := 65536

/-! ### The script clock

The event loop's clock is virtual and moves only by rule, so tests replay. A script's
own time is the instructions it ran, at `instructionsPerMs` (a stated rate, not a
measurement of this run): script time is the clock at the mark plus the instructions run
since the mark, in whole milliseconds. `performance.now()` and `Date.now()` read the
later of the loop's clock and script time; the loop's clock moves up to script time before
a timer or an animation frame is requested and after each run of the module, so a timer
set after a long script is due its delay after the script time it was set at. The host
moving the clock past script time moves the mark. A reading is never less than the
reading before it (`ScriptClock.read_monotone`, `ScriptClock.read_read`), and the loop's
clock never goes back (`ScriptClock.sync_ge`). -/

structure ScriptClock where
  /-- Instructions for one millisecond of script time: about the rate of QuickJS on the
  native and Wasm engines (100 million instructions a second). -/
  instructionsPerMs : Nat := 100000
  /-- The mark: a time (ms) and the instructions run in the session then. -/
  markClock : Nat := 0
  markSteps : Nat := 0
  /-- Instructions run in the session up to now. -/
  steps : Nat := 0
  /-- The last reading, in ns. -/
  last : Nat := 0
  deriving Inhabited, Repr

/-- Script time in ms: the mark, plus the whole milliseconds of instructions since it. -/
def ScriptClock.ms (c : ScriptClock) : Nat :=
  c.markClock + (c.steps - c.markSteps) / max 1 c.instructionsPerMs

/-- The time in ns with the loop's clock at `clock`: the later of the two, and never less
than the last reading. -/
def ScriptClock.reading (c : ScriptClock) (clock : Nat) : Nat :=
  max c.last (max clock c.ms * 1000000)

/-- A reading, kept as the last. -/
def ScriptClock.read (c : ScriptClock) (clock : Nat) : Nat × ScriptClock :=
  let t := c.reading clock
  (t, { c with last := t })

/-- Each reading is at least the one before, and is the next reading's floor. -/
theorem ScriptClock.read_monotone (c : ScriptClock) (clock : Nat) :
    c.last ≤ (c.read clock).1 ∧ (c.read clock).2.last = (c.read clock).1 :=
  ⟨Nat.le_max_left _ _, rfl⟩

/-- Two readings with any change between them that keeps the last reading (instructions
run, the mark moved, the loop's clock moved): the second is not less. -/
theorem ScriptClock.read_read (c : ScriptClock) (clock clock' : Nat) (f : ScriptClock → ScriptClock)
    (keeps : ∀ d, (f d).last = d.last) :
    (c.read clock).1 ≤ ((f (c.read clock).2).read clock').1 := by
  have h := (ScriptClock.read_monotone (f (c.read clock).2) clock').1
  rw [keeps, (ScriptClock.read_monotone c clock).2] at h
  exact h

/-- At a run of the module with `steps` instructions run so far: when the loop's clock is
past script time (the host moved it), the mark moves to it. -/
def ScriptClock.atRun (c : ScriptClock) (clock steps : Nat) : ScriptClock :=
  let c := { c with steps }
  if c.ms < clock then { c with markClock := clock, markSteps := steps } else c

/-- The loop's clock moved up to script time. -/
def ScriptClock.sync (c : ScriptClock) (clock : Nat) : Nat := max clock c.ms

theorem ScriptClock.sync_ge (c : ScriptClock) (clock : Nat) : clock ≤ c.sync clock := Nat.le_max_left _ _

/-- With no instructions run past the mark, script time is the mark: a page whose scripts
run fewer than `instructionsPerMs` instructions between moves of the clock sees the
clock alone. -/
theorem ScriptClock.ms_mark (c : ScriptClock) (h : c.steps - c.markSteps < max 1 c.instructionsPerMs) :
    c.ms = c.markClock := by
  simp [ScriptClock.ms, Nat.div_eq_of_lt h]

/-! ### Pointer input -/

/-- A press, a pointer move waiting for its frame, and the event being dispatched. -/
structure PointerState where
  /-- The target of the press not yet released, and whether its `pointerdown` was
  canceled (then no compatibility mouse events, Pointer Events 3 §11.1). -/
  pressed : Option Nat := none
  canceled : Bool := false
  /-- The frame (the clock in 16 ms steps) of the last `pointermove` dispatched, and a
  move that waits for the next frame: at most one move is dispatched in a frame. -/
  moveFrame : Option Nat := none
  pending : Option (Nat × String) := none
  deriving Inhabited, Repr

/-- Everything the imports change, except the store. -/
structure Host where
  dom : DomHost
  loop : Loop := {}
  listeners : Array Listener := #[]
  time : ScriptClock := {}
  pointer : PointerState := {}
  /-- The init of the event of the user agent being dispatched, as JSON (`node_query`
  op 16); empty when none. -/
  event : String := ""
  deriving Inhabited

/-- Budgets of one session. -/
structure Limits where
  /-- Instructions for one script, task or event. -/
  fuel : Nat := 4000000000
  /-- Host calls in one run of an export. -/
  hostCalls : Nat := 50000000
  /-- Promise jobs in one microtask checkpoint. -/
  jobs : Nat := 100000
  /-- Memory pages of 64 KiB: 2048 is 128 MiB (QuickJS's own heap limit is 64 MiB). -/
  pages : Nat := 2048
  /-- Commands a page may make (`Hosts.Dom.State.commandLimit`). -/
  commands : Nat := 4096
  /-- The page number of this session's GPU objects (`L4Factoidal.PageGpu.Gid.page`). -/
  gpuPage : Nat := 0
  /-- Console lines a page may write (`Hosts.Dom.State.logLimit`). -/
  logs : Nat := 1024
  /-- Nested browsing contexts for `iframe` elements (`Hosts.Dom.State.framing`). -/
  frames : Bool := false
  deriving Inhabited

/-- The exports of the module, by function address. -/
structure Exports where
  alloc : Nat
  free : Nat
  eval : Nat
  call : Nat
  dispatch : Nat
  runJob : Nat
  page : Nat
  release : Nat
  deriving Inhabited

structure Session where
  store : Store
  inst : Nat
  mem : Nat
  bindings : Array Wasi.Binding
  host : Host
  fx : Exports
  limits : Limits
  /-- Instructions run in total. -/
  steps : Nat := 0
  /-- Promise jobs run in total. -/
  jobs : Nat := 0
  /-- Tasks, frame callbacks and events run in total. -/
  tasks : Nat := 0
  /-- Exceptions that reached the session (each also logged by the page as "Uncaught"). -/
  errors : Array String := #[]
  /-- The time of the last animation frame, if any. -/
  lastFrame : Option Nat := none
  deriving Inhabited

/-! ## The host: WASI with the virtual clock, `foafnaut_dom`, and the event loop imports -/

/-- WASI: the script clock (realtime and monotonic), in nanoseconds (`ScriptClock`).
Nothing else. -/
def caps : Wasi.Caps (StateM Host) :=
  { clock := fun id => if id ≤ 1 then some (do
      let h ← get
      let (t, time) := h.time.read h.loop.clock
      set { h with time }
      return t.toUInt64) else none,
    clockRes := fun id => if id ≤ 1 then some 1000 else none }

/-- The imports served here rather than by `Hosts.Dom`. -/
def loopImports : List (String × Nat) :=
  [("listen", 5), ("unlisten", 1), ("dispatch_plan", 6), ("set_timer", 3), ("clear_timer", 1),
   ("request_frame", 1), ("cancel_frame", 1)]

def accepts (mo nm : String) : Bool :=
  (mo == Hosts.Dom.moduleName && (Hosts.Dom.accepts mo nm || loopImports.any (·.1 == nm))) ||
  (mo == "env" && nm == "emscripten_notify_memory_growth")

/-- The event path of DOM §2.9, target first: the node and its ancestors, then the window
when the root is the document. Any other target is a path of one. -/
def path (d : Arena) (target : Nat) : List Nat := Id.run do
  if target ≥ d.size then return [target]
  let mut out := [target]
  let mut k := target
  for _ in [0:d.size] do
    match (d.get k).parent with
    | some p => out := p :: out; k := p
    | none => break
  let atDocument := (d.get k).type == .document
  return (if atDocument then windowId :: out else out).reverse

def phaseCode : L4Factoidal.EventLoop.Dispatch.Phase → Nat
  | .capturing => 1 | .atTarget => 2 | .bubbling => 3

/-- `dispatch_plan`: `[path length, path (target first)..., then for each listener call
of `Dispatch.plan`: callback, node, phase + 8 × capture, depth]`. -/
def planList (h : Host) (target : Nat) (type : String) (bubbles : Bool) : Array Nat :=
  let p := path h.dom.dom target
  let ls := (h.listeners.toList.filter (·.type == type)).map fun l =>
    ({ node := l.target, capture := l.capture, callback := l.callback } : L4Factoidal.EventLoop.Dispatch.Listener)
  let visits := L4Factoidal.EventLoop.Dispatch.plan p.reverse ls bubbles
  #[p.length] ++ p.toArray ++ (visits.toArray.flatMap fun v =>
    #[v.callback, v.node, phaseCode v.phase + (if v.capture then 8 else 0), v.depth])

section
variable {M : Type} [LinearMemory M]

/-- `node_query` ops served here: 16 the init of the event being dispatched (JSON). -/
def pageQuery (h : Host) (_node op : Nat) : Host × Except Int String :=
  match op with
  | 16 => (h, if h.event.isEmpty then .error (-1) else .ok h.event)
  | _ => (h, .error (-2))

/-- Serve one `foafnaut_dom` import, or `env.emscripten_notify_memory_growth`. -/
def serveExtra (mem : Nat) (mo nm : String) (args : Array Value) (h : Host) (st : StoreOf M) :
    Host × StoreOf M × HostResult :=
  if mo != Hosts.Dom.moduleName then (h, st, .values #[]) else
  let a := Hosts.Dom.arg args
  match nm with
  | "node_query" =>
    if a 1 < 16 then
      let (dom, st, r) := Hosts.Dom.serve mem nm args h.dom st
      ({ h with dom }, st, r)
    else
      let (h, answer) := pageQuery h (a 0) (a 1)
      let (st, r) := Hosts.Dom.answerStr mem st (a 4) (a 5) answer
      (h, st, r)
  | "listen" =>
    match Hosts.Dom.readStr mem st (a 1) (a 2) Hosts.Dom.maxAttrName with
    | .error e => (h, st, Hosts.Dom.codeOrTrap e)
    | .ok type =>
      if h.listeners.size ≥ maxListeners then (h, st, Hosts.Dom.ret (-5))
      else ({ h with listeners := h.listeners.push { target := a 0, type, capture := a 4 != 0, callback := a 3 } },
        st, Hosts.Dom.ret 0)
  | "unlisten" => ({ h with listeners := h.listeners.filter (·.callback != a 0) }, st, Hosts.Dom.ret 0)
  | "dispatch_plan" =>
    match Hosts.Dom.readStr mem st (a 1) (a 2) Hosts.Dom.maxAttrName with
    | .error e => (h, st, Hosts.Dom.codeOrTrap e)
    | .ok type =>
      let (st, r) := Hosts.Dom.answerList mem st (a 4) (a 5) (.ok (planList h (a 0) type (a 3 != 0)))
      (h, st, r)
  | "set_timer" =>
    let (loop, id) := { h.loop with clock := h.time.sync h.loop.clock }.setTimer (a 0) (a 1) (a 2 != 0)
    ({ h with loop }, st, Hosts.Dom.ret id)
  | "clear_timer" => ({ h with loop := h.loop.clearTimer (a 0) }, st, Hosts.Dom.ret 0)
  | "request_frame" =>
    let (loop, id) := { h.loop with clock := h.time.sync h.loop.clock }.requestFrame (a 0)
    ({ h with loop }, st, Hosts.Dom.ret id)
  | "cancel_frame" => ({ h with loop := h.loop.cancelFrame (a 0) }, st, Hosts.Dom.ret 0)
  | _ =>
    let (dom, st, r) := Hosts.Dom.serve mem nm args h.dom st
    ({ h with dom }, st, r)

/-- Host id `id` (an import index) with its binding. -/
def serve (mem : Nat) (bs : Array Wasi.Binding) (id : Nat) (args : Array Value) (h : Host) (st : StoreOf M) :
    Host × StoreOf M × HostResult :=
  match bs[id]? with
  | some (.wasi f) => let ((st, r), h) := (Wasi.call caps mem f args st).run h; (h, st, r)
  | some (.extra mo nm) => serveExtra mem mo nm args h st
  | none => (h, st, .trap s!"no host function {id}")

end

/-! ## Running exports -/

/-- Run function `fa`: host calls are served until the run ends, and the fuel is shared
by the whole run. The answer has the instructions run. The script clock counts them
(`ScriptClock`), and the loop's clock moves up to script time at the end. -/
def Session.run (s : Session) (fa : Nat) (args : Array Value) : Session × Outcome := Id.run do
  let ⟨st, inst, mem, bs, h, fx, lim, steps, jobs, tasks, errors, lastFrame⟩ := s
  let budget : Budget := { fuel := lim.fuel }
  let (st0, o0, n0) := invokeSteps st fa args budget
  let mut st := st0
  let mut o := o0
  let mut n := n0
  let mut h := { h with time := h.time.atRun h.loop.clock steps }
  for _ in [0:lim.hostCalls] do
    match o with
    | .hostCall id vs k =>
      let (h', st', r) := serve mem bs id vs { h with time := h.time.atRun h.loop.clock (steps + n) } st
      h := h'
      let (st'', o', n') := resumeSteps st' k r { budget with fuel := lim.fuel - n }
      st := st''; o := o'; n := n + n'
    | _ => break
  -- Script time passed: the loop's clock moves up to it.
  let time := h.time.atRun h.loop.clock (steps + n)
  h := { h with time, loop := { h.loop with clock := time.sync h.loop.clock } }
  return (⟨st, inst, mem, bs, h, fx, lim, steps + n, jobs, tasks, errors, lastFrame⟩, o)

def i32v (x : Int) : Value := .i32 (Int.toNat (x % 4294967296)).toUInt32

def Session.fail (s : Session) (what : String) : Session :=
  { s with errors := if s.errors.size < 256 then s.errors.push what else s.errors }

/-- An export that answers one i32. -/
def Session.i32 (s : Session) (fa : Nat) (args : Array Value) : Session × Option Nat :=
  match s.run fa args with
  | (s, .values #[.i32 r]) => (s, some r.toNat)
  | (s, .values _) => (s, some 0)
  | (s, o) => (s.fail s!"WasmVM: {o.describe}", none)

/-- Copy `b` into the module (`qjs_alloc`, with a NUL after it). -/
def Session.put (s : Session) (b : ByteArray) : Session × Option Nat :=
  match s.i32 s.fx.alloc #[.i32 (b.size + 1).toUInt32] with
  | (s, some p) =>
    if p == 0 then (s.fail "qjs_alloc gave 0", none) else
    let ⟨st, inst, mem, bs, h, fx, lim, steps, jobs, tasks, errors, lastFrame⟩ := s
    match st.writeMem mem p (b.push 0) with
    | .ok st => (⟨st, inst, mem, bs, h, fx, lim, steps, jobs, tasks, errors, lastFrame⟩, some p)
    | .error e => (Session.fail ⟨st, inst, mem, bs, h, fx, lim, steps, jobs, tasks, errors, lastFrame⟩ e, none)
  | (s, none) => (s, none)

def Session.freePtr (s : Session) (p : Nat) : Session := (s.run s.fx.free #[.i32 p.toUInt32]).1

def u32At (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat + b[i+1]!.toNat * 256 + b[i+2]!.toNat * 65536 + b[i+3]!.toNat * 16777216

/-- A result block (status, text), freed after reading. -/
def Session.result (s : Session) (p : Nat) : Session × Nat × String :=
  if p == 0 then (s.fail "no result block", 2, "") else
  match s.store.readMem s.mem p 8 with
  | .error e => (s.fail e, 2, "")
  | .ok hdr =>
    let status := u32At hdr 0
    let len := u32At hdr 4
    let text := match s.store.readMem s.mem (p + 8) len with
      | .ok b => (String.fromUTF8? b).getD "<not UTF-8>"
      | .error _ => ""
    (s.freePtr p, status, text)

/-- An export that answers a result block. -/
def Session.block (s : Session) (fa : Nat) (args : Array Value) : Session × Nat × String :=
  match s.i32 fa args with
  | (s, some p) => s.result p
  | (s, none) => (s, 2, "")

/-- Run a classic script. -/
def Session.eval (s : Session) (src : String) : Session × Nat × String :=
  let b := src.toUTF8
  match s.put b with
  | (s, some p) =>
    let (s, r) := s.block s.fx.eval #[.i32 p.toUInt32, .i32 b.size.toUInt32]
    (s.freePtr p, r)
  | (s, none) => (s, 2, "")

/-- `qjs_page`: 0 the document URL; 1 the current script node (`-1` none). -/
def Session.setUrl (s : Session) (url : String) : Session :=
  let b := url.toUTF8
  match s.put b with
  | (s, some p) => ((s.run s.fx.page #[.i32 0, .i32 p.toUInt32, .i32 b.size.toUInt32]).1).freePtr p
  | (s, none) => s

def Session.setScript (s : Session) (node : Int) : Session :=
  (s.run s.fx.page #[.i32 1, .i32 0, i32v node]).1

/-- Queue the `load` event of each new `about:blank` frame (HTML §4.8.5 "iframe load
event steps", as a task). -/
def Session.blankLoads (s : Session) : Session := Id.run do
  let navs := s.host.dom.navigations
  if navs.all (!·.2.isEmpty) then return s
  let mut s := s
  for (el, url) in navs do
    if url.isEmpty then
      s := { s with host := { s.host with loop := s.host.loop.queueTask .domManipulation 0 (some { type := "load", target := el }) } }
  return { s with host := { s.host with dom := { s.host.dom with navigations := navs.filter (!·.2.isEmpty) } } }

/-- The microtask checkpoint: run promise jobs until none is pending, at most `limits.jobs`. -/
def Session.runJobs (s : Session) : Session := Id.run do
  let mut s := s
  for _ in [0:s.limits.jobs] do
    match s.i32 s.fx.runJob #[] with
    | (s', some 1) => s := { s' with jobs := s'.jobs + 1 }
    | (s', some 0) => s := s'; break
    | (s', some _) => s := { s' with jobs := s'.jobs + 1 }
    | (s', none) => s := s'; break
  return s.blankLoads

/-- Event flags of `qjs_dispatch`: 1 bubbles, 2 cancelable, 4 composed. -/
def flagsOf (type : String) : Nat :=
  if type == "click" || type.startsWith "mouse" || type.startsWith "pointer" then 7
  else if type == "DOMContentLoaded" then 1
  else 0

def Session.loop (s : Session) : Loop := s.host.loop
def Session.setLoop (s : Session) (l : Loop) : Session := { s with host := { s.host with loop := l } }

/-- Dispatch an event of the user agent, with no microtask checkpoint. -/
def Session.dispatchOnly (s : Session) (target : Nat) (type : String) : Session × Bool :=
  let b := type.toUTF8
  match s.put b with
  | (s, some p) =>
    let (s, status, text) := s.block s.fx.dispatch #[.i32 target.toUInt32, .i32 p.toUInt32, .i32 b.size.toUInt32, .i32 (flagsOf type).toUInt32]
    let s := s.freePtr p
    let s := if status == 1 then s.fail text else s
    ({ s with tasks := s.tasks + 1 }, text == "prevented")
  | (s, none) => (s, false)

/-- Dispatch an event of the user agent; then the microtask checkpoint. -/
def Session.dispatch (s : Session) (target : Nat) (type : String) : Session × Bool :=
  let (s, prevented) := s.dispatchOnly target type
  (s.runJobs, prevented)

/-- Run one callback of a timer (target -1) or of an animation frame (-2). -/
def Session.callbackOnly (s : Session) (cb : Nat) (target : Int) (arg : Nat) : Session :=
  let (s, status, text) := s.block s.fx.call #[i32v cb, i32v target, i32v arg]
  let s := if status == 1 then s.fail text else s
  { s with tasks := s.tasks + 1 }

/-- Run one callback, then the microtask checkpoint. -/
def Session.callback (s : Session) (cb : Nat) (target : Int) (arg : Nat) : Session :=
  (s.callbackOnly cb target arg).runJobs

/-- Run what the event loop gave. A task's steps end (`EventLoop.State.finish`: an interval
is armed again, and the currently running task is null again) before the microtask
checkpoint, as in HTML §8.1.7.3 steps 6 and 7: so a timer set from a microtask does not
take the nesting level of the task before it. -/
def Session.runTask (s : Session) (r : L4Factoidal.EventLoop.Run) : Session :=
  match r.kind with
  | .task =>
    match r.event with
    | some e =>
      let s := (s.dispatchOnly e.target e.type).1
      (s.setLoop s.loop.finish).runJobs
    | none =>
      let s := s.callbackOnly r.callback (-1) 0
      -- A timeout's callback runs once; an interval's stays.
      let periodic : Bool := match s.loop.current with
        | some t => match t.timer with
          | some tm => tm.periodic
          | none => false
        | none => false
      let s := s.setLoop s.loop.finish
      let s := if periodic = true then s else (s.run s.fx.release #[.i32 r.callback.toUInt32]).1
      s.runJobs
  | .microtask => s.callback r.callback (-1) 0
  | .frame => s.callback r.callback (-2) r.now

/-- The next animation frame time: frames come every 16 ms of the virtual clock. -/
def Session.nextFrame (s : Session) : Option Nat :=
  if s.loop.frames.isEmpty then none else
  let t := (s.loop.clock + 15) / 16 * 16
  some (if s.lastFrame == some t then t + 16 else t)

/-- The session as a host of the event loop (`EventLoop.Driver`): the loop's runs are
callbacks in the module. -/
def Session.driver : L4Factoidal.EventLoop.Driver Session :=
  { loop := Session.loop, setLoop := Session.setLoop, run := Session.runTask }

/-- Run the event loop until the virtual clock is at `target` and no task waits, or
`maxTasks` steps have run. The clock stops at each due timer, in order. At most one
animation frame batch runs, at the last frame time the advance reaches
(`EventLoop.frameSlot`; `EventLoop.Driver.advanceGo_frames`): a host that fell behind
gets one frame with the latest time, as a browser does, not every missed frame. The
answer says whether the loop ran out of steps. -/
def Session.advance (s : Session) (target : Nat) (maxTasks : Nat := 100000) : Session × Bool :=
  let slot := L4Factoidal.EventLoop.frameSlot s.loop.clock target s.lastFrame
  let (s, frames, out) := Session.driver.advanceGo target maxTasks slot s 0
  ({ s with lastFrame := if frames == 0 then s.lastFrame else slot }, out)

/-- No task, timer or animation frame waits. -/
def Session.quiet (s : Session) : Bool :=
  s.loop.idle && s.loop.timers.isEmpty && s.loop.frames.isEmpty

/-- Run the loop until nothing waits (no task, armed timer or animation frame), or the
virtual clock has moved `budgetMs`, or `maxTasks` steps. The answer says whether it
ended quiet. -/
def Session.settle (s : Session) (budgetMs : Nat) (maxTasks : Nat := 100000) : Session × Bool := Id.run do
  let stop := s.loop.clock + budgetMs
  let mut s := s
  for _ in [0:maxTasks] do
    let (s', _) := s.advance s.loop.clock 1000
    s := s'
    if s.quiet then return (s, true)
    -- A navigation waits for the embedder: give the session back (not quiet).
    if s.host.dom.navigations.any (!·.2.isEmpty) then return (s, false)
    let next := match s.loop.timers, s.nextFrame with
      | t :: _, some f => min t.due f
      | t :: _, none => t.due
      | [], some f => f
      | [], none => s.loop.clock
    if next > stop then
      let (s', _) := s.advance stop 1000
      return (s', s'.quiet)
    let (s', _) := s.advance next 1000
    s := s'
  return (s, s.quiet)

/-- The node itself when it is an element, else its nearest element ancestor (a click on
text goes to the element that holds it), else the node. -/
def elementOf (d : Arena) (n : Nat) : Nat := Id.run do
  let mut k := n
  for _ in [0:d.size + 1] do
    if k ≥ d.size || (d.get k).type == .element then return k
    match (d.get k).parent with
    | some p => k := p
    | none => return n
  return n

/-- A click of the user at `node` (a task of the user interaction source); then the loop
runs at the current time. -/
def Session.click (s : Session) (node : Nat) : Session :=
  let target := elementOf s.host.dom.dom node
  let s := s.setLoop (s.loop.queueTask .userInteraction 0 (some { type := "click", target }))
  (s.advance s.loop.clock).1

/-- Dispatch an event of the user agent with the pointer data `init` (a JSON object the
prelude reads with `node_query` op 16), then the microtask checkpoint. -/
def Session.dispatchWith (s : Session) (target : Nat) (type init : String) : Session × Bool :=
  let s := { s with host := { s.host with event := init } }
  let (s, prevented) := s.dispatch target type
  ({ s with host := { s.host with event := "" } }, prevented)

def Session.setPointer (s : Session) (p : PointerState) : Session := { s with host := { s.host with pointer := p } }

/-- The nearest inclusive ancestor of `a` that is also an inclusive ancestor of `b` (HTML
"click": the press and the release on different elements click their common ancestor). -/
def commonAncestor (d : Arena) (a b : Nat) : Nat :=
  let pb := path d b
  ((path d a).find? fun k => k < d.size && (d.get k).type == .element && pb.contains k).getD b

/-- The frame of a time: the clock in 16 ms steps, as `nextFrame`. -/
def frameOf (clock : Nat) : Nat := clock / 16

/-- `pointermove`, then `mousemove` unless the press's `pointerdown` was canceled. -/
def Session.moveNow (s : Session) (target : Nat) (init : String) : Session :=
  let p := s.host.pointer
  let (s, _) := s.dispatchWith target "pointermove" init
  let s := if p.pressed.isSome && p.canceled then s else (s.dispatchWith target "mousemove" init).1
  s.setPointer { s.host.pointer with moveFrame := some (frameOf s.loop.clock), pending := none }

/-- The move that waits, when its frame has come. -/
def Session.flushMove (s : Session) : Session :=
  match s.host.pointer.pending with
  | some (target, init) => if s.host.pointer.moveFrame == some (frameOf s.loop.clock) then s else s.moveNow target init
  | none => s

/-- When the move that waits is due: the next frame. -/
def Session.moveWake (s : Session) : Option Nat :=
  match s.host.pointer.pending, s.host.pointer.moveFrame with
  | some _, some f => some ((f + 1) * 16)
  | _, _ => none

inductive PointerKind where | down | move | up | cancel
  deriving BEq, Repr

/-- Pointer input of the user at `node` (Pointer Events 3, UI Events §5): a press is
`pointerdown` then `mousedown`; a release is `pointerup`, `mouseup`, then `click` at the
common ancestor of the press and the release; a move is `pointermove` and `mousemove`,
at most one in a frame (a later move in the same frame replaces the one that waits); a
cancel is `pointercancel`. A canceled `pointerdown` stops the compatibility mouse events
of its press, not the click. `init` is the JSON of the coordinates and buttons. What is
due runs first; then the loop runs at the current time. -/
def Session.pointer (s : Session) (kind : PointerKind) (node : Nat) (init : String) : Session :=
  let target := elementOf s.host.dom.dom node
  let s := (s.advance s.loop.clock).1
  let s := if kind == .move then s else s.flushMove
  let p := s.host.pointer
  let s := match kind with
    | .down =>
      let (s, prevented) := s.dispatchWith target "pointerdown" init
      let s := if prevented then s else (s.dispatchWith target "mousedown" init).1
      s.setPointer { s.host.pointer with pressed := some target, canceled := prevented }
    | .up =>
      let (s, _) := s.dispatchWith target "pointerup" init
      let s := if p.pressed.isSome && p.canceled then s else (s.dispatchWith target "mouseup" init).1
      let s := match p.pressed with
        | some pressed => (s.dispatchWith (commonAncestor s.host.dom.dom pressed target) "click" init).1
        | none => s
      s.setPointer { s.host.pointer with pressed := none, canceled := false }
    | .cancel =>
      let (s, _) := s.dispatchWith target "pointercancel" init
      s.setPointer { s.host.pointer with pressed := none, canceled := false, pending := none }
    | .move =>
      if p.moveFrame == some (frameOf s.loop.clock) then s.setPointer { p with pending := some (target, init) }
      else s.moveNow target init
  (s.advance s.loop.clock).1

/-! ## Starting a page -/

/-- The module, decoded and validated once. `base` is an instance after `_initialize`,
`qjs_new` (the prelude) and page mode, on an empty document: each page starts from a
copy of it with its own arena, so the prelude runs once, not once per page. -/
structure Module' where
  module : Module
  valid : ValidModule
  bytes : Nat
  base : Option Session := none

/-- An arena with only a document node (node 0). -/
def emptyDocument : Arena := { nodes := #[{ type := .document, doc := 0 }] }

def memOf (st : Store) (ia : Nat) : Nat :=
  match st.export? ia "memory" with
  | some (.mem a) => a
  | _ => st.mems.size + 1

/-- Instantiate the module on arena `dom`, run `_initialize`, `qjs_new` (the prelude)
and page mode. -/
def instantiatePage (m : Module') (dom : Arena) (lim : Limits := {}) : Except String Session := do
  let (st, ex, bs) ← Wasi.link ({ pageLimit := lim.pages } : Store) m.module accepts
  let (st, ia) ← match instantiate st m.valid ex with
    | (_, .error e) => throw s!"instantiate: {e.toString}"
    | (st, .ok (ia, none)) => pure (st, ia)
    | (_, .ok (_, some _)) => throw "the module has a start function"
  let fa := fun (name : String) => match st.export? ia name with
    | some (.func a) => Except.ok a
    | _ => Except.error s!"the module has no export {name}"
  let alloc ← fa "qjs_alloc"
  let free ← fa "qjs_free"
  let evalF ← fa "qjs_eval"
  let callF ← fa "qjs_call"
  let dispatchF ← fa "qjs_dispatch"
  let runJob ← fa "qjs_run_job"
  let page ← fa "qjs_page"
  let release ← fa "qjs_release"
  let fx : Exports := { alloc, free, eval := evalF, call := callF, dispatch := dispatchF, runJob, page, release }
  let init ← fa "_initialize"
  let qnew ← fa "qjs_new"
  let mode ← fa "qjs_page_mode"
  let host : Host := { dom := { dom, commandLimit := lim.commands, logLimit := lim.logs } }
  let s : Session := { store := st, inst := ia, mem := memOf st ia, bindings := bs, host, fx, limits := lim }
  let (s, o) := s.run init #[]
  if let .values _ := o then pure () else throw s!"_initialize: {o.describe}"
  let (s, r) := s.i32 qnew #[]
  if r != some 0 then throw s!"qjs_new: {r} {s.errors.toList}"
  let (s, _) := s.run mode #[.i32 1]
  return s

def prepare (bytes : ByteArray) (lim : Limits := {}) : Except String Module' := do
  let md ← match Binary.decode bytes with
    | .ok md => pure md
    | .error e => throw s!"decode: {e.toString}"
  let vm ← match validate md with
    | .ok vm => pure vm
    | .error e => throw s!"validate: {e.toString}"
  let m : Module' := { module := md, valid := vm, bytes := bytes.size }
  let base ← instantiatePage m emptyDocument lim
  return { m with base := some base }

/-- The navigations that wait for the embedder: an `iframe` and its `src` URL. The
`load` events of `about:blank` documents are queued here, as tasks. -/
def Session.frameLoads (s : Session) : Array (Nat × String) :=
  s.host.dom.navigations.filter (!·.2.isEmpty)

/-- The embedder's answer to the navigation of `el`: its new document (`none` when it
could not be loaded, which keeps the old one). The document joins the arena and the
`load` event at `el` is queued. -/
def Session.attachFrame (s : Session) (el : Nat) (doc : Option Arena) : Session := Id.run do
  let h := s.host.dom
  let navs := h.navigations.filter (·.1 != el)
  let mut h := { h with navigations := navs }
  if let some d := doc then
    let (dom, root) := h.dom.graft d
    h := { h with dom, frames := (h.frames.filter (·.1 != el)).push (el, root) }
  let s := { s with host := { s.host with dom := h } }
  return s.setLoop (s.loop.queueTask .networking 0 (some { type := "load", target := el }))

/-- Start a page: its classic scripts in document order (each with the current script set
and a microtask checkpoint after it), `DOMContentLoaded` at the document, then the `load`
event at the window as a task, and the tasks that are due at time 0. `scripts` are the
script element's node and its source. `frames` are the `iframe` elements whose documents
the embedder loaded, each with its document parsed on its own: each joins the page's arena
(`Dom.graft`), and its `load` event at the `iframe` is a task before the window's. The
frames share the page's script realm. -/
def start (m : Module') (dom : Arena) (url : String) (scripts : Array (Nat × String)) (lim : Limits := {})
    (frames : Array (Nat × Arena) := #[]) (time : ScriptClock := {}) : Except String Session := do
  let mut dom := dom
  let mut framed : Array (Nat × Nat) := #[]
  for (el, doc) in frames do
    if el < dom.size then
      let (d, root) := dom.graft doc
      dom := d
      framed := framed.push (el, root)
  let s : Session ← match m.base with
    | some b =>
      let domHost : DomHost := { dom, commandLimit := lim.commands, logLimit := lim.logs, frames := framed, framing := lim.frames }
      let host : Host := { dom := domHost, time }
      pure { b with host, limits := lim, steps := 0 }
    | none => do
      let s ← instantiatePage m dom lim
      pure { s with host := { s.host with dom := { s.host.dom with frames := framed, framing := lim.frames }, time } }
  let s := { s with host := { s.host with dom := { s.host.dom with gpu := L4Factoidal.PageGpu.State.empty lim.gpuPage } } }
  let s := (s.run s.fx.page #[.i32 2, .i32 0, .i32 0]).1
  let mut s := s.setUrl url
  for (node, src) in scripts do
    s := s.setScript node
    let (s', status, text) := s.eval src
    s := if status == 1 then s'.fail text else s'
    s := s.runJobs
  s := s.setScript (-1)
  s := (s.dispatch 0 "DOMContentLoaded").1
  for (el, _) in framed do
    s := s.setLoop (s.loop.queueTask .domManipulation 0 (some { type := "load", target := el }))
  s := s.setLoop (s.loop.queueTask .domManipulation 0 (some { type := "load", target := windowId }))
  return (s.advance 0).1

/-! ## What a turn did -/

def Session.commands (s : Session) : Array Hosts.Dom.Command := s.host.dom.commands
def Session.logs (s : Session) : Array String := s.host.dom.logs

/-- Changes recorded since the start (`Hosts.Dom.State.changes`). -/
def Session.changes (s : Session) : Nat := s.host.dom.changes

/-- The cost contract of a turn: the arena changed exactly when a change was recorded,
so a host lays the page out again only then (`changed`). A write of the value an
attribute or data already has records nothing. -/
def changed (before after : Session) : Bool := after.changes != before.changes

end L4Factoidal.WasmVM.Hosts.Page
