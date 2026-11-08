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

/-! ### Pointer input and layout reads -/

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

/-- The layout reads of scripts: the engine's layout of an arena at a viewport (CSS
pixels), as the answers of `node_query` ops 17 (a node's boxes) and 18 (an SVG element's
bounding box). The engine gives the function; it lays out when a read first asks. -/
abbrev Measure := Arena → Nat → Nat → (Nat → Nat → Option String)

structure Reads where
  measure : Option Measure := none
  width : Nat := 800
  height : Nat := 600
  /-- DOM writes served so far: a layout is of one version. -/
  version : Nat := 0
  /-- The answers of the layout of `version` at the viewport, once a read asked. -/
  kept : Option (Nat × (Nat → Nat → Option String)) := none
  /-- Layouts made for reads. -/
  layouts : Nat := 0
  deriving Inhabited

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
  reads : Reads := {}
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

/-- The imports of `foafnaut_dom` that change nothing a layout reads. -/
def readOnlyImports : List String :=
  ["get_element_by_id", "document_element", "tag_name", "text_content_get", "get_attribute", "node_info",
   "node_string", "node_children", "node_query", "console_log", "gpu_command"]

/-- A layout of the current arena and viewport for reads, counted. -/
def Host.measureNow (h : Host) : Host × Option (Nat → Nat → Option String) :=
  match h.reads.measure with
  | none => (h, none)
  | some m =>
    let f := m h.dom.dom h.reads.width h.reads.height
    ({ h with reads := { h.reads with kept := some (h.reads.version, f), layouts := h.reads.layouts + 1 } }, some f)

/-- The answers of the layout of the current arena and viewport: kept until a write or a
new viewport, so reads after no write share one layout, and a read after writes makes
one (as a browser's forced layout). -/
def Host.measured (h : Host) : Host × Option (Nat → Nat → Option String) :=
  match h.reads.kept with
  | some (v, f) => if v == h.reads.version then (h, some f) else h.measureNow
  | none => h.measureNow

/-- `node_query` ops served here: 16 the init of the event being dispatched; 17 a node's
layout, "x y w h left top width height" (border box in the page, then the client box);
18 an SVG element's bounding box in its user space, "x y w h"; 19 the viewport, "w h". -/
def pageQuery (h : Host) (node op : Nat) : Host × Except Int String :=
  match op with
  | 16 => (h, if h.event.isEmpty then .error (-1) else .ok h.event)
  | 19 => (h, .ok s!"{h.reads.width} {h.reads.height}")
  | _ =>
    let (h, f) := h.measured
    match f with
    | some f => (h, match f node op with | some r => .ok r | none => .error (-1))
    | none => (h, .error (-2))

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
    let reads := if readOnlyImports.contains nm then h.reads else { h.reads with version := h.reads.version + 1 }
    ({ h with dom, reads }, st, r)

/-- Host id `id` (an import index) with its binding. -/
def serve (mem : Nat) (bs : Array Wasi.Binding) (id : Nat) (args : Array Value) (h : Host) (st : StoreOf M) :
    Host × StoreOf M × HostResult :=
  match bs[id]? with
  | some (.wasi f) => let ((st, r), h) := (Wasi.call caps mem f args st).run h; (h, st, r)
  | some (.extra mo nm) => serveExtra mem mo nm args h st
  | none => (h, st, .trap s!"no host function {id}")

end

/-! ## The machine that runs the guest

The session code below is written once, as a `Prog`: pure Lean that stops with an `Ask`
where it needs the guest, and goes on with the `Reply`. Two machines answer the asks:

- the interpreter (`Prog.runLocal`): `Session.run` on the session's own store, the path
  of every embedding so far;
- the host's WebAssembly engine, running the guest that `WasmVM.Aot` translated
  (`labs/demos/foafnaut/WebScripts.lean` on the Hub): the engine hands each ask to the
  host and continues the program with the host's reply
  (docs/designissues/2026-11-08-wasmvm-aot.md, section 5).

So the order of scripts, tasks, microtask checkpoints and frames, and every DOM command,
is decided by the same Lean code on both. -/

/-- Run function `fa` with the interpreter: host calls are served until the run ends, and the fuel is shared
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

/-- What the session code asks of the machine. -/
inductive Ask where
  /-- Run export `fa` (a number of `Session.fx`) with these arguments; the machine serves
  the host calls on the session's host state and adds the instructions to `steps`. -/
  | invoke (fa : Nat) (args : Array Value)
  /-- `len` bytes of the guest's memory at `ptr`. -/
  | read (ptr len : Nat)
  /-- Write the bytes into the guest's memory at `ptr`. -/
  | write (ptr : Nat) (bytes : ByteArray)

inductive Reply where
  | ran (o : Outcome)
  | bytes (r : Except String ByteArray)
  | wrote (r : Except String Unit)
  deriving Inhabited

/-- A session program. `ask q s k`: the machine answers `q` on session `s` and the
program goes on with `k` of the session and the reply. -/
inductive Prog (α : Type) where
  | done (a : α)
  | ask (q : Ask) (s : Session) (k : Session → Reply → Prog α)

def Prog.bind : Prog α → (α → Prog β) → Prog β
  | .done a, f => f a
  | .ask q s k, f => .ask q s fun s r => (k s r).bind f

instance : Monad Prog where
  pure := .done
  bind := Prog.bind

/-- The interpreter's answer to one ask. The store is taken apart before a write, so the
memory is written in place. -/
def Session.serveAsk (s : Session) : Ask → Session × Reply
  | .invoke fa args => let (s, o) := s.run fa args; (s, .ran o)
  | .read p n => (s, .bytes (s.store.readMem s.mem p n))
  | .write p b =>
    let ⟨st, inst, mem, bs, h, fx, lim, steps, jobs, tasks, errors, lastFrame⟩ := s
    match st.writeMem mem p b with
    | .ok st => (⟨st, inst, mem, bs, h, fx, lim, steps, jobs, tasks, errors, lastFrame⟩, .wrote (.ok ()))
    | .error e => (⟨st, inst, mem, bs, h, fx, lim, steps, jobs, tasks, errors, lastFrame⟩, .wrote (.error e))

/-- Run a program with the interpreter. -/
def Prog.runLocal : Prog α → α
  | .done a => a
  | .ask q s k => let (s, r) := s.serveAsk q; runLocal (k s r)

/-- `runLocal` is a monad morphism to `Id`: on the interpreter a program is its steps, in
order, each ask answered by `serveAsk` as it comes. So the interpreter path computes what
the same code computed before it was a program. -/
@[simp] theorem Prog.runLocal_pure (a : α) : (pure a : Prog α).runLocal = a := rfl

theorem Prog.runLocal_bind (p : Prog α) (f : α → Prog β) : (p >>= f).runLocal = (f p.runLocal).runLocal := by
  induction p with
  | done a => rfl
  | ask q s k ih =>
    show (Prog.bind (.ask q s k) f).runLocal = _
    simp only [Prog.bind, Prog.runLocal]
    exact ih _ _

/-- Run export `fa` on the machine. -/
def Session.runP (s : Session) (fa : Nat) (args : Array Value) : Prog (Session × Outcome) :=
  .ask (.invoke fa args) s fun s r => .done (s, match r with
    | .ran o => o
    | _ => .trap (.host "the machine answered a run with no outcome"))

/-- On the interpreter, a run on the machine is `Session.run`. -/
theorem runP_local (s : Session) (fa : Nat) (args : Array Value) :
    (s.runP fa args).runLocal = s.run fa args := by
  simp only [Session.runP, Prog.runLocal, Session.serveAsk]

def i32v (x : Int) : Value := .i32 (Int.toNat (x % 4294967296)).toUInt32

def Session.fail (s : Session) (what : String) : Session :=
  { s with errors := if s.errors.size < 256 then s.errors.push what else s.errors }

/-- An export that answers one i32. -/
def Session.i32P (s : Session) (fa : Nat) (args : Array Value) : Prog (Session × Option Nat) := do
  let (s, o) ← s.runP fa args
  return match o with
    | .values #[.i32 r] => (s, some r.toNat)
    | .values _ => (s, some 0)
    | o => (s.fail s!"WasmVM: {o.describe}", none)

/-- Copy `b` into the module (`qjs_alloc`, with a NUL after it). -/
def Session.putP (s : Session) (b : ByteArray) : Prog (Session × Option Nat) := do
  match ← s.i32P s.fx.alloc #[.i32 (b.size + 1).toUInt32] with
  | (s, some p) =>
    if p == 0 then return (s.fail "qjs_alloc gave 0", none)
    .ask (.write p (b.push 0)) s fun s r => .done (match r with
      | .wrote (.ok ()) => (s, some p)
      | .wrote (.error e) => (s.fail e, none)
      | _ => (s.fail "the machine answered a write with no result", none))
  | (s, none) => return (s, none)

def Session.freeP (s : Session) (p : Nat) : Prog Session := do
  return (← s.runP s.fx.free #[.i32 p.toUInt32]).1

def u32At (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat + b[i+1]!.toNat * 256 + b[i+2]!.toNat * 65536 + b[i+3]!.toNat * 16777216

def Session.readP (s : Session) (p n : Nat) : Prog (Session × Except String ByteArray) :=
  .ask (.read p n) s fun s r => .done (s, match r with
    | .bytes b => b
    | _ => .error "the machine answered a read with no bytes")

/-- A result block (status, text), freed after reading. -/
def Session.resultP (s : Session) (p : Nat) : Prog (Session × Nat × String) := do
  if p == 0 then return (s.fail "no result block", 2, "")
  match ← s.readP p 8 with
  | (s, .error e) => return (s.fail e, 2, "")
  | (s, .ok hdr) =>
    let status := u32At hdr 0
    let len := u32At hdr 4
    let (s, b) ← s.readP (p + 8) len
    let text := match b with
      | .ok b => (String.fromUTF8? b).getD "<not UTF-8>"
      | .error _ => ""
    return (← s.freeP p, status, text)

/-- An export that answers a result block. -/
def Session.blockP (s : Session) (fa : Nat) (args : Array Value) : Prog (Session × Nat × String) := do
  match ← s.i32P fa args with
  | (s, some p) => s.resultP p
  | (s, none) => return (s, 2, "")

/-- Run a classic script. -/
def Session.evalP (s : Session) (src : String) : Prog (Session × Nat × String) := do
  let b := src.toUTF8
  match ← s.putP b with
  | (s, some p) =>
    let (s, r) ← s.blockP s.fx.eval #[.i32 p.toUInt32, .i32 b.size.toUInt32]
    return (← s.freeP p, r)
  | (s, none) => return (s, 2, "")

/-- `qjs_page`: 0 the document URL; 1 the current script node (`-1` none). -/
def Session.setUrlP (s : Session) (url : String) : Prog Session := do
  let b := url.toUTF8
  match ← s.putP b with
  | (s, some p) => (← s.runP s.fx.page #[.i32 0, .i32 p.toUInt32, .i32 b.size.toUInt32]).1.freeP p
  | (s, none) => return s

def Session.setScriptP (s : Session) (node : Int) : Prog Session := do
  return (← s.runP s.fx.page #[.i32 1, .i32 0, i32v node]).1

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
def Session.runJobsP (s : Session) : Prog Session := do
  let mut s := s
  for _ in [0:s.limits.jobs] do
    match ← s.i32P s.fx.runJob #[] with
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
def Session.dispatchOnlyP (s : Session) (target : Nat) (type : String) : Prog (Session × Bool) := do
  let b := type.toUTF8
  match ← s.putP b with
  | (s, some p) =>
    let (s, status, text) ← s.blockP s.fx.dispatch #[.i32 target.toUInt32, .i32 p.toUInt32, .i32 b.size.toUInt32, .i32 (flagsOf type).toUInt32]
    let s ← s.freeP p
    let s := if status == 1 then s.fail text else s
    return ({ s with tasks := s.tasks + 1 }, text == "prevented")
  | (s, none) => return (s, false)

/-- Dispatch an event of the user agent; then the microtask checkpoint. -/
def Session.dispatchP (s : Session) (target : Nat) (type : String) : Prog (Session × Bool) := do
  let (s, prevented) ← s.dispatchOnlyP target type
  return (← s.runJobsP, prevented)

/-- Run one callback of a timer (target -1) or of an animation frame (-2). -/
def Session.callbackOnlyP (s : Session) (cb : Nat) (target : Int) (arg : Nat) : Prog Session := do
  let (s, status, text) ← s.blockP s.fx.call #[i32v cb, i32v target, i32v arg]
  let s := if status == 1 then s.fail text else s
  return { s with tasks := s.tasks + 1 }

/-- Run one callback, then the microtask checkpoint. -/
def Session.callbackP (s : Session) (cb : Nat) (target : Int) (arg : Nat) : Prog Session := do
  (← s.callbackOnlyP cb target arg).runJobsP

/-- Run what the event loop gave. A task's steps end (`EventLoop.State.finish`: an interval
is armed again, and the currently running task is null again) before the microtask
checkpoint, as in HTML §8.1.7.3 steps 6 and 7: so a timer set from a microtask does not
take the nesting level of the task before it. -/
def Session.runTaskP (s : Session) (r : L4Factoidal.EventLoop.Run) : Prog Session := do
  match r.kind with
  | .task =>
    match r.event with
    | some e =>
      let s := (← s.dispatchOnlyP e.target e.type).1
      (s.setLoop s.loop.finish).runJobsP
    | none =>
      let s ← s.callbackOnlyP r.callback (-1) 0
      -- A timeout's callback runs once; an interval's stays.
      let periodic : Bool := match s.loop.current with
        | some t => match t.timer with
          | some tm => tm.periodic
          | none => false
        | none => false
      let s := s.setLoop s.loop.finish
      if periodic = true then s.runJobsP
      else
        let (s, _) ← s.runP s.fx.release #[.i32 r.callback.toUInt32]
        s.runJobsP
  | .microtask => s.callbackP r.callback (-1) 0
  | .frame => s.callbackP r.callback (-2) r.now

/-- The next animation frame time: frames come every 16 ms of the virtual clock. -/
def Session.nextFrame (s : Session) : Option Nat :=
  if s.loop.frames.isEmpty then none else
  let t := (s.loop.clock + 15) / 16 * 16
  some (if s.lastFrame == some t then t + 16 else t)

/-! ### The event loop's host, with runs on the machine

`DriverM` is `EventLoop.Driver` with `run` in a monad: the same loop, step for step
(`DriverM.ofDriver_advanceGo`: in `Id` it is `Driver.advanceGo`), so the theorems of
`EventLoop.Driver` (one animation frame batch per advance) are about this loop. -/

structure DriverM (m : Type → Type) (σ : Type) where
  loop : σ → Loop
  setLoop : σ → Loop → σ
  run : σ → L4Factoidal.EventLoop.Run → m σ

namespace DriverM
variable {m : Type → Type} [Monad m] {σ : Type} (d : DriverM m σ)

def frameGo : Nat → σ → m σ
  | 0, s => pure s
  | fuel + 1, s =>
    let (l, r) := (d.loop s).frameStep
    let s := d.setLoop s l
    match r with
    | some r => do frameGo fuel (← d.run s r)
    | none => pure s

def frame (s : σ) : m σ :=
  let s := d.setLoop s (d.loop s).render
  d.frameGo ((d.loop s).frameBatch.length + 1) s

def advanceGo (target : Nat) : Nat → Option Nat → σ → Nat → m (σ × Nat × Bool)
  | 0, _, s, frames => pure (s, frames, true)
  | fuel + 1, slot, s, frames =>
    let (l, r) := (d.loop s).step
    let s := d.setLoop s l
    match r with
    | some r => do advanceGo target fuel slot (← d.run s r) frames
    | none =>
      let goal := match slot with | some f => min f target | none => target
      let (l, fired) := (d.loop s).advanceTo goal
      let s := d.setLoop s l
      if fired.isEmpty ∧ slot = some l.clock then
        if l.frames.isEmpty then advanceGo target fuel none s frames
        else do advanceGo target fuel none (← d.frame s) (frames + 1)
      else if fired.isEmpty ∧ target ≤ l.clock then pure (s, frames, false)
      else advanceGo target fuel slot s frames

/-- A pure driver as a driver in `Id`. -/
def ofDriver (d : L4Factoidal.EventLoop.Driver σ) : DriverM Id σ := ⟨d.loop, d.setLoop, d.run⟩

theorem ofDriver_frameGo (d : L4Factoidal.EventLoop.Driver σ) :
    ∀ (fuel : Nat) (s : σ), (ofDriver d).frameGo fuel s = d.frameGo fuel s := by
  intro fuel; induction fuel with
  | zero => intro s; rfl
  | succ fuel ih =>
    intro s
    simp only [frameGo, L4Factoidal.EventLoop.Driver.frameGo]
    split <;> simp_all [ofDriver, bind, pure]

theorem ofDriver_frame (d : L4Factoidal.EventLoop.Driver σ) (s : σ) :
    (ofDriver d).frame s = d.frame s := by
  simp only [frame, L4Factoidal.EventLoop.Driver.frame, ofDriver_frameGo]; rfl

/-- In `Id`, this loop is `EventLoop.Driver.advanceGo`. -/
theorem ofDriver_advanceGo (d : L4Factoidal.EventLoop.Driver σ) (target : Nat) :
    ∀ (fuel : Nat) (slot : Option Nat) (s : σ) (frames : Nat),
      (ofDriver d).advanceGo target fuel slot s frames = d.advanceGo target fuel slot s frames := by
  intro fuel; induction fuel with
  | zero => intro slot s frames; rfl
  | succ fuel ih =>
    intro slot s frames
    simp only [advanceGo, L4Factoidal.EventLoop.Driver.advanceGo]
    first
      | (simp only [ih, ofDriver_frame]; rfl)
      | (simp only [ih, ofDriver_frame]; simp [ofDriver, bind, pure])
      | (split <;> (try split) <;> (try split) <;> (try split) <;> simp [ih, ofDriver_frame, ofDriver, bind, pure])

end DriverM

/-- The session as a host of the event loop: the loop's runs are callbacks in the
module, on the machine. -/
def Session.driver : DriverM Prog Session :=
  { loop := Session.loop, setLoop := Session.setLoop, run := Session.runTaskP }

/-- Run the event loop until the virtual clock is at `target` and no task waits, or
`maxTasks` steps have run. The clock stops at each due timer, in order. At most one
animation frame batch runs, at the last frame time the advance reaches
(`EventLoop.frameSlot`; `EventLoop.Driver.advanceGo_frames`): a host that fell behind
gets one frame with the latest time, as a browser does, not every missed frame. The
answer says whether the loop ran out of steps. -/
def Session.advanceP (s : Session) (target : Nat) (maxTasks : Nat := 100000) : Prog (Session × Bool) := do
  let slot := L4Factoidal.EventLoop.frameSlot s.loop.clock target s.lastFrame
  let (s, frames, out) ← Session.driver.advanceGo target maxTasks slot s 0
  return ({ s with lastFrame := if frames == 0 then s.lastFrame else slot }, out)

/-- No task, timer or animation frame waits. -/
def Session.quiet (s : Session) : Bool :=
  s.loop.idle && s.loop.timers.isEmpty && s.loop.frames.isEmpty

/-- Run the loop until nothing waits (no task, armed timer or animation frame), or the
virtual clock has moved `budgetMs`, or `maxTasks` steps. The answer says whether it
ended quiet. -/
def Session.settleP (s : Session) (budgetMs : Nat) (maxTasks : Nat := 100000) : Prog (Session × Bool) := do
  let stop := s.loop.clock + budgetMs
  let mut s := s
  for _ in [0:maxTasks] do
    let (s', _) ← s.advanceP s.loop.clock 1000
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
      let (s', _) ← s.advanceP stop 1000
      return (s', s'.quiet)
    let (s', _) ← s.advanceP next 1000
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
def Session.clickP (s : Session) (node : Nat) : Prog Session := do
  let target := elementOf s.host.dom.dom node
  let s := s.setLoop (s.loop.queueTask .userInteraction 0 (some { type := "click", target }))
  return (← s.advanceP s.loop.clock).1


/-- Dispatch an event of the user agent with the pointer data `init` (a JSON object the
prelude reads with `node_query` op 16), then the microtask checkpoint. -/
def Session.dispatchWithP (s : Session) (target : Nat) (type init : String) : Prog (Session × Bool) := do
  let s := { s with host := { s.host with event := init } }
  let (s, prevented) ← s.dispatchP target type
  return ({ s with host := { s.host with event := "" } }, prevented)

def Session.setPointer (s : Session) (p : PointerState) : Session := { s with host := { s.host with pointer := p } }

/-- The nearest inclusive ancestor of `a` that is also an inclusive ancestor of `b` (HTML
"click": the press and the release on different elements click their common ancestor). -/
def commonAncestor (d : Arena) (a b : Nat) : Nat :=
  let pb := path d b
  ((path d a).find? fun k => k < d.size && (d.get k).type == .element && pb.contains k).getD b

/-- The frame of a time: the clock in 16 ms steps, as `nextFrame`. -/
def frameOf (clock : Nat) : Nat := clock / 16

/-- `pointermove`, then `mousemove` unless the press's `pointerdown` was canceled. -/
def Session.moveNowP (s : Session) (target : Nat) (init : String) : Prog Session := do
  let p := s.host.pointer
  let (s, _) ← s.dispatchWithP target "pointermove" init
  let s ← if p.pressed.isSome && p.canceled then pure s else (·.1) <$> s.dispatchWithP target "mousemove" init
  return s.setPointer { s.host.pointer with moveFrame := some (frameOf s.loop.clock), pending := none }

/-- The move that waits, when its frame has come. -/
def Session.flushMoveP (s : Session) : Prog Session :=
  match s.host.pointer.pending with
  | some (target, init) => if s.host.pointer.moveFrame == some (frameOf s.loop.clock) then pure s else s.moveNowP target init
  | none => pure s

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
def Session.pointerP (s : Session) (kind : PointerKind) (node : Nat) (init : String) : Prog Session := do
  let target := elementOf s.host.dom.dom node
  let (s, _) ← s.advanceP s.loop.clock
  let s ← if kind == .move then pure s else s.flushMoveP
  let p := s.host.pointer
  let s ← match kind with
    | .down => do
      let (s, prevented) ← s.dispatchWithP target "pointerdown" init
      let s ← if prevented then pure s else (·.1) <$> s.dispatchWithP target "mousedown" init
      pure (s.setPointer { s.host.pointer with pressed := some target, canceled := prevented })
    | .up => do
      let (s, _) ← s.dispatchWithP target "pointerup" init
      let s ← if p.pressed.isSome && p.canceled then pure s else (·.1) <$> s.dispatchWithP target "mouseup" init
      let s ← match p.pressed with
        | some pressed => (·.1) <$> s.dispatchWithP (commonAncestor s.host.dom.dom pressed target) "click" init
        | none => pure s
      pure (s.setPointer { s.host.pointer with pressed := none, canceled := false })
    | .cancel => do
      let (s, _) ← s.dispatchWithP target "pointercancel" init
      pure (s.setPointer { s.host.pointer with pressed := none, canceled := false, pending := none })
    | .move =>
      if p.moveFrame == some (frameOf s.loop.clock) then pure (s.setPointer { p with pending := some (target, init) })
      else s.moveNowP target init
  return (← s.advanceP s.loop.clock).1

/-- The viewport moved to `width` by `height` CSS pixels: reads lay out again, and `resize`
is dispatched at the window (CSSOM View §13.1) when the size changed. -/
def Session.resizeP (s : Session) (width height : Nat) : Prog Session := do
  let r := s.host.reads
  if r.width == width && r.height == height then return s
  let s := { s with host := { s.host with reads := { r with width, height, kept := none } } }
  return (← s.dispatchP windowId "resize").1

/-- Layouts made for the reads of scripts. -/
def Session.layouts (s : Session) : Nat := s.host.reads.layouts

/-! ### The same actions with the interpreter -/

def Session.i32 (s : Session) (fa : Nat) (args : Array Value) : Session × Option Nat := (s.i32P fa args).runLocal
def Session.put (s : Session) (b : ByteArray) : Session × Option Nat := (s.putP b).runLocal
def Session.freePtr (s : Session) (p : Nat) : Session := (s.freeP p).runLocal
def Session.result (s : Session) (p : Nat) : Session × Nat × String := (s.resultP p).runLocal
def Session.block (s : Session) (fa : Nat) (args : Array Value) : Session × Nat × String := (s.blockP fa args).runLocal
def Session.eval (s : Session) (src : String) : Session × Nat × String := (s.evalP src).runLocal
def Session.setUrl (s : Session) (url : String) : Session := (s.setUrlP url).runLocal
def Session.setScript (s : Session) (node : Int) : Session := (s.setScriptP node).runLocal
def Session.runJobs (s : Session) : Session := s.runJobsP.runLocal
def Session.dispatchOnly (s : Session) (target : Nat) (type : String) : Session × Bool := (s.dispatchOnlyP target type).runLocal
def Session.dispatch (s : Session) (target : Nat) (type : String) : Session × Bool := (s.dispatchP target type).runLocal
def Session.callbackOnly (s : Session) (cb : Nat) (target : Int) (arg : Nat) : Session := (s.callbackOnlyP cb target arg).runLocal
def Session.callback (s : Session) (cb : Nat) (target : Int) (arg : Nat) : Session := (s.callbackP cb target arg).runLocal
def Session.runTask (s : Session) (r : L4Factoidal.EventLoop.Run) : Session := (s.runTaskP r).runLocal
def Session.advance (s : Session) (target : Nat) (maxTasks : Nat := 100000) : Session × Bool := (s.advanceP target maxTasks).runLocal
def Session.settle (s : Session) (budgetMs : Nat) (maxTasks : Nat := 100000) : Session × Bool := (s.settleP budgetMs maxTasks).runLocal
def Session.click (s : Session) (node : Nat) : Session := (s.clickP node).runLocal
def Session.dispatchWith (s : Session) (target : Nat) (type init : String) : Session × Bool := (s.dispatchWithP target type init).runLocal
def Session.moveNow (s : Session) (target : Nat) (init : String) : Session := (s.moveNowP target init).runLocal
def Session.flushMove (s : Session) : Session := s.flushMoveP.runLocal
def Session.pointer (s : Session) (kind : PointerKind) (node : Nat) (init : String) : Session := (s.pointerP kind node init).runLocal
def Session.resize (s : Session) (width height : Nat) : Session := (s.resizeP width height).runLocal

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

/-- The exports a page needs, in this order: the eight of `Exports`, then `_initialize`,
`qjs_new` and `qjs_page_mode`. On the AOT path an export's number is its place here. -/
def exportNames : Array String :=
  #["qjs_alloc", "qjs_free", "qjs_eval", "qjs_call", "qjs_dispatch", "qjs_run_job", "qjs_page",
    "qjs_release", "_initialize", "qjs_new", "qjs_page_mode"]

/-- The exports, each found by `find`. -/
def Exports.of (find : String → Except String Nat) : Except String (Exports × Nat × Nat × Nat) := do
  let alloc ← find "qjs_alloc"
  let free ← find "qjs_free"
  let evalF ← find "qjs_eval"
  let callF ← find "qjs_call"
  let dispatchF ← find "qjs_dispatch"
  let runJob ← find "qjs_run_job"
  let page ← find "qjs_page"
  let release ← find "qjs_release"
  let init ← find "_initialize"
  let qnew ← find "qjs_new"
  let mode ← find "qjs_page_mode"
  return ({ alloc, free, eval := evalF, call := callF, dispatch := dispatchF, runJob, page, release }, init, qnew, mode)

/-- After instantiation: `_initialize`, `qjs_new` (the prelude) and page mode. -/
def Session.initP (s : Session) (init qnew mode : Nat) : Prog (Except String Session) := do
  let (s, o) ← s.runP init #[]
  if let .values _ := o then pure () else return .error s!"_initialize: {o.describe}"
  let (s, r) ← s.i32P qnew #[]
  if r != some 0 then return .error s!"qjs_new: {r} {s.errors.toList}"
  let (s, _) ← s.runP mode #[.i32 1]
  return .ok s

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
  let (fx, init, qnew, mode) ← Exports.of fa
  let host : Host := { dom := { dom, commandLimit := lim.commands, logLimit := lim.logs } }
  let s : Session := { store := st, inst := ia, mem := memOf st ia, bindings := bs, host, fx, limits := lim }
  (s.initP init qnew mode).runLocal

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

/-- The document of an `iframe` with no `src` (HTML §7.3.1 "about:blank"): an HTML
document with `html`, `head` and `body` and no doctype. -/
def aboutBlank : Arena := Id.run do
  let el := fun (d : Arena) (name : String) => d.create { type := .element, doc := 0, ns := some L4Factoidal.DOM.htmlNS, lname := name }
  let d : Arena := { nodes := #[{ type := .document, doc := 0 }] }
  let (d, html) := el d "html"
  let d := d.linkChild 0 html none
  let (d, head) := el d "head"
  let d := d.linkChild html head none
  let (d, body) := el d "body"
  return d.linkChild html body none

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

/-- The arena of a page with its frames' documents grafted in (`Dom.graft`), and each
`iframe` element with the root of its document. -/
def graftFrames (dom : Arena) (frames : Array (Nat × Arena)) : Arena × Array (Nat × Nat) := Id.run do
  let mut dom := dom
  let mut framed : Array (Nat × Nat) := #[]
  for (el, doc) in frames do
    if el < dom.size then
      let (d, root) := dom.graft doc
      dom := d
      framed := framed.push (el, root)
  return (dom, framed)

/-- The page's scripts, `DOMContentLoaded`, the frames' and the window's `load` events,
and the tasks due at time 0, on a session that holds the page's arena. -/
def Session.startP (s : Session) (url : String) (scripts : Array (Nat × String)) (framed : Array (Nat × Nat)) :
    Prog Session := do
  let s := (← s.runP s.fx.page #[.i32 2, .i32 0, .i32 0]).1
  let mut s ← s.setUrlP url
  for (node, src) in scripts do
    s ← s.setScriptP node
    let (s', status, text) ← s.evalP src
    s := if status == 1 then s'.fail text else s'
    s ← s.runJobsP
  s ← s.setScriptP (-1)
  s := (← s.dispatchP 0 "DOMContentLoaded").1
  for (el, _) in framed do
    s := s.setLoop (s.loop.queueTask .domManipulation 0 (some { type := "load", target := el }))
  s := s.setLoop (s.loop.queueTask .domManipulation 0 (some { type := "load", target := windowId }))
  return (← s.advanceP 0).1

/-- Start a page: its classic scripts in document order (each with the current script set
and a microtask checkpoint after it), `DOMContentLoaded` at the document, then the `load`
event at the window as a task, and the tasks that are due at time 0. `scripts` are the
script element's node and its source. `frames` are the `iframe` elements whose documents
the embedder loaded, each with its document parsed on its own: each joins the page's arena
(`Dom.graft`), and its `load` event at the `iframe` is a task before the window's. The
frames share the page's script realm. -/
def start (m : Module') (dom : Arena) (url : String) (scripts : Array (Nat × String)) (lim : Limits := {})
    (frames : Array (Nat × Arena) := #[]) (reads : Reads := {}) (time : ScriptClock := {}) : Except String Session := do
  let (dom, framed) := graftFrames dom frames
  let s : Session ← match m.base with
    | some b =>
      let domHost : DomHost := { dom, commandLimit := lim.commands, logLimit := lim.logs, frames := framed, framing := lim.frames }
      let host : Host := { dom := domHost, reads, time }
      pure { b with host, limits := lim, steps := 0 }
    | none => do
      let s ← instantiatePage m dom lim
      pure { s with host := { s.host with dom := { s.host.dom with frames := framed, framing := lim.frames }, reads, time } }
  let s := { s with host := { s.host with dom := { s.host.dom with gpu := L4Factoidal.PageGpu.State.empty lim.gpuPage } } }
  return (s.startP url scripts framed).runLocal

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
