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
import L4Factoidal.WasmVM.Hosts.WebApi
import L4Factoidal.WasmVM.Hosts.PageWasm
import L4Factoidal.WasmVM.Hosts.DomOps
import L4Factoidal.Rendering.MediaQuery
import L4Factoidal.EventLoop.Model
import L4Factoidal.EventLoop.Dispatch
import L4Factoidal.HTML.FrameSessions
import L4Factoidal.JSON.Serialize
import L4Factoidal.WebDriver.Input
import L4Factoidal.WebDriver.Touch
import L4Factoidal.WebDriver.Capture
import L4Factoidal.Rendering.Animation.Api
import L4Factoidal.Rendering.Animation.Computed

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
  /-- The element the pointer is over (the target of its last event): what the boundary
  events (over, out, enter, leave) of the next event compare with. -/
  over : Option Nat := none
  /-- The last press, for the click count (`WebDriver.Input.clickCount`). -/
  last : Option L4Factoidal.WebDriver.Input.LastPress := none
  /-- The default action of the last `keydown` for the host, until the host reads it:
  `true` when no listener canceled it and the key did not go to a text control or an
  editing host (`Dom.keyEdits`), so the host may scroll the page for it. -/
  keyDefault : Option Bool := none
  /-- The touch points on the surface (`WebDriver.Touch`), from the touch pointers. -/
  touches : L4Factoidal.WebDriver.Touch.Surface := {}
  /-- Pointer capture (`WebDriver.Capture`), and the pointers other than the mouse that are
  down (the mouse, pointer 1, is always active). -/
  capture : L4Factoidal.WebDriver.Capture.State := {}
  active : List Nat := []
  deriving Inhabited, Repr

/-- The answers of one layout: node, op and the op's text (empty for most ops). -/
abbrev Answers := Nat → Nat → String → Option String

/-- What the cascade of one measure leaves for the next measure of the page: the rules
in their buckets, the element state (with no animated value) and the style of every
node. Only a page with no shadow tree, at text scale 1, whose rules do not read the
`style` attribute has one (`CSS.restyleWith`). -/
structure Carry where
  index : L4Factoidal.Rendering.CSS.RuleIndex
  rules : List L4Factoidal.Rendering.CSS.Rule
  state : L4Factoidal.Rendering.CSS.ElementState
  styles : Array L4Factoidal.Rendering.CSS.Computed
  /-- No rule has `:has()` (`CSS.attributesReachParentOnly`): a write of an element's
  `class` then changes styles in the subtree of its parent alone. -/
  parentOnly : Bool := false

/-- The layout reads of scripts: the engine's layout of an arena at a viewport (CSS
pixels) with the values of the page's animations, as answers. The engine gives the
function; it lays out when a read first asks.

The last argument is what an earlier measure left with the nodes to style again: the
caller says by it that the arena, the viewport and the animated values are those of that
measure except for the `style` attribute and the animated values of those nodes, and
for the `class` of their children when the measure's rules have no `:has()`
(`Carry.parentOnly`); their subtrees are styled again, the rest is taken as it was. With none the cascade is of the
whole document. The second answer is what this measure leaves (none when the page is not
one a `Carry` is for); asking for it makes the cascade. -/
abbrev Measure := Arena → Nat → Nat → List L4Factoidal.Rendering.Animation.Override → Option (Carry × List Nat) →
  Answers × Thunk (Option Carry)

/-- What a page with animations keeps of its last measure: the styles with no animated
value and with them, the animated values, the elements that declare an animation or a
transition, and the timeline time and the count of script changes of animations it was
made at. -/
structure StyleKept where
  width : Nat
  height : Nat
  base : Option Carry
  final : Option Carry
  overrides : List L4Factoidal.Rendering.Animation.Override
  candidates : List Nat
  now : Int
  epoch : Nat

structure Reads where
  measure : Option Measure := none
  width : Nat := 800
  height : Nat := 600
  /-- DOM writes served so far: a layout is of one version. -/
  version : Nat := 0
  /-- The answers of the layout of `version` at the viewport, once a read asked. -/
  kept : Option (Nat × Answers) := none
  /-- The timeline time of the kept answers: a page with animations is laid out again
  when the time moved (`Host.measured`). -/
  keptNow : Int := 0
  /-- Layouts made for reads. -/
  layouts : Nat := 0
  /-- Of a page with animations: its last measure (`Host.measureNow`). -/
  styleKept : Option StyleKept := none
  /-- The elements to style again: those whose `style` attribute was written since the
  last measure and the parents of those whose `class` was, when nothing else of the
  document was written since; none after any other write. -/
  styleWrites : Option (List Nat) := none
  /-- One of `styleWrites` is there for a `class` written under it: the rules that match
  in its subtree may differ, not only the declarations of the element itself. -/
  styleSubtrees : Bool := false
  /-- The version that the last write which may change a style made (`Reads.wrote`, not
  neutral): a layout of that version or a later one has the styles of the document as it
  is (`Host.frameStyles`). -/
  styleWriteAt : Nat := 0
  /-- The version `styleWrites` is exact for: `Reads.wrote` keeps it at `version`. A write
  that raises `version` by any other way leaves it behind, and the next measure is then
  of the whole document (`Host.measureNow`): a new write path that does not go through
  `Reads.wrote` costs a cascade, never a stale style. -/
  styleVersion : Nat := 0
  /-- Changes of animations by scripts (`animOp`). -/
  animEpoch : Nat := 0
  /-- A script listens for an animation or a transition event (`animationEventTypes`):
  the styles of the page are then brought up to date in its frames (`Host.frameStyles`),
  as a rendering update does, so that an animation or a transition starts, and its
  events come, with no layout read by a script. -/
  animEvents : Bool := false
  /-- The fonts, SVG path parser and images Canvas 2D draws with (the engine's). -/
  canvasEnv : L4Factoidal.PageCanvas.Env := {}
  deriving Inhabited

/-- The reads after a write of the document: a new version. `style` is the element
whose `style` attribute alone the write set, or, with `subtree`, the parent of the
element whose `class` alone it set; `neutral` a write that changes nothing a style reads
(a timer, a listener). Any other write forgets the noted elements, and so does a long
list of them. -/
def Reads.wrote (r : Reads) (style : Option Nat := none) (neutral : Bool := false) (subtree : Bool := false) : Reads :=
  -- the noted elements, when they are exact for the version before this write
  let noted := if r.styleVersion == r.version then r.styleWrites else none
  { r with
    version := r.version + 1
    styleVersion := r.version + 1
    styleWrites :=
      if neutral then noted
      else match style, noted with
        | some n, some ns => if ns.contains n then some ns else if ns.length ≥ 32 then none else some (n :: ns)
        | _, _ => none
    styleSubtrees := if neutral then r.styleSubtrees else r.styleSubtrees || subtree
    styleWriteAt := if neutral then r.styleWriteAt else r.version + 1 }

/-- Kind: safety of the partial restyle. Says: after a write that is neither of a `style`
attribute nor neutral, no element is noted: the next measure styles the whole document.
Does not say: that every write of the engine calls `wrote` (a write that only raises
`version` leaves `styleVersion` behind, which `Host.measureNow` reads the same way). -/
theorem Reads.wrote_other (r : Reads) (subtree : Bool) : (r.wrote none false subtree).styleWrites = none := by
  simp [Reads.wrote]

/-- Kind: safety of the partial restyle. Says: a write noted for a subtree (a `class`
write) leaves the mark that a subtree is to be read again, and no later write takes the
mark away: only a measure does (`Host.measureNow`). Does not say: that the mark is exact
(it may stay after the noted elements are forgotten, which costs nothing). -/
theorem Reads.wrote_subtree (r : Reads) (n : Nat) :
    (r.wrote (some n) false true).styleSubtrees = true := by
  simp [Reads.wrote]

/-- Kind: cost. Says: a neutral write (a timer, a listener, a change of an animation by a
script) does not move the version of the last style write: a frame after it alone makes
no style change (`Host.frameStyles`). -/
theorem Reads.wrote_neutral (r : Reads) (style : Option Nat) (subtree : Bool) :
    (r.wrote style true subtree).styleWriteAt = r.styleWriteAt := by
  simp [Reads.wrote]

/-- Kind: liveness. Says: a write that is not neutral is the last style write of the new
version, so a layout kept from before it is behind it. -/
theorem Reads.wrote_style (r : Reads) (style : Option Nat) (subtree : Bool) :
    (r.wrote style false subtree).styleWriteAt = (r.wrote style false subtree).version := by
  simp [Reads.wrote]

theorem Reads.wrote_keeps_subtree (r : Reads) (style : Option Nat) (neutral subtree : Bool)
    (h : r.styleSubtrees = true) : (r.wrote style neutral subtree).styleSubtrees = true := by
  cases neutral <;> simp [Reads.wrote, h]

/-- Kind: bookkeeping. Says: every `wrote` leaves the noted elements exact for the new
version, and the version one higher. -/
theorem Reads.wrote_version (r : Reads) (style : Option Nat) (neutral subtree : Bool) :
    (r.wrote style neutral subtree).styleVersion = (r.wrote style neutral subtree).version ∧
    (r.wrote style neutral subtree).version = r.version + 1 := by
  simp [Reads.wrote]

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
  /-- The web APIs over Lean (`Hosts.WebApi`): streaming decoders and the generator. -/
  web : Hosts.WebApi.State := {}
  /-- The page's WebAssembly (`Hosts.PageWasm`): its own WasmVM store, empty until a
  script uses the JavaScript API. -/
  wasm : Hosts.PageWasm.State := {}
  /-- The slots of the shadow trees with their assigned nodes when `node_query` op 33 last
  answered (`DOM.Dom.slotAssignments`): what "signal a slot change" compares with. -/
  slots : Array (Nat × Array Nat) := #[]
  /-- Messages this session posted to a frame's session or to its parent's
  (`HTML.FrameSessions`), which the host has not taken. -/
  outbox : Array L4Factoidal.HTML.FrameSessions.Message := #[]
  /-- The rules of the page's style sheets for the editing commands (`Hosts.Dom.editOp`),
  with the sheet text they were parsed from: parsed again only when the text changes. -/
  editIndex : Option (String × L4Factoidal.Rendering.CSS.RuleIndex) := none
  /-- The page's animations (`Rendering.Animation.Engine`): empty, and never read by a
  layout, on a page that animates nothing. -/
  anim : L4Factoidal.Rendering.Animation.State := {}
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
  commands : Nat := Hosts.Dom.maxCommands
  /-- The page number of this session's GPU objects (`L4Factoidal.PageGpu.Gid.page`). -/
  gpuPage : Nat := 0
  /-- The embedder replays the page's GPU commands on a GPU (`PageGpu.State.replay`). -/
  gpuReplay : Bool := false
  /-- Console lines a page may write (`Hosts.Dom.State.logLimit`). -/
  logs : Nat := 1024
  /-- Nested browsing contexts for `iframe` elements (`Hosts.Dom.State.framing`). -/
  frames : Bool := false
  /-- The embedder loads frames' URLs (`Hosts.Dom.State.hostLoads`). -/
  hostLoads : Bool := false
  /-- Entropy from the embedder's own generator, which seeds the page's
  `crypto.getRandomValues` (`Hosts.WebApi`); empty leaves it off. -/
  entropy : ByteArray := ByteArray.empty
  /-- The encoding the host decoded the page with (`document.characterSet`); "" if unknown. -/
  encoding : String := ""
  /-- The embedder performs the page's requests (`Net.Xhr`): `network:true` of `start`. -/
  network : Bool := false
  /-- The browser that runs the Hub enforces CORS (`Net.PageFetch.Page.hostCors`). -/
  hostCors : Bool := false
  /-- The address the embedder loaded the page from, when it knows it: a special-purpose one
  makes the page local (`Net.PageFetch.Page.ofUrl`). -/
  pageAddress : String := ""
  /-- The `Referrer-Policy` field of the page's response, when the embedder gave it (several
  fields joined with commas); "" for none: the default policy (`Net.Xhr.policyOfHeader`). -/
  referrerPolicy : String := ""
  /-- The page's Content Security Policy as the embedder delivered it: the
  `Content-Security-Policy` fields of its response (joined with commas), the
  `Content-Security-Policy-Report-Only` fields, and the contents of its `meta` elements
  (`HTML.CspSource.metaText`); the session's policy is `Net.Xhr.cspOf` of the three. -/
  csp : String := ""
  cspReportOnly : String := ""
  cspMeta : String := ""
  /-- Violations found before the session began (the scripts the policy did not let run,
  `HTML.CspSource.filterScripts`): reported with the first of the session's own. -/
  cspViolations : Array String := #[]
  /-- Sync requests: the run is redone with these answers (`Net.Xhr.syncAnswers`). -/
  syncAnswers : Array L4Factoidal.Net.PageFetch.Answer := #[]
  /-- The embedder can undo and redo a run (not the AOT path). -/
  syncOk : Bool := false
  /-- The page's scripts may make a sync request in a later action (`Net.Xhr.State.mayBlock`). -/
  mayBlock : Bool := false
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
   ("request_frame", 1), ("cancel_frame", 1), ("web_api", 6), ("wasm_call", 8)]

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

/-- The event path through shadow trees (`DOM.Dom.eventPath`, DOM §2.9), target first, then
the window when the last node is a document. Any target that is not a node is a path of
one. -/
def shadowPath (d : Arena) (target : Nat) (composed : Bool) : List Nat :=
  if target ≥ d.size then [target] else
  let p := d.eventPath target composed
  match p.getLast? with
  | some k => if (d.get k).type == .document then p ++ [windowId] else p
  | none => p

/-- The target a listener at `node` sees (DOM §2.5 "retarget"): the window sees the
target retargeted against its document; -1 when none. -/
def targetFor (d : Arena) (path : List Nat) (target node : Nat) : Int :=
  if target ≥ d.size then target else
  let at_ := if node == windowId then (path.reverse.find? (· < d.size)).getD 0 else node
  if at_ ≥ d.size then target else
  match d.retarget target at_ with
  | some t => t
  | none => -1

def phaseCode : L4Factoidal.EventLoop.Dispatch.Phase → Nat
  | .capturing => 1 | .atTarget => 2 | .bubbling => 3

/-- `dispatch_plan`: `[path length, path (target first)..., then for each listener call
of `Dispatch.plan`: callback, node, phase + 8 × capture, depth]`. Flags: 1 the event bubbles,
2 it is composed, 4 the path goes through shadow trees (`shadowPath`, `Dispatch.planAt`)
and each listener call has a fifth number, the target it sees (`targetFor`, DOM §2.5;
-1 for none). Without 4, the answer is the first form on the tree's parents alone. -/
def planList (h : Host) (target : Nat) (type : String) (flags : Nat) : Array Int :=
  let bubbles := flags % 2 == 1
  let ls := (h.listeners.toList.filter (·.type == type)).map fun l =>
    ({ node := l.target, capture := l.capture, callback := l.callback } : L4Factoidal.EventLoop.Dispatch.Listener)
  if flags / 4 % 2 == 0 then
    let p := path h.dom.dom target
    let visits := L4Factoidal.EventLoop.Dispatch.plan p.reverse ls bubbles
    (#[p.length] ++ p.toArray ++ (visits.toArray.flatMap fun v =>
      #[v.callback, v.node, phaseCode v.phase + (if v.capture then 8 else 0), v.depth])).map Int.ofNat
  else
    let d := h.dom.dom
    let p := shadowPath d target (flags / 2 % 2 == 1)
    let rootFirst := p.reverse
    -- A path through no shadow root stays in the target's tree: every listener sees the
    -- target, and only the target is at the target (the plan of `Dispatch.plan`), so the
    -- retargeting walks are skipped.
    let crossing := p.any (fun k => k < d.size && d.isShadowRoot k)
    let targetFor := fun (d : Arena) (p : List Nat) (target node : Nat) =>
      if crossing then targetFor d p target node else (target : Int)
    let atTarget := fun (k : Nat) => if crossing then (let node := rootFirst.getD k 0; targetFor d p target node == node)
      else k + 1 == rootFirst.length
    let visits := L4Factoidal.EventLoop.Dispatch.planAt rootFirst atTarget ls bubbles
    #[(p.length : Int)] ++ (p.toArray.map Int.ofNat) ++ (visits.toArray.flatMap fun v =>
      #[(v.callback : Int), v.node, phaseCode v.phase + (if v.capture then 8 else 0), v.depth, targetFor d p target v.node])

section
variable {M : Type} [LinearMemory M]

/-- The imports of `foafnaut_dom` that change nothing a layout reads. -/
def readOnlyImports : List String :=
  ["get_element_by_id", "document_element", "tag_name", "text_content_get", "get_attribute", "node_info",
   "node_string", "node_children", "node_query", "console_log", "gpu_command"]

/-- The imports that write nothing a style reads: a layout is made again after them as
after any write, with the styles it had. -/
def styleNeutralImports : List String := ["add_event_listener", "set_timer", "clear_timer"]

/-- A write of `foafnaut_dom` that changes nothing in a document's tree: a new node, a
clone, or a change of a node that is in no document's tree and stays in none (an
insertion there of a node that is itself in none). The styles and the layout of every
document are as they were. `a` gives the import's i32 arguments: the node, or the parent
then the node. -/
def detachedWrite (dom : Arena) (nm : String) (a : Nat → Nat) : Bool :=
  let off := fun (n : Nat) => n < dom.size && !dom.connected n
  if nm == "create_element" || nm == "clone_node" then true
  -- kind 15 of `create_node` is a write of a frame
  else if nm == "create_node" then a 0 % 16 != 15
  else if nm == "set_attribute" || nm == "remove_attribute" || nm == "text_content_set" || nm == "remove_child" then
    off (a 0)
  else if nm == "append_child" || nm == "insert_before" || nm == "replace_child" then off (a 0) && off (a 1)
  else false

/-- Kind: safety of the partial restyle. Says: a write whose first node (the node written,
or the parent written into) is in a document's tree is never taken as changing nothing
there, whatever the import, except the three that only make a node. Does not say: that
`Hosts.Dom.serve` changes only what the import's name says. -/
theorem detachedWrite_connected (dom : Arena) (nm : String) (a : Nat → Nat)
    (h : dom.connected (a 0) = true) (h1 : nm ≠ "create_element") (h2 : nm ≠ "clone_node")
    (h3 : nm ≠ "create_node") : detachedWrite dom nm a = false := by
  have e1 : (nm == "create_element") = false := beq_eq_false_iff_ne.mpr h1
  have e2 : (nm == "clone_node") = false := beq_eq_false_iff_ne.mpr h2
  have e3 : (nm == "create_node") = false := beq_eq_false_iff_ne.mpr h3
  simp only [detachedWrite, e1, e2, e3, h]
  simp

/-- The name and value pairs of a `getComputedStyle` answer (measure op 20). -/
def stylePairs (text : Option String) : List (String × String) :=
  match text with
  | some t => L4Factoidal.Rendering.Animation.Css.ofCascadedText t
  | none => []

/-- What the animation engine reads of the page at a style change: `base` is the layout
with no animated value, `prev` the answers of the style change before (the before-change
style of CSS Transitions 1 §3). Measure ops: 20 the computed style, 24 an element's
cascaded animation and transition longhands, 25 the text of the sheets, 27 the computed
value of "property U+0000 value" on an element, 28 the elements that declare an
animation or a transition, 29 the computed value of the longhand named, 26 the
declarations of the element's rules and `style` attribute as one text, with "names"
the longhands they declare (U+0000 between them), with "rules" the rules' part of the
text, with "style" the longhands of the `style` attribute and their values. -/
def animationAccess (dom : Arena) (base : Answers) (prev : Option Answers) (candidates : Option (List Nat) := none) :
    L4Factoidal.Rendering.Animation.Access :=
  { connected := fun n => n < dom.size && dom.connected n
    base := fun n p => base n 29 p
    prev := fun n p => prev.bind fun f => f n 29 p
    changed := fun n => match prev with
      | some f =>
        -- the layout profile's properties that differ (op 20 lists them in one order), and
        -- the properties declared for the element then or now (op 26) that differ
        let profile := ((stylePairs (base n 20 "")).zip (stylePairs (f n 20 ""))).filterMap fun ((k, v), (k', v')) =>
          if k == k' && v != v' then some k else none
        -- (only when the declarations the element's cascade reads changed: op 26 with no text)
        if base n 26 "" == f n 26 "" then profile else
        -- with the same rules and a font, colour and flow that stayed: the longhands that
        -- the two `style` attributes declare differently, and no other
        let narrowed := L4Factoidal.Rendering.Animation.Computed.styleAttributeDiff
          ((f n 26 "style").getD "") ((base n 26 "style").getD "")
        let narrow := base n 26 "rules" == f n 26 "rules" &&
          !(profile ++ narrowed).any L4Factoidal.Rendering.Animation.Computed.reachesOthers
        let declared := if narrow then narrowed
          else ((((base n 26 "names").getD "").splitOn "\x00") ++ (((f n 26 "names").getD "").splitOn "\x00")).eraseDups
        (profile ++ declared.filter fun p => p != "" && base n 29 p != f n 29 p).eraseDups
      | none => []
    compute := fun n p v => base n 27 (p ++ "\x00" ++ v)
    decls := fun n => L4Factoidal.Rendering.Animation.Css.ofCascadedText ((base n 24 "").getD "")
    candidates := match candidates with
      | some cs => cs
      | none => (((base 0 28 "").getD "").splitOn " ").filterMap String.toNat?
    sheet := fun _ => (base 0 25 "").getD ""
    longhands := L4Factoidal.Rendering.Animation.Css.longhandsOf }

/-- Ask for an animation frame for the page's animations, once (`Animation.frameHandle`:
the page's script objects answer it with op 67). It is the first callback of its frame:
"update animations and send events" comes before the animation frame callbacks of the
page (HTML §8.1.7.3 "update the rendering"), so a callback of the page reads the
animations as that frame's time has them. -/
def Host.askAnimationFrame (h : Host) : Host :=
  if h.anim.frameAsked then h else
  let (loop, id) := { h.loop with clock := h.time.sync h.loop.clock }.requestFrame L4Factoidal.Rendering.Animation.frameHandle
  let loop := { loop with frames := loop.frames.filter (·.id == id) ++ loop.frames.filter (·.id != id) }
  { h with loop, anim := { h.anim with frameAsked := true } }

/-- The nodes of the subtrees on `stack`, at most `fuel` of them: none when there are
more. -/
def subtreesGo (dom : Arena) : Nat → List Nat → List Nat → Option (List Nat)
  | _, [], out => some out
  | 0, _ :: _, _ => none
  | fuel + 1, n :: rest, out => subtreesGo dom fuel ((dom.children n).toList ++ rest) (n :: out)

/-- The most nodes that a write of a `class` styles again on its own: with more under
the parent, the styles are made whole (`Host.measureNow`). -/
def subtreeLimit : Nat := 512

/-- The nodes of the subtrees of `roots`, when they are at most `subtreeLimit`. -/
def subtreesWithin (dom : Arena) (roots : List Nat) : Option (List Nat) :=
  subtreesGo dom subtreeLimit roots []

theorem subtreesGo_length (dom : Arena) (fuel : Nat) (stack out ns : List Nat)
    (h : subtreesGo dom fuel stack out = some ns) : ns.length ≤ out.length + fuel := by
  induction fuel generalizing stack out with
  | zero =>
    cases stack with
    | nil => simp [subtreesGo] at h; subst h; simp
    | cons a t => simp [subtreesGo] at h
  | succ k ih =>
    cases stack with
    | nil => simp [subtreesGo] at h; subst h; omega
    | cons a t =>
      simp only [subtreesGo] at h
      have := ih _ _ h
      simp at this
      omega

/-- Kind: resource bound. Says: the nodes that the partial path reads for `class` writes
are at most `subtreeLimit`, whatever the document (with more, there is no such list and
the measure is of the whole document). Does not say: a bound for `style` attribute
writes, whose elements' subtrees are styled again whatever their size, or for the whole
cascade. -/
theorem subtreesWithin_length (dom : Arena) (roots ns : List Nat)
    (h : subtreesWithin dom roots = some ns) : ns.length ≤ subtreeLimit := by
  have := subtreesGo_length dom subtreeLimit roots [] ns h
  simpa using this

/-- Node `n` is one of `roots` or has one as an ancestor. -/
def underAny (dom : Arena) (roots : List Nat) (n : Nat) : Bool := Id.run do
  if roots.isEmpty then return false
  let mut cur := some n
  for _ in [0:dom.size + 1] do
    match cur with
    | none => return false
    | some c => if roots.contains c then return true else cur := (dom.get c).parent
  return false

/-- A layout of the current arena and viewport for reads, counted. A page with an
animation, or with an animation or transition declaration (measure op 28), has a style
change first (`Animation.styleChange`), and its layout takes the animated values
(`Animation.overrides`); any other page takes neither step.

Such a page keeps its styles (`StyleKept`). When only `style` attributes and `class`
attributes were written since its last measure (`Reads.styleWrites`), the cascade is of
the subtrees of those elements, and of the parents of the elements whose `class` was
written when no rule has `:has()` and those subtrees are small (`subtreesWithin`;
`Measure`'s last argument), and, when no time passed and no script changed an
animation, so are the style change (`Animation.styleChangeOn`) and the effect stacks
(`Animation.overridesWhere`): the animated values of the other elements are those of the
last measure. When only the time moved (a frame of a page whose animations run), there is
no style change: the effect stacks at the new time, and the animated elements styled again. A script that writes one element's style and reads a computed value, again
and again, then pays for that element each time and not for the document. -/
def Host.measureNow (h : Host) : Host × Option Answers :=
  match h.reads.measure with
  | none => (h, none)
  | some m =>
    let dom := h.dom.dom
    let w := h.reads.width
    let ht := h.reads.height
    -- the last measure, when it is one to go on from: with the elements written since
    -- (with a `class` written: the nodes under the noted elements, when the rules and their
    -- count allow the partial path)
    let last : Option (StyleKept × List Nat × List Nat) :=
      match h.reads.styleKept, h.reads.styleWrites with
      | some k, some nodes =>
        if k.width == w && k.height == ht && k.base.isSome && h.reads.styleVersion == h.reads.version then
          if !h.reads.styleSubtrees then some (k, nodes, nodes)
          else if (k.base.map (·.parentOnly)) == some true then (subtreesWithin dom nodes).map fun under => (k, nodes, under)
          else none
        else none
      | _, _ => none
    let (base, baseLeft) := m dom w ht [] (last.bind fun (k, nodes, _) => k.base.map fun c => (c, nodes))
    let keep := fun (h : Host) (f : Answers) (kept : Option StyleKept) =>
      ({ h with reads := { h.reads with
          kept := some (h.reads.version, f), keptNow := h.anim.now, layouts := h.reads.layouts + 1,
          styleKept := kept, styleWrites := kept.map fun _ => [], styleSubtrees := false,
          styleVersion := h.reads.version } }, some f)
    -- with the style change made and the animated values known: the layout with them
    let finish := fun (h : Host) (anim : L4Factoidal.Rendering.Animation.State)
        (ovs : List L4Factoidal.Rendering.Animation.Override) (candidates : List Nat) (fromFinal : Option (Carry × List Nat)) =>
      -- the events and the pending tasks of what the style change started need a frame
      let h : Host := { h with anim := L4Factoidal.Rendering.Animation.noteAnimated anim ovs }
      let h := if L4Factoidal.Rendering.Animation.needsFrame anim then h.askAnimationFrame else h
      let baseCarry := baseLeft.get
      let (final, finalLeft) :=
        if ovs.isEmpty then (base, baseLeft)
        else m dom w ht ovs (match fromFinal with
          | some c => some c
          -- from the styles with no animated value: the animated elements again
          | none => baseCarry.map fun c => (c, (ovs.map (·.node)).eraseDups))
      keep h final (some { width := w, height := ht, base := baseCarry, final := finalLeft.get, overrides := ovs,
                           candidates, now := h.anim.now, epoch := h.reads.animEpoch })
    match last with
    | none =>
      let candidates := (((base 0 28 "").getD "").splitOn " ").filterMap String.toNat?
      if h.anim.idle && candidates.isEmpty then keep h base none
      else
        let ac := animationAccess dom base (h.reads.kept.map (·.2)) (some candidates)
        let anim := L4Factoidal.Rendering.Animation.styleChange h.anim ac
        finish h anim (L4Factoidal.Rendering.Animation.overrides anim ac) candidates none
    | some (k, nodes, under) =>
      let ac := animationAccess dom base (h.reads.kept.map (·.2)) (some k.candidates)
      -- of the elements whose declarations may differ (the written ones; with a `class`
      -- written, all under the noted ones), those that declare an animation or a transition now
      let declare := (under.filter fun n => n < dom.size && dom.connected n && !(ac.decls n).isEmpty).eraseDups
      let candidates := k.candidates.filter (fun c => !under.contains c) ++ declare
      let ac := { ac with candidates }
      if k.now == h.anim.now && k.epoch == h.reads.animEpoch then
        let dirty := underAny dom nodes
        let anim := L4Factoidal.Rendering.Animation.styleChangeOn h.anim ac dirty (candidates.filter dirty)
        let ovs := k.overrides.filter (fun o => !dirty o.node) ++
          L4Factoidal.Rendering.Animation.overridesWhere anim ac dirty
        if anim.idle && candidates.isEmpty then keep h base none
        else finish h anim ovs candidates (k.final.map fun c => (c, nodes))
      else if nodes.isEmpty && k.epoch == h.reads.animEpoch then
        -- only the time moved: no declaration and no style changed, so style starts and
        -- cancels nothing (a style change would find every animation as it is); the effect
        -- stacks are those of the new time
        finish h h.anim (L4Factoidal.Rendering.Animation.overrides h.anim ac) candidates none
      else
        -- a script changed an animation: every animation again
        let anim := L4Factoidal.Rendering.Animation.styleChange h.anim ac
        if anim.idle && candidates.isEmpty then keep h base none
        else finish h anim (L4Factoidal.Rendering.Animation.overrides anim ac) candidates none

/-- The answers of the layout of the current arena and viewport: kept until a write or a
new viewport, so reads after no write share one layout, and a read after writes makes
one (as a browser's forced layout). With animations the answers are also of one timeline
time. -/
def Host.measured (h : Host) : Host × Option Answers :=
  match h.reads.kept with
  | some (v, f) =>
    if v == h.reads.version && (h.anim.idle || h.reads.keptNow == h.anim.now) then (h, some f) else h.measureNow
  | none => h.measureNow

/-- The event types of CSS Animations 1 §5 and CSS Transitions 1 §6, with the prefixed
types of Compatibility §3.3. -/
def animationEventTypes : List String :=
  ["animationstart", "animationend", "animationiteration", "animationcancel",
   "transitionrun", "transitionstart", "transitionend", "transitioncancel",
   "webkitAnimationStart", "webkitAnimationEnd", "webkitAnimationIteration", "webkitTransitionEnd"]

/-- After a write of a page: `listens` says the write is a new listener for one of
`animationEventTypes`, `neutral` that it changes nothing a style reads. A page with such
a listener gets an animation frame after each write that may change a style (and after
the listener itself): the frame makes the style change (`Host.frameStyles`). HTML §8.1.7.3
"update the rendering" does that in every frame of every page; here only where a script
can see the difference without reading a style or a layout, which is by these events. -/
def Host.afterWrite (h : Host) (listens neutral : Bool) : Host :=
  let h := if listens then { h with reads := { h.reads with animEvents := true } } else h
  if h.reads.animEvents && (listens || !neutral) then h.askAnimationFrame else h

theorem Host.askAnimationFrame_reads (h : Host) : h.askAnimationFrame.reads = h.reads := by
  unfold Host.askAnimationFrame
  split <;> rfl

/-- Kind: cost (a page that does not use the feature pays nothing). Says: on a page with
no listener for an animation or transition event, a write that adds none leaves the host
as it is: no frame is asked for, nothing is measured. Does not say: what such a page pays
when a script reads a layout (`Host.measureNow`). -/
theorem Host.afterWrite_quiet (h : Host) (neutral : Bool) (hq : h.reads.animEvents = false) :
    h.afterWrite false neutral = h := by
  simp [Host.afterWrite, hq]

/-- Kind: liveness of the events. Says: after a new listener for one of the event types
the page is marked, whatever it was. -/
theorem Host.afterWrite_listens (h : Host) (neutral : Bool) :
    (h.afterWrite true neutral).reads.animEvents = true := by
  simp [Host.afterWrite, Host.askAnimationFrame_reads]

/-- The style part of a frame's rendering update, for a page whose script listens for an
animation or transition event: when something was written since the last measure, the
styles are made again, which starts and cancels the animations and transitions of the
written elements (`Host.measureNow`). A frame in which nothing that a style reads was
written since the last measure (`Reads.styleWriteAt`) measures nothing here: the time
alone, a timer, a listener or a script's change of an animation asks for no style change. -/
def Host.frameStyles (h : Host) : Host :=
  if !h.reads.animEvents then h else
  match h.reads.kept with
  | some (v, _) => if h.reads.styleWriteAt ≤ v then h else h.measureNow.1
  | none => h.measureNow.1

/-- Kind: cost. Says: when the kept layout is of the last style write or later, a frame
measures nothing, whatever the page listens for. -/
theorem Host.frameStyles_fresh (h : Host) (v : Nat) (f : Answers) (hk : h.reads.kept = some (v, f))
    (hv : h.reads.styleWriteAt ≤ v) : h.frameStyles = h := by
  unfold Host.frameStyles
  split
  · rfl
  · simp [hk, hv]

/-- Kind: cost. Says: a frame of a page with no such listener makes no style change and
no measure of its own. -/
theorem Host.frameStyles_quiet (h : Host) (hq : h.reads.animEvents = false) : h.frameStyles = h := by
  simp [Host.frameStyles, hq]

/-- The document timeline's time is the event loop's clock when a task or a frame
starts: it does not move while a script runs (Web Animations 1 §4.3: the timeline time is
that of the last "update animations and send events"). -/
def Host.tickTimeline (h : Host) : Host :=
  let t := L4Factoidal.Rendering.Animation.Fix.ofInt (Int.ofNat h.loop.clock)
  if h.anim.now == t then h else { h with anim := { h.anim with now := t } }

/-- `node_query` ops 60 to 69, the Web Animations interfaces (`Rendering.Animation.Api`;
requests and answers are JSON): 60 a new effect on element `node` (a node that is not an
element: no target); 61 a change of effect `node`; 62 a read of effect `node`; 63 a
new animation; 64 a method or setter of animation `node`; 65 the state of animation
`node` with its acts; 66 the animations of element `node` (`q` "subtree": and of its
descendants; node 0 with "subtree": of the document), after a style change; 67 the
frame's part ("update animations": the events of CSS animations and transitions, and
whether another frame is needed; with `q` "ask": ask for a frame); 68 the timeline time in
ms; 69 which names of a keyframe object are animatable properties. A change of an
animation is a change of what a layout reads. -/
def animOp (h : Host) (node op : Nat) (q : String) : Host × Except Int String :=
  let supports := L4Factoidal.Rendering.CSS.supportsDeclaration
  let dom := h.dom.dom
  let bump := fun (h : Host) (anim : L4Factoidal.Rendering.Animation.State) =>
    -- a change of what a layout reads that writes nothing of the document (`Reads.wrote`, neutral)
    { h with anim, reads := { (h.reads.wrote none true) with animEpoch := h.reads.animEpoch + 1 } }
  let api := L4Factoidal.Rendering.Animation.Api.createEffect
  match op with
  | 60 =>
    let target := if node < dom.size && (dom.get node).type == .element then some node else none
    let (anim, r) := api supports h.anim target q
    (bump h anim, .ok r)
  | 61 =>
    let (anim, r) := L4Factoidal.Rendering.Animation.Api.setEffect supports h.anim node q
    (bump h anim, .ok r)
  | 62 => (h, .ok (L4Factoidal.Rendering.Animation.Api.getEffect h.anim node q))
  | 63 =>
    let (anim, r) := L4Factoidal.Rendering.Animation.Api.createAnim h.anim q
    (bump h anim, .ok r)
  | 64 =>
    let (anim, r) := L4Factoidal.Rendering.Animation.Api.callAnim h.anim node q
    (bump h anim, .ok r)
  | 65 =>
    let (anim, r) := L4Factoidal.Rendering.Animation.Api.snapshot h.anim node
    ({ h with anim }, .ok r)
  | 66 =>
    -- the style change first: CSS animations and transitions exist after it
    let (h, _) := h.measured
    let dom := h.dom.dom
    let subtree := q == "subtree"
    let under := fun (t : Nat) => Id.run do
      -- `node` is `t` or an ancestor of it
      let mut cur := some t
      for _ in [0:dom.size + 1] do
        match cur with
        | none => return false
        | some c => if c == node then return true else cur := (dom.get c).parent
      return false
    let wanted := fun (t : Nat) =>
      t < dom.size && dom.connected t && (if subtree then node == 0 || under t else t == node)
    (h, .ok (L4Factoidal.Rendering.Animation.Api.listAnimations h.anim wanted))
  | 67 =>
    if q == "ask" then (h.askAnimationFrame, .ok "{}")
    else
      -- the styles of the writes since the last measure first (only on a page that listens
      -- for the events of animations): what they start is ticked in this frame
      let h := h.frameStyles
      let ticked := L4Factoidal.Rendering.Animation.tick h.anim (fun n => n < dom.size && dom.connected n)
      -- a layout is of the animations' state: a frame that changed none keeps it
      let same := (List.range ticked.anims.size).all fun i =>
        (ticked.anims[i]?).map (·.player) == (h.anim.anims[i]?).map (·.player)
      let (anim, r) := L4Factoidal.Rendering.Animation.Api.frameAnswer ticked
      let h := if same then { h with anim } else bump h anim
      let h := if L4Factoidal.Rendering.Animation.needsFrame anim then h.askAnimationFrame else h
      (h, .ok r)
  | 68 => (h, .ok (L4Factoidal.Rendering.Animation.Fix.format h.anim.now))
  | 69 => (h, .ok (L4Factoidal.Rendering.Animation.Api.animatableNames supports q))
  | _ => (h, .error (-2))

/-- The `node_query` ops that `Hosts.Dom.serve` answers: below 16, and 30 to 32 (slots, the
composed path, the postMessage origin check). Ops 100 to 199 are `Hosts.Dom.domOp`'s; the
others (16 to 29, 33, 34, 41, 42, 200 and up) are this module's (`pageQuery`, `postToFrame`,
`mediaAnswer`, `captureOp`). -/
def domQueryOps (op : Nat) : Bool := op < 16 || (op ≥ 30 && op ≤ 32)

/-- The `node_query` ops that `Hosts.Dom.domOp` answers: 100 to 199. -/
def domOpRange (op : Nat) : Bool := op ≥ 100 && op < 200

/-- The `node_query` op of a document's referrer source (`HTML.ReferrerSource`, `DomOps`). -/
def referrerSourceOp : Nat := 173

/-- Kind: correctness theorem. Says: no op of `getComputedStyle` (200 + k, the k-th computed
property; 100200 + k, the computed value; 200 + 1000000 × (i + 1) + k, a pseudo-element's) is
routed to `Hosts.Dom.domOp`: the two ranges are disjoint. -/
theorem domOpRange_computed (k : Nat) : domOpRange (200 + k) = false := by
  simp only [domOpRange, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega

/-- Kind: correctness theorem. Says: the referrer source op is routed to `Hosts.Dom.domOp` and
is not a `getComputedStyle` op. -/
theorem referrerSourceOp_route : domOpRange referrerSourceOp = true ∧ ∀ k, referrerSourceOp ≠ 200 + k := by
  refine ⟨by decide, fun k => ?_⟩
  simp only [referrerSourceOp]; omega

/-- The `node_query` op of pointer capture (`captureOp`). It was 220, the number of the
twentieth computed property (`border-right-width`): `getComputedStyle(el).borderRightWidth`
answered `NotFoundError` on every page. -/
def pointerCaptureOp : Nat := 42

/-- The `node_query` ops of `getComputedStyle` and of the resolved grid values: 200 and up
(200 + k, the k-th computed property; 100200 + k, the computed value; 200 + 1000000 × (i + 1)
+ k, a pseudo-element's). No other op may take a number here. -/
def computedRange (op : Nat) : Bool := op ≥ 200

/-- Kind: correctness theorem. Says: the pointer capture op is not a `getComputedStyle` op (no
200 + k), and is none of the ops that `Hosts.Dom.serve`, `animOp` (60 to 69) or
`Hosts.Dom.domOp` answer, so `serveExtra` routes it to `captureOp` alone. -/
theorem pointerCaptureOp_route :
    computedRange pointerCaptureOp = false ∧ (∀ k, pointerCaptureOp ≠ 200 + k) ∧
    domQueryOps pointerCaptureOp = false ∧ domOpRange pointerCaptureOp = false ∧
    ¬ (pointerCaptureOp ≥ 60 ∧ pointerCaptureOp < 70) := by
  refine ⟨by decide, fun k => ?_, by decide, by decide, by decide⟩
  simp only [pointerCaptureOp]; omega

/-- Kind: correctness theorem. Says: every op that `Hosts.Dom.serve` or `Hosts.Dom.domOp`
answers, and the referrer source and pointer capture ops, are below the computed range: an
op of `getComputedStyle` reaches the layout reads and nothing else. -/
theorem computedRange_others (op : Nat)
    (h : domQueryOps op = true ∨ domOpRange op = true ∨ op = referrerSourceOp ∨ op = pointerCaptureOp) :
    computedRange op = false := by
  simp only [domQueryOps, domOpRange, referrerSourceOp, pointerCaptureOp, computedRange,
    Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_false_iff_not] at *
  omega

/-- The most messages a session may have waiting for the host. -/
def maxOutbox : Nat := 4096

/-- `node_query` op 34: `postMessage` to the window of a frame with a session of its own
(`node` its `iframe` element) or, in a frame's session, to its parent (`node` the window);
`q` is "targetOrigin U+0000 data" (the data serialized). The origin check is
`HTML.Frames.postMessageDelivers`: "1" queued in the outbox, "0" not delivered, -12 a
target origin that is not a URL, -2 no such frame. -/
def postToFrame (h : Host) (node : Nat) (q : String) : Host × Except Int String :=
  match q.splitOn "\x00" with
  | targetOrigin :: rest =>
    let data := "\x00".intercalate rest
    let d := h.dom
    let src := Hosts.Dom.pageOrigin d
    let target : Option (Nat × Bool × L4Factoidal.HTML.Frames.Origin) :=
      if node == windowId then d.parentOrigin.map fun o => (0, true, o)
      else if node < d.dom.size && Hosts.Dom.frameOwner (d.dom.get node) then
        some (node, false, (Hosts.Dom.elementFrame d node).origin)
      else none
    match target with
    | none => (h, .error (-2))
    | some (el, up, o) =>
      match L4Factoidal.HTML.Frames.postMessageDelivers src o targetOrigin with
      | none => (h, .error (-12))
      | some false => (h, .ok "0")
      | some true =>
        if h.outbox.size ≥ maxOutbox then (h, .error (-5)) else
        ({ h with outbox := h.outbox.push { frame := el, toParent := up, data, origin := src.serialize } }, .ok "1")
  | [] => (h, .error (-2))

/-- `node_query` ops served here: 16 the init of the event being dispatched; 17 a node's
layout, "x y w h left top width height" (border box in the page, then the client box);
18 an SVG element's bounding box in its user space, "x y w h"; 19 the viewport, "w h";
22 the device pixel ratio (`devicePixelRatio`), which the measure answers from its layout
request with no layout, so it is not counted as one (dprfix);
33 the slots whose assigned nodes changed since the last op 33 (DOM §4.2.2.5 "signal a
slot change"), as decimal node numbers separated by spaces. -/
def pageQuery (h : Host) (node op : Nat) : Host × Except Int String :=
  match op with
  | 16 => (h, if h.event.isEmpty then .error (-1) else .ok h.event)
  | 19 => (h, .ok s!"{h.reads.width} {h.reads.height}")
  | 22 => (h, match h.reads.measure with
      | some m => match (m h.dom.dom h.reads.width h.reads.height [] none).1 node 22 "" with
        | some r => .ok r
        | none => .error (-1)
      | none => .error (-2))
  | 34 => (h, .error (-2))
  | 33 =>
    let d := h.dom.dom
    let roots := ((List.range d.size).filter (d.isShadowRoot ·)).toArray
    let now := d.slotAssignments roots
    ({ h with slots := now }, .ok (" ".intercalate ((L4Factoidal.DOM.Dom.slotChanges h.slots now).toList.map toString)))
  | _ =>
    let (h, f) := h.measured
    match f with
    | some f => (h, match f node op "" with | some r => .ok r | none => .error (-1))
    | none => (h, .error (-2))

/-- The rules of the page's style sheets for an editing command: the text of the sheets
comes from the layout reads (measure op 40, no layout); the index of the last text is kept. -/
def Host.editRules (h : Host) : Host × L4Factoidal.Rendering.CSS.RuleIndex :=
  let (h, f) := h.measured
  let sheet := match f with
    | some f => (f 0 40 "").getD ""
    | none => ""
  match h.editIndex with
  | some (text, ix) =>
    if text == sheet then (h, ix)
    else let ix := Hosts.Dom.editIndex sheet; ({ h with editIndex := some (sheet, ix) }, ix)
  | none => let ix := Hosts.Dom.editIndex sheet; ({ h with editIndex := some (sheet, ix) }, ix)

/-- The media environment of a layout (`MediaQuery.Env`): the media type, and the viewport
in CSS px, `width` by `rows` device pixels at the text scale `percent` (a text scale of 200%
on a 1600 px wide window is an 800 px wide viewport, as a page zoom of 200% is). Pages are
drawn in light colours: `prefers-color-scheme: dark` does not hold. The one maker of the
environment: the layout's sheets (`WebDocument.mediaEnv`) and `matchMedia` both take it. -/
def mediaEnvOf (medium : String) (width rows percent : Nat) : L4Factoidal.Rendering.MediaQuery.Env :=
  let css := fun (n : Nat) => n.toFloat * 100 / (max 1 percent).toFloat
  {medium, width := some (css width), height := some (css rows), dark := some false}

/-- `matchMedia` (CSSOM View §4.2, `node_query` op 41): whether the media query list `q`
holds in the media environment of the page's layout. The layout request says the
environment's inputs (measure op 41: the media type, the viewport in CSS pixels and the
zoom, with no layout), `mediaEnvOf` makes the environment as the layout does, and
`MediaQuery.holds` is the evaluator of the sheets. "1" or "0"; "" for a list that can not
be read. A session with no layout request answers -2. -/
def mediaAnswer (h : Host) (q : String) : Except Int String :=
  match h.reads.measure with
  | none => .error (-2)
  | some m =>
    match (m h.dom.dom h.reads.width h.reads.height [] none).1 0 41 "" with
    | none => .error (-1)
    | some text =>
      match text.splitOn " " with
      | [medium, w, r, p] =>
        match w.toNat?, r.toNat?, p.toNat? with
        | some w, some r, some p =>
          .ok (match L4Factoidal.Rendering.MediaQuery.holds (mediaEnvOf medium w r p) q with
            | some true => "1"
            | some false => "0"
            | none => "")
        | _, _, _ => .error (-1)
      | _ => .error (-1)

/-- A placeholder for the DOM state while an import holds it. -/
def emptyDomHost : DomHost := { dom := {} }

/-- `setPointerCapture`, `releasePointerCapture` and `hasPointerCapture` (node_query op 42,
`pointerCaptureOp`)
on element `node`: "" when done, "NotFoundError" for a pointer that is not active,
"InvalidStateError" for an element that is not connected; `hasPointerCapture` answers "1" or
"0". A pointer that is not in the active buttons state is not captured (§10.1). -/
def captureOp (h : Host) (node : Nat) (q : String) : Host × String :=
  let p := h.pointer
  match q.splitOn " " with
  | [verb, n] =>
    match n.toNat? with
    | none => (h, "NotFoundError")
    | some id =>
      let active := id == 1 || p.active.contains id
      if verb == "h" then (h, if p.capture.has id node then "1" else "0")
      else if !active then (h, "NotFoundError")
      else if verb == "s" then
        if !(L4Factoidal.DOM.Dom.connected h.dom.dom node) then (h, "InvalidStateError")
        else if (if id == 1 then p.pressed.isSome else true) then
          ({ h with pointer := { p with capture := p.capture.set id node } }, "")
        else (h, "")
      else if verb == "r" then ({ h with pointer := { p with capture := p.capture.release id node } }, "")
      else (h, "NotFoundError")
  | _ => (h, "NotFoundError")

/-- Serve one `foafnaut_dom` import, or `env.emscripten_notify_memory_growth`. -/
def serveExtra (mem : Nat) (mo nm : String) (args : Array Value) (h : Host) (st : StoreOf M) :
    Host × StoreOf M × HostResult :=
  if mo != Hosts.Dom.moduleName then (h, st, .values #[]) else
  let a := Hosts.Dom.arg args
  match nm with
  | "gpu_command" =>
    -- Canvas 2D (L4Factoidal.PageCanvas; docs/designissues/2026-11-08-canvas-2d.md): a batch
    -- of drawing commands, or a query; WebGPU and WebGL ops are below 200.
    if a 0 < L4Factoidal.PageCanvas.Wire.batchOp then
      let (dom, st, r) := Hosts.Dom.serve mem nm args h.dom st
      ({ h with dom }, st, r)
    else if a 3 > L4Factoidal.PageGpu.maxBuffer + 65536 then (h, st, Hosts.Dom.ret (-5)) else
    match st.readMem mem (a 2) (a 3) with
    | .error _ => (h, st, Hosts.Dom.codeOrTrap (-8))
    | .ok b =>
      if a 0 == L4Factoidal.PageCanvas.Wire.wordsOp then
        -- Pixels as bytes (the `gpuBytes` native, an ArrayBuffer): the answer counts bytes.
        match L4Factoidal.PageCanvas.Wire.callWords h.dom.canvas (a 0) b with
        | .error _ => (h, st, Hosts.Dom.ret (-1))
        | .ok bytes =>
          let (st, r) := Hosts.Dom.putOut mem st (a 4) (a 5) bytes
          (h, st, r)
      else
      let (canvas, answer) := L4Factoidal.PageCanvas.Wire.call h.dom.canvas h.reads.canvasEnv (a 0) b
      let (st, r) := Hosts.Dom.answerStr mem st (a 4) (a 5) (.ok answer)
      ({ h with dom := { h.dom with canvas } }, st, r)
  | "node_query" =>
    if domQueryOps (a 1) then
      let (dom, st, r) := Hosts.Dom.serve mem nm args h.dom st
      ({ h with dom }, st, r)
    else if a 1 ≥ 60 && a 1 < 70 then
      -- the Web Animations interfaces (`animOp`)
      match Hosts.Dom.readStr mem st (a 2) (a 3) Hosts.Dom.maxString with
      | .error e => (h, st, Hosts.Dom.codeOrTrap e)
      | .ok q =>
        let (h, answer) := animOp h (a 0) (a 1) q
        let (st, r) := Hosts.Dom.answerStr mem st (a 4) (a 5) answer
        (h, st, r)
    else if domOpRange (a 1) then
      -- ranges, selection, traversal, CharacterData, a document's referrer source (173; it
      -- was 210, the number of the tenth computed property: ops 200 and up are
      -- `getComputedStyle`'s, one a property)
      -- (`Hosts.Dom.domOp`)
      match Hosts.Dom.readStr mem st (a 2) (a 3) Hosts.Dom.maxString with
      | .error e => (h, st, Hosts.Dom.codeOrTrap e)
      | .ok q =>
        if Hosts.Dom.editOps.contains (a 1) then
          -- editing (`Hosts.Dom.editOp`): the algorithms read styles, so they get the rules of
          -- the page's style sheets (`Host.editRules`, no layout); 175 changes the tree
          let (h, ix) := if a 1 ≥ 177 then (h, Hosts.Dom.editIndex "") else h.editRules
          let ds := h.dom
          let h := { h with dom := emptyDomHost }
          let (dom, answer) := Hosts.Dom.editOp ds ix (a 0) (a 1) q
          let reads := if a 1 == 175 then h.reads.wrote else h.reads
          let (st, r) := Hosts.Dom.answerStr mem st (a 4) (a 5) answer
          ({ h with dom, reads }, st, r)
        else
        let ds := h.dom
        let h := { h with dom := emptyDomHost }
        let (dom, answer) := Hosts.Dom.domOp ds (a 0) (a 1) q
        let reads := if Hosts.Dom.treeOps.contains (a 1) then h.reads.wrote else h.reads
        let (st, r) := Hosts.Dom.answerStr mem st (a 4) (a 5) answer
        ({ h with dom, reads }, st, r)
    else
      if a 1 == pointerCaptureOp then
        -- pointer capture (Pointer Events 3 §10.1): `q` is "s ID", "r ID" or "h ID"
        (match Hosts.Dom.readStr mem st (a 2) (a 3) Hosts.Dom.maxString with
        | .error e => (h, st, Hosts.Dom.codeOrTrap e)
        | .ok q =>
          let (h, answer) := captureOp h (a 0) q
          let (st, r) := Hosts.Dom.answerStr mem st (a 4) (a 5) (.ok answer)
          (h, st, r))
      else if a 1 == 34 then
        (match Hosts.Dom.readStr mem st (a 2) (a 3) Hosts.Dom.maxString with
        | .error e => (h, st, Hosts.Dom.codeOrTrap e)
        | .ok q =>
          let (h, answer) := postToFrame h (a 0) q
          let (st, r) := Hosts.Dom.answerStr mem st (a 4) (a 5) answer
          (h, st, r))
      else if a 1 == 41 then
        -- matchMedia: the query text against the layout's media environment (`mediaAnswer`)
        (match Hosts.Dom.readStr mem st (a 2) (a 3) Hosts.Dom.maxString with
        | .error e => (h, st, Hosts.Dom.codeOrTrap e)
        | .ok q =>
          let (st, r) := Hosts.Dom.answerStr mem st (a 4) (a 5) (mediaAnswer h q)
          (h, st, r))
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
      let (st, r) := Hosts.Dom.answerList mem st (a 4) (a 5) (.ok ((planList h (a 0) type (a 3)).map fun x => (x % 4294967296).toNat))
      (h, st, r)
  | "set_timer" =>
    let (loop, id) := { h.loop with clock := h.time.sync h.loop.clock }.setTimer (a 0) (a 1) (a 2 != 0)
    ({ h with loop }, st, Hosts.Dom.ret id)
  | "clear_timer" => ({ h with loop := h.loop.clearTimer (a 0) }, st, Hosts.Dom.ret 0)
  | "request_frame" =>
    let (loop, id) := { h.loop with clock := h.time.sync h.loop.clock }.requestFrame (a 0)
    ({ h with loop }, st, Hosts.Dom.ret id)
  | "cancel_frame" => ({ h with loop := h.loop.cancelFrame (a 0) }, st, Hosts.Dom.ret 0)
  | "web_api" =>
    if a 0 == 140 then
      -- WebNN (`WebNN.GpuRun`): the page's GPU state is lent for the call, so a graph on the GPU
      -- path makes its objects in the page's own table, under the page's quotas; the host
      -- commands it makes join the page's (`Hosts.Dom.maxGpuOut` bounds them as a page's own).
      let nn := { h.web.nn with page := h.dom.gpu, out := #[], room := Hosts.Dom.maxGpuOut - h.dom.gpuOut.size }
      let dom := { h.dom with gpu := {} }
      let (web, st, r) := Hosts.WebApi.serve mem args { h.web with nn } st dom.dom
      let nn := web.nn
      ({ h with web := { web with nn := { nn with page := {}, out := #[] } },
                dom := { dom with gpu := nn.page, gpuOut := dom.gpuOut ++ nn.out } }, st, r)
    else
    let (web, st, r) := Hosts.WebApi.serve mem args h.web st h.dom.dom
    ({ h with web }, st, r)
  | "wasm_call" =>
    -- The page's WebAssembly: its store is taken out of the host while it runs, so the
    -- runs change it in place.
    let w := h.wasm
    let h := { h with wasm := {} }
    let (w, st, r) := Hosts.PageWasm.serve mem args w st
    ({ h with wasm := w }, st, r)
  | _ =>
    -- a write of an element's `style` attribute is noted as that (`Reads.styleWrites`), and
    -- a write of its `class` as one under its parent; a write that changes nothing in a
    -- document's tree (`detachedWrite`) changes no style
    let styleOf : Option (Nat × Bool) :=
      if nm == "set_attribute" || nm == "remove_attribute" then
        match Hosts.Dom.readStr mem st (a 1) (a 2) 8 with
        | .ok name =>
          if name == "style" then some (a 0, false)
          else if name == "class" then (h.dom.dom.get (a 0)).parent.map fun p => (p, true)
          else none
        | .error _ => none
      else none
    let neutral := styleNeutralImports.contains nm || detachedWrite h.dom.dom nm a
    let reads := if readOnlyImports.contains nm then h.reads
      else h.reads.wrote (styleOf.map (·.1)) neutral (styleOf.any (·.2))
    -- a new listener for an animation or transition event (`Host.afterWrite`)
    let listens := nm == "add_event_listener" &&
      (match Hosts.Dom.readStr mem st (a 1) (a 2) 24 with
        | .ok name => animationEventTypes.contains name
        | .error _ => false)
    -- the DOM state leaves the host for the call, so that a change of the arena is in place
    -- (`Hosts.Dom.change`)
    let ds := h.dom
    let h := { h with dom := emptyDomHost }
    let (dom, st, r) := Hosts.Dom.serve mem nm args ds st
    let h := { h with dom, reads }
    ((if readOnlyImports.contains nm then h else h.afterWrite listens neutral), st, r)

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
  -- The page's WebAssembly runs in this run's host calls: its instructions are script time
  -- too, from the call that ran them on.
  let wasm0 := h.wasm.steps
  for _ in [0:lim.hostCalls] do
    match o with
    | .hostCall id vs k =>
      let (h', st', r) := serve mem bs id vs { h with time := h.time.atRun h.loop.clock (steps + n + (h.wasm.steps - wasm0)) } st
      h := h'
      let (st'', o', n') := resumeSteps st' k r { budget with fuel := lim.fuel - n }
      st := st''; o := o'; n := n + n'
    | _ => break
  n := n + (h.wasm.steps - wasm0)
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
  -- enter and leave do not bubble, can not be canceled and are not composed (UI Events
  -- §5.3, Pointer Events 3 §4.2)
  if type == "mouseenter" || type == "mouseleave" || type == "pointerenter" || type == "pointerleave" then 0
  -- these bubble and are composed, and can not be canceled
  else if type == "pointercancel" || type == "gotpointercapture" || type == "lostpointercapture" then 5
  else if type == "click" || type == "auxclick" || type == "dblclick" || type == "contextmenu" || type == "wheel"
      || type.startsWith "mouse" || type.startsWith "pointer" then 7
  -- keys and `beforeinput` bubble, can be canceled and are composed; `input` can not be canceled
  else if type == "keydown" || type == "keyup" || type == "keypress" || type == "beforeinput" then 7
  else if type == "input" then 5
  -- touch events bubble and are composed; `touchcancel` can not be canceled (Touch Events §5)
  else if type == "touchstart" || type == "touchmove" || type == "touchend" then 7
  else if type == "touchcancel" then 5
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
  let s := { s with host := s.host.tickTimeline }
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
    if s.quiet && !s.host.web.net.waiting && s.host.web.net.syncWanted.isNone then return (s, true)
    -- A request waits for the embedder: give the session back (not quiet).
    if s.host.web.net.waiting || s.host.web.net.syncWanted.isSome then return (s, false)
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

/-- The init of the `message` event of a message from another session (HTML §9.3.3, the
posted message task): the data as its serialization, the source's origin, and the frame
it came through (-1 from the parent). -/
def messageInit (m : L4Factoidal.HTML.FrameSessions.Message) : String :=
  let q := fun (t : String) => "\"" ++ L4Factoidal.JSON.escapeString t ++ "\""
  "{\"data\":" ++ q m.data ++ ",\"origin\":" ++ q m.origin ++ ",\"frame\":" ++
    (if m.toParent then toString m.frame else "-1") ++ "}"

/-- Deliver a message from another session: a `message` event at the window. -/
def Session.deliverP (s : Session) (m : L4Factoidal.HTML.FrameSessions.Message) : Prog Session := do
  let (s, _) ← s.dispatchWithP windowId "message" (messageInit m)
  s.runJobsP

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
  let host : Host := { dom := { dom, commandLimit := lim.commands, logLimit := lim.logs }, web := { entropy := lim.entropy, docEncoding := lim.encoding } }
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

/-- A frame's navigation ends with document `source` ("" is `about:blank`;
`Hosts.Dom.attachDocument`): its classic scripts run in the page's realm, in document order,
each with the current script set (so `document` is the frame's document while it runs) and
a microtask checkpoint after it; then the `load` event at the `iframe` is a task, and the
window's when it was waiting for this frame. `scripts` are the script elements of `source`
parsed on its own, with their sources. A frame of another origin, or one whose sandbox
forbids scripts, runs none here (`Hosts.Dom.realmScripts`, asked after the document is
attached: the origin is the one of the URL it came from). -/
def Session.loadFrameP (s : Session) (el : Nat) (source : String) (scripts : Array (Nat × String))
    (xml : Bool := false) (responseUrl : Option String := none) : Prog Session := do
  let (dom, root) := Hosts.Dom.attachDocument s.host.dom el source xml responseUrl
  -- asked of the frame as it is after this navigation (`Hosts.Dom.realmScripts`)
  let scripts := Hosts.Dom.realmScripts dom el scripts
  let mut s := { s with host := { s.host with dom } }
  if let some root := root then
    for (node, src) in scripts do
      s ← s.setScriptP (node + root : Nat)
      let (s', status, text) ← s.evalP src
      s := if status == 1 then s'.fail text else s'
      s ← s.runJobsP
    s ← s.setScriptP (-1)
  s := s.setLoop (s.loop.queueTask .networking 0 (some { type := "load", target := el }))
  -- the last frame that the window's load event waited for
  if s.host.dom.loadWaits && !Hosts.Dom.framesLoading s.host.dom then
    s := { s with host := { s.host with dom := { s.host.dom with loadWaits := false } } }
    s := s.setLoop (s.loop.queueTask .domManipulation 0 (some { type := "load", target := windowId }))
  return s

def Session.loadFrame (s : Session) (el : Nat) (source : String) (scripts : Array (Nat × String))
    (xml : Bool := false) : Session :=
  (s.loadFrameP el source scripts xml).runLocal

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
  -- The page's own `iframe` elements get their browsing contexts before its scripts run
  -- (HTML §4.8.5); a page with none pays one look at its nodes. Their initial about:blank
  -- documents are there before any script runs, and that load is not an event scripts see.
  let d0 := { s.host.dom with url }
  let web := { s.host.web with net := { enabled := s.limits.network, page := L4Factoidal.Net.PageFetch.Page.ofUrl url s.limits.hostCors s.limits.pageAddress, client := url, policy := L4Factoidal.Net.Xhr.policyOfHeader s.limits.referrerPolicy, csp := L4Factoidal.Net.Xhr.cspOf s.limits.csp s.limits.cspReportOnly s.limits.cspMeta, violations := s.limits.cspViolations, syncOk := s.limits.syncOk, syncAnswers := s.limits.syncAnswers, mayBlock := s.limits.mayBlock } }
  let s := { s with host := { s.host with web } }
  let d0 := if d0.framing && d0.dom.nodes.any Hosts.Dom.frameOwner then
    let d1 := Hosts.Dom.connectFrames d0 #[0]
    { d1 with navigations := d1.navigations.filter (!·.2.isEmpty) } else d0
  let s := { s with host := { s.host with dom := d0 } }
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
  -- The window's load event waits for frames still loading (`Hosts.Dom.State.loadWaits`).
  if Hosts.Dom.framesLoading s.host.dom then
    s := { s with host := { s.host with dom := { s.host.dom with loadWaits := true } } }
  else
    s := s.setLoop (s.loop.queueTask .domManipulation 0 (some { type := "load", target := windowId }))
  return (← s.advanceP 0).1

/-- Start a page: its classic scripts in document order (each with the current script set
and a microtask checkpoint after it), `DOMContentLoaded` at the document, then the `load`
event at the window as a task, and the tasks that are due at time 0. `scripts` are the
script element's node and its source. `frames` are the `iframe` elements whose documents
the embedder loaded, each with its document parsed on its own: each joins the page's arena
(`Dom.graft`), and its `load` event at the `iframe` is a task before the window's. The
frames share the page's script realm. `origins`: this is a sandboxed frame's own session
(`HTML.FrameSessions`), with its own origin and its parent's. -/
def start (m : Module') (dom : Arena) (url : String) (scripts : Array (Nat × String)) (lim : Limits := {})
    (frames : Array (Nat × Arena) := #[]) (reads : Reads := {}) (time : ScriptClock := {})
    (origins : Option (L4Factoidal.HTML.Frames.Origin × L4Factoidal.HTML.Frames.Origin) := none) : Except String Session := do
  let (dom, framed) := graftFrames dom frames
  let s : Session ← match m.base with
    | some b =>
      let domHost : DomHost := { dom, commandLimit := lim.commands, logLimit := lim.logs, frames := framed, framing := lim.frames, hostLoads := lim.hostLoads, selfOrigin := origins.map (·.1), parentOrigin := origins.map (·.2) }
      let host : Host := { dom := domHost, reads, time, web := { entropy := lim.entropy, docEncoding := lim.encoding } }
      pure { b with host, limits := lim, steps := 0 }
    | none => do
      let s ← instantiatePage m dom lim
      let web : Hosts.WebApi.State := { entropy := lim.entropy, docEncoding := lim.encoding }
      let dh := { s.host.dom with frames := framed, framing := lim.frames, hostLoads := lim.hostLoads, selfOrigin := origins.map (·.1), parentOrigin := origins.map (·.2) }
      pure { s with host := { s.host with dom := dh, reads, time, web } }
  let s := { s with host := { s.host with dom := { s.host.dom with gpu := L4Factoidal.PageGpu.State.empty lim.gpuPage lim.gpuReplay } } }
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
