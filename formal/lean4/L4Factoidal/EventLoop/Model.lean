import L4Factoidal.EventLoop.Timers

/-!
# The event loop of a window (WHATWG HTML §8.1.7)

A pure model of one window event loop: task queues, the microtask queue, the
list of active timers (HTML §8.6), a virtual clock in milliseconds, and the
animation frame callbacks (HTML §8.10).

Callbacks are opaque handles. The model decides WHAT runs and WHEN; the host or
the script engine runs the callback. The calls that a callback makes
(`setTimeout`, `queueMicrotask`, ...) come back to the model as `Call` values.
No effect happens inside the model.

Choices that HTML leaves to the user agent, and the choice made here:

* "Let taskQueue be one such task queue, chosen in an implementation-defined
  manner": the queue whose first runnable task is oldest. All tasks are kept
  in one list in the order queued; the task queue of a source is the
  subsequence of that source (`tasks.filter (·.source == s)`), so each queue
  stays first in, first out.
* Rendering opportunities: the host asks for one (`render`). The model does not
  decide the frame rate.
* Time: the host moves the clock (`advanceTo`). The clock moves to the due time
  of the first armed timer when that is before the target, so that a callback of
  that timer can arm an earlier timer than the next one.

Proofs: `L4Factoidal.EventLoop.Theorems`. Tests: `L4Factoidal.EventLoop.Tests`.
-/
namespace L4Factoidal.EventLoop

/-- The task sources of HTML §8.1.7.4 that a page script reaches. -/
inductive Source where
  | domManipulation | userInteraction | networking | historyTraversal
  | timer | postedMessage | other
  deriving DecidableEq, Repr, Inhabited

/-- A user interaction event that a task dispatches. `target` is a node of the
DOM arena. -/
structure Event where
  type : String
  target : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A task. `timer` is the timer that queued it (HTML §8.6 step "Let task be a
task that runs the following substeps"); `nesting` is its timer nesting level. -/
structure Task where
  source : Source
  callback : Handle
  timer : Option Timer := none
  event : Option Event := none
  nesting : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- An animation frame callback (HTML §8.10). -/
structure Frame where
  id : Nat
  callback : Handle
  deriving DecidableEq, Repr, Inhabited

inductive Kind where
  | task | microtask | frame
  deriving DecidableEq, Repr, Inhabited

/-- What the host must run now. `timer` is the id of the timer whose callback it
is; `now` is the clock, for the `DOMHighResTimeStamp` of a frame callback. -/
structure Run where
  kind : Kind
  callback : Handle
  source : Option Source := none
  timer : Option Nat := none
  event : Option Event := none
  now : Nat := 0
  deriving DecidableEq, Repr, Inhabited

structure State where
  clock : Nat := 0
  /-- All task queues, in the order queued. -/
  tasks : List Task := []
  microtasks : List Handle := []
  /-- Armed timers, `Sorted` (firing order). -/
  timers : List Timer := []
  /-- The map of active timers of HTML §8.6, as its keys. -/
  active : List Nat := []
  /-- HTML timer ids are greater than zero. -/
  nextTimer : Nat := 1
  nextSeq : Nat := 0
  /-- The map of animation frame callbacks, in order of request. -/
  frames : List Frame := []
  /-- The callbacks of the frame being run by `frameStep`. -/
  frameBatch : List Frame := []
  nextFrame : Nat := 1
  /-- The currently running task, until the next `step` finishes it. -/
  current : Option Task := none
  deriving Repr, Inhabited

/-- The calls that a running callback makes. -/
inductive Call where
  | queueTask (source : Source) (callback : Handle)
  | queueMicrotask (callback : Handle)
  | setTimer (callback : Handle) (timeout : Nat) (periodic : Bool)
  | clearTimer (id : Nat)
  | requestFrame (callback : Handle)
  | cancelFrame (id : Nat)
  deriving DecidableEq, Repr, Inhabited

def Task.run (t : Task) : Run :=
  { kind := .task, callback := t.callback, source := some t.source,
    timer := t.timer.map (·.id), event := t.event }

namespace State

/-- HTML §8.6 timer initialization step 3: the nesting level is that of the
currently running task when a timer queued it, else 0. -/
def nesting (st : State) : Nat :=
  match st.current with
  | some task => task.nesting
  | none => 0

/-- Timer initialization steps 4 to 7 for a timer of id `id`. `level` is the
nesting level of step 3. -/
def arm (id callback timeout : Nat) (periodic : Bool) (level : Nat) (st : State) : State :=
  let timer : Timer := { id, callback, due := st.clock + clamp level timeout, seq := st.nextSeq,
                         timeout, periodic, nesting := level + 1 }
  { st with timers := insert timer st.timers, nextSeq := st.nextSeq + 1 }

/-- `setTimeout` (`periodic` false) and `setInterval` (true). The answer is the id. -/
def setTimer (callback timeout : Nat) (periodic : Bool) (st : State) : State × Nat :=
  let id := st.nextTimer
  let next := { st with active := id :: st.active, nextTimer := id + 1 }
  (next.arm id callback timeout periodic st.nesting, id)

/-- `clearTimeout` and `clearInterval`: remove the id from the map of active
timers. A task already queued for it then does nothing. -/
def clearTimer (id : Nat) (st : State) : State :=
  { st with timers := st.timers.filter (fun t => t.id != id),
            active := st.active.filter (fun x => x != id) }

def queueTask (source : Source) (callback : Handle) (event : Option Event := none) (st : State) : State :=
  { st with tasks := st.tasks ++ [{ source, callback, event }] }

def queueMicrotask (callback : Handle) (st : State) : State :=
  { st with microtasks := st.microtasks ++ [callback] }

/-- `requestAnimationFrame`; the answer is the handle. -/
def requestFrame (callback : Handle) (st : State) : State × Nat :=
  ({ st with frames := st.frames ++ [{ id := st.nextFrame, callback }], nextFrame := st.nextFrame + 1 },
   st.nextFrame)

/-- `cancelAnimationFrame`, also for a callback of the frame being run. -/
def cancelFrame (id : Nat) (st : State) : State :=
  { st with frames := st.frames.filter (fun f => f.id != id),
            frameBatch := st.frameBatch.filter (fun f => f.id != id) }

/-- HTML "update the rendering", the step "run the animation frame callbacks":
the callbacks requested so far form this frame; callbacks requested while they
run belong to the next frame. -/
def render (st : State) : State :=
  { st with frameBatch := st.frameBatch ++ st.frames, frames := [] }

/-- The next callback of the frame being run. -/
def frameStep (st : State) : State × Option Run :=
  match st.frameBatch with
  | [] => (st, none)
  | f :: rest => ({ st with frameBatch := rest }, some { kind := .frame, callback := f.callback, now := st.clock })

/-- Queue the tasks of the timers that are due. -/
def fire (st : State) : State × List Timer :=
  let (now, later) := due st.clock st.timers
  ({ st with timers := later,
             tasks := st.tasks ++ now.map fun t =>
               { source := .timer, callback := t.callback, timer := some t, nesting := t.nesting } },
   now)

/-- Move the clock towards `target`, stopping at the due time of the first armed
timer if that comes first, and queue the tasks of the timers due then. The
clock never goes back. -/
def nextClock (target : Nat) (st : State) : Nat :=
  match st.timers with
  | t :: _ => if t.due ≤ target then max st.clock t.due else max st.clock target
  | [] => max st.clock target

def advanceTo (target : Nat) (st : State) : State × List Timer :=
  fire { st with clock := st.nextClock target }

/-- No task is running. -/
def done (st : State) : State := { st with current := none }

/-- The task steps of a timer, after its callback (HTML §8.6): a timeout leaves
the map of active timers; an interval that is still active is armed again with
the same id, the nesting level of its own task, and the next `seq`. -/
def finish (st : State) : State :=
  match st.current with
  | none => st.done
  | some task =>
    match task.timer with
    | none => st.done
    | some t =>
      if st.active.contains t.id then
        if t.periodic then st.done.arm t.id t.callback t.timeout true task.nesting
        else { st.done with active := st.active.filter (fun x => x != t.id) }
      else st.done

/-- A task runs unless it is the task of a timer that is no longer active. -/
def runnable (active : List Nat) (task : Task) : Bool :=
  match task.timer with
  | some t => active.contains t.id
  | none => true

/-- The oldest runnable task and the tasks after it. Tasks of cleared timers
before it are dropped. -/
def takeTask (active : List Nat) : List Task → Option (Task × List Task)
  | [] => none
  | t :: rest => if runnable active t then some (t, rest) else takeTask active rest

/-- One step of the event loop processing model. The previous task (if any) is
finished first. Then a microtask runs if one is queued (the microtask
checkpoint after a task); else the oldest runnable task becomes the currently
running task. `none`: the loop is idle until the clock moves or a task is
queued. -/
def step (st : State) : State × Option Run :=
  let st := st.finish
  match st.microtasks with
  | m :: rest => ({ st with microtasks := rest }, some { kind := .microtask, callback := m })
  | [] =>
    match takeTask st.active st.tasks with
    | none => ({ st with tasks := [] }, none)
    | some (t, rest) => ({ st with tasks := rest, current := some t }, some t.run)

/-- One step of "perform a microtask checkpoint" alone, as HTML "clean up after
running script" asks after each event listener. -/
def microtaskStep (st : State) : State × Option Handle :=
  match st.microtasks with
  | [] => (st, none)
  | m :: rest => ({ st with microtasks := rest }, some m)

/-- No task, microtask or frame callback waits. -/
def idle (st : State) : Bool :=
  st.microtasks.isEmpty && (takeTask st.active st.tasks).isNone && st.frameBatch.isEmpty

end State

/-- Apply a call that a callback made. Ids are those `State.setTimer` and
`State.requestFrame` answer. -/
def Call.apply : Call → State → State
  | .queueTask s cb, st => st.queueTask s cb
  | .queueMicrotask cb, st => st.queueMicrotask cb
  | .setTimer cb timeout p, st => (st.setTimer cb timeout p).1
  | .clearTimer id, st => st.clearTimer id
  | .requestFrame cb, st => (st.requestFrame cb).1
  | .cancelFrame id, st => st.cancelFrame id

def applyAll (calls : List Call) (st : State) : State :=
  calls.foldl (fun s c => c.apply s) st

/-- "Perform a microtask checkpoint" with `effects` as the calls each microtask
makes, for at most `fuel` microtasks. The answer is the state and the handles
run, in order. -/
def checkpointGo (effects : Handle → List Call) : Nat → State → List Handle → State × List Handle
  | 0, st, acc => (st, acc.reverse)
  | fuel + 1, st, acc =>
    match st.microtasks with
    | [] => (st, acc.reverse)
    | m :: rest => checkpointGo effects fuel (applyAll (effects m) { st with microtasks := rest }) (m :: acc)

def checkpoint (effects : Handle → List Call) (fuel : Nat) (st : State) : State × List Handle :=
  checkpointGo effects fuel st []

/-- One turn of the event loop (HTML §8.1.7.3 steps 1 to 7): run the oldest
runnable task, apply its calls, then perform a microtask checkpoint of at most
`fuel` microtasks. -/
def turn (effects : Handle → List Call) (fuel : Nat) (st : State) : State × List Run :=
  let st := st.finish
  match State.takeTask st.active st.tasks with
  | none => ({ st with tasks := [] }, [])
  | some (t, rest) =>
    let st := applyAll (effects t.callback) { st with tasks := rest, current := some t }
    let st := st.finish
    let (st, ran) := checkpoint effects fuel st
    (st, t.run :: ran.map fun m => { kind := .microtask, callback := m })

/-- The inputs of the model: a call of a callback, or a step of the host. -/
inductive Input where
  | call (c : Call)
  | advance (target : Nat)
  | step
  | render
  | frameStep
  deriving DecidableEq, Repr, Inhabited

structure Output where
  run : Option Run := none
  fired : List Timer := []
  deriving Repr, Inhabited

def Input.apply : Input → State → State × Output
  | .call c, st => (c.apply st, {})
  | .advance target, st => let (st, fired) := st.advanceTo target; (st, { fired })
  | .step, st => let (st, run) := st.step; (st, { run })
  | .render, st => (st.render, {})
  | .frameStep, st => let (st, run) := st.frameStep; (st, { run })

/-! ## A host's advance: at most one animation frame per advance

HTML §8.1.7.3 "update the rendering" runs at most once per rendering opportunity, with
the time of that opportunity. A host whose clock is behind (a slow turn, a busy worker)
does not get every missed frame back to back: it gets one frame, at the latest frame
time it reached. Timers due before that time still run first, in order; timers due
after it, up to the target, run after it.

`Driver` is the host: a state `σ` that holds a loop `State` and runs what the loop
gives (`run`: a callback in the script engine, which may change the loop through its
calls). `Driver.advanceGo` is the loop of `WasmVM.Hosts.Page.Session.advance`.
`advanceGo_frames` (in `Theorems`): one advance runs at most one frame batch.
-/

/-- The frame interval of the virtual clock, in milliseconds. -/
def frameInterval : Nat := 16

/-- The time of the one animation frame that an advance from `clock` to `target` may
run: the last frame time at or before `target`, when it is not before `clock` and not
the time of the last frame (`last`). -/
def frameSlot (clock target : Nat) (last : Option Nat) : Option Nat :=
  let f := target / frameInterval * frameInterval
  if clock ≤ f ∧ last ≠ some f then some f else none

/-- A host of the event loop: its state holds a loop `State`; `run` runs a `Run`. -/
structure Driver (σ : Type) where
  loop : σ → State
  setLoop : σ → State → σ
  run : σ → Run → σ

namespace Driver
variable {σ : Type} (d : Driver σ)

/-- The callbacks of the frame being run, in order, at most `fuel`. -/
def frameGo : Nat → σ → σ
  | 0, s => s
  | fuel + 1, s =>
    let (l, r) := (d.loop s).frameStep
    let s := d.setLoop s l
    match r with
    | some r => frameGo fuel (d.run s r)
    | none => s

/-- "Update the rendering", the animation frame step: the callbacks requested so far
form the batch (`State.render`); each runs, in order. -/
def frame (s : σ) : σ :=
  let s := d.setLoop s (d.loop s).render
  d.frameGo ((d.loop s).frameBatch.length + 1) s

/-- Run the loop until the clock is at `target` and no task waits, or `fuel` steps.
`slot` is the frame time not yet used (`frameSlot`): the clock stops there, and the
frame batch runs once when callbacks wait; after it, `slot` is `none`. The answer: the
state, `frames` plus the frame batches run, and whether the fuel ran out. Every call is
a tail call. -/
def advanceGo (target : Nat) : Nat → Option Nat → σ → Nat → σ × Nat × Bool
  | 0, _, s, frames => (s, frames, true)
  | fuel + 1, slot, s, frames =>
    let (l, r) := (d.loop s).step
    let s := d.setLoop s l
    match r with
    | some r => advanceGo target fuel slot (d.run s r) frames
    | none =>
      let goal := match slot with | some f => min f target | none => target
      let (l, fired) := (d.loop s).advanceTo goal
      let s := d.setLoop s l
      if fired.isEmpty ∧ slot = some l.clock then
        if l.frames.isEmpty then advanceGo target fuel none s frames
        else advanceGo target fuel none (d.frame s) (frames + 1)
      else if fired.isEmpty ∧ target ≤ l.clock then (s, frames, false)
      else advanceGo target fuel slot s frames

end Driver

end L4Factoidal.EventLoop
