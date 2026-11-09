# The HTML event loop and timers in Lean, run by QuickJS

Date: 2026-11-08. Author: event-loop, a subagent of session depmap-0e.
Related: https://github.com/danbri/factoidal/issues/1252 (page JavaScript in
VerifiedJS; QuickJS stays the default).

## 1. Result

Page scripts in Foafnaut now have `setTimeout`, `setInterval`, `clearTimeout`,
`clearInterval`, `queueMicrotask`, `requestAnimationFrame`,
`cancelAnimationFrame`, and `addEventListener` / `removeEventListener` with
capture, bubbling, `stopPropagation`, `stopImmediatePropagation`,
`preventDefault` and `once`. Lean decides the order of every callback. QuickJS
runs the callback that Lean names. No host timer decides any order.

Parts:

- `formal/lean4/L4Factoidal/EventLoop/` (library `EventLoop`, only Lean core):
  - `Timers.lean`: the armed timers in firing order, and the timeout clamp.
  - `Model.lean`: the state, the calls a callback makes (`Call`), and the host
    steps (`step`, `microtaskStep`, `advanceTo`, `render`, `frameStep`).
  - `Dispatch.lean`: the listener order of one event (DOM §2.9).
  - `Theorems.lean`: the theorems of section 3.
  - `Tests.lean`: `#guard` scenarios and the `#print axioms` audit.
- `labs/demos/foafnaut/WebEventLoop.lean`: the `eventLoop` operation of the
  web-render engine (the wire form of the state, and the actions). `WebDocument`
  calls it with the other input operations; it needs no document.
- `labs/demos/foafnaut/web-render/script-engine/`: `lean-dom.mjs`
  (`createLeanLoop`), `worker.mjs` (the loop that asks Lean and runs QuickJS),
  `guest.mjs` (the page APIs), `quickjs.mjs` (`runJobs`), `session.mjs`
  (`advance(ms)`, `frame()`).
- `WebRenderScript.snapshot` gives each element its `parent`, so the guest can
  make the event path.
- Test page `labs/demos/foafnaut/web-render/fixtures/timers.html`, test
  `script-engine/event-loop.test.mjs`.

## 2. How it works

The model is a pure function of a state and an input. The state is:

- `tasks`: all task queues in one list, in the order queued. Each task names
  its source (`domManipulation`, `userInteraction`, `timer`, ...). The queue of
  one source is the subsequence of that source, so each queue stays first in,
  first out.
- `microtasks`: the microtask queue.
- `timers`: the armed timers, sorted by `(due, seq)`. `seq` is the number of
  arms before this one. `active` is the key set of HTML's "map of active
  timers".
- `clock`: virtual milliseconds, a natural number.
- `frames`, `frameBatch`: the animation frame callbacks.
- `current`: the running task, so that a timer's nesting level and an
  interval's re-arm are known.

Callbacks are opaque numbers (handles). The guest keeps the functions in a map
from handle to function. When a callback calls `setTimeout`, the guest sends
`setTimer` to Lean and gets the id back. The effects of a callback are inputs to
the model. The model does no effect.

The worker runs the loop:

1. `step`: Lean finishes the last task (re-arms an interval that is still
   active; removes a finished timeout from the active map), then gives a
   microtask if one waits, else the oldest runnable task. A task of a cleared
   timer is dropped.
2. The worker runs that callback in QuickJS, then runs QuickJS's Promise jobs.
3. When `step` gives nothing, `advance` moves the clock to the due time of the
   first armed timer, or to the target. The timers due then become tasks.
4. It stops when the clock is at the target and no timer is due.

`frame()` asks Lean to `render` (the frame callbacks requested so far form the
frame), then runs each with a microtask checkpoint after it.

A click is a task of the user interaction source with an event. When it runs,
the guest makes the path from the target up through `parent`, and asks Lean for
the plan (`dispatch`). It runs the listeners in the plan order, with a microtask
checkpoint after each one. After `stopPropagation` it asks Lean which visits
still run (`afterStop`): the rest of the same invoke.

The state goes to the worker and back as JSON on each call. `stateOf` refuses a
state whose timers are out of order, so the theorems hold for every state the
operation accepts.

Choices where HTML lets the user agent choose:

- The task queue to take a task from: the one whose first runnable task is
  oldest.
- The time: the host moves it (`session.advance(ms)`). The clock stops at each
  due timer, so a callback can arm a timer that is due before the next one.
- A rendering opportunity: the host asks for it (`session.frame()`).

## 3. Theorems

All use only the axioms `propext`, `Classical.choice` and `Quot.sound`
(`Tests.lean` prints them). No `sorry`, `native_decide`, `bv_decide` or
`partial def`.

- `checkpoint_empties`: when the microtasks queue no more microtasks, a
  checkpoint with fuel at least the queue length ends with the queue empty.
  `checkpoint_fifo`: it runs them in the order queued.
  `checkpoint_empties_or_fuel`: with any effects, the queue is empty or all the
  fuel is used.
- `trace_fired_sorted`: over any sequence of inputs from a valid state, the
  fired timers are sorted by `(due, seq)`. So due times do not decrease, and
  timers with the same due time fire in the order they were set (HTML §8.6 "run
  steps after a timeout", the step that waits for earlier invocations with an
  equal or smaller timeout). `insert_sorted`, `due_sorted` and `setTimer_armed`
  are the parts.
- `cleared_never_fires`: after `clearTimer id` of an allocated id, no sequence
  of inputs runs a callback of that timer.
- `clamp_shallow`, `clamp_deep`, `clamp_ge`, with `setTimer_armed`: a timer
  set from a task of nesting level greater than 5 with a timeout less than 4
  waits 4 ms; else it waits its timeout. `Tests.lean` shows a chain of 0 ms
  timeouts: timers 1 to 6 run at 0 ms, timer 7 at 4 ms, timer 8 at 8 ms.
- `Dispatch.plan_ordered`: the plan visits capture listeners root first, then
  the target, then bubble listeners target first (each visit has a rank, and
  the ranks do not decrease). `plan_node`: each visit is at the path node of
  its depth. `plan_phase`: the phase is `AT_TARGET` exactly at the target.
  `plan_no_bubbles`: an event that does not bubble visits no bubble listener of
  an ancestor. `afterStop_same_node`: after `stopPropagation`, only visits at
  the same node (the same invoke) still run; `afterStop_immediate`: after
  `stopImmediatePropagation`, none.

## 4. Limits

- Promise reactions are QuickJS jobs, not Lean microtasks. They run after each
  callback, after the Lean microtasks of that callback. A `queueMicrotask` and a
  `then` queued in the same callback therefore run Lean's first. Inside event
  dispatch, the checkpoint after each listener runs only Lean microtasks; the
  Promise jobs run after the whole dispatch.
- The event path holds elements only: no Document, no Window, no shadow trees.
- The plan is fixed when dispatch starts. A listener added during dispatch to a
  node not reached yet does not run (DOM clones the list at each node). A
  removed listener does not run.
- `passive`, `AbortSignal` options, `Event` constructors and `dispatchEvent`
  from script are not there.
- The guest's `addEventListener` takes any event type, but the hosts send only
  clicks.
- `performance.now()` and `Date.now()` do not read the virtual clock.
- (Note, 2026-11-09: `document-client.mjs` is the local lab host. The browser window and
  the Hub worker are separate hosts.) The live browser host (`document-client.mjs`) does not yet call
  `session.advance` or `session.frame`. Its timers and frames wait until a host
  pump calls them. The pump may use host time to choose how far to move the
  clock; Lean still decides the order.
- A web-render engine built before this change refuses `eventLoop`; the worker
  then runs without the loop (as before) unless the host asks for it.

## 5. WPT next

Directories this opens, and what each still needs:

- `html/webappapis/timers/`: ordering, clamping, `clearTimeout` of another
  timer's id, negative and huge timeouts, string handlers. Needs a testharness
  runner (below).
- `html/webappapis/microtask-queuing/`: `queueMicrotask` order and exceptions.
  To pass the tests that mix `queueMicrotask` with Promises, the Promise jobs
  must become Lean microtasks (a QuickJS host job hook, `JS_EnqueueJob`, or the
  VerifiedJS job queue).
- `dom/events/`: listener order, phases, `stopPropagation`, `once`,
  `removeEventListener` during dispatch. Needs `new Event(...)`,
  `dispatchEvent`, `EventTarget` on Document and Window, and the list clone at
  each node.
- `html/webappapis/animation-frames/` (requestAnimationFrame): needs a host
  that gives frames.

What the testharness.js runner needs:

1. `testharness.js` and `testharnessreport.js` as classic scripts, loaded by
   the Lean resource path.
2. `add_completion_callback` results passed out through `console.log` or a new
   result channel of the session.
3. A run that moves the virtual clock to quiescence (`advance` until no timer is
   armed, with a budget), so `async_test` and `promise_test` finish.
   `step_timeout` is `setTimeout`, so it works now.
4. More DOM: `document.body`, `createElement`, `appendChild`, `Event`, and
   `EventTarget` on Document and Window.
