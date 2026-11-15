module

public import Veil

/-!
# Pages, engine workers, the main thread, the GPU queue and input

A system-level model of how Foafnaut runs several pages at once (core issue 398; the runtime
parallelism work on branch `wip/par`). It is a design model, not a model of one host's code:
`formal/lean4/L4Factoidal/HostPipeline/Model.lean` (branch `wip/par`) is the small, core-only
trace-check model whose observations (`pump`, `submit`, `ask`, `answer`) the hosts log; this
model is the richer one with several pages and workers that those observations are meant to
project from.

- Pages are loaded on engine workers; a worker holds at most one page and a page is on at most
  one worker.
- Events (input, timers, network completions) are queued per page with sequence numbers; a
  worker handles one event of its page at a time, in sequence order.
- The main thread takes input from the window and pumps it into a page's queue, and submits
  frames to the GPU queue. Waiting for a GPU fence happens off the main thread (the change on
  `wip/par`): the main thread never blocks on the GPU, and while input waits it submits at most
  one further frame.
- At most `maxInFlight` frames are submitted and not finished.

Invariants proved by `#check_invariants` with SMT proof reconstruction (`veil.smt.trust false`):
see the list at the end. `#model_check` on a small instance is test evidence only.
-/

set_option veil.smt.trust false

veil module FramePipeline

type page
type worker

/- Frames that may be submitted to the GPU and not yet finished. -/
immutable individual maxInFlight : Nat

relation assigned : worker → page → Bool
/- Events queued for a page so far: their sequence numbers are `0 .. sent p - 1`. -/
function sent : page → Nat
/- The sequence number of the page's next event to handle. -/
function handled : page → Nat
/- `processing w p`: worker `w` is handling event `handled p` of page `p`. -/
relation processing : worker → page → Bool
individual inFlight : Nat
/- Input from the window that the main thread has not yet pumped into a page. -/
individual inputWaiting : Bool
/- Frames the main thread submitted since the oldest waiting input arrived. -/
individual gpuSinceInput : Nat

#gen_state

assumption [some_frame] maxInFlight ≥ 1

after_init {
  assigned U P := false
  sent P := 0
  handled P := 0
  processing U P := false
  inFlight := 0
  inputWaiting := false
  gpuSinceInput := 0
}

/- A page starts loading on a free worker. -/
action openPage (w : worker) (p : page) {
  require ∀ q, ¬ assigned w q
  require ∀ v, ¬ assigned v p
  assigned w p := true
}

/- A page closes once its worker is idle; events still queued for it are dropped. -/
action closePage (w : worker) (p : page) {
  require assigned w p
  require ¬ processing w p
  assigned w p := false
}

/- Input reaches the main thread from the window. -/
action inputArrives {
  if ¬ inputWaiting then
    inputWaiting := true
    gpuSinceInput := 0
}

/- The main thread hands the waiting input to page `p`'s queue. -/
action pump (p : page) {
  require inputWaiting
  sent p := sent p + 1
  inputWaiting := false
  gpuSinceInput := 0
}

/- A timer or a network completion queues an event for page `p`. -/
action enqueue (p : page) {
  sent p := sent p + 1
}

/- An idle worker starts the page's next event, when no event of the page is in progress. -/
action dispatch (w : worker) (p : page) {
  require assigned w p
  require handled p < sent p
  require ∀ v, ¬ processing v p
  require ∀ q, ¬ processing w q
  processing w p := true
}

/- The worker finishes the page's event `handled p`; the next one becomes current. -/
action finish (w : worker) (p : page) {
  require processing w p
  processing w p := false
  handled p := handled p + 1
}

/- The main thread submits a frame. While input waits, at most one frame goes first. -/
action submit {
  require inFlight < maxInFlight
  require ¬ inputWaiting ∨ gpuSinceInput < 1
  inFlight := inFlight + 1
  if inputWaiting then
    gpuSinceInput := gpuSinceInput + 1
}

/- The GPU finishes the oldest frame (its fence is seen off the main thread). -/
action gpuFinish {
  require inFlight > 0
  inFlight := inFlight - 1
}

-- Bounded frames in flight.
safety [frames_bounded] inFlight ≤ maxInFlight
-- Input never waits behind more than one frame of GPU work submitted after it.
safety [input_one_frame] inputWaiting → gpuSinceInput ≤ 1
-- Each page's events are handled one at a time, in sequence order.
safety [in_order] processing U P → handled P < sent P
safety [one_per_page] processing V P ∧ processing U P → V = U
invariant [handled_le_sent] handled P ≤ sent P
-- A worker handles only its own page, and holds at most one page; a page is on one worker.
invariant [busy_assigned] processing U P → assigned U P
safety [worker_one_page] assigned U P ∧ assigned U Q → P = Q
safety [page_one_worker] assigned V P ∧ assigned U P → V = U
-- No deadlock for a loaded page: when it has queued events, its worker is handling one or the
-- page's next event can be dispatched (no event of the page is in progress elsewhere).
safety [page_progress]
  assigned U P ∧ handled P < sent P → (∀ V, ¬ processing V P) ∨ processing U P
-- No deadlock for input: waiting input can always be pumped (`pump` needs only `inputWaiting`),
-- and the GPU queue drains (`gpuFinish` needs only `inFlight > 0`). Both are by construction of
-- the actions' guards, which is the design point: the main thread never blocks on a fence.

-- Model checking only: bound the queues of the finite instance.
state_constraint [small_queues] sent P ≤ 2

#gen_spec

#check_invariants

#gen_theorems

#model_check { page := Fin 2, worker := Fin 2 } { maxInFlight := 2 }

end FramePipeline
