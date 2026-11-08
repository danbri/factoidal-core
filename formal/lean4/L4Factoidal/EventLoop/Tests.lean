import L4Factoidal.EventLoop.Theorems

/-! Build-time tests of the event loop model. Each `#guard` runs while the
module elaborates; a wrong answer fails the build. -/
namespace L4Factoidal.EventLoop.Tests
open L4Factoidal.EventLoop

/-- Run the loop with `effects` until idle or out of fuel; then move the clock
towards `target` and continue. The answer is the callbacks run, with the clock. -/
def driveGo (effects : Handle → List Call) (target : Nat) : Nat → State → List (Kind × Handle × Nat) → State × List (Kind × Handle × Nat)
  | 0, st, acc => (st, acc.reverse)
  | fuel + 1, st, acc =>
    match st.step with
    | (st', some r) =>
      driveGo effects target fuel (applyAll (effects r.callback) st') ((r.kind, r.callback, st'.clock) :: acc)
    | (st', none) =>
      if st'.clock ≥ target ∧ (st'.timers.all fun t => decide (target < t.due)) then (st', acc.reverse)
      else driveGo effects target fuel (st'.advanceTo target).1 acc

def drive (effects : Handle → List Call) (target fuel : Nat) (st : State) : State × List (Kind × Handle × Nat) :=
  driveGo effects target fuel st []

-- Script 1 queues a microtask 2 and a timeout 3 of 0 ms; 2 logs before 3.
def script : Handle → List Call
  | 1 => [.queueMicrotask 2, .setTimer 3 0 false]
  | _ => []

#guard (drive script 10 50 (({} : State).queueTask .domManipulation 1)).2.map (·.2.1) == [1, 2, 3]

-- An interval of 10 ms, cleared by its third callback.
def interval : Handle → List Call
  | 1 => [.setTimer 7 10 true]
  | 7 => []
  | _ => []

#guard ((drive interval 35 100 (({} : State).queueTask .domManipulation 1)).2.map fun (k, h, c) => (k == .task, h, c))
  == [(true, 1, 0), (true, 7, 10), (true, 7, 20), (true, 7, 30)]

-- Equal due times fire in the order set; earlier due first.
def three : Handle → List Call
  | 1 => [.setTimer 20 5 false, .setTimer 21 3 false, .setTimer 22 5 false]
  | _ => []

#guard (drive three 10 50 (({} : State).queueTask .domManipulation 1)).2.map (·.2.1) == [1, 21, 20, 22]

-- A cleared timer never runs.
def cleared : Handle → List Call
  | 1 => [.setTimer 30 5 false, .setTimer 31 5 false, .clearTimer 1]
  | _ => []

#guard (drive cleared 10 50 (({} : State).queueTask .domManipulation 1)).2.map (·.2.1) == [1, 31]

-- Nesting: a chain of 0 ms timeouts from a script task. Timer k runs in a task of
-- nesting level k. Timers set from levels 0 to 5 keep 0 ms; a timer set from a task
-- of level 6 or more ("greater than 5") gets 4 ms: timers 1 to 6 run at 0, timer 7 at 4.
def chain : Handle → List Call
  | h => if h < 10 then [.setTimer (h + 1) 0 false] else []

#guard (drive chain 100 100 (({} : State).queueTask .domManipulation 0)).2.map (·.2.2)
  == [0, 0, 0, 0, 0, 0, 0, 4, 8, 12, 16]

-- Animation frames: callbacks requested during a frame run in the next one.
def frames : State :=
  let (st, _) := ({} : State).requestFrame 40
  let (st, _) := st.requestFrame 41
  st.render

#guard (frames.frameStep.2.map (·.callback)) == some 40
#guard (frames.frameStep.1.frameStep.2.map (·.callback)) == some 41
#guard ((frames.frameStep.1.requestFrame 42).1.frameStep.1.frameStep.2) == none
#guard ((frames.cancelFrame 2).frameStep.1.frameStep.2) == none

-- Dispatch: path html(1) > body(2) > button(3); listeners in the order added.
open Dispatch in
def listeners : List Listener :=
  [⟨3, false, 100⟩, ⟨1, true, 101⟩, ⟨2, false, 102⟩, ⟨3, true, 103⟩, ⟨1, false, 104⟩, ⟨2, true, 105⟩]

#guard (Dispatch.plan [1, 2, 3] listeners true).map (·.callback) == [101, 105, 103, 100, 102, 104]
#guard (Dispatch.plan [1, 2, 3] listeners false).map (·.callback) == [101, 105, 103, 100]
-- stopPropagation in the target's bubbling listener 100 (index 3): nothing more.
#guard (Dispatch.afterStop (Dispatch.plan [1, 2, 3] listeners true) 3 false) == []
#guard (Dispatch.plan [1, 2, 3] (listeners ++ [⟨2, false, 106⟩]) true |> (Dispatch.afterStop · 4 false) |>.map (·.callback)) == [106]

#guard Dispatch.rank 2 ⟨3, 2, true, .atTarget, 0⟩ == 2

#print axioms trace_fired_sorted
#print axioms cleared_never_fires
#print axioms checkpoint_empties
#print axioms checkpoint_fifo
#print axioms Dispatch.plan_ordered
#print axioms Dispatch.afterStop_same_node
#print axioms clamp_deep

end L4Factoidal.EventLoop.Tests
