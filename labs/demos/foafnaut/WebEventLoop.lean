import L4Factoidal.EventLoop.Model
import L4Factoidal.EventLoop.Dispatch
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

/-! The `eventLoop` operation: the wire form of `L4Factoidal.EventLoop`.

The script engine keeps the loop state as an opaque JSON value and gives it back
with each request. Lean decides which callback runs next, the timer ids, the
frame handles, and the listener order of an event; the script engine only runs
the callbacks it is told to run. Record: `docs/designissues/2026-11-08-event-loop.md`.

Request: `{"op":"eventLoop","action":A,"state":S,...}`; `state` absent or null
for `init`. Answer: `{"state":S',...}`, or for `dispatch` and `afterStop`
(which need no state) the visits. -/
namespace WebEventLoop
open L4Factoidal
open L4Factoidal.EventLoop

private def num (n : Nat) : JSON.Json := .number (toString n)

private def natOf (j : JSON.Json) : Except String Nat := do
  let .number raw := j | throw "eventLoop: expected a natural number"
  let some n := raw.toNat? | throw "eventLoop: expected a natural number"
  if n > 4294967295 then throw "eventLoop: number exceeds bound"
  return n

private def natField (j : JSON.Json) (key : String) : Except String Nat := do
  let some v := j.field? key | throw s!"eventLoop: missing {key}"
  natOf v

private def boolField (j : JSON.Json) (key : String) : Bool :=
  j.field? key == some (.bool true)

private def listOf (j : JSON.Json) (limit : Nat) : Except String (List JSON.Json) := do
  let .array items := j | throw "eventLoop: expected an array"
  if items.length > limit then throw "eventLoop: list exceeds bound"
  return items

private def natList (j : JSON.Json) (limit : Nat := 65536) : Except String (List Nat) :=
  (listOf j limit) >>= (·.mapM natOf)

def sources : List (String × Source) :=
  [("domManipulation",.domManipulation),("userInteraction",.userInteraction),("networking",.networking),
   ("historyTraversal",.historyTraversal),("timer",.timer),("postedMessage",.postedMessage),("other",.other)]

def sourceName (s : Source) : String := ((sources.find? (·.2 == s)).map (·.1)).getD "other"

private def sourceOf (j : JSON.Json) : Except String Source := do
  let .string name := j | throw "eventLoop: source must be a string"
  let some (_, s) := sources.find? (·.1 == name) | throw "eventLoop: unknown task source"
  return s

def timerJson (t : Timer) : JSON.Json :=
  .array [num t.id, num t.callback, num t.due, num t.seq, num t.timeout, .bool t.periodic, num t.nesting]

private def timerOf (j : JSON.Json) : Except String Timer := do
  let [id, cb, due, seq, timeout, .bool periodic, nesting] ← listOf j 7 | throw "eventLoop: bad timer"
  return { id := ← natOf id, callback := ← natOf cb, due := ← natOf due, seq := ← natOf seq,
           timeout := ← natOf timeout, periodic, nesting := ← natOf nesting }

def eventJson : Option Event → JSON.Json
  | none => .null
  | some e => .object [("type",.string e.type),("target",num e.target)]

private def eventOf : JSON.Json → Except String (Option Event)
  | .null => pure none
  | j => do
    let some (.string type) := j.field? "type" | throw "eventLoop: event type required"
    if type.utf8ByteSize > 64 then throw "eventLoop: event type exceeds bound"
    return some { type, target := ← natField j "target" }

def taskJson (t : Task) : JSON.Json :=
  .array [.string (sourceName t.source), num t.callback,
    (match t.timer with | some tm => timerJson tm | none => .null), eventJson t.event, num t.nesting]

private def taskOf (j : JSON.Json) : Except String Task := do
  let [source, cb, timer, event, nesting] ← listOf j 5 | throw "eventLoop: bad task"
  let timer ← match timer with
    | .null => pure none
    | other => some <$> timerOf other
  return { source := ← sourceOf source, callback := ← natOf cb, timer, event := ← eventOf event,
           nesting := ← natOf nesting }

private def frameOf (j : JSON.Json) : Except String Frame := do
  let [id, cb] ← listOf j 2 | throw "eventLoop: bad frame"
  return { id := ← natOf id, callback := ← natOf cb }

def frameJson (f : Frame) : JSON.Json := .array [num f.id, num f.callback]

def stateJson (st : State) : JSON.Json :=
  .object [("clock",num st.clock),("tasks",.array (st.tasks.map taskJson)),
    ("microtasks",.array (st.microtasks.map num)),("timers",.array (st.timers.map timerJson)),
    ("active",.array (st.active.map num)),("nextTimer",num st.nextTimer),("nextSeq",num st.nextSeq),
    ("frames",.array (st.frames.map frameJson)),("frameBatch",.array (st.frameBatch.map frameJson)),
    ("nextFrame",num st.nextFrame),
    ("current",match st.current with | some t => taskJson t | none => .null)]

/-- Read a state back. The proofs assume `Inv`: timers in firing order, each
armed before `nextSeq`. A state that breaks it is refused. -/
def stateOf (j : JSON.Json) : Except String State := do
  let field := fun (key : String) => match j.field? key with
    | some v => Except.ok v
    | none => Except.error s!"eventLoop: state field {key} missing"
  let st : State := {
    clock := ← natField j "clock",
    tasks := ← (listOf (← field "tasks") 65536) >>= (·.mapM taskOf),
    microtasks := ← natList (← field "microtasks"),
    timers := ← (listOf (← field "timers") 65536) >>= (·.mapM timerOf),
    active := ← natList (← field "active"),
    nextTimer := ← natField j "nextTimer", nextSeq := ← natField j "nextSeq",
    frames := ← (listOf (← field "frames") 65536) >>= (·.mapM frameOf),
    frameBatch := ← (listOf (← field "frameBatch") 65536) >>= (·.mapM frameOf),
    nextFrame := ← natField j "nextFrame",
    current := ← match ← field "current" with
      | .null => pure none
      | other => some <$> taskOf other }
  let sorted := (st.timers.zip st.timers.tail).all fun (a, b) => keyLe a b
  if !sorted || !(st.timers.all fun t => decide (t.seq < st.nextSeq)) then
    throw "eventLoop: state timers out of order"
  return st

def kindName : Kind → String
  | .task => "task" | .microtask => "microtask" | .frame => "frame"

def runJson : Option Run → JSON.Json
  | none => .null
  | some r => .object [("kind",.string (kindName r.kind)),("callback",num r.callback),
      ("source",match r.source with | some s => .string (sourceName s) | none => .null),
      ("timer",match r.timer with | some t => num t | none => .null),
      ("event",eventJson r.event),("now",num r.now)]

def visitJson (v : Dispatch.Visit) : JSON.Json :=
  .object [("node",num v.node),("depth",num v.depth),("capture",.bool v.capture),
    ("phase",num (match v.phase with | .capturing => 1 | .atTarget => 2 | .bubbling => 3)),
    ("callback",num v.callback)]

private def visitOf (j : JSON.Json) : Except String Dispatch.Visit := do
  let phase ← natField j "phase"
  return { node := ← natField j "node", depth := ← natField j "depth", capture := boolField j "capture",
           phase := if phase == 1 then .capturing else if phase == 2 then .atTarget else .bubbling,
           callback := ← natField j "callback" }

private def listenerOf (j : JSON.Json) : Except String Dispatch.Listener := do
  return { node := ← natField j "node", capture := boolField j "capture", callback := ← natField j "callback" }

private def answer (st : State) (extra : List (String × JSON.Json)) : String :=
  (JSON.Json.object (("state",stateJson st) :: extra)).toString

/-- The `eventLoop` operation. -/
def op (name : String) (request : JSON.Json) : Except String (Option String) := do
  if name != "eventLoop" then return none
  let some (.string action) := request.field? "action" | throw "eventLoop: action required"
  if action == "dispatch" then
    let path ← natList ((request.field? "path").getD .null) 4096
    if path.isEmpty then throw "eventLoop: empty event path"
    let listeners ← (listOf ((request.field? "listeners").getD .null) 65536) >>= (·.mapM listenerOf)
    let visits := Dispatch.plan path listeners (boolField request "bubbles")
    return some (JSON.Json.object [("visits",.array (visits.map visitJson))]).toString
  if action == "afterStop" then
    let visits ← (listOf ((request.field? "visits").getD .null) 65536) >>= (·.mapM visitOf)
    let rest := Dispatch.afterStop visits (← natField request "index") (boolField request "immediate")
    return some (JSON.Json.object [("visits",.array (rest.map visitJson))]).toString
  let st ← if action == "init" then pure ({} : State) else stateOf ((request.field? "state").getD .null)
  match action with
  | "init" => return some (answer st [])
  | "queueTask" =>
    let event ← eventOf ((request.field? "event").getD .null)
    return some (answer (st.queueTask (← sourceOf ((request.field? "source").getD .null))
      (← natField request "callback") event) [])
  | "queueMicrotask" => return some (answer (st.queueMicrotask (← natField request "callback")) [])
  | "setTimer" =>
    let (st, id) := st.setTimer (← natField request "callback") (← natField request "timeout") (boolField request "periodic")
    return some (answer st [("id",num id)])
  | "clearTimer" => return some (answer (st.clearTimer (← natField request "id")) [])
  | "requestFrame" =>
    let (st, id) := st.requestFrame (← natField request "callback")
    return some (answer st [("id",num id)])
  | "cancelFrame" => return some (answer (st.cancelFrame (← natField request "id")) [])
  | "step" =>
    let (st, run) := st.step
    return some (answer st [("run",runJson run)])
  | "microtaskStep" =>
    let (st, m) := st.microtaskStep
    return some (answer st [("callback",match m with | some h => num h | none => .null)])
  | "advance" =>
    -- `settled`: the clock is at the target and no armed timer is due by then.
    let target ← natField request "target"
    let (st, fired) := st.advanceTo target
    let settled := st.clock ≥ target && st.timers.all (fun t => decide (target < t.due))
    return some (answer st [("fired",num fired.length),("settled",.bool settled)])
  | "render" => return some (answer st.render [])
  | "frameStep" =>
    let (st, run) := st.frameStep
    return some (answer st [("run",runJson run)])
  | _ => throw "eventLoop: unknown action"

/-- Round trip of the state through its wire form. -/
def roundTrips (st : State) : Bool :=
  match stateOf (stateJson st) with
  | .ok back => stateJson back == stateJson st
  | .error _ => false

#guard roundTrips (((({} : State).setTimer 3 10 true).1.queueTask .userInteraction 0 (some ⟨"click",4⟩)).queueMicrotask 9)

#guard (op "eventLoop" (.object [("action",.string "dispatch"),("path",.array [num 1,num 2]),
  ("bubbles",.bool true),("listeners",.array [
    .object [("node",num 2),("capture",.bool false),("callback",num 7)],
    .object [("node",num 1),("capture",.bool false),("callback",num 8)],
    .object [("node",num 1),("capture",.bool true),("callback",num 9)]])])) ==
  .ok (some "{\"visits\":[{\"node\":1,\"depth\":0,\"capture\":true,\"phase\":1,\"callback\":9},{\"node\":2,\"depth\":1,\"capture\":false,\"phase\":2,\"callback\":7},{\"node\":1,\"depth\":0,\"capture\":false,\"phase\":3,\"callback\":8}]}")

#guard match stateOf (stateJson { timers := [⟨1,1,9,0,9,false,1⟩, ⟨2,2,5,1,5,false,1⟩], nextSeq := 2 }) with
  | .error _ => true | .ok _ => false

end WebEventLoop
