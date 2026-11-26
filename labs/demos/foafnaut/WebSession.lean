import WebDocument

/-! # Engine sessions on Lean tasks

docs/designissues/2026-11-26-foafnaut-engine-sessions.md, stages 3 and 4 (issue
https://github.com/danbri/factoidal-core/issues/1031).

A session is the engine of one tab. Here its state (`WebDocument.Engine`) lives in one
dedicated Lean task (`Task.Priority.dedicated`: a thread of its own, outside the task pool),
which takes the session's calls in arrival order from its inbox, one at a time, and answers
each through the promise its caller waits on. A caller on another thread (the host's FFI
call) adds a call to the inbox and waits for its answer; calls on two sessions run at the
same time on two threads.

The engine value is made in the task and never leaves it, so it is never shared between
threads: its updates stay in place (a value that two threads can reach is marked
multi-threaded and copied on every change, `skills/lean4-performance`). What crosses threads
is the call (its strings and bytes) and the answer.

Every ref of a `Session` is reached by the task and by callers, so each uses one family of
ref operations only (`modify` and `modifyGet`): with `get` or `set` beside them a write of
another thread can be lost (`skills/lean4-performance`, "Values that two threads can reach").

Ending: `close` lets the task answer the calls it has and then end; `cancel` also cancels the
task (`IO.cancel`), so the call in progress stops at the engine's next check
(`WebWasm.Machine.canceled`: before a render's layout and before its paint) and the calls not
started are refused. A layout in progress runs to its end. When the task ends, it takes the
inbox away (`none`): a call that comes after that is refused at once, and every call that was
put in before it is answered, so no caller waits for good.

This is native only: with no task manager (the Wasm build, or `FOAFNAUT_LEAN_THREADS=0`) a
task runs at once on the calling thread, so `start` would not return. The C shim makes a
session task only when the task manager runs (`web_session_new_task`). -/

namespace WebSession

open WebDocument

/-- A call of the engine: the stateful exports of `WebDocument`, as data. -/
inductive Call where
  /-- `WebDocument.compile`: a JSON text answer. -/
  | text (html request : String) (width height : UInt32)
  /-- `WebDocument.compileBin`: a bytes answer (`packAnswer`). -/
  | bin (html request : String) (width height : UInt32)
  /-- `WebDocument.fontLoadBin`. -/
  | font (bytes : ByteArray) (family sha256 : String) (fallback : UInt32)
  /-- `WebDocument.imageLoadBin`. -/
  | image (bytes : ByteArray) (key sha256 : String)
  /-- `WebDocument.pickKept`. -/
  | hit (regions : String) (width height : UInt32) (x y : Float)

/-- An answer: JSON text, or the bytes of `compileBin`. -/
inductive Answer where
  | text (value : String)
  | bytes (value : ByteArray)

instance : Nonempty Answer := ⟨.text ""⟩

/-- One call and the promise its caller waits on. -/
structure Job where
  call : Call
  reply : IO.Promise Answer

/-- What a session's task and its callers share. -/
structure Session where
  /-- Calls not started, in arrival order; `none` once the task has ended (no call is taken). -/
  inbox : IO.Ref (Option (Array Job))
  /-- The promise the task waits on while the inbox is empty; a caller that adds a call,
  `close` and `cancel` take it and resolve it. -/
  wake : IO.Ref (Option (IO.Promise Unit))
  /-- Set by `close` and `cancel`: the task ends when its inbox is empty. -/
  closing : IO.Ref Bool
  /-- Calls answered, for the host's trace. -/
  served : IO.Ref Nat

/-- One call on the engine: the next state and the answer. -/
def run (e : Engine) : Call → BaseIO (Engine × Answer)
  | .text html request width height => do
    let (e,a) ← compile e html request width height
    return (e,.text a)
  | .bin html request width height => do
    let (e,a) ← compileBin e html request width height
    return (e,.bytes a)
  | .font bytes family sha256 fallback =>
    let (e,a) := fontLoadBin e bytes family sha256 fallback
    return (e,.text a)
  | .image bytes key sha256 =>
    let (e,a) := imageLoadBin e bytes key sha256
    return (e,.text a)
  | .hit regions width height x y =>
    let (e,a) := pickKept e regions width height x y
    return (e,.text a)

/-- The answer of a call that did not run: JSON text, or the bytes of a JSON head. -/
def refusal (c : Call) (why : String) : Answer :=
  match c with
  | .bin .. => .bytes (packAnswer (WebRender.errorJSON why) #[])
  | _ => .text (WebRender.errorJSON why)

/-- The calls not started, taken out of the inbox (none once the task has ended). -/
@[inline] def take (s : Session) : BaseIO (Array Job) :=
  s.inbox.modifyGet fun
    | some jobs => (jobs,some #[])
    | none => (#[],none)

/-- `close` or `cancel` was called. -/
@[inline] def isClosing (s : Session) : BaseIO Bool :=
  s.closing.modifyGet fun c => (c,c)

/-- Wake the task if it waits. -/
@[inline] def wakeUp (s : Session) : BaseIO Unit := do
  if let some p ← s.wake.modifyGet (fun w => (w,none)) then p.resolve ()

/-- The session's task: the engine's state, and the calls answered in arrival order. The
engine state starts empty, as `WebDocument.engineNew`. -/
def serve (s : Session) : BaseIO Unit := do
  let mut e : Engine := {}
  -- Ends when the host has ended the session (`close` or `cancel`, from another thread) and no
  -- call is left: an outside event, so a `repeat` loop (CLAUDE.md, "Loops yes, new partial def
  -- no").
  repeat
    let jobs ← take s
    if jobs.isEmpty then
      if ← isClosing s then break
      -- Publish the promise to wait on, then look again: a call, `close` or `cancel` that came
      -- before the promise was published is seen here; one that comes after resolves it.
      let p ← IO.Promise.new
      s.wake.modify fun _ => some p
      let again ← take s
      if again.isEmpty then
        if ← isClosing s then break
        let _ ← IO.wait p.result?
      else
        -- Put them back, in order, ahead of any that came since: the next turn runs them.
        s.inbox.modify fun
          | some later => some (again ++ later)
          | none => none
    else
      for job in jobs do
        if ← IO.checkCanceled then
          job.reply.resolve (refusal job.call "engine session canceled")
        else
          let (e',answer) ← run e job.call
          e := e'
          job.reply.resolve answer
      s.served.modify (· + jobs.size)
  -- No call is taken from here on; the calls put in before this are refused, so none waits.
  let left ← s.inbox.modifyGet fun
    | some jobs => (jobs,none)
    | none => (#[],none)
  for job in left do
    job.reply.resolve (refusal job.call "engine session ended")

/-- A session and its task. The task's closure holds the session; the handle holds both, and
the session does not hold the task, so freeing the handle frees all of it once the task ends. -/
structure Handle where
  session : Session
  task : Task (Except IO.Error Unit)

/-- A new session, with its task started on a dedicated thread. The exports below take the
handle owned (an export can not borrow): the C shim adds a reference before each call. -/
@[export web_session_task_start]
def start (_ : Unit) : BaseIO Handle := do
  let inbox ← IO.mkRef (some #[])
  let wake ← IO.mkRef none
  let closing ← IO.mkRef false
  let served ← IO.mkRef 0
  let session : Session := { inbox, wake, closing, served }
  let task ← IO.asTask (serve session) Task.Priority.dedicated
  return ⟨session,task⟩

/-- Add a call to the inbox and wait for its answer. A session that was closed, canceled or
has ended answers an error and runs nothing. -/
def call (h : @& Handle) (c : Call) : BaseIO Answer := do
  if ← isClosing h.session then return refusal c "engine session ended"
  let reply ← IO.Promise.new
  let taken ← h.session.inbox.modifyGet fun
    | some jobs => (true,some (jobs.push ⟨c,reply⟩))
    | none => (false,none)
  if !taken then return refusal c "engine session ended"
  wakeUp h.session
  match ← IO.wait reply.result? with
  | some a => return a
  | none => return refusal c "engine session ended before it answered"

/-- `call` with a text answer (a bytes answer is not one of these calls). -/
def callText (h : @& Handle) (c : Call) : BaseIO String := do
  match ← call h c with
  | .text t => return t
  | .bytes _ => return WebRender.errorJSON "engine session: bytes answer to a text call"

@[export web_session_task_call]
def callCompile (h : Handle) (html request : String) (width height : UInt32) : BaseIO String :=
  callText h (.text html request width height)

@[export web_session_task_call_bin]
def callCompileBin (h : Handle) (html request : String) (width height : UInt32) : BaseIO ByteArray := do
  match ← call h (.bin html request width height) with
  | .bytes b => return b
  | .text t => return packAnswer t #[]

@[export web_session_task_font]
def callFont (h : Handle) (bytes : ByteArray) (family sha256 : String) (fallback : UInt32) : BaseIO String :=
  callText h (.font bytes family sha256 fallback)

@[export web_session_task_image]
def callImage (h : Handle) (bytes : ByteArray) (key sha256 : String) : BaseIO String :=
  callText h (.image bytes key sha256)

@[export web_session_task_hit]
def callHit (h : Handle) (regions : String) (width height : UInt32) (x y : Float) : BaseIO String :=
  callText h (.hit regions width height x y)

/-- End the session: no call is taken after this; the task answers the calls it has, then
ends. Waits for the task when `wait` is 1. -/
@[export web_session_task_close]
def close (h : Handle) (wait : UInt8) : BaseIO Unit := do
  h.session.closing.modify fun _ => true
  wakeUp h.session
  if wait == 1 then let _ ← IO.wait h.task

/-- Stop the session: `close`, and the task is canceled, so the call in progress stops at the
engine's next check and the calls not started are refused. Waits for the task when `wait` is
1. -/
@[export web_session_task_cancel]
def cancel (h : Handle) (wait : UInt8) : BaseIO Unit := do
  h.session.closing.modify fun _ => true
  IO.cancel h.task
  wakeUp h.session
  if wait == 1 then let _ ← IO.wait h.task

/-- Calls answered so far. -/
@[export web_session_task_served]
def served (h : Handle) : BaseIO UInt64 := do
  return (← h.session.served.modifyGet fun n => (n,n)).toUInt64

end WebSession
