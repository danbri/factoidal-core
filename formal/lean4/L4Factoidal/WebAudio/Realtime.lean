import L4Factoidal.WebAudio.Api
import L4Factoidal.WebAudio.Sink

/-!
# Web Audio: the rendering task of a real-time `AudioContext`

Step D3 of https://github.com/danbri/factoidal-core/issues/1169 (audio in Foafnaut); plan:
`docs/designissues/2026-11-26-foafnaut-audio-plan.md`, sections 13.2 to 13.4 and 13.9.

One Lean dedicated task (`Task.Priority.dedicated`: a thread of its own) per real-time context. The
task holds its own copy of the context state. It takes the control messages that the engine's IO
layer gives it (`give`), applies them with `Api.op` (the same function as the control side), renders
render quanta (`Render.renderQuantumWith`) into the audio sink's ring ahead of the consumer, and
publishes a report (`takeReport`) that the IO layer merges into the control side
(`Api.applyReport`).

Contract of the parts that are not Lean (plan section 4): the sink (`Sink.lean`, `ffi/audio_sink.c`)
copies frames, counts and keeps time; it decides nothing about the audio. Named assumption of every
path that uses the macOS consumer: "CoreAudio plays the frames it is given, in order, at the device
rate".

Threads. The control side (the engine's turn) and the task share only the refs of `Shared`. Each
ref is used with `modify` and `modifyGet` only (`skills/lean4-performance`, "Values that two
threads can reach"). The task's context state is made in the task and never leaves it.

No task manager (the Wasm build, or `FOAFNAUT_LEAN_THREADS=0`): `IO.asTask` would run the task at
once on the calling thread, and the loop would not return. `threadsAvailable` checks this before
any task starts; without threads the engine has no audio output and op 190 answers -23.

Trace (plan 13.9, `CLAUDE.md` "Observability from the start"): one JSON line `native-audio` on
standard error per running context and second of wall time; `native-audio-first-sound` once for
each batch that has a `start()`; `native-audio-divergence` for a message that fails on the
rendering side; `native-audio-end` when the task ends. `FOAFNAUT_AUDIO_TRACE=0` turns them off.
-/

namespace L4Factoidal.WebAudio.Realtime

open L4Factoidal.WebAudio

/-- What the engine and one rendering task share. -/
structure Shared where
  /-- Control messages (op code, fields) not yet applied, in order. -/
  inbox : IO.Ref (Array (Nat × Array ByteArray))
  /-- The report since the last `takeReport`: counters are the latest values, the event arrays
  are the events since then. -/
  report : IO.Ref Api.Report
  /-- Set by `stop` (the page session ended): the task closes the context and ends. -/
  stopping : IO.Ref Bool
  /-- Monotonic ns when a batch with a `start()` (op 181) was given; 0 when none waits. -/
  startNs : IO.Ref Nat
  /-- Set by the task when it has ended (its sink is closed). -/
  ended : IO.Ref Bool

/-- A rendering task and what it shares. -/
structure Handle where
  shared : Shared
  task : Task (Except IO.Error Unit)

/-- The parameters of the first message (190) of a context's outbox. -/
structure Params where
  id : Nat
  rate : Float
  channels : Nat
  target : Nat
  running : Bool

/-- The fields of message 190: `[ID, RATE (binary64), CHANNELS, TARGET, STATE]` (`Api.newAudioContextOp`). -/
def Params.ofMessage (fs : Array ByteArray) : Option Params := do
  let id ← (Api.natArg fs 0).toOption
  let rate ← (Api.f64Arg fs 1).toOption
  let ch ← (Api.natArg fs 2).toOption
  let target ← (Api.natArg fs 3).toOption
  let st ← (Api.natArg fs 4).toOption
  pure { id, rate, channels := ch, target, running := st == 1 }

/-- Ring capacity for a target (plan 13.4): 4 times the target, at least 8192 frames. -/
def capacityOf (target : Nat) : Nat := max 8192 (4 * target)

/-- Render quanta in a batch at most: the target in quanta, plus one. -/
def quantaPerBatch (target quantum : Nat) : Nat := target / (max 1 quantum) + 1

/-- The interleaved frames of a block: frame `i`, channel `c` at `i * channels + c`; a channel the
block does not have is 0. -/
def interleave (b : Kernels.Block) (channels n : Nat) : FloatArray := Id.run do
  let mut out := FloatArray.emptyWithCapacity (channels * n)
  for i in [0:n] do
    for c in [0:channels] do
      out := out.push (Kernels.getF (b.getD c ⟨#[]⟩) i)
  return out

/-- True when a value of the block is not 0. -/
def audible (b : Kernels.Block) : Bool :=
  b.any fun ch => ch.data.any (· != 0.0)

def traceOn : BaseIO Bool := do
  return (← IO.getEnv "FOAFNAUT_AUDIO_TRACE") != some "0"

def trace (on : Bool) (fields : List (String × String)) : BaseIO Unit := do
  if on then
    let t ← IO.monoMsNow
    let body := ",".intercalate (fields.map fun (k, v) => s!"\"{k}\":{v}")
    let _ ← (IO.eprintln s!"\{\"t\":{t},{body}}").toBaseIO

def num (x : Nat) : String := toString x
/-- A JSON string of `s` (quotes, backslashes and control characters escaped). -/
def quote (s : String) : String :=
  "\"" ++ String.join (s.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\" else if c.toNat < 32 then " " else c.toString) ++ "\""
def flo (x : Float) : String := if x.isFinite then toString x else "null"

/-! ## Threads -/

/-- True when a dedicated task runs on a thread of its own. With no task manager a task runs at
once on the calling thread: a probe task that sleeps 50 ms makes `IO.asTask` return after it. With
a task manager it returns at once. Not in the Wasm build; not with `FOAFNAUT_LEAN_THREADS=0`. The
caller keeps the answer (`WebDocument.Engine.audioDevice`): this module holds no global state. -/
def threadsAvailable : BaseIO Bool := do
  if System.Platform.isEmscripten then return false
  if (← IO.getEnv "FOAFNAUT_LEAN_THREADS") == some "0" then return false
  let t0 ← IO.monoMsNow
  let _ ← IO.asTask (IO.sleep 50) Task.Priority.dedicated
  let t1 ← IO.monoMsNow
  return t1 - t0 < 40

/-! ## The task -/

/-- What the task keeps between batches. -/
structure Local where
  st : Api.State
  plan : Render.Plan
  state : Api.RtState
  reported : Std.HashSet Nat := {}
  divergences : Nat := 0
  /-- Wall ms of the last `native-audio` line, and the render ns, ahead minimum and maximum since. -/
  lastTrace : Nat := 0
  renderNs : Nat := 0
  framesAtTrace : Nat := 0
  aheadMin : Nat := 0
  aheadMax : Nat := 0

/-- Apply one batch of messages. 191 is the task's own: `resume`, `suspend`, `close`. Answers the
new local state, the state changes and the control calls carried out. -/
def applyBatch (p : Params) (sink : Sink.Sink) (on : Bool) (l : Local) (msgs : Array (Nat × Array ByteArray)) :
    BaseIO (Local × Array Api.RtState × Array Nat) := do
  let mut l := l
  let mut changes : Array Api.RtState := #[]
  let mut confirmed : Array Nat := #[]
  let mut graph := false
  for (code, fs) in msgs do
    if code == 190 then continue
    if code == 191 then
      let verb := Api.strArg fs 1
      let call := (Api.natArg fs 2).toOption.getD 0
      let next : Api.RtState :=
        if verb == "resume" then .running else if verb == "suspend" then .suspended else .closed
      if l.state != .closed then
        if next != l.state then
          changes := changes.push next
          l := { l with state := next }
          Sink.pause sink (next != .running)
      confirmed := confirmed.push call
    else
      let (s', r) := Api.op l.st code fs
      match r with
      | .ok _ => l := { l with st := s' }; graph := true
      | .error e =>
        l := { l with divergences := l.divergences + 1 }
        trace on [("type", "\"native-audio-divergence\""), ("ctx", num p.id), ("op", num code), ("error", toString e)]
  if graph then
    match l.st.contexts[p.id]? with
    | some c => l := { l with plan := Render.Plan.of c.state.graph }
    | none => pure ()
  return (l, changes, confirmed)

/-- Render quanta while the ring holds fewer than the target, at most `quantaPerBatch`. Answers the
new local state, the source ids that ended, and whether an audible frame was written. -/
def fill (p : Params) (sink : Sink.Sink) (l : Local) : BaseIO (Local × Array Nat × Bool) := do
  let some c := l.st.contexts[p.id]? | return (l, #[], false)
  let q := c.state.quantum
  let mut c := c
  let mut l := l
  let mut heard := false
  let t0 ← IO.monoNanosNow
  for _ in [0:quantaPerBatch p.target q] do
    let cnt ← Sink.counters sink
    let written := cnt[0]!.toUInt64.toNat
    let read := cnt[1]!.toUInt64.toNat
    let ahead := written - read
    l := { l with aheadMin := if l.aheadMax == 0 && l.aheadMin == 0 then ahead else min l.aheadMin ahead,
                  aheadMax := max l.aheadMax ahead }
    if ahead ≥ p.target then break
    let (st', block) := Render.renderQuantumWith c.state l.plan
    let frames := interleave block p.channels q
    let taken ← Sink.write sink frames
    if taken == 0 then break
    c := { c with state := st' }
    if audible block then heard := true
  let t1 ← IO.monoNanosNow
  let ended := (Api.endedIds c).filter (fun i => !l.reported.contains i)
  let reported := ended.foldl (fun h i => h.insert i) l.reported
  let st := { l.st with contexts := l.st.contexts.insert p.id c }
  return ({ l with st, reported, renderNs := l.renderNs + (t1 - t0) }, ended.toArray, heard)

/-- Publish the counters and add the events to the report. -/
def publish (sh : Shared) (sink : Sink.Sink) (l : Local) (p : Params) (ended : Array Nat)
    (changes : Array Api.RtState) (confirmed : Array Nat) : BaseIO Unit := do
  let cnt ← Sink.counters sink
  let rendered := match l.st.contexts[p.id]? with | some c => c.state.frame | none => 0
  sh.report.modify fun r =>
    { r with framesRendered := rendered, framesPlayed := cnt[1]!.toUInt64.toNat,
             underruns := cnt[2]!.toUInt64.toNat, latencyFrames := cnt[4]!.toUInt64.toNat,
             ended := r.ended ++ ended, stateChanges := r.stateChanges ++ changes,
             confirmed := r.confirmed ++ confirmed }

/-- The loop of a rendering task. Ends when the context is closed (a `close()` message) or when the
engine stops it (`stop`): an outside event, so a `repeat` loop (`CLAUDE.md`, "Loops yes, new partial
def no"). -/
def serveWith (sh : Shared) (p : Params) (on : Bool) (sink : Sink.Sink) (c0 : Context.OfflineContext) : BaseIO Unit := do
  let st : Api.State := { contexts := ({} : Std.HashMap Nat Context.OfflineContext).insert p.id c0, next := p.id + 1 }
  let start : Api.RtState := if p.running then .running else .suspended
  Sink.pause sink (!p.running)
  let mut l : Local := { st, plan := Render.Plan.of c0.state.graph, state := start, lastTrace := ← IO.monoMsNow }
  if p.running then sh.report.modify fun r => { r with stateChanges := r.stateChanges.push .running }
  repeat
    let msgs ← sh.inbox.modifyGet fun m => (m, #[])
    let (l1, changes, confirmed) ← applyBatch p sink on l msgs
    l := l1
    let stop ← sh.stopping.modifyGet fun b => (b, b)
    if stop && l.state != .closed then l := { l with state := .closed }
    if l.state == .closed then
      publish sh sink l p #[] (if changes.contains .closed then changes else changes.push .closed) confirmed
      break
    let mut ended := #[]
    if l.state == .running then
      let (l2, e, heard) ← fill p sink l
      l := l2
      ended := e
      if heard then
        let s ← sh.startNs.modifyGet fun n => (n, 0)
        if s != 0 then
          let now ← IO.monoNanosNow
          trace on [("type", "\"native-audio-first-sound\""), ("ctx", num p.id),
                    ("handoverToRingMs", flo ((now - s).toFloat / 1e6))]
    publish sh sink l p ended changes confirmed
    let now ← IO.monoMsNow
    if l.state == .running && now - l.lastTrace ≥ 1000 then
      let cnt ← Sink.counters sink
      let rendered := match l.st.contexts[p.id]? with | some c => c.state.frame | none => 0
      let audioSec := (rendered - l.framesAtTrace).toFloat / p.rate
      trace on [("type", "\"native-audio\""), ("ctx", num p.id), ("framesRendered", num rendered),
        ("framesPlayed", num cnt[1]!.toUInt64.toNat), ("underruns", num cnt[2]!.toUInt64.toNat),
        ("silentFrames", num cnt[3]!.toUInt64.toNat),
        ("renderMsPerAudioSec", flo (if audioSec > 0.0 then l.renderNs.toFloat / 1e6 / audioSec else 0.0)),
        ("aheadMin", num l.aheadMin), ("aheadMax", num l.aheadMax),
        ("latencyFrames", num cnt[4]!.toUInt64.toNat), ("divergences", num l.divergences)]
      l := { l with lastTrace := now, renderNs := 0, framesAtTrace := rendered, aheadMin := 0, aheadMax := 0 }
    -- Running: sleep until about half of the target has played (at least 1 ms). Otherwise wait
    -- for a message in steps of 5 ms.
    let ms := if l.state == .running then max 1 (((p.target.toFloat / p.rate) * 500.0).toUInt32) else 5
    IO.sleep ms
  let cnt ← Sink.counters sink
  Sink.close sink
  trace on [("type", "\"native-audio-end\""), ("ctx", num p.id),
    ("framesPlayed", num cnt[1]!.toUInt64.toNat), ("underruns", num cnt[2]!.toUInt64.toNat),
    ("divergences", num l.divergences)]
  sh.ended.modify fun _ => true

/-- The body of a rendering task: open the sink, then `serveWith`. A context or a sink that can not
be made ends the task with the state `closed` reported. -/
def serve (sh : Shared) (p : Params) (spec : String) : BaseIO Unit := do
  let on ← traceOn
  let fail := fun (why : String) => do
    trace on [("type", "\"native-audio-end\""), ("ctx", num p.id), ("error", quote why)]
    sh.report.modify fun r => { r with stateChanges := r.stateChanges.push .closed }
    sh.ended.modify fun _ => true
  match Context.OfflineContext.new 2 1 p.rate with
  | .error _ => fail "context"
  | .ok c =>
    match ← (Sink.open spec p.rate p.channels.toUInt32 (capacityOf p.target).toUInt32).toBaseIO with
    | .error e => fail (toString e)
    | .ok sink => serveWith sh p on sink { c with length := 0 }

/-! ## What the engine's IO layer calls -/

/-- Start the rendering task of a context whose first message is 190. `initial` (the rest of that
batch) is in the inbox before the task starts, so the task renders no quantum before the batch's
graph is there: a source started at 0 starts at frame 0, as in an `OfflineAudioContext`. -/
def startTask (p : Params) (spec : String) (initial : Array (Nat × Array ByteArray)) : BaseIO Handle := do
  let now ← IO.monoNanosNow
  let shared : Shared :=
    { inbox := ← IO.mkRef initial, report := ← IO.mkRef {}, stopping := ← IO.mkRef false,
      startNs := ← IO.mkRef (if initial.any (·.1 == 181) then now else 0), ended := ← IO.mkRef false }
  let task ← IO.asTask (serve shared p spec) Task.Priority.dedicated
  return { shared, task }

/-- Give a batch of messages (plan 13.2: the messages of one page task, as one batch). -/
def give (h : Handle) (msgs : Array (Nat × Array ByteArray)) : BaseIO Unit := do
  if msgs.isEmpty then return
  if msgs.any (·.1 == 181) then
    let now ← IO.monoNanosNow
    h.shared.startNs.modify fun n => if n == 0 then now else n
  h.shared.inbox.modify fun m => m ++ msgs

/-- The report since the last call; its events are taken. -/
def takeReport (h : Handle) : BaseIO Api.Report :=
  h.shared.report.modifyGet fun r =>
    (r, { r with ended := #[], stateChanges := #[], confirmed := #[], rejected := #[] })

/-- Ask the task to close its context and end. -/
def stop (h : Handle) : BaseIO Unit := h.shared.stopping.modify fun _ => true

def hasEnded (h : Handle) : BaseIO Bool := h.shared.ended.modifyGet fun b => (b, b)

/-! ## The engine's tables -/

/-- The rendering tasks of one engine, by (page session, context). -/
abbrev Tasks := Std.HashMap (Nat × Nat) Handle

/-- The audio output: the sink spec and the device's preferred rate and channels; `none` when there
is no output (no threads, or the sink kind gives no device). Asked once by each engine. -/
def device : BaseIO (Option (String × Float × Nat)) := do
  if !(← threadsAvailable) then return none
  let spec ← Sink.defaultSpec
  let info ← Sink.deviceInfo spec
  if info.size < 2 then return none
  return some (spec, info[0]!, info[1]!.toUInt64.toNat)

/-- Before a page action of session `sid`: merge the reports of its tasks into `audio`, and drop
the tasks that ended. `nowMs` is the page clock (for `getOutputTimestamp().performanceTime`). -/
def before (tasks : Tasks) (sid : Nat) (audio : Api.State) (nowMs : Nat) : BaseIO (Tasks × Api.State) := do
  let mut audio := audio
  let mut tasks := tasks
  for ((s, ctx), h) in tasks.toList do
    if s != sid then continue
    let r ← takeReport h
    audio := Api.applyReport audio ctx { r with timeMs := nowMs.toFloat }
    if ← hasEnded h then tasks := tasks.erase (s, ctx)
  return (tasks, audio)

/-- After a page action of session `sid`: each outbox goes to its task, one batch per context; a
context whose first message is 190 gets a new task. -/
def after (tasks : Tasks) (sid : Nat) (spec : String) (audio : Api.State) : BaseIO (Tasks × Api.State) := do
  let (audio, boxes) := Api.takeOutbox audio
  let mut tasks := tasks
  for (ctx, msgs) in boxes do
    match tasks[(sid, ctx)]? with
    | some h => give h msgs
    | none =>
      match msgs[0]? with
      | some (190, fs) =>
        match Params.ofMessage fs with
        | some p =>
          let h ← startTask p spec (msgs.extract 1 msgs.size)
          tasks := tasks.insert (sid, ctx) h
        | none => pure ()
      | _ => pure ()
  return (tasks, audio)

/-- Stop every task of the sessions that are not in `live` (the page session ended). -/
def stopGone (tasks : Tasks) (live : List Nat) : BaseIO Tasks := do
  let mut tasks := tasks
  for ((s, ctx), h) in tasks.toList do
    if !live.contains s then
      stop h
      tasks := tasks.erase (s, ctx)
  return tasks

end L4Factoidal.WebAudio.Realtime
