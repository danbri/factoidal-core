import L4Factoidal.WebAudio.Decode
import L4Factoidal.WebAudio.RenderSide
import L4Factoidal.WebAudio.Sink
import WebScripts

/-! # WebAudioRun: real-time Web Audio contexts in the engine

Step D3, first part, of docs/designissues/2026-11-26-foafnaut-audio-plan.md, section 13 (issue
https://github.com/danbri/factoidal-core/issues/1169): `new AudioContext()` in a page plays
through the engine's audio output (`L4Factoidal.WebAudio.Sink`, `formal/lean4/ffi/audio_sink.c`).

- **One dedicated Lean task per real-time context** (`serve`; `Task.Priority.dedicated`, a thread
  of its own). It holds the context's rendering side (`L4Factoidal.WebAudio.RenderSide`, pure),
  made in the task from the first message, so the state never crosses threads. Its loop (plan
  13.4): take the inbox and apply the messages (`RenderSide.applyBatch`); while running, read the
  sink's counters and render the quanta that bring the frames ahead of the output to the context's
  target (`RenderSide.quantaFor`), each written to the sink when it is rendered
  (`RenderSide.quantum`), except while the output takes nothing yet (after the sink opens, or
  after a `resume()`: the sink stays paused until then), when they go in one write
  (`RenderSide.fill`); collect the sources that ended; publish the report; sleep until about half
  the target has played (at least 1 ms). While suspended it waits for a message (a promise the
  poster resolves, as `WebSession.serve` waits). The sink is opened by the task with the context's
  rate, the device's channels and a capacity of 4 times the target (at least 8192 frames), paused
  while the context is suspended and closed when it closes.
- **The registry** (`Registry`, a field of `WebDocument.Engine`): the runs by (page session,
  context), the audio output (asked once, `probe`) and the sink spec.
- **`before`** (before a `scriptSession` call): the engine's audio output goes to `Held.audio`
  (a session started by the call takes it, `WebScripts.audioLimits`); the reports of the page's
  runs are merged into the page's Web Audio state (`Api.applyReport`, with the page clock as the
  report's time); the page callbacks of the contexts with events are queued as tasks
  (`Api.takeWakeups`, `EventLoop.queueTask .other`, as `WebScripts.gpuGive` does).
- **`after`** (after it): the runs of a page session that is gone end (their sinks close, the
  engine waits for their tasks); the page's outboxes (`Api.takeOutbox`) go to the runs, a new run
  for each context whose first message is its opening (190), and the task is woken.
- **`endAll`**: when the engine session ends, every run ends (`WebDocument.engineEnd`: the C
  shim's `web_session_free`, the end of a session's task in `WebSession.serve`, and the document
  op `audioEnd`, which a host sends before it drops an engine it does not free, such as the
  default session of a tab worker's own copy of the library).

What crosses threads: the messages (op codes and their fields), the reports and the measures,
through `Shared`'s refs, each used with `modify` and `modifyGet` only
(`skills/lean4-performance`, "Values that two threads can reach").

With no task manager (the Wasm build, or `FOAFNAUT_LEAN_THREADS=0`, `web_render_shim.c`) a task
runs at once on the calling thread, so a real-time task would never return: the device stays
`none` and `new AudioContext()` answers `NotSupportedError`. Whether the task manager runs is
asked of Lean itself (`taskManagerRuns`: a dedicated task runs on another thread only then), so
the engine needs no C entry point for it (the render command line, `WebRenderCLI`, links these
modules without `web_render_shim.c`).

Measures (plan 13.9): `Stats`, read by the document op `audioRuns`.

## Decode jobs (ops 194 and 195, stage C)

`decodeAudioData` is a job of the page's Web Audio state (`Api.DecodeJob`). In `after`, the jobs
the page queued (`Api.takeDecodeJobs`) each start a task of the task pool
(`BaseIO.asTask`, default priority, not a dedicated thread) that runs
`WebAudio.Decode.decodeAudioData` with the pinned decoder modules and packs the samples as binary32
(`Api.channelsBytes`). In `before` (and in `after`, for a task that has already finished) the
finished tasks give their result to the page (`Api.finishDecode`, which queues the page callback
as a task); a job with no result asks for turns (`Api.needsTurns`). The modules are read once per
engine (`loadDecoders`) from `FOAFNAUT_MEDIA_DECODERS`, else `~/.cache/factoidal/media-decoders`
(`tools/fetch-media-decoders.sh`), each checked with `L4Factoidal.Media.Modules.check`; a module that is
missing or has other bytes than its pin makes a file that needs it answer `NotSupportedError`
(code -23). The format a decode does not read, or data a decoder refuses, answers `EncodingError`
(-30). With no task manager (the Wasm build, or `FOAFNAUT_LEAN_THREADS=0`) `BaseIO.asTask` runs
the decode at once on the calling thread, inside `after`: the answer is right and the page is
blocked for the decode (only slower).

## Not done

- A host that drops an engine with none of the steps of `endAll` (no `close`, no session end, no
  `audioEnd`) leaves its runs playing until the process ends; if the library is then unloaded
  (`dlclose`), a run's thread runs unloaded code. Task sessions pin the library
  (`web_render_shim.c`); real-time runs do not.
- The `native-audio` trace line and the
  `--perf-summary` block of plan 13.9 (host work).
-/

namespace WebAudioRun

open L4Factoidal
open L4Factoidal.WebAudio
open L4Factoidal.WasmVM.Hosts

/-- Measures of one run (plan 13.9), kept by its task. -/
structure Stats where
  /-- The task's thread (`IO.getTID`; on Linux `/proc/self/task/TID`). -/
  tid : UInt64 := 0
  /-- Render quanta written to the sink. -/
  quanta : Nat := 0
  /-- Monotonic-clock time of rendering and writing, in nanoseconds. -/
  renderNs : Nat := 0
  /-- Frames ahead of the output when the task looked, before it rendered (the least), and after
  it wrote (the most). Looked at only after the first write. -/
  aheadMin : Nat := 0
  aheadMax : Nat := 0
  looks : Nat := 0
  /-- Quanta the sink refused, each lost. Not expected: the task renders only while fewer frames
  than the target are ahead of the output, and the ring holds at least 4 times the target. -/
  refused : Nat := 0
  divergence : Nat := 0
  /-- The sink's counters (`Sink.counters`). -/
  written : Nat := 0
  read : Nat := 0
  underruns : Nat := 0
  silent : Nat := 0
  sinkError : String := ""
  finished : Bool := false
  /-- The rendering side's state (`Api.RtState.code`). -/
  state : Nat := 0
  /-- Events (sources ended, changes of state, calls carried out or refused) the task published,
  and those the engine took. -/
  eventsOut : Nat := 0
  eventsIn : Nat := 0
  deriving Inhabited

/-- What a run's task and the engine share. -/
structure Shared where
  /-- Messages not taken, in order; `none` once the task has ended. -/
  inbox : IO.Ref (Option (Array (Nat × Array ByteArray)))
  /-- The promise the task waits on while its context is suspended; the poster resolves it. -/
  wake : IO.Ref (Option (IO.Promise Unit))
  /-- The reports the engine has not taken, merged (`RenderSide.mergeReport`). -/
  report : IO.Ref (Option Api.Report)
  stats : IO.Ref Stats

/-- A rendering task: the page session and the context it renders. -/
structure Run where
  page : Nat
  ctx : Nat
  shared : Shared
  task : Task Unit

/-- The pinned decoder modules that were found and passed `L4Factoidal.Media.Modules.check`, and the files of
the pins that were not (missing, or other bytes). -/
structure Decoders where
  modules : Array (String × ByteArray) := #[]
  missing : Array String := #[]

/-- A decode job of a page running on a task: its result in the form `Api.finishDecode` takes. -/
structure DecodeRun where
  page : Nat
  job : Nat
  task : Task (Except Int (Nat × Nat × Float × ByteArray))

/-- What the engine keeps for real-time audio (`WebDocument.Engine.audio`). -/
structure Registry where
  runs : Array Run := #[]
  /-- The decode jobs of the page sessions, running or finished and not yet given to a page. -/
  decodes : Array DecodeRun := #[]
  /-- The decoder modules, read when the first job starts. -/
  decoders : Option Decoders := none
  /-- The audio output, asked once (`probe`); `none` before. -/
  env : Option WebScripts.AudioEnv := none
  /-- The sink spec (`Sink.defaultSpec`), read with `env`. -/
  spec : String := "null"

/-! ## The output -/

/-- Lean's task manager runs: a dedicated task then runs on a thread of its own. Without it a task
runs at once on the calling thread (and its thread id is the caller's). -/
def taskManagerRuns : BaseIO Bool := do
  let here ← IO.getTID
  let there ← IO.wait (← BaseIO.asTask IO.getTID Task.Priority.dedicated)
  return here != there

/-- The audio output (the sink's preferred rate and channels, `Sink.deviceInfo`) when the task
manager runs. Asked once per engine. The permission to start with no user activation is not here:
it comes with each session's start request (`WebScripts.audioLimits`). -/
def probe (reg : Registry) : BaseIO (Registry × WebScripts.AudioEnv) := do
  match reg.env with
  | some env => return (reg, env)
  | none =>
    let spec ← Sink.defaultSpec
    let device ← if ← taskManagerRuns then do
        let info ← Sink.deviceInfo spec
        let rate := info.get! 0
        let ch := (info.get! 1).toUInt64.toNat
        pure (if rate ≥ 3000.0 && rate ≤ 768000.0 && 0 < ch && ch ≤ 32 then some (rate, ch) else none)
      else pure none
    let env : WebScripts.AudioEnv := { device }
    return ({ reg with env := some env, spec }, env)

/-! ## The rendering task -/

/-- The messages not taken (none once the task has ended). -/
@[inline] def take (sh : Shared) : BaseIO (Array (Nat × Array ByteArray)) :=
  sh.inbox.modifyGet fun
    | some m => (m, some #[])
    | none => (#[], none)

/-- A message waits in the inbox. -/
@[inline] def hasMessages (sh : Shared) : BaseIO Bool :=
  sh.inbox.modifyGet fun m => ((m.map (!·.isEmpty)).getD false, m)

/-- The number of events of a report. -/
def eventCount (r : Api.Report) : Nat :=
  r.ended.size + r.stateChanges.size + r.confirmed.size + r.rejected.size

/-- A report with no event (the counters only). -/
def quiet (r : Api.Report) : Bool := eventCount r == 0

/-- Add a report for the engine (merged with one it has not taken). -/
@[inline] def publish (sh : Shared) (rep : Api.Report) (state : Api.RtState) : BaseIO Unit := do
  sh.report.modify fun
    | some a => some (RenderSide.mergeReport a rep)
    | none => some rep
  sh.stats.modify fun st => { st with eventsOut := st.eventsOut + eventCount rep, state := state.code }

/-- `f ()`, evaluated when this action runs (so not moved out of a timed span). -/
@[noinline] def evalNow {α : Type} (f : Unit → α) : BaseIO α := pure (f ())

/-- The sink's counters as whole numbers: written, read, under-run events, silent frames, device
latency frames. -/
def countersOf (c : FloatArray) : Nat × Nat × Nat × Nat × Nat :=
  let n := fun (i : Nat) => (c.get! i).toUInt64.toNat
  (n 0, n 1, n 2, n 3, n 4)

/-- The loop of one real-time context (plan 13.4), on its own dedicated task. `open190` holds the
fields of the context's first message; the rendering side is made here, so it never crosses
threads. -/
def serve (sh : Shared) (spec : String) (open190 : Array ByteArray) : BaseIO Unit := do
  let tid ← IO.getTID
  sh.stats.modify fun st => { st with tid }
  match RenderSide.ofOpen open190 with
  | none => sh.stats.modify fun st => { st with sinkError := "the first message is not an opening", finished := true }
  | some rs0 =>
    let capacity := max 8192 (4 * rs0.target)
    let opened ← (Sink.open spec rs0.rate rs0.channels.toUInt32 capacity.toUInt32).toBaseIO
    let sink? : Option Sink.Sink := match opened with
      | .ok s => some s
      | .error _ => none
    if let .error e := opened then sh.stats.modify fun st => { st with sinkError := toString e }
    if let some s := sink? then Sink.pause s (rs0.state != .running)
    -- about half the target, in ms, at least 1
    let sleepMs : UInt32 := (max 1 ((Float.ofNat rs0.target * 500.0 / rs0.rate).floor.toUInt64.toNat)).toUInt32
    let mut rs := rs0
    -- The output takes frames: it has had a write since it was opened or last paused, and it is not
    -- paused. Until then it takes nothing (`Sink`: a consumer starts at the first write), and the
    -- sink stays paused after a `resume` until that write.
    let mut flowing := false
    -- Ends when the context closes: by the page's `close()` or because its page is gone, a message
    -- from the engine on another thread: an outside event, so a `repeat` loop (CLAUDE.md, "Loops
    -- yes, new partial def no").
    repeat
      let msgs ← take sh
      if !msgs.isEmpty then
        let was := rs.state
        rs := RenderSide.applyBatch rs msgs sink?.isNone
        if rs.state != was then
          if let some s := sink? then
            match rs.state with
            | .running => pure ()
            | .suspended => Sink.pause s true; flowing := false
            | .closed => Sink.close s
      if rs.state == .closed then break
      match sink? with
      | some s =>
        if rs.state == .running then
          let (written, read, _, _, _) := countersOf (← Sink.counters s)
          let ahead := written - read
          let k := RenderSide.quantaFor rs.target ahead rs.c.state.quantum
          let t0 ← IO.monoNanosNow
          let mut wrote := 0
          if flowing then
            -- Plan 13.4, step 3: one quantum at a time, rendered and then written, so the output
            -- has the next frames after one quantum's work.
            for _ in [0:k] do
              let (rs', frames) ← evalNow fun _ => RenderSide.quantum rs
              rs := rs'
              if (← Sink.write s frames) > 0 then wrote := wrote + 1
          else
            -- The output takes nothing yet: the quanta up to the target in one write
            -- (`RenderSide.fill`), so that the output starts with the whole target ahead of it
            -- (the `null` and `wav` consumers take 256 frames at once, more than one quantum).
            let (rs', frames) ← evalNow fun _ => RenderSide.fill k rs ⟨#[]⟩
            rs := rs'
            if k > 0 then
              if (← Sink.write s frames) > 0 then wrote := k
            Sink.pause s false
            flowing := true
          let t1 ← IO.monoNanosNow
          rs := RenderSide.noteEnded rs
          let (written', read', under, silent, latency) := countersOf (← Sink.counters s)
          let (rs2, rep) := RenderSide.takeReport rs read' under latency
          rs := rs2
          publish sh rep rs.state
          let div := rs.divergence
          sh.stats.modify fun st =>
            let first := written > 0
            { st with quanta := st.quanta + wrote, renderNs := st.renderNs + (t1 - t0),
                      aheadMin := if !first then st.aheadMin else if st.looks == 0 then ahead else min st.aheadMin ahead,
                      aheadMax := max st.aheadMax (written' - read'),
                      looks := if first then st.looks + 1 else st.looks,
                      refused := st.refused + (k - wrote),
                      divergence := div, written := written', read := read', underruns := under, silent }
          IO.sleep sleepMs
        else
          -- suspended: the events so far, then wait for a message
          let (_, read', under, _, latency) := countersOf (← Sink.counters s)
          let (rs2, rep) := RenderSide.takeReport rs read' under latency
          rs := rs2
          if !quiet rep then publish sh rep rs.state
          let p ← (IO.Promise.new : BaseIO (IO.Promise Unit))
          sh.wake.modify fun _ => some p
          if !(← hasMessages sh) then
            let _ ← IO.wait p.result?
      | none =>
        -- no output: control calls are answered (a `resume` is refused), nothing renders
        let (rs2, rep) := RenderSide.takeReport rs 0 0 0
        rs := rs2
        if !quiet rep then publish sh rep rs.state
        let p ← (IO.Promise.new : BaseIO (IO.Promise Unit))
        sh.wake.modify fun _ => some p
        if !(← hasMessages sh) then
          let _ ← IO.wait p.result?
    -- closed: the last report (the close's confirmation), the sink closed, the inbox taken away
    let latency ← match sink? with
      | some s => do let (_, _, _, _, l) := countersOf (← Sink.counters s); pure l
      | none => pure 0
    let (_, rep) := RenderSide.takeReport rs 0 0 latency
    publish sh rep rs.state
    if let some s := sink? then Sink.close s
    let _ ← sh.inbox.modifyGet fun _ => ((), (none : Option (Array (Nat × Array ByteArray))))
    sh.stats.modify fun st => { st with finished := true }

/-- A new run of context `ctx` of page session `page`: its task is started with the opening's
fields; the messages after the opening wait in its inbox. -/
def startRun (spec : String) (page ctx : Nat) (open190 : Array ByteArray)
    (rest : Array (Nat × Array ByteArray)) : BaseIO Run := do
  let inbox ← IO.mkRef (some rest)
  let wake ← IO.mkRef (none : Option (IO.Promise Unit))
  let report ← IO.mkRef (none : Option Api.Report)
  let stats ← IO.mkRef ({} : Stats)
  let sh : Shared := { inbox, wake, report, stats }
  let task ← BaseIO.asTask (serve sh spec open190) Task.Priority.dedicated
  return { page, ctx, shared := sh, task }

/-- Post messages to a run and wake its task; false when the task has ended. -/
def post (r : Run) (ms : Array (Nat × Array ByteArray)) : BaseIO Bool := do
  let ok ← r.shared.inbox.modifyGet fun
    | some q => (true, some (q ++ ms))
    | none => (false, none)
  if let some p ← r.shared.wake.modifyGet (fun w => (w, none)) then p.resolve ()
  return ok

/-- End a run whose page is gone (message 0: closed with no event) and wait for its task. -/
def endRun (r : Run) : BaseIO Unit := do
  let _ ← post r #[(0, #[])]
  let _ ← IO.wait r.task

/-- End every run (their sinks close) and wait for their tasks: the engine session ends
(`WebDocument.engineEnd`). -/
def endAll (reg : Registry) : BaseIO Registry := do
  for r in reg.runs do endRun r
  return { reg with runs := #[] }

/-! ## The engine's steps around a page task -/

/-- `f` on the page host of the held session (either engine), with its answer; `none` with no
session. -/
def withHost {α : Type} (held : WebScripts.Held) (f : Page.Host → Page.Host × α) : WebScripts.Held × Option α :=
  match held.leanSession with
  | some (id, s, m) =>
    let (h, x) := f s.host
    ({ held with leanSession := some (id, s.setHost h, m) }, some x)
  | none =>
    match held.session with
    | some (id, s, m) =>
      let (h, x) := f s.host
      ({ held with session := some (id, { s with host := h }, m) }, some x)
    | none => (held, none)

/-- The Web Audio state of the held session. -/
def audioOf (held : WebScripts.Held) : Option Api.State :=
  match held.leanSession, held.session with
  | some (_, s, _), _ => some s.host.web.audio
  | none, some (_, s, _) => some s.host.web.audio
  | none, none => none

/-! ## Decode jobs -/

/-- The directory of the decoder modules: `FOAFNAUT_MEDIA_DECODERS`, else
`~/.cache/factoidal/media-decoders` (where `tools/fetch-media-decoders.sh` puts them). -/
def decoderDir : BaseIO String := do
  match ← IO.getEnv "FOAFNAUT_MEDIA_DECODERS" with
  | some d => if d.isEmpty then pure "" else pure d
  | none =>
    match ← IO.getEnv "HOME" with
    | some h => pure (h ++ "/.cache/factoidal/media-decoders")
    | none => pure ""

/-- Read the pinned modules from `decoderDir`; each is kept only when it has its pin's size and
SHA-256 (`L4Factoidal.Media.Modules.check`). -/
def loadDecoders : BaseIO Decoders := do
  let dir ← decoderDir
  let mut mods : Array (String × ByteArray) := #[]
  let mut missing : Array String := #[]
  for p in L4Factoidal.Media.Modules.pins do
    match ← (IO.FS.readBinFile (dir ++ "/" ++ p.file)).toBaseIO with
    | .ok b =>
      match L4Factoidal.Media.Modules.check p.file b with
      | .ok _ => mods := mods.push (p.file, b)
      | .error _ => missing := missing.push p.file
    | .error _ => missing := missing.push p.file
  return { modules := mods, missing }

/-- The code of a decode error. A file that needs a module that is not there answers -23, as does
a context rate outside the supported range; the rest is -30. `Decode.getModule` words the first
as "decoder module FILE was not given". -/
def errorCode : WebAudio.Decode.DecodeError → Int
  | .notSupported _ => Api.errNotSupported
  | .encoding d => if (d.splitOn "decoder module ").length > 1 then Api.errNotSupported else Api.errEncoding

/-- One decode job, in the form of `Api.finishDecode`'s result: channels, length, rate and the
samples as binary32, channel by channel. -/
def decodeJob (dec : Decoders) (rate : Float) (bytes : ByteArray) :
    BaseIO (Except Int (Nat × Nat × Float × ByteArray)) := do
  let find := fun (n : String) => (dec.modules.find? (·.1 == n)).map (·.2)
  match ← (WebAudio.Decode.decodeAudioData bytes rate find).toBaseIO with
  | .error _ => return .error Api.errEncoding
  | .ok (.error e) => return .error (errorCode e)
  | .ok (.ok b) => return .ok (b.numberOfChannels, b.length, b.sampleRate, Api.channelsBytes b.data)

/-- Start a task for each decode job the page of `held` queued. The decoder modules are read before
the first one. -/
def startDecodes (reg : Registry) (held : WebScripts.Held) : BaseIO (Registry × WebScripts.Held) := do
  match WebScripts.currentId held, audioOf held with
  | some page, some audio =>
    if audio.decodeJobs.isEmpty then return (reg, held)
    let (held, jobs) := withHost held fun h =>
      let (a, jobs) := Api.takeDecodeJobs h.web.audio
      ({ h with web := { h.web with audio := a } }, jobs)
    let jobs := jobs.getD #[]
    if jobs.isEmpty then return (reg, held)
    let (reg, dec) ← match reg.decoders with
      | some d => pure (reg, d)
      | none => do let d ← loadDecoders; pure ({ reg with decoders := some d }, d)
    let mut decodes := reg.decodes
    for (job, rate, bytes) in jobs do
      let task ← BaseIO.asTask (decodeJob dec rate bytes)
      decodes := decodes.push { page, job, task }
    return ({ reg with decodes }, held)
  | _, _ => return (reg, held)

/-- Give the page of `held` the results of its decode jobs whose tasks have finished
(`Api.finishDecode`, which queues the job's callback in the page's Web Audio state; the callers
queue it as a task of the page's loop). -/
def finishDecodes (reg : Registry) (held : WebScripts.Held) : BaseIO (Registry × WebScripts.Held) := do
  match WebScripts.currentId held with
  | some page =>
    let mut keep : Array DecodeRun := #[]
    let mut done : Array (Nat × Except Int (Nat × Nat × Float × ByteArray)) := #[]
    for d in reg.decodes do
      if d.page != page then keep := keep.push d
      else if ← IO.hasFinished d.task then done := done.push (d.job, d.task.get)
      else keep := keep.push d
    if done.isEmpty then return (reg, held)
    let (held, _) := withHost held fun h =>
      let a := done.foldl (fun a (job, r) => Api.finishDecode a job r) h.web.audio
      ({ h with web := { h.web with audio := a } }, ())
    return ({ reg with decodes := keep }, held)
  | none => return (reg, held)

/-- Queue the page callbacks of the Web Audio state (`Api.takeWakeups`) as tasks of the page's loop. -/
def queueWakeups (held : WebScripts.Held) : WebScripts.Held :=
  (withHost held fun h =>
    let (a, wakeups) := Api.takeWakeups h.web.audio
    ({ h with web := { h.web with audio := a }, loop := wakeups.foldl (fun l w => l.queueTask .other w) h.loop }, ())).1

/-- Before a `scriptSession` call (plan 13.3): the engine's audio output for the call; the reports
of the page's runs merged into its Web Audio state, and the page callbacks of the contexts with
events queued as tasks. A run whose task has ended leaves the registry once its last report is
taken (the task is looked at before its report is taken). -/
def before (reg : Registry) (held : WebScripts.Held) : BaseIO (Registry × WebScripts.Held) := do
  let (reg, env) ← probe reg
  let held := { held with audio := env }
  let (reg, held) ← finishDecodes reg held
  match WebScripts.currentId held, audioOf held with
  | some page, some audio =>
    let held := if audio.device == env.device then held
      else (withHost held fun h => ({ h with web := { h.web with audio := { h.web.audio with device := env.device } } }, ())).1
    let mine := reg.runs.filter (·.page == page)
    if mine.isEmpty && audio.wakeups.isEmpty then return (reg, held)
    let mut reports : Array (Nat × Api.Report) := #[]
    let mut ended : Array Nat := #[]
    for r in mine do
      if ← IO.hasFinished r.task then ended := ended.push r.ctx
      if let some rep ← r.shared.report.modifyGet (fun x => (x, none)) then
        reports := reports.push (r.ctx, rep)
        r.shared.stats.modify fun st => { st with eventsIn := st.eventsIn + eventCount rep }
    let runs := reg.runs.filter fun r => !(r.page == page && ended.contains r.ctx)
    let (held, _) := withHost held fun h =>
      let now := Float.ofNat h.loop.clock
      let a := reports.foldl (fun a (ctx, rep) => Api.applyReport a ctx { rep with timeMs := now }) h.web.audio
      let (a, wakeups) := Api.takeWakeups a
      ({ h with web := { h.web with audio := a }, loop := wakeups.foldl (fun l w => l.queueTask .other w) h.loop }, ())
    return ({ reg with runs }, held)
  | _, _ => return (reg, held)

/-- After a `scriptSession` call: the runs of a page session that is gone end; the page's control
messages go to its runs, a new run for a context whose first message is its opening. -/
def after (reg : Registry) (held : WebScripts.Held) : BaseIO (Registry × WebScripts.Held) := do
  let cur := WebScripts.currentId held
  for r in reg.runs do
    if some r.page != cur then endRun r
  let reg := { reg with runs := reg.runs.filter fun r => some r.page == cur
                        decodes := reg.decodes.filter fun d => some d.page == cur }
  let (reg, held) ← startDecodes reg held
  -- a decode that has already finished (with no task manager, `asTask` ran it at once)
  let (reg, held) ← finishDecodes reg held
  let held := queueWakeups held
  match cur, audioOf held with
  | some page, some audio =>
    if audio.realtime.isEmpty then return (reg, held)
    let (held, msgs) := withHost held fun h =>
      let (a, msgs) := Api.takeOutbox h.web.audio
      ({ h with web := { h.web with audio := a } }, msgs)
    let msgs := msgs.getD #[]
    let mut reg := reg
    for (ctx, ms) in msgs do
      match reg.runs.find? (fun r => r.page == page && r.ctx == ctx) with
      | some r => let _ ← post r ms
      | none =>
        match ms[0]? with
        | some (190, fs) =>
          let run ← startRun reg.spec page ctx fs (ms.extract 1 ms.size)
          reg := { reg with runs := reg.runs.push run }
        -- a context whose run has ended: nothing renders its messages
        | _ => pure ()
    return (reg, held)
  | _, _ => return (reg, held)

/-! ## Measures -/

private def num (n : Nat) : JSON.Json := .number (toString n)

/-- The answer of the document op `audioRuns`: the output, and each run with its measures. -/
def runsAnswer (reg : Registry) : BaseIO String := do
  let mut items : Array JSON.Json := #[]
  for r in reg.runs do
    let st ← r.shared.stats.modifyGet fun s => (s, s)
    let done ← IO.hasFinished r.task
    items := items.push (.object [("page", num r.page), ("ctx", num r.ctx), ("tid", num st.tid.toNat),
      ("quanta", num st.quanta), ("renderNs", num st.renderNs), ("aheadMin", num st.aheadMin),
      ("aheadMax", num st.aheadMax), ("looks", num st.looks), ("refused", num st.refused),
      ("divergence", num st.divergence), ("written", num st.written), ("read", num st.read),
      ("underruns", num st.underruns), ("silent", num st.silent), ("sinkError", .string st.sinkError),
      ("state", num st.state), ("eventsOut", num st.eventsOut), ("eventsIn", num st.eventsIn),
      ("finished", .bool (done || st.finished))])
  let device : JSON.Json := match reg.env.bind (·.device) with
    | some (rate, ch) => .object [("rate", .number (toString rate.toUInt64.toNat)), ("channels", num ch)]
    | none => .null
  return (JSON.Json.object [("runs", num reg.runs.size), ("items", .array items.toList), ("device", device),
    ("spec", .string reg.spec)]).toString

end WebAudioRun
