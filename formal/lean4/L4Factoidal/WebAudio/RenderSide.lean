/-
L4Factoidal.WebAudio.RenderSide: the rendering side of one real-time `AudioContext`, as pure
functions (step D3 of docs/designissues/2026-11-26-foafnaut-audio-plan.md, section 13; issue
https://github.com/danbri/factoidal-core/issues/1169).

The engine's task (`labs/demos/foafnaut/WebAudioRun.lean`, one dedicated Lean task per context)
holds one `State`. It applies the control messages with `applyBatch`, renders with `fill`, writes
the frames to the audio sink (`WebAudio.Sink`) and publishes `takeReport`. This file has no IO.

- `ofOpen`: the state from the first message of the context's outbox, `(190, [ID, RATE, CHANNELS,
  TARGET, STATE])` (`Api.addRealtime`). The graph state is `Api.rtContext` of the rate, as on the
  control side (`Api.newAudioContextOp_context`).
- `applyBatch`: the messages in order (plan 13.2). Ops 176 to 185 go through `Api.op`, the
  function the control side used, on a state that holds only this context under its id and no
  `Realtime` record, so that nothing is added to an outbox. Node ids are given in op order, so
  both copies give the same ids. A message that fails here is counted (`divergence`): it is not
  expected. Ops 176, 177 and 178 change the graph: the processing order is made again
  (`Render.Plan.of`). A control call (191) sets the state and is confirmed; it is refused on a
  closed context (`control_closed`). Message 0 (from the engine, never from a page) ends a context
  whose page is gone: closed, with no event (Web Audio API, `close()`: "If this control message
  is being run in a reaction to the document being unloaded, abort this algorithm").
- `quantum`: one render quantum (`Render.renderQuantumWith`), the destination's block mixed to the
  output's channel count by the speaker rule (`Mix.matrix .speakers`) when they differ, then
  interleaved (frame after frame, channel after channel). `fill k`: `k` quanta in a row, appended
  in order (`fill_frames`); the current frame advances by `k` quanta (`fill_frame`); the frames
  are `k * channels * quantum` values (`fill_size`). The task writes the frames of one `fill` in
  one all-or-nothing write (`Ring.write`) and keeps the state after it only when the sink took
  them, so a refused write loses no quantum and repeats none.
- `noteEnded`: the scheduled sources that ended since the last call (`Api.endedIds`), each once.
- `takeReport`: the events since the last report and the counters; `mergeReport` joins two reports
  that the engine has not taken yet (counters: the larger; events: appended in order).

## Not done

- The decode jobs of ops 194 and 195 (stage C).
- An `AudioWorklet`, `MediaElementAudioSourceNode` or any node without a kernel here.
-/
import L4Factoidal.WebAudio.Api

namespace L4Factoidal.WebAudio.RenderSide

open L4Factoidal.WebAudio

/-- The rendering side of one real-time context (plan 13.1). -/
structure State where
  /-- The context's id (the same as on the control side). -/
  ctx : Nat
  /-- The rendering side's own copy of the graph state. -/
  c : Context.OfflineContext
  /-- The processing order of `c`'s graph (`Render.Plan.of`), made again when the graph changes. -/
  plan : Render.Plan
  /-- The `[[rendering thread state]]`. -/
  state : Api.RtState
  rate : Float
  /-- The output's channel count (the device's). -/
  channels : Nat
  /-- Frames to keep ahead of the output (plan 13.4). -/
  target : Nat
  /-- Messages that failed here although the control side's op succeeded (plan 13.2). -/
  divergence : Nat := 0
  /-- The sources whose `ended` was reported. -/
  endedSent : Array Nat := #[]
  /-- The events since the last report. -/
  pending : Api.Report := {}

/-- The state of a state code (`Api.RtState.code`). -/
def stateOfCode : Nat → Option Api.RtState
  | 0 => some .suspended
  | 1 => some .running
  | 2 => some .closed
  | _ => none

/-- The fields of the first message of a context's outbox, `[ID, RATE (binary64), CHANNELS,
TARGET, STATE]` (`Api.addRealtime`), checked: 1 to 32 channels, a target above 0, a state code. -/
def openFields (fs : Array ByteArray) : Option (Nat × Float × Nat × Nat × Api.RtState) := do
  let ctx ← (Api.natArg fs 0).toOption
  let rate ← (Api.f64Arg fs 1).toOption
  let channels ← (Api.natArg fs 2).toOption
  let target ← (Api.natArg fs 3).toOption
  let state ← stateOfCode (← (Api.natArg fs 4).toOption)
  if channels == 0 || channels > 32 || target == 0 then none
  pure (ctx, rate, channels, target, state)

/-- The rendering side of the context opened by `fs` (`openFields`); `none` for fields that are not
those, or a rate `Api.rtContext` refuses. -/
def ofOpen (fs : Array ByteArray) : Option State := do
  let (ctx, rate, channels, target, state) ← openFields fs
  let c ← (Api.rtContext rate).toOption
  -- A context that starts running reports it in its first report: the control side answered
  -- `suspended` (Web Audio API, the constructor), and the page's `statechange` comes from this.
  pure { ctx, c, plan := Render.Plan.of c.state.graph, state, rate, channels, target,
         pending := { stateChanges := if state == .running then #[.running] else #[] } }

/-- Says: the graph state of an opened rendering side is `Api.rtContext` of the rate it read, the
function op 190 used on the control side (`Api.newAudioContextOp_context`). Does not say: that
the control side's context has not changed since (its later ops are messages too). -/
theorem ofOpen_context (fs : Array ByteArray) (rs : State) (h : ofOpen fs = some rs) :
    Api.rtContext rs.rate = .ok rs.c := by
  unfold ofOpen at h
  cases ho : openFields fs with
  | none => simp [ho] at h
  | some v =>
    obtain ⟨ctx, rate, channels, target, state⟩ := v
    cases hc : Api.rtContext rate with
    | error e => simp [ho, hc, Except.toOption] at h
    | ok c =>
      simp only [ho, hc, Except.toOption, Option.bind_some, Option.pure_def, Option.some.injEq,
        bind, pure] at h
      subst h
      exact hc

/-! ## Messages -/

/-- A state with only this context, under its id, and no `Realtime` record. -/
def apiOf (rs : State) : Api.State :=
  { contexts := ({} : Std.HashMap Nat Context.OfflineContext).insert rs.ctx rs.c, next := rs.ctx + 1 }

/-- An op 176 to 185, applied with `Api.op` as the control side applied it. -/
def applyOp (rs : State) (code : Nat) (fs : Array ByteArray) : State :=
  match Api.op (apiOf rs) code fs with
  | (api, .ok _) =>
    match api.contexts[rs.ctx]? with
    | some c =>
      let plan := if code == 176 || code == 177 || code == 178 then Render.Plan.of c.state.graph else rs.plan
      { rs with c, plan }
    | none => { rs with divergence := rs.divergence + 1 }
  | (_, .error _) => { rs with divergence := rs.divergence + 1 }

/-- The state a control verb asks for. -/
def verbState : String → Option Api.RtState
  | "resume" => some .running
  | "suspend" => some .suspended
  | "close" => some .closed
  | _ => none

/-- A control call, fields `[ctx, verb, callId]` (`Api.controlOp`). The state follows the verb and
the call is confirmed; a change of state is reported (Web Audio API, `resume()`, `suspend()` and
`close()`: the promise is resolved, then the `state` attribute is set when it differs). A call on a
closed context, a verb that is not one of the three, and a `resume` when the output can not play
(`noOutput`: the sink did not open) are refused. -/
def control (noOutput : Bool) (rs : State) (fs : Array ByteArray) : State :=
  let call := ((Api.natArg fs 2).toOption).getD 0
  let p := rs.pending
  match verbState (Api.strArg fs 1) with
  | some to =>
    if rs.state == .closed || (noOutput && to == .running) then
      { rs with pending := { p with rejected := p.rejected.push call } }
    else
      let changes := if rs.state == to then p.stateChanges else p.stateChanges.push to
      { rs with state := to, pending := { p with confirmed := p.confirmed.push call, stateChanges := changes } }
  | none => { rs with pending := { p with rejected := p.rejected.push call } }

/-- Says: a control call on a closed context is refused and changes neither the state nor the
graph. Does not say: anything about a context that is not closed. -/
theorem control_closed (noOutput : Bool) (rs : State) (fs : Array ByteArray) (h : rs.state = .closed) :
    (control noOutput rs fs).state = .closed ∧ (control noOutput rs fs).c = rs.c ∧
    (control noOutput rs fs).pending.rejected = rs.pending.rejected.push (((Api.natArg fs 2).toOption).getD 0) := by
  unfold control
  split <;> simp [h]

/-- One message (plan 13.2): 0 ends a context whose page is gone; 191 is a control call; 176 to
185 are ops; anything else, and any op after the context closed, is ignored. -/
def applyMessage (noOutput : Bool) (rs : State) (m : Nat × Array ByteArray) : State :=
  if m.1 == 0 then { rs with state := .closed }
  else if m.1 == 191 then control noOutput rs m.2
  else if Api.outboxCode m.1 && rs.state != .closed then applyOp rs m.1 m.2
  else rs

/-- The messages of one batch, in order. -/
def applyBatch (rs : State) (msgs : Array (Nat × Array ByteArray)) (noOutput : Bool := false) : State :=
  msgs.foldl (applyMessage noOutput) rs

/-- Says: once a batch has closed the context, it stays closed through the rest of the batch.
Does not say: when a batch closes it. -/
theorem applyMessage_closed (noOutput : Bool) (rs : State) (m : Nat × Array ByteArray)
    (h : rs.state = .closed) : (applyMessage noOutput rs m).state = .closed := by
  unfold applyMessage
  split
  · rfl
  · split
    · exact (control_closed noOutput rs m.2 h).1
    · split
      · rename_i hc; simp [h] at hc
      · exact h

theorem applyBatch_closed (noOutput : Bool) (msgs : List (Nat × Array ByteArray)) :
    ∀ rs : State, rs.state = .closed → (msgs.foldl (applyMessage noOutput) rs).state = .closed := by
  induction msgs with
  | nil => intro rs h; exact h
  | cons m ms ih => intro rs h; exact ih _ (applyMessage_closed noOutput rs m h)

/-! ## Rendering -/

/-- Element `i` of the result is frame `i / channels` of channel `i % channels` of `b` (0 where `b`
has no such frame). -/
def interleave (b : Kernels.Block) (channels n : Nat) : FloatArray :=
  Kernels.mkChan (channels * n) fun i => Kernels.getF (b.getD (i % channels) ⟨#[]⟩) (i / channels)

/-- Says: `interleave b channels n` has `channels * n` values. Does not say: which. -/
theorem interleave_size (b : Kernels.Block) (channels n : Nat) :
    (interleave b channels n).size = channels * n := Kernels.mkChan_size _ _

/-- `a`, then the values of `b`. A tail call on the count. -/
def appendF (a b : FloatArray) : FloatArray :=
  Kernels.iter (fun j (x : FloatArray) => x.push (Kernels.getF b j)) b.size 0 a

theorem appendF_size (a b : FloatArray) : (appendF a b).size = a.size + b.size :=
  Kernels.iter_push_size _ _ _ _

/-- The destination's block as `channels` channels: the speaker rule of section 4 when the counts
differ. -/
def toOutput (b : Kernels.Block) (channels n : Nat) : Kernels.Block :=
  if b.size == channels then b else Mix.apply (Mix.matrix .speakers b.size channels) b n

/-- One render quantum: the state after it, and its frames as the output takes them. -/
def quantum (rs : State) : State × FloatArray :=
  let q := rs.c.state.quantum
  let r := Render.renderQuantumWith rs.c.state rs.plan
  ({ rs with c := { rs.c with state := r.1 } }, interleave (toOutput r.2 rs.channels q) rs.channels q)

theorem quantum_frame (rs : State) :
    (quantum rs).1.c.state.frame = rs.c.state.frame + rs.c.state.quantum := rfl

theorem quantum_quantum (rs : State) : (quantum rs).1.c.state.quantum = rs.c.state.quantum := rfl

theorem quantum_channels (rs : State) : (quantum rs).1.channels = rs.channels := rfl

theorem quantum_size (rs : State) : (quantum rs).2.size = rs.channels * rs.c.state.quantum :=
  interleave_size _ _ _

/-- `k` render quanta in a row, their frames appended to `acc` quantum after quantum. A tail call
on `k`. -/
def fill : Nat → State → FloatArray → State × FloatArray
  | 0, rs, acc => (rs, acc)
  | k + 1, rs, acc =>
    let r := quantum rs
    fill k r.1 (appendF acc r.2)

/-- The frames of `k` quanta from `rs`, one entry a quantum, in order. -/
def quanta : Nat → State → List FloatArray
  | 0, _ => []
  | k + 1, rs => (quantum rs).2 :: quanta k (quantum rs).1

/-- Says: the frames of `fill k` are the frames of the `k` quanta from `rs`, appended in the order
they were rendered, after `acc`. So the frames written to the sink are the rendered quanta in
order. Does not say: what a quantum's values are (`Render`). -/
theorem fill_frames (k : Nat) : ∀ (rs : State) (acc : FloatArray),
    (fill k rs acc).2 = (quanta k rs).foldl appendF acc := by
  induction k with
  | zero => intro rs acc; rfl
  | succ k ih => intro rs acc; simp only [fill, quanta, List.foldl_cons]; exact ih _ _

/-- Says: after `fill k` the rendering side's current frame has advanced by `k` render quanta, and
the quantum size and channel count are unchanged. Does not say: how long it took. -/
theorem fill_frame (k : Nat) : ∀ (rs : State) (acc : FloatArray),
    (fill k rs acc).1.c.state.frame = rs.c.state.frame + k * rs.c.state.quantum ∧
    (fill k rs acc).1.c.state.quantum = rs.c.state.quantum ∧
    (fill k rs acc).1.channels = rs.channels := by
  induction k with
  | zero => intro rs acc; simp [fill]
  | succ k ih =>
    intro rs acc
    obtain ⟨h1, h2, h3⟩ := ih (quantum rs).1 (appendF acc (quantum rs).2)
    simp only [fill]
    refine ⟨?_, ?_, ?_⟩
    · rw [h1, quantum_frame, quantum_quantum, Nat.succ_mul]; omega
    · rw [h2, quantum_quantum]
    · rw [h3, quantum_channels]

/-- Says: `fill k` appends `k * channels * quantum` values to `acc`. Does not say: which. -/
theorem fill_size (k : Nat) : ∀ (rs : State) (acc : FloatArray),
    (fill k rs acc).2.size = acc.size + k * (rs.channels * rs.c.state.quantum) := by
  induction k with
  | zero => intro rs acc; simp [fill]
  | succ k ih =>
    intro rs acc
    simp only [fill]
    rw [ih, appendF_size, quantum_size, quantum_channels, quantum_quantum, Nat.succ_mul]
    omega

/-- The quanta that bring `ahead` frames to at least `target`: `ceil ((target - ahead) / q)`. -/
def quantaFor (target ahead q : Nat) : Nat :=
  if q == 0 then 0 else (target - ahead + q - 1) / q

/-- Says: rendering `quantaFor target ahead q` quanta of `q` frames brings the frames ahead to at
least `target`, and to less than `target + q` when they were below it. Does not say: that the
output takes them. -/
theorem quantaFor_bounds (target ahead q : Nat) (hq : 0 < q) :
    target ≤ ahead + quantaFor target ahead q * q ∧
    (ahead < target → ahead + quantaFor target ahead q * q < target + q) := by
  unfold quantaFor
  have hq' : (q == 0) = false := by simp; omega
  simp only [hq', Bool.false_eq_true, if_false]
  constructor
  · have := Nat.div_add_mod (target - ahead + q - 1) q
    have := Nat.mod_lt (target - ahead + q - 1) hq
    rw [Nat.mul_comm]
    omega
  · intro h
    have := Nat.div_mul_le_self (target - ahead + q - 1) q
    omega

/-! ## Events and reports -/

/-- The scheduled sources that ended since the last call, added to the next report once each, in
node order. -/
def noteEnded (rs : State) : State :=
  let fresh := (Api.endedIds rs.c).filter fun i => !rs.endedSent.contains i
  if fresh.isEmpty then rs
  else { rs with endedSent := rs.endedSent ++ fresh.toArray,
                 pending := { rs.pending with ended := rs.pending.ended ++ fresh.toArray } }

/-- The report of the events since the last one, with the counters given (frames rendered: the
rendering side's current frame); the events are then cleared. -/
def takeReport (rs : State) (played underruns latency : Nat) : State × Api.Report :=
  ({ rs with pending := {} },
   { rs.pending with framesRendered := rs.c.state.frame, framesPlayed := played,
                     underruns, latencyFrames := latency })

/-- Two reports the engine has not taken, as one: the counters are the larger (the newer's latency
and time), the events of `a` then those of `b`. -/
def mergeReport (a b : Api.Report) : Api.Report :=
  { framesRendered := max a.framesRendered b.framesRendered
    framesPlayed := max a.framesPlayed b.framesPlayed
    underruns := max a.underruns b.underruns
    latencyFrames := b.latencyFrames
    timeMs := b.timeMs
    ended := a.ended ++ b.ended
    stateChanges := a.stateChanges ++ b.stateChanges
    confirmed := a.confirmed ++ b.confirmed
    rejected := a.rejected ++ b.rejected }

/-- Says: a merged report keeps every event of both, in order, and frames rendered and played do not
decrease. Does not say: that the merge is applied as two reports would be (the page reads one
batch of events either way). -/
theorem mergeReport_events (a b : Api.Report) :
    (mergeReport a b).ended = a.ended ++ b.ended ∧
    (mergeReport a b).stateChanges = a.stateChanges ++ b.stateChanges ∧
    (mergeReport a b).confirmed = a.confirmed ++ b.confirmed ∧
    (mergeReport a b).rejected = a.rejected ++ b.rejected ∧
    a.framesRendered ≤ (mergeReport a b).framesRendered ∧ b.framesRendered ≤ (mergeReport a b).framesRendered ∧
    a.framesPlayed ≤ (mergeReport a b).framesPlayed ∧ b.framesPlayed ≤ (mergeReport a b).framesPlayed :=
  ⟨rfl, rfl, rfl, rfl, Nat.le_max_left _ _, Nat.le_max_right _ _, Nat.le_max_left _ _, Nat.le_max_right _ _⟩

/-! ## Tests -/

namespace Tests

private def d (x : Float) : ByteArray := Api.f64le x
private def n (k : Nat) : ByteArray := Api.ofStr (toString k)
private def t (x : String) : ByteArray := Api.ofStr x

private def open1 : Array ByteArray := #[n 1, d 48000.0, n 2, n 1024, n 1]
/-- `f` of the rendering side opened by `open1` after the messages `ms`. -/
private def with1 {α : Type} (ms : Array (Nat × Array ByteArray)) (f : State → α) (noOutput := false) : Option α :=
  (ofOpen open1).map fun rs => f (applyBatch rs ms noOutput)

#guard (ofOpen open1).map (fun rs => (rs.ctx, rs.rate, rs.channels, rs.target, rs.state == .running, rs.c.length)) ==
  some (1, 48000.0, 2, 1024, true, 0)
#guard (ofOpen #[n 1, d 48000.0, n 2, n 1024]).isNone
#guard (ofOpen #[n 1, d 48000.0, n 0, n 1024, n 1]).isNone
#guard (ofOpen #[n 1, d 100.0, n 2, n 1024, n 1]).isNone
#guard (ofOpen #[n 1, d 48000.0, n 2, n 1024, n 7]).isNone

-- An oscillator into the destination, started at 0 and stopped at 128 frames (2.666 ms).
private def oscMsgs : Array (Nat × Array ByteArray) :=
  #[(176, #[n 1, t "oscillator"]), (177, #[n 1, n 1, n 0, n 0, n 0, n 0]),
    (181, #[n 1, n 1, d 0.0]), (182, #[n 1, n 1, d (128.0 / 48000.0)])]
#guard with1 oscMsgs (fun rs => rs.divergence == 0 && rs.c.state.nodes.size == 2 && rs.plan.steps.length == 2) == some true
-- A failed op is counted: a node that does not exist.
#guard with1 #[(181, #[n 1, n 9, d 0.0])] (·.divergence) == some 1
-- The frames of two quanta: 2 * 128 frames of 2 channels; the current frame advances.
#guard with1 oscMsgs (fun rs => ((fill 2 rs ⟨#[]⟩).2.size, (fill 2 rs ⟨#[]⟩).1.c.state.frame)) == some (512, 256)
-- Frame 1 of both channels is sin(2 pi 440 / 48000); the two channels are equal (a mono source
-- up-mixed); after the stop, silence.
#guard with1 oscMsgs (fun rs => let f := (fill 2 rs ⟨#[]⟩).2
  (decide ((f.get! 2 - Float.sin (2.0 * 3.141592653589793 * 440.0 / 48000.0)).abs < 1e-6),
   f.get! 2 == f.get! 3, (List.range 256).all fun i => f.get! (256 + i) == 0.0)) == some (true, true, true)
-- The same values as an offline context rendering the same graph (binary64 here; the sink and
-- the offline render both round to binary32).
private def offline : Option (Array FloatArray) := do
  let c ← (Context.OfflineContext.new 2 256 48000.0).toOption
  let (c, _) ← c.createOscillator.toOption
  let c ← (c.connect 1 0 0 0).toOption
  let c ← (c.start 1 0.0).toOption
  let c ← (c.stop 1 (128.0 / 48000.0)).toOption
  let (_, chans) ← c.startRendering.toOption
  pure chans
#guard (offline.bind fun chans => with1 oscMsgs fun rs => let f := (fill 2 rs ⟨#[]⟩).2
  (List.range 256).all fun i =>
    (f.get! (2 * i)).toFloat32.toFloat == chans[0]!.get! i && (f.get! (2 * i + 1)).toFloat32.toFloat == chans[1]!.get! i) ==
  some true
-- The source ended once: reported in the next report, not in the one after.
#guard with1 oscMsgs (fun rs => (noteEnded (fill 2 rs ⟨#[]⟩).1).pending.ended.toList) == some [1]
#guard with1 oscMsgs (fun rs =>
  (noteEnded (takeReport (noteEnded (fill 2 rs ⟨#[]⟩).1) 0 0 0).1).pending.ended.toList) == some []
#guard with1 oscMsgs (fun rs => (takeReport (noteEnded (fill 2 rs ⟨#[]⟩).1) 100 0 0).2.framesRendered) == some 256

-- Control calls: resume on a running context is confirmed with no state change; suspend changes
-- the state; close confirms and closes; a call after the close is refused, and an op after it
-- changes nothing. The first report starts with the state `running` of the context's start.
#guard with1 #[(191, #[n 1, t "resume", n 4]), (191, #[n 1, t "suspend", n 5]),
               (191, #[n 1, t "close", n 6]), (191, #[n 1, t "resume", n 7]), (176, #[n 1, t "gain"])]
  (fun rs => (rs.state == .closed, rs.pending.confirmed.toList, rs.pending.rejected.toList, rs.c.state.nodes.size,
              rs.pending.stateChanges.toList.map Api.RtState.code)) ==
  some (true, [4, 5, 6], [7], 1, [1, 0, 2])
#guard with1 #[(191, #[n 1, t "play", n 3])] (·.pending.rejected.toList) == some [3]
-- With no output, a resume is refused and a suspend is confirmed.
#guard with1 #[(191, #[n 1, t "resume", n 3]), (191, #[n 1, t "suspend", n 4])]
  (fun rs => (rs.pending.rejected.toList, rs.pending.confirmed.toList)) (noOutput := true) == some ([3], [4])
-- The page is gone: closed, with no event after the start's `running`.
#guard with1 #[(0, #[])] (fun rs => (rs.state == .closed, rs.pending.stateChanges.toList.map Api.RtState.code)) == some (true, [1])

-- A device of 6 channels: the stereo destination up-mixed by the speaker rule (L and R to the first
-- two; the others silent).
#guard ((ofOpen #[n 1, d 48000.0, n 6, n 1024, n 1]).map fun rs =>
  let rs := applyBatch rs #[(176, #[n 1, t "constantSource"]), (177, #[n 1, n 1, n 0, n 0, n 0, n 0]), (181, #[n 1, n 1, d 0.0])]
  let f := (fill 1 rs ⟨#[]⟩).2
  (f.size, (List.range 6).map fun ch => f.get! (6 * 5 + ch))) == some (768, [1.0, 1.0, 0.0, 0.0, 0.0, 0.0])

-- The quanta needed for the target.
#guard quantaFor 1024 0 128 == 8 && quantaFor 1024 1000 128 == 1 && quantaFor 1024 1024 128 == 0 &&
  quantaFor 1024 2000 128 == 0 && quantaFor 1000 0 128 == 8

-- Merging reports.
#guard (mergeReport { framesRendered := 10, ended := #[1] } { framesRendered := 5, ended := #[2], confirmed := #[3] }).framesRendered == 10
#guard (mergeReport { framesRendered := 10, ended := #[1] } { framesRendered := 5, ended := #[2], confirmed := #[3] }).ended.toList == [1, 2]

end Tests

end L4Factoidal.WebAudio.RenderSide
