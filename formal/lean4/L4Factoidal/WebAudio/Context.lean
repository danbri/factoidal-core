/-
# Web Audio API: the offline context

Follows https://webaudio.github.io/web-audio-api/ : the `OfflineAudioContext` interface
(constructor `OfflineAudioContext(numberOfChannels, length, sampleRate)` and its checks,
`startRendering`), section 2.4 "Supported Sample Rates", section 2.5 "Supported Render Quantum
Sizes", the factory methods of `BaseAudioContext` (`createGain`, `createConstantSource`,
`createDelay`, `createStereoPanner`, `createChannelSplitter`, `createChannelMerger`), `connect`,
`AudioScheduledSourceNode.start` and `stop`, and the `AudioParam` methods.

Stage B of https://github.com/danbri/factoidal-core/issues/1169 (audio in Foafnaut); plan:
`docs/designissues/2026-11-26-foafnaut-audio-plan.md`, sections 4 and 9. The rendering of each
quantum is `Render.lean`.

## Model

`OfflineContext` holds the `Render.State` (graph, node states, current frame, render quantum
size), the constructor arguments `numberOfChannels` and `length`, and whether `startRendering`
has run. Every operation is a pure function that returns the new context, or the error of the
specification (`Error`: `NotSupportedError`, `IndexSizeError`, `InvalidAccessError`,
`InvalidStateError`, `RangeError`, `TypeError`; `unknownNode` is added for a node id that is not
in the graph, which cannot happen through the API where the argument is an object). Node ids:
the destination is node 0 and each created node gets the next number. Parameter numbers are
those of `Graph.Kind.numParams`: Gain `gain` 0; ConstantSource `offset` 0; Delay `delayTime` 0;
StereoPanner `pan` 0.

`startRendering` renders `ceil (length / n)` quanta, then returns `numberOfChannels` channels of
exactly `length` frames. Each value is rounded to binary32 (`Float.toFloat32`), because the
specification exposes the data as `Float32Array`; the channel is a `FloatArray` that holds the
binary32 values as binary64 numbers.

## Proved

`new_valid` (what the constructor accepts), `startRendering_shape` (channels and frames of the
result), `renderLoop_frame`, `renderLoop_blocks`, `renderLoop_graph` (the loop advances the
frame by `k * n`, makes `k` blocks and does not change the graph), `startRendering_graph` (the
graph of the context is not changed by rendering), `startRendering_twice` (a second call is
refused). Values are `#guard` tests.

## Not done

* `startRendering(chunkSize)`, `suspend` and `resume`: one call renders all `length` frames.
* The page layer converts doubles to binary32 for `AudioParam` values and times (the IDL type is
  `float`); here the values are binary64 as given.
* `disconnect`, `createBuffer`-based nodes, Oscillator, BiquadFilter, AudioBufferSource (other
  files; a node of these types exists in the graph and outputs silence until `Render.runKernel`
  has its kernel), `setValueCurveAtTime`, `cancelAndHoldAtTime` (in `Automation`, not exposed
  here), `AudioListener`, and `OfflineAudioContextOptions.renderSizeHint` as a string (the
  quantum size is a number argument).
-/
import L4Factoidal.WebAudio.Mix
import L4Factoidal.WebAudio.Automation
import L4Factoidal.WebAudio.Kernels
import L4Factoidal.WebAudio.Graph
import L4Factoidal.WebAudio.Render

namespace L4Factoidal.WebAudio.Context

open L4Factoidal.WebAudio
open L4Factoidal.WebAudio.Kernels (Block mkChan getF)

/-- The `DOMException` and error types of the specification. -/
inductive Error where
  | notSupported (msg : String)
  | indexSize
  | invalidAccess
  | invalidState (msg : String)
  | range (msg : String)
  | type (msg : String)
  | unknownNode
  deriving DecidableEq, Repr

/-- The error of `Graph.connect` and its relatives. -/
def Error.ofGraph : Graph.Error → Error
  | .indexSize => .indexSize
  | .invalidAccess => .invalidAccess
  | .unknownNode => .unknownNode

/-- The error of an `AudioParam` automation method. -/
def Error.ofAutomation : Automation.Error → Error
  | .notSupported m => .notSupported m
  | .range m => .range m
  | .invalidState m => .invalidState m
  | .type m => .type m

/-- An `OfflineAudioContext`. -/
structure OfflineContext where
  state : Render.State
  numberOfChannels : Nat
  length : Nat
  /-- `startRendering` has run: the committed frames are at least `length`. -/
  rendered : Bool := false

/-- The node id of `destination`. -/
def OfflineContext.destination (_ : OfflineContext) : Nat := 0

/-- `sampleRate`. -/
def OfflineContext.sampleRate (c : OfflineContext) : Float := c.state.sampleRate

/-- `currentTime` as an exact frame count over the rate: the current frame. -/
def OfflineContext.currentFrame (c : OfflineContext) : Nat := c.state.frame

/-- `new OfflineAudioContext(numberOfChannels, length, sampleRate)`. `NotSupportedError` for a
channel count of 0 or above 32, a length of 0, a sample rate outside 3000 to 768000 Hz (section
2.4; NaN is outside), or a render quantum size outside 1 to `floor (6 * sampleRate)` (section
2.5). The destination has `numberOfChannels` channels, mode `explicit`, interpretation
`speakers`. -/
def OfflineContext.new (numberOfChannels length : Nat) (sampleRate : Float)
    (quantum : Nat := 128) : Except Error OfflineContext :=
  if numberOfChannels = 0 ∨ 32 < numberOfChannels then
    .error (.notSupported "numberOfChannels is 0 or above 32")
  else if length = 0 then .error (.notSupported "length is 0")
  else if !(sampleRate ≥ 3000.0 && sampleRate ≤ 768000.0) then
    .error (.notSupported "sampleRate is outside 3000 to 768000")
  else if quantum = 0 ∨ (6.0 * sampleRate).floor.toUInt64.toNat < quantum then
    .error (.notSupported "render quantum size is outside 1 to 6 * sampleRate")
  else
    .ok { state := Render.State.init sampleRate numberOfChannels quantum
          numberOfChannels, length }

/-! ## Creating nodes -/

/-- Add a node; no check can fail. -/
def OfflineContext.addNode (c : OfflineContext) (k : Graph.Kind) (maxDelayTime : Float := 1.0) :
    OfflineContext × Nat :=
  let r := c.state.addNode k maxDelayTime
  ({ c with state := r.1 }, r.2)

/-- `createGain()`. -/
def OfflineContext.createGain (c : OfflineContext) : Except Error (OfflineContext × Nat) :=
  .ok (c.addNode .gain)

/-- `createConstantSource()`. -/
def OfflineContext.createConstantSource (c : OfflineContext) :
    Except Error (OfflineContext × Nat) :=
  .ok (c.addNode .constantSource)

/-- `createStereoPanner()`. -/
def OfflineContext.createStereoPanner (c : OfflineContext) :
    Except Error (OfflineContext × Nat) :=
  .ok (c.addNode .stereoPanner)

/-- `createDelay(maxDelayTime)`: `NotSupportedError` unless `0 < maxDelayTime < 180`
("greater than zero and less than three minutes"). -/
def OfflineContext.createDelay (c : OfflineContext) (maxDelayTime : Float := 1.0) :
    Except Error (OfflineContext × Nat) :=
  if maxDelayTime > 0.0 && maxDelayTime < 180.0 then .ok (c.addNode .delay maxDelayTime)
  else .error (.notSupported "maxDelayTime must be greater than 0 and less than 180")

/-- `createChannelSplitter(numberOfOutputs)`: `IndexSizeError` unless 1 to 32. -/
def OfflineContext.createChannelSplitter (c : OfflineContext) (numberOfOutputs : Nat := 6) :
    Except Error (OfflineContext × Nat) :=
  if 1 ≤ numberOfOutputs ∧ numberOfOutputs ≤ 32 then .ok (c.addNode (.splitter numberOfOutputs))
  else .error .indexSize

/-- `createChannelMerger(numberOfInputs)`: `IndexSizeError` unless 1 to 32. -/
def OfflineContext.createChannelMerger (c : OfflineContext) (numberOfInputs : Nat := 6) :
    Except Error (OfflineContext × Nat) :=
  if 1 ≤ numberOfInputs ∧ numberOfInputs ≤ 32 then .ok (c.addNode (.merger numberOfInputs))
  else .error .indexSize

/-! ## Connections -/

/-- `connect(destinationNode, output, input)`. -/
def OfflineContext.connect (c : OfflineContext) (src out dst inp : Nat) :
    Except Error OfflineContext :=
  match Graph.connect c.state.graph src out dst inp with
  | .ok g => .ok { c with state := { c.state with graph := g } }
  | .error e => .error (Error.ofGraph e)

/-- `connect(destinationParam, output)`; `param` is the number of the `AudioParam` of `dst`. -/
def OfflineContext.connectParam (c : OfflineContext) (src out dst param : Nat) :
    Except Error OfflineContext :=
  match Graph.connectParam c.state.graph src out dst param with
  | .ok g => .ok { c with state := { c.state with graph := g } }
  | .error e => .error (Error.ofGraph e)

/-! ## Scheduled sources -/

private def OfflineContext.setKs (c : OfflineContext) (id : Nat) (nd : Render.Node) :
    OfflineContext :=
  { c with state := { c.state with nodes := c.state.nodes.set! id nd } }

/-- `start(when)` of a scheduled source. `RangeError` for a negative time, `TypeError` for a
non-finite one, `InvalidStateError` when `start` was called before. -/
def OfflineContext.start (c : OfflineContext) (id : Nat) (when_ : Float := 0.0) :
    Except Error OfflineContext :=
  if !when_.isFinite then .error (.type "when is not finite")
  else if when_ < 0.0 then .error (.range "when is negative")
  else
    match c.state.nodes[id]? with
    | none => .error .unknownNode
    | some nd =>
      match nd.ks with
      | .const s =>
        if s.startFrame.isSome then .error (.invalidState "start was called before")
        else
          .ok (c.setKs id
            { nd with ks := .const { s with startFrame := some (Kernels.frameOfTime when_ c.sampleRate) } })
      -- PLACE FOR Oscillator and AudioBufferSource: their `start` (other files).
      | .pending => .ok c
      | _ => .error (.invalidState "the node is not a scheduled source")

/-- `stop(when)` of a scheduled source. `InvalidStateError` when `start` was not called,
`RangeError` for a negative time, `TypeError` for a non-finite one. -/
def OfflineContext.stop (c : OfflineContext) (id : Nat) (when_ : Float := 0.0) :
    Except Error OfflineContext :=
  if !when_.isFinite then .error (.type "when is not finite")
  else if when_ < 0.0 then .error (.range "when is negative")
  else
    match c.state.nodes[id]? with
    | none => .error .unknownNode
    | some nd =>
      match nd.ks with
      | .const s =>
        if s.startFrame.isNone then .error (.invalidState "start was not called")
        else
          .ok (c.setKs id
            { nd with ks := .const { s with stopFrame := some (Kernels.frameOfTime when_ c.sampleRate) } })
      | .pending => .ok c
      | _ => .error (.invalidState "the node is not a scheduled source")

/-! ## AudioParam automation -/

/-- Apply `f` to the timeline of parameter `param` of node `id`, with the current time and the
parameter's current intrinsic value. -/
private def OfflineContext.withParam (c : OfflineContext) (id param : Nat)
    (f : Render.ParamState → Rat → Float → Except Automation.Error Automation.Timeline) :
    Except Error OfflineContext :=
  match c.state.nodes[id]? with
  | none => .error .unknownNode
  | some nd =>
    match nd.params[param]? with
    | none => .error .indexSize
    | some p =>
      let now := Automation.frameTime c.state.frame c.sampleRate
      let cur := Automation.valueAt p.timeline p.spec.defaultValue now
      match f p now cur with
      | .error e => .error (Error.ofAutomation e)
      | .ok tl =>
        .ok (c.setKs id { nd with params := nd.params.set! param { p with timeline := tl } })

/-- Insert one event: `time` is a double, converted exactly. -/
private def OfflineContext.addEvent (c : OfflineContext) (id param : Nat) (k : Automation.Kind)
    (value time : Float) : Except Error OfflineContext :=
  c.withParam id param fun p now cur => do
    let t ← Automation.eventTime time
    Automation.insert p.timeline ⟨k, t, value⟩ now cur

/-- `setValueAtTime(value, startTime)`. -/
def OfflineContext.setValueAtTime (c : OfflineContext) (id param : Nat) (value time : Float) :
    Except Error OfflineContext := c.addEvent id param .setValue value time

/-- `linearRampToValueAtTime(value, endTime)`. -/
def OfflineContext.linearRampToValueAtTime (c : OfflineContext) (id param : Nat)
    (value time : Float) : Except Error OfflineContext :=
  c.addEvent id param .linearRamp value time

/-- `exponentialRampToValueAtTime(value, endTime)`. -/
def OfflineContext.exponentialRampToValueAtTime (c : OfflineContext) (id param : Nat)
    (value time : Float) : Except Error OfflineContext :=
  c.addEvent id param .exponentialRamp value time

/-- `setTargetAtTime(target, startTime, timeConstant)`. -/
def OfflineContext.setTargetAtTime (c : OfflineContext) (id param : Nat)
    (target startTime timeConstant : Float) : Except Error OfflineContext :=
  c.addEvent id param (.setTarget timeConstant) target startTime

/-- The `value` setter: `setValueAtTime(value, currentTime)`. -/
def OfflineContext.setParamValue (c : OfflineContext) (id param : Nat) (value : Float) :
    Except Error OfflineContext :=
  c.addEvent id param .setValue value
    (Automation.timeToFloat (Automation.frameTime c.state.frame c.sampleRate))

/-- `cancelScheduledValues(cancelTime)`. -/
def OfflineContext.cancelScheduledValues (c : OfflineContext) (id param : Nat)
    (cancelTime : Float) : Except Error OfflineContext :=
  c.withParam id param fun p now _ => do
    let t ← Automation.cancelTimeOfDouble cancelTime now
    pure (Automation.cancelScheduledValues p.timeline t)

/-- The `automationRate` attribute: `true` is "a-rate", `false` is "k-rate". -/
def OfflineContext.setAutomationRate (c : OfflineContext) (id param : Nat) (aRate : Bool) :
    Except Error OfflineContext :=
  match c.state.nodes[id]? with
  | none => .error .unknownNode
  | some nd =>
    match nd.params[param]? with
    | none => .error .indexSize
    | some p =>
      let p' : Render.ParamState := { p with spec := { p.spec with aRate := aRate } }
      .ok (c.setKs id { nd with params := nd.params.set! param p' })

/-! ## Rendering -/

/-- `k` render quanta in a row; the blocks are appended to `acc`. A tail call on the count. -/
def renderLoop : Nat → Render.State → Render.Plan → Array Block → Render.State × Array Block
  | 0, st, _, acc => (st, acc)
  | k + 1, st, pl, acc =>
    let r := Render.renderQuantumWith st pl
    renderLoop k r.1 pl (acc.push r.2)

/-- The output channels: `channels` channels of `length` frames; frame `i` is frame `i % q` of
block `i / q`, rounded to binary32. -/
def assemble (channels length q : Nat) (chunks : Array Block) : Array FloatArray :=
  Array.ofFn (n := channels) fun ch =>
    mkChan length fun i =>
      (getF ((chunks.getD (i / q) #[]).getD ch.1 ⟨#[]⟩) (i % q)).toFloat32.toFloat

/-- `startRendering()`: renders `ceil (length / n)` quanta and returns the context after the
render and `numberOfChannels` channels of `length` frames (binary32 values). `InvalidStateError`
when the context was already rendered. -/
def OfflineContext.startRendering (c : OfflineContext) :
    Except Error (OfflineContext × Array FloatArray) :=
  if c.rendered then .error (.invalidState "rendering already started")
  else
    let q := c.state.quantum
    let r := renderLoop ((c.length + q - 1) / q) c.state (Render.Plan.of c.state.graph) #[]
    .ok ({ c with state := r.1, rendered := true },
         assemble c.numberOfChannels c.length q r.2)

/-! ## Theorems -/

/-- Says: a context that the constructor returns has 1 to 32 channels, a positive length, a
sample rate from 3000 to 768000 Hz and a positive quantum size, and its destination has the
requested channel count. Does not say: that every such argument list is accepted (the quantum
size has an upper limit too). -/
theorem new_valid (nch len : Nat) (sr : Float) (q : Nat) (c : OfflineContext)
    (h : OfflineContext.new nch len sr q = .ok c) :
    1 ≤ c.numberOfChannels ∧ c.numberOfChannels ≤ 32 ∧ 0 < c.length ∧ 0 < c.state.quantum ∧
    c.numberOfChannels = nch ∧ c.length = len ∧ Render.destChannels c.state = nch := by
  unfold OfflineContext.new at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  · cases h
    rename_i h1 h2 h3 h4
    dsimp only
    refine ⟨by omega, by omega, by omega, ?_, rfl, rfl, ?_⟩
    · show 0 < q
      omega
    simp [Render.destChannels, Render.State.init, Render.Node.new, Render.chanDefaults]

/-- Says: `renderLoop k` advances the current frame by `k * n` and leaves the quantum size. -/
theorem renderLoop_frame (k : Nat) (st : Render.State) (pl : Render.Plan) (acc : Array Block) :
    (renderLoop k st pl acc).1.frame = st.frame + k * st.quantum ∧
    (renderLoop k st pl acc).1.quantum = st.quantum := by
  induction k generalizing st acc with
  | zero => simp [renderLoop]
  | succ k ih =>
    have h := ih (Render.renderQuantumWith st pl).1 (acc.push (Render.renderQuantumWith st pl).2)
    have hf : (Render.renderQuantumWith st pl).1.frame = st.frame + st.quantum := rfl
    have hq : (Render.renderQuantumWith st pl).1.quantum = st.quantum := rfl
    show (renderLoop k (Render.renderQuantumWith st pl).1 pl
      (acc.push (Render.renderQuantumWith st pl).2)).1.frame = _ ∧
      (renderLoop k (Render.renderQuantumWith st pl).1 pl
      (acc.push (Render.renderQuantumWith st pl).2)).1.quantum = _
    rw [h.1, h.2, hf, hq, Nat.succ_mul]
    exact ⟨by omega, rfl⟩

/-- Says: `renderLoop k` appends exactly `k` blocks. -/
theorem renderLoop_blocks (k : Nat) (st : Render.State) (pl : Render.Plan) (acc : Array Block) :
    (renderLoop k st pl acc).2.size = acc.size + k := by
  induction k generalizing st acc with
  | zero => simp [renderLoop]
  | succ k ih => simp only [renderLoop]; rw [ih]; simp; omega

/-- Says: `renderLoop` does not change the graph. Does not say: that the plan fits the graph
(the caller computes the plan from it). -/
theorem renderLoop_graph (k : Nat) (st : Render.State) (pl : Render.Plan) (acc : Array Block) :
    (renderLoop k st pl acc).1.graph = st.graph := by
  induction k generalizing st acc with
  | zero => rfl
  | succ k ih => simp only [renderLoop, Render.renderQuantumWith]; rw [ih]

/-- Says: `assemble` has exactly `channels` channels of `length` frames. Does not say: the
values. -/
theorem assemble_shape (channels length q : Nat) (chunks : Array Block) :
    (assemble channels length q chunks).size = channels ∧
    ∀ c ∈ assemble channels length q chunks, c.size = length := by
  unfold assemble
  constructor
  · simp
  · intro c hc
    simp only [Array.mem_ofFn] at hc
    obtain ⟨j, rfl⟩ := hc
    exact Kernels.mkChan_size _ _

/-- Says: `startRendering` returns exactly `numberOfChannels` channels of exactly `length`
frames each. Does not say: which values they hold. -/
theorem startRendering_shape (c c' : OfflineContext) (out : Array FloatArray)
    (h : c.startRendering = .ok (c', out)) :
    out.size = c.numberOfChannels ∧ ∀ ch ∈ out, ch.size = c.length := by
  unfold OfflineContext.startRendering at h
  split at h
  · cases h
  · cases h
    exact assemble_shape _ _ _ _

/-- Says: rendering does not change the graph. Does not say: that the node states are
unchanged. -/
theorem startRendering_graph (c c' : OfflineContext) (out : Array FloatArray)
    (h : c.startRendering = .ok (c', out)) : c'.state.graph = c.state.graph := by
  unfold OfflineContext.startRendering at h
  split at h
  · cases h
  · cases h
    exact renderLoop_graph _ _ _ _

/-- Says: after a successful `startRendering` a second call returns `InvalidStateError`. -/
theorem startRendering_twice (c c' : OfflineContext) (out : Array FloatArray)
    (h : c.startRendering = .ok (c', out)) :
    c'.startRendering = .error (.invalidState "rendering already started") := by
  unfold OfflineContext.startRendering at h
  split at h
  · cases h
  · cases h
    simp [OfflineContext.startRendering]

/-! ## Tests -/

section Tests

private def approxL (xs ys : List Float) : Bool :=
  xs.length == ys.length && (List.zip xs ys).all fun (x, y) => (x - y).abs < 1e-6

/-- Render a graph built by `build`; sample rate 4096 (every frame time is an exact double),
render quantum 4, unless given. -/
private def go (nch len : Nat) (build : OfflineContext → Except Error OfflineContext)
    (q : Nat := 4) (sr : Float := 4096.0) : Except Error (Array FloatArray) := do
  let c ← OfflineContext.new nch len sr q
  let c ← build c
  let (_, out) ← c.startRendering
  pure out

private def chk (r : Except Error (Array FloatArray)) (exp : List (List Float)) : Bool :=
  match r with
  | .ok out => out.size == exp.length &&
      (List.zip out.toList exp).all fun (a, b) => approxL a.data.toList b
  | .error _ => false

private def isErr (r : Except Error α) (e : Error) : Bool :=
  match r with
  | .error e' => e' == e
  | .ok _ => false

/-- The time of frame `k` at 4096 Hz. -/
private def fr (k : Nat) : Float := k.toFloat / 4096.0

private def ones (k : Nat) : List Float := List.replicate k 1.0
private def zeros (k : Nat) : List Float := List.replicate k 0.0

-- Constructor errors (WPT the-offlineaudiocontext-interface/ctor-offlineaudiocontext.html,
-- "options-2": 33 channels, length 0 and a sample rate of 1 give NotSupportedError).
#guard (match OfflineContext.new 33 42 8000.0 with | .error (.notSupported _) => true | _ => false)
#guard (match OfflineContext.new 0 42 8000.0 with | .error (.notSupported _) => true | _ => false)
#guard (match OfflineContext.new 1 0 8000.0 with | .error (.notSupported _) => true | _ => false)
#guard (match OfflineContext.new 1 1 1.0 with | .error (.notSupported _) => true | _ => false)
#guard (match OfflineContext.new 1 1 2999.0 with | .error (.notSupported _) => true | _ => false)
#guard (match OfflineContext.new 1 1 768001.0 with | .error (.notSupported _) => true | _ => false)
#guard (match OfflineContext.new 1 1 (0.0 / 0.0) with | .error (.notSupported _) => true | _ => false)
-- "options-3" and the 3-argument case: valid contexts; destination channel count; the bounds.
#guard (match OfflineContext.new 3 42 12345.0 with
  | .ok c => c.length == 42 && c.numberOfChannels == 3 && Render.destChannels c.state == 3
  | _ => false)
#guard (OfflineContext.new 32 1 3000.0).toOption.isSome
#guard (OfflineContext.new 1 1 768000.0).toOption.isSome
#guard (match OfflineContext.new 1 1 8000.0 0 with | .error (.notSupported _) => true | _ => false)
#guard (match OfflineContext.new 1 1 3000.0 18001 with | .error (.notSupported _) => true | _ => false)

-- A ConstantSource to the destination (default offset 1), length 10, quanta of 4 (not a
-- multiple).
#guard chk (go 1 10 fun c => do
    let (c, s) ← c.createConstantSource
    let c ← c.connect s 0 0 0
    c.start s) [ones 10]
-- Not started: silence (WPT constant-source-basic.html: the output is zero before start).
#guard chk (go 1 10 fun c => do
    let (c, s) ← c.createConstantSource
    c.connect s 0 0 0) [zeros 10]
-- Start inside a quantum (frame 2) and inside a later one (frame 5).
#guard chk (go 1 10 fun c => do
    let (c, s) ← c.createConstantSource
    let c ← c.connect s 0 0 0
    c.start s (fr 2)) [zeros 2 ++ ones 8]
#guard chk (go 1 10 fun c => do
    let (c, s) ← c.createConstantSource
    let c ← c.connect s 0 0 0
    c.start s (fr 5)) [zeros 5 ++ ones 5]
-- Start at 0 and stop at frame 6 (inside the second quantum).
#guard chk (go 1 10 fun c => do
    let (c, s) ← c.createConstantSource
    let c ← c.connect s 0 0 0
    let c ← c.start s
    c.stop s (fr 6)) [ones 6 ++ zeros 4]
-- Start at frame 5, stop at frame 7.
#guard chk (go 1 10 fun c => do
    let (c, s) ← c.createConstantSource
    let c ← c.connect s 0 0 0
    let c ← c.start s (fr 5)
    c.stop s (fr 7)) [zeros 5 ++ ones 2 ++ zeros 3]
-- ConstantSource offset automation straight to the output (a-rate): setValueAtTime then a
-- linear ramp, 0 at frame 0 to 1 at frame 8 (WPT constant-source-output.html checks the offset
-- automation against the expected curve).
#guard chk (go 1 10 fun c => do
    let (c, s) ← c.createConstantSource
    let c ← c.connect s 0 0 0
    let c ← c.setValueAtTime s 0 0.0 0.0
    let c ← c.linearRampToValueAtTime s 0 1.0 (fr 8)
    c.start s) [[0, 0.125, 0.25, 0.375, 0.5, 0.625, 0.75, 0.875, 1, 1]]
-- Exponential ramp: 1 at frame 0 to 4 at frame 4: value at frame i is 4^(i/4).
#guard chk (go 1 5 fun c => do
    let (c, s) ← c.createConstantSource
    let c ← c.connect s 0 0 0
    let c ← c.setValueAtTime s 0 1.0 0.0
    let c ← c.exponentialRampToValueAtTime s 0 4.0 (fr 4)
    c.start s) [[1, 1.4142135623730951, 2, 2.8284271247461903, 4]]
-- The `value` setter, and an offset of 0.1 is rounded to binary32 in the result.
#guard chk (go 1 4 fun c => do
    let (c, s) ← c.createConstantSource
    let c ← c.connect s 0 0 0
    let c ← c.setParamValue s 0 0.25
    c.start s) [[0.25, 0.25, 0.25, 0.25]]

-- GainNode with a constant gain (WPT the-gainnode-interface/gain.html: output is input times
-- gain): source offset 2, gain 0.5.
#guard chk (go 1 6 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, g) ← c.createGain
    let c ← c.setParamValue s 0 2.0
    let c ← c.setParamValue g 0 0.5
    let c ← c.connect s 0 g 0
    let c ← c.connect g 0 0 0
    c.start s) [[1, 1, 1, 1, 1, 1]]
-- Gain 1 until frame 3, then 0.25 (setValueAtTime).
#guard chk (go 1 6 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, g) ← c.createGain
    let c ← c.setValueAtTime g 0 0.25 (fr 3)
    let c ← c.connect s 0 g 0
    let c ← c.connect g 0 0 0
    c.start s) [[1, 1, 1, 0.25, 0.25, 0.25]]
-- Gain with a linear ramp: input 1, gain i/8.
#guard chk (go 1 10 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, g) ← c.createGain
    let c ← c.setValueAtTime g 0 0.0 0.0
    let c ← c.linearRampToValueAtTime g 0 1.0 (fr 8)
    let c ← c.connect s 0 g 0
    let c ← c.connect g 0 0 0
    c.start s) [[0, 0.125, 0.25, 0.375, 0.5, 0.625, 0.75, 0.875, 1, 1]]
-- k-rate gain with the same ramp: the value at the first frame of each quantum (0 for frames
-- 0 to 3, 0.5 for frames 4 to 7, 1 after).
#guard chk (go 1 10 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, g) ← c.createGain
    let c ← c.setAutomationRate g 0 false
    let c ← c.setValueAtTime g 0 0.0 0.0
    let c ← c.linearRampToValueAtTime g 0 1.0 (fr 8)
    let c ← c.connect s 0 g 0
    let c ← c.connect g 0 0 0
    c.start s) [[0, 0, 0, 0, 0.5, 0.5, 0.5, 0.5, 1, 1]]
-- Audio-rate modulation (WPT audioparam-connect-audioratesignal.html: a signal connected to
-- gain.gain, with gain 0, scales a constant 1 exactly by the signal): control signal i/8 from a
-- ConstantSource with a ramp.
#guard chk (go 1 10 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, m) ← c.createConstantSource
    let (c, g) ← c.createGain
    let c ← c.setParamValue g 0 0.0
    let c ← c.setValueAtTime m 0 0.0 0.0
    let c ← c.linearRampToValueAtTime m 0 1.0 (fr 8)
    let c ← c.connect s 0 g 0
    let c ← c.connectParam m 0 g 0
    let c ← c.connect g 0 0 0
    let c ← c.start s
    c.start m) [[0, 0.125, 0.25, 0.375, 0.5, 0.625, 0.75, 0.875, 1, 1]]
-- Modulation adds to the intrinsic value: gain 1 plus signal 0.5, source 2 gives 3.
#guard chk (go 1 4 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, m) ← c.createConstantSource
    let (c, g) ← c.createGain
    let c ← c.setParamValue s 0 2.0
    let c ← c.setParamValue m 0 0.5
    let c ← c.connect s 0 g 0
    let c ← c.connectParam m 0 g 0
    let c ← c.connect g 0 0 0
    let c ← c.start s
    c.start m) [[3, 3, 3, 3]]
-- Two sources into one input are summed.
#guard chk (go 1 4 fun c => do
    let (c, a) ← c.createConstantSource
    let (c, b) ← c.createConstantSource
    let c ← c.setParamValue b 0 2.0
    let c ← c.connect a 0 0 0
    let c ← c.connect b 0 0 0
    let c ← c.start a
    c.start b) [[3, 3, 3, 3]]
-- A gain on stereo input applies to each channel (merger of 1 and 2).
#guard chk (go 2 3 fun c => do
    let (c, a) ← c.createConstantSource
    let (c, b) ← c.createConstantSource
    let (c, m) ← c.createChannelMerger 2
    let (c, g) ← c.createGain
    let c ← c.setParamValue b 0 2.0
    let c ← c.setParamValue g 0 0.5
    let c ← c.connect a 0 m 0
    let c ← c.connect b 0 m 1
    let c ← c.connect m 0 g 0
    let c ← c.connect g 0 0 0
    let c ← c.start a
    c.start b) [[0.5, 0.5, 0.5], [1, 1, 1]]
-- Clamping to the nominal range: a pan of 5 (from a connected signal) gives hard right.
#guard chk (go 2 2 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, m) ← c.createConstantSource
    let (c, p) ← c.createStereoPanner
    let c ← c.setParamValue m 0 5.0
    let c ← c.connect s 0 p 0
    let c ← c.connectParam m 0 p 0
    let c ← c.connect p 0 0 0
    let c ← c.start s
    c.start m) [[0, 0], [1, 1]]

-- StereoPanner, mono to stereo (formulas of the Spatialization section): pan -1, 0, 1.
#guard chk (go 2 2 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, p) ← c.createStereoPanner
    let c ← c.setParamValue p 0 (-1.0)
    let c ← c.connect s 0 p 0
    let c ← c.connect p 0 0 0
    c.start s) [[1, 1], [0, 0]]
#guard chk (go 2 2 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, p) ← c.createStereoPanner
    let c ← c.connect s 0 p 0
    let c ← c.connect p 0 0 0
    c.start s) [[0.7071067811865476, 0.7071067811865476], [0.7071067811865476, 0.7071067811865476]]
#guard chk (go 2 2 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, p) ← c.createStereoPanner
    let c ← c.setParamValue p 0 1.0
    let c ← c.connect s 0 p 0
    let c ← c.connect p 0 0 0
    c.start s) [[0, 0], [1, 1]]

-- Splitter and merger: two constants (1 and 2) merged to stereo into a stereo destination.
#guard chk (go 2 3 fun c => do
    let (c, a) ← c.createConstantSource
    let (c, b) ← c.createConstantSource
    let (c, m) ← c.createChannelMerger 2
    let c ← c.setParamValue b 0 2.0
    let c ← c.connect a 0 m 0
    let c ← c.connect b 0 m 1
    let c ← c.connect m 0 0 0
    let c ← c.start a
    c.start b) [[1, 1, 1], [2, 2, 2]]
-- Merger then splitter; output 1 of the splitter goes to a mono destination.
#guard chk (go 1 3 fun c => do
    let (c, a) ← c.createConstantSource
    let (c, b) ← c.createConstantSource
    let (c, m) ← c.createChannelMerger 2
    let (c, sp) ← c.createChannelSplitter 2
    let c ← c.setParamValue b 0 2.0
    let c ← c.connect a 0 m 0
    let c ← c.connect b 0 m 1
    let c ← c.connect m 0 sp 0
    let c ← c.connect sp 1 0 0
    let c ← c.start a
    c.start b) [[2, 2, 2]]
-- Mono into a stereo destination: speakers up-mix copies the channel.
#guard chk (go 2 3 fun c => do
    let (c, s) ← c.createConstantSource
    let c ← c.connect s 0 0 0
    c.start s) [[1, 1, 1], [1, 1, 1]]
-- Stereo (1, 2) into a mono destination: speakers down-mix is 0.5 * (L + R).
#guard chk (go 1 3 fun c => do
    let (c, a) ← c.createConstantSource
    let (c, b) ← c.createConstantSource
    let (c, m) ← c.createChannelMerger 2
    let c ← c.setParamValue b 0 2.0
    let c ← c.connect a 0 m 0
    let c ← c.connect b 0 m 1
    let c ← c.connect m 0 0 0
    let c ← c.start a
    c.start b) [[1.5, 1.5, 1.5]]

-- Delay of whole frames (WPT the-delaynode-interface/delaynode-maxdelay.html uses a delay time
-- above the default maximum; here the maximum is the default 1 s): the pulse of frames 0 and 1,
-- delayed by 3 frames.
#guard chk (go 1 10 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, d) ← c.createDelay
    let c ← c.setParamValue d 0 (fr 3)
    let c ← c.connect s 0 d 0
    let c ← c.connect d 0 0 0
    let c ← c.start s
    c.stop s (fr 2)) [zeros 3 ++ ones 2 ++ zeros 5]
-- A delay of 5 frames, across a quantum boundary.
#guard chk (go 1 10 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, d) ← c.createDelay
    let c ← c.setParamValue d 0 (fr 5)
    let c ← c.connect s 0 d 0
    let c ← c.connect d 0 0 0
    let c ← c.start s
    c.stop s (fr 2)) [zeros 5 ++ ones 2 ++ zeros 3]
-- A delay of 0 outside a cycle gives the input unchanged.
#guard chk (go 1 6 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, d) ← c.createDelay
    let c ← c.connect s 0 d 0
    let c ← c.connect d 0 0 0
    let c ← c.start s
    c.stop s (fr 2)) [[1, 1, 0, 0, 0, 0]]
-- A delay maximum below 0 or at 180 s is refused.
#guard isErr (OfflineContext.new 1 4 4096.0 4 >>= fun c => c.createDelay 0.0 >>= fun _ => pure ())
  (.notSupported "maxDelayTime must be greater than 0 and less than 180")
#guard isErr (OfflineContext.new 1 4 4096.0 4 >>= fun c => c.createDelay 180.0 >>= fun _ => pure ())
  (.notSupported "maxDelayTime must be greater than 0 and less than 180")

-- A cycle through a Delay: s -> gain(0.5) -> delay -> gain, delay -> destination. The delay in a
-- cycle is at least one quantum (4 frames) even with delayTime 0: y(t) = 0.5 (s(t-4) + y(t-4)),
-- with s a pulse at frame 0 (start 0, stop frame 1).
private def feedback (dt : Float) (c : OfflineContext) : Except Error OfflineContext := do
  let (c, s) ← c.createConstantSource
  let (c, g) ← c.createGain
  let (c, d) ← c.createDelay
  let c ← c.setParamValue g 0 0.5
  let c ← c.setParamValue d 0 dt
  let c ← c.connect s 0 g 0
  let c ← c.connect g 0 d 0
  let c ← c.connect d 0 g 0
  let c ← c.connect d 0 0 0
  let c ← c.start s
  c.stop s (fr 1)
#guard chk (go 1 12 (feedback 0.0))
  [[0, 0, 0, 0, 0.5, 0, 0, 0, 0.25, 0, 0, 0]]
-- With delayTime 8 frames: y(t) = 0.5 (s(t-8) + y(t-8)).
#guard chk (go 1 20 (feedback (fr 8)))
  [zeros 8 ++ [0.5] ++ zeros 7 ++ [0.25] ++ zeros 3]
-- The plan splits the delay: the cycle is cut, nothing is muted.
#guard (match OfflineContext.new 1 4 4096.0 4 >>= feedback 0.0 with
  | .ok c =>
    let pl := Render.Plan.of c.state.graph
    pl.muted.isEmpty && pl.steps.contains (.delayRead 3) && pl.steps.contains (.delayWrite 3) &&
    !pl.steps.contains (.node 3)
  | .error _ => false)

-- A cycle with no Delay: the two gains are muted, the destination gets silence.
#guard chk (go 1 8 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, g1) ← c.createGain
    let (c, g2) ← c.createGain
    let c ← c.connect s 0 g1 0
    let c ← c.connect g1 0 g2 0
    let c ← c.connect g2 0 g1 0
    let c ← c.connect g2 0 0 0
    c.start s) [zeros 8]
-- The same cycle with a second, uncycled path still plays the path.
#guard chk (go 1 4 fun c => do
    let (c, s) ← c.createConstantSource
    let (c, g1) ← c.createGain
    let (c, g2) ← c.createGain
    let c ← c.connect s 0 g1 0
    let c ← c.connect g1 0 g2 0
    let c ← c.connect g2 0 g1 0
    let c ← c.connect s 0 0 0
    c.start s) [[1, 1, 1, 1]]

-- Render lengths. A destination with nothing connected: silence, `numberOfChannels` channels.
#guard chk (go 3 5 fun c => pure c) [zeros 5, zeros 5, zeros 5]
-- 300 frames at 44100 Hz with the default quantum of 128: 3 quanta, trimmed to 300 frames.
#guard (match go 1 300 (fun c => do
      let (c, s) ← c.createConstantSource
      let c ← c.connect s 0 0 0
      c.start s) 128 44100.0 with
  | .ok out => out.size == 1 && out[0]!.size == 300 && out[0]!.data[299]! == 1.0
  | .error _ => false)
-- The same length with a pulse that starts at frame 129 and stops at frame 258 (quantum edges
-- at 128 and 256).
#guard (match go 1 300 (fun c => do
      let (c, s) ← c.createConstantSource
      let c ← c.connect s 0 0 0
      let c ← c.start s (129.0 / 44100.0)
      c.stop s (258.0 / 44100.0)) 128 44100.0 with
  | .ok out => out[0]!.data[128]! == 0.0 && out[0]!.data[129]! == 1.0 &&
      out[0]!.data[257]! == 1.0 && out[0]!.data[258]! == 0.0
  | .error _ => false)
-- Binary32 rounding: 0.1 is stored as the nearest binary32 value, not as the binary64 value.
#guard (match go 1 2 (fun c => do
      let (c, s) ← c.createConstantSource
      let c ← c.setParamValue s 0 0.1
      let c ← c.connect s 0 0 0
      c.start s) with
  | .ok out => out[0]!.data[0]! == (0.1 : Float).toFloat32.toFloat && out[0]!.data[0]! != 0.1
  | .error _ => false)
-- A number above the binary32 range becomes infinity; the value 1.0 is unchanged.
#guard (3.5e38 : Float).toFloat32.toFloat == (1.0 / 0.0 : Float)

-- Errors of the graph and the nodes.
#guard (match OfflineContext.new 1 4 4096.0 4 with
  | .ok c => isErr (c.createChannelMerger 0 >>= fun _ => pure ()) .indexSize &&
             isErr (c.createChannelMerger 33 >>= fun _ => pure ()) .indexSize &&
             isErr (c.createChannelSplitter 0 >>= fun _ => pure ()) .indexSize &&
             (c.createChannelSplitter 32).toOption.isSome
  | .error _ => false)
-- connect: output 1 of a gain does not exist; a destination has no output; input 1 of the
-- destination does not exist; parameter 1 of a gain does not exist.
#guard (match OfflineContext.new 1 4 4096.0 4 >>= fun c => c.createGain with
  | .ok (c, g) => isErr (c.connect g 1 0 0) .indexSize && isErr (c.connect 0 0 g 0) .indexSize &&
      isErr (c.connect g 0 0 1) .indexSize && isErr (c.connectParam g 0 g 1) .indexSize &&
      isErr (c.connect g 0 9 0) .unknownNode
  | .error _ => false)
-- start twice, stop before start, negative and non-finite times.
#guard (match OfflineContext.new 1 4 4096.0 4 >>= fun c => c.createConstantSource with
  | .ok (c, s) =>
    isErr (c.stop s 0.0 >>= fun _ => pure ()) (.invalidState "start was not called") &&
    isErr (c.start s (-1.0) >>= fun _ => pure ()) (.range "when is negative") &&
    isErr (c.start s (0.0 / 0.0) >>= fun _ => pure ()) (.type "when is not finite") &&
    (match c.start s with
     | .ok c2 => isErr (c2.start s >>= fun _ => pure ()) (.invalidState "start was called before")
     | .error _ => false)
  | .error _ => false)
-- AudioParam errors: a negative time (RangeError), a non-finite value (TypeError), a ramp to 0
-- exponentially (RangeError).
#guard (match OfflineContext.new 1 4 4096.0 4 >>= fun c => c.createGain with
  | .ok (c, g) =>
    isErr (c.setValueAtTime g 0 1.0 (-1.0) >>= fun _ => pure ()) (.range "time is negative") &&
    isErr (c.setValueAtTime g 0 (0.0 / 0.0) 0.0 >>= fun _ => pure ()) (.type "value is not finite") &&
    isErr (c.exponentialRampToValueAtTime g 0 0.0 1.0 >>= fun _ => pure ()) (.range "exponential ramp to 0") &&
    isErr (c.setValueAtTime g 1 1.0 0.0 >>= fun _ => pure ()) .indexSize
  | .error _ => false)
-- startRendering twice (WPT startrendering-after-discard.html expects InvalidStateError for a
-- context that cannot render; the second call of a rendered context gives the same error).
#guard (match OfflineContext.new 1 4 4096.0 4 >>= fun c => c.startRendering with
  | .ok (c, out) => out.size == 1 && out[0]!.size == 4 &&
      isErr (c.startRendering >>= fun _ => pure ()) (.invalidState "rendering already started")
  | .error _ => false)
-- A result of 3 channels has exactly the requested size, also when the length is below one
-- quantum.
#guard (match go 3 1 (fun c => pure c) with
  | .ok out => out.size == 3 && out.all (·.size == 1)
  | .error _ => false)

end Tests

end L4Factoidal.WebAudio.Context
