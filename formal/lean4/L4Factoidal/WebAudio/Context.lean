/-
# Web Audio API: the offline context

Follows https://webaudio.github.io/web-audio-api/ : the `OfflineAudioContext` interface
(constructor `OfflineAudioContext(numberOfChannels, length, sampleRate)` and its checks,
`startRendering`), section 2.4 "Supported Sample Rates", section 2.5 "Supported Render Quantum
Sizes", the factory methods of `BaseAudioContext` (`createGain`, `createConstantSource`,
`createDelay`, `createStereoPanner`, `createChannelSplitter`, `createChannelMerger`,
`createOscillator`, `createBiquadFilter`, `createBufferSource`, `createBuffer`,
`createPeriodicWave`), the setters of those nodes (`type`, `setPeriodicWave`, `buffer`, `loop`,
`loopStart`, `loopEnd`), `connect`,
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
StereoPanner `pan` 0; Oscillator `frequency` 0, `detune` 1; BiquadFilter `frequency` 0, `detune` 1,
`Q` 2, `gain` 3; AudioBufferSource `playbackRate` 0, `detune` 1.

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
* `disconnect`, `getFrequencyResponse` of the filter, the `ended` event as an event (`ended` is
  a function of the context: true when the source has finished), `setValueCurveAtTime`, `cancelAndHoldAtTime` (in `Automation`, not exposed
  here), `AudioListener`, and `OfflineAudioContextOptions.renderSizeHint` as a string (the
  quantum size is a number argument).
-/
import L4Factoidal.WebAudio.Mix
import L4Factoidal.WebAudio.Automation
import L4Factoidal.WebAudio.Kernels
import L4Factoidal.WebAudio.Graph
import L4Factoidal.WebAudio.Render
import L4Factoidal.WebAudio.Oscillator
import L4Factoidal.WebAudio.Filters
import L4Factoidal.WebAudio.Buffer

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

/-- The error of `Buffer.lean`. -/
def Error.ofBuffer : Buffer.Error → Error
  | .typeError => .type "argument is not finite"
  | .indexSize => .indexSize
  | .notSupported => .notSupported "argument outside the supported range"
  | .invalidState => .invalidState "invalid state"
  | .range => .range "negative argument"

/-- The error of `Oscillator.lean`. -/
def Error.ofWave : Oscillator.WaveError → Error
  | .indexSizeError => .indexSize
  | .typeError => .type "coefficient is not finite"
  | .invalidStateError => .invalidState "type custom needs a PeriodicWave"

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

/-- `createOscillator()`: type `sine`, `frequency` 440, `detune` 0. -/
def OfflineContext.createOscillator (c : OfflineContext) : Except Error (OfflineContext × Nat) :=
  .ok (c.addNode .oscillator)

/-- `createBiquadFilter()`: type `lowpass`, `frequency` 350, `detune` 0, `Q` 1, `gain` 0. -/
def OfflineContext.createBiquadFilter (c : OfflineContext) : Except Error (OfflineContext × Nat) :=
  .ok (c.addNode .biquad)

/-- `createBufferSource()`: no buffer, `loop` false, `loopStart` and `loopEnd` 0,
`playbackRate` 1, `detune` 0. -/
def OfflineContext.createBufferSource (c : OfflineContext) : Except Error (OfflineContext × Nat) :=
  .ok (c.addNode .bufferSource)

/-- `createBuffer(numberOfChannels, length, sampleRate)`: `NotSupportedError` when a value is out
of range (`Buffer.AudioBuffer.create`). -/
def OfflineContext.createBuffer (_ : OfflineContext) (numberOfChannels length : Nat)
    (sampleRate : Float) : Except Error Buffer.AudioBuffer :=
  match Buffer.AudioBuffer.create numberOfChannels length sampleRate with
  | .ok b => .ok b
  | .error e => .error (Error.ofBuffer e)

/-- `createPeriodicWave(real, imag, constraints)` (`Oscillator.createPeriodicWave`). -/
def OfflineContext.createPeriodicWave (_ : OfflineContext) (real imag : FloatArray)
    (disableNormalization : Bool := false) : Except Error Oscillator.PeriodicWave :=
  match Oscillator.createPeriodicWave real imag disableNormalization with
  | .ok w => .ok w
  | .error e => .error (Error.ofWave e)

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
      | .osc s =>
        if s.startFrame.isSome then .error (.invalidState "start was called before")
        else .ok (c.setKs id { nd with ks := .osc (s.start when_) })
      | .buf cfg s set =>
        match s.start when_ with
        | .ok s' => .ok (c.setKs id { nd with ks := .buf cfg s' set })
        | .error e => .error (Error.ofBuffer e)
      | _ => .error (.invalidState "the node is not a scheduled source")

/-- `start(when, offset, duration)` of an `AudioBufferSourceNode` (`duration` absent: play to the
end). `InvalidStateError` when `start` was called before, `TypeError` for a non-finite argument,
`RangeError` for a negative one (`Buffer.SourceState.start`). -/
def OfflineContext.startBuffer (c : OfflineContext) (id : Nat) (when_ : Float := 0.0)
    (offset : Float := 0.0) (duration : Option Float := none) : Except Error OfflineContext :=
  match c.state.nodes[id]? with
  | none => .error .unknownNode
  | some nd =>
    match nd.ks with
    | .buf cfg s set =>
      match s.start when_ offset duration with
      | .ok s' => .ok (c.setKs id { nd with ks := .buf cfg s' set })
      | .error e => .error (Error.ofBuffer e)
    | _ => .error (.invalidState "the node is not an AudioBufferSourceNode")

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
      | .osc s =>
        if s.startFrame.isNone then .error (.invalidState "start was not called")
        else .ok (c.setKs id { nd with ks := .osc (s.stop when_) })
      | .buf cfg s set =>
        match s.stop (some when_) with
        | .ok s' => .ok (c.setKs id { nd with ks := .buf cfg s' set })
        | .error e => .error (Error.ofBuffer e)
      | _ => .error (.invalidState "the node is not a scheduled source")

/-- Has the scheduled source finished? A constant source or oscillator: its stop frame is set and
has been reached by the current frame. An `AudioBufferSourceNode`: it was started and its playback
has ended (`SourceState.finished`: the stop time, the `duration` or the end of a buffer that does
not loop, reached at the end of a block). This is the condition of the `ended` event, not the
event. -/
def OfflineContext.ended (c : OfflineContext) (id : Nat) : Bool :=
  match c.state.nodes[id]? with
  | some nd =>
    match nd.ks with
    | .const s => match s.stopFrame with | some e => decide (e ≤ c.state.frame) | none => false
    | .osc s => match s.stopFrame with | some e => decide (e ≤ c.state.frame) | none => false
    | .buf _ s _ => s.startFrame.isSome && s.finished
    | _ => false
  | none => false

/-! ## Node attributes -/

/-- Replace the kernel state of node `id` by `f` of it (`f` may fail with the error of the
specification). -/
private def OfflineContext.modifyKs (c : OfflineContext) (id : Nat)
    (f : Render.KState → Except Error Render.KState) : Except Error OfflineContext :=
  match c.state.nodes[id]? with
  | none => .error .unknownNode
  | some nd =>
    match f nd.ks with
    | .ok ks => .ok (c.setKs id { nd with ks := ks })
    | .error e => .error e

/-- The `type` setter of an `OscillatorNode`: a built-in type; `custom` gives `InvalidStateError`.
The phase is kept. -/
def OfflineContext.setOscillatorType (c : OfflineContext) (id : Nat) (t : Oscillator.OscType) :
    Except Error OfflineContext :=
  c.modifyKs id fun ks =>
    match ks with
    | .osc s =>
      match s.setType t with
      | .ok s' => .ok (.osc s')
      | .error e => .error (Error.ofWave e)
    | _ => .error (.invalidState "the node is not an OscillatorNode")

/-- `setPeriodicWave(periodicWave)`: the type becomes `custom`; the phase is kept. -/
def OfflineContext.setPeriodicWave (c : OfflineContext) (id : Nat) (w : Oscillator.PeriodicWave) :
    Except Error OfflineContext :=
  c.modifyKs id fun ks =>
    match ks with
    | .osc s => .ok (.osc (s.setPeriodicWave w))
    | _ => .error (.invalidState "the node is not an OscillatorNode")

/-- The `type` setter of a `BiquadFilterNode`. -/
def OfflineContext.setBiquadType (c : OfflineContext) (id : Nat) (t : Filters.BiquadType) :
    Except Error OfflineContext :=
  c.modifyKs id fun ks =>
    match ks with
    | .biquad s => .ok (.biquad { s with type := t })
    | _ => .error (.invalidState "the node is not a BiquadFilterNode")

/-- The `buffer` setter of an `AudioBufferSourceNode`. `InvalidStateError` when a non-null buffer
was set before and the new value is non-null too ("the buffer attribute ... was previously set to
a non-null value"). Setting `null` is allowed. -/
def OfflineContext.setBuffer (c : OfflineContext) (id : Nat) (b : Option Buffer.AudioBuffer) :
    Except Error OfflineContext :=
  c.modifyKs id fun ks =>
    match ks with
    | .buf cfg s set =>
      if b.isSome && set then .error (.invalidState "buffer was already set to a non-null value")
      else .ok (.buf { cfg with buffer := b } s (set || b.isSome))
    | _ => .error (.invalidState "the node is not an AudioBufferSourceNode")

/-- "Acquire the content" of the buffer of an `AudioBufferSourceNode` (`start()`, or the `buffer`
setter after `start()`): the node takes the samples that the buffer has now. A node whose `buffer`
was not set to a non-null value is left alone (`InvalidStateError` for a node that is not a buffer
source). Unlike `setBuffer` it does not refuse a second non-null buffer. -/
def OfflineContext.acquireBuffer (c : OfflineContext) (id : Nat) (b : Buffer.AudioBuffer) :
    Except Error OfflineContext :=
  c.modifyKs id fun ks =>
    match ks with
    | .buf cfg s set => .ok (.buf (if set then { cfg with buffer := some b } else cfg) s set)
    | _ => .error (.invalidState "the node is not an AudioBufferSourceNode")

/-- The `loop` attribute. -/
def OfflineContext.setLoop (c : OfflineContext) (id : Nat) (loop : Bool) :
    Except Error OfflineContext :=
  c.modifyKs id fun ks =>
    match ks with
    | .buf cfg s set => .ok (.buf { cfg with loop := loop } s set)
    | _ => .error (.invalidState "the node is not an AudioBufferSourceNode")

/-- The `loopStart` attribute, in seconds of the buffer. -/
def OfflineContext.setLoopStart (c : OfflineContext) (id : Nat) (v : Float) :
    Except Error OfflineContext :=
  c.modifyKs id fun ks =>
    match ks with
    | .buf cfg s set => .ok (.buf { cfg with loopStart := v } s set)
    | _ => .error (.invalidState "the node is not an AudioBufferSourceNode")

/-- The `loopEnd` attribute, in seconds of the buffer. -/
def OfflineContext.setLoopEnd (c : OfflineContext) (id : Nat) (v : Float) :
    Except Error OfflineContext :=
  c.modifyKs id fun ks =>
    match ks with
    | .buf cfg s set => .ok (.buf { cfg with loopEnd := v } s set)
    | _ => .error (.invalidState "the node is not an AudioBufferSourceNode")

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

/-- `setValueCurveAtTime(values, startTime, duration)`. Errors as `Automation.validate` and
`Automation.insert` decide: a non-finite element or time is a `TypeError`, fewer than 2 values an
`InvalidStateError`, a negative start time or a duration that is not strictly positive a
`RangeError`, an overlap a `NotSupportedError`. -/
def OfflineContext.setValueCurveAtTime (c : OfflineContext) (id param : Nat)
    (values : Array Float) (startTime duration : Float) : Except Error OfflineContext :=
  c.withParam id param fun p now cur => do
    let t ← Automation.eventTime startTime
    let d ← Automation.eventTime duration
    Automation.insert p.timeline ⟨.setValueCurve values d none, t, 0.0⟩ now cur

/-- `cancelAndHoldAtTime(cancelTime)`. -/
def OfflineContext.cancelAndHoldAtTime (c : OfflineContext) (id param : Nat)
    (cancelTime : Float) : Except Error OfflineContext :=
  c.withParam id param fun p now _ => do
    let t ← Automation.cancelTimeOfDouble cancelTime now
    pure (Automation.cancelAndHold p.timeline t p.spec.defaultValue)

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
  if c.rendered ∨ 0 < c.state.frame then .error (.invalidState "rendering already started")
  else
    let q := c.state.quantum
    let r := renderLoop ((c.length + q - 1) / q) c.state (Render.Plan.of c.state.graph) #[]
    .ok ({ c with state := r.1, rendered := true },
         assemble c.numberOfChannels c.length q r.2)

/-- Rendering in steps (`suspend`, `resume`, `startRendering(chunkSize)`): renders at most `quanta`
render quanta from the current frame and returns the context after them with `numberOfChannels`
channels of the frames of those quanta (binary32 values). The last chunk of the context is cut at
`length`: the number of frames is `min (k * n) (length - frame)` for the `k` quanta rendered, and
`k` is `quanta` or fewer when `length` comes first. `InvalidStateError` when the context has
already reached its `length`. The context is `rendered` once `frame ≥ length`. The graph is
planned again at each step, so a step sees the changes that the page made after the one before. -/
def OfflineContext.renderChunk (c : OfflineContext) (quanta : Nat) :
    Except Error (OfflineContext × Array FloatArray) :=
  if c.length ≤ c.state.frame then .error (.invalidState "rendering finished")
  else
    let q := c.state.quantum
    let left := (c.length - c.state.frame + q - 1) / q
    let k := if quanta < left then quanta else left
    let frames := if k * q < c.length - c.state.frame then k * q else c.length - c.state.frame
    let r := renderLoop k c.state (Render.Plan.of c.state.graph) #[]
    .ok ({ c with state := r.1, rendered := c.length ≤ r.1.frame },
         assemble c.numberOfChannels frames q r.2)

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

/-- Says: a step returns exactly `numberOfChannels` channels, all of one length. Does not say: the
values, or how long the length is. -/
theorem renderChunk_shape (c c' : OfflineContext) (quanta : Nat) (out : Array FloatArray)
    (h : c.renderChunk quanta = .ok (c', out)) :
    out.size = c.numberOfChannels ∧ ∃ n, ∀ ch ∈ out, ch.size = n := by
  unfold OfflineContext.renderChunk at h
  split at h
  · cases h
  · cases h
    exact ⟨(assemble_shape _ _ _ _).1, _, (assemble_shape _ _ _ _).2⟩

/-- Says: a step does not change the graph. -/
theorem renderChunk_graph (c c' : OfflineContext) (quanta : Nat) (out : Array FloatArray)
    (h : c.renderChunk quanta = .ok (c', out)) : c'.state.graph = c.state.graph := by
  unfold OfflineContext.renderChunk at h
  split at h
  · cases h
  · cases h
    exact renderLoop_graph _ _ _ _

/-- Says: a step from the start of a context advances the frame by whole quanta, so that a step
ends at a quantum boundary. -/
theorem renderChunk_frame (c c' : OfflineContext) (quanta : Nat) (out : Array FloatArray)
    (h : c.renderChunk quanta = .ok (c', out)) :
    ∃ k, c'.state.frame = c.state.frame + k * c.state.quantum := by
  unfold OfflineContext.renderChunk at h
  split at h
  · cases h
  · cases h
    exact ⟨_, (renderLoop_frame _ _ _ _).1⟩

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

-- binary32 outputs (WPT nan-param.html): 1e30 through a gain of 1e30 is +infinity, through a gain of
-- -1e30 is -infinity, and the two meet at the destination as NaN.
#guard (match go 1 4 (fun c => do
    let (c, m) ← c.createConstantSource
    let c ← c.setValueAtTime m 0 1e30 0.0
    let (c, g1) ← c.createGain
    let (c, g2) ← c.createGain
    let c ← c.setValueAtTime g1 0 1e30 0.0
    let c ← c.setValueAtTime g2 0 (-1e30) 0.0
    let c ← c.connect m 0 g1 0
    let c ← c.connect m 0 g2 0
    let c ← c.connect g1 0 0 0
    let c ← c.connect g2 0 0 0
    c.start m) with
  | .ok out => (out.getD 0 ⟨#[]⟩).data.all (fun x => x != x)
  | .error _ => false)

-- a NaN input of a parameter is replaced by the default value (WPT nan-param.html, second part)
#guard (match go 1 4 (fun c => do
    let (c, m) ← c.createConstantSource
    let c ← c.setValueAtTime m 0 1e30 0.0
    let (c, g1) ← c.createGain
    let (c, g2) ← c.createGain
    let c ← c.setValueAtTime g1 0 1e30 0.0
    let c ← c.setValueAtTime g2 0 (-1e30) 0.0
    let c ← c.connect m 0 g1 0
    let c ← c.connect m 0 g2 0
    let (c, src) ← c.createConstantSource
    let c ← c.setValueAtTime src 0 100.0 0.0
    let c ← c.connectParam g1 0 src 0
    let c ← c.connectParam g2 0 src 0
    let c ← c.connect src 0 0 0
    let c ← c.start m
    c.start src) with
  | .ok out => (out.getD 0 ⟨#[]⟩).data.all (fun x => x == 1.0)
  | .error _ => false)

-- Rendering in steps: length 10, quanta of 4, a source starting at frame 5. One quantum gives 4
-- frames, the next step is cut at the length (6 frames, not 8), and a third step is refused.
private def stepped : Except Error (Array FloatArray × Array FloatArray × Bool) := do
  let c ← OfflineContext.new 1 10 4096.0 4
  let (c, s) ← c.createConstantSource
  let c ← c.connect s 0 0 0
  let c ← c.start s (fr 5)
  let (c, a) ← c.renderChunk 1
  let (c, b) ← c.renderChunk 5
  pure (a, b, (c.renderChunk 1).toOption.isNone && c.rendered)
#guard (match stepped with
  | .ok (a, b, ok) => approxL a[0]!.data.toList (zeros 4) && approxL b[0]!.data.toList [0.0, 1.0, 1.0, 1.0, 1.0, 1.0] && ok
  | .error _ => false)
-- The same graph rendered at once, and a whole render after a step, which is refused.
#guard (match (do
    let c ← OfflineContext.new 1 10 4096.0 4
    let (c, _) ← c.renderChunk 1
    c.startRendering : Except Error _) with
  | .error (.invalidState _) => true | _ => false)

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

/-! ### Oscillator, BiquadFilter, AudioBufferSource and the split delay

Sample rate 4096 Hz, quantum 4. An oscillator at 1024 Hz advances its phase by 1/4 cycle per frame,
so its sine takes the exact values 0, 1, 0, -1 (WPT `OscillatorNode/osc-basic-waveform.html`
compares a sine with `sin` in the same way). -/

/-- Like `go`, and also returns the context after the render. -/
private def goC (nch len : Nat) (build : OfflineContext → Except Error OfflineContext)
    (q : Nat := 4) : Except Error (OfflineContext × Array FloatArray) := do
  let c ← OfflineContext.new nch len 4096.0 q
  let c ← build c
  c.startRendering

private def sine4 : List Float := [0, 1, 0, -1]

/-- An oscillator of frequency `f` into the destination; returns the context and the node. -/
private def oscTo (c : OfflineContext) (f : Float) : Except Error (OfflineContext × Nat) := do
  let (c, s) ← c.createOscillator
  let c ← c.connect s 0 0 0
  let c ← c.setValueAtTime s 0 f 0.0
  pure (c, s)

-- 1. Sine at 1024 Hz started at 0, length 8 (two quanta).
#guard chk (go 1 8 fun c => do
    let (c, s) ← oscTo c 1024.0
    c.start s) [sine4 ++ sine4]
-- 2. Not started: silence.
#guard chk (go 1 8 fun c => do
    let (c, _) ← oscTo c 1024.0
    pure c) [zeros 8]
-- 3. Start at frame 2 (inside the first quantum): the phase is 0 at the start frame.
#guard chk (go 1 8 fun c => do
    let (c, s) ← oscTo c 1024.0
    c.start s (fr 2)) [[0, 0, 0, 1, 0, -1, 0, 1]]
-- 4. Start at 0, stop at frame 5 (inside the second quantum).
#guard chk (go 1 8 fun c => do
    let (c, s) ← oscTo c 1024.0
    let c ← c.start s
    c.stop s (fr 5)) [[0, 1, 0, -1, 0, 0, 0, 0]]
-- 5. Stop inside the quantum of the start: start at frame 1, stop at frame 3.
#guard chk (go 1 8 fun c => do
    let (c, s) ← oscTo c 1024.0
    let c ← c.start s (fr 1)
    c.stop s (fr 3)) [[0, 0, 1, 0, 0, 0, 0, 0]]
-- 6. Detune 1200 cents doubles the frequency: 512 Hz with detune 1200 is 1024 Hz.
#guard chk (go 1 8 fun c => do
    let (c, s) ← oscTo c 512.0
    let c ← c.setValueAtTime s 1 1200.0 0.0
    c.start s) [sine4 ++ sine4]
-- 7. Frequency automation, a step at frame 4 from 512 to 1024 Hz (a-rate, so the step is
-- applied inside the quantum boundary at frame 4): the phase is 0.5 at frame 4.
#guard chk (go 1 8 fun c => do
    let (c, s) ← oscTo c 512.0
    let c ← c.setValueAtTime s 0 1024.0 (fr 4)
    c.start s) [[0, 0.70710678, 1, 0.70710678, 0, -1, 0, 1]]
-- 8. A frequency above Nyquist is clamped to Nyquist (nominal range), where no partial is below
-- the Nyquist frequency: silence.
#guard chk (go 1 8 fun c => do
    let (c, s) ← oscTo c 1.0e9
    c.start s) [zeros 8]
-- 9. A negative frequency (inside the nominal range): the phase runs backwards.
#guard chk (go 1 8 fun c => do
    let (c, s) ← oscTo c (-1024.0)
    c.start s) [[0, -1, 0, 1, 0, -1, 0, 1]]
-- 10. `frequency` driven by a ConstantSource: intrinsic 0 plus the input of 1024.
#guard chk (go 1 8 fun c => do
    let (c, s) ← c.createOscillator
    let c ← c.connect s 0 0 0
    let c ← c.setValueAtTime s 0 0.0 0.0
    let (c, k) ← c.createConstantSource
    let c ← c.setParamValue k 0 1024.0
    let c ← c.connectParam k 0 s 0
    let c ← c.start k
    c.start s) [sine4 ++ sine4]
-- 11. An oscillator through a gain of 0.5.
#guard chk (go 1 8 fun c => do
    let (c, s) ← c.createOscillator
    let (c, g) ← c.createGain
    let c ← c.setValueAtTime s 0 1024.0 0.0
    let c ← c.setValueAtTime g 0 0.5 0.0
    let c ← c.connect s 0 g 0
    let c ← c.connect g 0 0 0
    c.start s) [[0, 0.5, 0, -0.5, 0, 0.5, 0, -0.5]]
-- 12. A custom wave (cosine, normalization off) with `setPeriodicWave`.
#guard chk (go 1 8 fun c => do
    let (c, s) ← oscTo c 1024.0
    let w ← c.createPeriodicWave ⟨#[0.0, 1.0]⟩ ⟨#[0.0, 0.0]⟩ true
    let c ← c.setPeriodicWave s w
    c.start s) [[1, 0, -1, 0, 1, 0, -1, 0]]
-- 13. `type` setter: a built-in type is accepted, `custom` is InvalidStateError.
#guard (match OfflineContext.new 1 4 4096.0 4 >>= fun c => c.createOscillator with
  | .ok (c, s) =>
    (c.setOscillatorType s .square).toOption.isSome &&
    isErr (c.setOscillatorType s .custom >>= fun _ => pure ()) (.invalidState "type custom needs a PeriodicWave")
  | .error _ => false)
-- 14. Errors of `start` and `stop` of an oscillator, and of `createPeriodicWave`.
#guard (match OfflineContext.new 1 4 4096.0 4 >>= fun c => c.createOscillator with
  | .ok (c, s) =>
    isErr (c.stop s >>= fun _ => pure ()) (.invalidState "start was not called") &&
    isErr (c.start s (-1.0) >>= fun _ => pure ()) (.range "when is negative") &&
    (match c.start s with
     | .ok c2 => isErr (c2.start s >>= fun _ => pure ()) (.invalidState "start was called before")
     | .error _ => false) &&
    isErr (c.createPeriodicWave ⟨#[0.0, 1.0]⟩ ⟨#[0.0]⟩ >>= fun _ => pure ()) .indexSize &&
    isErr (c.createPeriodicWave ⟨#[0.0]⟩ ⟨#[0.0]⟩ >>= fun _ => pure ()) .indexSize
  | .error _ => false)
-- 15. A setter on a node of another type is InvalidStateError; an unknown node is `unknownNode`.
#guard (match OfflineContext.new 1 4 4096.0 4 >>= fun c => c.createGain with
  | .ok (c, g) =>
    isErr (c.setLoop g true >>= fun _ => pure ()) (.invalidState "the node is not an AudioBufferSourceNode") &&
    isErr (c.setBiquadType 9 .notch >>= fun _ => pure ()) .unknownNode
  | .error _ => false)

/-! Filters. The reference is the filter kernel run alone on the blocks of the oscillator kernel
run alone (same state, same parameter values). -/

/-- The oscillator kernel alone: `k` blocks of 4 frames of a sine of frequency `f`. -/
private def oscRef (f : Float) (k : Nat) : List Block :=
  let s0 : Oscillator.OscState :=
    { sampleRate := 4096.0, type := .sine, wave := Render.sineWave, startFrame := some 0 }
  (List.range k).foldl (init := ([], s0)) (fun (acc : List Block × Oscillator.OscState) _ =>
      let r := Oscillator.oscProcess 4 acc.2 #[] #[⟨#[f]⟩, ⟨#[0.0]⟩]
      (acc.1 ++ [r.2.getD 0 #[]], r.1)) |>.1

/-- The filter kernel alone over the blocks, with `freqs` the frequency of each block. -/
private def filterRef (t : Filters.BiquadType) (freqs : List Float) (blocks : List Block) :
    List Float :=
  let s0 : Filters.BiquadState := { type := t, sampleRate := 4096.0 }
  let r := (List.zip freqs blocks).foldl (init := (s0, ([] : List Float)))
    (fun (acc : Filters.BiquadState × List Float) (p : Float × Block) =>
      let o := Filters.biquadProcess 4 acc.1
        #[p.2] #[⟨#[p.1, p.1, p.1, p.1]⟩, ⟨#[0.0, 0.0, 0.0, 0.0]⟩, ⟨#[1.0, 1.0, 1.0, 1.0]⟩,
                 ⟨#[0.0, 0.0, 0.0, 0.0]⟩]
      (o.1, acc.2 ++ ((o.2.getD 0 #[]).getD 0 ⟨#[]⟩).data.toList))
  r.2

/-- Oscillator at `f` through a filter of type `t`, to the destination. -/
private def oscFilter (c : OfflineContext) (f : Float) (t : Filters.BiquadType) :
    Except Error (OfflineContext × Nat) := do
  let (c, s) ← c.createOscillator
  let (c, b) ← c.createBiquadFilter
  let c ← c.setValueAtTime s 0 f 0.0
  let c ← c.setBiquadType b t
  let c ← c.connect s 0 b 0
  let c ← c.connect b 0 0 0
  let c ← c.start s
  pure (c, b)

-- 16. Lowpass (default frequency 350, Q 1) on a 1024 Hz sine equals the kernel alone.
#guard chk (go 1 16 fun c => do
    let (c, _) ← oscFilter c 1024.0 .lowpass
    pure c) [filterRef .lowpass [350, 350, 350, 350] (oscRef 1024.0 4)]
-- 17. Highpass equals the kernel alone.
#guard chk (go 1 16 fun c => do
    let (c, _) ← oscFilter c 1024.0 .highpass
    pure c) [filterRef .highpass [350, 350, 350, 350] (oscRef 1024.0 4)]
-- 18. The filter changes the signal: the lowpass output is smaller than the sine at frame 15, and
-- the highpass output differs from the lowpass output.
#guard (match go 1 16 (fun c => do let (c, _) ← oscFilter c 1024.0 .lowpass; pure c),
              go 1 16 (fun c => do let (c, _) ← oscFilter c 1024.0 .highpass; pure c) with
  | .ok a, .ok b => (a[0]!.data[15]!).abs < 0.9 && (a[0]!.data[15]! - b[0]!.data[15]!).abs > 1e-3
  | _, _ => false)
-- 19. A step of the filter frequency at frame 8 (the start of a quantum) equals the kernel alone
-- with the new frequency from the third block.
#guard chk (go 1 16 fun c => do
    let (c, b) ← oscFilter c 1024.0 .lowpass
    c.setValueAtTime b 0 700.0 (fr 8)) [filterRef .lowpass [350, 350, 700, 700] (oscRef 1024.0 4)]
-- 20. An oscillator not started gives a filter output of silence.
#guard chk (go 1 8 fun c => do
    let (c, s) ← c.createOscillator
    let (c, b) ← c.createBiquadFilter
    let c ← c.connect s 0 b 0
    c.connect b 0 0 0) [zeros 8]

/-! AudioBufferSourceNode. The buffer has the sample rate of the context, so a rate of 1 plays one
buffer frame per output frame. -/

/-- A buffer from channel lists, at 4096 Hz. -/
private def mkBuf (c : OfflineContext) (chs : List (List Float)) : Except Error Buffer.AudioBuffer := do
  let len := (chs.headD []).length
  let b ← c.createBuffer chs.length len 4096.0
  pure ((List.range chs.length).foldl (init := b) fun b ch =>
    (List.range len).foldl (init := b) fun b i => b.writeSample ch i ((chs.getD ch []).getD i 0.0))

/-- A buffer source of the buffer `[1, 2, 3, 4]` into the destination. -/
private def bufTo (c : OfflineContext) : Except Error (OfflineContext × Nat) := do
  let b ← mkBuf c [[1, 2, 3, 4]]
  let (c, s) ← c.createBufferSource
  let c ← c.setBuffer s (some b)
  let c ← c.connect s 0 0 0
  pure (c, s)

-- 21. Rate 1: the buffer once, then silence.
#guard chk (go 1 12 fun c => do
    let (c, s) ← bufTo c
    c.start s) [[1, 2, 3, 4] ++ zeros 8]
-- 22. Not started: silence.
#guard chk (go 1 8 fun c => do
    let (c, _) ← bufTo c
    pure c) [zeros 8]
-- 23. playbackRate 0.5: linear interpolation; the value at frame 3.5 is the buffer
-- continued along its last two frames: 4 + 0.5 * (4 - 3) = 4.5.
#guard chk (go 1 12 fun c => do
    let (c, s) ← bufTo c
    let c ← c.setValueAtTime s 0 0.5 0.0
    c.start s) [[1, 1.5, 2, 2.5, 3, 3.5, 4, 4.5] ++ zeros 4]
-- 24. detune 1200 cents doubles the rate (k-rate).
#guard chk (go 1 8 fun c => do
    let (c, s) ← bufTo c
    let c ← c.setValueAtTime s 1 1200.0 0.0
    c.start s) [[1, 3] ++ zeros 6]
-- 25. loop over the whole buffer.
#guard chk (go 1 12 fun c => do
    let (c, s) ← bufTo c
    let c ← c.setLoop s true
    c.start s) [[1, 2, 3, 4, 1, 2, 3, 4, 1, 2, 3, 4]]
-- 26. loop between frame 1 and frame 3 (`loopStart`, `loopEnd` in seconds).
#guard chk (go 1 12 fun c => do
    let (c, s) ← bufTo c
    let c ← c.setLoop s true
    let c ← c.setLoopStart s (fr 1)
    let c ← c.setLoopEnd s (fr 3)
    c.start s) [[1, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2]]
-- 27. start(0, offset = 2 frames).
#guard chk (go 1 8 fun c => do
    let (c, s) ← bufTo c
    c.startBuffer s 0.0 (fr 2)) [[3, 4] ++ zeros 6]
-- 28. start(when = frame 2), stop at frame 4 (inside the second quantum for stop at 5).
#guard chk (go 1 8 fun c => do
    let (c, s) ← bufTo c
    let c ← c.start s (fr 2)
    c.stop s (fr 5)) [[0, 0, 1, 2, 3, 0, 0, 0]]
-- 29. start(0, 0, duration = 3 frames).
#guard chk (go 1 8 fun c => do
    let (c, s) ← bufTo c
    c.startBuffer s 0.0 0.0 (some (fr 3))) [[1, 2, 3] ++ zeros 5]
-- 30. A buffer of two channels into a destination of two channels.
#guard chk (go 2 8 fun c => do
    let b ← mkBuf c [[1, 2], [3, 4]]
    let (c, s) ← c.createBufferSource
    let c ← c.setBuffer s (some b)
    let c ← c.connect s 0 0 0
    c.start s) [[1, 2] ++ zeros 6, [3, 4] ++ zeros 6]
-- 31. A buffer source modulating a gain: the gain is 0 plus the buffer value, the input is 1.
#guard chk (go 1 8 fun c => do
    let b ← mkBuf c [[1, 2, 3, 4]]
    let (c, s) ← c.createBufferSource
    let c ← c.setBuffer s (some b)
    let (c, g) ← c.createGain
    let (c, k) ← c.createConstantSource
    let c ← c.setValueAtTime g 0 0.0 0.0
    let c ← c.connect k 0 g 0
    let c ← c.connect g 0 0 0
    let c ← c.connectParam s 0 g 0
    let c ← c.start k
    c.start s) [[1, 2, 3, 4] ++ zeros 4]
-- 32. `ended`: true after the buffer has played out and the block has ended; false when the source
-- loops, when it was not started, and before the render.
#guard (match goC 1 8 (fun c => do let (c, s) ← bufTo c; c.start s) with
  | .ok (c, _) => c.ended 1
  | .error _ => false)
#guard (match goC 1 8 (fun c => do let (c, s) ← bufTo c; let c ← c.setLoop s true; c.start s) with
  | .ok (c, _) => !c.ended 1
  | .error _ => false)
#guard (match goC 1 8 (fun c => do let (c, _) ← bufTo c; pure c) with
  | .ok (c, _) => !c.ended 1
  | .error _ => false)
-- 33. `ended` of an oscillator once its stop frame has passed.
#guard (match goC 1 8 (fun c => do
      let (c, s) ← oscTo c 1024.0
      let c ← c.start s
      c.stop s (fr 3)) with
  | .ok (c, _) => c.ended 1
  | .error _ => false)
-- 34. Errors of the buffer source: a second non-null buffer, `start` twice, `stop` before
-- `start`, a negative offset, a non-finite `when`, `createBuffer` out of range.
#guard (match (do
    let c ← OfflineContext.new 1 4 4096.0 4
    let b ← mkBuf c [[1, 2, 3, 4]]
    let (c, s) ← c.createBufferSource
    let c ← c.setBuffer s (some b)
    pure (c, s, b) : Except Error (OfflineContext × Nat × Buffer.AudioBuffer)) with
  | .ok (c, s, b) =>
    isErr (c.setBuffer s (some b) >>= fun _ => pure ()) (.invalidState "buffer was already set to a non-null value") &&
    (c.setBuffer s none).toOption.isSome &&
    isErr (c.stop s >>= fun _ => pure ()) (.invalidState "invalid state") &&
    isErr (c.startBuffer s 0.0 (-1.0) >>= fun _ => pure ()) (.range "negative argument") &&
    isErr (c.start s (0.0 / 0.0) >>= fun _ => pure ()) (.type "when is not finite") &&
    (match c.start s with
     | .ok c2 => isErr (c2.start s >>= fun _ => pure ()) (.invalidState "invalid state") &&
                 isErr (c2.startBuffer s >>= fun _ => pure ()) (.invalidState "invalid state")
     | .error _ => false)
  | .error _ => false)
#guard (match OfflineContext.new 1 4 4096.0 4 with
  | .ok c =>
    isErr (c.createBuffer 0 4 4096.0 >>= fun _ => pure ()) (.notSupported "argument outside the supported range") &&
    isErr (c.createBuffer 1 0 4096.0 >>= fun _ => pure ()) (.notSupported "argument outside the supported range") &&
    isErr (c.createBuffer 1 4 2999.0 >>= fun _ => pure ()) (.notSupported "argument outside the supported range") &&
    (c.createBuffer 1 4 3000.0).toOption.isSome
  | .error _ => false)

/-! The `delayTime` of a delay in a cycle, fed by a node that is numbered after the delay.
Nodes: 0 destination, 1 delay, 2 gain (0, the feedback path), 3 constant source (1) into the delay,
4 constant source (6 frames) into `delayTime`. Order: 4, `delayRead 1`, ..., `delayWrite 1`
(`Graph.paramDstStep`). The delay of 6 frames is above the one-quantum minimum of a delay in a
cycle, so the constant 1 arrives at frame 6. Before `delayTime` went to the reader, the reader
did not see node 4 and the delay was the minimum of 4 frames. -/
private def delayCycle (c : OfflineContext) : Except Error OfflineContext := do
  let (c, d) ← c.createDelay
  let (c, g) ← c.createGain
  let (c, k1) ← c.createConstantSource
  let (c, k2) ← c.createConstantSource
  let c ← c.setValueAtTime g 0 0.0 0.0
  let c ← c.connect d 0 0 0
  let c ← c.connect d 0 g 0
  let c ← c.connect g 0 d 0
  let c ← c.connect k1 0 d 0
  let c ← c.setParamValue k2 0 (fr 6)
  let c ← c.connectParam k2 0 d 0
  let c ← c.start k1
  c.start k2

-- 35. The delay is 6 frames.
#guard chk (go 1 12 delayCycle) [zeros 6 ++ ones 6]
-- 36. The same with the `delayTime` source numbered before the delay.
#guard chk (go 1 12 fun c => do
    let (c, k2) ← c.createConstantSource
    let c ← c.setParamValue k2 0 (fr 6)
    let c ← c.start k2
    let (c, d) ← c.createDelay
    let (c, g) ← c.createGain
    let (c, k1) ← c.createConstantSource
    let c ← c.setValueAtTime g 0 0.0 0.0
    let c ← c.connect d 0 0 0
    let c ← c.connect d 0 g 0
    let c ← c.connect g 0 d 0
    let c ← c.connect k1 0 d 0
    let c ← c.connectParam k2 0 d 0
    c.start k1) [zeros 6 ++ ones 6]

end Tests

end L4Factoidal.WebAudio.Context
