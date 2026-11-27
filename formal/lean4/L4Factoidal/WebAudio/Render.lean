/-
# Web Audio API: rendering one render quantum

Follows https://webaudio.github.io/web-audio-api/ , section "Rendering an Audio Graph" (the
algorithm "process a render quantum"), section 1.6.3 "Computation of Value" of `AudioParam`,
the `AudioNode` channel rules, and `AudioDestinationNode`.

Stage B of https://github.com/danbri/factoidal-core/issues/1169 (audio in Foafnaut); plan:
`docs/designissues/2026-11-26-foafnaut-audio-plan.md`, sections 4 and 9.

## What one quantum does (`renderQuantumWith`)

1. The ordered steps come from `Graph.order` (`Plan.of`): a `DelayNode` in a cycle is split into
   a `delayRead` step and a `delayWrite` step that share one `DelayState`; a muted node outputs
   silence and is not processed.
2. For each step, in order:
   * for each `AudioParam` of the node: the intrinsic values for the quantum (`Automation.fill`,
     a-rate: `n` values; k-rate: the value at the first frame), plus the sum of the connections
     to the parameter, each down-mixed to mono (`Mix.mixInput` with 1 channel, `speakers`;
     k-rate: the first frame of the sum); NaN is replaced by the default value; the result is
     clamped to the nominal range (`paramComputedValue`);
   * for each input: the connections are mixed to `computedNumberOfChannels` (`Mix.computedChannels`,
     `Mix.mixInput`); an input with no connection is silent;
   * the kernel of the node type runs (`runKernel`) and its outputs are stored.
3. The mixed input of the destination node is the output of the quantum (restricted to the
   channel count of the destination and to `n` frames).
4. The current frame advances by `n`.

## Split delay

The `delayRead` step runs the delay kernel on a silent input and keeps only its output. The
kernel reads, for a node in a cycle, at least one render quantum back (`minFrames = n`), so
the samples read are all from earlier quanta and do not depend on the input of this quantum. The
`delayWrite` step runs the kernel on the real input and keeps only the new state. The
`delayTime` parameter of a split delay is used by the `delayRead` step, and `Graph.order` puts
every source of `delayTime` before that step (`Graph.paramDstStep`), so the reader sees all of
them (a source that is on a cycle with the reader is muted and contributes silence). The
`delayWrite` step also computes the parameters; its kernel run does not use them for the new state.

## Node types with their own kernel file

`Oscillator.lean` (`oscProcess`, `OscState`), `Filters.lean` (`biquadProcess`, `BiquadState`) and
`Buffer.lean` (`Buffer.process`, `SourceConfig`, `SourceState`) are called by `runKernel` without
change. Their `AudioParam`s are the rows of `paramSpecs`: OscillatorNode `frequency` (default 440,
-Nyquist to Nyquist) and `detune` (default 0, plus or minus 1200 log2 of the largest binary32
value), both a-rate; BiquadFilterNode `frequency` (350, 0 to Nyquist), `detune`, `Q` (1, plus or
minus the largest binary32), `gain` (0, up to 40 log10 of the largest binary32), all a-rate;
AudioBufferSourceNode `playbackRate` (1) and `detune` (0), both k-rate, both with the nominal range
of the largest binary32 value in each direction (Web Audio API 1.1; WPT `audioparam-nominal-range.html`).

## Proved

`renderQuantum_frame`, `renderQuantum_shape`, `renderQuantum_graph`, `renderQuantum_nodes_size`:
structural statements (counts, sizes, the graph is not changed). Every statement about a sample
value is a `#guard` here or in `Context.lean`.

## Not done

* Control messages are applied by `Context.lean` between quanta, not inside the quantum; for an
  `OfflineAudioContext` this is what the specification describes (the queue is empty while
  rendering).
* `automationRate` of a parameter is a field (`ParamSpec.aRate`) with no setter here.
* The mixing of stored delay samples when the input channel count changes (see `Kernels`).
* The `AudioListener` and `AudioWorklet` messages.
-/
import L4Factoidal.WebAudio.Mix
import L4Factoidal.WebAudio.Automation
import L4Factoidal.WebAudio.Kernels
import L4Factoidal.WebAudio.Graph
import L4Factoidal.WebAudio.Oscillator
import L4Factoidal.WebAudio.Filters
import L4Factoidal.WebAudio.Buffer

namespace L4Factoidal.WebAudio.Render

open L4Factoidal.WebAudio
open L4Factoidal.WebAudio.Kernels (Block mkChan silence getF)

/-! ## Node settings -/

/-- `channelCount`, `channelCountMode` and `channelInterpretation` of a node. -/
structure ChannelSettings where
  count : Nat
  mode : Mix.CountMode
  interp : Mix.Interpretation
  deriving Repr

/-- Default channel settings of each node type (the "Channel count", "ChannelCountMode" and
"ChannelInterpretation" lines of each interface). The destination's count is set by the context. -/
def chanDefaults (destChannels : Nat) : Graph.Kind → ChannelSettings
  | .destination => ⟨destChannels, .explicit, .speakers⟩
  | .stereoPanner => ⟨2, .clampedMax, .speakers⟩
  | .splitter n => ⟨n, .explicit, .discrete⟩
  | .merger _ => ⟨1, .explicit, .speakers⟩
  | _ => ⟨2, .max, .speakers⟩

/-- The largest finite binary32 value: `most-positive-single-float`, the nominal range of a
parameter that has no smaller one. -/
def floatMax : Float := 3.4028234663852886e38

/-- Default value, nominal range and rate of an `AudioParam`. -/
structure ParamSpec where
  defaultValue : Float
  minValue : Float
  maxValue : Float
  /-- `true`: a-rate; `false`: k-rate. -/
  aRate : Bool
  deriving Repr

/-- The state of an `AudioParam`: its constants and its automation event list. -/
structure ParamState where
  spec : ParamSpec
  timeline : Automation.Timeline := ⟨[]⟩

/-- Nominal range limit of `detune`: `1200 * log2 (most-positive-single-float)` (about 153600). -/
def detuneMax : Float := 1200.0 * Float.log2 floatMax

/-- Upper nominal bound of the `gain` of a `BiquadFilterNode`: `40 * log10 (most-positive-single-float)`
evaluated in single precision, as WPT `audioparam-nominal-range.html` states it
(`fround (40 * fround (log10 FLT_MAX))`): `log10 FLT_MAX` is rounded to binary32 first, then the
product is. The result is 1541.273681640625. -/
def biquadGainMax : Float :=
  (40.0 * (Float.log10 floatMax).toFloat32.toFloat).toFloat32.toFloat

#guard biquadGainMax == 1541.273681640625

/-- A parameter of a node type of `Kind.other` (no kernel here). -/
def placeholderParam (d : Float) : ParamSpec := ⟨d, -floatMax, floatMax, true⟩

/-- The normalized built-in sine wave, computed once, at its first use (the FFT of the
normalization; `Oscillator.builtinWaveCached`). -/
def sineWave (_ : Unit := ()) : Oscillator.PeriodicWave := Oscillator.builtinWaveCached .sine

/-- The `AudioParam`s of each node type, in the order of `Graph.Kind.numParams`: Gain `gain`;
ConstantSource `offset`; Delay `delayTime` (nominal range 0 to `maxDelayTime`); StereoPanner `pan`
(-1 to 1); Oscillator, BiquadFilter and AudioBufferSource as in the module comment; all a-rate
except the two of the AudioBufferSource. One table. `sampleRate` gives the Nyquist frequency. -/
def paramSpecs (k : Graph.Kind) (maxDelayTime sampleRate : Float) : Array ParamSpec :=
  match k with
  | .gain => #[⟨1.0, -floatMax, floatMax, true⟩]
  | .constantSource => #[⟨1.0, -floatMax, floatMax, true⟩]
  | .delay => #[⟨0.0, 0.0, maxDelayTime, true⟩]
  | .stereoPanner => #[⟨0.0, -1.0, 1.0, true⟩]
  | .oscillator =>
    #[⟨440.0, -(sampleRate / 2.0), sampleRate / 2.0, true⟩, ⟨0.0, -detuneMax, detuneMax, true⟩]
  | .bufferSource =>
    #[⟨1.0, -floatMax, floatMax, false⟩, ⟨0.0, -floatMax, floatMax, false⟩]
  | .biquad =>
    #[⟨350.0, 0.0, sampleRate / 2.0, true⟩, ⟨0.0, -detuneMax, detuneMax, true⟩,
      ⟨1.0, -floatMax, floatMax, true⟩, ⟨0.0, -floatMax, biquadGainMax, true⟩]
  | .other _ _ _ p => Array.replicate p (placeholderParam 0.0)
  | _ => #[]

/-- The state a node keeps between quanta, by node type. -/
inductive KState where
  /-- Gain, StereoPanner, Splitter, Merger, destination: no state. -/
  | none
  | const (s : Kernels.ConstState)
  /-- The delay line and `maxDelayTime` (the nominal range of `delayTime`). -/
  | delay (s : Kernels.DelayState) (maxDelayTime : Float)
  /-- OscillatorNode (`Oscillator.lean`). -/
  | osc (s : Oscillator.OscState)
  /-- BiquadFilterNode (`Filters.lean`). -/
  | biquad (s : Filters.BiquadState)
  /-- AudioBufferSourceNode (`Buffer.lean`): the attributes read on each block, the playback state,
  and whether `buffer` was set to a non-null value (a second non-null value is
  `InvalidStateError`). -/
  | buf (cfg : Buffer.SourceConfig) (s : Buffer.SourceState) (bufferSet : Bool)

/-- One node: channel settings, `AudioParam`s, kernel state. -/
structure Node where
  chan : ChannelSettings
  params : Array ParamState
  ks : KState

/-- A new node of type `k`. `maxDelayTime` is used by a `delay` only. -/
def Node.new (k : Graph.Kind) (destChannels : Nat) (sampleRate : Float)
    (maxDelayTime : Float := 1.0) (quantum : Nat := 0) : Node :=
  { chan := chanDefaults destChannels k
    params := (paramSpecs k maxDelayTime sampleRate).map (fun s => { spec := s })
    ks := match k with
      | .constantSource => .const {}
      | .delay => .delay (Kernels.DelayState.init maxDelayTime sampleRate 1 0 quantum) maxDelayTime
      | .oscillator => .osc { sampleRate, type := .sine, wave := sineWave () }
      | .bufferSource => .buf {} { sampleRate } false
      | .biquad => .biquad { type := .lowpass, sampleRate }
      | _ => .none }

/-! ## State of one context -/

/-- A context: the graph, one `Node` per `NodeId` of the graph, the sample rate, the current frame
(`[[current frame]]`), the render quantum size `n` (`[[render quantum size]]`), and the id of the
destination node. -/
structure State where
  graph : Graph.Graph
  nodes : Array Node
  sampleRate : Float
  frame : Nat
  quantum : Nat
  dest : Nat

/-- The context with only a destination node (id 0) of `destChannels` channels. -/
def State.init (sampleRate : Float) (destChannels : Nat) (quantum : Nat := 128) : State :=
  { graph := (Graph.Graph.empty.addNode .destination).1
    nodes := #[Node.new .destination destChannels sampleRate]
    sampleRate, frame := 0, quantum, dest := 0 }

/-- Add a node of type `k` to the graph and to the node table; returns the new id. -/
def State.addNode (st : State) (k : Graph.Kind) (maxDelayTime : Float := 1.0) : State × Nat :=
  let (g, id) := st.graph.addNode k
  let dc := (st.nodes[st.dest]?.map (·.chan.count)).getD 1
  ({ st with graph := g, nodes := st.nodes.push (Node.new k dc st.sampleRate maxDelayTime st.quantum) }, id)

/-- Number of channels of the destination (the channel count of the output of a quantum). -/
def destChannels (st : State) : Nat := (st.nodes[st.dest]?.map (·.chan.count)).getD 0

/-! ## The plan: the order of the steps, computed once per graph -/

/-- The ordered steps, the muted nodes, and which nodes are delays in a cycle. -/
structure Plan where
  steps : List Graph.Step
  muted : List Nat
  cycleDelay : Array Bool

/-- The plan of a graph (`Graph.order`). -/
def Plan.of (g : Graph.Graph) : Plan :=
  let o := Graph.order g
  { steps := o.steps, muted := o.muted
    cycleDelay := (Array.range g.kinds.size).map (fun i => Graph.isCycleDelay g i) }

/-! ## Values of one quantum -/

/-- `paramComputedValue`: NaN is replaced by the default value, then the value is clamped to the
nominal range. -/
def finalValue (s : ParamSpec) (x : Float) : Float :=
  let y := if x.isNaN then s.defaultValue else x
  let z := if y < s.minValue then s.minValue else if y > s.maxValue then s.maxValue else y
  -- the computed value of a parameter is a binary32 value (WPT k-rate-audiobuffersource-connections.html
  -- compares an automation with a connected signal exactly)
  z.toFloat32.toFloat

/-- The block of output `out` of node `src`, or one mono channel of silence when the node has not
produced it (a muted node, or a node that comes later in the order). -/
def srcBlock (outs : Array (Array Block)) (n src out : Nat) : Block :=
  (outs.getD src #[]).getD out (silence 1 n)

/-- The values of a parameter for one quantum, as the kernels read them: `n` values if a-rate, one
value if k-rate. `inputSum` is the sum of the parameter's connections mixed down to mono (empty
when nothing is connected). -/
def paramValues (n : Nat) (sampleRate : Float) (frame : Nat) (p : ParamState)
    (inputSum : FloatArray) : FloatArray :=
  let cnt := if p.spec.aRate then n else 1
  match (if inputSum.size == 0 then Automation.fillConst p.timeline p.spec.defaultValue frame sampleRate
         else none) with
  -- constant over the quantum and nothing connected: one value (every kernel reads a one-value
  -- array as constant over the block, `Kernels.paramAt`), not `cnt` equal ones
  | some v => ⟨#[finalValue p.spec (v + Kernels.zeroF)]⟩
  | none =>
    let intr := Automation.fill p.timeline p.spec.defaultValue frame cnt sampleRate
    ⟨intr.mapIdx fun i v => finalValue p.spec (v + getF inputSum i)⟩

/-- Accumulator over the steps of one quantum. -/
structure Acc where
  nodes : Array Node
  outs : Array (Array Block)
  destIn : Block

/-- The values of the parameters of node `id` at this point of the quantum. -/
def nodeParams (st : State) (acc : Acc) (id : Nat) (node : Node) : Array FloatArray :=
  let n := st.quantum
  node.params.mapIdx fun j p =>
    let conns := (st.graph.paramEdges.filter (fun e => e.dst == id && e.param == j)).map
      (fun e => srcBlock acc.outs n e.src e.out)
    let sum : FloatArray :=
      if conns.isEmpty then ⟨#[]⟩ else (Mix.mixInput .speakers 1 conns n).getD 0 ⟨#[]⟩
    paramValues n st.sampleRate st.frame p sum

/-- The mixed input blocks of node `id`: one block per input, each mixed to the node's
`computedNumberOfChannels`. -/
def nodeInputs (st : State) (acc : Acc) (id : Nat) (node : Node) (numInputs : Nat) :
    Array Block :=
  let n := st.quantum
  Array.ofFn (n := numInputs) fun j =>
    let conns := (st.graph.edges.filter (fun e => e.dst == id && e.inp == j.1)).map
      (fun e => srcBlock acc.outs n e.src e.out)
    let toCh := Mix.computedChannels node.chan.mode node.chan.count (conns.map (·.size))
    Mix.mixInput node.chan.interp toCh conns n

/-- Run the kernel of a node type. `cyc`: the node is a delay in a cycle, so its minimum delay is
one render quantum. Returns the new state and the output blocks (one per output). -/
def runKernel (n frame : Nat) (k : Graph.Kind) (cyc : Bool) (interp : Mix.Interpretation)
    (ks : KState)
    (inputs : Array Block) (params : Array FloatArray) : KState × Array Block :=
  match k, ks with
  | .gain, _ => (ks, (Kernels.gainProcess n () inputs params).2)
  | .constantSource, .const s =>
    let r := Kernels.constProcess n { s with frame := frame } inputs params
    (.const r.1, r.2)
  | .delay, .delay s md =>
    let r := Kernels.delayProcess n { s with minFrames := if cyc then n else 0, interp } inputs params
    (.delay r.1 md, r.2)
  | .stereoPanner, _ => (ks, (Kernels.panProcess n () inputs params).2)
  | .splitter m, _ => (ks, (Kernels.splitProcess n m inputs params).2)
  | .merger m, _ => (ks, (Kernels.mergeProcess n m inputs params).2)
  | .destination, _ => (ks, #[])
  | .oscillator, .osc s =>
    let r := Oscillator.oscProcess n { s with frame := frame } inputs params
    (.osc r.1, r.2)
  | .biquad, .biquad s =>
    let r := Filters.biquadProcess n s inputs params
    (.biquad r.1, r.2)
  | .bufferSource, .buf cfg s set =>
    let r := Buffer.process n cfg { s with frame := frame } inputs params
    -- A node that has not played in this quantum is not actively processing: one channel of
    -- silence (Web Audio API 1.1, "actively processing"; WPT audiobuffersource-output-channel-count).
    (.buf cfg r.1 set, if r.1.started then r.2 else #[silence 1 n])
  -- A node type with no kernel (`Kind.other`): one mono channel of silence per output.
  | _, _ => (ks, Array.replicate k.numOutputs (silence 1 n))

/-- The output of a node is binary32 data: each sample is rounded to the nearest binary32 value, so
that an overflow is an infinity at the node that overflows (and `inf - inf` is NaN where two such
outputs meet), as in a single-precision engine. The kernels compute in binary64. Specification:
"AudioBuffer ... 32-bit floating-point"; WPT `nan-param.html` needs this. -/
def roundOut (bs : Array Block) : Array Block :=
  bs.map fun b => b.map fun c => mkChan c.size fun i => (getF c i).toFloat32.toFloat

/-- Process one step of the ordered list. -/
def runStep (st : State) (pl : Plan) (acc : Acc) : Graph.Step → Acc
  | .node id =>
    match acc.nodes[id]?, st.graph.kinds[id]? with
    | some node, some k =>
      let inputs := nodeInputs st acc id node k.numInputs
      let params := nodeParams st acc id node
      let cyc := pl.cycleDelay.getD id false
      let r := runKernel st.quantum st.frame k cyc node.chan.interp node.ks inputs params
      let acc' := if id == st.dest then { acc with destIn := inputs.getD 0 #[] } else acc
      { acc' with nodes := acc'.nodes.set! id { node with ks := r.1 }
                  outs := acc'.outs.set! id (roundOut r.2) }
    | _, _ => acc
  | .delayRead id =>
    match acc.nodes[id]?, st.graph.kinds[id]? with
    | some node, some k =>
      match node.ks with
      | .delay s _ =>
        let silent : Array Block := #[silence s.bufs.size st.quantum]
        let r := runKernel st.quantum st.frame k true node.chan.interp node.ks silent (nodeParams st acc id node)
        { acc with outs := acc.outs.set! id (roundOut r.2) }
      | _ => acc
    | _, _ => acc
  | .delayWrite id =>
    match acc.nodes[id]?, st.graph.kinds[id]? with
    | some node, some k =>
      let inputs := nodeInputs st acc id node k.numInputs
      let r := runKernel st.quantum st.frame k true node.chan.interp node.ks inputs (nodeParams st acc id node)
      { acc with nodes := acc.nodes.set! id { node with ks := r.1 } }
    | _, _ => acc

/-- A block of exactly `channels` channels of `n` frames: channel `c` frame `i` is the source's
value, or 0 where the source has none. -/
def normalize (channels n : Nat) (b : Block) : Block :=
  Array.ofFn (n := channels) fun c => mkChan n (fun i => getF (b.getD c.1 ⟨#[]⟩) i)

/-- One render quantum with a given plan: returns the new state and the output of the
destination (`destChannels` channels of `n` frames). -/
def renderQuantumWith (st : State) (pl : Plan) : State × Block :=
  let outs0 : Array (Array Block) := (Array.range st.graph.kinds.size).map fun i =>
    if pl.muted.contains i then
      Array.replicate (st.graph.kinds.getD i .destination).numOutputs (silence 1 st.quantum)
    else #[]
  let acc := pl.steps.foldl (runStep st pl) { nodes := st.nodes, outs := outs0, destIn := #[] }
  ({ st with nodes := acc.nodes, frame := st.frame + st.quantum },
   normalize (destChannels st) st.quantum acc.destIn)

/-- One render quantum of "Rendering an Audio Graph". -/
def renderQuantum (st : State) : State × Block := renderQuantumWith st (Plan.of st.graph)

/-! ## Theorems -/

/-- Says: rendering one quantum advances the current frame by the render quantum size.
Does not say: anything about the samples. -/
theorem renderQuantum_frame (st : State) :
    (renderQuantum st).1.frame = st.frame + st.quantum := rfl

/-- Says: the output of a quantum has exactly the destination's channel count, and each channel
has exactly `n` frames. Does not say: which values the frames hold. -/
theorem renderQuantum_shape (st : State) :
    (renderQuantum st).2.size = destChannels st ∧
    ∀ c ∈ (renderQuantum st).2, c.size = st.quantum := by
  unfold renderQuantum renderQuantumWith normalize
  constructor
  · simp
  · intro c hc
    simp only [Array.mem_ofFn] at hc
    obtain ⟨j, rfl⟩ := hc
    exact Kernels.mkChan_size _ _

/-- Says: rendering does not change the graph, the sample rate, the quantum size or the
destination id. Does not say: that the node states are unchanged (the kernels change them). -/
theorem renderQuantum_graph (st : State) :
    (renderQuantum st).1.graph = st.graph ∧ (renderQuantum st).1.sampleRate = st.sampleRate ∧
    (renderQuantum st).1.quantum = st.quantum ∧ (renderQuantum st).1.dest = st.dest :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem runStep_nodes_size (st : State) (pl : Plan) (acc : Acc) (s : Graph.Step) :
    (runStep st pl acc s).nodes.size = acc.nodes.size := by
  cases s with
  | node id =>
    simp only [runStep]
    split
    · simp only []
      split <;> simp [Array.set!]
    · rfl
  | delayRead id =>
    simp only [runStep]
    split
    · split <;> rfl
    · rfl
  | delayWrite id =>
    simp only [runStep]
    split
    · simp [Array.set!]
    · rfl

theorem foldl_runStep_nodes_size (st : State) (pl : Plan) (steps : List Graph.Step) (acc : Acc) :
    (steps.foldl (runStep st pl) acc).nodes.size = acc.nodes.size := by
  induction steps generalizing acc with
  | nil => rfl
  | cons s rest ih => simp only [List.foldl_cons]; rw [ih, runStep_nodes_size]

/-- Says: rendering keeps the number of node records. Does not say: that the table agrees with
the graph (that is the invariant of the functions that add nodes). -/
theorem renderQuantum_nodes_size (st : State) :
    (renderQuantum st).1.nodes.size = st.nodes.size := by
  unfold renderQuantum renderQuantumWith
  exact foldl_runStep_nodes_size _ _ _ _

/-! ## Tests -/

section Tests

private def L (a : FloatArray) : List Float := a.data.toList
private def near (x y : Float) : Bool := (x - y).abs < 1e-9
private def approxL (xs ys : List Float) : Bool :=
  xs.length == ys.length && (List.zip xs ys).all fun (x, y) => near x y
private def approxB (b : Block) (cs : List (List Float)) : Bool :=
  b.size == cs.length && (List.zip b.toList cs).all fun (x, y) => approxL (L x) y

/-- Connect a node and add timeline events directly (the checked versions are in `Context.lean`). -/
private def conn (st : State) (a o b i : Nat) : State :=
  match Graph.connect st.graph a o b i with
  | Except.ok g => { st with graph := g }
  | Except.error _ => st

-- A ConstantSource (offset 1) started at frame 0, into the destination of 1 channel, quantum 4.
private def cs1 : State :=
  let st := State.init 8.0 1 4
  let (st, c) := st.addNode .constantSource
  let st := conn st c 0 0 0
  { st with nodes := st.nodes.modify c fun nd => { nd with ks := .const { startFrame := some 0 } } }

#guard approxB (renderQuantum cs1).2 [[1, 1, 1, 1]]
#guard (renderQuantum cs1).1.frame == 4
#guard approxB (renderQuantum (renderQuantum cs1).1).2 [[1, 1, 1, 1]]
-- Not started: silence.
#guard approxB (renderQuantum { cs1 with nodes := cs1.nodes.modify 1 fun nd => { nd with ks := .const {} } }).2
  [[0, 0, 0, 0]]

end Tests

end L4Factoidal.WebAudio.Render
