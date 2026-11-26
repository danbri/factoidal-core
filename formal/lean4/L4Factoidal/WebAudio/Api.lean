/-
L4Factoidal.WebAudio.Api: the Web Audio operations of the `web_api` import, with the state that
lives between script turns (stage B of https://github.com/danbri/factoidal-core/issues/1169;
design: docs/designissues/2026-11-26-foafnaut-audio-plan.md, section 12).

## Op numbers

The plan named ops 170 to 189. Ops 170, 171 and 172 of `WasmVM/Hosts/WebApi.lean` are the
layout observers (`Rendering.Observe`, `DOM.PiAttributes`), so these ops are **173 to 196**
(173 to 189: contexts, nodes, rendering; 190 to 196: real-time contexts and decoding, step D2 of
the plan). Routing: `173 ≤ code < 200` (197 to 199 answer -2).

## Argument and answer conventions

The arguments are the fields of the import's argument block (`Array ByteArray`).

  * A count, an id or a flag is decimal text (`"0"`, `"12"`). An absent optional number is the
    empty field `""`.
  * A real number (IDL `float` or `double`) is the 8 bytes of a binary64, little-endian. The page
    passes the value it converted as Web IDL says. An absent optional real is the empty field.
  * Audio data (buffer samples, `Float32Array` arguments) is binary32 little-endian, channel by
    channel. An array that is not given is the one byte `"-"` where an op says so.
  * A name (node kind, method, attribute, enum value) is UTF-8 text.
  * An answer is bytes. A node or context id is decimal text. Reals in an answer are 8-byte
    little-endian binary64 or binary32, as each op says. `u32` is 4 bytes little-endian.
  * The context is field 0 of every op from 176 on. Node 0 is the destination.
  * A failed op leaves the state as it was.

## Error codes (a negative answer)

| code | name | when |
|---|---|---|
| -20 | `TypeError` | a field that is not what the op reads; a non-finite number; a node or context that does not exist |
| -21 | `RangeError` | a negative time |
| -23 | `NotSupportedError` | a value outside what the specification supports |
| -25 | `InvalidAccessError` | a connection that does not exist; unequal array lengths |
| -28 | `IndexSizeError` | an output, input or channel index out of range |
| -29 | `InvalidStateError` | an operation the node's state forbids |
| -30 | `EncodingError` | reserved for `decodeAudioData` (stage C); no op here answers it |

-2 is "not an op of this engine" (`WebApi`). Codes -20, -21, -23 and -25 are those of the header
of `WebApi.lean`; -28 to -30 are new.

## The ops

  * 173 `interface(name)`: the interface `name` of `Idl` as tab-separated lines: `i NAME PARENT EXT`;
    `k MINARGS SIGS` (constructor); `a NAME READONLY(1/0) TYPE`; `o NAME MINARGS SIGS`;
    `s NAME MINARGS SIGS` (static); `x TEXT` (other members). `name` = "" answers the names of all
    interfaces, one per line. -20 for an unknown name.
  * 174 `idl(kind, name)`: `kind` "enum": the values, one per line; "dict": a line `p PARENT`, then
    `m NAME TYPE REQUIRED(1/0) DEFAULT`, tab-separated; "callback": `r RETURN ARGS`. -20 for an
    unknown name or kind.
  * 175 `newContext(numberOfChannels, length, sampleRate, [renderQuantumSize])`:
    `OfflineContext.new`; answers the new context's id. -23 for what the constructor refuses, and
    for `numberOfChannels * length` above 2^25 (a bound of this engine).
  * 176 `createNode(ctx, kind, [option])`: `kind` is `gain`, `constantSource`, `stereoPanner`,
    `oscillator`, `biquadFilter`, `bufferSource`, `delay` (option: `maxDelayTime`, real),
    `channelSplitter` (option: `numberOfOutputs`), `channelMerger` (option: `numberOfInputs`).
    Answers `"ID NUMINPUTS NUMOUTPUTS NUMPARAMS"`. -23 `maxDelayTime` out of range; -28 splitter
    or merger count outside 1 to 32; -20 an unknown kind; -23 more than 65536 nodes.
  * 177 `connect(ctx, src, output, dst, input, toParam)`: `toParam` "1": `input` is the number of
    the `AudioParam` of `dst`. Answers "". -28 index; -20 node.
  * 178 `disconnect(ctx, src, dst, output, input, toParam)`: `dst`, `output`, `input` may be "";
    the overload is chosen by which are given (`disconnect()`, `disconnect(output)`,
    `disconnect(node[, output[, input]])`, `disconnect(param[, output])`: for a parameter, `input`
    is the parameter number). -25 no such connection; -28 index.
  * 179 `paramCall(ctx, node, param, method, args...)`: `method` is `setValueAtTime(value, time)`,
    `linearRampToValueAtTime(value, time)`, `exponentialRampToValueAtTime(value, time)`,
    `setTargetAtTime(target, start, timeConstant)`, `setValue(value)` (the `value` setter),
    `setValueCurveAtTime(values, startTime, duration)` (`values`: binary32 array, the times
    doubles: -20 a non-finite value or time, -29 fewer than 2 values (as `Automation.validate`
    decides; the coordinator's brief said TypeError), -21 a negative start or a duration that is
    not above 0, -23 an overlap), `cancelAndHoldAtTime(cancelTime)` (double: -20 non-finite, -21
    negative), `cancelScheduledValues(time)` or `setAutomationRate(name)` ("a-rate" or "k-rate"; the
    parameters of an `AudioBufferSourceNode` are fixed k-rate: -29 for "a-rate"). The reals are
    8-byte doubles. Errors: -20 non-finite; -21 RangeError; -23 NotSupportedError; -29
    InvalidStateError (automation rules of `Automation.insert`); -28 no such parameter.
  * 180 `paramInfo(ctx, node, param)`: 4 doubles (`value`, `defaultValue`, `minValue`,
    `maxValue`) then one byte: 1 a-rate, 0 k-rate. `value` is the automation value at the current
    time.
  * 181 `start(ctx, node, [when], [offset], [duration])`: reals; an absent `when` is 0.
    `offset` and `duration` are for an `AudioBufferSourceNode`. -29 started before; -21; -20.
  * 182 `stop(ctx, node, [when])`: -29 not started; -21; -20.
  * 183 `setAttr(ctx, node, name, value)`: `type` (oscillator: `sine`, `square`, `sawtooth`,
    `triangle`, `custom`; `custom` answers -29; biquad: the eight filter types), `loop` ("0" or
    "1"), `loopStart` and `loopEnd` (real), `channelCount` (decimal), `channelCountMode`,
    `channelInterpretation`. Channel rules: a count of 0 or above 32 is -23; a `ChannelMergerNode`,
    a `ChannelSplitterNode` and the offline destination refuse a change of count, mode or
    interpretation (-29, except where the value is the one it has); a `StereoPanner` count above
    2 and the mode `max` are -23. An unknown name or enum value is -20.
  * 184 `setBuffer(ctx, node, channels, length, sampleRate, data)`: the `buffer` setter of an
    `AudioBufferSourceNode`; `channels` "" sets null; `data` is `channels * length` binary32
    values. -29 when a non-null buffer was set before; -20 when the byte count does not match;
    -23 buffer values out of range (`AudioBuffer.create`).
  * 185 `setPeriodicWave(ctx, node, real, imag, disableNormalization)`: `setPeriodicWave` of an
    oscillator; `real` and `imag` are binary32 arrays or "-". -28, -20 as `createPeriodicWave`.
  * 186 `check(kind, args...)`: `kind` "buffer" (`channels`, `length`, `sampleRate`: the
    `createBuffer` checks, -23) or "wave" (`real`, `imag`, `disableNormalization`: the
    `createPeriodicWave` checks, -28, -20). Answers "".
  * 187 `startRendering(ctx)`: renders the whole length. Answer: `u32` channels, `u32` length,
    the samples as binary32 channel by channel (`channels * length` values), `u32` count K, then K
    `u32` ids of the source nodes (constant, oscillator, buffer source) that have ended, in
    ascending node id. -29 when it ran before.
  * 188 `frequencyResponse(ctx, node, frequencyHz, magLength, phaseLength)`: `frequencyHz` is a
    binary32 array. Answer: `magLength` binary32 values then `phaseLength` values. -25 when a
    length differs from that of `frequencyHz`; -29 for a node that is not a `BiquadFilterNode`.
  * 189 `info(ctx)`: the double `sampleRate`, then `u32` length, channels, current frame, render
    quantum size, number of nodes, and one byte 1 when `startRendering` has run.

Real-time contexts (plan section 13). `contexts` holds the graph state of every context, offline
and real-time, so ops 176 to 188 work on both (187 on a real-time context answers -29). A
real-time context also has a `Realtime` record in `realtime`: its state, the outbox of the
messages for its rendering side, its unconfirmed control calls, its events for the page and the
last report of the rendering side. The IO layer (step D3) moves the outboxes (`takeOutbox`),
merges the reports (`applyReport`), takes decode jobs and wakeups; this file has no IO.

  * 190 `newAudioContext(latencyHint, sampleRate, callback)`: `latencyHint` is `interactive`,
    `balanced`, `playback` (else -20) or an 8-byte double of seconds (non-finite or negative: -20);
    `sampleRate` "" is the device rate, else a double from 3000 to 768000 (else -23); `callback` is
    the page callback handle for events (decimal). -23 when `device` is `none` (no audio output)
    or when 16 real-time contexts that are not closed exist. Answers `"ID RATE CHANNELS STATE"`:
    the id, the rate, the device's channel count (`maxChannelCount`; the destination has 2) and the
    state (`suspended`, `running`, `closed`). The state is `running` when `autoplay` or `activated`.
    The first message of the outbox is `(190, [ID, RATE (binary64), CHANNELS, TARGET])`, the target
    in frames (1024, 2048, 4096 for the hints; `ceil(seconds * rate)` from 256 to 16384).
  * 191 `control(ctx, verb)`: `resume`, `suspend`, `close` (else -20); -20 for a context that is
    not real-time; -29 when the context is closed. Answers the call id (decimal) and appends
    `(191, [ctx, verb, callId])` to the outbox; the promise resolves when an event of kind 3 (or
    rejects: kind 4) names the call id. A `resume` before `autoplay` or `activated` waits in
    `pendingResume`; op 196 releases it.
  * 192 `time(ctx)`: doubles `currentTime`, `baseLatency`, `outputLatency`, one state byte (0
    suspended, 1 running, 2 closed), doubles `contextTime` and `performanceTime` (of
    `getOutputTimestamp()`; the page-clock ms of the last report, 0 before the first).
  * 193 `events(ctx)`: `u32` count, then each event as a kind byte and a `u32` value; clears them.
    Kind 1 source ended (node id), 2 state changed (0, 1, 2 as above), 3 control call resolved
    (call id), 4 control call rejected (call id).
  * 194 `decodeAudioData(ctx, bytes, callback)`: any context; queues a job; answers the job id.
  * 195 `decodeResult(job)`: `u32` channels, `u32` length, the rate (double), the samples as
    binary32 channel by channel; or the error the decoder gave (-30, -23). The job is removed
    when the result is given, and also when it is an error (so 195 is the one op that changes the
    state while it answers an error). -29 while the job is pending; -20 for no such job.
  * 196 `activate()`: the page's sticky activation; releases the pending `resume` calls.

No op changes a context other than the one it names (`withCtx_other`), and an op that fails
changes nothing (`op_error_state`; op 195 with a stored error result excepted).
-/
import L4Factoidal.WebAudio.Context
import L4Factoidal.WebAudio.Idl
import Std.Data.HashMap

namespace L4Factoidal.WebAudio.Api

open L4Factoidal.WebAudio

/-- Contexts of one session. -/
def maxContexts : Nat := 256

/-- Largest `numberOfChannels * length` of a context or buffer: the rendered result is that many
binary32 values. -/
def maxSamples : Nat := 33554432

/-- Largest number of nodes of one context. -/
def maxNodes : Nat := 65536

/-- The state of a real-time context (IDL `AudioContextState`). -/
inductive RtState where
  | suspended | running | closed
  deriving DecidableEq, Inhabited, Repr

def RtState.code : RtState → Nat
  | .suspended => 0 | .running => 1 | .closed => 2

def RtState.text : RtState → String
  | .suspended => "suspended" | .running => "running" | .closed => "closed"

/-- What the control side keeps of a real-time context besides its graph state (which is in
`State.contexts`). Plan section 13.1. -/
structure Realtime where
  state : RtState := .suspended
  /-- The device's channel count: `maxChannelCount`. -/
  maxChannels : Nat := 2
  /-- Frames the rendering side keeps ahead of the output (plan 13.4). -/
  target : Nat := 1024
  /-- The page callback handle that takes the events. -/
  callback : Nat := 0
  /-- Control messages (op code, fields) for the rendering side, in order. -/
  outbox : Array (Nat × Array ByteArray) := #[]
  /-- Control calls (call id, verb) not yet confirmed or rejected. -/
  calls : Array (Nat × String) := #[]
  /-- Call ids of `resume` calls waiting for activation. -/
  pendingResume : Array Nat := #[]
  /-- Events for the page: kind 1 source ended (node), 2 state changed, 3 call resolved, 4 call
  rejected. -/
  events : Array (UInt8 × Nat) := #[]
  framesRendered : Nat := 0
  framesPlayed : Nat := 0
  underruns : Nat := 0
  latencyFrames : Nat := 0
  /-- The page-clock time of the last report, in ms. -/
  reportMs : Float := 0.0
  deriving Inhabited

/-- What a rendering side tells the control side (plan 13.3). -/
structure Report where
  framesRendered : Nat := 0
  framesPlayed : Nat := 0
  underruns : Nat := 0
  latencyFrames : Nat := 0
  timeMs : Float := 0.0
  /-- Ids of the source nodes that ended. -/
  ended : Array Nat := #[]
  /-- State changes the rendering side made, in order. -/
  stateChanges : Array RtState := #[]
  /-- Control calls it carried out. -/
  confirmed : Array Nat := #[]
  /-- Control calls it refused. -/
  rejected : Array Nat := #[]
  deriving Inhabited

/-- A `decodeAudioData` job. `result` is (channels, length, sample rate, samples as binary32
channel by channel) or the error code. -/
structure DecodeJob where
  rate : Float
  bytes : ByteArray
  callback : Nat
  taken : Bool := false
  result : Option (Except Int (Nat × Nat × Float × ByteArray)) := none

instance : Inhabited DecodeJob := ⟨{ rate := 0.0, bytes := ByteArray.empty, callback := 0 }⟩

/-- What the session keeps for Web Audio between calls. -/
structure State where
  contexts : Std.HashMap Nat Context.OfflineContext := {}
  next : Nat := 1
  /-- The real-time contexts (their ids are also in `contexts`). -/
  realtime : Std.HashMap Nat Realtime := {}
  /-- The output's preferred sample rate and channel count, set by the engine; `none`: no audio
  output (op 190 answers -23). -/
  device : Option (Float × Nat) := none
  /-- True: no activation is needed (the WPT runner and tests). -/
  autoplay : Bool := false
  /-- The page's sticky activation (op 196). -/
  activated : Bool := false
  nextCall : Nat := 1
  decodeJobs : Std.HashMap Nat DecodeJob := {}
  nextJob : Nat := 1
  /-- Page callback handles the engine queues as tasks (`takeWakeups`). -/
  wakeups : Array Nat := #[]
  deriving Inhabited

/-! ## Error codes -/

def errType : Int := -20
def errRange : Int := -21
def errNotSupported : Int := -23
def errInvalidAccess : Int := -25
def errIndexSize : Int := -28
def errInvalidState : Int := -29
def errEncoding : Int := -30

/-- The code of an error of the engine. A node that does not exist cannot occur through the page's
objects; it answers `TypeError`. -/
def codeOf : Context.Error → Int
  | .notSupported _ => errNotSupported
  | .indexSize => errIndexSize
  | .invalidAccess => errInvalidAccess
  | .invalidState _ => errInvalidState
  | .range _ => errRange
  | .type _ => errType
  | .unknownNode => errType

def lift {α : Type} (r : Except Context.Error α) : Except Int α := r.mapError codeOf

/-! ## Reading arguments and writing answers -/

def strArg (fs : Array ByteArray) (i : Nat) : String :=
  match fs[i]? with
  | some b => (String.fromUTF8? b).getD ""
  | none => ""

def natArg (fs : Array ByteArray) (i : Nat) : Except Int Nat :=
  match (strArg fs i).toNat? with | some n => .ok n | none => .error errType

def optNatArg (fs : Array ByteArray) (i : Nat) : Except Int (Option Nat) :=
  if strArg fs i == "" then .ok none else (natArg fs i).map some

/-- Bytes `i` to `i + 3` of `b` as a little-endian `UInt32` (0 past the end). -/
def u32At (b : ByteArray) (i : Nat) : UInt32 :=
  (b.get! i).toUInt32 ||| ((b.get! (i + 1)).toUInt32 <<< 8) |||
  ((b.get! (i + 2)).toUInt32 <<< 16) ||| ((b.get! (i + 3)).toUInt32 <<< 24)

def u64At (b : ByteArray) (i : Nat) : UInt64 :=
  (u32At b i).toUInt64 ||| ((u32At b (i + 4)).toUInt64 <<< 32)

def u32le (n : Nat) : ByteArray :=
  let v := n.toUInt32
  ⟨#[v.toUInt8, (v >>> 8).toUInt8, (v >>> 16).toUInt8, (v >>> 24).toUInt8]⟩

def f32le (x : Float) : ByteArray := u32le x.toFloat32.toBits.toNat

def f64le (x : Float) : ByteArray :=
  let v := x.toBits
  ⟨(Array.range 8).map fun i => (v >>> (8 * i).toUInt64).toUInt8⟩

/-- A real: 8 bytes, little-endian. -/
def f64Arg (fs : Array ByteArray) (i : Nat) : Except Int Float :=
  match fs[i]? with
  | some b => if b.size == 8 then .ok (Float.ofBits (u64At b 0)) else .error errType
  | none => .error errType

def optF64Arg (fs : Array ByteArray) (i : Nat) : Except Int (Option Float) :=
  match fs[i]? with
  | none => .ok none
  | some b => if b.size == 0 then .ok none else (f64Arg fs i).map some

/-- A binary32 array. -/
def f32s (b : ByteArray) : Except Int FloatArray :=
  if b.size % 4 != 0 then .error errType
  else .ok ⟨(Array.range (b.size / 4)).map fun i => (Float32.ofBits (u32At b (4 * i))).toFloat⟩

def f32sBytes (a : FloatArray) : ByteArray :=
  a.data.foldl (fun acc x => acc ++ f32le x) ByteArray.empty

def optF32s (fs : Array ByteArray) (i : Nat) : Except Int (Option FloatArray) :=
  match fs[i]? with
  | some b => if b == "-".toUTF8 then .ok none else (f32s b).map some
  | none => .ok none

def ofStr (s : String) : ByteArray := s.toUTF8

/-! ## Contexts -/

/-- Run `f` on the context named by field 0 and store the context it returns. The only entry of
`contexts` that changes is that one. -/
def withCtx (s : State) (fs : Array ByteArray)
    (f : Context.OfflineContext → Except Int (Context.OfflineContext × ByteArray)) :
    Except Int (State × ByteArray) := do
  let id ← natArg fs 0
  match s.contexts[id]? with
  | none => .error errType
  | some c =>
    let (c', out) ← f c
    pure ({ s with contexts := s.contexts.insert id c' }, out)

/-- Says: the contexts other than the one named by field 0 are the same after `withCtx`. Does not
say: anything about the named context. -/
theorem withCtx_other (s s' : State) (fs : Array ByteArray) (out : ByteArray) (id' : Nat)
    (f : Context.OfflineContext → Except Int (Context.OfflineContext × ByteArray))
    (h : withCtx s fs f = .ok (s', out)) (hid : natArg fs 0 ≠ .ok id') :
    s'.contexts[id']? = s.contexts[id']? := by
  unfold withCtx at h
  generalize hn : natArg fs 0 = n at h hid
  match n, h, hid with
  | .error _, h, _ => simp [bind, Except.bind] at h
  | .ok id, h, hid =>
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · rename_i c hc
      split at h
      · simp at h
      · rename_i r hr
        simp [pure, Except.pure] at h
        obtain ⟨rfl, -⟩ := h
        have hne : id ≠ id' := fun e => hid (by rw [e])
        simp [Std.HashMap.getElem?_insert, hne]

/-- `s` with the context stored under `id` replaced by `c`. -/
def setCtx (s : State) (id : Nat) (c : Context.OfflineContext) : State :=
  { s with contexts := s.contexts.insert id c }

def nodeKind? (c : Context.OfflineContext) (id : Nat) : Option Graph.Kind := c.state.graph.kinds[id]?

/-! ## 173, 174: the interface text -/

def tab : String := "\t"

def ifaceText (i : Idl.Iface) : String :=
  let l1 := [s!"i\t{i.name}\t{i.parent}\t{i.ext}"]
  let l2 := (match i.ctor with | some o => [s!"k\t{o.minArgs}\t{o.sigs}"] | none => [])
  let l3 := i.attrs.map fun a => s!"a\t{a.name}\t{if a.readOnly then 1 else 0}\t{a.type}"
  let l4 := i.ops.map fun o => s!"o\t{o.name}\t{o.minArgs}\t{o.sigs}"
  let l5 := i.statics.map fun o => s!"s\t{o.name}\t{o.minArgs}\t{o.sigs}"
  let l6 := i.other.map fun x => s!"x\t{x}"
  "\n".intercalate (l1 ++ l2 ++ l3 ++ l4 ++ l5 ++ l6)

def interfaceOp (fs : Array ByteArray) : Except Int ByteArray :=
  let n := strArg fs 0
  if n == "" then .ok (ofStr ("\n".intercalate (Idl.interfaces.map (·.name))))
  else match Idl.findInterface n with
    | some i => .ok (ofStr (ifaceText i))
    | none => .error errType

def idlOp (fs : Array ByteArray) : Except Int ByteArray :=
  let n := strArg fs 1
  match strArg fs 0 with
  | "enum" =>
    match Idl.enumValues n with
    | some vs => .ok (ofStr ("\n".intercalate vs))
    | none => .error errType
  | "dict" =>
    match Idl.findDict n with
    | some d =>
      .ok (ofStr ("\n".intercalate
        (s!"p\t{d.parent}" :: d.members.map fun m =>
          s!"m\t{m.name}\t{m.type}\t{if m.required then 1 else 0}\t{m.default}")))
    | none => .error errType
  | "callback" =>
    match Idl.callbacks.find? (·.name == n) with
    | some c => .ok (ofStr s!"r\t{c.ret}\t{c.args}")
    | none => .error errType
  | _ => .error errType

/-! ## 175, 176: contexts and nodes -/

def newContextOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) := do
  let nch ← natArg fs 0
  let len ← natArg fs 1
  let sr ← f64Arg fs 2
  let q ← optNatArg fs 3
  if nch * len > maxSamples || s.contexts.size ≥ maxContexts then .error errNotSupported
  else
    let c ← lift (Context.OfflineContext.new nch len sr (q.getD 128))
    let id := s.next
    pure ({ s with contexts := s.contexts.insert id c, next := id + 1 }, ofStr (toString id))

def createNodeOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  withCtx s fs fun c => do
    if c.state.nodes.size ≥ maxNodes then throw errNotSupported
    let r ← match strArg fs 1 with
      | "gain" => lift c.createGain
      | "constantSource" => lift c.createConstantSource
      | "stereoPanner" => lift c.createStereoPanner
      | "oscillator" => lift c.createOscillator
      | "biquadFilter" => lift c.createBiquadFilter
      | "bufferSource" => lift c.createBufferSource
      | "delay" => do
        let m ← optF64Arg fs 2
        lift (c.createDelay (m.getD 1.0))
      | "channelSplitter" => do
        let n ← optNatArg fs 2
        lift (c.createChannelSplitter (n.getD 6))
      | "channelMerger" => do
        let n ← optNatArg fs 2
        lift (c.createChannelMerger (n.getD 6))
      | _ => throw errType
    let (c', id) := r
    let k := (nodeKind? c' id).getD .gain
    pure (c', ofStr s!"{id} {k.numInputs} {k.numOutputs} {k.numParams}")

/-! ## 177, 178: connections -/

def connectOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  withCtx s fs fun c => do
    let src ← natArg fs 1
    let out ← natArg fs 2
    let dst ← natArg fs 3
    let inp ← natArg fs 4
    let c' ← lift (if strArg fs 5 == "1" then c.connectParam src out dst inp
                   else c.connect src out dst inp)
    pure (c', ByteArray.empty)

def withGraph (c : Context.OfflineContext) (r : Except Graph.Error Graph.Graph) :
    Except Int Context.OfflineContext :=
  match r with
  | .ok g => .ok { c with state := { c.state with graph := g } }
  | .error e => .error (codeOf (Context.Error.ofGraph e))

def disconnectOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  withCtx s fs fun c => do
    let src ← natArg fs 1
    let dst ← optNatArg fs 2
    let out ← optNatArg fs 3
    let inp ← optNatArg fs 4
    let g := c.state.graph
    let toParam := strArg fs 5 == "1"
    let r :=
      match dst, out, inp with
      | none, none, _ => Graph.disconnectAll g src
      | none, some o, _ => Graph.disconnectOutput g src o
      | some d, none, none => Graph.disconnectNode g src d
      | some d, some o, none => Graph.disconnectNodeOutput g src d o
      | some d, none, some i =>
        if toParam then Graph.disconnectParam g src d i else Graph.disconnectNode g src d
      | some d, some o, some i =>
        if toParam then Graph.disconnectParamOutput g src d i o
        else Graph.disconnectNodeOutputInput g src d o i
    let c' ← withGraph c r
    pure (c', ByteArray.empty)

/-! ## 179, 180: AudioParam -/

def paramCallOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  withCtx s fs fun c => do
    let id ← natArg fs 1
    let p ← natArg fs 2
    let c' ← match strArg fs 3 with
      | "setValueAtTime" => do lift (c.setValueAtTime id p (← f64Arg fs 4) (← f64Arg fs 5))
      | "linearRampToValueAtTime" =>
        do lift (c.linearRampToValueAtTime id p (← f64Arg fs 4) (← f64Arg fs 5))
      | "exponentialRampToValueAtTime" =>
        do lift (c.exponentialRampToValueAtTime id p (← f64Arg fs 4) (← f64Arg fs 5))
      | "setTargetAtTime" =>
        do lift (c.setTargetAtTime id p (← f64Arg fs 4) (← f64Arg fs 5) (← f64Arg fs 6))
      | "setValue" => do lift (c.setParamValue id p (← f64Arg fs 4))
      | "cancelScheduledValues" => do lift (c.cancelScheduledValues id p (← f64Arg fs 4))
      | "cancelAndHoldAtTime" => do lift (c.cancelAndHoldAtTime id p (← f64Arg fs 4))
      | "setValueCurveAtTime" => do
        let vs ← f32s (fs.getD 4 ByteArray.empty)
        lift (c.setValueCurveAtTime id p vs.data (← f64Arg fs 5) (← f64Arg fs 6))
      | "setAutomationRate" =>
        match strArg fs 4 with
        | "a-rate" =>
          if nodeKind? c id == some .bufferSource then throw errInvalidState
          else lift (c.setAutomationRate id p true)
        | "k-rate" => lift (c.setAutomationRate id p false)
        | _ => throw errType
      | _ => throw errType
    pure (c', ByteArray.empty)

def paramInfoOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  withCtx s fs fun c => do
    let id ← natArg fs 1
    let p ← natArg fs 2
    match c.state.nodes[id]? with
    | none => throw errType
    | some nd =>
      match nd.params[p]? with
      | none => throw errIndexSize
      | some ps =>
        let now := Automation.frameTime c.state.frame c.sampleRate
        let v := Automation.valueAt ps.timeline ps.spec.defaultValue now
        let out := f64le v ++ f64le ps.spec.defaultValue ++ f64le ps.spec.minValue ++
          f64le ps.spec.maxValue ++ ⟨#[if ps.spec.aRate then 1 else 0]⟩
        pure (c, out)

/-! ## 181, 182: scheduled sources -/

def startOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  withCtx s fs fun c => do
    let id ← natArg fs 1
    let w ← optF64Arg fs 2
    let off ← optF64Arg fs 3
    let dur ← optF64Arg fs 4
    let c' ← if nodeKind? c id == some .bufferSource then
        lift (c.startBuffer id (w.getD 0.0) (off.getD 0.0) dur)
      else lift (c.start id (w.getD 0.0))
    pure (c', ByteArray.empty)

def stopOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  withCtx s fs fun c => do
    let id ← natArg fs 1
    let w ← optF64Arg fs 2
    let c' ← lift (c.stop id (w.getD 0.0))
    pure (c', ByteArray.empty)

/-! ## 183 to 186: attributes, buffers, waves -/

def oscTypeOf : String → Option Oscillator.OscType
  | "sine" => some .sine | "square" => some .square | "sawtooth" => some .sawtooth
  | "triangle" => some .triangle | "custom" => some .custom | _ => none

def biquadTypeOf : String → Option Filters.BiquadType
  | "lowpass" => some .lowpass | "highpass" => some .highpass | "bandpass" => some .bandpass
  | "lowshelf" => some .lowshelf | "highshelf" => some .highshelf | "peaking" => some .peaking
  | "notch" => some .notch | "allpass" => some .allpass | _ => none

def modeOf : String → Option Mix.CountMode
  | "max" => some .max | "clamped-max" => some .clampedMax | "explicit" => some .explicit
  | _ => none

def interpOf : String → Option Mix.Interpretation
  | "speakers" => some .speakers | "discrete" => some .discrete | _ => none

def withChan (c : Context.OfflineContext) (id : Nat) (f : Render.ChannelSettings → Render.ChannelSettings) :
    Context.OfflineContext :=
  match c.state.nodes[id]? with
  | some nd => { c with state := { c.state with nodes := c.state.nodes.set! id { nd with chan := f nd.chan } } }
  | none => c

/-- Channel attributes of a node, with the constraints of its interface (section on each node's
"channelCount", "channelCountMode" and "channelInterpretation" lines): the merger, the splitter and
the offline destination are fixed; a stereo panner has at most 2 channels and not the mode `max`. -/
def setChannelAttr (c : Context.OfflineContext) (id : Nat) (name : String) (v : String) :
    Except Int Context.OfflineContext := do
  let nd ← match c.state.nodes[id]? with | some nd => pure nd | none => throw errType
  let k ← match nodeKind? c id with | some k => pure k | none => throw errType
  let fixed := match k with
    | .destination | .splitter _ | .merger _ => true
    | _ => false
  match name with
  | "channelCount" =>
    let n ← match v.toNat? with | some n => pure n | none => throw errType
    if fixed then (if n == nd.chan.count then pure c else throw errInvalidState)
    else if n == 0 || n > 32 then throw errNotSupported
    else if k == .stereoPanner && n > 2 then throw errNotSupported
    else pure (withChan c id fun ch => { ch with count := n })
  | "channelCountMode" =>
    let m ← match modeOf v with | some m => pure m | none => throw errType
    if fixed then (if m == nd.chan.mode then pure c else throw errInvalidState)
    else if k == .stereoPanner && m == .max then throw errNotSupported
    else pure (withChan c id fun ch => { ch with mode := m })
  | _ =>
    let i ← match interpOf v with | some i => pure i | none => throw errType
    match k with
    | .splitter _ => if i == nd.chan.interp then pure c else throw errInvalidState
    | _ => pure (withChan c id fun ch => { ch with interp := i })

def setAttrOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  withCtx s fs fun c => do
    let id ← natArg fs 1
    let name := strArg fs 2
    let c' ← match name with
      | "type" =>
        match nodeKind? c id with
        | some .oscillator =>
          match oscTypeOf (strArg fs 3) with
          | some t => lift (c.setOscillatorType id t)
          | none => throw errType
        | some .biquad =>
          match biquadTypeOf (strArg fs 3) with
          | some t => lift (c.setBiquadType id t)
          | none => throw errType
        | _ => throw errInvalidState
      | "loop" => lift (c.setLoop id (strArg fs 3 == "1"))
      | "loopStart" => do lift (c.setLoopStart id (← f64Arg fs 3))
      | "loopEnd" => do lift (c.setLoopEnd id (← f64Arg fs 3))
      | "channelCount" | "channelCountMode" | "channelInterpretation" =>
        setChannelAttr c id name (strArg fs 3)
      | _ => throw errType
    pure (c', ByteArray.empty)

/-- A buffer from the fields `channels, length, sampleRate, data`; `none` for null (`channels`
""). -/
def bufferArgs (fs : Array ByteArray) (i : Nat) :
    Except Int (Option Buffer.AudioBuffer) := do
  match ← optNatArg fs i with
  | none => pure none
  | some nch =>
    let len ← natArg fs (i + 1)
    let sr ← f64Arg fs (i + 2)
    let data := fs.getD (i + 3) ByteArray.empty
    if nch * len > maxSamples then throw errNotSupported
    let b ← lift (Buffer.AudioBuffer.create nch len sr |>.mapError Context.Error.ofBuffer)
    if data.size != nch * len * 4 then throw errType
    let all ← f32s data
    let chans := (Array.range nch).map fun ch =>
      (⟨(Array.range len).map fun j => all.data[ch * len + j]!⟩ : FloatArray)
    pure (some { b with data := chans })

def setBufferOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  withCtx s fs fun c => do
    let id ← natArg fs 1
    let b ← bufferArgs fs 2
    let c' ← lift (c.setBuffer id b)
    pure (c', ByteArray.empty)

def waveOf (fs : Array ByteArray) (i : Nat) : Except Int Oscillator.PeriodicWave := do
  let r ← optF32s fs i
  let im ← optF32s fs (i + 1)
  lift ((Oscillator.PeriodicWave.create r im (strArg fs (i + 2) == "1")).mapError Context.Error.ofWave)

def setPeriodicWaveOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  withCtx s fs fun c => do
    let id ← natArg fs 1
    let w ← waveOf fs 2
    let c' ← lift (c.setPeriodicWave id w)
    pure (c', ByteArray.empty)

def checkOp (fs : Array ByteArray) : Except Int ByteArray :=
  match strArg fs 0 with
  | "buffer" => do
    let nch ← natArg fs 1
    let len ← natArg fs 2
    let sr ← f64Arg fs 3
    if nch * len > maxSamples then throw errNotSupported
    let _ ← lift (Buffer.AudioBuffer.create nch len sr |>.mapError Context.Error.ofBuffer)
    pure ByteArray.empty
  | "wave" => do
    let _ ← waveOf fs 1
    pure ByteArray.empty
  | _ => .error errType

/-! ## 187 to 189: rendering and queries -/

def endedIds (c : Context.OfflineContext) : List Nat :=
  (List.range c.state.nodes.size).filter fun id =>
    match nodeKind? c id with
    | some .constantSource | some .oscillator | some .bufferSource => c.ended id
    | _ => false

def startRenderingOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  withCtx s fs fun c => do
    let (c', chans) ← lift c.startRendering
    let ended := endedIds c'
    let samples := chans.foldl (fun acc ch => acc ++ f32sBytes ch) ByteArray.empty
    let tail := ended.foldl (fun acc i => acc ++ u32le i) (u32le ended.length)
    pure (c', u32le c.numberOfChannels ++ u32le c.length ++ samples ++ tail)

def frequencyResponseOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  withCtx s fs fun c => do
    let id ← natArg fs 1
    let freqs ← f32s (fs.getD 2 ByteArray.empty)
    let ml ← natArg fs 3
    let pl ← natArg fs 4
    match c.state.nodes[id]? with
    | none => throw errType
    | some nd =>
      match nd.ks with
      | .biquad st =>
        let now := Automation.frameTime c.state.frame c.sampleRate
        let v := fun (i : Nat) => match nd.params[i]? with
          | some p => Automation.valueAt p.timeline p.spec.defaultValue now
          | none => 0.0
        let bp : Filters.BiquadParams :=
          { type := st.type, frequency := v 0, detune := v 1, q := v 2, gain := v 3 }
        match Filters.getFrequencyResponse bp c.sampleRate freqs ml pl with
        | .ok (m, p) => pure (c, f32sBytes m ++ f32sBytes p)
        | .error _ => throw errInvalidAccess
      | _ => throw errInvalidState

def infoOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  withCtx s fs fun c => do
    pure (c, f64le c.sampleRate ++ u32le c.length ++ u32le c.numberOfChannels ++
      u32le c.currentFrame ++ u32le c.state.quantum ++ u32le c.state.nodes.size ++
      ⟨#[if c.rendered then 1 else 0]⟩)


/-! ## 190 to 196: real-time contexts, decoding -/

/-- Decimal text of a count, as bytes. -/
def dec (k : Nat) : ByteArray := ofStr (toString k)

/-- A sample rate as text: an integer when it is one. -/
def rateText (r : Float) : String :=
  if r == r.floor && r < 1e9 then toString r.toUInt64.toNat else toString r

/-- Real-time contexts that are not closed. -/
def liveRealtime (s : State) : Nat :=
  s.realtime.fold (fun n _ rt => if rt.state == .closed then n else n + 1) 0

def maxLiveRealtime : Nat := 16

/-- The latency hint: a fixed number of frames, or seconds. -/
inductive Hint where
  | frames (n : Nat)
  | seconds (x : Float)

def parseHint (b : ByteArray) : Except Int Hint :=
  if b == "interactive".toUTF8 then .ok (.frames 1024)
  else if b == "balanced".toUTF8 then .ok (.frames 2048)
  else if b == "playback".toUTF8 then .ok (.frames 4096)
  else if b.size == 8 then
    let x := Float.ofBits (u64At b 0)
    if x.isFinite && x ≥ 0.0 then .ok (.seconds x) else .error errType
  else .error errType

/-- Target frames (plan 13.4): the hint's, seconds rounded up and kept within 256 to 16384. -/
def targetFrames (h : Hint) (rate : Float) : Nat :=
  match h with
  | .frames n => n
  | .seconds x => min 16384 (max 256 (x * rate).ceil.toUInt64.toNat)

def newAudioContextOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) := do
  let hint ← parseHint (fs.getD 0 ByteArray.empty)
  let cb ← natArg fs 2
  let rateField := fs.getD 1 ByteArray.empty
  let (devRate, devCh) := s.device.getD (0.0, 0)
  let rate ← if rateField.size == 0 then pure devRate else f64Arg fs 1
  if !(rate ≥ 3000.0 && rate ≤ 768000.0) then throw errNotSupported
  if s.device.isNone || liveRealtime s ≥ maxLiveRealtime || s.contexts.size ≥ maxContexts then
    throw errNotSupported
  let c0 ← lift (Context.OfflineContext.new 2 1 rate)
  let c := { c0 with length := 0 }
  let id := s.next
  let target := targetFrames hint rate
  let rt : Realtime :=
    { state := if s.autoplay || s.activated then .running else .suspended
      maxChannels := devCh, target, callback := cb
      outbox := #[(190, #[dec id, f64le rate, dec devCh, dec target])] }
  pure ({ s with contexts := s.contexts.insert id c, realtime := s.realtime.insert id rt,
                 next := id + 1 },
        ofStr s!"{id} {rateText rate} {devCh} {rt.state.text}")

def controlOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) := do
  let id ← natArg fs 0
  let rt ← match s.realtime[id]? with | some rt => pure rt | none => throw errType
  let verb := strArg fs 1
  if !(verb == "resume" || verb == "suspend" || verb == "close") then throw errType
  if rt.state == .closed then throw errInvalidState
  let call := s.nextCall
  let wait := verb == "resume" && !(s.autoplay || s.activated)
  let rt' : Realtime :=
    { rt with calls := rt.calls.push (call, verb)
              pendingResume := if wait then rt.pendingResume.push call else rt.pendingResume
              outbox := if wait then rt.outbox
                        else rt.outbox.push (191, #[dec id, ofStr verb, dec call]) }
  pure ({ s with realtime := s.realtime.insert id rt', nextCall := call + 1 }, dec call)

def timeOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) := do
  let id ← natArg fs 0
  let rt ← match s.realtime[id]? with | some rt => pure rt | none => throw errType
  let c ← match s.contexts[id]? with | some c => pure c | none => throw errType
  let r := c.sampleRate
  let sec (n : Nat) : Float := Float.ofNat n / r
  pure (s, f64le (sec rt.framesRendered) ++ f64le (sec rt.target) ++ f64le (sec rt.latencyFrames) ++
    ⟨#[rt.state.code.toUInt8]⟩ ++ f64le (sec rt.framesPlayed) ++ f64le rt.reportMs)

def eventsOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) := do
  let id ← natArg fs 0
  let rt ← match s.realtime[id]? with | some rt => pure rt | none => throw errType
  let out := rt.events.foldl (fun acc (k, v) => acc ++ ⟨#[k]⟩ ++ u32le v) (u32le rt.events.size)
  pure ({ s with realtime := s.realtime.insert id { rt with events := #[] } }, out)

def decodeAudioDataOp (s : State) (fs : Array ByteArray) : Except Int (State × ByteArray) := do
  let id ← natArg fs 0
  let c ← match s.contexts[id]? with | some c => pure c | none => throw errType
  let cb ← natArg fs 2
  let job := s.nextJob
  pure ({ s with decodeJobs := s.decodeJobs.insert job
                   { rate := c.sampleRate, bytes := fs.getD 1 ByteArray.empty, callback := cb }
                 nextJob := job + 1 }, dec job)

/-- The result of a finished job as the bytes of op 195. -/
def decodeAnswer (r : Nat × Nat × Float × ByteArray) : ByteArray :=
  u32le r.1 ++ u32le r.2.1 ++ f64le r.2.2.1 ++ r.2.2.2

/-- Op 195. The job leaves the table when its result is given, error results included. -/
def decodeResultOp (s : State) (fs : Array ByteArray) : State × Except Int ByteArray :=
  match natArg fs 0 with
  | .error e => (s, .error e)
  | .ok job =>
    match s.decodeJobs[job]? with
    | none => (s, .error errType)
    | some j =>
      match j.result with
      | none => (s, .error errInvalidState)
      | some r => ({ s with decodeJobs := s.decodeJobs.erase job }, r.map decodeAnswer)

/-- Op 196: sticky activation. Each pending `resume` call goes to its context's outbox. -/
def activate (s : State) : State :=
  { s with activated := true
           realtime := s.realtime.map fun id rt =>
             if rt.pendingResume.isEmpty then rt
             else { rt with pendingResume := #[]
                            outbox := rt.pendingResume.foldl
                              (fun o call => o.push (191, #[dec id, ofStr "resume", dec call]))
                              rt.outbox } }

/-! ## What the IO layer of step D3 calls -/

/-- Merge a report of the rendering side of context `ctx`. Frames rendered and played become the
larger of the old and the new value (also in the graph state's `frame`, which automation reads at
the current time); ended sources, state changes and the control calls carried out or refused
become events; the context's callback is queued once when any event was added. A context that is
not real-time is not changed. -/
def applyReport (s : State) (ctx : Nat) (r : Report) : State :=
  match s.realtime[ctx]?, s.contexts[ctx]? with
  | some rt, some c =>
    let evs : Array (UInt8 × Nat) :=
      r.ended.map (fun i => ((1 : UInt8), i)) ++
      r.stateChanges.map (fun st => ((2 : UInt8), st.code)) ++
      r.confirmed.map (fun i => ((3 : UInt8), i)) ++
      r.rejected.map (fun i => ((4 : UInt8), i))
    let done (i : Nat) : Bool := r.confirmed.contains i || r.rejected.contains i
    let fr := max rt.framesRendered r.framesRendered
    let rt' : Realtime :=
      { rt with state := r.stateChanges.back?.getD rt.state
                framesRendered := fr
                framesPlayed := max rt.framesPlayed r.framesPlayed
                underruns := max rt.underruns r.underruns
                latencyFrames := r.latencyFrames
                reportMs := r.timeMs
                calls := rt.calls.filter (fun (i, _) => !done i)
                events := rt.events ++ evs }
    let c' := { c with state := { c.state with frame := max c.state.frame fr } }
    { s with realtime := s.realtime.insert ctx rt', contexts := s.contexts.insert ctx c'
             wakeups := if evs.isEmpty then s.wakeups else s.wakeups.push rt.callback }
  | _, _ => s

/-- A sequence of reports, in order. -/
def applyReports (s : State) (rs : List (Nat × Report)) : State :=
  rs.foldl (fun s (c, r) => applyReport s c r) s

/-- All outboxes, emptied: the contexts that have messages, each with its messages in order. -/
def takeOutbox (s : State) : State × Array (Nat × Array (Nat × Array ByteArray)) :=
  ({ s with realtime := s.realtime.map fun _ rt => { rt with outbox := #[] } },
   (s.realtime.toList.filterMap fun (id, rt) =>
      if rt.outbox.isEmpty then none else some (id, rt.outbox)).toArray)

/-- The decode jobs not yet taken: (job id, sample rate, bytes), in job order. They are marked
taken. -/
def takeDecodeJobs (s : State) : State × Array (Nat × Float × ByteArray) :=
  let l := s.decodeJobs.toList.filter fun (_, j) => !j.taken && j.result.isNone
  let l := l.toArray.qsort (fun a b => a.1 < b.1)
  ({ s with decodeJobs := s.decodeJobs.map fun _ j => { j with taken := true } },
   l.map fun (id, j) => (id, j.rate, j.bytes))

/-- Store the result of decode job `job` and queue its callback. A job that does not exist, or
that has a result, is left alone. -/
def finishDecode (s : State) (job : Nat) (result : Except Int (Nat × Nat × Float × ByteArray)) :
    State :=
  match s.decodeJobs[job]? with
  | some j =>
    if j.result.isNone then
      { s with decodeJobs := s.decodeJobs.insert job { j with taken := true, result := some result }
               wakeups := s.wakeups.push j.callback }
    else s
  | none => s

def takeWakeups (s : State) : State × Array Nat := ({ s with wakeups := #[] }, s.wakeups)

/-! ## The dispatch -/

def run (s : State) (code : Nat) (fs : Array ByteArray) : Except Int (State × ByteArray) :=
  match code with
  | 173 => (interfaceOp fs).map (s, ·)
  | 174 => (idlOp fs).map (s, ·)
  | 175 => newContextOp s fs
  | 176 => createNodeOp s fs
  | 177 => connectOp s fs
  | 178 => disconnectOp s fs
  | 179 => paramCallOp s fs
  | 180 => paramInfoOp s fs
  | 181 => startOp s fs
  | 182 => stopOp s fs
  | 183 => setAttrOp s fs
  | 184 => setBufferOp s fs
  | 185 => setPeriodicWaveOp s fs
  | 186 => (checkOp fs).map (s, ·)
  | 187 =>
    match natArg fs 0 with
    | .ok id => if s.realtime.contains id then .error errInvalidState else startRenderingOp s fs
    | .error _ => startRenderingOp s fs
  | 188 => frequencyResponseOp s fs
  | 189 => infoOp s fs
  | 190 => newAudioContextOp s fs
  | 191 => controlOp s fs
  | 192 => timeOp s fs
  | 193 => eventsOp s fs
  | 194 => decodeAudioDataOp s fs
  | 196 => pure (activate s, ByteArray.empty)
  | _ => .error (-2)

/-- The ops whose success is also sent to the rendering side of a real-time context. -/
def outboxCode (code : Nat) : Bool :=
  (176 ≤ code && code ≤ 179) || (181 ≤ code && code ≤ 185)

/-- Append `(code, fs)` to the outbox of the real-time context named by field 0, if it is not
closed. -/
def pushOutbox (s : State) (code : Nat) (fs : Array ByteArray) : State :=
  match natArg fs 0 with
  | .ok id =>
    match s.realtime[id]? with
    | some rt =>
      if rt.state == .closed then s
      else { s with realtime := s.realtime.insert id { rt with outbox := rt.outbox.push (code, fs) } }
    | none => s
  | .error _ => s

/-- The operations 173 to 196. A failed op leaves the state as it was (except 195 with a stored
error result); the answer is the error code (negative) or the bytes. -/
def op (s : State) (code : Nat) (fs : Array ByteArray) : State × Except Int ByteArray :=
  if code = 195 then decodeResultOp s fs
  else
    match run s code fs with
    | .ok (s', out) => ((if outboxCode code then pushOutbox s' code fs else s'), .ok out)
    | .error e => (s, .error e)

/-- Says: an op other than 195 that answers an error returns the state it was given. Does not
say: that an op that succeeds changes the state (a query does not); nor anything about 195, which
removes a job whose stored result is an error. -/
theorem op_error_state (s : State) (code : Nat) (fs : Array ByteArray) (e : Int)
    (hc : code ≠ 195) (h : (op s code fs).2 = .error e) : (op s code fs).1 = s := by
  unfold op at *
  simp only [hc, if_false] at *
  split at h <;> simp_all

/-- Says: a code outside 173 to 196 answers -2 and leaves the state alone. Does not say: anything
about the codes inside the range. -/
theorem op_unknown (s : State) (code : Nat) (fs : Array ByteArray) (h : code < 173 ∨ 196 < code) :
    op s code fs = (s, .error (-2)) := by
  have hr : run s code fs = .error (-2) := by
    unfold run
    split <;> first | omega | rfl
  have hc : code ≠ 195 := by omega
  unfold op
  rw [if_neg hc, hr]

/-- Says: `withCtx` changes only `contexts`. Does not say: which context. -/
theorem withCtx_fields (s s' : State) (fs : Array ByteArray) (out : ByteArray)
    (f : Context.OfflineContext → Except Int (Context.OfflineContext × ByteArray))
    (h : withCtx s fs f = .ok (s', out)) : ∃ m, s' = { s with contexts := m } := by
  unfold withCtx at h
  generalize hn : natArg fs 0 = n at h
  match n, h with
  | .error _, h => simp [bind, Except.bind] at h
  | .ok id, h =>
    simp only [bind, Except.bind] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp [pure, Except.pure] at h
        exact ⟨_, h.1.symm⟩

/-- Says: a successful op of the outbox codes leaves `realtime` as it was. Does not say: that the
outbox is not appended to by `op` (it is, see `op_outbox`). -/
theorem run_realtime (s s' : State) (code : Nat) (fs : Array ByteArray) (out : ByteArray)
    (hc : outboxCode code = true) (h : run s code fs = .ok (s', out)) :
    s'.realtime = s.realtime := by
  have hc' : code = 176 ∨ code = 177 ∨ code = 178 ∨ code = 179 ∨ code = 181 ∨ code = 182 ∨
      code = 183 ∨ code = 184 ∨ code = 185 := by
    unfold outboxCode at hc; simp at hc; omega
  have key : ∀ f, withCtx s fs f = .ok (s', out) → s'.realtime = s.realtime := by
    intro f hw
    obtain ⟨m, rfl⟩ := withCtx_fields s s' fs out f hw
    rfl
  rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
    | exact key _ h
    | (simp only [run] at h; exact key _ h)

/-- Says: a successful op 176 to 179 or 181 to 185 on a real-time context that is not closed
appends exactly `(code, fs)` to its outbox, and changes no other context's record. Does not say:
what happens to the graph state (`withCtx_other`), or for a closed context. -/
theorem op_outbox (s s' : State) (code : Nat) (fs : Array ByteArray) (out : ByteArray)
    (id : Nat) (rt : Realtime) (hc : outboxCode code = true) (hid : natArg fs 0 = .ok id)
    (hrt : s.realtime[id]? = some rt) (hopen : rt.state ≠ .closed)
    (h : op s code fs = (s', .ok out)) :
    s'.realtime[id]? = some { rt with outbox := rt.outbox.push (code, fs) } ∧
    ∀ id', id' ≠ id → s'.realtime[id']? = s.realtime[id']? := by
  have hn : code ≠ 195 := by unfold outboxCode at hc; simp at hc; omega
  unfold op at h
  rw [if_neg hn] at h
  split at h
  · rename_i s1 o1 hr
    have hrt1 := run_realtime s s1 code fs o1 hc hr
    simp only [hc, if_true, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hrt' : s1.realtime[id]? = some rt := by rw [hrt1]; exact hrt
    unfold pushOutbox
    rw [hid]
    simp only [hrt']
    have hb : (rt.state == RtState.closed) = false := by
      cases hs : rt.state <;> simp_all
    simp only [hb]
    refine ⟨by simp, ?_⟩
    intro id' hne
    have : id ≠ id' := fun e => hne e.symm
    simp [Std.HashMap.getElem?_insert, this, hrt1]
  · simp at h

/-! ## Tests -/

namespace Tests

private def d (x : Float) : ByteArray := f64le x
private def n (k : Nat) : ByteArray := ofStr (toString k)
private def t (x : String) : ByteArray := ofStr x

/-- Run a list of ops in order; `none` on the first error. -/
private def chain (s : State) : List (Nat × List ByteArray) → Option State
  | [] => some s
  | (c, a) :: rest =>
    match run s c a.toArray with
    | .ok (s', _) => chain s' rest
    | .error _ => none

private def ans (s : State) (c : Nat) (a : List ByteArray) : Except Int ByteArray :=
  (run s c a.toArray).map (·.2)

private def err (s : State) (c : Nat) (a : List ByteArray) : Int :=
  match run s c a.toArray with | .error e => e | .ok _ => 0

private def st0 : State := (chain {} [(175, [n 1, n 1000, d 44100.0])]).getD {}

/-- The samples of a rendering answer (after the 8-byte header). -/
private def samples (r : ByteArray) (count : Nat) : List Float :=
  (List.range count).map fun i => (Float32.ofBits (u32At r (8 + 4 * i))).toFloat

private def okBytes (r : Except Int ByteArray) : ByteArray := (r.toOption).getD ByteArray.empty

-- Contexts: ids, refusals.
#guard (ans {} 175 [n 2, n 100, d 44100.0]).toOption == some (t "1")
#guard err {} 175 [n 0, n 100, d 44100.0] == errNotSupported
#guard err {} 175 [n 1, n 100, d 100.0] == errNotSupported
#guard err {} 175 [n 1, n 0, d 44100.0] == errNotSupported
#guard err {} 175 [n 1, n 100, ByteArray.empty] == errType
#guard err {} 175 [n 32, n 2000000, d 44100.0] == errNotSupported
#guard err st0 189 [n 99] == errType
#guard err {} 999 [] == -2

-- A constant source of 1 straight to the destination: the bytes of the first samples.
private def constRender : Option State :=
  chain st0 [(176, [n 1, t "constantSource"]), (177, [n 1, n 1, n 0, n 0, n 0, n 0]),
             (181, [n 1, n 1, d 0.0])]

#guard (ans (constRender.getD {}) 176 [n 1, t "gain"]).toOption == some (t "2 1 1 1")
#guard ((ans (constRender.getD {}) 187 [n 1]).toOption.map (·.size)) == some (8 + 4000 + 4)
#guard (ans (constRender.getD {}) 187 [n 1]).toOption.map (fun r => (r.extract 8 12).toList) ==
  some [0x00, 0x00, 0x80, 0x3F]
#guard (ans (constRender.getD {}) 187 [n 1]).toOption.map (fun r => (r.extract 0 8).toList) ==
  some [1, 0, 0, 0, 0xE8, 0x03, 0, 0]
#guard (ans (constRender.getD {}) 187 [n 1]).toOption.map (fun r => samples r 1000 |>.all (· == 1.0)) ==
  some true
-- Not stopped: the source has not ended, so the ended list is empty.
#guard (ans (constRender.getD {}) 187 [n 1]).toOption.map (fun r => u32At r (8 + 4000)) == some 0
-- Rendering twice.
#guard (do let s ← constRender
           let (s, _) ← (run s 187 #[n 1]).toOption
           pure (err s 187 [n 1])) == some errInvalidState

-- A stopped source ends and is reported by id.
private def stopped : Option State :=
  chain st0 [(176, [n 1, t "constantSource"]), (177, [n 1, n 1, n 0, n 0, n 0, n 0]),
             (181, [n 1, n 1, d 0.0]), (182, [n 1, n 1, d 0.001])]
#guard (stopped.bind fun s => (ans s 187 [n 1]).toOption.map fun r =>
    (u32At r (8 + 4000), u32At r (8 + 4000 + 4),
     (samples r 1000).getD 44 9.0, (samples r 1000).getD 45 9.0)) ==
  some (1, 1, 1.0, 0.0)

-- Gain with automation: constant 1 * gain ramping 0 to 1 over 0.01 s (441 frames).
private def ramped : Option State :=
  chain st0 [(176, [n 1, t "constantSource"]), (176, [n 1, t "gain"]),
             (177, [n 1, n 1, n 0, n 2, n 0, n 0]), (177, [n 1, n 2, n 0, n 0, n 0, n 0]),
             (179, [n 1, n 2, n 0, t "setValueAtTime", d 0.0, d 0.0]),
             (179, [n 1, n 2, n 0, t "linearRampToValueAtTime", d 1.0, d 0.01]),
             (181, [n 1, n 1])]
#guard (ramped.bind fun s => (ans s 187 [n 1]).toOption.map fun r =>
    let xs := samples r 1000
    (xs.getD 0 9.0 == 0.0, decide ((xs.getD 441 0.0 - 1.0).abs < 1e-6), xs.getD 999 0.0 == 1.0,
     decide ((xs.getD 220 0.0 - 220.0 / 441.0).abs < 1e-5))) == some (true, true, true, true)

-- An oscillator: a sine at 440 Hz; frame k is sin(2 pi 440 k / 44100) within binary32 rounding
-- (frame 1: 0.0626483..., frame 100: the value below).
private def osc : Option State :=
  chain st0 [(176, [n 1, t "oscillator"]), (177, [n 1, n 1, n 0, n 0, n 0, n 0]),
             (181, [n 1, n 1])]
#guard (osc.bind fun s => (ans s 187 [n 1]).toOption.map fun r =>
    let xs := samples r 1000
    (xs.getD 0 9.0 == 0.0, decide ((xs.getD 1 0.0 - 0.0626483241787437).abs < 1e-6),
     decide ((xs.getD 100 0.0 - (-0.0142471037071029)).abs < 1e-6),
     xs.all (fun x => x.abs ≤ 1.0001))) == some (true, true, true, true)
-- Frequency set through the parameter: a square wave.
#guard (do
  let s ← chain st0 [(176, [n 1, t "oscillator"]), (177, [n 1, n 1, n 0, n 0, n 0, n 0]),
                     (183, [n 1, n 1, t "type", t "square"]), (181, [n 1, n 1])]
  let r ← (ans s 187 [n 1]).toOption
  pure ((samples r 1000).any (· > 0.5))) == some true

-- A buffer source with a buffer given as bytes.
private def bufBytes : ByteArray := f32le 0.5 ++ f32le (-0.25) ++ f32le 0.125 ++ f32le 1.0
private def bufRender : Option State :=
  chain st0 [(176, [n 1, t "bufferSource"]), (177, [n 1, n 1, n 0, n 0, n 0, n 0]),
             (184, [n 1, n 1, n 1, n 4, d 44100.0, bufBytes]), (181, [n 1, n 1])]
#guard (bufRender.bind fun s => (ans s 187 [n 1]).toOption.map fun r =>
    ((samples r 6).take 6, u32At r (8 + 4000))) == some ([0.5, -0.25, 0.125, 1.0, 0.0, 0.0], 1)
-- A second non-null buffer is refused; null is accepted.
#guard (bufRender.map fun s => err s 184 [n 1, n 1, n 1, n 4, d 44100.0, bufBytes]) == some errInvalidState
#guard (bufRender.map fun s => err s 184 [n 1, n 1, ByteArray.empty]) == some 0
-- Wrong byte count; out of range sample rate; a node that is not a buffer source.
#guard (chain st0 [(176, [n 1, t "bufferSource"])]).map
  (fun s => (err s 184 [n 1, n 1, n 1, n 4, d 44100.0, bufBytes.extract 0 8],
             err s 184 [n 1, n 1, n 1, n 4, d 10.0, bufBytes])) == some (errType, errNotSupported)
#guard err st0 184 [n 1, n 0, n 1, n 4, d 44100.0, bufBytes] == errInvalidState
#guard (chain st0 [(176, [n 1, t "gain"])]).map
  (fun s => err s 184 [n 1, n 1, n 1, n 4, d 44100.0, bufBytes]) == some errInvalidState

-- Connect and disconnect.
#guard (chain st0 [(176, [n 1, t "gain"])]).map
  (fun s => (err s 177 [n 1, n 1, n 1, n 0, n 0, n 0],      -- output 1 of a gain does not exist
             err s 177 [n 1, n 1, n 0, n 0, n 5, n 0],      -- input 5 of the destination
             err s 177 [n 1, n 1, n 0, n 1, n 7, n 1],      -- parameter 7 of a gain
             err s 177 [n 1, n 9, n 0, n 0, n 0, n 0])) ==   -- no node 9
  some (errIndexSize, errIndexSize, errIndexSize, errType)
#guard (chain st0 [(176, [n 1, t "gain"])]).map
  (fun s => (err s 178 [n 1, n 1, n 0, ByteArray.empty, ByteArray.empty, n 0],   -- not connected
             err s 178 [n 1, n 1, ByteArray.empty, n 3, ByteArray.empty, n 0],   -- output 3
             err s 178 [n 1, n 1, ByteArray.empty, ByteArray.empty, ByteArray.empty, n 0])) ==
  some (errInvalidAccess, errIndexSize, 0)
#guard (do
  let s ← constRender
  let s ← chain s [(178, [n 1, n 1, n 0, ByteArray.empty, ByteArray.empty, n 0])]
  let r ← (ans s 187 [n 1]).toOption
  pure ((samples r 1000).all (· == 0.0))) == some true
#guard (do
  let s ← constRender
  let s ← chain s [(178, [n 1, n 1, ByteArray.empty, ByteArray.empty, ByteArray.empty, n 0])]
  let r ← (ans s 187 [n 1]).toOption
  pure ((samples r 1000).all (· == 0.0))) == some true
#guard (do
  let s ← chain st0 [(176, [n 1, t "gain"]), (176, [n 1, t "gain"]),
                     (177, [n 1, n 1, n 0, n 2, n 0, n 1])]
  let s' ← chain s [(178, [n 1, n 1, n 2, ByteArray.empty, n 0, n 1])]
  pure (err s' 178 [n 1, n 1, n 2, ByteArray.empty, n 0, n 1])) == some errInvalidAccess

-- AudioParam methods and errors.
#guard (chain st0 [(176, [n 1, t "gain"])]).map
  (fun s => (err s 179 [n 1, n 1, n 0, t "setValueAtTime", d 1.0, d (-1.0)],
             err s 179 [n 1, n 1, n 5, t "setValueAtTime", d 1.0, d 0.0],
             err s 179 [n 1, n 1, n 0, t "frobnicate"],
             err s 179 [n 1, n 1, n 0, t "setAutomationRate", t "fast"],
             err s 179 [n 1, n 1, n 0, t "setValueAtTime", d 1.0, d 0.0])) ==
  some (errRange, errIndexSize, errType, errType, 0)
-- The value setter and getter.
#guard (do
  let s ← chain st0 [(176, [n 1, t "gain"]), (179, [n 1, n 1, n 0, t "setValue", d 0.25])]
  let r ← (ans s 180 [n 1, n 1, n 0]).toOption
  pure (Float.ofBits (u64At r 0), Float.ofBits (u64At r 8), r.size, r.get! 32)) ==
  some (0.25, 1.0, 33, 1)
-- k-rate: allowed for a gain; fixed for a buffer source.
#guard (do
  let s ← chain st0 [(176, [n 1, t "gain"]), (176, [n 1, t "bufferSource"]),
                     (179, [n 1, n 1, n 0, t "setAutomationRate", t "k-rate"])]
  let r ← (ans s 180 [n 1, n 1, n 0]).toOption
  pure (r.get! 32, err s 179 [n 1, n 2, n 0, t "setAutomationRate", t "a-rate"])) ==
  some (0, errInvalidState)

-- start and stop errors.
#guard (chain st0 [(176, [n 1, t "oscillator"]), (181, [n 1, n 1])]).map
  (fun s => (err s 181 [n 1, n 1], err s 181 [n 1, n 1, d (-1.0)], err s 182 [n 1, n 1, d (-1.0)])) ==
  some (errInvalidState, errRange, errRange)
#guard (chain st0 [(176, [n 1, t "oscillator"])]).map
  (fun s => (err s 182 [n 1, n 1, d 1.0], err s 181 [n 1, n 1, d (1.0 / 0.0)],
             err s 181 [n 1, n 0, d 0.0], err s 181 [n 1, n 9])) ==
  some (errInvalidState, errType, errInvalidState, errType)

-- Attributes.
#guard (chain st0 [(176, [n 1, t "oscillator"]), (176, [n 1, t "biquadFilter"]),
                   (176, [n 1, t "channelMerger"]), (176, [n 1, t "stereoPanner"]),
                   (176, [n 1, t "bufferSource"])]).map
  (fun s => (err s 183 [n 1, n 1, t "type", t "custom"],
             err s 183 [n 1, n 1, t "type", t "wobble"],
             err s 183 [n 1, n 2, t "type", t "notch"],
             err s 183 [n 1, n 3, t "type", t "notch"],
             err s 183 [n 1, n 3, t "channelCount", t "2"],
             err s 183 [n 1, n 4, t "channelCount", t "3"],
             err s 183 [n 1, n 4, t "channelCountMode", t "max"],
             err s 183 [n 1, n 5, t "channelCount", t "0"],
             err s 183 [n 1, n 0, t "channelCount", t "3"],
             err s 183 [n 1, n 5, t "channelCount", t "6"])) ==
  some (errInvalidState, errType, 0, errInvalidState, errInvalidState, errNotSupported,
        errNotSupported, errNotSupported, errInvalidState, 0)
-- A periodic wave.
private def sq : ByteArray := f32le 0.0 ++ f32le 0.0
private def sn : ByteArray := f32le 0.0 ++ f32le 1.0
#guard (chain st0 [(176, [n 1, t "oscillator"])]).map
  (fun s => (err s 185 [n 1, n 1, sq, sn, t "0"], err s 185 [n 1, n 1, sq, f32le 0.0, t "0"],
             err s 185 [n 1, n 1, f32le 0.0, f32le 0.0, t "0"],
             err s 185 [n 1, n 1, sq, t "-", t "0"],
             err s 185 [n 1, n 1, f32le 0.0 ++ f32le (1.0 / 0.0), sn, t "0"])) ==
  some (0, errIndexSize, errIndexSize, 0, errType)
#guard (do
  let s ← chain st0 [(176, [n 1, t "oscillator"]), (177, [n 1, n 1, n 0, n 0, n 0, n 0]),
                     (185, [n 1, n 1, sq, sn, t "0"]), (181, [n 1, n 1])]
  let r ← (ans s 187 [n 1]).toOption
  pure ((samples r 1000).any (· > 0.5))) == some true
#guard err {} 186 [t "wave", sq, sn, t "0"] == 0
#guard err {} 186 [t "wave", f32le 0.0, f32le 0.0, t "0"] == errIndexSize
#guard err {} 186 [t "buffer", n 2, n 10, d 44100.0] == 0
#guard err {} 186 [t "buffer", n 0, n 10, d 44100.0] == errNotSupported
#guard err {} 186 [t "buffer", n 2, n 10, d 1.0] == errNotSupported
#guard err {} 186 [t "other"] == errType

-- Creating nodes.
#guard (ans st0 176 [n 1, t "oscillator"]).toOption == some (t "1 0 1 2")
#guard (ans st0 176 [n 1, t "biquadFilter"]).toOption == some (t "1 1 1 4")
#guard (ans st0 176 [n 1, t "channelMerger", n 4]).toOption == some (t "1 4 1 0")
#guard (ans st0 176 [n 1, t "channelSplitter"]).toOption == some (t "1 1 6 0")
#guard err st0 176 [n 1, t "channelSplitter", n 33] == errIndexSize
#guard err st0 176 [n 1, t "channelMerger", n 0] == errIndexSize
#guard err st0 176 [n 1, t "delay", d 0.0] == errNotSupported
#guard err st0 176 [n 1, t "delay", d 180.0] == errNotSupported
#guard (ans st0 176 [n 1, t "delay", d 2.0]).toOption == some (t "1 1 1 1")
#guard err st0 176 [n 1, t "convolver"] == errType

-- A failed op leaves the state alone.
#guard (op st0 176 #[n 1, t "convolver"]).1.contexts.size == 1
#guard (op st0 175 #[n 2, n 10, d 44100.0]).1.next == 3
#guard (op st0 175 #[n 0, n 10, d 44100.0]).1.next == 2

-- The frequency response.
#guard (do
  let s ← chain st0 [(176, [n 1, t "biquadFilter"])]
  let fr := f32le 0.0 ++ f32le 100.0 ++ f32le 30000.0
  let r ← (ans s 188 [n 1, n 1, fr, n 3, n 3]).toOption
  let xs := (List.range 6).map fun i => (Float32.ofBits (u32At r (4 * i))).toFloat
  pure (r.size, (xs.getD 0 0.0 - 1.0).abs < 1e-6,           -- lowpass: unity gain at 0 Hz
        xs.getD 1 0.0 > 0.9, (xs.getD 2 0.0) != (xs.getD 2 0.0),   -- NaN above Nyquist
        (xs.getD 3 0.0).abs < 1e-6)) == some (24, true, true, true, true)
#guard (chain st0 [(176, [n 1, t "biquadFilter"])]).map
  (fun s => err s 188 [n 1, n 1, f32le 0.0, n 2, n 1]) == some errInvalidAccess
#guard (chain st0 [(176, [n 1, t "gain"])]).map
  (fun s => err s 188 [n 1, n 1, f32le 0.0, n 1, n 1]) == some errInvalidState
-- The peaking filter's gain parameter changes the response.
#guard (do
  let s ← chain st0 [(176, [n 1, t "biquadFilter"]), (183, [n 1, n 1, t "type", t "peaking"]),
                     (179, [n 1, n 1, n 3, t "setValue", d 12.0]),
                     (179, [n 1, n 1, n 0, t "setValue", d 1000.0])]
  let r ← (ans s 188 [n 1, n 1, f32le 1000.0, n 1, n 1]).toOption
  let m := (Float32.ofBits (u32At r 0)).toFloat
  pure ((m - 3.981).abs < 0.01)) == some true   -- 12 dB = 3.981

-- Info.
#guard (ans st0 189 [n 1]).toOption.map (fun r =>
  (Float.ofBits (u64At r 0), u32At r 8, u32At r 12, u32At r 16, u32At r 20, u32At r 24, r.get! 28)) ==
  some (44100.0, 1000, 1, 0, 128, 1, 0)

-- The interface text.
#guard (ans {} 173 [t "OfflineAudioContext"]).toOption.map (fun r => (String.fromUTF8! r).startsWith "i\tOfflineAudioContext\tBaseAudioContext") == some true
#guard (ans {} 173 [t ""]).toOption.map (fun r => ((String.fromUTF8! r).splitOn "\n").contains "AudioParam") == some true
#guard (ans {} 173 [t "AudioParam"]).toOption.map (fun r => (String.fromUTF8! r).contains 'a' &&
    ((String.fromUTF8! r).splitOn "\n").any (·.startsWith "o\tsetValueAtTime\t2")) == some true
#guard err {} 173 [t "NoSuchInterface"] == errType
#guard (ans {} 174 [t "enum", t "BiquadFilterType"]).toOption.map (fun r => (String.fromUTF8! r).splitOn "\n") ==
  some ["lowpass", "highpass", "bandpass", "lowshelf", "highshelf", "peaking", "notch", "allpass"]
#guard (ans {} 174 [t "enum", t "OscillatorType"]).toOption.map (fun r => (String.fromUTF8! r).startsWith "sine") == some true
#guard err {} 174 [t "enum", t "Nope"] == errType
#guard err {} 174 [t "struct", t "Nope"] == errType
#guard (ans {} 174 [t "dict", t "OfflineAudioContextOptions"]).toOption.map (fun r => (String.fromUTF8! r).startsWith "p\t") == some true

-- Contexts do not interact.
#guard (do
  let s ← chain st0 [(175, [n 1, n 100, d 44100.0]), (176, [n 1, t "gain"]), (176, [n 2, t "gain"]),
                     (176, [n 2, t "gain"])]
  pure ((ans s 189 [n 1]).toOption.map (fun r => u32At r 24), (ans s 189 [n 2]).toOption.map (fun r => u32At r 24))) ==
  some (some 2, some 3)

-- The codes of the errors of the engine.
#guard codeOf (.notSupported "") == -23 && codeOf .indexSize == -28 && codeOf .invalidAccess == -25
#guard codeOf (.invalidState "") == -29 && codeOf (.range "") == -21 && codeOf (.type "") == -20
#guard errEncoding == -30

end Tests

end L4Factoidal.WebAudio.Api
