import L4Factoidal.WebAudio.Mix

/-!
# Web Audio block kernels

Per-block processing of six nodes of the W3C Web Audio API
(https://webaudio.github.io/web-audio-api/): `GainNode`, `ConstantSourceNode`,
`DelayNode`, `StereoPannerNode`, `ChannelSplitterNode`, `ChannelMergerNode`.
Stage B of https://github.com/danbri/factoidal-core/issues/1169; structure in
`docs/designissues/2026-11-26-foafnaut-audio-plan.md` section 9.

A block is `Array FloatArray`: one `FloatArray` of `n` frames for each channel. A kernel takes
the frame count `n`, its state, its input blocks (already mixed to the node's computed channel
count by `WebAudio.Mix`) and its `AudioParam` value arrays (`params[i]` has `n` values for an
a-rate parameter or one value for a k-rate parameter), and returns the new state and the output
blocks. Computation is in 64-bit `Float`.

Every loop over frames is `iter`, a structurally recursive tail call: no stack frame per sample.

## What is proved

* Output shapes of every kernel (counts of blocks and channels, `n` frames in each channel).
  These are statements about `Array.size`.
* `active`: false before the start frame and at or after the stop frame, true between.
* The delay ring buffer keeps its size, and its write index stays below the size.
* Splitter followed by merger returns the input channels (a statement about where each channel
  is copied from).

## What is tested only with `#guard`

Every statement about a `Float` value. `Float` is opaque to the kernel, so values are checked at
chosen points (cases from the Web Platform Tests are named at each one).

## Not done in this file

* Nothing of the delay line's channel-count change: when the input's count differs, the stored
  ring is up- or down-mixed with `Mix.apply` (`DelayState.retarget`, `interp` field).
* `AudioParam` automation and the summing of parameter inputs (the caller supplies `params`).
* The cycle rule is a field (`minFrames`); the graph module decides when it is `n`. In a cycle the
  minimum wins over `maxDelayTime` (the ring is sized for it, see `DelayState.init`).
* The ConstantSource `start`/`stop` control messages: here the frames are given.
-/

namespace L4Factoidal.WebAudio.Kernels

/-- A block: one `FloatArray` of `n` frames for each channel. -/
abbrev Block := Array FloatArray

/-! ## Loop and array helpers -/

/-- `iter step k i s` applies `step i`, `step (i+1)`, ... `step (i+k-1)` to `s` in order.
Structural recursion on `k`, a tail call. -/
@[specialize] def iter {σ : Type} (step : Nat → σ → σ) : Nat → Nat → σ → σ
  | 0, _, s => s
  | k + 1, i, s => iter step k (i + 1) (step i s)

/-- The constant 0 as a binary64 number. A `Float` literal inside an inlined function is
evaluated by `Float.ofScientific` at every call (about 1 microsecond: it parses a big integer
literal); a named constant is evaluated once. -/
@[noinline] def zeroF : Float := 0.0

@[simp] theorem zeroF_eq : zeroF = 0.0 := rfl

/-- Element `i` of `a`, or 0 outside the array. -/
@[inline] def getF (a : FloatArray) (i : Nat) : Float :=
  if i < a.size then a.get! i else zeroF

/-- A channel of `n` frames, frame `i` being `f i`. -/
@[specialize] def mkChan (n : Nat) (f : Nat → Float) : FloatArray :=
  iter (fun i (a : FloatArray) => a.push (f i)) n 0 ⟨#[]⟩

/-- `channels` channels of `n` frames of silence. -/
def silence (channels n : Nat) : Block :=
  Array.replicate channels (mkChan n (fun _ => 0.0))

/-- Value `i` of a parameter array: an a-rate array has `n` values; a k-rate array has one value,
constant over the block. An empty array reads as 0. -/
def paramAt (p : FloatArray) (i : Nat) : Float :=
  if p.size = 1 then getF p 0 else getF p i

/-- Every channel of the block has `n` frames. -/
def IsBlock (n : Nat) (b : Block) : Prop := ∀ c ∈ b, c.size = n

theorem size_push (a : FloatArray) (x : Float) : (a.push x).size = a.size + 1 := by
  cases a; simp [FloatArray.push, FloatArray.size]

theorem size_set! (a : FloatArray) (i : Nat) (x : Float) : (a.set! i x).size = a.size := by
  cases a; simp [FloatArray.set!, FloatArray.size]

theorem iter_push_size (f : Nat → Float) (k i : Nat) (a : FloatArray) :
    (iter (fun j (a : FloatArray) => a.push (f j)) k i a).size = a.size + k := by
  induction k generalizing i a with
  | zero => simp [iter]
  | succ k ih => simp only [iter, ih, size_push]; omega

/-- Says: `mkChan n f` has `n` frames. Does not say: anything about the values. -/
theorem mkChan_size (n : Nat) (f : Nat → Float) : (mkChan n f).size = n := by
  have := iter_push_size f n 0 ⟨#[]⟩
  simpa [mkChan, FloatArray.size] using this

/-- Says: `silence channels n` is a block of `channels` channels of `n` frames.
Does not say: that the frames are zero. -/
theorem silence_shape (channels n : Nat) :
    (silence channels n).size = channels ∧ IsBlock n (silence channels n) := by
  constructor
  · simp [silence]
  · intro c hc
    simp only [silence] at hc
    have := Array.eq_of_mem_replicate hc
    subst this; exact mkChan_size n _

/-- Channel `c` of block `b`, silent when the block has no such channel. -/
def chanOr (n : Nat) (b : Block) (c : Nat) : FloatArray :=
  if h : c < b.size then b[c] else mkChan n (fun _ => 0.0)

theorem chanOr_size (n : Nat) (b : Block) (hb : IsBlock n b) (c : Nat) :
    (chanOr n b c).size = n := by
  unfold chanOr
  split
  · exact hb _ (Array.getElem_mem _)
  · exact mkChan_size n _

/-! ## Scheduled sources (AudioScheduledSourceNode) -/

/-- First frame at or after time `t` seconds: frame `f` has time `f / sampleRate`.
The specification (`AudioScheduledSourceNode`: a source plays at times "greater or equal to the
time the node is set to start, and less than the time it is set to stop") gives both the start
frame and the stop frame as `ceil (t * sampleRate)`. Negative and non-finite values give 0. -/
def frameOfTime (t sampleRate : Float) : Nat :=
  let x := t * sampleRate
  if x > 0.0 then x.ceil.toUInt64.toNat else 0

/-- Whether a scheduled source outputs its signal at `frame`: it has been started, `frame` is not
before the start frame, and `frame` is before the stop frame when one is set. -/
def active (startFrame stopFrame : Option Nat) (frame : Nat) : Bool :=
  match startFrame with
  | none => false
  | some s => decide (s ≤ frame) && (match stopFrame with
      | none => true
      | some e => decide (frame < e))

/-- Says: a source is silent before its start frame. Does not say: anything about the signal
value after it. -/
theorem active_before_start (s : Nat) (stop : Option Nat) (f : Nat) (h : f < s) :
    active (some s) stop f = false := by
  simp [active, Nat.not_le.mpr h]

/-- Says: a source is silent at and after its stop frame. Does not say: what a stop frame earlier
than the start frame means (the source then never plays; both silent cases apply). -/
theorem active_at_or_after_stop (s e : Nat) (f : Nat) (h : e ≤ f) :
    active (some s) (some e) f = false := by
  simp [active, Nat.not_lt.mpr h]

/-- Says: between the start frame (inclusive) and the stop frame (exclusive, or no stop) the
source is active. Does not say: that the signal is non-zero. -/
theorem active_between (s : Nat) (stop : Option Nat) (f : Nat) (h1 : s ≤ f)
    (h2 : ∀ e, stop = some e → f < e) : active (some s) stop f = true := by
  cases stop with
  | none => simp [active, h1]
  | some e => simp [active, h1, h2 e rfl]

/-- Says: a source on which `start` was never called is silent. -/
theorem active_not_started (stop : Option Nat) (f : Nat) : active none stop f = false := by
  simp [active]

/-! ## GainNode

Section "The GainNode Interface": output is the input multiplied by the `gain` `AudioParam`,
for every channel. The output has the input's channel count. `params[0]` is `gain`. -/

/-- One output block with the input's channel count: `out[c][i] = in[c][i] * gain[i]`. -/
def gainProcess (n : Nat) (_ : Unit) (inputs : Array Block) (params : Array FloatArray) :
    Unit × Array Block :=
  let inp := inputs.getD 0 #[]
  let g := params.getD 0 ⟨#[]⟩
  let out : Block := Array.ofFn (n := inp.size) fun c =>
    mkChan n (fun i => getF (inp.getD c.1 ⟨#[]⟩) i * paramAt g i)
  ((), #[out])

/-- Says: the gain kernel returns one block, with the input's number of channels and `n` frames in
each. Does not say: the values. -/
theorem gain_shape (n : Nat) (inputs : Array Block) (params : Array FloatArray) :
    let o := (gainProcess n () inputs params).2
    o.size = 1 ∧ (∀ b ∈ o, b.size = (inputs.getD 0 #[]).size ∧ IsBlock n b) := by
  intro o
  refine ⟨by simp [o, gainProcess], ?_⟩
  intro b hb
  simp only [o, gainProcess, Array.mem_singleton] at hb
  subst hb
  refine ⟨by simp, ?_⟩
  intro c hc
  simp only [Array.mem_ofFn] at hc
  obtain ⟨j, rfl⟩ := hc
  exact mkChan_size n _

/-! ## ConstantSourceNode

Section "The ConstantSourceNode Interface": one output channel, value `offset` (a-rate), as an
`AudioScheduledSourceNode`: silence before the start frame and from the stop frame on.
`params[0]` is `offset`. -/

structure ConstState where
  startFrame : Option Nat := none
  stopFrame : Option Nat := none
  /-- Frames rendered so far (`currentFrame` of the node's first frame of the block). -/
  frame : Nat := 0

def constProcess (n : Nat) (s : ConstState) (_ : Array Block) (params : Array FloatArray) :
    ConstState × Array Block :=
  let off := params.getD 0 ⟨#[]⟩
  let ch := mkChan n fun i =>
    if active s.startFrame s.stopFrame (s.frame + i) then paramAt off i else 0.0
  ({ s with frame := s.frame + n }, #[#[ch]])

/-- Says: one output block of one channel of `n` frames; the frame counter advances by `n`.
Does not say: the values. -/
theorem const_shape (n : Nat) (s : ConstState) (inputs : Array Block) (params : Array FloatArray) :
    let r := constProcess n s inputs params
    r.2.size = 1 ∧ (∀ b ∈ r.2, b.size = 1 ∧ IsBlock n b) ∧ r.1.frame = s.frame + n := by
  intro r
  refine ⟨by simp [r, constProcess], ?_, by simp [r, constProcess]⟩
  intro b hb
  simp only [r, constProcess, Array.mem_singleton] at hb
  subst hb
  refine ⟨by simp, ?_⟩
  intro c hc
  simp only [Array.mem_singleton] at hc
  subst hc
  exact mkChan_size n _

/-! ## DelayNode

Section "The DelayNode Interface": `output(t) = input(t - delayTime(t))`; the output has the
input's channel count; `delayTime` is clamped to `[0, maxDelayTime]`, and to at least one render
quantum when the node is in a cycle (field `minFrames`, set by the graph).

The specification does not name an interpolation. This kernel uses linear interpolation between
the two stored samples that surround `t - delayTime(t)`, as WPT `delaynode-scheduling.html`
and `delaynode.html` accept. The ring buffer has `ceil (maxDelayTime * sampleRate) + 1`
frames per channel, so that the sample just written (delay 0) and the sample at the maximum delay
are both held. The sample is written before the read, so delay 0 returns the current input.
`params[0]` is `delayTime` in seconds. -/

structure DelayState where
  sampleRate : Float
  /-- `ceil (maxDelayTime * sampleRate)`: the largest delay in frames when the node is not in a
  cycle. -/
  maxFrames : Nat
  /-- Smallest delay in frames: 0, or `n` when the node is in a cycle. -/
  minFrames : Nat
  /-- `channelInterpretation` of the node: how stored samples are mixed when the input channel
  count changes. -/
  interp : Mix.Interpretation := .speakers
  /-- Frames in each channel's ring buffer. -/
  size : Nat
  /-- Index the next input frame is written to. -/
  w : Nat
  /-- One ring buffer per channel. -/
  bufs : Array FloatArray

/-- Initial state: `channels` silent ring buffers. The ring has `max (ceil (maxDelayTime * rate))
quantum + 1` frames: a delay in a cycle reads at least one render quantum back even when that is
above `maxDelayTime` (specification: "clamped to a minimum of one render quantum"), so the ring
must hold `quantum` frames. `Render` passes its quantum; the default 0 gives the plain
`ceil (maxDelayTime * rate) + 1`. -/
def DelayState.init (maxDelayTime sampleRate : Float) (channels : Nat) (minFrames : Nat := 0)
    (quantum : Nat := 0) : DelayState :=
  let mx := frameOfTime maxDelayTime sampleRate
  let sz := max mx quantum + 1
  { sampleRate, maxFrames := mx, minFrames, size := sz, w := 0
    bufs := Array.replicate channels (mkChan sz (fun _ => 0.0)) }

/-- The invariant: positive size, write index below the size, every buffer of `size` frames. -/
def DelayState.WF (s : DelayState) : Prop :=
  0 < s.size ∧ s.w < s.size ∧ ∀ b ∈ s.bufs, b.size = s.size

/-- Delay in frames: non-finite or negative gives the lower bound, then at most `hi`. -/
def clampDelay (d : Float) (lo hi : Nat) : Float :=
  let a := if d ≥ lo.toFloat then d else lo.toFloat
  if a ≤ hi.toFloat then a else hi.toFloat

/-- One step of `delayChan`: write input frame `i`, then read the delayed frame. -/
def delayStep (S w : Nat) (sr : Float) (minF hiF : Nat) (dly inp : FloatArray) (i : Nat)
    (p : FloatArray × FloatArray) : FloatArray × FloatArray :=
  let pos := (w + i) % S
  let buf1 := p.1.set! pos (getF inp i)
  let d := clampDelay (paramAt dly i * sr) minF (min hiF (S - 1))
  let k := d.floor.toUInt64.toNat
  let fr := d - d.floor
  let a := getF buf1 ((pos + S - k) % S)
  let b := getF buf1 ((pos + S - k - 1) % S)
  (buf1, p.2.push (a * (1.0 - fr) + b * fr))

/-- One channel of one block. Writes `inp` into the ring `buf` starting at `w` and returns the new
ring and the output channel. -/
def delayChan (n S w : Nat) (sr : Float) (minF hiF : Nat) (dly inp buf : FloatArray) :
    FloatArray × FloatArray :=
  iter (delayStep S w sr minF hiF dly inp) n 0 (buf, ⟨#[]⟩)

/-- The ring buffers as `channels` channels. When the count differs from the stored one, the whole
ring is up- or down-mixed (all `size` frames) by `Mix.apply` with the node's `interp`, so that all
internal delay-line mixing uses the prevailing channel layout (DelayNode section). -/
def DelayState.retarget (s : DelayState) (channels : Nat) : Array FloatArray :=
  if channels == s.bufs.size then s.bufs
  else Mix.apply (Mix.matrix s.interp s.bufs.size channels) s.bufs s.size

def delayProcess (n : Nat) (s : DelayState) (inputs : Array Block) (params : Array FloatArray) :
    DelayState × Array Block :=
  let inp := inputs.getD 0 #[]
  let dly := params.getD 0 ⟨#[]⟩
  let bufs := s.retarget (inputs.getD 0 #[]).size
  let hiF := max s.maxFrames s.minFrames
  let res : Array (FloatArray × FloatArray) := Array.ofFn (n := inp.size) fun c =>
    delayChan n s.size s.w s.sampleRate s.minFrames hiF dly (inp.getD c.1 ⟨#[]⟩)
      (bufs.getD c.1 (mkChan s.size (fun _ => 0.0)))
  ({ s with w := (s.w + n) % s.size, bufs := res.map Prod.fst }, #[res.map Prod.snd])

theorem delayIter_sizes (S w : Nat) (sr : Float) (minF hiF : Nat) (dly inp : FloatArray)
    (k i : Nat) (p : FloatArray × FloatArray) :
    (iter (delayStep S w sr minF hiF dly inp) k i p).1.size = p.1.size ∧
    (iter (delayStep S w sr minF hiF dly inp) k i p).2.size = p.2.size + k := by
  induction k generalizing i p with
  | zero => simp [iter]
  | succ k ih =>
    simp only [iter]
    have h1 : (delayStep S w sr minF hiF dly inp i p).1.size = p.1.size := by
      simp [delayStep, size_set!]
    have h2 : (delayStep S w sr minF hiF dly inp i p).2.size = p.2.size + 1 := by
      simp [delayStep, size_push]
    have := ih (i + 1) (delayStep S w sr minF hiF dly inp i p)
    omega

theorem delayChan_sizes (n S w : Nat) (sr : Float) (minF hiF : Nat) (dly inp buf : FloatArray) :
    (delayChan n S w sr minF hiF dly inp buf).1.size = buf.size ∧
    (delayChan n S w sr minF hiF dly inp buf).2.size = n := by
  have := delayIter_sizes S w sr minF hiF dly inp n 0 (buf, ⟨#[]⟩)
  unfold delayChan
  simp only [FloatArray.size] at this ⊢
  simpa using this

/-- Says: for a well-formed state, `delayProcess` keeps the ring-buffer size, keeps the write index
below it, and keeps every channel's ring at that size. Does not say: that the ring holds the right
samples (that is tested with `#guard`), or anything when the state is not well-formed. -/
theorem delay_state_wf (n : Nat) (s : DelayState) (hs : s.WF) (inputs : Array Block)
    (params : Array FloatArray) :
    (delayProcess n s inputs params).1.size = s.size ∧ (delayProcess n s inputs params).1.WF := by
  obtain ⟨h0, hw, hb⟩ := hs
  have hsz : (delayProcess n s inputs params).1.size = s.size := rfl
  refine ⟨hsz, ?_⟩
  refine ⟨by rw [hsz]; exact h0, ?_, ?_⟩
  · show (s.w + n) % s.size < (delayProcess n s inputs params).1.size
    rw [hsz]; exact Nat.mod_lt _ h0
  · intro b hbm
    simp only [delayProcess, Array.mem_map, Array.mem_ofFn] at hbm
    obtain ⟨p, ⟨j, rfl⟩, rfl⟩ := hbm
    rw [(delayChan_sizes ..).1]
    show _ = s.size
    have hr : ∀ x ∈ s.retarget (inputs.getD 0 #[]).size, x.size = s.size := by
      intro x hx
      unfold DelayState.retarget at hx
      split at hx
      · exact hb x hx
      · exact Mix.apply_shape _ _ _ x hx
    rw [Array.getD_eq_getD_getElem?]
    cases h : (s.retarget (inputs.getD 0 #[]).size)[j.1]? with
    | none => simpa using mkChan_size s.size _
    | some x =>
      simp only [Option.getD_some]
      exact hr x (Array.mem_of_getElem? h)

/-- Says: one output block, with the input's channel count and `n` frames in each channel.
Does not say: the values. -/
theorem delay_shape (n : Nat) (s : DelayState) (inputs : Array Block) (params : Array FloatArray) :
    let o := (delayProcess n s inputs params).2
    o.size = 1 ∧ (∀ b ∈ o, b.size = (inputs.getD 0 #[]).size ∧ IsBlock n b) := by
  intro o
  refine ⟨by simp [o, delayProcess], ?_⟩
  intro b hb
  simp only [o, delayProcess, Array.mem_singleton] at hb
  subst hb
  refine ⟨by simp, ?_⟩
  intro c hc
  simp only [Array.mem_map, Array.mem_ofFn] at hc
  obtain ⟨p, ⟨j, rfl⟩, rfl⟩ := hc
  exact (delayChan_sizes ..).2

/-! ## StereoPannerNode

Section "StereoPannerNode Panning" (in "Spatialization / Panning Algorithm"): `pan` is clamped
to [-1, 1]; for mono input `x = (pan + 1) / 2`; for stereo input `x = pan + 1` if `pan <= 0`
and `x = pan` otherwise; `gainL = cos (x * pi / 2)`, `gainR = sin (x * pi / 2)`. Mono:
`outL = in * gainL`, `outR = in * gainR`. Stereo, `pan <= 0`: `outL = inL + inR * gainL`,
`outR = inR * gainR`; else `outL = inL * gainL`, `outR = inR + inL * gainR`.
The output always has 2 channels. An input of one channel is mono; any other count is read as
stereo (channels 0 and 1, a missing channel silent): the caller mixes to 1 or 2 channels.
`params[0]` is `pan` (a-rate). -/

def pi : Float := 3.141592653589793

def clampPan (p : Float) : Float :=
  if p.isNaN then 0.0 else if p < -1.0 then -1.0 else if p > 1.0 then 1.0 else p

/-- Left and right output frame for input frames `l`, `r` (for mono, `r` is unused) at `pan`. -/
def panFrame (mono : Bool) (pan l r : Float) : Float × Float :=
  let p := clampPan pan
  if mono then
    let x := (p + 1.0) / 2.0
    (l * Float.cos (x * pi / 2.0), l * Float.sin (x * pi / 2.0))
  else
    let x := if p ≤ 0.0 then p + 1.0 else p
    let gl := Float.cos (x * pi / 2.0)
    let gr := Float.sin (x * pi / 2.0)
    if p ≤ 0.0 then (l + r * gl, r * gr) else (l * gl, r + l * gr)

def panProcess (n : Nat) (_ : Unit) (inputs : Array Block) (params : Array FloatArray) :
    Unit × Array Block :=
  let inp := inputs.getD 0 #[]
  let pn := params.getD 0 ⟨#[]⟩
  let mono := decide (inp.size = 1)
  let a := inp.getD 0 ⟨#[]⟩
  let b := inp.getD 1 ⟨#[]⟩
  let left := mkChan n fun i => (panFrame mono (paramAt pn i) (getF a i) (getF b i)).1
  let right := mkChan n fun i => (panFrame mono (paramAt pn i) (getF a i) (getF b i)).2
  ((), #[#[left, right]])

/-- Says: one output block of 2 channels of `n` frames, for any input. Does not say: the values. -/
theorem pan_shape (n : Nat) (inputs : Array Block) (params : Array FloatArray) :
    let o := (panProcess n () inputs params).2
    o.size = 1 ∧ (∀ b ∈ o, b.size = 2 ∧ IsBlock n b) := by
  intro o
  refine ⟨by simp [o, panProcess], ?_⟩
  intro b hb
  simp only [o, panProcess, Array.mem_singleton] at hb
  subst hb
  refine ⟨by simp, ?_⟩
  intro c hc
  simp at hc
  rcases hc with rfl | rfl <;> exact mkChan_size n _

/-! ## ChannelSplitterNode

Section "The ChannelSplitterNode Interface": one input, `numberOfOutputs` outputs (default 6),
each mono. Output `k` carries input channel `k`; an output with no input channel is silent. -/

def splitProcess (n : Nat) (outputs : Nat) (inputs : Array Block) (_ : Array FloatArray) :
    Nat × Array Block :=
  let inp := inputs.getD 0 #[]
  (outputs, Array.ofFn (n := outputs) fun k => #[chanOr n inp k.1])

/-- Says: `outputs` blocks of one channel each, `n` frames each, when the input channels have `n`
frames. Does not say: which input channel feeds which output (see `split_merge_roundtrip`). -/
theorem split_shape (n outputs : Nat) (inputs : Array Block) (ps : Array FloatArray)
    (hin : IsBlock n (inputs.getD 0 #[])) :
    let o := (splitProcess n outputs inputs ps).2
    o.size = outputs ∧ (∀ b ∈ o, b.size = 1 ∧ IsBlock n b) := by
  intro o
  refine ⟨by simp [o, splitProcess], ?_⟩
  intro b hb
  simp only [o, splitProcess, Array.mem_ofFn] at hb
  obtain ⟨k, rfl⟩ := hb
  refine ⟨by simp, ?_⟩
  intro c hc
  simp only [Array.mem_singleton] at hc
  subst hc
  exact chanOr_size n _ hin _

/-! ## ChannelMergerNode

Section "The ChannelMergerNode Interface": `numberOfInputs` inputs (default 6), each mono (the
caller down-mixes), one output of `numberOfInputs` channels; channel `k` is input `k`; an
unconnected input contributes silence. -/

def mergeProcess (n : Nat) (inputsN : Nat) (inputs : Array Block) (_ : Array FloatArray) :
    Nat × Array Block :=
  (inputsN, #[Array.ofFn (n := inputsN) fun k => chanOr n (inputs.getD k.1 #[]) 0])

/-- Says: one output block of `inputsN` channels of `n` frames, when each input has channels of `n`
frames. Does not say: the values. -/
theorem merge_shape (n inputsN : Nat) (inputs : Array Block) (ps : Array FloatArray)
    (hin : ∀ b ∈ inputs, IsBlock n b) :
    let o := (mergeProcess n inputsN inputs ps).2
    o.size = 1 ∧ (∀ b ∈ o, b.size = inputsN ∧ IsBlock n b) := by
  intro o
  refine ⟨by simp [o, mergeProcess], ?_⟩
  intro b hb
  simp only [o, mergeProcess, Array.mem_singleton] at hb
  subst hb
  refine ⟨by simp, ?_⟩
  intro c hc
  simp only [Array.mem_ofFn] at hc
  obtain ⟨k, rfl⟩ := hc
  refine chanOr_size n _ ?_ 0
  by_cases h : k.1 < inputs.size
  · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem h, Option.getD_some]
    exact hin _ (Array.getElem_mem h)
  · simp only [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (Nat.not_lt.mp h),
      Option.getD_none]
    intro c hc; simp at hc

/-- Says: feeding each splitter output to the merger input of the same index (`numberOfOutputs =
numberOfInputs = N`, input with exactly `N` channels) gives back the input's channels: the merged
block is the input block. Does not say: anything about an input with other than `N` channels, or
about timing. -/
theorem split_merge_roundtrip (n N : Nat) (inp : Block) (hN : inp.size = N)
    (ps : Array FloatArray) :
    (mergeProcess n N (splitProcess n N #[inp] ps).2 ps).2 = #[inp] := by
  simp only [mergeProcess, splitProcess]
  apply congrArg (fun x : Block => (#[x] : Array Block))
  apply Array.ext
  · simp [hN]
  · intro k h1 h2
    simp only [Array.getElem_ofFn]
    have hk : k < N := by simpa using h1
    have hk' : k < inp.size := by omega
    simp [chanOr, hk, hk']


/-! ## Tests on values

Each `#guard` evaluates the kernel on a small block and compares with the value the specification
gives. `approxB` compares to 1e-9. -/

section Tests

def L (a : FloatArray) : List Float := a.data.toList
def approxL (xs ys : List Float) : Bool :=
  xs.length == ys.length && (List.zip xs ys).all fun (x, y) => (x - y).abs < 1e-9
def blk (cs : List (List Float)) : Block := (cs.map fun c => FloatArray.mk c.toArray).toArray
def approxB (b : Block) (cs : List (List Float)) : Bool :=
  b.size == cs.length && (List.zip b.toList cs).all fun (x, y) => approxL (L x) y
def kr (v : Float) : FloatArray := ⟨#[v]⟩
def ar (xs : List Float) : FloatArray := ⟨xs.toArray⟩

def gainOut (n : Nat) (inp : Block) (g : FloatArray) : Block :=
  (gainProcess n () #[inp] #[g]).2[0]!

-- GainNode (WPT the-gainnode-interface/gain.html: output is input times gain).
#guard approxB (gainOut 4 (blk [[1, 2, 3, 4]]) (kr 2.0)) [[2, 4, 6, 8]]
#guard approxB (gainOut 4 (blk [[1, 1, 1, 1]]) (ar [0, 1, 2, 3])) [[0, 1, 2, 3]]
#guard approxB (gainOut 3 (blk [[1, 2, 3], [4, 5, 6]]) (kr 0.5)) [[0.5, 1, 1.5], [2, 2.5, 3]]
#guard approxB (gainOut 3 (blk [[1, 2, 3]]) (kr 0.0)) [[0, 0, 0]]
#guard approxB (gainOut 3 (blk [[1, 2, 3]]) (kr (-1.0))) [[-1, -2, -3]]
#guard approxB (gainOut 2 (blk []) (kr 1.0)) []

-- paramAt, silence
#guard paramAt (kr 7.0) 3 == 7.0
#guard paramAt (ar [1, 2, 3]) 2 == 3.0
#guard approxB (silence 2 3) [[0, 0, 0], [0, 0, 0]]

-- Scheduled sources: frameOfTime (frame f has time f / sampleRate; first frame at or after t).
#guard frameOfTime 0.5 4.0 == 2
#guard frameOfTime 0.3 10.0 == 3
#guard frameOfTime 0.0 44100.0 == 0
#guard frameOfTime (-1.0) 44100.0 == 0
#guard frameOfTime 0.26 10.0 == 3

#guard active (some 2) (some 5) 1 == false
#guard active (some 2) (some 5) 2 == true
#guard active (some 2) (some 5) 4 == true
#guard active (some 2) (some 5) 5 == false
#guard active none none 100 == false
#guard active (some 2) none 1000 == true

-- ConstantSourceNode (WPT the-constantsourcenode-interface).
def constOut (n : Nat) (s : ConstState) (off : FloatArray) : ConstState × Block :=
  let r := constProcess n s #[] #[off]
  (r.1, r.2[0]!)

-- starts and stops inside one block
#guard approxB (constOut 4 { startFrame := some 1, stopFrame := some 3 } (kr 5.0)).2 [[0, 5, 5, 0]]
-- a-rate offset
#guard approxB (constOut 4 { startFrame := some 0 } (ar [1, 2, 3, 4])).2 [[1, 2, 3, 4]]
-- never started
#guard approxB (constOut 4 {} (kr 5.0)).2 [[0, 0, 0, 0]]
-- start in the second block; the frame counter carries over
#guard (constOut 4 { startFrame := some 6 } (kr 1.0)).1.frame == 4
#guard approxB (constOut 4 (constOut 4 { startFrame := some 6 } (kr 1.0)).1 (kr 1.0)).2
  [[0, 0, 1, 1]]
-- stop in the second block
#guard approxB (constOut 4 { startFrame := some 0, stopFrame := some 5, frame := 4 } (kr 2.0)).2
  [[2, 0, 0, 0]]

-- DelayNode: sample rate 1, so delayTime in seconds equals frames. Maximum delay 4 frames.
def dly0 : DelayState := DelayState.init 4.0 1.0 1
def delayRun (n : Nat) (s : DelayState) (inp : Block) (d : FloatArray) : DelayState × Block :=
  let r := delayProcess n s #[inp] #[d]
  (r.1, r.2[0]!)
def impulse8 : Block := blk [[1, 0, 0, 0, 0, 0, 0, 0]]

#guard dly0.size == 5
#guard (DelayState.init 1.0 44100.0 2).size == 44101
#guard (DelayState.init 1.0 44100.0 2).bufs.size == 2
-- delay 0 gives the current input
#guard approxB (delayRun 8 dly0 impulse8 (kr 0.0)).2 [[1, 0, 0, 0, 0, 0, 0, 0]]
-- delay 1
#guard approxB (delayRun 8 dly0 impulse8 (kr 1.0)).2 [[0, 1, 0, 0, 0, 0, 0, 0]]
-- delay 2
#guard approxB (delayRun 8 dly0 impulse8 (kr 2.0)).2 [[0, 0, 1, 0, 0, 0, 0, 0]]
-- fractional delay 0.5: linear interpolation
#guard approxB (delayRun 8 dly0 impulse8 (kr 0.5)).2 [[0.5, 0.5, 0, 0, 0, 0, 0, 0]]
#guard approxB (delayRun 8 dly0 impulse8 (kr 1.25)).2 [[0, 0.75, 0.25, 0, 0, 0, 0, 0]]
-- maximum delay
#guard approxB (delayRun 8 dly0 impulse8 (kr 4.0)).2 [[0, 0, 0, 0, 1, 0, 0, 0]]
-- above the maximum is clamped to it; negative is clamped to 0
#guard approxB (delayRun 8 dly0 impulse8 (kr 10.0)).2 [[0, 0, 0, 0, 1, 0, 0, 0]]
#guard approxB (delayRun 8 dly0 impulse8 (kr (-3.0))).2 [[1, 0, 0, 0, 0, 0, 0, 0]]
-- a-rate delay time
#guard approxB (delayRun 4 dly0 (blk [[1, 2, 3, 4]]) (ar [0, 1, 1, 2])).2 [[1, 1, 2, 2]]
-- state across blocks: ring of 7 frames wraps (write index 0, 4, 1)
def dly6 : DelayState := DelayState.init 6.0 1.0 1
#guard approxB (delayRun 4 (delayRun 4 dly6 (blk [[1, 0, 0, 0]]) (kr 5.0)).1
    (blk [[0, 0, 0, 0]]) (kr 5.0)).2 [[0, 1, 0, 0]]
#guard (delayRun 4 (delayRun 4 dly6 (blk [[1, 0, 0, 0]]) (kr 5.0)).1
    (blk [[0, 0, 0, 0]]) (kr 5.0)).1.w == 1
-- in a cycle the delay is at least one render quantum (4 frames here)
def dlyCycle : DelayState := DelayState.init 6.0 1.0 1 4
#guard approxB (delayRun 4 dlyCycle (blk [[1, 0, 0, 0]]) (kr 0.0)).2 [[0, 0, 0, 0]]
#guard approxB (delayRun 4 (delayRun 4 dlyCycle (blk [[1, 0, 0, 0]]) (kr 0.0)).1
    (blk [[0, 0, 0, 0]]) (kr 0.0)).2 [[1, 0, 0, 0]]
-- cycle with maxDelayTime (2 frames) below the quantum (4 frames): the minimum wins, so the delay
-- is 4 frames even though 10 frames are asked for (specification: minimum of one render quantum)
def dlyTiny : DelayState := DelayState.init 2.0 1.0 1 4 4
#guard dlyTiny.size == 5 && dlyTiny.maxFrames == 2
#guard approxB (delayRun 4 dlyTiny (blk [[1, 0, 0, 0]]) (kr 10.0)).2 [[0, 0, 0, 0]]
#guard approxB (delayRun 4 (delayRun 4 dlyTiny (blk [[1, 0, 0, 0]]) (kr 10.0)).1
    (blk [[0, 0, 0, 0]]) (kr 10.0)).2 [[1, 0, 0, 0]]
-- the same node outside a cycle: the maximum (2 frames) still bounds the delay
#guard approxB (delayRun 4 { dlyTiny with minFrames := 0 } (blk [[1, 0, 0, 0]]) (kr 10.0)).2
  [[0, 0, 1, 0]]
-- the input channel count changes: stored samples are mixed to the new layout
-- mono ring holding an impulse, then a stereo input: speakers up-mix 1 to 2, both channels
def dlyMono : DelayState :=
  (delayRun 2 (DelayState.init 4.0 1.0 1) (blk [[1, 0]]) (kr 3.0)).1
#guard approxB (delayRun 2 dlyMono (blk [[0, 0], [0, 0]]) (kr 3.0)).2 [[0, 1], [0, 1]]
-- stereo ring holding (1, 3), then a mono input: speakers down-mix averages to 2
def dlyStereo : DelayState :=
  (delayRun 2 (DelayState.init 4.0 1.0 2) (blk [[1, 0], [3, 0]]) (kr 3.0)).1
#guard approxB (delayRun 2 dlyStereo (blk [[0, 0]]) (kr 3.0)).2 [[0, 2]]
-- discrete 2 to 1 keeps channel 0
#guard approxB (delayRun 2 { dlyStereo with interp := .discrete } (blk [[0, 0]]) (kr 3.0)).2
  [[0, 1]]
-- an unchanged channel count leaves the ring alone
#guard approxB (delayRun 2 dlyStereo (blk [[0, 0], [0, 0]]) (kr 3.0)).2 [[0, 1], [0, 3]]
-- output channel count follows the input; channels are independent
#guard approxB (delayRun 3 (DelayState.init 4.0 1.0 2) (blk [[1, 2, 3], [4, 5, 6]]) (kr 1.0)).2
  [[0, 1, 2], [0, 4, 5]]
-- the delay line keeps its tail when the input is silent afterwards
#guard approxB (delayRun 2 (delayRun 2 dly0 (blk [[7, 8]]) (kr 3.0)).1 (blk [[0, 0]]) (kr 3.0)).2
  [[0, 7]]

-- StereoPannerNode (WPT stereopanner-testing.js getChannelGain: same formulas).
def panOut (n : Nat) (inp : Block) (p : FloatArray) : Block :=
  (panProcess n () #[inp] #[p]).2[0]!
def sq : Float := 0.7071067811865476
-- mono input of 1.0: left gain cos, right gain sin
#guard approxB (panOut 1 (blk [[1]]) (kr (-1.0))) [[1], [0]]
#guard approxB (panOut 1 (blk [[1]]) (kr 0.0)) [[sq], [sq]]
#guard approxB (panOut 1 (blk [[1]]) (kr 1.0)) [[0], [1]]
-- pan beyond the range is clamped
#guard approxB (panOut 1 (blk [[1]]) (kr (-3.0))) [[1], [0]]
#guard approxB (panOut 1 (blk [[1]]) (kr 7.0)) [[0], [1]]
-- stereo input of (1, 1): pan <= 0 gives L = 1 + cos, R = sin
#guard approxB (panOut 1 (blk [[1], [1]]) (kr (-1.0))) [[2], [0]]
#guard approxB (panOut 1 (blk [[1], [1]]) (kr 0.0)) [[1], [1]]
#guard approxB (panOut 1 (blk [[1], [1]]) (kr 1.0)) [[0], [2]]
-- stereo input (1, 0) panned right: L = in L * cos, R = inR + inL * sin
#guard approxB (panOut 1 (blk [[1], [0]]) (kr 0.5)) [[0.7071067811865476], [0.7071067811865476]]
-- a-rate pan over three frames
#guard approxB (panOut 3 (blk [[1, 1, 1]]) (ar [-1, 0, 1])) [[1, sq, 0], [0, sq, 1]]

-- ChannelSplitterNode.
def splitOut (n outputs : Nat) (inp : Block) : Array Block :=
  (splitProcess n outputs #[inp] #[]).2
def twoCh : Block := blk [[1, 2], [3, 4]]
#guard (splitOut 2 3 twoCh).size == 3
#guard approxB (splitOut 2 3 twoCh)[0]! [[1, 2]]
#guard approxB (splitOut 2 3 twoCh)[1]! [[3, 4]]
-- more outputs than channels: the extra output is silent
#guard approxB (splitOut 2 3 twoCh)[2]! [[0, 0]]
-- fewer outputs than channels: the extra channels are dropped
#guard (splitOut 2 1 twoCh).size == 1
#guard approxB (splitOut 2 1 twoCh)[0]! [[1, 2]]
#guard (splitOut 2 0 twoCh).size == 0

-- ChannelMergerNode.
def mergeOut (n inputsN : Nat) (ins : Array Block) : Block :=
  (mergeProcess n inputsN ins #[]).2[0]!
#guard approxB (mergeOut 2 2 #[blk [[1, 2]], blk [[3, 4]]]) [[1, 2], [3, 4]]
-- an unconnected input (no channels) gives silence
#guard approxB (mergeOut 2 3 #[blk [[1, 2]], blk [], blk [[5, 6]]]) [[1, 2], [0, 0], [5, 6]]
-- more inputs than the node has: the extra inputs are ignored
#guard approxB (mergeOut 2 1 #[blk [[1, 2]], blk [[3, 4]]]) [[1, 2]]
-- more node inputs than supplied blocks: silent channels
#guard approxB (mergeOut 2 3 #[blk [[1, 2]]]) [[1, 2], [0, 0], [0, 0]]

-- Splitter then merger returns the input (value form of `split_merge_roundtrip`).
#guard approxB (mergeProcess 2 2 (splitProcess 2 2 #[twoCh] #[]).2 #[]).2[0]! [[1, 2], [3, 4]]
-- with a mono input and 3 outputs and 3 inputs: channel 0 is kept, the others silent
#guard approxB (mergeProcess 2 3 (splitProcess 2 3 #[blk [[9, 8]]] #[]).2 #[]).2[0]!
  [[9, 8], [0, 0], [0, 0]]

end Tests

end L4Factoidal.WebAudio.Kernels
