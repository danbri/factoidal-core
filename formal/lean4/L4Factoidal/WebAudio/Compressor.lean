import L4Factoidal.WebAudio.Kernels

/-!
# Web Audio `DynamicsCompressorNode` kernel

Section 1.19 of the W3C Web Audio API (https://webaudio.github.io/web-audio-api/). Stage F of
https://github.com/danbri/factoidal-core/issues/1169. Pure Lean, binary64 `Float`; every loop over
frames is `Kernels.iter` (a tail call). A block is `Kernels.Block`.

## Structure (from the specification)

* Signal path: input, pre-delay of 0.006 s, gain, output. The envelope follower reads the input
  (not the delayed signal), so the gain reacts 0.006 s before the loud part arrives.
* Detector: the largest absolute value over the channels of each frame (linked channels).
* Static curve on linear amplitude: identity up to the threshold, a soft knee of `knee` dB above
  it, then a straight line in dB; knee 0 is a hard knee.
* Detector average `D`, compressor gain `G` with attack and release, makeup gain, and `reduction`
  (dB) read after each block. `reduction` is 0 before any signal.
* Parameters (all k-rate): `threshold` (-24 dB, range -100 to 0), `knee` (30 dB, 0 to 40),
  `ratio` (12, 1 to 20), `attack` (0.003 s, 0 to 1), `release` (0.25 s, 0 to 1), `makeupGain`
  (0 dB). A value outside its nominal range is clamped; NaN reads as the default.
  `makeupGain` is read only when the makeup is not automatic.

## Choices the specification leaves to the implementation

Each line names its source: SPEC (the draft says it), CHROMIUM (Chromium's
`DynamicsCompressorKernel` design, from memory), OURS (a choice made here).

* Pre-delay length: `ceil (0.006 * sampleRate)` frames, at least 1 (SPEC: 0.006 s; OURS: the
  rounding, with a tolerance of 1e-6 frame so that 0.006 * 48000 gives 288). The ring is read
  before it is written, so the delay is exactly its size.
* Soft knee (CHROMIUM): `kneeCurve x = x` below `linearThreshold`, and
  `linearThreshold + (1 - exp (-k (x - linearThreshold))) / k` from there to the knee end
  `K = 10^((threshold + knee) / 20)`. `k` is found by bisection (40 steps, geometric mean, range
  0.1 to 10000) so that the slope at `K`, which is `exp (-k (K - linearThreshold))`, equals
  `1 / ratio`. The knee starts at the threshold and ends at `threshold + knee` dB.
* Above the knee (CHROMIUM): a line in dB with slope `1 / ratio`, through the knee curve's value
  at `K`. Continuous at `K` by construction. (The draft's text `f x = x / ratio` is a rough
  statement; its curve is only required to be continuous and increasing.)
* Ratio 1 is the identity curve (OURS: so that a ratio of 1 never changes the signal).
* Automatic makeup (CHROMIUM): `(1 / curve 1.0)^0.6`, in dB `-0.6 * dB(curve 1.0)`. (SPEC: "computed
  from the curve", no formula given.)
* Gain target per frame (CHROMIUM): `a = curve x / x`, clamped to [0, 1]; `a = 1` when `x < 0.0001`.
* Detector `D` (OURS, in the spirit of the draft's "detector average"): `D = a` at once when `a`
  is below `D` (the attack is left to `G`; the pre-delay gives the look-ahead), else
  `D + (a - D) * rd` with `rd` the per-frame rate of a 1 ms time constant. The draft starts at
  D = 0; we start at D = 1 because with D = 0 the gain would fall on silence.
* Gain `G` (CHROMIUM-like, simplified; no adaptive release zones): `G + (D - G) * rate`, with the
  attack rate when `D < G` and the release rate otherwise. A rate is `1 - exp (-1 / (t * sampleRate))`
  for time `t` seconds, and 1 when `t * sampleRate <= 1` (so attack 0 reaches the target in one
  frame). `G` starts at 1.
* Output gain at frame `i`: `G_i * makeupLinear` (SPEC), applied to the delayed signal.
* Metering (CHROMIUM): `reduction` is `20 log10 G` after the last frame of the block, without
  the makeup gain, so it is at most 0. A value of 0 or below in linear gives -1000 dB (SPEC).
* Parameters are read once per block (k-rate), at index 0.

## What is proved

Output shape; the ring size and write index stay valid; `reduction` of a new state is 0.
Everything about values is checked with `#guard`.

## Not done

Adaptive release zones and the sat-release curve of Chromium (the release is one exponential);
a-rate parameters (the draft makes them k-rate only); `channelCount` and mode checks (the page
layer); tail time (the node has the 0.006 s latency only).
-/

namespace L4Factoidal.WebAudio.Compressor

open L4Factoidal.WebAudio.Kernels

/-- ln 10 (a 16-digit literal, so a named constant). -/
@[noinline] def ln10 : Float := 2.302585092994046

/-- 20 log10 of `v`; `v <= 0` (or NaN) and results below -1000 give -1000. -/
def linearToDb (v : Float) : Float :=
  if v > 0.0 then
    let d := 20.0 * Float.log v / ln10
    if d < -1000.0 then -1000.0 else d
  else -1000.0

/-- `10^(db / 20)`. -/
def dbToLinear (db : Float) : Float := Float.exp (db * ln10 / 20.0)

/-- Clamp to `[lo, hi]`; NaN gives `dflt`. -/
def clampP (x lo hi dflt : Float) : Float :=
  if x != x then dflt else if x < lo then lo else if x > hi then hi else x

/-! ## The static curve -/

/-- The static curve, precomputed from threshold, knee and ratio. -/
structure Curve where
  /-- Linear threshold `10^(threshold/20)`. -/
  lt : Float
  /-- Linear knee end `10^((threshold+knee)/20)`. -/
  ke : Float
  /-- Knee end in dB. -/
  kneeDb : Float
  /-- The knee's rate constant. -/
  k : Float
  /-- The curve's value at the knee end, in dB. -/
  yKneeDb : Float
  /-- Slope above the knee in dB, `1 / ratio`. -/
  slope : Float
  /-- Ratio 1: the identity. -/
  ident : Bool
  deriving Inhabited

/-- The soft-knee piece (Chromium). -/
def kneeCurve (lt k x : Float) : Float :=
  if x < lt then x else lt + (1.0 - Float.exp (-k * (x - lt))) / k

/-- `k` such that the slope `exp (-k (ke - lt))` at the knee end is `desired` (bisection, 40 steps,
geometric mean). -/
def kAtSlope (lt ke desired : Float) : Float :=
  let r := iter (fun _ (p : Float × Float) =>
      let k := Float.sqrt (p.1 * p.2)
      if Float.exp (-k * (ke - lt)) < desired then (p.1, k) else (k, p.2)) 40 0 (0.1, 10000.0)
  Float.sqrt (r.1 * r.2)

/-- Build the curve. Parameters are clamped to their nominal ranges. -/
def Curve.make (threshold knee ratio : Float) : Curve :=
  let thr := clampP threshold (-100.0) 0.0 (-24.0)
  let kn := clampP knee 0.0 40.0 30.0
  let ra := clampP ratio 1.0 20.0 12.0
  let lt := dbToLinear thr
  let ke := dbToLinear (thr + kn)
  let soft := kn > 0.0 && ke > lt
  let k := if soft then kAtSlope lt ke (1.0 / ra) else 1.0
  { lt, ke, kneeDb := thr + kn, k, yKneeDb := linearToDb (kneeCurve lt k ke)
    slope := 1.0 / ra, ident := ra <= 1.0 }

/-- The static curve on linear amplitude. -/
def Curve.eval (c : Curve) (x : Float) : Float :=
  if c.ident then x
  else if x < c.ke then kneeCurve c.lt c.k x
  else dbToLinear (c.yKneeDb + c.slope * (linearToDb x - c.kneeDb))

/-- The static curve on linear amplitude, from the parameters. -/
def curve (threshold knee ratio : Float) (x : Float) : Float :=
  (Curve.make threshold knee ratio).eval x

/-- The automatic makeup gain in dB: `20 log10 ((1 / curve 1.0)^0.6)`. -/
def makeupGainDb (threshold knee ratio : Float) : Float :=
  let y := curve threshold knee ratio 1.0
  if y > 0.0 then -0.6 * linearToDb y else 0.0

/-! ## State -/

/-- Compressor state. `ringSize` is the pre-delay in frames; `rings` has one ring of `ringSize`
frames for each channel of the last block, `w` is the index the next input frame is written to. -/
structure State where
  sampleRate : Float
  ringSize : Nat
  w : Nat
  rings : Array FloatArray
  /-- Detector average. -/
  d : Float
  /-- Compressor gain. -/
  g : Float
  /-- The `reduction` attribute, dB. -/
  reduction : Float
  autoMakeup : Bool
  deriving Inhabited

/-- Pre-delay in frames: `ceil (0.006 * rate)` (tolerance 1e-6), between 1 and 2^20. -/
def ringFrames (sampleRate : Float) : Nat :=
  let x := 0.006 * sampleRate
  let r := x.round
  let c := if (x - r).abs < 0.000001 then r else x.ceil
  let n := if c > 0.0 then (if c < 1048576.0 then c.toUInt64.toNat else 1048576) else 0
  max 1 n

/-- A new state: one silent channel, `D = 1`, `G = 1`, `reduction = 0`. -/
def State.init (sampleRate : Float) (autoMakeup : Bool := true) : State :=
  let sz := ringFrames sampleRate
  { sampleRate, ringSize := sz, w := 0, rings := #[mkChan sz (fun _ => 0.0)]
    d := 1.0, g := 1.0, reduction := 0.0, autoMakeup }

/-- The invariant: positive size, write index below it, every ring of that size. -/
def State.WF (s : State) : Prop :=
  0 < s.ringSize ∧ s.w < s.ringSize ∧ ∀ b ∈ s.rings, b.size = s.ringSize

/-- The `reduction` attribute in dB. -/
def reduction (s : State) : Float := s.reduction

/-! ## Processing -/

/-- Per-frame rate of an exponential approach with time constant `t` seconds. -/
def rate (t sampleRate : Float) : Float :=
  let x := t * sampleRate
  if x <= 1.0 then 1.0 else 1.0 - Float.exp (-1.0 / x)

/-- Envelope loop state: detector average, gain, and the gain at each frame so far. -/
structure Env where
  d : Float
  g : Float
  gs : FloatArray

/-- The largest absolute value over the channels at frame `i`. -/
def detect (chans : Array FloatArray) (i : Nat) : Float :=
  chans.foldl (fun m ch => let v := (getF ch i).abs; if v > m then v else m) 0.0

/-- One frame of the envelope follower. -/
def envStep (c : Curve) (rd ra rr : Float) (chans : Array FloatArray) (i : Nat) (e : Env) : Env :=
  let x := detect chans i
  let a0 := if x < 0.0001 then 1.0 else c.eval x / x
  let a := if a0 != a0 then 1.0 else if a0 < 0.0 then 0.0 else if a0 > 1.0 then 1.0 else a0
  let d := if a < e.d then a else e.d + (a - e.d) * rd
  let g := if d < e.g then e.g + (d - e.g) * ra else e.g + (d - e.g) * rr
  { d, g, gs := e.gs.push g }

/-- One frame of one channel: read the delayed sample, write the input, scale. -/
def chanStep (S w : Nat) (mk : Float) (gs inp : FloatArray) (i : Nat)
    (p : FloatArray × FloatArray) : FloatArray × FloatArray :=
  let pos := (w + i) % S
  (p.1.set! pos (getF inp i), p.2.push (getF p.1 pos * getF gs i * mk))

/-- One channel of one block. -/
def chanBlock (n S w : Nat) (mk : Float) (gs inp ring : FloatArray) : FloatArray × FloatArray :=
  iter (chanStep S w mk gs inp) n 0 (ring, ⟨#[]⟩)

/-- A parameter's value, or its default when the array is absent or empty. -/
def pval (params : Array FloatArray) (i : Nat) (dflt : Float) : Float :=
  let p := params.getD i ⟨#[]⟩
  if p.size = 0 then dflt else paramAt p 0

/-- One block. `params` are threshold, knee, ratio, attack, release, makeupGain (k-rate). -/
def process (n : Nat) (s : State) (inputs : Array Block) (params : Array FloatArray) :
    State × Array Block :=
  let inp0 := inputs.getD 0 #[]
  let nch := max 1 inp0.size
  let chans : Array FloatArray := Array.ofFn (n := nch) fun c => inp0.getD c.1 ⟨#[]⟩
  let thr := pval params 0 (-24.0)
  let kn := pval params 1 30.0
  let ra := pval params 2 12.0
  let cv := Curve.make thr kn ra
  let attack := clampP (pval params 3 0.003) 0.0 1.0 0.003
  let release := clampP (pval params 4 0.25) 0.0 1.0 0.25
  let mkDb := if s.autoMakeup then makeupGainDb thr kn ra
    else clampP (pval params 5 0.0) (-1000.0) 771.0 0.0
  let mk := dbToLinear mkDb
  let rd := rate 0.001 s.sampleRate
  let env := iter (envStep cv rd (rate attack s.sampleRate) (rate release s.sampleRate) chans) n 0
    ({ d := s.d, g := s.g, gs := ⟨#[]⟩ } : Env)
  let res : Array (FloatArray × FloatArray) := Array.ofFn (n := nch) fun c =>
    chanBlock n s.ringSize s.w mk env.gs (chans.getD c.1 ⟨#[]⟩)
      (s.rings.getD c.1 (mkChan s.ringSize (fun _ => 0.0)))
  ({ s with w := (s.w + n) % s.ringSize, rings := res.map Prod.fst, d := env.d, g := env.g
            reduction := linearToDb env.g }, #[res.map Prod.snd])

/-! ## Theorems -/

theorem chanIter_sizes (S w : Nat) (mk : Float) (gs inp : FloatArray) (k i : Nat)
    (p : FloatArray × FloatArray) :
    (iter (chanStep S w mk gs inp) k i p).1.size = p.1.size ∧
    (iter (chanStep S w mk gs inp) k i p).2.size = p.2.size + k := by
  induction k generalizing i p with
  | zero => simp [iter]
  | succ k ih =>
    simp only [iter]
    have h1 : (chanStep S w mk gs inp i p).1.size = p.1.size := by
      simp [chanStep, size_set!]
    have h2 : (chanStep S w mk gs inp i p).2.size = p.2.size + 1 := by
      simp [chanStep, size_push]
    have := ih (i + 1) (chanStep S w mk gs inp i p)
    omega

theorem chanBlock_sizes (n S w : Nat) (mk : Float) (gs inp ring : FloatArray) :
    (chanBlock n S w mk gs inp ring).1.size = ring.size ∧
    (chanBlock n S w mk gs inp ring).2.size = n := by
  have := chanIter_sizes S w mk gs inp n 0 (ring, ⟨#[]⟩)
  unfold chanBlock
  simp only [FloatArray.size] at this ⊢
  simpa using this

/-- Says: for a well-formed state, `process` keeps the ring size and the write index below it, and
every ring at that size. Does not say: that the rings hold the right samples (`#guard`), or
anything for a state that is not well-formed. -/
theorem process_wf (n : Nat) (s : State) (hs : s.WF) (inputs : Array Block)
    (params : Array FloatArray) :
    (process n s inputs params).1.ringSize = s.ringSize ∧ (process n s inputs params).1.WF := by
  obtain ⟨h0, hw, hb⟩ := hs
  have hsz : (process n s inputs params).1.ringSize = s.ringSize := rfl
  refine ⟨hsz, ?_⟩
  refine ⟨by rw [hsz]; exact h0, ?_, ?_⟩
  · show (s.w + n) % s.ringSize < (process n s inputs params).1.ringSize
    rw [hsz]; exact Nat.mod_lt _ h0
  · intro b hbm
    simp only [process, Array.mem_map, Array.mem_ofFn] at hbm
    obtain ⟨p, ⟨j, rfl⟩, rfl⟩ := hbm
    rw [(chanBlock_sizes ..).1]
    show _ = s.ringSize
    rw [Array.getD_eq_getD_getElem?]
    cases h : s.rings[j.1]? with
    | none => simpa using mkChan_size s.ringSize _
    | some x =>
      simp only [Option.getD_some]
      exact hb x (Array.mem_of_getElem? h)

/-- Says: one output block, with `max 1` of the input's channel count as its channel count, and
`n` frames in each channel. Does not say: the values. -/
theorem process_shape (n : Nat) (s : State) (inputs : Array Block) (params : Array FloatArray) :
    let o := (process n s inputs params).2
    o.size = 1 ∧ (∀ b ∈ o, b.size = max 1 (inputs.getD 0 #[]).size ∧ IsBlock n b) := by
  intro o
  refine ⟨by simp [o, process], ?_⟩
  intro b hb
  simp only [o, process, Array.mem_singleton] at hb
  subst hb
  refine ⟨by simp, ?_⟩
  intro c hc
  simp only [Array.mem_map, Array.mem_ofFn] at hc
  obtain ⟨p, ⟨j, rfl⟩, rfl⟩ := hc
  exact (chanBlock_sizes ..).2

/-- Says: a new state is well-formed. Does not say: anything about processing. -/
theorem init_wf (sr : Float) (b : Bool) : (State.init sr b).WF := by
  have h : 0 < ringFrames sr := Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)
  refine ⟨h, h, ?_⟩
  intro x hx
  simp only [State.init, Array.mem_singleton] at hx
  subst hx
  exact mkChan_size _ _

/-- Says: `reduction` of a new state is 0 (the Web Platform Tests expect 0 before any signal).
Does not say: that it stays 0 after a block. -/
theorem init_reduction (sr : Float) (b : Bool) : reduction (State.init sr b) = 0.0 := rfl

/-! ## Guards -/

/-- Run `k` blocks of 128 frames of the same input; return the state and the last output. -/
def runBlocks (k : Nat) (s : State) (inp : Block) (params : Array FloatArray) :
    State × Block :=
  iter (fun _ (p : State × Block) =>
      let r := process 128 p.1 #[inp] params
      (r.1, r.2.getD 0 #[])) k 0 (s, #[])

def defaults : Array FloatArray :=
  #[⟨#[-24.0]⟩, ⟨#[30.0]⟩, ⟨#[12.0]⟩, ⟨#[0.003]⟩, ⟨#[0.25]⟩, ⟨#[0.0]⟩]

def mean (a : FloatArray) : Float :=
  if a.size = 0 then 0.0 else (iter (fun i (t : Float) => t + a.get! i) a.size 0 0.0) / a.size.toFloat

def near (a b e : Float) : Bool := (a - b).abs < e

#guard ringFrames 44100.0 == 265
#guard ringFrames 48000.0 == 288
#guard reduction (State.init 44100.0) == 0.0

-- silent input: reduction stays 0
#guard reduction (runBlocks 5 (State.init 44100.0) (silence 1 128) defaults).1 == 0.0

-- a loud constant input: reduction negative after one block, and the level falls
#guard reduction (runBlocks 1 (State.init 44100.0) #[mkChan 128 (fun _ => 1.0)] defaults).1 < 0.0
#guard
  let inp : Block := #[mkChan 128 (fun _ => 1.0)]
  let s0 := State.init 44100.0
  let a := (runBlocks 4 s0 inp defaults).2   -- frames 384 to 511, past the pre-delay
  let b := (runBlocks 60 s0 inp defaults).2
  mean b[0]! < mean a[0]! && mean a[0]! < 1.0 && mean b[0]! > 0.0

-- the curve: identity below the threshold; continuity at both ends of the knee; increasing
#guard curve (-24.0) 30.0 12.0 0.01 == 0.01
#guard curve (-24.0) 30.0 12.0 0.0 == 0.0
#guard
  let c := Curve.make (-24.0) 30.0 12.0
  near (c.eval (c.lt * (1.0 - 1e-12))) (c.eval (c.lt * (1.0 + 1e-12))) 1e-9 &&
  near (c.eval (c.ke * (1.0 - 1e-12))) (c.eval (c.ke * (1.0 + 1e-12))) 1e-9
#guard
  let c := Curve.make (-24.0) 30.0 12.0
  let xs := (List.range 2000).map fun i => 0.0001 * Float.exp (i.toFloat * 0.005)
  let ys := xs.map c.eval
  (ys.zip ys.tail).all fun (a, b) => a < b
-- slope 1 / ratio above the knee, in dB
#guard
  let c := Curve.make (-24.0) 30.0 12.0
  let x1 := c.ke * 2.0
  let x2 := c.ke * 8.0
  near ((linearToDb (c.eval x2) - linearToDb (c.eval x1)) / (linearToDb x2 - linearToDb x1))
    (1.0 / 12.0) 1e-9
#guard
  let c := Curve.make (-40.0) 10.0 4.0
  let x1 := c.ke * 2.0
  let x2 := c.ke * 8.0
  near ((linearToDb (c.eval x2) - linearToDb (c.eval x1)) / (linearToDb x2 - linearToDb x1))
    0.25 1e-9
-- the slope of the knee curve at its end is 1 / ratio (the bisection found k)
#guard
  let c := Curve.make (-24.0) 30.0 12.0
  near (Float.exp (-c.k * (c.ke - c.lt))) (1.0 / 12.0) 1e-9
-- knee 0 is a hard knee: identity up to the threshold, the dB line from there
#guard
  let c := Curve.make (-24.0) 0.0 4.0
  near c.ke c.lt 1e-12 && c.eval (c.lt * 0.5) == c.lt * 0.5 &&
  near (c.eval (c.lt * 2.0)) (c.lt * Float.pow 2.0 0.25) 1e-9 &&
  near (c.eval (c.lt * (1.0 + 1e-12))) c.lt 1e-9
-- ratio 1 is the identity
#guard curve (-24.0) 30.0 1.0 0.7 == 0.7
-- automatic makeup: (1 / curve 1)^0.6 in dB; zero when the curve passes 1.0 unchanged
#guard near (makeupGainDb (-24.0) 30.0 12.0) (-0.6 * linearToDb (curve (-24.0) 30.0 12.0 1.0)) 1e-12
#guard makeupGainDb (-24.0) 30.0 12.0 > 0.0
#guard near (makeupGainDb 0.0 0.0 12.0) 0.0 1e-9

-- below the threshold, makeup 0 dB (manual): the output is the input delayed by 265 frames, exactly
#guard
  let ramp : Nat → Float := fun i => (i.toFloat + 1.0) / 10000.0   -- at most 0.0384 < 0.0631
  let s0 := State.init 44100.0 false
  let r1 := process 128 s0 #[#[mkChan 128 (fun i => ramp i)]] defaults
  let r2 := process 128 r1.1 #[#[mkChan 128 (fun i => ramp (128 + i))]] defaults
  let r3 := process 128 r2.1 #[#[mkChan 128 (fun i => ramp (256 + i))]] defaults
  let o3 := r3.2[0]![0]!
  (List.range 128).all fun i =>
    let f := 256 + i
    if f < 265 then o3.get! i == 0.0 else o3.get! i == ramp (f - 265)
-- the same with the automatic makeup: the delayed input times the makeup gain
#guard
  let ramp : Nat → Float := fun i => (i.toFloat + 1.0) / 10000.0
  let s0 := State.init 44100.0 true
  let r1 := process 128 s0 #[#[mkChan 128 (fun i => ramp i)]] defaults
  let r2 := process 128 r1.1 #[#[mkChan 128 (fun i => ramp (128 + i))]] defaults
  let r3 := process 128 r2.1 #[#[mkChan 128 (fun i => ramp (256 + i))]] defaults
  let mk := dbToLinear (makeupGainDb (-24.0) 30.0 12.0)
  let o3 := r3.2[0]![0]!
  (List.range 128).all fun i =>
    let f := 256 + i
    if f < 265 then o3.get! i == 0.0 else near (o3.get! i) (ramp (f - 265) * mk) 1e-12
-- and the reduction is 0 there
#guard
  let s0 := State.init 44100.0 true
  let r := process 128 s0 #[#[mkChan 128 (fun _ => 0.01)]] defaults
  reduction r.1 == 0.0

-- stereo: L and R stay apart (a silent channel stays silent; the loud one is heard)
#guard
  let s0 := State.init 44100.0 false
  let inp : Block := #[mkChan 128 (fun _ => 1.0), mkChan 128 (fun _ => 0.0)]
  let o := (runBlocks 4 s0 inp defaults).2
  o.size == 2 && (o[1]!.toList.all fun v => v == 0.0) && mean o[0]! > 0.0
#guard
  let s0 := State.init 44100.0 false
  let inp : Block := #[mkChan 128 (fun _ => 0.0), mkChan 128 (fun _ => 1.0)]
  let o := (runBlocks 4 s0 inp defaults).2
  (o[0]!.toList.all fun v => v == 0.0) && mean o[1]! > 0.0
-- the channel count change: a mono block after stereo keeps channel 0's ring
#guard
  let s0 := State.init 44100.0 false
  let st := (runBlocks 1 s0 #[mkChan 128 (fun _ => 0.01), mkChan 128 (fun _ => 0.02)] defaults).1
  let r := process 128 st #[#[mkChan 128 (fun _ => 0.01)]] defaults
  r.1.rings.size == 1 && r.2[0]!.size == 1
-- an empty input block is one channel of silence
#guard (process 128 (State.init 44100.0) #[#[]] defaults).2[0]!.size == 1

end L4Factoidal.WebAudio.Compressor
