import L4Factoidal.WebAudio.Kernels

/-!
# Web Audio: WaveShaperNode

Section "The WaveShaperNode Interface" of the W3C Web Audio API
(https://webaudio.github.io/web-audio-api/). Stage F of
https://github.com/danbri/factoidal-core/issues/1169.

## What is here

* `curveValue`: the mapping of one sample through a curve of `N >= 2` values,
  `v = (N - 1) / 2 * (x + 1)`, `c[0]` for `v <= 0`, `c[N - 1]` for `v >= N - 1`, else linear
  interpolation between `c[floor v]` and `c[floor v + 1]`. A curve of fewer than 2 values (the
  null curve) passes the input through.
* `setCurve`, `setOversample`, `Oversample.ofString?`: the attribute setters. A curve of one
  value is `InvalidStateError`; a curve of no values is the null curve.
* `process`: the block kernel. Curve null: the output is the input. Oversample `none`: the curve
  is applied to each sample. `2x` and `4x`: the signal is up-sampled by 2 (zero-stuffing, gain 2),
  shaped at the high rate, and down-sampled by 2 with the same low-pass filter. `4x` nests two
  such stages. The filter is a linear-phase half-band FIR of 63 taps (windowed sinc, Blackman
  window). The specification leaves the filters to the implementation ("an implementation SHOULD
  use a high-quality anti-aliasing filter").

## The filter

`halfBand` has 63 taps: the centre tap (index 31) is exactly 0.5; taps at an even distance from
the centre are exactly 0; the taps at an odd distance are `sin(pi m / 2) / (pi m)` times the
Blackman window, scaled so that they sum to exactly 0.5. So each of the two polyphase branches of
the zero-stuffed up-sampler has a coefficient sum of 0.5, and a constant input stays constant
(no tone at half the sample rate).

Delay, with the curve set and an identity curve: a 2x stage delays the signal by 31 frames
(31 at the high rate for each filter, 62 high-rate samples, 31 base-rate frames). A 4x node
delays by 186 samples at four times the rate, which is 46.5 base-rate frames (the outer stage
filters at twice the rate, the inner at four times). A signal that has been constant for 63 frames
(2x) or 94 frames (4x) comes out constant; see the `#guard`s for the measured values.

## State

`hist` has one entry for each channel: an array of four `FloatArray`s, `[up of the outer stage,
down of the outer stage, up of the inner stage, down of the inner stage]`. An up history is the
previous 31 low-rate inputs of the stage (oldest first, all zero at the start). A down history
is the previous 62 high-rate shaped samples (all `curveValue curve 0` at the start, which is what a
silent past gives through the curve). An empty entry means "start of the channel". So a silent
input with a curve that maps 0 to 0.5 gives 0.5 at every frame, also with `2x` and `4x` (WPT
`silent-inputs.html` intends this; its second test sets the misspelled property `overSample`, which
is not the attribute, so a browser does not run it with oversampling).
A change of the input's channel count keeps the histories of the channels that remain; a new
channel starts at the start state.

## What is proved

Output shape (one block, `max 1 (input channel count)` channels, `n` frames each) and the number
of channel histories. Value statements are `#guard`s.

## Cases not decided by the specification or by WPT

* An input of NaN gives NaN (`v` is NaN, no comparison holds, and the interpolation cannot pick
  an index). No WPT test uses NaN.
* An infinite input gives `c[0]` or `c[N - 1]`.
* The 2x and 4x output is not compared by WPT: only the attribute round trip
  (`waveshaper-simple.html`) and the constructor (`ctor-waveshaper.html`) touch `oversample`.

## Not done in this file

* The tail time of an oversampled node (the filter's 31 or 46.5 frames after the input ends):
  the graph module decides how long the node keeps rendering.
* Polyphase cost reductions beyond the half of the up-sampler's work that zero-stuffing removes.
-/

namespace L4Factoidal.WebAudio.WaveShaper

open L4Factoidal.WebAudio.Kernels

/-! ## Attributes -/

inductive Oversample where
  | none | x2 | x4
  deriving DecidableEq, Repr, Inhabited

/-- The attribute's value for a string: `"none"`, `"2x"`, `"4x"`. Another string is not a value
(the setter of the interface ignores it, WPT `waveshaper-simple.html`). -/
def Oversample.ofString? : String → Option Oversample
  | "none" => some .none
  | "2x" => some .x2
  | "4x" => some .x4
  | _ => Option.none

def Oversample.text : Oversample → String
  | .none => "none"
  | .x2 => "2x"
  | .x4 => "4x"

structure State where
  /-- The curve's values (binary32 values held as `Float`); empty means null. -/
  curve : FloatArray := ⟨#[]⟩
  oversample : Oversample := .none
  /-- Per channel: `[up outer, down outer, up inner, down inner]` histories, or empty for a
  channel that has not started (see the module comment). -/
  hist : Array (Array FloatArray) := #[]
  deriving Inhabited

/-! ## The curve mapping -/

/-- The specification's mapping of `x` through `curve`. A curve of fewer than 2 values passes `x`
through (the null curve). NaN gives NaN. -/
def curveValue (curve : FloatArray) (x : Float) : Float :=
  let nN := curve.size
  if nN < 2 then x else
  let top := (nN - 1).toFloat
  let v := top / 2.0 * (x + 1.0)
  if v != v then v
  else if v ≤ 0.0 then getF curve 0
  else if v ≥ top then getF curve (nN - 1)
  else
    let k := v.floor.toUInt64.toNat
    let f := v - k.toFloat
    (1.0 - f) * getF curve k + f * getF curve (k + 1)

/-- Setting `curve`: one value is `InvalidStateError`; no value is the null curve; otherwise the
node keeps a copy of the values (a `FloatArray` is a value: a later change of the caller's array
does not reach the node, WPT `waveshaper-copy-curve.html`). -/
def setCurve (s : State) (c : FloatArray) : Except String State :=
  if c.size = 1 then
    .error "InvalidStateError: the curve of a WaveShaperNode must have 0 (null) or at least 2 values"
  else .ok { s with curve := c }

/-- Setting `oversample` starts the filters again. -/
def setOversample (s : State) (o : Oversample) : State :=
  { s with oversample := o, hist := #[] }

/-! ## The half-band filter -/

def piC : Float := 3.141592653589793

/-- The taps at an odd distance from the centre before scaling: `sin(pi m / 2) / (pi m)` times the
Blackman window `0.42 - 0.5 cos(2 pi k / 62) + 0.08 cos(4 pi k / 62)`, `m = k - 31`. The other
taps are set in `halfBand`. -/
def hbRaw (k : Nat) : Float :=
  if k % 2 = 1 then 0.0 else
  let kf := k.toFloat
  let m := kf - 31.0
  let w := 0.42 - 0.5 * Float.cos (2.0 * piC * kf / 62.0) + 0.08 * Float.cos (4.0 * piC * kf / 62.0)
  Float.sin (piC * m / 2.0) / (piC * m) * w

/-- The 63 taps (see the module comment). -/
@[noinline] def halfBand : FloatArray :=
  let raw := mkChan 63 hbRaw
  let total := iter (fun k (acc : Float) => acc + getF raw k) 63 0 0.0
  mkChan 63 fun k => if k = 31 then 0.5 else if k % 2 = 1 then 0.0 else getF raw k * (0.5 / total)

/-- Up-sampling by 2 of `n` frames `x` with the previous 31 inputs `hist`: `2n` high-rate samples
(`u[2m] = 2 x[m]`, `u[2m+1] = 0`, filtered) and the new history. -/
def up2 (n : Nat) (hist x : FloatArray) : FloatArray × FloatArray :=
  let xe := mkChan (31 + n) fun i => if i < 31 then getF hist i else getF x (i - 31)
  let phase := fun (p ph cnt : Nat) =>
    iter (fun j (acc : Float) => acc + getF halfBand (2 * j + ph) * getF xe (p - j)) cnt 0 0.0
  let hi := mkChan (2 * n) fun j =>
    let m := j / 2
    if j % 2 = 0 then 2.0 * phase (m + 31) 0 32 else 2.0 * phase (m + 31) 1 31
  (hi, mkChan 31 fun i => getF xe (n + i))

/-- Down-sampling by 2: the filter applied to `2n` high-rate samples `y` with the previous 62
(`hist`), every second output kept: `n` samples and the new history. -/
def down2 (n : Nat) (hist y : FloatArray) : FloatArray × FloatArray :=
  let ye := mkChan (62 + 2 * n) fun i => if i < 62 then getF hist i else getF y (i - 62)
  let out := mkChan n fun m =>
    iter (fun k (acc : Float) => acc + getF halfBand k * getF ye (62 + 2 * m - k)) 63 0 0.0
  (out, mkChan 62 fun i => getF ye (2 * n + i))

/-- The histories of a channel at its start. -/
def freshHist (pad : Float) : Array FloatArray :=
  #[mkChan 31 (fun _ => 0.0), mkChan 62 (fun _ => pad), mkChan 31 (fun _ => 0.0),
    mkChan 62 (fun _ => pad)]

/-! ## The kernel -/

/-- The curve applied to the first `n` frames of `a`. -/
def mapCurve (curve : FloatArray) (n : Nat) (a : FloatArray) : FloatArray :=
  mkChan n fun i => curveValue curve (getF a i)

/-- One channel of `n` frames through a non-null curve with oversampling `os`. -/
def shapeChan (n : Nat) (curve : FloatArray) (os : Oversample) (inp : FloatArray)
    (hs0 : Array FloatArray) : FloatArray × Array FloatArray :=
  let hs := if hs0.size = 4 then hs0 else freshHist (curveValue curve 0.0)
  let e : FloatArray := ⟨#[]⟩
  match os with
  | .none => (mapCurve curve n inp, hs0)
  | .x2 =>
    let (hi, uA) := up2 n (hs.getD 0 e) inp
    let (out, dA) := down2 n (hs.getD 1 e) (mapCurve curve (2 * n) hi)
    (out, #[uA, dA, hs.getD 2 e, hs.getD 3 e])
  | .x4 =>
    let (hiA, uA) := up2 n (hs.getD 0 e) inp
    let (hiB, uB) := up2 (2 * n) (hs.getD 2 e) hiA
    let (loB, dB) := down2 (2 * n) (hs.getD 3 e) (mapCurve curve (4 * n) hiB)
    let (out, dA) := down2 n (hs.getD 1 e) loB
    (out, #[uA, dA, uB, dB])

/-- `params` is unused (no `AudioParam`). Input 0 has one or more channels; an empty block is one
channel of silence. The output is one block with as many channels as the input (at least 1). -/
def process (n : Nat) (s : State) (inputs : Array Block) (_params : Array FloatArray) :
    State × Array Block :=
  let inp := inputs.getD 0 #[]
  let ch := max 1 inp.size
  if s.curve.size < 2 then
    (s, #[Array.ofFn (n := ch) fun c => mkChan n fun i => getF (inp.getD c.1 ⟨#[]⟩) i])
  else
    let res : Array (FloatArray × Array FloatArray) := Array.ofFn (n := ch) fun c =>
      shapeChan n s.curve s.oversample (inp.getD c.1 ⟨#[]⟩) (s.hist.getD c.1 #[])
    ({ s with hist := res.map Prod.snd }, #[res.map Prod.fst])

theorem shapeChan_size (n : Nat) (curve : FloatArray) (os : Oversample) (inp : FloatArray)
    (hs : Array FloatArray) : (shapeChan n curve os inp hs).1.size = n := by
  unfold shapeChan
  cases os <;> simp [mapCurve, down2, mkChan_size]

/-- Says: the kernel returns one block with `max 1 (input channel count)` channels and `n` frames in
each, whatever the curve and the oversampling. Does not say: the values. -/
theorem process_shape (n : Nat) (s : State) (inputs : Array Block) (params : Array FloatArray) :
    (process n s inputs params).2.size = 1 ∧
    (∀ b ∈ (process n s inputs params).2, b.size = max 1 (inputs.getD 0 #[]).size ∧ IsBlock n b) := by
  unfold process
  by_cases hc : s.curve.size < 2
  · simp only [hc, if_true]
    refine ⟨by simp, ?_⟩
    intro b hb
    simp only [Array.mem_singleton] at hb
    subst hb
    refine ⟨by simp, ?_⟩
    intro c hc'
    simp only [Array.mem_ofFn] at hc'
    obtain ⟨j, rfl⟩ := hc'
    exact mkChan_size n _
  · simp only [hc, if_false]
    refine ⟨by simp, ?_⟩
    intro b hb
    simp only [Array.mem_singleton] at hb
    subst hb
    refine ⟨by simp, ?_⟩
    intro c hc'
    simp only [Array.mem_map, Array.mem_ofFn] at hc'
    obtain ⟨p, ⟨j, rfl⟩, rfl⟩ := hc'
    exact shapeChan_size n _ _ _ _

/-- Says: after a block with a non-null curve the state holds one history entry for each output
channel. Does not say: anything about the stored values. -/
theorem process_hist_size (n : Nat) (s : State) (inputs : Array Block) (params : Array FloatArray)
    (hc : ¬ s.curve.size < 2) :
    (process n s inputs params).1.hist.size = max 1 (inputs.getD 0 #[]).size := by
  simp [process, hc]

/-- Says: with a null curve the kernel does not change the state. Does not say: anything about
the output. -/
theorem process_null_state (n : Nat) (s : State) (inputs : Array Block) (params : Array FloatArray)
    (hc : s.curve.size < 2) : (process n s inputs params).1 = s := by
  simp [process, hc]

/-- Says: the curve of one value is refused; any other array is accepted and the node's curve is
that array. Does not say: how a page's typed array is copied. -/
theorem setCurve_one (s : State) (c : FloatArray) (h : c.size = 1) :
    ∃ m, setCurve s c = .error m := by
  unfold setCurve
  rw [if_pos h]
  exact ⟨_, rfl⟩

theorem setCurve_ok (s : State) (c : FloatArray) (h : c.size ≠ 1) :
    setCurve s c = .ok { s with curve := c } := by
  simp [setCurve, h]

/-! ## Tests

Cases of the Web Platform Tests (`webaudio/the-audio-api/the-waveshapernode-interface`) are named
at each guard. `ws` runs one block on one channel and returns the channel as a list. -/

section Tests

def near (tol : Float) (xs ys : List Float) : Bool :=
  xs.length == ys.length && (List.zip xs ys).all fun (x, y) => (x - y).abs ≤ tol

def stateWith (curve : List Float) (o : Oversample := .none) : State :=
  { curve := ⟨curve.toArray⟩, oversample := o }

def wsRun (n : Nat) (s : State) (cs : List (List Float)) : State × Block :=
  let r := process n s #[(cs.map fun c => FloatArray.mk c.toArray).toArray] #[]
  (r.1, r.2[0]!)

def ws (curve : List Float) (xs : List Float) : List Float :=
  ((wsRun xs.length (stateWith curve) [xs]).2[0]!).data.toList

-- curve-tests.html: -1, 0, +1 map to the curve [2, -3, 4].
#guard near 1e-12 (ws [2, -3, 4] [-1, 0, 1]) [2, -3, 4]
-- curve-tests.html: interpolation.
#guard near 1e-12 (ws [2, -3, 4] [-0.5, 0.5, 0.75]) [-0.5, 0.5, 2.25]
-- curve-tests.html: out-of-range inputs map to the first and last values.
#guard near 1e-12 (ws [2, -3, 4] [-1.5, 1.5]) [2, 4]
-- curve-tests.html: a 2-element curve.
#guard near 1e-12 (ws [2, -2] [-1, 0, 1]) [2, 0, -2]
-- curve-tests.html: a 4-element curve (no middle element).
#guard near 1e-12 (ws [1, 2, 4, 7] [-1, 0, 1]) [1, 3, 7]
-- curve-tests.html: a huge curve, c[i] = i / 3.5435, 60001 values.
#guard
  let big : List Float := (List.range 60001).map fun i => i.toFloat / 3.5435
  near 1e-9 (ws big [-1, 0, 1]) [big[0]!, big[30000]!, big[60000]!]
-- curve-tests.html: the null curve passes the input through.
#guard near 0.0 (ws [] [-1, 0, 1, 2]) [-1, 0, 1, 2]
-- Identity curve [-1, 0, 1] (silent-inputs.html's identityCurve).
#guard near 1e-12 (ws [-1, 0, 1] [-1, -0.5, 0, 0.3, 1]) [-1, -0.5, 0, 0.3, 1]
-- Between points of a 5-value curve: x = -0.25 gives v = 1.5, halfway between c[1] and c[2].
#guard near 1e-12 (ws [0, 1, 3, 2, 8] [-0.25, 0.25, 0.5]) [2, 2.5, 2]
-- A constant curve maps 0 to its value.
#guard near 1e-12 (ws [0.5, 0.5, 0.5] [0]) [0.5]
-- Infinite inputs map to the ends; a NaN input gives NaN (no WPT case; see the module comment).
#guard near 0.0 (ws [2, -3, 4] [1.0 / 0.0, -1.0 / 0.0]) [4, 2]
#guard (ws [2, -3, 4] [0.0 / 0.0]).all fun x => x != x

-- waveshaper-limits.html: curve [0, 1, 0]; 23 inputs from -1 - scale to 1 + scale, scale 0.1.
#guard
  let scale : Float := 0.1
  let xs := (List.range 23).map fun k => k.toFloat * scale - 1.1
  let ref := (List.range 23).map fun k =>
    if k = 0 then 0.0 else if k ≤ 11 then (k - 1).toFloat * scale
    else if k ≤ 21 then 2.0 - (k - 1).toFloat * scale else 0.0
  near 1e-6 (ws [0, 1, 0] xs) ref

-- waveshaper.html: the curve atan(5x) / (pi / 2) on 65536 points, input a ramp over [-1, 1).
-- The output is the spec's interpolation of the sampled curve; as a check that does not repeat the
-- formula, it is within 2e-4 of the analytic curve (the sampling offset of half a curve step, 1.5e-5
-- in x, times a slope of at most 3.2).
#guard
  let nC := 65536
  let curve := (List.range nC).map fun i =>
    let x := (i.toFloat - (nC / 2).toFloat) / (nC / 2).toFloat
    Float.atan (5.0 * x) / (0.5 * piC)
  let xs := (List.range 1001).map fun i => i.toFloat / 500.0 - 1.0
  near 2e-4 (ws curve xs) (xs.map fun x => Float.atan (5.0 * x) / (0.5 * piC))

-- silent-inputs.html test-0: curve [0.5, 0.5, 0.5], silent input (offset 0): 0.5 at every frame.
#guard near 0.0 (ws [0.5, 0.5, 0.5] (List.replicate 40 0.0)) (List.replicate 40 0.5)
-- silent-inputs.html test-2: no input at all (an unconnected input is an empty block here):
-- one channel of 0.5.
#guard
  let r := process 6 (stateWith [0.5, 0.5, 0.5]) #[#[]] #[]
  near 0.0 (r.2[0]![0]!.data.toList) (List.replicate 6 0.5) && r.2[0]!.size == 1
-- silent-inputs.html test-1 intends the same with oversample "2x" and "4x": 0.5 at every frame.
#guard
  (wsRun 40 (stateWith [0.5, 0.5, 0.5] .x2) [List.replicate 40 0.0]).2[0]!.data.toList.all
    fun x => (x - 0.5).abs < 1e-12
#guard
  (wsRun 40 (stateWith [0.5, 0.5, 0.5] .x4) [List.replicate 40 0.0]).2[0]!.data.toList.all
    fun x => (x - 0.5).abs < 1e-12

-- The filter: half-band structure, exact sums, symmetry.
#guard halfBand.size == 63
#guard halfBand.get! 31 == 0.5
#guard ((List.range 63).filter (fun k => k % 2 = 1 && k ≠ 31)).all fun k => halfBand.get! k == 0.0
#guard ((List.range 32).foldl (fun acc j => acc + halfBand.get! (2 * j)) 0.0 - 0.5).abs < 1e-15
#guard (List.range 63).all fun k => (halfBand.get! k - halfBand.get! (62 - k)).abs < 1e-15

/-- Channel 0 of `k` blocks of `n` frames run in turn on consecutive parts of `xs`. -/
def wsBlocks (s : State) (sizes : List Nat) (xs : List Float) : List Float := Id.run do
  let mut st := s
  let mut rest := xs
  let mut out : List Float := []
  for n in sizes do
    let r := wsRun n st [rest.take n]
    st := r.1
    out := out ++ r.2[0]!.data.toList
    rest := rest.drop n
  return out

def constSig (v : Float) (n : Nat) : List Float := List.replicate n v

-- 2x and 4x with the identity curve and a constant 0.25: constant after the filter's start.
-- The delay of the 2x filters is 31 frames; the output is within 1e-9 of 0.25 from frame 62 on.
#guard
  let o := wsBlocks (stateWith [-1, 0, 1] .x2) [64, 64, 64] (constSig 0.25 192)
  o.length == 192 && ((o.drop 62).all fun x => (x - 0.25).abs < 1e-9)
-- 4x: the same from frame 93 on (total delay 46.5 frames).
#guard
  let o := wsBlocks (stateWith [-1, 0, 1] .x4) [64, 64, 64] (constSig 0.25 192)
  o.length == 192 && ((o.drop 93).all fun x => (x - 0.25).abs < 1e-9)
-- The start is a ramp: the filter has not filled yet at frame 0.
#guard
  let o := wsBlocks (stateWith [-1, 0, 1] .x2) [8] (constSig 0.25 8)
  o.all fun x => x < 0.25 - 1e-6

-- Delay: an impulse through the 2x filter with the identity curve peaks at frame 31 and the
-- response is symmetric about it (linear phase).
def argmax (xs : List Float) : Nat :=
  (List.range xs.length).foldl (fun best i => if xs.getD i 0.0 > xs.getD best 0.0 then i else best) 0

def impulse (n : Nat) : List Float := 1.0 :: constSig 0.0 (n - 1)

#guard
  let o := wsBlocks (stateWith [-1, 0, 1] .x2) [100] (impulse 100)
  argmax o == 31 && (List.range 31).all fun d => ((o.getD (31 - d) 0) - (o.getD (31 + d) 0)).abs < 1e-12
-- 4x: delay 186 / 4 = 46.5 frames: the response is symmetric about 46.5.
#guard
  let o := wsBlocks (stateWith [-1, 0, 1] .x4) [140] (impulse 140)
  (argmax o == 46 || argmax o == 47) &&
  (List.range 47).all fun d => ((o.getD (46 - d) 0) - (o.getD (47 + d) 0)).abs < 1e-12

-- A block boundary changes nothing (bit for bit), for 2x and 4x.
def mixed : List Float := (List.range 90).map fun i => Float.sin (0.37 * i.toFloat) * 0.9
#guard
  let a := wsBlocks (stateWith [-1, -0.2, 0.7, 1] .x2) [90] mixed
  let b := wsBlocks (stateWith [-1, -0.2, 0.7, 1] .x2) [13, 40, 1, 36] mixed
  a == b
#guard
  let a := wsBlocks (stateWith [-1, -0.2, 0.7, 1] .x4) [90] mixed
  let b := wsBlocks (stateWith [-1, -0.2, 0.7, 1] .x4) [29, 29, 32] mixed
  a == b
-- A null curve with oversampling is the identity, exactly.
#guard wsBlocks (stateWith [] .x4) [90] mixed == mixed

-- Channels: two channels are shaped independently; a third channel starts later.
#guard
  let s := stateWith [-1, 0, 1] .x2
  let r := wsRun 4 s [[0.25, 0.25, 0.25, 0.25], [0.5, 0.5, 0.5, 0.5]]
  let r1 := wsRun 4 s [[0.25, 0.25, 0.25, 0.25]]
  r.2.size == 2 && r.1.hist.size == 2 && r.2[0]! == r1.2[0]! &&
  (r.2[1]!.data.toList.map (· * 0.5) |> near 1e-12 (r.2[0]!.data.toList))
#guard
  let s := stateWith [-1, 0, 1] .x2
  let r1 := wsRun 4 s [[0.25, 0.25, 0.25, 0.25]]
  let r2 := wsRun 4 r1.1 [[0.25, 0.25, 0.25, 0.25], [0.25, 0.25, 0.25, 0.25]]
  r2.2.size == 2 && r2.1.hist.size == 2 && r2.2[0]! != r2.2[1]!

-- Attributes: waveshaper-simple.html and ctor-waveshaper.html.
#guard Oversample.ofString? "none" == some .none
#guard Oversample.ofString? "2x" == some .x2
#guard Oversample.ofString? "4x" == some .x4
#guard Oversample.ofString? "invalid" == Option.none
#guard (Oversample.ofString? "4x").map Oversample.text == some "4x"
-- A curve of one value is InvalidStateError; none is null; [-1, 0.25, 0.75] is stored.
#guard (match setCurve {} ⟨#[1.0]⟩ with | .error _ => true | .ok _ => false)
#guard (match setCurve (stateWith [1, 2, 3]) ⟨#[]⟩ with | .ok s => s.curve.size == 0 | .error _ => false)
#guard (match setCurve {} ⟨#[-1.0, 0.25, 0.75]⟩ with
  | .ok s => s.curve.data.toList == [-1.0, 0.25, 0.75] | .error _ => false)
-- Setting the oversample starts the filters again.
#guard
  let r := wsRun 4 (stateWith [-1, 0, 1] .x2) [[0.25, 0.25, 0.25, 0.25]]
  r.1.hist.size == 1 && (setOversample r.1 .x4).hist.size == 0 && (setOversample r.1 .x4).oversample == .x4

end Tests

end L4Factoidal.WebAudio.WaveShaper
