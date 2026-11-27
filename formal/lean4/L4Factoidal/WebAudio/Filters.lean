import L4Factoidal.WebAudio.Kernels

/-!
# Web Audio: BiquadFilterNode

Section "The BiquadFilterNode Interface" of the W3C Web Audio API
(https://webaudio.github.io/web-audio-api/). Stage B of
https://github.com/danbri/factoidal-core/issues/1169; structure in
`docs/designissues/2026-11-26-foafnaut-audio-plan.md` section 9.

## What is here

* `biquadCoefs`: the six coefficients of the specification ("Filters Characteristics") for the
  eight filter types, from the normalized frequency `computedFrequency / Nyquist`, `Q` and `gain`,
  divided by `a0` (so `BiquadCoef` has five fields).
* `computedFrequency`: `frequency * 2^(detune / 1200)`.
* `biquadProcess`: the block kernel, `process : State → inputs → params → State × outputs`.
  `params[0..3]` are `frequency`, `detune`, `Q`, `gain` (all a-rate; an array of one value is
  read as constant over the block, see `paramAt`). The filter is the difference equation of the
  specification, `a0 y(n) + a1 y(n-1) + a2 y(n-2) = b0 x(n) + b1 x(n-1) + b2 x(n-2)`, computed in
  direct form I (four stored values per channel: the last two inputs and outputs), with the
  coefficients of each frame. (Transposed direct form II is equal for fixed coefficients and
  differs when they change; WPT `biquad-automation.html` computes direct form I.)
* `getFrequencyResponse`: magnitude and phase at given frequencies, `H(e^{i omega})` with
  `omega = pi f / Nyquist`, NaN outside `[0, Nyquist]`.

## Cases at the edges of the formulas

The formulas divide by `Q` or give `a0 = 0` at the ends of the frequency range. The specification
gives the formulas only; the Web Platform Tests reference
(`webaudio/resources/biquad-filters.js`, functions `create*Filter`) gives the limits, which this
file follows: a normalized frequency of 0 or 1 (a value outside `[0, 1]` is clamped to it, NaN
reads as 0), and `Q <= 0` for the filters whose `Q` is linear (bandpass, peaking, notch, allpass).
`Q` of lowpass and highpass is in dB and has no such case.

## What is proved

Output shapes; the filter state keeps one `BiquadChan` (four values) for each input channel;
`getFrequencyResponse` returns arrays of the length of `frequencyHz` and fails with
`InvalidAccessError` exactly when an output array has another length.

## What is tested only with `#guard`

Every statement about a `Float` value, against values computed by running the specification's
reference code (`biquad-filters.js` of the Web Platform Tests) in Node.

## Not done in this file

* `AudioParam` automation and the summing of parameter inputs (the caller supplies `params`).
* The channel-count change rule: when the input channel count changes, channels that no longer
  exist are dropped and new channels start with zero state.
* Flushing of denormal values and NaN in the filter state (the specification only permits a
  warning).
* The `type` setter has no error case (every value of `BiquadType` is valid).
-/

namespace L4Factoidal.WebAudio.Filters

open L4Factoidal.WebAudio.Kernels

/-! ## Types and coefficients -/

inductive BiquadType where
  | lowpass | highpass | bandpass | lowshelf | highshelf | peaking | notch | allpass
  deriving DecidableEq, Repr

/-- Coefficients of the difference equation, each divided by `a0` (so `a0 = 1` and is not stored). -/
structure BiquadCoef where
  b0 : Float
  b1 : Float
  b2 : Float
  a1 : Float
  a2 : Float

/-- The identity filter `y = x`. -/
def BiquadCoef.wire : BiquadCoef := ⟨1.0, 0.0, 0.0, 0.0, 0.0⟩

/-- The filter `y = 0`. -/
def BiquadCoef.zero : BiquadCoef := ⟨0.0, 0.0, 0.0, 0.0, 0.0⟩

/-- A constant gain `y = g x`. -/
def BiquadCoef.gain (g : Float) : BiquadCoef := ⟨g, 0.0, 0.0, 0.0, 0.0⟩

def piF : Float := 3.141592653589793

/-- `computedFrequency(t) = frequency(t) * pow(2, detune(t) / 1200)` (BiquadFilterNode and
OscillatorNode). -/
def computedFrequency (frequency detune : Float) : Float :=
  frequency * Float.exp2 (detune / 1200.0)

/-- Divide the six coefficients by `a0`, as the specification's transfer function does. -/
def normalizeCoefs (b0 b1 b2 a0 a1 a2 : Float) : BiquadCoef :=
  let s := 1.0 / a0
  ⟨b0 * s, b1 * s, b2 * s, a1 * s, a2 * s⟩

/-- The normalized frequency `f0 / Nyquist` clamped into `[0, 1]`; NaN reads as 0. -/
def clampRatio (r : Float) : Float :=
  if r ≥ 1.0 then 1.0 else if r > 0.0 then r else 0.0

/-- The coefficients of the specification, section "Filters Characteristics".
`freq` is `computedFrequency / Nyquist`; `q` is `Q` (in dB for lowpass and highpass, linear for
the other types that use it); `gain` is in dB (used by lowshelf, highshelf and peaking). -/
def biquadCoefs (t : BiquadType) (freq q gain : Float) : BiquadCoef :=
  let f := clampRatio freq
  let a := Float.pow 10.0 (gain / 40.0)
  let w0 := piF * f
  let cosw := Float.cos w0
  let sinw := Float.sin w0
  match t with
  | .lowpass =>
    if f == 1.0 then BiquadCoef.wire else
    let alphaDb := sinw / (2.0 * Float.pow 10.0 (q / 20.0))
    let beta := (1.0 - cosw) / 2.0
    normalizeCoefs beta (2.0 * beta) beta (1.0 + alphaDb) (-2.0 * cosw) (1.0 - alphaDb)
  | .highpass =>
    if f == 1.0 then BiquadCoef.zero else
    if f == 0.0 then BiquadCoef.wire else
    let alphaDb := sinw / (2.0 * Float.pow 10.0 (q / 20.0))
    let beta := (1.0 + cosw) / 2.0
    normalizeCoefs beta (-2.0 * beta) beta (1.0 + alphaDb) (-2.0 * cosw) (1.0 - alphaDb)
  | .bandpass =>
    if f > 0.0 && f < 1.0 then
      if q > 0.0 then
        let al := sinw / (2.0 * q)
        normalizeCoefs al 0.0 (-al) (1.0 + al) (-2.0 * cosw) (1.0 - al)
      else BiquadCoef.wire
    else BiquadCoef.zero
  | .lowshelf =>
    if f == 1.0 then BiquadCoef.gain (a * a) else
    if f == 0.0 then BiquadCoef.wire else
    let alphaS := sinw / 2.0 * Float.sqrt ((a + 1.0 / a) * (1.0 / 1.0 - 1.0) + 2.0)
    let k2 := 2.0 * Float.sqrt a * alphaS
    let ap1 := a + 1.0
    let am1 := a - 1.0
    normalizeCoefs (a * (ap1 - am1 * cosw + k2)) (2.0 * a * (am1 - ap1 * cosw))
      (a * (ap1 - am1 * cosw - k2)) (ap1 + am1 * cosw + k2) (-2.0 * (am1 + ap1 * cosw))
      (ap1 + am1 * cosw - k2)
  | .highshelf =>
    if f == 1.0 then BiquadCoef.wire else
    if f == 0.0 then BiquadCoef.gain (a * a) else
    let alphaS := sinw / 2.0 * Float.sqrt ((a + 1.0 / a) * (1.0 / 1.0 - 1.0) + 2.0)
    let k2 := 2.0 * Float.sqrt a * alphaS
    let ap1 := a + 1.0
    let am1 := a - 1.0
    normalizeCoefs (a * (ap1 + am1 * cosw + k2)) (-2.0 * a * (am1 + ap1 * cosw))
      (a * (ap1 + am1 * cosw - k2)) (ap1 - am1 * cosw + k2) (2.0 * (am1 - ap1 * cosw))
      (ap1 - am1 * cosw - k2)
  | .peaking =>
    if f > 0.0 && f < 1.0 then
      if q > 0.0 then
        let al := sinw / (2.0 * q)
        normalizeCoefs (1.0 + al * a) (-2.0 * cosw) (1.0 - al * a) (1.0 + al / a) (-2.0 * cosw)
          (1.0 - al / a)
      else BiquadCoef.gain (a * a)
    else BiquadCoef.wire
  | .notch =>
    if f > 0.0 && f < 1.0 then
      if q > 0.0 then
        let al := sinw / (2.0 * q)
        normalizeCoefs 1.0 (-2.0 * cosw) 1.0 (1.0 + al) (-2.0 * cosw) (1.0 - al)
      else BiquadCoef.zero
    else BiquadCoef.wire
  | .allpass =>
    if f > 0.0 && f < 1.0 then
      if q > 0.0 then
        let al := sinw / (2.0 * q)
        normalizeCoefs (1.0 - al) (-2.0 * cosw) (1.0 + al) (1.0 + al) (-2.0 * cosw) (1.0 - al)
      else BiquadCoef.gain (-1.0)
    else BiquadCoef.wire

/-- Coefficients from the parameter values and the sample rate: the computed frequency
(`frequency` with `detune`) divided by the Nyquist frequency `sampleRate / 2`. -/
def coefsAt (t : BiquadType) (sampleRate frequency detune q gain : Float) : BiquadCoef :=
  biquadCoefs t (computedFrequency frequency detune / (sampleRate / 2.0)) q gain

/-! ## The block kernel -/

/-- The four stored values of one channel (direct form I): the last two inputs and the last two
outputs. -/
structure BiquadChan where
  x1 : Float := 0.0
  x2 : Float := 0.0
  y1 : Float := 0.0
  y2 : Float := 0.0

structure BiquadState where
  type : BiquadType
  sampleRate : Float
  /-- One entry for each channel. -/
  chans : Array BiquadChan := #[]

/-- Coefficients for each frame of the block: one entry per frame when some parameter array is
a-rate (more than one value), one entry for the whole block when every parameter has one value.
`params` is `[frequency, detune, Q, gain]`. -/
def blockCoefs (n : Nat) (t : BiquadType) (sampleRate : Float) (params : Array FloatArray) :
    Array BiquadCoef :=
  let fr := params.getD 0 ⟨#[]⟩
  let de := params.getD 1 ⟨#[]⟩
  let qq := params.getD 2 ⟨#[]⟩
  let gg := params.getD 3 ⟨#[]⟩
  let at_ := fun i => coefsAt t sampleRate (paramAt fr i) (paramAt de i) (paramAt qq i) (paramAt gg i)
  if fr.size ≤ 1 && de.size ≤ 1 && qq.size ≤ 1 && gg.size ≤ 1 then #[at_ 0]
  else Array.ofFn (n := n) fun i => at_ i.1

/-- Coefficients of frame `i`. -/
def coefOf (cs : Array BiquadCoef) (i : Nat) : BiquadCoef :=
  if cs.size = 1 then cs.getD 0 BiquadCoef.wire else cs.getD i BiquadCoef.wire

/-- One frame of one channel, direct form I: `y = (b0 x + b1 x1 + b2 x2) - (a1 y1 + a2 y2)`. With a
coefficient that changes at every frame this is the difference equation of the specification with
the coefficients of the frame, which is what the Web Platform Tests (`biquad-automation.html`,
`no-dezippering.html`) compute as the reference. -/
def biquadStep (cs : Array BiquadCoef) (inp : FloatArray) (i : Nat)
    (p : BiquadChan × FloatArray) : BiquadChan × FloatArray :=
  let c := coefOf cs i
  let x := getF inp i
  let z := p.1
  let y := (c.b0 * x + c.b1 * z.x1 + c.b2 * z.x2) - (c.a1 * z.y1 + c.a2 * z.y2)
  (⟨x, z.x1, y, z.y1⟩, p.2.push y)

def biquadChan (n : Nat) (cs : Array BiquadCoef) (inp : FloatArray) (z : BiquadChan) :
    BiquadChan × FloatArray :=
  iter (biquadStep cs inp) n 0 (z, ⟨#[]⟩)

/-- The kernel. Output: one block with the input's channel count; the state has one `BiquadChan`
for each input channel (a new channel starts at zero). -/
def biquadProcess (n : Nat) (s : BiquadState) (inputs : Array Block) (params : Array FloatArray) :
    BiquadState × Array Block :=
  let inp := inputs.getD 0 #[]
  let cs := blockCoefs n s.type s.sampleRate params
  let res : Array (BiquadChan × FloatArray) := Array.ofFn (n := inp.size) fun c =>
    biquadChan n cs (inp.getD c.1 ⟨#[]⟩) (s.chans.getD c.1 {})
  ({ s with chans := res.map Prod.fst }, #[res.map Prod.snd])

theorem biquadIter_size (cs : Array BiquadCoef) (inp : FloatArray) (k i : Nat)
    (p : BiquadChan × FloatArray) :
    (iter (biquadStep cs inp) k i p).2.size = p.2.size + k := by
  induction k generalizing i p with
  | zero => simp [iter]
  | succ k ih =>
    simp only [iter]
    have := ih (i + 1) (biquadStep cs inp i p)
    have h2 : (biquadStep cs inp i p).2.size = p.2.size + 1 := by
      simp [biquadStep, size_push]
    omega

theorem biquadChan_size (n : Nat) (cs : Array BiquadCoef) (inp : FloatArray) (z : BiquadChan) :
    (biquadChan n cs inp z).2.size = n := by
  have := biquadIter_size cs inp n 0 (z, ⟨#[]⟩)
  unfold biquadChan
  simpa [FloatArray.size] using this

/-- Says: the biquad kernel returns one block with the input's number of channels and `n` frames
in each channel. Does not say: the values. -/
theorem biquad_shape (n : Nat) (s : BiquadState) (inputs : Array Block)
    (params : Array FloatArray) :
    let o := (biquadProcess n s inputs params).2
    o.size = 1 ∧ (∀ b ∈ o, b.size = (inputs.getD 0 #[]).size ∧ IsBlock n b) := by
  intro o
  refine ⟨by simp [o, biquadProcess], ?_⟩
  intro b hb
  simp only [o, biquadProcess, Array.mem_singleton] at hb
  subst hb
  refine ⟨by simp, ?_⟩
  intro c hc
  simp only [Array.mem_map, Array.mem_ofFn] at hc
  obtain ⟨p, ⟨j, rfl⟩, rfl⟩ := hc
  exact biquadChan_size n _ _ _

/-- Says: after a block the state holds one `BiquadChan` (four values) for each
channel of the input, so a node whose input keeps its channel count keeps the size of its state
across blocks; the type and the sample rate are unchanged. Does not say: that the stored values
are the right ones (tested with `#guard`), or what happens to the stored values of a channel when
the input channel count changes. -/
theorem biquad_state_size (n : Nat) (s : BiquadState) (inputs : Array Block)
    (params : Array FloatArray) :
    let s' := (biquadProcess n s inputs params).1
    s'.chans.size = (inputs.getD 0 #[]).size ∧ s'.type = s.type ∧ s'.sampleRate = s.sampleRate := by
  simp [biquadProcess]

/-- Says: with a constant channel count the state size is the same before and after a block.
Does not say: anything about the values. -/
theorem biquad_state_size_stable (n : Nat) (s : BiquadState) (inputs : Array Block)
    (params : Array FloatArray) (h : s.chans.size = (inputs.getD 0 #[]).size) :
    (biquadProcess n s inputs params).1.chans.size = s.chans.size := by
  rw [h]; simp [biquadProcess]

/-! ## getFrequencyResponse -/

/-- Errors of `getFrequencyResponse`. -/
inductive FilterError where
  /-- "The three parameters MUST be Float32Arrays of the same length." -/
  | invalidAccessError
  deriving DecidableEq, Repr

def nan : Float := 0.0 / 0.0

/-- Magnitude and phase of `H(e^{i omega})`, `omega = pi * ratio`, ratio being the frequency over
the Nyquist frequency. The numerator and the denominator are split into real and imaginary parts
as in the Web Platform Tests reference (`biquad-getFrequencyResponse.html`); the phase is the
difference of the two arguments, wrapped into `(-pi, pi)`. -/
def responseAt (c : BiquadCoef) (ratio : Float) : Float × Float :=
  let o := piF * ratio
  let nr := c.b0 + c.b1 * Float.cos o + c.b2 * Float.cos (2.0 * o)
  let ni := -(c.b1 * Float.sin o + c.b2 * Float.sin (2.0 * o))
  let dr := 1.0 + c.a1 * Float.cos o + c.a2 * Float.cos (2.0 * o)
  let di := -(c.a1 * Float.sin o + c.a2 * Float.sin (2.0 * o))
  let mag := Float.sqrt ((nr * nr + ni * ni) / (dr * dr + di * di))
  let ph := Float.atan2 ni nr - Float.atan2 di dr
  let ph := if ph ≥ piF then ph - 2.0 * piF else if ph ≤ -piF then ph + 2.0 * piF else ph
  (mag, ph)

/-- The current values of the filter's parameters. -/
structure BiquadParams where
  type : BiquadType := .lowpass
  frequency : Float := 350.0
  detune : Float := 0.0
  q : Float := 1.0
  gain : Float := 0.0

/-- `getFrequencyResponse(frequencyHz, magResponse, phaseResponse)`: the arrays `magResponse` and
`phaseResponse` have lengths `magLen` and `phaseLen`; they must have the length of `frequencyHz`
(else `InvalidAccessError`). A frequency outside `[0, sampleRate / 2]` (or NaN) gives NaN in both
outputs. The parameters are the current values, including `detune`. -/
def getFrequencyResponse (p : BiquadParams) (sampleRate : Float) (frequencyHz : FloatArray)
    (magLen phaseLen : Nat) : Except FilterError (FloatArray × FloatArray) :=
  if magLen = frequencyHz.size ∧ phaseLen = frequencyHz.size then
    let c := coefsAt p.type sampleRate p.frequency p.detune p.q p.gain
    let nyq := sampleRate / 2.0
    let at_ := fun (i : Nat) =>
      let f := getF frequencyHz i
      if f ≥ 0.0 && f ≤ nyq then responseAt c (f / nyq) else (nan, nan)
    .ok (mkChan frequencyHz.size (fun i => (at_ i).1), mkChan frequencyHz.size (fun i => (at_ i).2))
  else .error .invalidAccessError

/-- Says: on success both arrays have the length of `frequencyHz`; the call fails with
`InvalidAccessError` exactly when `magLen` or `phaseLen` differs from that length. Does not say:
the values. -/
theorem frequencyResponse_sizes (p : BiquadParams) (sr : Float) (fs : FloatArray)
    (magLen phaseLen : Nat) :
    (∀ m ph, getFrequencyResponse p sr fs magLen phaseLen = .ok (m, ph) →
      m.size = fs.size ∧ ph.size = fs.size) ∧
    (getFrequencyResponse p sr fs magLen phaseLen = .error .invalidAccessError ↔
      ¬(magLen = fs.size ∧ phaseLen = fs.size)) := by
  constructor
  · intro m ph h
    unfold getFrequencyResponse at h
    split at h
    · injection h with h
      injection h with h1 h2
      subst h1; subst h2
      exact ⟨mkChan_size _ _, mkChan_size _ _⟩
    · cases h
  · unfold getFrequencyResponse
    split <;> simp_all

/-! ## Tests

Reference values: the specification's reference code in the Web Platform Tests,
`webaudio/resources/biquad-filters.js` (`createFilter`, `filterData`) and the response formula of
`the-biquadfilternode-interface/biquad-getFrequencyResponse.html`, run in Node. The parameter
sets come from `biquad-lowpass.html` (cutoff 0, 1, 0.25, 0.25 with detune 100, 0.01 with detune
-200; Q 1; gain 1) and from further cases for the other types. -/

def near (a b : Float) (tol : Float := 1.0e-12) : Bool := (a - b).abs ≤ tol

def coefNear (c : BiquadCoef) (b0 b1 b2 a1 a2 : Float) (tol : Float := 1.0e-12) : Bool :=
  near c.b0 b0 tol && near c.b1 b1 tol && near c.b2 b2 tol && near c.a1 a1 tol && near c.a2 a2 tol

def listNear : List Float → List Float → Bool
  | [], [] => true
  | x :: xs, y :: ys => near x y 1.0e-12 && listNear xs ys
  | _, _ => false

-- lowpass (WPT `biquad-lowpass.html`: cutoff 0.25, q 1, gain 1)
#guard coefNear (biquadCoefs .lowpass 0.25 1 1) 0.1113573689364915 0.222714737872983 0.1113573689364915 (-1.0753618814266488) 0.5207913571726148
#guard coefNear (biquadCoefs .lowpass 0.1 3 6) 0.022058863126275627 0.044117726252551254 0.022058863126275627 (-1.7145674096124806) 0.802802862117583
#guard coefNear (biquadCoefs .lowpass 0.01 10 12) 0.0002455005443062815 0.000491001088612563 0.0002455005443062815 (-1.9891341316454965) 0.9901161338227217
-- lowpass with detune (WPT: cutoff 0.25, detune 100): frequency ratio 0.25 * 2^(100/1200)
#guard coefNear (biquadCoefs .lowpass (0.25 * Float.exp2 (100.0 / 1200.0)) 1 1) 0.12285917490943515 0.2457183498188703 0.12285917490943515 (-1.012919966644805) 0.5043566662825456
-- the same through `coefsAt`: sample rate 32768, frequency 4096 Hz = ratio 0.25, detune 100
#guard coefNear (coefsAt .lowpass 32768 4096 100 1 1) 0.12285917490943515 0.2457183498188703 0.12285917490943515 (-1.012919966644805) 0.5043566662825456
-- lowpass with detune -200 at cutoff 0.01
#guard coefNear (biquadCoefs .lowpass (0.01 * Float.exp2 (-200.0 / 1200.0)) 1 1) 0.00019341297238717605 0.0003868259447743521 0.00019341297238717605 (-1.9745921158314177) 0.9753657677209663
-- highpass
#guard coefNear (biquadCoefs .highpass 0.25 1 1) 0.6490383096498159 (-1.2980766192996318) 0.6490383096498159 (-1.0753618814266488) 0.5207913571726148
#guard coefNear (biquadCoefs .highpass 0.1 3 6) 0.879342567932516 (-1.758685135865032) 0.879342567932516 (-1.7145674096124806) 0.802802862117583
#guard coefNear (biquadCoefs .highpass 0.5 0.5 (-6)) 0.339666889382243 (-0.679333778764486) 0.339666889382243 (-8.31943937716604e-17) 0.3586675575289719
-- bandpass
#guard coefNear (biquadCoefs .bandpass 0.25 1 1) 0.2612038749637414 0 (-0.2612038749637414) (-1.044815499854966) 0.47759225007251715
#guard coefNear (biquadCoefs .bandpass 0.1 3 6) 0.04898021270991402 0 (-0.04898021270991402) (-1.808947131655734) 0.9020395745801718
#guard coefNear (biquadCoefs .bandpass 0.5 0.5 (-6)) 0.5 0 (-0.5) (-6.123233995736766e-17) 0
-- lowshelf
#guard coefNear (biquadCoefs .lowshelf 0.25 1 1) 1.0308982227120056 (-0.9453423546589793) 0.3343732587977228 (-0.9681758039566465) 0.34243803221206126
#guard coefNear (biquadCoefs .lowshelf 0.1 3 6) 1.0791092977509111 (-1.5993157166994727) 0.6377117196113692 (-1.6286222887430097) 0.6875144453187432
#guard coefNear (biquadCoefs .lowshelf 0.5 0.5 (-6)) 0.7079457843841379 (-0.142697493203188) 0.12655537645215206 0.2015655666730532 0.1787642207125312
-- highshelf
#guard coefNear (biquadCoefs .highshelf 0.25 1 1) 1.088389163529884 (-1.0537520534182472) 0.3727058434401048 (-0.9170084241410831) 0.3243513776928242
#guard coefNear (biquadCoefs .highshelf 0.1 3 6) 1.8489900134559332 (-3.01130634757757) 1.2712073435010514 (-1.4820701851358156) 0.5909611945152297
#guard coefNear (biquadCoefs .highshelf 0.01 10 12) 3.919256881906851 (-7.715245453935927) 3.797897302726036 (-1.937267397539238) 0.9391761282361978 1.0e-11
-- peaking
#guard coefNear (biquadCoefs .peaking 0.25 1 1) 1.0305349808560955 (-1.060308210100507) 0.4689672701635827 (-1.060308210100507) 0.49950225101967816
#guard coefNear (biquadCoefs .peaking 0.1 3 6) 1.0350118951651512 (-1.8351994349510743) 0.8946309846293168 (-1.8351994349510743) 0.9296428797944677
#guard coefNear (biquadCoefs .peaking 0.5 0.5 (-6)) 0.7079457843841379 (-5.07617716406917e-17) 0.12105685827224309 (-5.07617716406917e-17) (-0.17099735734361904)
-- notch
#guard coefNear (biquadCoefs .notch 0.25 1 1) 0.7387961250362586 (-1.044815499854966) 0.7387961250362586 (-1.044815499854966) 0.47759225007251715
#guard coefNear (biquadCoefs .notch 0.1 3 6) 0.9510197872900858 (-1.808947131655734) 0.9510197872900858 (-1.808947131655734) 0.9020395745801718
-- allpass
#guard coefNear (biquadCoefs .allpass 0.25 1 1) 0.47759225007251715 (-1.044815499854966) 1 (-1.044815499854966) 0.47759225007251715
#guard coefNear (biquadCoefs .allpass 0.1 3 6) 0.9020395745801718 (-1.808947131655734) 1 (-1.808947131655734) 0.9020395745801718
-- edges of the formulas (WPT reference limits): frequency ratio 0 and 1, Q = 0
#guard coefNear (biquadCoefs .lowpass 0 1 6) 0 0 0 (-2) 1
#guard coefNear (biquadCoefs .lowpass 1 1 6) 1 0 0 0 0
#guard coefNear (biquadCoefs .highpass 0 1 6) 1 0 0 0 0
#guard coefNear (biquadCoefs .highpass 1 1 6) 0 0 0 0 0
#guard coefNear (biquadCoefs .bandpass 0 1 6) 0 0 0 0 0
#guard coefNear (biquadCoefs .bandpass 0.3 0 6) 1 0 0 0 0
#guard coefNear (biquadCoefs .lowshelf 1 1 6) 1.9952623149688797 0 0 0 0
#guard coefNear (biquadCoefs .lowshelf 0 1 6) 1 0 0 0 0
#guard coefNear (biquadCoefs .highshelf 0 1 6) 1.9952623149688797 0 0 0 0
#guard coefNear (biquadCoefs .highshelf 1 1 6) 1 0 0 0 0
#guard coefNear (biquadCoefs .peaking 0.3 0 6) 1.9952623149688797 0 0 0 0
#guard coefNear (biquadCoefs .peaking 0 1 6) 1 0 0 0 0
#guard coefNear (biquadCoefs .notch 0.3 0 6) 0 0 0 0 0
#guard coefNear (biquadCoefs .allpass 0.3 0 6) (-1) 0 0 0 0
#guard coefNear (biquadCoefs .allpass 1 1 6) 1 0 0 0 0
-- a ratio above 1 reads as 1 (computed frequency above Nyquist); a negative or NaN ratio as 0
#guard coefNear (biquadCoefs .lowpass 3.0 1 6) 1 0 0 0 0
#guard coefNear (biquadCoefs .lowpass (-1.0) 1 6) 0 0 0 (-2) 1
#guard coefNear (biquadCoefs .lowpass nan 1 6) 0 0 0 (-2) 1
#guard coefNear (coefsAt .lowpass 44100 30000 0 1 0) 1 0 0 0 0

-- impulse responses (WPT `filterData` on an impulse), first six samples, through the kernel
def impulseBlock (n : Nat) : Block := #[mkChan n (fun i => if i = 0 then 1.0 else 0.0)]

/-- `n` output frames of a one-channel filter with constant parameters, input an impulse. -/
def runImpulse (t : BiquadType) (freqRatio q gain : Float) (n : Nat) : List Float :=
  -- sample rate 2 and frequency `freqRatio` Hz gives the ratio `freqRatio` (Nyquist is 1 Hz)
  let s : BiquadState := { type := t, sampleRate := 2.0 }
  let (_, o) := biquadProcess n s #[impulseBlock n]
    #[⟨#[freqRatio]⟩, ⟨#[0.0]⟩, ⟨#[q]⟩, ⟨#[gain]⟩]
  ((o.getD 0 #[]).getD 0 ⟨#[]⟩).toList

#guard listNear (runImpulse .lowpass 0.25 1 1 6) [0.1113573689364915, 0.3424642076432499, 0.42163636828941625, 0.2750592788000338, 0.07620368707948391, -0.061301954799748815]
#guard listNear (runImpulse .peaking 0.1 3 6 6) [1.0350118951651512, 0.06425381022365184, 0.05035810200235524, 0.032684063165847994, 0.01316672328741638, -0.006220943467659522]
#guard listNear (runImpulse .highshelf 0.5 0.5 (-6) 6) [0.7079457843841379, 0.2853949864063759, 0.057525802160649536, -0.03942319142936594, -0.018229913114632165, 0.003372933326520182]
#guard listNear (runImpulse .allpass 0.3 2 0 6) [0.6635416363380519, -0.3289907511697707, 0.23802361630428187, 0.45103980073589145, 0.28309050094519517, -0.022476312098247297]

-- state carried across blocks: two blocks of 3 frames give the frames of one block of 6
def runTwoBlocks : List Float :=
  let s : BiquadState := { type := .lowpass, sampleRate := 2.0 }
  let ps : Array FloatArray := #[⟨#[0.25]⟩, ⟨#[0.0]⟩, ⟨#[1.0]⟩, ⟨#[1.0]⟩]
  let (s1, o1) := biquadProcess 3 s #[impulseBlock 3] ps
  let (_, o2) := biquadProcess 3 s1 #[#[mkChan 3 (fun _ => 0.0)]] ps
  ((o1.getD 0 #[]).getD 0 ⟨#[]⟩).toList ++ ((o2.getD 0 #[]).getD 0 ⟨#[]⟩).toList

#guard listNear runTwoBlocks [0.1113573689364915, 0.3424642076432499, 0.42163636828941625, 0.2750592788000338, 0.07620368707948391, -0.061301954799748815]

-- state: one `BiquadChan` per channel, created at zero, two channels in and out
#guard
  let s : BiquadState := { type := .lowpass, sampleRate := 2.0 }
  let ins : Array Block := #[#[mkChan 4 (fun _ => 1.0), mkChan 4 (fun _ => 0.0)]]
  let (s1, o) := biquadProcess 4 s ins #[⟨#[0.25]⟩, ⟨#[0.0]⟩, ⟨#[1.0]⟩, ⟨#[1.0]⟩]
  s1.chans.size == 2 && (o.getD 0 #[]).size == 2 && near (s1.chans.getD 1 {}).y1 0.0 && near (s1.chans.getD 1 {}).y2 0.0

-- a-rate frequency: the coefficients change at every frame (frequency ramps 0.2 to 0.5)
#guard
  let s : BiquadState := { type := .lowpass, sampleRate := 2.0 }
  let ps : Array FloatArray := #[⟨#[0.2, 0.3, 0.4, 0.5]⟩, ⟨#[0.0]⟩, ⟨#[1.0]⟩, ⟨#[1.0]⟩]
  let (_, o) := biquadProcess 4 s #[#[mkChan 4 (fun _ => 1.0)]] ps
  let y := ((o.getD 0 #[]).getD 0 ⟨#[]⟩).toList
  -- frame 0 is b0 of the filter at ratio 0.2; the final frame uses the filter at ratio 0.5
  near (y.getD 0 0.0) (biquadCoefs .lowpass 0.2 1 1).b0 && y.length == 4 && (y.getD 3 0.0).isFinite

-- silent input gives silent output from a zero state
#guard (runImpulse .lowpass 0.25 1 1 4).tail!.length == 3
#guard listNear ((fun (l : List Float) => l.map (fun x => x * 0.0)) (runImpulse .notch 0.2 2 0 3)) [0, 0, 0]

-- getFrequencyResponse: peaking 1000 Hz, Q 1, gain 5 dB, sample rate 44100
-- (WPT `biquad-getFrequencyResponse.html` reference at its frequencies)
def peakP : BiquadParams := { type := .peaking, frequency := 1000.0, detune := 0.0, q := 1.0, gain := 5.0 }

def respList (p : BiquadParams) (sr : Float) (fs : List Float) : List (Float × Float) :=
  match getFrequencyResponse p sr ⟨fs.toArray⟩ fs.length fs.length with
  | .ok (m, ph) => (m.toList.zip ph.toList)
  | .error _ => []

def pairNear (xs : List (Float × Float)) (ys : List (Float × Float)) : Bool :=
  xs.length == ys.length && (xs.zip ys).all fun (a, b) => near a.1 b.1 1.0e-9 && near a.2 b.2 1.0e-9

#guard pairNear (respList peakP 44100 [0, 500, 1000, 2000, 10000, 22050])
  [(0.9999999999999942, 0), (1.1962005549543162, 0.2629163809178235), (1.7782794100389194, 0),
   (1.1943690820766926, -0.26229505327233626), (1.0041824496795144, -0.04818099623714622), (1, 0)]
-- lowpass at ratio 0.25 (WPT-style reference)
#guard pairNear (respList { type := .lowpass, frequency := 5512.5, q := 1.0, gain := 0.0 } 44100 [0, 2756.25, 5512.5, 11025, 22050])
  [(1, 0), (1.1358194209026033, -0.5076485260237298), (1.1220184543019636, -1.5707963267948961), (0.18917355823439827, -2.7223825399800328), (0, 0)]
-- allpass: magnitude 1 everywhere
#guard pairNear (respList { type := .allpass, frequency := 6615.0, q := 2.0 } 44100 [0, 3000, 15000])
  [(1, 0), (1, -0.509060073542606), (1, 0.3013038469271293)]
-- detune is part of the current value: frequency 500 Hz with detune 1200 cents is 1000 Hz
#guard pairNear (respList { peakP with frequency := 500.0, detune := 1200.0 } 44100 [1000.0]) [(1.7782794100389194, 0)]
-- outside [0, Nyquist] and NaN give NaN
#guard
  match getFrequencyResponse peakP 44100 ⟨#[-1.0, 22051.0, nan, 1000.0]⟩ 4 4 with
  | .ok (m, ph) =>
    (getF m 0).isNaN && (getF m 1).isNaN && (getF m 2).isNaN && !(getF m 3).isNaN
      && (getF ph 0).isNaN && (getF ph 1).isNaN
  | .error _ => false

def isInvalidAccess (r : Except FilterError (FloatArray × FloatArray)) : Bool :=
  match r with
  | .error .invalidAccessError => true
  | .ok _ => false

-- InvalidAccessError when the output arrays differ in length from frequencyHz
#guard isInvalidAccess (getFrequencyResponse peakP 44100 ⟨#[1.0, 2.0, 3.0]⟩ 3 2)
#guard isInvalidAccess (getFrequencyResponse peakP 44100 ⟨#[1.0, 2.0, 3.0]⟩ 4 3)
#guard !isInvalidAccess (getFrequencyResponse peakP 44100 ⟨#[]⟩ 0 0)

end L4Factoidal.WebAudio.Filters
