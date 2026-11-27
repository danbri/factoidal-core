import L4Factoidal.WebAudio.Kernels
import L4Factoidal.Prim.FloatOfNat

/-!
# Web Audio: PeriodicWave and OscillatorNode

Sections "The PeriodicWave Interface" and "The OscillatorNode Interface" of the W3C Web Audio API
(https://webaudio.github.io/web-audio-api/). Stage B of
https://github.com/danbri/factoidal-core/issues/1169; structure in
`docs/designissues/2026-11-26-foafnaut-audio-plan.md` section 9.

## What is here

* `PeriodicWave`: coefficient arrays `real` (`a`) and `imag` (`b`) with `a[0] = b[0] = 0`, a
  normalization factor, and the constructor rules (`PeriodicWave.create`, `createPeriodicWave`)
  with their errors (`WaveError`).
* The built-in waveforms `sine`, `square`, `sawtooth`, `triangle` by the Fourier coefficients of
  section "Oscillator Coefficients" (`builtinImag`), with `builtinLen = 2048` coefficients
  (partials 1 to 2047).
* Normalization (section "Waveform Normalization"): the factor `f` is the maximum of `|x~(n)|`
  over `N` samples of the series, `N` the smallest power of two with `N >= 4 L`, computed with a
  radix-2 FFT. It is a fixed factor for the wave, applied to every output sample.
* `OscillatorNode` as a block kernel `oscProcess : State → inputs → params → State × outputs`;
  `params[0]` is `frequency`, `params[1]` is `detune` (both a-rate; one value means constant over
  the block). The computed frequency is `frequency * 2^(detune/1200)` (`computedFrequency`).
  The phase is the running sum of `computedFrequency / sampleRate` (in cycles), zero at the start
  frame, kept when the type or wave is changed (`setType`, `setPeriodicWave`).

## Method and error bound

Each output sample is the partial sum of the Fourier series
`scale * sum_{k=1}^{K} (a[k] cos 2 pi k phase + b[k] sin 2 pi k phase)`, with `K` the number of
partials below the Nyquist frequency: the largest `k` with `k |computedFrequency| < sampleRate / 2`
(`partialCount`), and at most the last non-zero coefficient. So no partial at or above the Nyquist
frequency is present, and there is no aliasing from the partials; a frequency at or above Nyquist
gives silence. The sum is computed with one `cos` and one `sin` per sample and the angle-addition
recurrence for the harmonics (`partialSum`), so the cost is `K` multiply-adds per sample.

Error against the Fourier series cut at the same `K` (computed with a separate `cos` and `sin`
for every partial, `directSum`): the recurrence adds rounding error of order `K * 2^-52` times the
sum of `|a[k]|` and `|b[k]|`; the `#guard` tests below check at most `1e-12` for `K` up to 1102
(measured about `2e-15`). Error against the ideal waveform: the omitted partials. For the
built-in waveforms that is the series tail above the Nyquist frequency (the specification allows
this: "The actual waveforms produced by the oscillator may differ to prevent aliasing effects")
and above partial 2047 (only below `sampleRate / 4094` Hz, 11.7 Hz at 48 kHz). The Web Platform
Tests `osc-basic-waveform.html` compare sine and custom waves with `sin`/`cos`; their tolerances
(`2e-5` to `5e-7` absolute) are checked here with `1e-9` (measured at most `8e-15`).

## What is proved

Output shapes; the frame counter advances by `n`; the output is 0 at every frame where the source
is not active (`active` of `Kernels`); the array lengths and index-0 values of the built-in
waveforms and of every successfully created `PeriodicWave`.

## What is tested only with `#guard`

Every statement about a `Float` value.

## Not done in this file

* `AudioParam` automation and clamping of `frequency` and `detune` to their nominal ranges (the
  caller supplies `params`).
* The `start` and `stop` control messages: the state holds the frames (`OscState.start`, `stop`).
* `PeriodicWaveOptions` with `real` of length different from `imag` raising `NotSupportedError`
  (the dictionary text) versus `IndexSizeError` (the constructor steps and the Web Platform Tests):
  this file follows the constructor steps and the tests.
* Values are not rounded to 32-bit floats; `real` and `imag` are 64-bit here.
* A wavetable with interpolation (what browsers do for speed): this file sums the series.
-/

namespace L4Factoidal.WebAudio.Oscillator

open L4Factoidal.WebAudio.Kernels

def piF : Float := 3.141592653589793

/-- Errors of the specification. -/
inductive WaveError where
  /-- Lengths of `real` and `imag` differ, or a length is less than 2. -/
  | indexSizeError
  /-- A coefficient is not finite (the WebIDL conversion of `float`). -/
  | typeError
  /-- `type` set to `"custom"` directly, or `"custom"` with no `PeriodicWave`. -/
  | invalidStateError
  deriving DecidableEq, Repr

inductive OscType where
  | sine | square | sawtooth | triangle | custom
  deriving DecidableEq, Repr

/-- `frequency * pow(2, detune / 1200)`. -/
def computedFrequency (frequency detune : Float) : Float :=
  frequency * Float.exp2 (detune / 1200.0)

/-! ## Coefficient arrays -/

/-- A `FloatArray` of `n` values, element `k` being `f k`. -/
def mkCoefs (n : Nat) (f : Nat → Float) : FloatArray :=
  ⟨Array.ofFn (n := n) fun i => f i.1⟩

theorem mkCoefs_size (n : Nat) (f : Nat → Float) : (mkCoefs n f).size = n := by
  simp [mkCoefs, FloatArray.size]

theorem getF_mkCoefs (n : Nat) (f : Nat → Float) (m : Nat) (h : m < n) :
    getF (mkCoefs n f) m = f m := by
  simp [getF, mkCoefs, FloatArray.size, FloatArray.get!, h]

theorem getF_push (a : FloatArray) (x : Float) (m : Nat) :
    getF (a.push x) m = if m = a.size then x else getF a m := by
  cases a with | mk d =>
  simp only [getF, FloatArray.push, FloatArray.size, FloatArray.get!]
  by_cases h : m = d.size
  · subst h; simp
  · by_cases h2 : m < d.size
    · have h3 : m < d.size + 1 := by omega
      simp [h, h2, h3]; rw [Array.getElem_push]; simp [h2]
    · have h3 : ¬ m < d.size + 1 := by omega
      simp [h, h2, h3]

/-- Number of coefficients of a built-in wave: partials 1 to 2047. -/
def builtinLen : Nat := 2048

/-- `b[n]` of the built-in waveforms ("Oscillator Coefficients"); `b[0] = 0`. `a[n] = 0` always.
square: `2/(n pi) (1 - (-1)^n)`; sawtooth: `(-1)^(n+1) 2/(n pi)`; triangle:
`8 sin(n pi / 2) / (pi n)^2` (the sine is `+1` for `n = 1, 5, ...` and `-1` for `n = 3, 7, ...`,
`0` for even `n`). -/
def builtinImagAt (t : OscType) (k : Nat) : Float :=
  if k = 0 then 0.0 else
  match t with
  | .sine => if k = 1 then 1.0 else 0.0
  | .square => if k % 2 = 1 then 4.0 / (k.toFloat * piF) else 0.0
  | .sawtooth => (if k % 2 = 1 then 2.0 else -2.0) / (k.toFloat * piF)
  | .triangle =>
    if k % 2 = 0 then 0.0
    else (if k % 4 = 1 then 8.0 else -8.0) / ((piF * k.toFloat) * (piF * k.toFloat))
  | .custom => 0.0

def builtinImag (t : OscType) : FloatArray := mkCoefs builtinLen (builtinImagAt t)

def builtinReal : FloatArray := mkCoefs builtinLen (fun _ => 0.0)

/-- Says: each built-in `imag` array has `builtinLen` elements and `b[0] = 0`. Does not say: the
other values (tested with `#guard`). -/
theorem builtinImag_shape (t : OscType) :
    (builtinImag t).size = builtinLen ∧ getF (builtinImag t) 0 = 0.0 := by
  refine ⟨mkCoefs_size _ _, ?_⟩
  have h : 0 < builtinLen := by decide
  rw [builtinImag, getF_mkCoefs _ _ _ h]
  simp [builtinImagAt]

/-- Says: the `real` array of every built-in wave has `builtinLen` elements, and every element is
0 (`a[n] = 0` for all `n`, the waveforms being odd functions). -/
theorem builtinReal_zero : builtinReal.size = builtinLen ∧ ∀ k, getF builtinReal k = 0.0 := by
  refine ⟨mkCoefs_size _ _, ?_⟩
  intro k
  by_cases h : k < builtinLen
  · rw [builtinReal, getF_mkCoefs _ _ _ h]
  · simp [getF, builtinReal, mkCoefs, FloatArray.size, builtinLen] at *
    omega

/-! ## FFT, for the normalization factor -/

def bitrev (x bits : Nat) : Nat := Id.run do
  let mut r := 0
  let mut v := x
  for _ in [0:bits] do
    r := (r <<< 1) ||| (v &&& 1)
    v := v >>> 1
  return r

/-- Radix-2 FFT of `2^bits` complex values: `X[n] = sum_k x[k] e^{sign 2 pi i k n / N}`
(unnormalized). Loops only. -/
def fft (re0 im0 : FloatArray) (bits : Nat) (sign : Float) : FloatArray × FloatArray := Id.run do
  let n := 1 <<< bits
  let mut re := re0
  let mut im := im0
  for i in [0:n] do
    let j := bitrev i bits
    if i < j then
      let tr := re.get! i
      let ti := im.get! i
      re := re.set! i (re.get! j)
      im := im.set! i (im.get! j)
      re := re.set! j tr
      im := im.set! j ti
  let mut len := 2
  for _ in [0:bits] do
    let half := len / 2
    let ang := sign * 2.0 * piF / len.toFloat
    for blk in [0:n / len] do
      let base := blk * len
      for k in [0:half] do
        let wr := Float.cos (ang * k.toFloat)
        let wi := Float.sin (ang * k.toFloat)
        let i := base + k
        let j := i + half
        let xr := re.get! j * wr - im.get! j * wi
        let xi := re.get! j * wi + im.get! j * wr
        let ur := re.get! i
        let ui := im.get! i
        re := re.set! j (ur - xr)
        im := im.set! j (ui - xi)
        re := re.set! i (ur + xr)
        im := im.set! i (ui + xi)
    len := len * 2
  return (re, im)

/-- The normalization factor `f = max_n |x~(n)|` of the specification, with
`x~(n) = sum_k a[k] cos(2 pi k n / N) + b[k] sin(2 pi k n / N)` and `N` the smallest power of two
that is at least `4 L`. `x~(n)` is the real part of the unnormalized inverse DFT of
`a[k] - i b[k]`. -/
def normalizationFactor (a b : FloatArray) : Float :=
  let len := a.size
  let bits := Nat.log2 (4 * len - 1) + 1
  let n := 1 <<< bits
  let re := mkCoefs n (fun k => if k < len then getF a k else 0.0)
  let im := mkCoefs n (fun k => if k < len then -(getF b k) else 0.0)
  let (xr, _) := fft re im bits 1.0
  Id.run do
    let mut m := 0.0
    for k in [0:n] do
      let v := (xr.get! k).abs
      if v > m then m := v
    return m

/-! ## PeriodicWave -/

structure PeriodicWave where
  /-- `[[real]]`: cosine terms; element 0 is 0. -/
  real : FloatArray
  /-- `[[imag]]`: sine terms; element 0 is 0. -/
  imag : FloatArray
  /-- `[[normalize]]`: the inverse of `disableNormalization`. -/
  normalize : Bool
  /-- The factor applied to the series: `1 / f` when normalizing and `f > 0`, else 1. -/
  scale : Float
  /-- The largest `k` with `a[k] ≠ 0` or `b[k] ≠ 0` (0 if there is none); partials above it are
  not summed. -/
  last : Nat
  /-- Every `a[k]` is 0 (the built-in waves, and any wave built with no cosine terms): the series
  is summed with `partialSumSin`, which does not multiply by the zero terms. -/
  realZero : Bool

/-- The last index with a non-zero coefficient. -/
def lastNonZero (a b : FloatArray) (len : Nat) : Nat := Id.run do
  let mut l := 0
  for k in [0:len] do
    if getF a k != 0.0 || getF b k != 0.0 then l := k
  return l

/-- A `PeriodicWave` of `len` coefficients from `real` and `imag` (read as 0 beyond their size),
with element 0 of both set to 0 ("This sets the DC component to 0"). -/
def PeriodicWave.build (len : Nat) (real imag : FloatArray) (disableNormalization : Bool) :
    PeriodicWave :=
  let a := mkCoefs len (fun k => if k = 0 then 0.0 else getF real k)
  let b := mkCoefs len (fun k => if k = 0 then 0.0 else getF imag k)
  let f := if disableNormalization then 0.0 else normalizationFactor a b
  { real := a, imag := b, normalize := !disableNormalization
    scale := if !disableNormalization && f > 0.0 then 1.0 / f else 1.0
    last := lastNonZero a b len
    realZero := a.data.all (fun x => x == 0.0) }

def allFinite (a : FloatArray) : Bool := a.data.all (fun x => x.isFinite)

/-- The `PeriodicWave` constructor (`PeriodicWaveOptions`), steps in order:
non-finite values give `TypeError` (WebIDL `float`); both given with different lengths or a length
below 2, or one given with length below 2, give `IndexSizeError`; none given is the sine wave. -/
def PeriodicWave.create (real imag : Option FloatArray) (disableNormalization : Bool := false) :
    Except WaveError PeriodicWave :=
  if (real.any fun a => !allFinite a) || (imag.any fun a => !allFinite a) then .error .typeError
  else match real, imag with
  | some r, some i =>
    if r.size ≠ i.size ∨ r.size < 2 then .error .indexSizeError
    else .ok (PeriodicWave.build r.size r i disableNormalization)
  | some r, none =>
    if r.size < 2 then .error .indexSizeError
    else .ok (PeriodicWave.build r.size r (mkCoefs r.size (fun _ => 0.0)) disableNormalization)
  | none, some i =>
    if i.size < 2 then .error .indexSizeError
    else .ok (PeriodicWave.build i.size (mkCoefs i.size (fun _ => 0.0)) i disableNormalization)
  | none, none =>
    .ok (PeriodicWave.build 2 ⟨#[0.0, 0.0]⟩ ⟨#[0.0, 1.0]⟩ disableNormalization)

/-- `createPeriodicWave(real, imag, constraints)`: both arrays are given. -/
def createPeriodicWave (real imag : FloatArray) (disableNormalization : Bool := false) :
    Except WaveError PeriodicWave :=
  PeriodicWave.create (some real) (some imag) disableNormalization

/-- Says: a successfully created `PeriodicWave` has `real` and `imag` of the same length, at least
2, and element 0 of both is 0. Does not say: which input arrays succeed (see the definition), or
anything about the values at other indices. -/
theorem create_ok_shape (real imag : Option FloatArray) (d : Bool) (w : PeriodicWave)
    (h : PeriodicWave.create real imag d = .ok w) :
    w.real.size = w.imag.size ∧ 2 ≤ w.real.size ∧ getF w.real 0 = 0.0 ∧ getF w.imag 0 = 0.0 := by
  have key : ∀ len : Nat, 2 ≤ len → ∀ r i : FloatArray, ∀ d : Bool,
      (PeriodicWave.build len r i d).real.size = (PeriodicWave.build len r i d).imag.size ∧
      2 ≤ (PeriodicWave.build len r i d).real.size ∧
      getF (PeriodicWave.build len r i d).real 0 = 0.0 ∧
      getF (PeriodicWave.build len r i d).imag 0 = 0.0 := by
    intro len hl r i d
    have h0 : 0 < len := by omega
    simp only [PeriodicWave.build, mkCoefs_size]
    refine ⟨True.intro, hl, ?_, ?_⟩
    · rw [getF_mkCoefs _ _ _ h0]; simp
    · rw [getF_mkCoefs _ _ _ h0]; simp
  unfold PeriodicWave.create at h
  split at h
  · cases h
  · split at h
    · rename_i r i
      split at h
      · cases h
      · rename_i hc
        injection h with h; subst h
        exact key _ (by omega) _ _ _
    · rename_i r
      split at h
      · cases h
      · rename_i hc
        injection h with h; subst h
        exact key _ (by omega) _ _ _
    · rename_i i
      split at h
      · cases h
      · rename_i hc
        injection h with h; subst h
        exact key _ (by omega) _ _ _
    · injection h with h; subst h
      exact key _ (by omega) _ _ _

/-- The built-in wave of a type (not `custom`; `custom` gives the zero wave), normalized. -/
def builtinWave (t : OscType) : PeriodicWave :=
  PeriodicWave.build builtinLen builtinReal (builtinImag t) false

/-- `builtinWave`, each type's wave computed once, at its first use. Each branch is a closed term,
which Lean evaluates once when it is first needed. A top-level constant is evaluated when the
module starts instead: the waves cost every engine about 340 million instructions at library
load, also on pages with no audio (issue 471). Same value: `builtinWaveCached_eq`. -/
def builtinWaveCached : OscType → PeriodicWave
  | .sine => builtinWave .sine
  | .square => builtinWave .square
  | .sawtooth => builtinWave .sawtooth
  | .triangle => builtinWave .triangle
  | .custom => builtinWave .custom

theorem builtinWaveCached_eq (t : OscType) : builtinWaveCached t = builtinWave t := by
  cases t <;> rfl

/-! ## Evaluation of the series -/

/-- `acc + sum_{j=0}^{m-1} (a[k+j] cos(2 pi (k+j) phase) + b[k+j] sin(2 pi (k+j) phase))`, with
`(ck, sk)` the cosine and sine of `2 pi k phase` and `(c1, s1)` those of `2 pi phase`: the
harmonics come from the angle-addition rule. Tail recursion on the term count. -/
def partialSum (a b : FloatArray) (c1 s1 : Float) : Nat → Nat → Float → Float → Float → Float
  | 0, _, _, _, acc => acc
  | m + 1, k, ck, sk, acc =>
    partialSum a b c1 s1 m (k + 1) (ck * c1 - sk * s1) (sk * c1 + ck * s1)
      (acc + getF a k * ck + getF b k * sk)

/-- `partialSum` for `a` all zero: the same value without the multiplications by `a[k]`.
`acc + 0 * ck` is `acc` because `ck` is finite and `acc` is never `-0` (it starts at `+0` and a
round-to-nearest sum is `-0` only when both addends are `-0`). Tested against `partialSum` with
`#guard`, not proved (the kernel does not unfold `Float` arithmetic). -/
def partialSumSin (b : FloatArray) (c1 s1 : Float) : Nat → Nat → Float → Float → Float → Float
  | 0, _, _, _, acc => acc
  | m + 1, k, ck, sk, acc =>
    partialSumSin b c1 s1 m (k + 1) (ck * c1 - sk * s1) (sk * c1 + ck * s1)
      (acc + getF b k * sk)

/-- The Fourier series cut at `K`, one `cos` and one `sin` per partial (the reference for the error
bound; slower than `partialSum`). -/
def directSum (a b : FloatArray) (phase : Float) (K : Nat) : Float :=
  (List.range K).foldl (fun acc j =>
    let k := j + 1
    let th := 2.0 * piF * k.toFloat * phase
    acc + getF a k * Float.cos th + getF b k * Float.sin th) 0.0

/-- Number of partials below the Nyquist frequency for a computed frequency: the largest `k` with
`k |f| < sampleRate / 2` is `ceil (nyquist / |f|) - 1`; at most the last non-zero coefficient.
A non-finite or zero quotient reads as no partial; frequency 0 gives all partials. -/
def partialCount (w : PeriodicWave) (sampleRate fc : Float) : Nat :=
  let nyq := sampleRate / 2.0
  let a := fc.abs
  if a == 0.0 then w.last
  else
    let q := (nyq / a).ceil
    if q.isFinite then min w.last (q.toUInt64.toNat - 1) else if q > 0.0 then w.last else 0

/-- The sample of the wave at `phase` (in cycles), band-limited for the computed frequency `fc`. -/
def waveAt (w : PeriodicWave) (sampleRate fc phase : Float) : Float :=
  let th := 2.0 * piF * phase
  let c1 := Float.cos th
  let s1 := Float.sin th
  let cnt := partialCount w sampleRate fc
  w.scale * (if w.realZero then partialSumSin w.imag c1 s1 cnt 1 c1 s1 0.0
             else partialSum w.real w.imag c1 s1 cnt 1 c1 s1 0.0)

/-! ## The block kernel -/

structure OscState where
  sampleRate : Float
  type : OscType
  wave : PeriodicWave
  /-- Phase in cycles, in `[0, 1]`; zero until the start frame. -/
  phase : Float := 0.0
  startFrame : Option Nat := none
  stopFrame : Option Nat := none
  /-- Frames rendered so far. -/
  frame : Nat := 0

/-- A new oscillator of a built-in type. `type` `custom` here is `InvalidStateError` ("If this is
set to custom without also specifying a periodicWave"). -/
def OscState.new (sampleRate : Float) (t : OscType) : Except WaveError OscState :=
  match t with
  | .custom => .error .invalidStateError
  | _ => .ok { sampleRate, type := t, wave := builtinWaveCached t }

/-- A new oscillator with a custom wave (the `periodicWave` option, or `setPeriodicWave` at once). -/
def OscState.newCustom (sampleRate : Float) (w : PeriodicWave) : OscState :=
  { sampleRate, type := .custom, wave := w }

/-- The `type` setter: any built-in type; `custom` gives `InvalidStateError`. "When this attribute
is set, the phase of the oscillator MUST be conserved." -/
def OscState.setType (s : OscState) (t : OscType) : Except WaveError OscState :=
  match t with
  | .custom => .error .invalidStateError
  | _ => .ok { s with type := t, wave := builtinWaveCached t }

/-- `setPeriodicWave`: the type becomes `custom`; the phase is kept. -/
def OscState.setPeriodicWave (s : OscState) (w : PeriodicWave) : OscState :=
  { s with type := .custom, wave := w }

/-- `start(when)`: the first frame at or after `when` seconds. -/
def OscState.start (s : OscState) (when_ : Float) : OscState :=
  { s with startFrame := some (frameOfTime when_ s.sampleRate) }

def OscState.stop (s : OscState) (when_ : Float) : OscState :=
  { s with stopFrame := some (frameOfTime when_ s.sampleRate) }

/-- The phase after one frame at computed frequency `fc`: add `fc / sampleRate`, keep the
fractional part; a non-finite result gives 0. -/
def advancePhase (phase fc sampleRate : Float) : Float :=
  let x := phase + fc / sampleRate
  if x.isFinite then x - x.floor else 0.0

/-- One frame: when the source is active, the band-limited sample at the current phase and the
phase advanced by the computed frequency; otherwise 0 and the phase unchanged. -/
def oscStep (s : OscState) (freq det : FloatArray) (i : Nat) (p : Float × FloatArray) :
    Float × FloatArray :=
  if active s.startFrame s.stopFrame (s.frame + i) then
    let fc := computedFrequency (paramAt freq i) (paramAt det i)
    (advancePhase p.1 fc s.sampleRate, p.2.push (waveAt s.wave s.sampleRate fc p.1))
  else (p.1, p.2.push 0.0)

/-- The kernel: one output block of one channel; inputs are ignored. `params[0]` is `frequency`,
`params[1]` is `detune`. -/
def oscProcess (n : Nat) (s : OscState) (_ : Array Block) (params : Array FloatArray) :
    OscState × Array Block :=
  let fr := params.getD 0 ⟨#[]⟩
  let de := params.getD 1 ⟨#[]⟩
  let r := iter (oscStep s fr de) n 0 (s.phase, ⟨#[]⟩)
  ({ s with phase := r.1, frame := s.frame + n }, #[#[r.2]])

theorem oscStep_size (s : OscState) (fr de : FloatArray) (i : Nat) (p : Float × FloatArray) :
    (oscStep s fr de i p).2.size = p.2.size + 1 := by
  unfold oscStep
  split <;> simp [size_push]

theorem oscIter_size (s : OscState) (fr de : FloatArray) (k i : Nat) (p : Float × FloatArray) :
    (iter (oscStep s fr de) k i p).2.size = p.2.size + k := by
  induction k generalizing i p with
  | zero => simp [iter]
  | succ k ih =>
    simp only [iter]
    have := ih (i + 1) (oscStep s fr de i p)
    have h2 := oscStep_size s fr de i p
    omega

/-- Says: the oscillator kernel returns one block of one channel of `n` frames, and its frame
counter advances by `n`. Does not say: the values. -/
theorem osc_shape (n : Nat) (s : OscState) (inputs : Array Block) (params : Array FloatArray) :
    let r := oscProcess n s inputs params
    r.2.size = 1 ∧ (∀ b ∈ r.2, b.size = 1 ∧ IsBlock n b) ∧ r.1.frame = s.frame + n := by
  intro r
  refine ⟨by simp [r, oscProcess], ?_, by simp [r, oscProcess]⟩
  intro b hb
  simp only [r, oscProcess, Array.mem_singleton] at hb
  subst hb
  refine ⟨by simp, ?_⟩
  intro c hc
  simp only [Array.mem_singleton] at hc
  subst hc
  have := oscIter_size s (params.getD 0 ⟨#[]⟩) (params.getD 1 ⟨#[]⟩) n 0 (s.phase, ⟨#[]⟩)
  simpa [FloatArray.size] using this

theorem oscIter_zero (s : OscState) (fr de : FloatArray) (k i : Nat) (p : Float × FloatArray)
    (hi : i = p.2.size)
    (hp : ∀ m, m < p.2.size → active s.startFrame s.stopFrame (s.frame + m) = false →
      getF p.2 m = 0.0) :
    ∀ m, m < (iter (oscStep s fr de) k i p).2.size →
      active s.startFrame s.stopFrame (s.frame + m) = false →
      getF (iter (oscStep s fr de) k i p).2 m = 0.0 := by
  induction k generalizing i p with
  | zero => simpa [iter] using hp
  | succ k ih =>
    simp only [iter]
    apply ih
    · rw [oscStep_size]; omega
    · intro m hm hact
      rw [oscStep_size] at hm
      unfold oscStep
      by_cases ha : active s.startFrame s.stopFrame (s.frame + i) = true
      · simp only [ha, if_true]
        simp only [getF_push]
        by_cases hmi : m = p.2.size
        · subst hmi; rw [← hi] at hact; simp [ha] at hact
        · simp only [hmi, if_false]
          exact hp m (by omega) hact
      · have ha' : active s.startFrame s.stopFrame (s.frame + i) = false := by simpa using ha
        simp only [ha', Bool.false_eq_true, if_false]
        simp only [getF_push]
        by_cases hmi : m = p.2.size
        · simp [hmi]
        · simp only [hmi, if_false]
          exact hp m (by omega) hact

/-- Says: at every frame `j` of the block at which the source is not active (before the start
frame, at or after the stop frame, or never started), the output sample is exactly 0. Does not say:
anything about the samples at active frames. -/
theorem osc_silent_outside (n : Nat) (s : OscState) (inputs : Array Block)
    (params : Array FloatArray) (j : Nat) (hj : j < n)
    (hact : active s.startFrame s.stopFrame (s.frame + j) = false) :
    getF (((oscProcess n s inputs params).2.getD 0 #[]).getD 0 ⟨#[]⟩) j = 0.0 := by
  have hsz := oscIter_size s (params.getD 0 ⟨#[]⟩) (params.getD 1 ⟨#[]⟩) n 0 (s.phase, ⟨#[]⟩)
  have := oscIter_zero s (params.getD 0 ⟨#[]⟩) (params.getD 1 ⟨#[]⟩) n 0 (s.phase, ⟨#[]⟩)
    (by simp [FloatArray.size]) (by intro m hm; simp [FloatArray.size] at hm) j
    (by simp [FloatArray.size] at hsz ⊢; omega) hact
  simpa [oscProcess] using this

/-! ## Tests

Reference values are the formulas of the specification evaluated with `Float.sin` and
`Float.cos`; the cases follow the Web Platform Tests `the-oscillatornode-interface/
osc-basic-waveform.html` (sample rate 44100; sine 100, -100, 2 and 1 Hz; custom wave
`real [0, 1] imag [0, 1]` with `disableNormalization`, 100 and 1 Hz) and
`the-periodicwave-interface/periodicWave.html`, `createPeriodicWaveInfiniteValuesThrows.html`. -/

def maxDiff : List Float → List Float → Float
  | x :: xs, y :: ys => max (x - y).abs (maxDiff xs ys)
  | [], [] => 0.0
  | _, _ => 1.0e30

def fl (l : List Float) : FloatArray := ⟨l.toArray⟩

/-- Render `k` blocks of `blk` frames with constant `frequency` and `detune`, concatenated. -/
def renderBlocks (s : OscState) (blk : Nat) (fr de : FloatArray) : Nat → List Float
  | 0 => []
  | k + 1 =>
    let r := oscProcess blk s #[] #[fr, de]
    ((r.2.getD 0 #[]).getD 0 ⟨#[]⟩).toList ++ renderBlocks r.1 blk fr de k

def render (s : OscState) (blk k : Nat) (f d : Float) : List Float :=
  renderBlocks s blk (fl [f]) (fl [d]) k

def started (s : OscState) : OscState := s.start 0.0

def sr44 : Float := 44100.0

def okOr (r : Except WaveError OscState) (d : OscState) : OscState :=
  match r with | .ok s => s | .error _ => d

def sineState (_ : Unit := ()) : OscState := started (okOr (OscState.new sr44 .sine) (OscState.newCustom sr44 (builtinWave .sine)))

def refSine (f : Float) (n : Nat) : List Float :=
  (List.range n).map fun k => Float.sin (2.0 * piF * f * k.toFloat / sr44)

-- Test 0 to 3 of `osc-basic-waveform.html`: two render quanta (256 frames, as two blocks of 128)
#guard maxDiff (render sineState 128 2 100.0 0.0) (refSine 100.0 256) < 1.0e-9
#guard maxDiff (render sineState 128 2 (-100.0) 0.0) (refSine (-100.0) 256) < 1.0e-9
#guard maxDiff (render sineState 128 2 2.0 0.0) (refSine 2.0 256) < 1.0e-9
#guard maxDiff (render sineState 128 2 1.0 0.0) (refSine 1.0 256) < 1.0e-9
-- state carries across blocks: 2 blocks of 128 equal 1 block of 256, and 4 blocks of 64
#guard maxDiff (render sineState 128 2 440.0 0.0) (render sineState 256 1 440.0 0.0) == 0.0
#guard maxDiff (render sineState 64 4 440.0 0.0) (render sineState 256 1 440.0 0.0) == 0.0

def customWave (real imag : List Float) (disable : Bool) : PeriodicWave :=
  match createPeriodicWave (fl real) (fl imag) disable with
  | .ok w => w
  | .error _ => builtinWave .sine

def customState (real imag : List Float) (disable : Bool) : OscState :=
  started (OscState.newCustom sr44 (customWave real imag disable))

def refCustom (f a1 b1 : Float) (n : Nat) : List Float :=
  (List.range n).map fun k =>
    let w := 2.0 * piF * f * k.toFloat / sr44
    a1 * Float.cos w + b1 * Float.sin w

-- Test 4 and 5: custom wave `real [0, 1] imag [0, 1]`, `disableNormalization`, 100 and 1 Hz
#guard maxDiff (render (customState [0, 1] [0, 1] true) 128 2 100.0 0.0) (refCustom 100.0 1.0 1.0 256) < 1.0e-9
#guard maxDiff (render (customState [0, 1] [0, 1] true) 128 2 1.0 0.0) (refCustom 1.0 1.0 1.0 256) < 1.0e-9
-- the same wave normalized: peak of cos + sin is sqrt 2, so the scale is 1 / sqrt 2
#guard (maxDiff [(customWave [0, 1] [0, 1] false).scale] [0.7071067811865476]) < 1.0e-12
#guard (customWave [0, 1] [0, 1] true).scale == 1.0
#guard (customWave [0, 1] [0, 1] true).normalize == false && (customWave [0, 1] [0, 1] false).normalize == true

-- `periodicWave.html` output test: real[1] = 2, real[99] = 3, fundamental 19 Hz, normalized by the
-- peak 5; imag[0] = 6 is ignored, imag[3] = 0.5, fundamental 551 Hz, normalized by 0.5
def realWave : List Float := (List.range 100).map fun k => if k = 1 then 2.0 else if k = 99 then 3.0 else 0.0
def imagWave : List Float := [6.0, 0.0, 0.0, 0.5]
#guard maxDiff [(customWave realWave (List.replicate 100 0.0) false).scale] [0.2] < 1.0e-12
#guard maxDiff (render (customState realWave (List.replicate 100 0.0) false) 128 2 19.0 0.0)
  ((List.range 256).map fun k =>
    (2.0 * Float.cos (2.0 * piF * 19.0 * k.toFloat / sr44)
      + 3.0 * Float.cos (2.0 * piF * 99.0 * 19.0 * k.toFloat / sr44)) / 5.0) < 1.0e-9
#guard maxDiff (render (customState (List.replicate 4 0.0) imagWave false) 128 2 551.0 0.0)
  ((List.range 256).map fun k => Float.sin (2.0 * piF * 3.0 * 551.0 * k.toFloat / sr44)) < 1.0e-9
#guard (customWave (List.replicate 4 0.0) imagWave false).imag.size == 4
#guard getF (customWave (List.replicate 4 0.0) imagWave false).imag 0 == 0.0

-- built-in coefficients ("Oscillator Coefficients")
def coefNear (a b : Float) : Bool := (a - b).abs < 1.0e-14
#guard getF (builtinImag .sine) 1 == 1.0 && getF (builtinImag .sine) 2 == 0.0
#guard coefNear (getF (builtinImag .square) 1) (4.0 / piF) && getF (builtinImag .square) 2 == 0.0
  && coefNear (getF (builtinImag .square) 3) (4.0 / (3.0 * piF))
#guard coefNear (getF (builtinImag .sawtooth) 1) (2.0 / piF) && coefNear (getF (builtinImag .sawtooth) 2) (-1.0 / piF)
  && coefNear (getF (builtinImag .sawtooth) 3) (2.0 / (3.0 * piF))
#guard coefNear (getF (builtinImag .triangle) 1) (8.0 / (piF * piF)) && getF (builtinImag .triangle) 2 == 0.0
  && coefNear (getF (builtinImag .triangle) 3) (-8.0 / (9.0 * piF * piF))
  && coefNear (getF (builtinImag .triangle) 5) (8.0 / (25.0 * piF * piF))
#guard (builtinImag .square).size == 2048 && builtinReal.size == 2048 && getF (builtinImag .sawtooth) 0 == 0.0
-- the sine wave needs one partial; built-in sine is not rescaled
#guard (builtinWave .sine).last == 1 && (builtinWave .sine).scale == 1.0
-- the normalized square has maximum 1 over the table (Gibbs overshoot makes the scale below 1)
#guard (builtinWave .square).scale < 1.0 && (builtinWave .square).scale > 0.8
#guard (builtinWave .sawtooth).scale < 1.0 && (builtinWave .sawtooth).scale > 0.8

-- waveforms at chosen phases, unnormalized wave of many partials (error from the series tail)
def rawWave (t : OscType) : PeriodicWave := PeriodicWave.build builtinLen builtinReal (builtinImag t) true
-- square: 1 on (0, pi), so phase 0.25 gives 1 and phase 0.75 gives -1
#guard (waveAt (rawWave .square) 44100.0 1.0 0.25 - 1.0).abs < 1.0e-3
#guard (waveAt (rawWave .square) 44100.0 1.0 0.75 + 1.0).abs < 1.0e-3
-- sawtooth: x = t / pi on (-pi, pi]: phase 0.25 (t = pi/2) gives 0.5; phase 0.75 (t = 3 pi / 2) gives -0.5
#guard (waveAt (rawWave .sawtooth) 44100.0 1.0 0.25 - 0.5).abs < 1.0e-3
#guard (waveAt (rawWave .sawtooth) 44100.0 1.0 0.75 + 0.5).abs < 1.0e-3
-- triangle: 2 t / pi on [0, pi/2]: phase 0.125 gives 0.5, phase 0.25 gives 1, phase 0.5 gives 0
#guard (waveAt (rawWave .triangle) 44100.0 1.0 0.125 - 0.5).abs < 1.0e-6
#guard (waveAt (rawWave .triangle) 44100.0 1.0 0.25 - 1.0).abs < 1.0e-3
#guard (waveAt (rawWave .triangle) 44100.0 1.0 0.375 - 0.5).abs < 1.0e-6
#guard (waveAt (rawWave .triangle) 44100.0 1.0 0.75 + 1.0).abs < 1.0e-3
-- sine at phase 0.25 is 1
#guard (waveAt (builtinWave .sine) 44100.0 440.0 0.25 - 1.0).abs < 1.0e-14
-- `partialSumSin` against `partialSum`: bit equal on the built-in waves (a = 0) at many phases.
private def sinSumSame (t : OscType) (cnt : Nat) : Bool :=
  (List.range 12).all fun i =>
    let th := 2.0 * piF * (i.toFloat * 0.0831)
    let c1 := Float.cos th
    let s1 := Float.sin th
    let w := builtinWave t
    (partialSumSin w.imag c1 s1 cnt 1 c1 s1 0.0).toBits == (partialSum w.real w.imag c1 s1 cnt 1 c1 s1 0.0).toBits
#guard sinSumSame .sine 1 && sinSumSame .square 217 && sinSumSame .sawtooth 218 &&
  sinSumSame .triangle 2047 && sinSumSame .sawtooth 0
#guard (builtinWave .sawtooth).realZero && (builtinWave .sine).realZero

-- error bound of the recurrence against one `cos` and `sin` per partial
def sawW (_ : Unit := ()) : PeriodicWave := builtinWave .sawtooth
#guard (partialCount sawW 44100.0 440.0) == 50
#guard (partialCount sawW 44100.0 20.0) == 1102
#guard (waveAt sawW 44100.0 440.0 0.123 - (sawW ()).scale * directSum (sawW ()).real (sawW ()).imag 0.123 50).abs < 1.0e-12
#guard (waveAt sawW 44100.0 20.0 0.4321 - (sawW ()).scale * directSum (sawW ()).real (sawW ()).imag 0.4321 1102).abs < 1.0e-12
#guard (waveAt sawW 44100.0 20.0 0.9999 - (sawW ()).scale * directSum (sawW ()).real (sawW ()).imag 0.9999 1102).abs < 1.0e-12

-- band limit: no partial at or above Nyquist
-- wave with partials 1 to 3 of equal weight, not normalized
def threeW (_ : Unit := ()) : PeriodicWave := customWave [0, 0, 0, 0] [0, 1, 1, 1] true
#guard partialCount threeW 44100.0 (44100.0 / 8.0) == 3   -- 4 f = 11025 ... partials 1..3 are below 22050
#guard partialCount threeW 44100.0 (44100.0 / 3.0) == 1   -- nyquist / f = 1.5: only partial 1
#guard partialCount (customWave (List.replicate 40 0.0) (List.replicate 40 1.0) true) 44100.0 22050.0 == 0   -- f = Nyquist
#guard partialCount (customWave (List.replicate 40 0.0) (List.replicate 40 1.0) true) 44100.0 30000.0 == 0   -- above Nyquist
#guard partialCount (customWave (List.replicate 40 0.0) (List.replicate 40 1.0) true) 44100.0 (-22050.0) == 0
#guard partialCount (customWave (List.replicate 40 0.0) (List.replicate 40 1.0) true) 44100.0 11025.0 == 1   -- f = Nyquist / 2
#guard partialCount (customWave (List.replicate 40 0.0) (List.replicate 40 1.0) true) 44100.0 0.0 == 39   -- f = 0: all
-- output at and above Nyquist is silence for every type
#guard (render (started (okOr (OscState.new sr44 .sawtooth) sineState)) 128 1 22050.0 0.0).all (· == 0.0)
#guard (render (started (okOr (OscState.new sr44 .square) sineState)) 128 1 30000.0 0.0).all (· == 0.0)
#guard (render sineState 128 1 22049.0 0.0).any (· != 0.0)
-- a sine just below Nyquist keeps its single partial
#guard maxDiff (render sineState 128 1 21000.0 0.0) (refSine 21000.0 128) < 1.0e-9
-- three-partial wave at 44100/8 Hz: all three partials; at 44100/3 Hz only the fundamental
#guard maxDiff (render (started (OscState.newCustom sr44 threeW)) 128 1 (44100.0 / 8.0) 0.0)
  ((List.range 128).map fun k =>
    let w := 2.0 * piF * (44100.0 / 8.0) * k.toFloat / sr44
    Float.sin w + Float.sin (2.0 * w) + Float.sin (3.0 * w)) < 1.0e-9
#guard maxDiff (render (started (OscState.newCustom sr44 threeW)) 128 1 (44100.0 / 3.0) 0.0)
  ((List.range 128).map fun k => Float.sin (2.0 * piF * (44100.0 / 3.0) * k.toFloat / sr44)) < 1.0e-9

-- detune: 1200 cents is one octave; the computed frequency is frequency * 2^(detune/1200)
#guard maxDiff [computedFrequency 440.0 1200.0] [880.0] < 1.0e-9
#guard maxDiff [computedFrequency 880.0 (-1200.0)] [440.0] < 1.0e-9
#guard maxDiff (render sineState 128 2 440.0 1200.0) (render sineState 128 2 880.0 0.0) < 1.0e-9
#guard maxDiff (render sineState 128 2 440.0 (-1200.0)) (render sineState 128 2 220.0 0.0) < 1.0e-9
-- detune moves a frequency above Nyquist: 15000 Hz plus an octave is silent
#guard (render sineState 128 1 15000.0 1200.0).all (· == 0.0)
-- a-rate frequency: first frame at 0 Hz, the phase advances by the frequency of each frame
#guard
  let s := sineState
  let r := oscProcess 4 s #[] #[fl [0.0, 441.0, 441.0, 441.0], fl [0.0]]
  let y := ((r.2.getD 0 #[]).getD 0 ⟨#[]⟩).toList
  maxDiff y [0.0, 0.0, Float.sin (2.0 * piF * 441.0 / sr44), Float.sin (2.0 * piF * 882.0 / sr44)] < 1.0e-9

-- start and stop: cosine wave, so the first active sample is 1
def cosState (_ : Unit := ()) : OscState := OscState.newCustom sr44 (customWave [0, 1] [0, 0] true)
def window (_ : Unit := ()) : OscState := ((cosState ()).start (5.0 / 44100.0)).stop (20.0 / 44100.0)
#guard
  let y := render window 128 1 1000.0 0.0
  (y.take 5).all (· == 0.0) && (y.drop 20).all (· == 0.0) && y.getD 5 0.0 == 1.0
    && (y.getD 6 0.0 - Float.cos (2.0 * piF * 1000.0 / sr44)).abs < 1e-12
-- a source that was never started is silent; a stop frame before the start frame is silent
#guard (render (OscState.newCustom sr44 (customWave [0, 1] [0, 0] true)) 128 1 1000.0 0.0).all (· == 0.0)
#guard (render (((cosState ()).start (30.0 / 44100.0)).stop (10.0 / 44100.0)) 128 1 1000.0 0.0).all (· == 0.0)
-- the start is in the second block: the phase is 0 there
#guard
  let y := render ((cosState ()).start (200.0 / 44100.0)) 128 2 1000.0 0.0
  (y.take 200).all (· == 0.0) && y.getD 200 0.0 == 1.0

-- phase is conserved when the type changes
#guard
  let r := oscProcess 100 sineState #[] #[fl [440.0], fl [0.0]]
  match r.1.setType .square with
  | .ok s2 => s2.phase == r.1.phase && s2.type == .square && s2.phase > 0.0
  | .error _ => false
#guard
  let r := oscProcess 100 sineState #[] #[fl [440.0], fl [0.0]]
  (r.1.setPeriodicWave (customWave [0, 1] [0, 0] true)).phase == r.1.phase

-- errors of the specification
def isErr (r : Except WaveError α) (e : WaveError) : Bool :=
  match r with | .error e' => e' == e | .ok _ => false
def isOkW (r : Except WaveError α) : Bool :=
  match r with | .ok _ => true | .error _ => false
-- `type` set to "custom" directly
#guard isErr ((sineState ()).setType .custom) .invalidStateError
#guard isErr (OscState.new sr44 .custom) .invalidStateError
-- different lengths (`periodicWave.html`: 512 and 4), and lengths below 2
#guard isErr (createPeriodicWave (mkCoefs 512 (fun _ => 0.0)) (mkCoefs 4 (fun _ => 0.0))) .indexSizeError
#guard isErr (createPeriodicWave (fl [0.0]) (fl [0.0])) .indexSizeError
#guard isErr (createPeriodicWave (fl []) (fl [])) .indexSizeError
#guard isErr (PeriodicWave.create (some (fl [0.0])) none) .indexSizeError
#guard isErr (PeriodicWave.create none (some (fl [1.0]))) .indexSizeError
-- non-finite values (`createPeriodicWaveInfiniteValuesThrows.html`)
#guard isErr (createPeriodicWave (fl [0.0, 1.0 / 0.0]) (fl [0.0, 1.0])) .typeError
#guard isErr (createPeriodicWave (fl [0.0, 1.0]) (fl [1.0, 1.0 / 0.0])) .typeError
#guard isErr (createPeriodicWave (fl [0.0, 0.0 / 0.0]) (fl [0.0, 1.0])) .typeError
#guard isErr (createPeriodicWave (fl [0.0, -1.0 / 0.0]) (fl [0.0, 1.0])) .typeError
-- valid: equal lengths of 2 and of 8192 (`periodicWave.html` "create with factory method")
#guard isOkW (createPeriodicWave (fl [0.0, 1.0]) (fl [0.0, 0.0]))
#guard match createPeriodicWave (mkCoefs 8192 (fun _ => 0.0)) (mkCoefs 8192 (fun _ => 0.0)) with
  | .ok w => w.real.size == 8192 && w.imag.size == 8192 && w.scale == 1.0 && w.last == 0
  | .error _ => false
-- only `real`, only `imag`, neither
#guard match PeriodicWave.create (some (fl [5.0, 1.0])) none with
  | .ok w => w.imag.size == 2 && getF w.real 0 == 0.0 && getF w.real 1 == 1.0 && getF w.imag 1 == 0.0
  | .error _ => false
#guard match PeriodicWave.create none (some (fl [5.0, 1.0, 2.0])) with
  | .ok w => w.real.size == 3 && getF w.imag 0 == 0.0 && getF w.imag 2 == 2.0
  | .error _ => false
#guard match PeriodicWave.create none none with
  | .ok w => w.real.size == 2 && getF w.imag 1 == 1.0 && w.scale == 1.0
  | .error _ => false

end L4Factoidal.WebAudio.Oscillator
