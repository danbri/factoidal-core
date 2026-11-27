import L4Factoidal.WebAudio.Kernels
import L4Factoidal.WebAudio.Filters

/-!
# Web Audio: IIRFilterNode

Section "The IIRFilterNode Interface" of the W3C Web Audio API
(https://webaudio.github.io/web-audio-api/). Stage F of
https://github.com/danbri/factoidal-core/issues/1169.

## What is here

* `create`: the constructor's checks (1 to 20 values in each array, else `NotSupportedError`;
  feedforward not all zero and `feedback[0]` not zero, else `InvalidStateError`) and the
  normalization by `feedback[0]`, done in binary64.
* `process`: the difference equation
  `y[n] = sum_{k} b[k] x[n-k] - sum_{k>=1} a[k] y[n-k]` (coefficients already divided by `a[0]`),
  for each channel, with histories kept across blocks. The sums run from the lowest `k` up, so a
  filter made from biquad coefficients computes the same operations in the same order as the
  biquad kernel (direct form I) and gives the same samples bit for bit (`#guard`s).
* `frequencyResponse`: magnitude and phase of `H(e^{i omega})`, `omega = pi f / Nyquist`; NaN for
  `f < 0`, `f > Nyquist` and NaN.

## State

`xh[c]` holds the last `b.size - 1` inputs of channel `c`, oldest first; `yh[c]` the last
`a.size - 1` outputs, oldest first. A channel with no entry starts at zero; the state has one
entry for each channel of the last block. When the input has fewer channels than before, the
extra histories are dropped.

## What is proved

Output shape, the history sizes after a block, the response array sizes, and that `create` refuses
an empty or over-long array. Values are `#guard`s.

## Not done in this file

* Non-finite coefficients (`TypeError` in the interface): the page checks them before `create`.
* The length check of `getFrequencyResponse` (`InvalidAccessError`): the page checks it.
* Flushing of denormals and the tail time: the graph module decides.
-/

namespace L4Factoidal.WebAudio.IIR

open L4Factoidal.WebAudio.Kernels

inductive Error where
  | notSupported (msg : String)
  | invalidState (msg : String)
  deriving Repr

structure State where
  /-- Feedforward coefficients divided by `feedback[0]`. -/
  b : FloatArray
  /-- Feedback coefficients divided by `feedback[0]`; `a[0] = 1`. -/
  a : FloatArray
  /-- Per channel: the last `b.size - 1` inputs, oldest first. -/
  xh : Array FloatArray
  /-- Per channel: the last `a.size - 1` outputs, oldest first. -/
  yh : Array FloatArray
  deriving Inhabited

/-- The constructor of the interface. Order of the checks: lengths (both arrays), all-zero
feedforward, zero `feedback[0]`. -/
def create (feedforward feedback : FloatArray) : Except Error State :=
  if feedforward.size < 1 || 20 < feedforward.size then
    .error (.notSupported "NotSupportedError: feedforward must have 1 to 20 values")
  else if feedback.size < 1 || 20 < feedback.size then
    .error (.notSupported "NotSupportedError: feedback must have 1 to 20 values")
  else if iter (fun i (acc : Bool) => acc && getF feedforward i == 0.0) feedforward.size 0 true then
    .error (.invalidState "InvalidStateError: at least one feedforward value must be non-zero")
  else if getF feedback 0 == 0.0 then
    .error (.invalidState "InvalidStateError: feedback[0] must not be zero")
  else
    let a0 := getF feedback 0
    .ok { b := mkChan feedforward.size fun i => getF feedforward i / a0
          a := mkChan feedback.size fun i => if i = 0 then 1.0 else getF feedback i / a0
          xh := #[], yh := #[] }

/-- Says: an empty or an over-long array (more than 20 values) is refused with `notSupported`.
Does not say: anything about the other checks. -/
theorem create_refuses_size (ff fb : FloatArray)
    (h : ff.size = 0 ∨ 20 < ff.size ∨ fb.size = 0 ∨ 20 < fb.size) :
    ∃ m, create ff fb = .error (.notSupported m) := by
  unfold create
  by_cases h1 : ff.size < 1 || 20 < ff.size
  · rw [if_pos h1]; exact ⟨_, rfl⟩
  · rw [if_neg h1]
    have h2 : fb.size < 1 || 20 < fb.size := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or] at h1 ⊢
      omega
    rw [if_pos h2]; exact ⟨_, rfl⟩

/-- One channel of one block. Returns the output, the new input history and the new output
history. The extended arrays `xe` (history then block) and `ye` (history then outputs so far)
are indexed so that `x[n-k]` is `xe[n + (M-1) - k]` and `y[n-k]` is `ye[size - k]`. -/
def chanProc (n : Nat) (b a xh yh inp : FloatArray) : FloatArray × FloatArray × FloatArray :=
  let m1 := b.size - 1
  let n1 := a.size - 1
  let xe := mkChan (m1 + n) fun i => if i < m1 then getF xh i else getF inp (i - m1)
  let y0 := mkChan n1 fun i => getF yh i
  let ye := iter (fun i (y : FloatArray) =>
      let ff := iter (fun k (acc : Float) => acc + getF b k * getF xe (i + m1 - k)) b.size 0 0.0
      let fb := iter (fun k (acc : Float) => acc + getF a (k + 1) * getF y (y.size - (k + 1)))
        n1 0 0.0
      y.push (ff - fb)) n 0 y0
  (mkChan n fun i => getF ye (i + n1), mkChan m1 fun i => getF xe (n + i),
   mkChan n1 fun i => getF ye (n + i))

/-- `params` is unused. Input 0 has one or more channels; an empty block is one channel of
silence. The output is one block with as many channels as the input (at least 1). -/
def process (n : Nat) (s : State) (inputs : Array Block) (_params : Array FloatArray) :
    State × Array Block :=
  let inp := inputs.getD 0 #[]
  let ch := max 1 inp.size
  let res : Array (FloatArray × FloatArray × FloatArray) := Array.ofFn (n := ch) fun c =>
    chanProc n s.b s.a (s.xh.getD c.1 ⟨#[]⟩) (s.yh.getD c.1 ⟨#[]⟩) (inp.getD c.1 ⟨#[]⟩)
  ({ s with xh := res.map (·.2.1), yh := res.map (·.2.2) }, #[res.map (·.1)])

theorem chanProc_sizes (n : Nat) (b a xh yh inp : FloatArray) :
    (chanProc n b a xh yh inp).1.size = n ∧ (chanProc n b a xh yh inp).2.1.size = b.size - 1 ∧
    (chanProc n b a xh yh inp).2.2.size = a.size - 1 := by
  simp [chanProc, mkChan_size]

/-- Says: the kernel returns one block with `max 1 (input channel count)` channels and `n` frames
in each. Does not say: the values. -/
theorem process_shape (n : Nat) (s : State) (inputs : Array Block) (params : Array FloatArray) :
    (process n s inputs params).2.size = 1 ∧
    (∀ b ∈ (process n s inputs params).2,
      b.size = max 1 (inputs.getD 0 #[]).size ∧ IsBlock n b) := by
  unfold process
  refine ⟨by simp, ?_⟩
  intro b hb
  simp only [Array.mem_singleton] at hb
  subst hb
  refine ⟨by simp, ?_⟩
  intro c hc
  simp only [Array.mem_map, Array.mem_ofFn] at hc
  obtain ⟨p, ⟨j, rfl⟩, rfl⟩ := hc
  exact (chanProc_sizes n _ _ _ _ _).1

/-- Says: after a block the state has one history pair for each output channel, with `b.size - 1`
inputs and `a.size - 1` outputs, and the coefficients are unchanged. Does not say: the values. -/
theorem process_state_sizes (n : Nat) (s : State) (inputs : Array Block) (params : Array FloatArray) :
    let s' := (process n s inputs params).1
    s'.xh.size = max 1 (inputs.getD 0 #[]).size ∧ s'.yh.size = max 1 (inputs.getD 0 #[]).size ∧
    (∀ h ∈ s'.xh, h.size = s.b.size - 1) ∧ (∀ h ∈ s'.yh, h.size = s.a.size - 1) ∧
    s'.b = s.b ∧ s'.a = s.a := by
  intro s'
  refine ⟨by simp [s', process], by simp [s', process], ?_, ?_, rfl, rfl⟩
  · intro h hh
    simp only [s', process, Array.mem_map, Array.mem_ofFn] at hh
    obtain ⟨p, ⟨j, rfl⟩, rfl⟩ := hh
    exact (chanProc_sizes n _ _ _ _ _).2.1
  · intro h hh
    simp only [s', process, Array.mem_map, Array.mem_ofFn] at hh
    obtain ⟨p, ⟨j, rfl⟩, rfl⟩ := hh
    exact (chanProc_sizes n _ _ _ _ _).2.2

/-! ## getFrequencyResponse -/

def piI : Float := 3.141592653589793
def nanI : Float := 0.0 / 0.0

/-- `H(e^{i omega})` for `omega = pi * ratio`: magnitude and phase (the difference of the two
arguments, wrapped into `(-pi, pi)`, as the biquad's `responseAt`). -/
def responseAt (b a : FloatArray) (ratio : Float) : Float × Float :=
  let o := piI * ratio
  let sumC := fun (c : FloatArray) =>
    iter (fun k (acc : Float) => acc + getF c k * Float.cos (k.toFloat * o)) c.size 0 0.0
  let sumS := fun (c : FloatArray) =>
    iter (fun k (acc : Float) => acc + getF c k * Float.sin (k.toFloat * o)) c.size 0 0.0
  let nr := sumC b
  let ni := -(sumS b)
  let dr := sumC a
  let di := -(sumS a)
  let mag := Float.sqrt ((nr * nr + ni * ni) / (dr * dr + di * di))
  let ph := Float.atan2 ni nr - Float.atan2 di dr
  let ph := if ph ≥ piI then ph - 2.0 * piI else if ph ≤ -piI then ph + 2.0 * piI else ph
  (mag, ph)

/-- Magnitudes and phases at `freqs` (Hz). A frequency below 0, above `sampleRate / 2`, or NaN
gives NaN in both. -/
def frequencyResponse (s : State) (sampleRate : Float) (freqs : FloatArray) :
    FloatArray × FloatArray :=
  let nyq := sampleRate / 2.0
  let at_ := fun (i : Nat) =>
    let f := getF freqs i
    if f ≥ 0.0 && f ≤ nyq then responseAt s.b s.a (f / nyq) else (nanI, nanI)
  (mkChan freqs.size fun i => (at_ i).1, mkChan freqs.size fun i => (at_ i).2)

/-- Says: both arrays have as many values as `freqs`. Does not say: the values. -/
theorem frequencyResponse_size (s : State) (sampleRate : Float) (freqs : FloatArray) :
    (frequencyResponse s sampleRate freqs).1.size = freqs.size ∧
    (frequencyResponse s sampleRate freqs).2.size = freqs.size :=
  ⟨mkChan_size _ _, mkChan_size _ _⟩

/-! ## Tests

Cases of `webaudio/the-audio-api/the-iirfilternode-interface` are named at each guard. -/

section Tests

def near (tol : Float) (xs ys : List Float) : Bool :=
  xs.length == ys.length && (List.zip xs ys).all fun (x, y) => (x - y).abs ≤ tol

def fa (xs : List Float) : FloatArray := ⟨xs.toArray⟩

def mk! (ff fb : List Float) : State :=
  match create (fa ff) (fa fb) with
  | .ok s => s
  | .error _ => default

def isNS (r : Except Error State) : Bool := match r with | .error (.notSupported _) => true | _ => false
def isIS (r : Except Error State) : Bool := match r with | .error (.invalidState _) => true | _ => false
def isOk (r : Except Error State) : Bool := match r with | .ok _ => true | _ => false

/-- Run blocks of the sizes given over one channel; returns the final state and the output. -/
def runBlocks (s : State) (sizes : List Nat) (xs : List Float) : State × List Float := Id.run do
  let mut st := s
  let mut rest := xs
  let mut out : List Float := []
  for n in sizes do
    let r := process n st #[#[fa (rest.take n)]] #[]
    st := r.1
    out := out ++ r.2[0]![0]!.data.toList
    rest := rest.drop n
  return (st, out)

def run1 (ff fb xs : List Float) : List Float :=
  (runBlocks (mk! ff fb) [xs.length] xs).2

-- test-iirfilternode.html, iirfilter-basic.html: constructor checks.
#guard isNS (create (fa []) (fa [1.0]))
#guard isNS (create (fa [1.0]) (fa []))
#guard isNS (create (fa []) (fa []))
#guard isNS (create (fa (1.0 :: List.replicate 20 0.0)) (fa [1.0]))
#guard isNS (create (fa [1.0]) (fa (1.0 :: List.replicate 20 0.0)))
#guard isIS (create (fa [0.0, 0.0]) (fa [1.0]))
#guard isIS (create (fa (List.replicate 10 0.0)) (fa [1.0]))
#guard isIS (create (fa [0.5, 0.5]) (fa [0.0]))
#guard isIS (create (fa [1.0]) (fa [0.0, 0.0]))
-- iirfilter-basic.html: 20 values is allowed.
#guard isOk (create (fa (1.0 :: List.replicate 19 0.0)) (fa (1.0 :: List.replicate 19 0.0)))
#guard isOk (create (fa [1.0]) (fa [1.0]))

-- Normalization: b = [2], a = [1] doubles; b = [1], a = [2] halves.
#guard near 1e-15 (run1 [2.0] [1.0] [1, 2, 3]) [2, 4, 6]
#guard near 1e-15 (run1 [1.0] [2.0] [1, 2, 3]) [0.5, 1, 1.5]
-- iirfilter.html coefficient-normalization: a = [2, 1.8] scaled by 2 from [1, 0.9]; the impulse
-- response times 2 equals that of the unscaled filter.
#guard
  let imp := 1.0 :: List.replicate 63 0.0
  let r1 := run1 [1.0] [1.0, 0.9] imp
  let r2 := run1 [1.0] [2.0, 1.8] imp
  near 1e-15 (r2.map (· * 2.0)) r1
-- iirfilter.html one-zero: y(n) = 0.5 (x(n) + x(n-1)) on an impulse: 0.5, 0.5, 0, 0, ...
#guard near 0.0 (run1 [0.5, 0.5] [1.0] (1.0 :: List.replicate 9 0.0)) (0.5 :: 0.5 :: List.replicate 8 0.0)
-- iirfilter.html one-pole: y(n) + c y(n-1) = x(n), impulse: (-c)^n with c = 0.9.
#guard
  let r := run1 [1.0] [1.0, 0.9] (1.0 :: List.replicate 99 0.0)
  near 1e-12 r ((List.range 100).map fun k => (-0.9) ^ k.toFloat)
-- One pole y[n] = x[n] + 0.5 y[n-1] on an impulse across block boundaries: 1, 0.5, 0.25, ...
#guard
  let (_, r) := runBlocks (mk! [1.0] [1.0, -0.5]) [3, 1, 4, 2] (1.0 :: List.replicate 9 0.0)
  near 1e-15 r ((List.range 10).map fun k => 0.5 ^ k.toFloat)
-- A block boundary changes nothing, bit for bit.
def sig : List Float := (List.range 70).map fun i => Float.sin (0.37 * i.toFloat) + 0.25 * Float.cos (1.9 * i.toFloat)
#guard
  let s := mk! [0.2, 0.3, -0.1, 0.05] [1.0, -0.4, 0.2, -0.05]
  (runBlocks s [70] sig).2 == (runBlocks s [7, 1, 30, 32] sig).2
-- Channels: two channels are independent; a new channel starts at zero; fewer channels drop.
#guard
  let s := mk! [1.0] [1.0, -0.5]
  let r := process 2 s #[#[fa [1, 0], fa [0, 1]]] #[]
  r.2[0]!.size == 2 && near 0.0 (r.2[0]![0]!.data.toList) [1, 0.5] &&
  near 0.0 (r.2[0]![1]!.data.toList) [0, 1] && r.1.yh.size == 2 && r.1.xh.size == 2
#guard
  let s := mk! [1.0] [1.0, -0.5]
  let r1 := process 1 s #[#[fa [1]]] #[]
  let r2 := process 2 r1.1 #[#[fa [0, 0], fa [1, 0]]] #[]
  near 0.0 (r2.2[0]![0]!.data.toList) [0.5, 0.25] && near 0.0 (r2.2[0]![1]!.data.toList) [1, 0.5]
-- An empty block is one channel of silence (iir-filter-silent-block-crash.html).
#guard
  let r := process 4 (mk! [1.0] [1.0]) #[#[]] #[]
  r.2[0]!.size == 1 && near 0.0 (r.2[0]![0]!.data.toList) [0, 0, 0, 0]

-- iirfilter.html: an IIR filter made from biquad coefficients gives the same samples as the
-- biquad kernel, bit for bit (same operations in the same order), over three blocks.
def biquadRef (t : Filters.BiquadType) (freq q gain : Float) (sizes : List Nat) (xs : List Float) :
    List Float := Id.run do
  let sr : Float := 24000.0
  let mut st : Filters.BiquadState := { type := t, sampleRate := sr }
  let mut rest := xs
  let mut out : List Float := []
  for n in sizes do
    let r := Filters.biquadProcess n st #[#[fa (rest.take n)]]
      #[⟨#[freq]⟩, ⟨#[0.0]⟩, ⟨#[q]⟩, ⟨#[gain]⟩]
    st := r.1
    out := out ++ r.2[0]![0]!.data.toList
    rest := rest.drop n
  return out

def iirFromBiquad (t : Filters.BiquadType) (freq q gain : Float) : State :=
  let c := Filters.coefsAt t 24000.0 freq 0.0 q gain
  mk! [c.b0, c.b1, c.b2] [1.0, c.a1, c.a2]

#guard
  let sizes := [20, 25, 25]
  [Filters.BiquadType.lowpass, .highpass, .peaking, .lowshelf, .highshelf, .bandpass, .notch,
   .allpass].all fun t =>
    (runBlocks (iirFromBiquad t 3000.0 2.0 6.0) sizes sig).2 == biquadRef t 3000.0 2.0 6.0 sizes sig
-- Frequency response: the 1-pole filter against its analytic response (iirfilter-getFrequencyResponse.html,
-- 1000 frequencies from 0 to Nyquist, sample rate 48000).
#guard
  let freqs := fa ((List.range 1000).map fun k => k.toFloat * (24000.0 / 1000.0))
  let (mag, ph) := frequencyResponse (mk! [1.0] [1.0, -0.9]) 48000.0 freqs
  let scale := piI / 24000.0
  let ws := (List.range 1000).map fun k => scale * (k.toFloat * (24000.0 / 1000.0))
  near 1e-12 mag.data.toList (ws.map fun w => 1.0 / Float.sqrt (1.81 - 1.8 * Float.cos w)) &&
  near 1e-12 ph.data.toList (ws.map fun w => Float.atan (0.9 * Float.sin w / (0.9 * Float.cos w - 1.0)))
-- The same: an IIR filter equivalent to a biquad has the biquad's response.
#guard
  let freqs := fa ((List.range 1000).map fun k => k.toFloat * 24.0)
  [Filters.BiquadType.lowpass, .highpass, .peaking, .lowshelf, .bandpass, .notch].all fun t =>
    let c := Filters.coefsAt t 48000.0 350.0 0.0 1.0 0.0
    let s := mk! [c.b0, c.b1, c.b2] [1.0, c.a1, c.a2]
    let (m, p) := frequencyResponse s 48000.0 freqs
    match Filters.getFrequencyResponse { type := t } 48000.0 freqs 1000 1000 with
    | .ok (bm, bp) => near 1e-9 m.data.toList bm.data.toList && near 1e-9 p.data.toList bp.data.toList
    | .error _ => false
-- Out-of-range frequencies are NaN (iirfilter-getFrequencyResponse.html, test-iirfilternode.html).
#guard
  let (m, p) := frequencyResponse (mk! [1.0] [1.0, -0.9]) 48000.0 (fa [-1.0, 24001.0, 0.0 / 0.0])
  (m.data.toList ++ p.data.toList).all fun x => x != x
#guard
  let (m, p) := frequencyResponse (mk! [0.5, 0.5] [1.0]) 48000.0 (fa [-1.0, 23999.0, 48000.0])
  m.data[0]! != m.data[0]! && m.data[1]! == m.data[1]! && m.data[2]! != m.data[2]! &&
  p.data[0]! != p.data[0]! && p.data[1]! == p.data[1]! && p.data[2]! != p.data[2]!
-- The ends of the range are valid.
#guard
  let (m, _) := frequencyResponse (mk! [1.0] [1.0, -0.9]) 48000.0 (fa [0.0, 24000.0])
  near 1e-12 m.data.toList [10.0, 1.0 / 1.9]
-- iirfilter-normalization-precision.html: scaling both arrays by 0.1 gives the same magnitude
-- (within 1e-3) at 21 frequencies around 6 kHz.
#guard
  let ff := [1.0, 0.0, -1.0]
  let fb := [1.0, -2.0 * 0.9995 * Float.cos (piI / 4.0), 0.9995 * 0.9995]
  let freqs := fa ((List.range 21).map fun k => 5980.0 + 2.0 * k.toFloat)
  let r1 := (frequencyResponse (mk! ff fb) 48000.0 freqs).1.data.toList
  let r2 := (frequencyResponse (mk! (ff.map (· / 10.0)) (fb.map (· / 10.0))) 48000.0 freqs).1.data.toList
  near 1e-3 r2 r1

end Tests

end L4Factoidal.WebAudio.IIR
