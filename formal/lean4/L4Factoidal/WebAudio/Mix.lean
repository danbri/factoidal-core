/-!
# Web Audio API: channel rules of an `AudioNode` input

Follows https://webaudio.github.io/web-audio-api/ : the `AudioNode` attributes `channelCount`,
`channelCountMode`, `channelInterpretation`, the `ChannelCountMode` enumeration description, and
section 4 "Channel Up-Mixing and Down-Mixing" (4.1 Speaker Channel Layouts, 4.2 Channel Ordering,
4.4 Up Mixing Speaker Layouts, 4.5 Down Mixing Speaker Layouts).
Test reference: WPT `webaudio/the-audio-api/the-audionode-interface/audionode-channel-rules.html`
and `webaudio/resources/mixing-rules.js` (its `computeNumberOfChannels`, `speakersSum`,
`discreteSum`).

Stage B of https://github.com/danbri/factoidal-core/issues/1169 (audio in Foafnaut); plan:
`docs/designissues/2026-11-26-foafnaut-audio-plan.md`, section 4.

Layers:
* `computedChannels`: the rule for `computedNumberOfChannels` (natural numbers).
* `matrixWith` / `matrix`: the mixing as exact rational coefficients. Row `r` is the output
  channel `r`; column `c` is the input channel `c`.
* `apply`, `mixInput`: evaluation on blocks of `Float` samples. Lean's `Float` is opaque to the
  kernel, so the theorems are stated over `Rat` and `Nat`, and the `Float` code is tested
  against the `Rat` matrices with `#guard`.

Coefficients. The spec writes 0.5, 0.25 and `sqrt(0.5)`. 0.5 and 0.25 are exact (1/2, 1/4).
`sqrt(0.5)` is irrational, so `matrixWith` takes it as a rational parameter `s`; `matrix` uses
`sqrtHalf = 70710678/100000000` (0.70710678, which differs from the real value by under
1.0e-9; the WPT reference uses `Math.SQRT1_2`). Theorems that involve `s` hold for every `s`.

The no-connection case. The spec's `ChannelCountMode` text gives no value for an input with no
connections. The WPT reference (`computeNumberOfChannels`) starts from 1 ("Must have at least
one channel") for `max` and `clamped-max`, and this file follows it: an input with no
connections has one channel (of silence, by `mixInput`).

Layouts supported by the speaker rules: 1 (mono), 2 (stereo), 4 (quad), 6 (5.1), channel order
by section 4.2: mono `M`; stereo `L R`; quad `L R SL SR`; 5.1 `L R C LFE SL SR`. For any pair
of counts the spec's tables do not define, `speakers` behaves as `discrete` (the same-count
case is then the identity, as WPT `speakersSum` does).
Not covered: `ChannelCountMode` constraints per node type, the tail-time rule of section 4.3,
channel layouts beyond 6 channels, and the exceptions (`NotSupportedError`) for `channelCount`
of 0.
-/

namespace L4Factoidal.WebAudio.Mix

/-- `ChannelCountMode` enumeration: "max", "clamped-max", "explicit". -/
inductive CountMode where
  | max | clampedMax | explicit
  deriving DecidableEq, Repr

/-- `ChannelInterpretation` enumeration: "speakers", "discrete". -/
inductive Interpretation where
  | speakers | discrete
  deriving DecidableEq, Repr

/-- `computedNumberOfChannels` per the `ChannelCountMode` description.
`explicit`: `channelCount`. `max`: the maximum over the connections (`channelCount` ignored).
`clamped-max`: that maximum clamped to `channelCount`. The maximum starts from 1 (see the
header on the no-connection case). `inputs` are the channel counts of the connections. -/
def computedChannels (mode : CountMode) (channelCount : Nat) (inputs : List Nat) : Nat :=
  match mode with
  | .explicit => channelCount
  | .max => inputs.foldl Nat.max 1
  | .clampedMax => Nat.min (inputs.foldl Nat.max 1) channelCount

theorem foldl_max_ge (xs : List Nat) (a : Nat) : a ≤ xs.foldl Nat.max a := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih => exact Nat.le_trans (Nat.le_max_left a x) (ih (Nat.max a x))

theorem le_foldl_max_of_mem {xs : List Nat} {x : Nat} (h : x ∈ xs) (a : Nat) :
    x ≤ xs.foldl Nat.max a := by
  induction xs generalizing a with
  | nil => cases h
  | cons y ys ih =>
    cases h with
    | head => exact Nat.le_trans (Nat.le_max_right a x) (foldl_max_ge ys _)
    | tail _ h => exact ih h _

theorem foldl_max_le {xs : List Nat} {a b : Nat} (ha : a ≤ b) (h : ∀ x ∈ xs, x ≤ b) :
    xs.foldl Nat.max a ≤ b := by
  induction xs generalizing a with
  | nil => simpa using ha
  | cons y ys ih =>
    exact ih (Nat.max_le.mpr ⟨ha, h y (by simp)⟩) (fun x hx => h x (by simp [hx]))

/-- Says: in mode "explicit" the result is `channelCount`, whatever the connections.
Does not say: that `channelCount` is a valid value (the IDL refuses 0). -/
theorem computedChannels_explicit (c : Nat) (xs : List Nat) :
    computedChannels .explicit c xs = c := rfl

/-- Says: in mode "clamped-max" the result is at most `channelCount`.
Does not say: that it is at least 1 (that needs `channelCount ≥ 1`, which the IDL enforces). -/
theorem computedChannels_clampedMax_le (c : Nat) (xs : List Nat) :
    computedChannels .clampedMax c xs ≤ c := by
  simp only [computedChannels]; exact Nat.min_le_right _ _

/-- Says: in mode "max" the result is at least every connection's channel count, at least 1, and
at most any bound `b ≥ 1` that bounds every connection (so it is their maximum, floored at 1).
With no connection it is 1. Does not say: anything about `channelCount` (ignored in this
mode). -/
theorem computedChannels_max (xs : List Nat) :
    (∀ x ∈ xs, x ≤ computedChannels .max 0 xs) ∧ 1 ≤ computedChannels .max 0 xs ∧
    (∀ b, 1 ≤ b → (∀ x ∈ xs, x ≤ b) → computedChannels .max 0 xs ≤ b) ∧
    computedChannels .max 0 [] = 1 := by
  refine ⟨fun x hx => le_foldl_max_of_mem hx 1, foldl_max_ge xs 1,
    fun b hb h => foldl_max_le hb h, rfl⟩

/-- Says: "clamped-max" is "max" followed by `min` with `channelCount`.
Does not say: more than the definition. -/
theorem computedChannels_clampedMax_eq (c : Nat) (xs : List Nat) :
    computedChannels .clampedMax c xs = Nat.min (computedChannels .max c xs) c := rfl

/-! ## Matrices -/

/-- The rational used for `sqrt(0.5)`; see the header. -/
def sqrtHalf : Rat := 70710678 / 100000000

/-- Section 4.4 and 4.5 tables. `none` when the spec's tables define no rule for the pair.
Rows are output channels, columns input channels, order of section 4.2. `s` stands for
`sqrt(0.5)`. -/
def speakerRows (s : Rat) (f t : Nat) : Option (List (List Rat)) :=
  match f, t with
  -- 4.4 mono up-mix: 1 -> 2, 1 -> 4, 1 -> 5.1
  | 1, 2 => some [[1], [1]]
  | 1, 4 => some [[1], [1], [0], [0]]
  | 1, 6 => some [[0], [0], [1], [0], [0], [0]]
  -- 4.4 stereo up-mix: 2 -> 4, 2 -> 5.1
  | 2, 4 => some [[1, 0], [0, 1], [0, 0], [0, 0]]
  | 2, 6 => some [[1, 0], [0, 1], [0, 0], [0, 0], [0, 0], [0, 0]]
  -- 4.4 quad up-mix: 4 -> 5.1 (L, R, C=0, LFE=0, SL, SR)
  | 4, 6 => some [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0],
                  [0, 0, 1, 0], [0, 0, 0, 1]]
  -- 4.5 mono down-mix: 2 -> 1, 4 -> 1, 5.1 -> 1
  | 2, 1 => some [[1/2, 1/2]]
  | 4, 1 => some [[1/4, 1/4, 1/4, 1/4]]
  | 6, 1 => some [[s, s, 1, 0, 1/2, 1/2]]
  -- 4.5 stereo down-mix: 4 -> 2, 5.1 -> 2
  | 4, 2 => some [[1/2, 0, 1/2, 0], [0, 1/2, 0, 1/2]]
  | 6, 2 => some [[1, 0, s, 0, s, 0], [0, 1, s, 0, 0, s]]
  -- 4.5 quad down-mix: 5.1 -> 4
  | 6, 4 => some [[1, 0, s, 0, 0, 0], [0, 1, s, 0, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]]
  | _, _ => none

/-- The discrete rule (`channelInterpretation` "discrete", and the fallback for `speakers`):
output channel `r` is input channel `r` when it exists, else silence; extra inputs are dropped.
Entry `(r, c)` is 1 when `r = c`, else 0. -/
def discreteEntry (r c : Nat) : Rat := if r = c then 1 else 0

def discreteMatrix (f t : Nat) : Array (Array Rat) :=
  Array.ofFn (n := t) fun r => Array.ofFn (n := f) fun c => discreteEntry r.val c.val

/-- Mixing matrix with `sqrt(0.5)` given as `s`: `t` rows of `f` coefficients. -/
def matrixWith (s : Rat) (interp : Interpretation) (f t : Nat) : Array (Array Rat) :=
  match interp with
  | .discrete => discreteMatrix f t
  | .speakers =>
    match speakerRows s f t with
    | some rows => (rows.map List.toArray).toArray
    | none => discreteMatrix f t

/-- `matrixWith sqrtHalf`. -/
def matrix (interp : Interpretation) (f t : Nat) : Array (Array Rat) :=
  matrixWith sqrtHalf interp f t

theorem speakerRows_shape (s : Rat) (f t : Nat) (rows : List (List Rat))
    (h : speakerRows s f t = some rows) :
    rows.length = t ∧ ∀ r ∈ rows, r.length = f := by
  unfold speakerRows at h
  split at h <;> first | (cases h) | skip
  all_goals first | contradiction | (simp; done) | skip

/-- Says: the matrix has `t` rows, each of `f` coefficients, for every interpretation and every
pair of counts (so the mixing is total: no pair is left without a rule).
Does not say: anything about the coefficient values. -/
theorem matrix_shape (s : Rat) (i : Interpretation) (f t : Nat) :
    (matrixWith s i f t).size = t ∧ ∀ r ∈ (matrixWith s i f t).toList, r.size = f := by
  cases i <;> simp only [matrixWith, discreteMatrix] <;> try (simp; done)
  split
  · rename_i rows h
    obtain ⟨h1, h2⟩ := speakerRows_shape s f t rows h
    refine ⟨by simp [h1], ?_⟩
    intro r hr
    simp at hr
    obtain ⟨l, hl, rfl⟩ := hr
    simp [h2 l hl]
  · simp

/-- Says: with the discrete rule, row `r < min f t` is the unit vector of channel `r`, and rows
`r ≥ f` are zero (all entries 0).
Does not say: anything about the speaker interpretation. -/
theorem discrete_copy (s : Rat) (f t : Nat) :
    (∀ r, r < Nat.min f t → ∀ c, c < f →
      (matrixWith s .discrete f t)[r]![c]! = if r = c then 1 else 0) ∧
    (∀ r, f ≤ r → r < t → ∀ c, c < f → (matrixWith s .discrete f t)[r]![c]! = 0) := by
  constructor
  · intro r hr c hc
    have hrt : r < t := Nat.lt_of_lt_of_le hr (Nat.min_le_right _ _)
    simp [matrixWith, discreteMatrix, discreteEntry, hrt, hc]
  · intro r hr hrt c hc
    have : r ≠ c := by omega
    simp [matrixWith, discreteMatrix, discreteEntry, hrt, hc, this]

/-! ## Products over `Rat` -/

/-- Sum of `g 0 .. g (n-1)`. -/
def sumTo (g : Nat → Rat) : Nat → Rat
  | 0 => 0
  | n + 1 => sumTo g n + g n

/-- Product of an `a × n` matrix `A` and an `n × p` matrix `B`, entry by entry. -/
def mulMat (A B : Array (Array Rat)) (n p : Nat) : Array (Array Rat) :=
  Array.ofFn (n := A.size) fun i =>
    Array.ofFn (n := p) fun j => sumTo (fun k => A[i]![k]! * B[k]![j]!) n

/-- Matrix-vector product, `A` is `a × n`, `v` has `n` entries. -/
def mulVec (A : Array (Array Rat)) (v : Array Rat) (n : Nat) : Array Rat :=
  Array.ofFn (n := A.size) fun i => sumTo (fun k => A[i]![k]! * v[k]!) n

theorem mulMat_entry (A B : Array (Array Rat)) (n p i j : Nat) (hi : i < A.size) (hj : j < p) :
    (mulMat A B n p)[i]![j]! = sumTo (fun k => A[i]![k]! * B[k]![j]!) n := by
  simp [mulMat, getElem!_def, hi, hj]

theorem sumTo_unit (i j n : Nat) :
    sumTo (fun k => discreteEntry i k * discreteEntry k j) n =
      if i < n ∧ i = j then 1 else 0 := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [sumTo, ih]
    unfold discreteEntry
    by_cases h1 : i = n
    · subst h1
      by_cases h2 : i = j
      · subst h2; simp [Rat.zero_add]
      · simp [h2, Rat.zero_add]
    · have h3 : ¬ (i = n) := h1
      by_cases h4 : i < n
      · have : i < n + 1 := by omega
        simp [h3, h4, this, Rat.add_zero]
      · have : ¬ (i < n + 1) := by omega
        simp [h3, h4, this, Rat.zero_add]

/-- Says: mixing mono up to stereo and back to mono gives the identity matrix `[[1]]`, for every
`s`. Does not say: that stereo to mono to stereo is the identity (it is not). -/
theorem roundtrip_mono_stereo (s : Rat) :
    mulMat (matrixWith s .speakers 2 1) (matrixWith s .speakers 1 2) 2 1 = #[#[1]] := by
  simp [mulMat, matrixWith, speakerRows, sumTo, Array.ofFn_succ, Rat.zero_add]
  show (1 / 2 : Rat) + 1 / 2 = 1
  decide +kernel

/-- Says: mono up to 5.1 and back down to mono gives `[[1]]`, for every `s`: the 5.1-to-mono
formula `s*(L+R) + C + 0.5*(SL+SR)` reads only the center channel that the mono up-mix filled.
Does not say: anything about 5.1 to mono to 5.1. -/
theorem roundtrip_mono_51 (s : Rat) :
    mulMat (matrixWith s .speakers 6 1) (matrixWith s .speakers 1 6) 6 1 = #[#[1]] := by
  simp [mulMat, matrixWith, speakerRows, sumTo, Array.ofFn_succ, Rat.zero_add, Rat.mul_zero]
  show (1 : Rat) + 0 + 0 + 0 = 1
  decide +kernel

/-- Says: with the discrete rule, `f ≤ t`: up-mixing `f` to `t` channels and down-mixing back to
`f` gives the identity on `f` channels (the first `min f t = f` channels are kept).
Does not say: the reverse composition (down then up) is the identity; it zeroes channels
`≥ t`. -/
theorem roundtrip_discrete (s : Rat) (f t : Nat) (h : f ≤ t) (i j : Nat) (hi : i < f) (hj : j < f) :
    (mulMat (matrixWith s .discrete t f) (matrixWith s .discrete f t) t f)[i]![j]! =
      if i = j then 1 else 0 := by
  have hsz : (matrixWith s .discrete t f).size = f := by simp [matrixWith, discreteMatrix]
  have hit : i < t := Nat.lt_of_lt_of_le hi h
  have key : ∀ k, k < t →
      (matrixWith s .discrete t f)[i]![k]! = discreteEntry i k ∧
      (matrixWith s .discrete f t)[k]![j]! = discreteEntry k j := by
    intro k hk
    exact ⟨by simp [matrixWith, discreteMatrix, hi, hk],
           by simp [matrixWith, discreteMatrix, hj, hk]⟩
  have hs : sumTo (fun k => (matrixWith s .discrete t f)[i]![k]! *
        (matrixWith s .discrete f t)[k]![j]!) t =
      sumTo (fun k => discreteEntry i k * discreteEntry k j) t := by
    have : ∀ n, n ≤ t → sumTo (fun k => (matrixWith s .discrete t f)[i]![k]! *
        (matrixWith s .discrete f t)[k]![j]!) n =
        sumTo (fun k => discreteEntry i k * discreteEntry k j) n := by
      intro n
      induction n with
      | zero => intro _; rfl
      | succ n ih =>
        intro hn
        simp only [sumTo]
        rw [ih (by omega), (key n (by omega)).1, (key n (by omega)).2]
    exact this t (Nat.le_refl _)
  rw [mulMat_entry _ _ _ _ _ _ (by omega) hj, hs, sumTo_unit]
  by_cases hij : i = j
  · subst hij; simp [hit]
  · simp [hij]

/-! ## Evaluation on `Float` blocks -/

/-- A rational as a `Float` (numerator and denominator converted, then divided). -/
def ratToFloat (q : Rat) : Float := Float.ofInt q.num / Float.ofNat q.den

/-- Apply a mixing matrix to a block: `block[c][i]` is channel `c`, frame `i`; the result has one
`FloatArray` of `frames` samples per row. Coefficients are converted once. A zero coefficient
skips its channel (so a NaN in a channel that has coefficient 0 does not spread; the spec
defines no value for non-finite samples, section 5.2). Channels of `block` shorter than
`frames` read as 0.0. Loops over the frames, one stack frame in total. -/
def apply (m : Array (Array Rat)) (block : Array FloatArray) (frames : Nat) : Array FloatArray :=
  Id.run do
    let coefs := m.map (·.map ratToFloat)
    let mut out : Array FloatArray := Array.mkEmpty coefs.size
    for row in coefs do
      let mut ch : FloatArray := ⟨Array.replicate frames 0.0⟩
      for c in [0:row.size] do
        let k := row[c]!
        if k != 0.0 then
          let src := block[c]!
          for i in [0:frames] do
            ch := ch.set! i (ch.get! i + k * src.get! i)
      out := out.push ch
    return out

/-- Section 4, the algorithm: each connection is up- or down-mixed to `toCh` channels by the
rule of `interp`, then the results are summed channel by channel. An input with no
connections gives `toCh` channels of silence. -/
def mixInput (interp : Interpretation) (toCh : Nat) (connections : List (Array FloatArray))
    (frames : Nat) : Array FloatArray :=
  Id.run do
    let mut acc : Array FloatArray :=
      Array.replicate toCh ⟨Array.replicate frames 0.0⟩
    for conn in connections do
      let mixed := apply (matrix interp conn.size toCh) conn frames
      for r in [0:toCh] do
        let a := acc[r]!
        let b := mixed[r]!
        let mut s := a
        for i in [0:frames] do
          s := s.set! i (a.get! i + b.get! i)
        acc := acc.set! r s
    return acc

/-! ## Tests -/

private def near (a b : Float) : Bool := Float.abs (a - b) < 1.0e-7

private def toL (a : Array FloatArray) : List (List Float) := a.toList.map (·.data.toList)

private def nearL (a : List (List Float)) (b : List (List Float)) : Bool :=
  a.length == b.length && (a.zip b).all fun (x, y) =>
    x.length == y.length && (x.zip y).all fun (p, q) => near p q

private def blk (xs : List (List Float)) : Array FloatArray :=
  (xs.map fun l => FloatArray.mk l.toArray).toArray

-- computedChannels (WPT `computeNumberOfChannels` cases)
#guard computedChannels .explicit 2 [8, 4] == 2
#guard computedChannels .explicit 6 [] == 6
#guard computedChannels .max 2 [1, 2, 8] == 8
#guard computedChannels .max 2 [] == 1
#guard computedChannels .max 99 [3] == 3
#guard computedChannels .clampedMax 4 [1, 2, 8] == 4
#guard computedChannels .clampedMax 4 [1, 2] == 2
#guard computedChannels .clampedMax 4 [] == 1
-- matrix shapes
#guard (matrix .speakers 1 2).size == 2 && (matrix .speakers 1 2)[0]!.size == 1
#guard (matrix .speakers 6 4).size == 4 && (matrix .speakers 6 4)[0]!.size == 6
#guard (matrix .speakers 3 5).size == 5 && (matrix .speakers 3 5)[0]!.size == 3
-- every speaker pair of the spec (exact rationals)
#guard matrix .speakers 1 2 == #[#[1], #[1]]
#guard matrix .speakers 1 4 == #[#[1], #[1], #[0], #[0]]
#guard matrix .speakers 1 6 == #[#[0], #[0], #[1], #[0], #[0], #[0]]
#guard matrix .speakers 2 4 == #[#[1, 0], #[0, 1], #[0, 0], #[0, 0]]
#guard (matrix .speakers 2 6)[2]! == #[0, 0] && (matrix .speakers 2 6).size == 6
#guard (matrix .speakers 4 6)[4]! == #[0, 0, 1, 0] && (matrix .speakers 4 6)[2]! == #[0, 0, 0, 0]
#guard matrix .speakers 2 1 == #[#[1/2, 1/2]]
#guard matrix .speakers 4 1 == #[#[1/4, 1/4, 1/4, 1/4]]
#guard matrix .speakers 6 1 == #[#[sqrtHalf, sqrtHalf, 1, 0, 1/2, 1/2]]
#guard matrix .speakers 4 2 == #[#[1/2, 0, 1/2, 0], #[0, 1/2, 0, 1/2]]
#guard matrix .speakers 6 2 == #[#[1, 0, sqrtHalf, 0, sqrtHalf, 0], #[0, 1, sqrtHalf, 0, 0, sqrtHalf]]
#guard (matrix .speakers 6 4)[2]! == #[0, 0, 0, 0, 1, 0]
-- same count is the identity; unspecified pairs behave as discrete
#guard matrix .speakers 4 4 == #[#[1,0,0,0], #[0,1,0,0], #[0,0,1,0], #[0,0,0,1]]
#guard matrix .speakers 3 2 == matrix .discrete 3 2
#guard matrix .speakers 2 3 == #[#[1, 0], #[0, 1], #[0, 0]]
-- discrete
#guard matrix .discrete 1 2 == #[#[1], #[0]]
#guard matrix .discrete 2 1 == #[#[1, 0]]
#guard matrix .discrete 6 2 == #[#[1,0,0,0,0,0], #[0,1,0,0,0,0]]
-- sqrt(0.5) against Float
#guard near (ratToFloat sqrtHalf) 0.70710678
#guard (ratToFloat sqrtHalf - 0.7071067811865476).abs < 1.0e-8
-- Float evaluation: exact in binary where the coefficients are
#guard toL (apply (matrix .speakers 1 2) (blk [[0.25, -0.5]]) 2) == [[0.25, -0.5], [0.25, -0.5]]
#guard toL (apply (matrix .speakers 2 1) (blk [[1.0, 2.0], [3.0, 4.0]]) 2) == [[2.0, 3.0]]
#guard toL (apply (matrix .speakers 4 2) (blk [[1.0], [2.0], [3.0], [5.0]]) 1) == [[2.0], [3.5]]
-- Float evaluation of 5.1 down-mixes (within tolerance)
#guard nearL (toL (apply (matrix .speakers 6 1)
    (blk [[1.0], [0.0], [0.0], [0.0], [0.0], [0.0]]) 1)) [[0.70710678]]
#guard nearL (toL (apply (matrix .speakers 6 1)
    (blk [[0.0], [0.0], [1.0], [1.0], [0.0], [2.0]]) 1)) [[2.0]]
#guard nearL (toL (apply (matrix .speakers 6 2)
    (blk [[0.0], [0.0], [1.0], [0.0], [0.0], [0.0]]) 1)) [[0.70710678], [0.70710678]]
#guard nearL (toL (apply (matrix .speakers 6 4)
    (blk [[1.0], [2.0], [1.0], [9.0], [3.0], [4.0]]) 1))
    [[1.70710678], [2.70710678], [3.0], [4.0]]
-- Float evaluation against the Rat matrix, two frames
#guard (let m := matrix .speakers 4 1
        let r := apply m (blk [[1.0, 0.5], [2.0, 0.5], [3.0, 0.5], [4.0, 0.5]]) 2
        toL r == [[2.5, 0.5]])
-- discrete drops and zero-fills
#guard toL (apply (matrix .discrete 3 2) (blk [[1.0], [2.0], [3.0]]) 1) == [[1.0], [2.0]]
#guard toL (apply (matrix .discrete 1 3) (blk [[7.0]]) 1) == [[7.0], [0.0], [0.0]]
-- mixInput: mono and stereo into a stereo input (spec example), summed
#guard toL (mixInput .speakers 2 [blk [[1.0]], blk [[10.0], [20.0]]] 1) == [[11.0], [21.0]]
#guard toL (mixInput .discrete 2 [blk [[1.0]], blk [[10.0], [20.0]]] 1) == [[11.0], [20.0]]
#guard toL (mixInput .speakers 2 [] 2) == [[0.0, 0.0], [0.0, 0.0]]
#guard toL (mixInput .speakers 1 [blk [[1.0], [3.0]], blk [[2.0]]] 1) == [[4.0]]

end L4Factoidal.WebAudio.Mix
