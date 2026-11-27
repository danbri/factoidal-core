import L4Factoidal.WebAudio.Kernels

/-!
# A radix-2 FFT for the Web Audio nodes

The discrete Fourier transform of `n = 2^bits` complex values, for the nodes of stage F of
https://github.com/danbri/factoidal-core/issues/1169 (plan:
`docs/designissues/2026-11-26-foafnaut-audio-plan.md`, section 6): the `AnalyserNode`'s frequency
data (Web Audio API, "FFT Windowing and Smoothing over Time": the DFT of the windowed block) and
the `ConvolverNode`'s convolution by blocks.

* `Plan.make bits`: the cosine and sine of `2 pi k / n` for `k < n / 2`, computed once, and the
  bit-reversal permutation. A node keeps its plan in its state.
* `forward p re im`: `X[k] = sum_j x[j] e^(-2 pi i j k / n)`; `inverse p re im`:
  `x[j] = sum_k X[k] e^(2 pi i j k / n)`, not divided by `n` (the caller divides).
* Decimation in time: the input in bit-reversed order, then `bits` stages of `n / 2` butterflies.

Every loop is `Kernels.iter`, a structural tail call: no stack frame per value.

## Proved

The results have the sizes of the inputs (`permute_size`, `stage_size`, `run_size`), for inputs of
`n` values. Statements about values are about `Float`, which the kernel does not unfold: they are
`#guard`s against the DFT sum (`dft`), at sizes 1 to 64.

## Not done

A real-input transform of half size (the analyser and the convolver transform real signals with
the imaginary part 0; a half-size transform would halve the work).
-/

namespace L4Factoidal.WebAudio.FFT

open L4Factoidal.WebAudio.Kernels (iter getF mkChan size_set! mkChan_size)

/-- `pi` as a binary64 number (a named constant: see `Kernels.zeroF`). -/
@[noinline] def piF : Float := 3.141592653589793

/-- The bits of `x` below bit `bits`, in reverse order. -/
def bitrev (x bits : Nat) : Nat :=
  (iter (fun _ (rv : Nat × Nat) => ((rv.1 <<< 1) ||| (rv.2 &&& 1), rv.2 >>> 1)) bits 0 (0, x)).1

/-- The tables of a transform of `2^bits` values. -/
structure Plan where
  bits : Nat
  /-- `cos (2 pi k / n)` for `k < n / 2`. -/
  cosT : FloatArray
  /-- `sin (2 pi k / n)` for `k < n / 2`. -/
  sinT : FloatArray
  /-- `rev[i]` is `bitrev i bits`. -/
  rev : Array Nat

/-- `n = 2^bits`, the number of values of the transform. -/
def Plan.size (p : Plan) : Nat := 1 <<< p.bits

def Plan.make (bits : Nat) : Plan :=
  let n := 1 <<< bits
  let nf := n.toFloat
  { bits
    cosT := mkChan (n / 2) fun k => Float.cos (2.0 * piF * k.toFloat / nf)
    sinT := mkChan (n / 2) fun k => Float.sin (2.0 * piF * k.toFloat / nf)
    rev := Array.ofFn (n := n) fun i => bitrev i.1 bits }

/-- The smallest `bits` with `2^bits ≥ m` (0 for `m ≤ 1`). -/
def bitsFor (m : Nat) : Nat := if m ≤ 1 then 0 else Nat.log2 (m - 1) + 1

/-- Values `i` and `j` of `a` exchanged. -/
def swap (a : FloatArray) (i j : Nat) : FloatArray :=
  let x := getF a i
  (a.set! i (getF a j)).set! j x

theorem swap_size (a : FloatArray) (i j : Nat) : (swap a i j).size = a.size := by
  simp [swap, size_set!]

/-- The values in bit-reversed order: value `i` exchanged with value `rev[i]` when `i < rev[i]`. -/
def permute (p : Plan) (re im : FloatArray) : FloatArray × FloatArray :=
  iter (fun i (a : FloatArray × FloatArray) =>
    let j := p.rev.getD i 0
    if i < j then (swap a.1 i j, swap a.2 i j) else a) p.size 0 (re, im)

/-- One stage of butterflies on blocks of `2 * half` values: for each block and each `k < half`,
`(u, v) ↦ (u + w v, u - w v)` with `w = e^(sign 2 pi i k / (2 half))`, `w` read from the table at
`k * n / (2 half)`. -/
def stage (p : Plan) (sign : Float) (half : Nat) (a : FloatArray × FloatArray) :
    FloatArray × FloatArray :=
  let len := 2 * half
  let stride := p.size / len
  iter (fun t (a : FloatArray × FloatArray) =>
    let k := t % half
    let i := (t / half) * len + k
    let j := i + half
    let wr := getF p.cosT (k * stride)
    let wi := sign * getF p.sinT (k * stride)
    let re := a.1
    let im := a.2
    let xr := getF re j * wr - getF im j * wi
    let xi := getF re j * wi + getF im j * wr
    let ur := getF re i
    let ui := getF im i
    ((re.set! j (ur - xr)).set! i (ur + xr), (im.set! j (ui - xi)).set! i (ui + xi)))
    (p.size / 2) 0 a

/-- The transform with `w = e^(sign 2 pi i / n)`: `sign = -1` forward, `1` inverse (not divided). -/
def run (p : Plan) (re im : FloatArray) (sign : Float) : FloatArray × FloatArray :=
  iter (fun s a => stage p sign (1 <<< s) a) p.bits 0 (permute p re im)

/-- `X[k] = sum_j x[j] e^(-2 pi i j k / n)`. `re` and `im` hold `n` values. -/
def forward (p : Plan) (re im : FloatArray) : FloatArray × FloatArray := run p re im (-1.0)

/-- `x[j] = sum_k X[k] e^(2 pi i j k / n)`, not divided by `n`. -/
def inverse (p : Plan) (re im : FloatArray) : FloatArray × FloatArray := run p re im 1.0

/-! ## Sizes -/

/-- A property that each step keeps holds after any number of steps. -/
theorem iter_inv {σ : Type} (P : σ → Prop) (step : Nat → σ → σ)
    (h : ∀ i s, P s → P (step i s)) : ∀ k i s, P s → P (iter step k i s) := by
  intro k
  induction k with
  | zero => intro i s hs; simpa [iter] using hs
  | succ k ih => intro i s hs; simp only [iter]; exact ih _ _ (h _ _ hs)

/-- Says: `permute` keeps the sizes. Does not say: which values go where. -/
theorem permute_size (p : Plan) (re im : FloatArray) :
    (permute p re im).1.size = re.size ∧ (permute p re im).2.size = im.size := by
  unfold permute
  refine iter_inv (fun a : FloatArray × FloatArray => a.1.size = re.size ∧ a.2.size = im.size) _ ?_
    _ _ _ ⟨rfl, rfl⟩
  intro i a ha
  dsimp only
  split
  · exact ⟨by rw [swap_size]; exact ha.1, by rw [swap_size]; exact ha.2⟩
  · exact ha

/-- Says: a stage keeps the sizes. Does not say: what the values are. -/
theorem stage_size (p : Plan) (sign : Float) (half : Nat) (a : FloatArray × FloatArray) :
    (stage p sign half a).1.size = a.1.size ∧ (stage p sign half a).2.size = a.2.size := by
  unfold stage
  refine iter_inv (fun b : FloatArray × FloatArray => b.1.size = a.1.size ∧ b.2.size = a.2.size) _ ?_
    _ _ _ ⟨rfl, rfl⟩
  intro t b hb
  dsimp only
  exact ⟨by simp only [size_set!]; exact hb.1, by simp only [size_set!]; exact hb.2⟩

/-- Says: the transform's results have the sizes of its inputs. Does not say: that they are the
DFT (see the `#guard`s) or that the sizes are `p.size` (the caller gives `n` values). -/
theorem run_size (p : Plan) (re im : FloatArray) (sign : Float) :
    (run p re im sign).1.size = re.size ∧ (run p re im sign).2.size = im.size := by
  unfold run
  refine iter_inv (fun b : FloatArray × FloatArray => b.1.size = re.size ∧ b.2.size = im.size) _ ?_
    _ _ _ (permute_size p re im)
  intro s b hb
  have := stage_size p sign (1 <<< s) b
  exact ⟨this.1.trans hb.1, this.2.trans hb.2⟩

/-! ## Tests: against the DFT sum -/

/-- The DFT by its definition, `O(n^2)`: the reference of the `#guard`s. -/
def dft (re im : FloatArray) (sign : Float) : FloatArray × FloatArray :=
  let n := re.size
  let at_ (k : Nat) : Float × Float :=
    iter (fun j (acc : Float × Float) =>
      let ang := sign * 2.0 * piF * (j * k % n).toFloat / n.toFloat
      let c := Float.cos ang
      let s := Float.sin ang
      (acc.1 + getF re j * c - getF im j * s, acc.2 + getF re j * s + getF im j * c)) n 0 (0.0, 0.0)
  (mkChan n fun k => (at_ k).1, mkChan n fun k => (at_ k).2)

private def maxDiff (a b : FloatArray) : Float :=
  iter (fun i m => let d := (getF a i - getF b i).abs; if d > m then d else m) (max a.size b.size) 0 0.0

private def sig (n : Nat) (f : Nat → Float) : FloatArray := mkChan n f

/-- The forward transform of a test signal against the DFT, largest difference of the two parts. -/
private def errFwd (bits : Nat) : Float :=
  let p := Plan.make bits
  let n := p.size
  let re := sig n fun j => Float.sin (0.3 * j.toFloat) + 0.25 * (j % 3).toFloat
  let im := sig n fun j => Float.cos (0.7 * j.toFloat) - 0.5
  let (fr, fi) := forward p re im
  let (dr, di) := dft re im (-1.0)
  max (maxDiff fr dr) (maxDiff fi di)

/-- The inverse of the forward transform, divided by `n`, against the signal. -/
private def errRound (bits : Nat) : Float :=
  let p := Plan.make bits
  let n := p.size
  let re := sig n fun j => Float.sin (0.11 * j.toFloat * j.toFloat)
  let im := sig n fun _ => 0.0
  let (fr, fi) := forward p re im
  let (br, bi) := inverse p fr fi
  let nf := n.toFloat
  max (maxDiff (sig n fun j => getF br j / nf) re) (maxDiff (sig n fun j => getF bi j / nf) im)

#guard [0, 1, 2, 3, 4, 5, 6].all fun b => errFwd b < 1e-12
#guard [0, 1, 3, 6, 10].all fun b => errRound b < 1e-12
-- bit reversal and sizes
#guard bitrev 1 3 == 4 && bitrev 6 3 == 3 && bitrev 0 4 == 0
#guard bitsFor 1 == 0 && bitsFor 2 == 1 && bitsFor 3 == 2 && bitsFor 1024 == 10 && bitsFor 1025 == 11
#guard (Plan.make 5).size == 32 && (Plan.make 5).cosT.size == 16
-- a pure tone at bin 3 of 16: all its energy in bins 3 and 13
#guard (let p := Plan.make 4
  let (fr, fi) := forward p (sig 16 fun j => Float.cos (2.0 * piF * 3.0 * j.toFloat / 16.0)) (sig 16 fun _ => 0.0)
  (getF fr 3 - 8.0).abs < 1e-12 && (getF fr 13 - 8.0).abs < 1e-12 &&
  (List.range 16).all fun k => k == 3 || k == 13 || ((getF fr k).abs < 1e-12 && (getF fi k).abs < 1e-12))

end L4Factoidal.WebAudio.FFT
