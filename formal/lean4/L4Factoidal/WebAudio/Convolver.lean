import L4Factoidal.WebAudio.Kernels
import L4Factoidal.WebAudio.FFT

/-!
# ConvolverNode kernel

`ConvolverNode` of the W3C Web Audio API (https://webaudio.github.io/web-audio-api/, section
"The ConvolverNode Interface"). Stage F of https://github.com/danbri/factoidal-core/issues/1169.

The node convolves its input with an impulse response (a buffer of 1, 2 or 4 channels at the
context's sample rate), with zero latency: output frame `t` is `sum_k h[k] x[t - k]`, `x` being the
input across blocks.

## Channel configuration

Read from the Web Platform Tests `convolver-response-{1,2,4}-chan.html` and
`convolver-upmixing-1-channel-response.html`. The input has 1 or 2 channels (the node's
`channelCount` is at most 2, mode "clamped-max"; the graph mixes to that count). Input
`x = (L, R)` (a mono input is `L`); impulse response channels `h0 .. h3`:

* 1-channel response: mono input gives mono output `L * h0`; stereo input gives `(L * h0, R * h0)`.
* 2-channel response: mono input gives `(L * h0, L * h1)`; stereo input gives `(L * h0, R * h1)`.
* 4-channel response ("true stereo"): output `(L * h0 + R * h2, L * h1 + R * h3)`; a mono input is
  first up-mixed to `L = R`, so it gives `(L * (h0 + h2), L * (h1 + h3))`.

The output is mono only for a mono input and a mono response; every other case has 2 channels.
With no buffer the output is one channel of silence and nothing is remembered.

## Two ways to compute the same output

* `directOutput`: the sum above, `O(n * L)` for a block of `n` frames and a response of `L`
  frames. This is the definition. `convolveDirect` states it for a whole signal.
* `fastOutput`: uniformly partitioned overlap-save convolution with FFT (`WebAudio.FFT`). The
  response is cut into `N = ceil (L / P)` partitions of `P` frames (`P = 2^pbits`, default 128, the
  render quantum); the spectrum (size `2 P`) of each partition is computed once in `ofBufferWith`.
  Each block of `P` input frames is transformed together with the `P` frames before it, kept in a
  frequency-domain delay line of the last `N` spectra; the output is the last `P` frames of the
  inverse transform of the sum over partitions of the products. Cost per block: 1 or 2 forward
  FFTs, one inverse FFT per output channel and `N * 2 P` complex multiply-adds per route.

`process` uses the fast path when the block has exactly `P` frames and the response is longer than
`2 n`, otherwise the direct form. Both paths keep the same state, so the choice can differ from
block to block (see "State").

## State

The input history is a ring of `R = N * P >= L` frames for each of 2 input channels (a mono input is
written into both, which is the "speakers" up-mix of the history). The direct path reads the last
`L - 1` frames of the ring. The fast path also keeps the frequency-domain delay line `fdl`; the
direct path does not update it, so it marks it stale (`fdlValid = false`) and the fast path rebuilds
it from the ring (one FFT per partition and channel) when it is next used.

When the input channel count changes: from 1 to 2 nothing is needed (both history channels already
hold the mono signal, so the tail continues in both output channels); from 2 to 1 the two history
channels are replaced by their mean (the "speakers" down-mix of the tail), which is the history of
the mono signal that the down-mixed output tail would have. An input with more than 2 channels
uses its first 2.

## Proved

* `process_shape`: the number of output channels is `outputChannels` of the input and response
  channel counts, `n` frames in each.
* `ofBuffer_three_channels`, `ofBuffer_rate_mismatch`: a 3-channel buffer and a buffer whose
  sample rate differs from the context's are refused.
* `processWith_ring`: the ring buffers keep their size across `processWith`.
* Sizes of the helper loops.

## Tested with `#guard`

Every statement about a `Float` value: the normalization scale, the identity and delay responses
across block boundaries, the channel routing of 1-, 2- and 4-channel responses, the triangle of
`convolution-mono-mono.html`, channel-count changes, and fast path against direct form over
several blocks (including a switch between the paths).

## Not done

* `buffer` replaced while running (the page layer builds a new state; the history is empty again,
  as when a new reverb is created).
* The input channel count is not mixed here (the graph does that); `channelCountMode` and
  `channelInterpretation` are the caller's.
* The `normalize` setting is applied when the buffer is set (`ofBuffer`), as the specification says.
* The sample values of the impulse response are used in binary64, not rounded to binary32.
* A response longer than about 2^20 frames makes `ofBuffer` slow (it transforms every partition).
-/

namespace L4Factoidal.WebAudio.Convolver

open L4Factoidal.WebAudio.Kernels (iter getF mkChan zeroF Block IsBlock mkChan_size size_set!)

instance instInhabitedPlanConvolver : Inhabited FFT.Plan := ⟨FFT.Plan.make 0⟩

/-! ## Normalization -/

/-- `calculateNormalizationScale` of the specification: the scale applied to the response so
that responses of different loudness give similar output levels.
`power = sqrt (sum of squares / (channels * length))`, at least `MinPower = 0.000125` (also when
not finite); `scale = GainCalibration / power` with `GainCalibration = 0.00125`; multiplied by
`44100 / sampleRate` (when the rate is not 0) and by `0.5` for 4 channels. -/
def normalizationScale (channels : Array FloatArray) (sampleRate : Float) : Float :=
  let nch := channels.size
  let len := channels.foldl (fun m c => min m c.size) (channels.getD 0 ⟨#[]⟩).size
  let sumSq := channels.foldl (fun acc c =>
    iter (fun i (a : Float) => let v := getF c i; a + v * v) len 0 acc) 0.0
  let power := Float.sqrt (sumSq / (nch * len).toFloat)
  let power := if power.isFinite && power ≥ 0.000125 then power else 0.000125
  let scale := (1.0 / power) * 0.00125
  let scale := if sampleRate != 0.0 then scale * (44100.0 / sampleRate) else scale
  if nch == 4 then scale * 0.5 else scale

/-! ## Channel configuration -/

/-- The input channel count the kernel uses: 1 for an empty block, at most 2. -/
def inChOf (blockChannels : Nat) : Nat := min 2 (max 1 blockChannels)

/-- Output channels: 1 with no buffer (`irChannels = 0`) or for a mono input and a mono response,
else 2. An input channel count of 0 or 1 is mono. -/
def outputChannels (inputChannels irChannels : Nat) : Nat :=
  if irChannels = 0 then 1
  else if irChannels = 1 && inputChannels ≤ 1 then 1
  else 2

/-- For each output channel, the list of (input channel, response channel) pairs whose
convolutions are summed. -/
def routes (ic irc : Nat) : Array (Array (Nat × Nat)) :=
  if irc = 0 then #[#[]]
  else if irc = 1 then
    (if ic ≤ 1 then #[#[(0, 0)]] else #[#[(0, 0)], #[(1, 0)]])
  else if irc = 2 then
    (if ic ≤ 1 then #[#[(0, 0)], #[(0, 1)]] else #[#[(0, 0)], #[(1, 1)]])
  else
    (if ic ≤ 1 then #[#[(0, 0), (0, 2)], #[(0, 1), (0, 3)]]
     else #[#[(0, 0), (1, 2)], #[(0, 1), (1, 3)]])

/-- Says: `routes` has one entry for each output channel. Does not say: which pairs. -/
theorem routes_size (ic irc : Nat) : (routes ic irc).size = outputChannels ic irc := by
  unfold routes outputChannels
  by_cases h0 : irc = 0
  · simp [h0]
  · by_cases h1 : irc = 1
    · subst h1; by_cases hi : ic ≤ 1 <;> simp [hi]
    · by_cases h2 : irc = 2
      · subst h2; by_cases hi : ic ≤ 1 <;> simp [hi]
      · simp only [h0, h1, h2, if_false]
        by_cases hi : ic ≤ 1 <;> simp [hi]

/-! ## Array helpers -/

/-- `m` zeros. -/
def zeros (m : Nat) : FloatArray := mkChan m (fun _ => zeroF)

theorem zeros_size (m : Nat) : (zeros m).size = m := mkChan_size m _

/-- `src` copied into `dst` from index `off`. -/
def blit (dst : FloatArray) (off : Nat) (src : FloatArray) : FloatArray :=
  iter (fun i (d : FloatArray) => d.set! (off + i) (getF src i)) src.size 0 dst

/-- Says: `blit` keeps the size of the destination. Does not say: which values are copied. -/
theorem blit_size (dst : FloatArray) (off : Nat) (src : FloatArray) :
    (blit dst off src).size = dst.size := by
  unfold blit
  refine FFT.iter_inv (fun d : FloatArray => d.size = dst.size) _ ?_ _ _ _ rfl
  intro i d hd
  simp only [size_set!]; exact hd

/-- `x` written into the ring `r` at the write index `w`, `n` frames, wrapping. -/
def writeRing (r : FloatArray) (w n : Nat) (x : FloatArray) : FloatArray :=
  iter (fun t (a : FloatArray) => a.set! ((w + t) % r.size) (getF x t)) n 0 r

/-- Says: `writeRing` keeps the size of the ring. Does not say: which values are written. -/
theorem writeRing_size (r : FloatArray) (w n : Nat) (x : FloatArray) :
    (writeRing r w n x).size = r.size := by
  unfold writeRing
  refine FFT.iter_inv (fun d : FloatArray => d.size = r.size) _ ?_ _ _ _ rfl
  intro i d hd
  simp only [size_set!]; exact hd

/-! ## State -/

/-- Convolver state. -/
structure State where
  /-- The impulse response channels times the scale (empty: no buffer). -/
  ir : Array FloatArray
  /-- Frames of the response (0: no buffer). -/
  len : Nat
  /-- The partition size is `2 ^ pbits`. -/
  pbits : Nat
  /-- Number of partitions `ceil (len / P)` (at least 1 with a buffer). -/
  nparts : Nat
  /-- The plan of the transforms of `2 P` values. -/
  plan : FFT.Plan
  /-- Spectrum of every partition of each response channel: `nparts * 2 P` values per channel
  (real parts); partition `j` at offset `j * 2 P`. -/
  irRe : Array FloatArray
  /-- Imaginary parts of `irRe`. -/
  irIm : Array FloatArray
  /-- The input history of 2 channels, each a ring of `nparts * P` frames. -/
  ring : Array FloatArray
  /-- The write index of the rings. -/
  w : Nat
  /-- Channel count of the last block (0 before the first). -/
  inCh : Nat
  /-- The frequency-domain delay line of each input channel (real parts), `nparts` slots of
  `2 P` values. -/
  fdlRe : Array FloatArray
  /-- Imaginary parts of `fdlRe`. -/
  fdlIm : Array FloatArray
  /-- The slot of the newest spectrum. -/
  head : Nat
  /-- Whether the delay line matches the ring (the direct path does not keep it). -/
  fdlValid : Bool
  deriving Inhabited

/-- The state of a node with no buffer. -/
def State.empty : State where
  ir := #[]
  len := 0
  pbits := 7
  nparts := 0
  plan := FFT.Plan.make 0
  irRe := #[]
  irIm := #[]
  ring := #[]
  w := 0
  inCh := 0
  fdlRe := #[]
  fdlIm := #[]
  head := 0
  fdlValid := true

/-- The partition size `P`. -/
def State.part (s : State) : Nat := 1 <<< s.pbits

/-- The channel count of the response, 0 with no buffer. -/
def State.irChannels (s : State) : Nat := if s.len = 0 then 0 else s.ir.size

/-- The spectra of the partitions of `h`: `N` partitions of `P = 2^pbits` frames, each zero-padded
to `2 P` and transformed. -/
def irSpectra (plan : FFT.Plan) (pbits N : Nat) (h : FloatArray) : FloatArray × FloatArray :=
  let P := 1 <<< pbits
  let P2 := 2 * P
  iter (fun j (a : FloatArray × FloatArray) =>
      let win := mkChan P2 (fun i => if i < P then getF h (j * P + i) else zeroF)
      let sp := FFT.forward plan win (zeros P2)
      (blit a.1 (j * P2) sp.1, blit a.2 (j * P2) sp.2))
    N 0 (zeros (N * P2), zeros (N * P2))

/-- The state for a buffer, with partition size `2 ^ pbits` (at least 2). The scale is computed
here (`normalize`) or 1. 0 channels (or 0 frames) is the null buffer. Channel counts other than
1, 2, 4 and `bufferRate != contextRate` give `NotSupportedError`. -/
def State.ofBufferWith (pbits : Nat) (channels : Array FloatArray) (bufferRate contextRate : Float)
    (normalize : Bool) : Except String State :=
  if channels.size = 0 then .ok State.empty
  else if !(channels.size = 1 || channels.size = 2 || channels.size = 4) then
    .error "NotSupportedError: the buffer of a ConvolverNode has 1, 2 or 4 channels"
  else if bufferRate != contextRate then
    .error "NotSupportedError: the sample rate of the buffer is not the sample rate of the context"
  else
    let len := channels.foldl (fun m c => min m c.size) (channels.getD 0 ⟨#[]⟩).size
    if len = 0 then .ok State.empty
    else
      let pb := max 2 pbits
      let P := 1 <<< pb
      let N := (len + P - 1) / P
      let scale := if normalize then normalizationScale channels contextRate else 1.0
      let ir := channels.map (fun c => mkChan len (fun i => getF c i * scale))
      let plan := FFT.Plan.make (pb + 1)
      let spec := ir.map (irSpectra plan pb N)
      .ok { ir, len, pbits := pb, nparts := N, plan
            irRe := spec.map Prod.fst, irIm := spec.map Prod.snd
            ring := Array.replicate 2 (zeros (N * P)), w := 0, inCh := 0
            fdlRe := Array.replicate 2 (zeros (N * 2 * P))
            fdlIm := Array.replicate 2 (zeros (N * 2 * P))
            head := 0, fdlValid := true }

/-- `ofBufferWith` with the partition size 128, the render quantum. -/
def State.ofBuffer (channels : Array FloatArray) (bufferRate contextRate : Float)
    (normalize : Bool) : Except String State :=
  State.ofBufferWith 7 channels bufferRate contextRate normalize

/-- Says: every ring of the state has `R` frames and there are 2 of them. Does not say: anything
about the values. -/
def State.RingSize (s : State) (R : Nat) : Prop :=
  s.ring.size = 2 ∧ ∀ c ∈ s.ring, c.size = R

/-! ## The definition: direct convolution -/

/-- The convolution of the signal `x` with `h` at zero latency, `x.size` frames:
`y[t] = sum_{k <= t, k < h.size} h[k] x[t - k]`. The reference of the guards. -/
def convolveDirect (h x : FloatArray) : FloatArray :=
  mkChan x.size (fun t =>
    iter (fun k (a : Float) => if k ≤ t then a + getF h k * getF x (t - k) else a) h.size 0 zeroF)

/-- `sum_{k <= E} h[k] ext[E + t - k]`: output frame `t` of a block, `ext` being the last `E`
frames before the block followed by the block. -/
def dotAt (ext h : FloatArray) (E t : Nat) : Float :=
  iter (fun k (a : Float) => a + getF h k * getF ext (E + t - k)) (E + 1) 0 zeroF

/-- Output of the group of `pairs` for the block, by the direct sum. -/
def directOutput (s : State) (n : Nat) (x0 x1 : FloatArray) (ic : Nat)
    (pairs : Array (Nat × Nat)) : FloatArray :=
  let E := s.len - 1
  let ext := fun (c : Nat) (x : FloatArray) =>
    mkChan (E + n) (fun i =>
      if i < E then
        (let r := s.ring.getD c ⟨#[]⟩
         getF r ((s.w + r.size - (E - i)) % r.size))
      else getF x (i - E))
  let e0 := ext 0 x0
  let e1 := if ic = 2 then ext 1 x1 else e0
  let exts : Array FloatArray := #[e0, e1]
  mkChan n (fun t => pairs.foldl (fun acc ck =>
    acc + dotAt (exts.getD ck.1 ⟨#[]⟩) (s.ir.getD ck.2 ⟨#[]⟩) E t) zeroF)

/-! ## The fast path: uniformly partitioned overlap-save -/

/-- The spectra of the lags 1 to `nparts - 1` rebuilt from the ring (the lag 0 is the block that
comes next); the head is set so that the next head is slot 0. -/
def rebuild (s : State) : State :=
  let P := s.part
  let P2 := 2 * P
  let N := s.nparts
  let fill := fun (c : Nat) (a : FloatArray × FloatArray) (m : Nat) =>
    let r := s.ring.getD c ⟨#[]⟩
    let win := mkChan P2 (fun i => getF r ((s.w + r.size - ((m + 1) * P - i)) % r.size))
    let sp := FFT.forward s.plan win (zeros P2)
    let slot := (N - m) % N
    (blit a.1 (slot * P2) sp.1, blit a.2 (slot * P2) sp.2)
  let f := fun (c : Nat) =>
    iter (fun m a => fill c a m) (N - 1) 1 (zeros (N * P2), zeros (N * P2))
  let f0 := f 0
  let f1 := f 1
  { s with fdlRe := #[f0.1, f1.1], fdlIm := #[f0.2, f1.2], head := N - 1, fdlValid := true }

/-- The spectrum of the block (with the `P` frames before it) stored in slot `head'`. A mono
input stores its spectrum in both channels. -/
def fastStore (s : State) (head' : Nat) (x0 x1 : FloatArray) (ic : Nat) : State :=
  let P := s.part
  let P2 := 2 * P
  let win := fun (c : Nat) (x : FloatArray) =>
    mkChan P2 (fun i =>
      if i < P then
        (let r := s.ring.getD c ⟨#[]⟩
         getF r ((s.w + r.size - (P - i)) % r.size))
      else getF x (i - P))
  let sp0 := FFT.forward s.plan (win 0 x0) (zeros P2)
  let sp1 := if ic = 2 then FFT.forward s.plan (win 1 x1) (zeros P2) else sp0
  { s with
    fdlRe := #[blit (s.fdlRe.getD 0 ⟨#[]⟩) (head' * P2) sp0.1,
               blit (s.fdlRe.getD 1 ⟨#[]⟩) (head' * P2) sp1.1]
    fdlIm := #[blit (s.fdlIm.getD 0 ⟨#[]⟩) (head' * P2) sp0.2,
               blit (s.fdlIm.getD 1 ⟨#[]⟩) (head' * P2) sp1.2]
    head := head', fdlValid := true }

/-- `a += H * X` over `len` values: `H` from offset `ho` of `(hr, hi)`, `X` from `xo` of
`(xr, xi)`, complex products. -/
def macSlot (hr hi : FloatArray) (ho : Nat) (xr xi : FloatArray) (xo len : Nat)
    (a : FloatArray × FloatArray) : FloatArray × FloatArray :=
  iter (fun k (a : FloatArray × FloatArray) =>
    let p := getF hr (ho + k)
    let q := getF hi (ho + k)
    let u := getF xr (xo + k)
    let v := getF xi (xo + k)
    (a.1.set! k (getF a.1 k + p * u - q * v), a.2.set! k (getF a.2 k + p * v + q * u))) len 0 a

/-- The sum over the pairs and partitions of the products of the spectra of the response
partitions and of the delay line (slot `head - j` for partition `j`). -/
def accumulate (s : State) (pairs : Array (Nat × Nat)) : FloatArray × FloatArray :=
  let P2 := 2 * s.part
  let N := s.nparts
  pairs.foldl (fun (acc : FloatArray × FloatArray) (ck : Nat × Nat) =>
    iter (fun j (a : FloatArray × FloatArray) =>
      macSlot (s.irRe.getD ck.2 ⟨#[]⟩) (s.irIm.getD ck.2 ⟨#[]⟩) (j * P2)
        (s.fdlRe.getD ck.1 ⟨#[]⟩) (s.fdlIm.getD ck.1 ⟨#[]⟩) (((s.head + N - j) % N) * P2) P2 a)
      N 0 acc) (zeros P2, zeros P2)

/-- Output of the group of `pairs`, the last `P` frames of the inverse transform divided by `2 P`
(the inverse transform of `FFT` is not divided). The delay line must already hold this block. -/
def fastOutput (s : State) (pairs : Array (Nat × Nat)) : FloatArray :=
  let P := s.part
  let y := accumulate s pairs
  let t := FFT.inverse s.plan y.1 y.2
  let inv := 1.0 / (2 * P).toFloat
  mkChan P (fun i => getF t.1 (P + i) * inv)

/-! ## The node -/

/-- Input channels 2 to 1: the history of the two channels replaced by their mean. -/
def retarget (s : State) (ic : Nat) : State :=
  if s.inCh = 2 && ic = 1 then
    let r0 := s.ring.getD 0 ⟨#[]⟩
    let r1 := s.ring.getD 1 ⟨#[]⟩
    let m := mkChan r0.size (fun i => 0.5 * (getF r0 i + getF r1 i))
    { s with ring := #[m, m], fdlValid := false }
  else s

/-- The block written into the rings (a mono block into both), the write index advanced. -/
def commit (s : State) (n : Nat) (x0 x1 : FloatArray) (ic : Nat) : State :=
  let r0 := s.ring.getD 0 ⟨#[]⟩
  let r1 := s.ring.getD 1 ⟨#[]⟩
  { s with ring := #[writeRing r0 s.w n x0, writeRing r1 s.w n x1],
           w := (s.w + n) % r0.size, inCh := ic }

/-- The output blocks: for each route group, `f pairs` (at least `n` values) as `n` frames. -/
def render (n ic irc : Nat) (f : Array (Nat × Nat) → FloatArray) : Array FloatArray :=
  (routes ic irc).map (fun pairs => let y := f pairs; mkChan n (fun t => getF y t))

/-- `process` with the path chosen by `force`: `none` automatic (fast when the block has `P`
frames and the response is longer than `2 n`), `some true` fast whenever the block has `P` frames,
`some false` direct. -/
def processWith (force : Option Bool) (n : Nat) (s : State) (inputs : Array Block)
    (_params : Array FloatArray) : State × Array Block :=
  if s.len = 0 then (s, #[#[mkChan n (fun _ => zeroF)]])
  else
    let blk := inputs.getD 0 #[]
    let ic := inChOf blk.size
    let x0 := Kernels.chanOr n blk 0
    let x1 := if ic = 2 then Kernels.chanOr n blk 1 else x0
    let s1 := retarget s ic
    let irc := s1.irChannels
    let useFast := n == s1.part &&
      (match force with | some b => b | none => decide (s1.len > 2 * n))
    if useFast then
      let s2 := if s1.fdlValid then s1 else rebuild s1
      let head' := (s2.head + 1) % s2.nparts
      let s3 := fastStore s2 head' x0 x1 ic
      (commit s3 n x0 x1 ic, #[render n ic irc (fastOutput s3)])
    else
      (commit { s1 with fdlValid := false } n x0 x1 ic,
       #[render n ic irc (directOutput s1 n x0 x1 ic)])

/-- One block through the node. `inputs[0]` has 1 or 2 channels (an empty block is one channel of
silence); `params` is not used (the node has no `AudioParam`). With no buffer: one channel of
silence and the state unchanged. -/
def process (n : Nat) (s : State) (inputs : Array Block) (params : Array FloatArray) :
    State × Array Block :=
  processWith none n s inputs params

end L4Factoidal.WebAudio.Convolver
