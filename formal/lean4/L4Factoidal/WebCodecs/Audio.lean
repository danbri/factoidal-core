/-
L4Factoidal.WebCodecs.Audio: `AudioData` (WebCodecs §9.2) and the PCM decoders of the codec
registry (WebCodecs PCM, μ-law and A-law codec registrations). Record:
docs/designissues/2026-11-14-webgl-webcodecs.md, section 4.

  * `initCheck`: "valid AudioDataInit" (§9.2.2): frames, channels and a sample rate above zero,
    and enough bytes for them; the duration in microseconds, exactly (`durationOf`, on the
    double's mantissa and exponent).
  * `plan`: "Compute Copy Element Count" (§9.2.5) for `allocationSize` and `copyTo`: the
    RangeErrors of a plane index, frame offset or frame count, and the elements copied.
  * `copy`: the elements as samples of the destination format. Every source byte read is inside
    the data (`srcIndex_lt`). Integer formats are converted by shifting (`widen` and `narrow`:
    narrowing what was widened gives the sample back, `narrow_widen`); to and from `f32` by the
    scale 2^(bits-1), rounded to nearest and clamped; `f32` to `f32` copies the bits.
  * `pcmDecode`: the bytes of a PCM chunk as the samples of an `AudioData`: `u8`, `s16`, `s32` and
    `f32` as they are, `s24` widened to `s32`, μ-law and A-law (ITU-T G.711) expanded to `s16`
    (`ulaw_range`, `alaw_range`, `ulaw_odd`, `alaw_odd`, all 256 codes checked by `decide`).
-/
import L4Factoidal.WebCodecs.Codec
import L4Factoidal.WebCodecs.Frame

namespace L4Factoidal.WebCodecs.Audio

/-! ## Sample formats -/

inductive Sample where
  | u8 | s16 | s32 | f32
  deriving DecidableEq, Repr, Inhabited

def Sample.bytes : Sample → Nat
  | .u8 => 1 | .s16 => 2 | .s32 => 4 | .f32 => 4

/-- Bits of an integer sample. -/
def Sample.bits : Sample → Nat
  | .u8 => 8 | .s16 => 16 | .s32 => 32 | .f32 => 32

theorem Sample.bytes_pos (s : Sample) : 0 < s.bytes := by cases s <;> decide

structure Format where
  sample : Sample
  planar : Bool
  deriving DecidableEq, Repr, Inhabited

def Format.name (f : Format) : String :=
  (match f.sample with | .u8 => "u8" | .s16 => "s16" | .s32 => "s32" | .f32 => "f32") ++
  (if f.planar then "-planar" else "")

def Format.all : List Format :=
  [⟨.u8, false⟩, ⟨.s16, false⟩, ⟨.s32, false⟩, ⟨.f32, false⟩,
   ⟨.u8, true⟩, ⟨.s16, true⟩, ⟨.s32, true⟩, ⟨.f32, true⟩]

def Format.ofName? (s : String) : Option Format := Format.all.find? (·.name == s)

/-- Round trip. Says: every `AudioSampleFormat` name is read as its format. -/
theorem Format.ofName?_name (f : Format) : Format.ofName? f.name = some f := by
  rcases f with ⟨s, p⟩; cases s <;> cases p <;> decide

/-! ## AudioDataInit -/

/-- `⌊frames × 10⁶ / rate⌋` for the rate `m × 2^e` (a positive double), exactly. -/
def durationOf (frames : Nat) (m : Nat) (e : Int) : Nat :=
  if 0 ≤ e then frames * 1000000 / (m * 2 ^ e.toNat) else frames * 1000000 * 2 ^ (-e).toNat / m

/-- "valid AudioDataInit" and the duration: `none` (a TypeError) unless frames, channels and the
rate are above zero and the data has the bytes of every sample. The answer: the bytes the
`AudioData` keeps, and its duration in microseconds. -/
def initCheck (f : Format) (frames channels : Nat) (rate : Option (Int × Int)) (dataSize : Nat) : Option (Nat × Nat) :=
  match rate with
  | some (m, e) =>
    let size := frames * channels * f.sample.bytes
    if frames = 0 ∨ channels = 0 ∨ m ≤ 0 ∨ dataSize < size then none
    else some (size, durationOf frames m.toNat e)
  | none => none

/-- Refusal. Says: an init with no frames, no channels, or a rate that is not above zero is
refused, whatever its data. -/
theorem initCheck_refuses (f : Format) (frames channels : Nat) (m e : Int) (dataSize : Nat)
    (h : frames = 0 ∨ channels = 0 ∨ m ≤ 0) : initCheck f frames channels (some (m, e)) dataSize = none := by
  unfold initCheck
  simp only
  rw [if_pos (by omega)]

/-! ## copyTo -/

/-- What a copy refuses: a RangeError, or a conversion this does not make (NotSupportedError). -/
inductive Refusal where
  | range | notSupported
  deriving DecidableEq, Repr

/-- The elements of a copy: from frame `offset`, `count` frames; one channel (`plane`) for a planar
destination, all channels interleaved for an interleaved one. -/
structure Plan where
  dst : Format
  plane : Nat
  offset : Nat
  count : Nat
  elements : Nat
  deriving Repr, DecidableEq

def Plan.size (p : Plan) : Nat := p.elements * p.dst.sample.bytes

/-- "Compute Copy Element Count" (§9.2.5). Every conversion between the eight formats is made, so
no copy is refused as not supported. -/
def plan (src : Format) (frames channels : Nat) (dst : Option Format) (plane offset : Nat) (count : Option Nat) :
    Except Refusal Plan :=
  let d := dst.getD src
  if !d.planar && plane > 0 then .error .range
  else if d.planar && plane ≥ channels then .error .range
  else if offset ≥ frames then .error .range
  else
    let avail := frames - offset
    match count with
    | some c => if c > avail then .error .range else .ok ⟨d, plane, offset, c, if d.planar then c else c * channels⟩
    | none => .ok ⟨d, plane, offset, avail, if d.planar then avail else avail * channels⟩

/-- The source byte of sample (frame `f`, channel `c`). -/
def srcIndex (src : Format) (frames channels f c : Nat) : Nat :=
  (if src.planar then c * frames + f else f * channels + c) * src.sample.bytes

theorem lin_lt {r c w h : Nat} (hr : r < h) (hc : c < w) : r * w + c < h * w := by
  have : (r + 1) * w ≤ h * w := Nat.mul_le_mul_right w hr
  rw [Nat.succ_mul] at this
  omega

/-- Bounds. Says: every sample a copy reads starts inside the data of `frames × channels` samples,
with its whole width inside. -/
theorem srcIndex_lt (src : Format) (frames channels f c : Nat) (hf : f < frames) (hc : c < channels) :
    srcIndex src frames channels f c + src.sample.bytes ≤ frames * channels * src.sample.bytes := by
  unfold srcIndex
  have hb := src.sample.bytes_pos
  have key : (if src.planar then c * frames + f else f * channels + c) < frames * channels := by
    split
    · have := lin_lt hc hf; rw [Nat.mul_comm channels frames] at this; exact this
    · exact lin_lt hf hc
  have := Nat.mul_le_mul_right src.sample.bytes (Nat.succ_le_of_lt key)
  rw [Nat.succ_mul] at this
  exact this

/-! ## Samples -/

def u32le (b : ByteArray) (o : Nat) : Nat :=
  (b.get! o).toNat + (b.get! (o + 1)).toNat * 256 + (b.get! (o + 2)).toNat * 65536 + (b.get! (o + 3)).toNat * 16777216

/-- Two's complement of `bits` bits. -/
def signed (v bits : Nat) : Int := if v < 2 ^ (bits - 1) then v else (v : Int) - 2 ^ bits

/-- A sample, read: an integer sample centred on zero (`u8` less its bias of 128), or the bits of
an `f32`. -/
inductive Value where
  | int (v : Int)
  | float (bits : UInt32)

def read (s : Sample) (b : ByteArray) (o : Nat) : Value :=
  match s with
  | .u8 => .int ((b.get! o).toNat - 128 : Int)
  | .s16 => .int (signed ((b.get! o).toNat + (b.get! (o + 1)).toNat * 256) 16)
  | .s32 => .int (signed (u32le b o) 32)
  | .f32 => .float (UInt32.ofNat (u32le b o))

/-- An integer sample of `k` bits as one of `k'` bits, by shifting: exact when widening; when
narrowing, the low bits are dropped (rounding down, as an arithmetic shift does). -/
def widen (v : Int) (k k' : Nat) : Int := v * 2 ^ (k' - k)
def narrow (v : Int) (k k' : Nat) : Int := v / 2 ^ (k - k')

def rescale (v : Int) (k k' : Nat) : Int := if k ≤ k' then widen v k k' else narrow v k k'

/-- Round trip, lossless. Says: a sample widened to more bits and narrowed back is itself. -/
theorem narrow_widen (v : Int) (k k' : Nat) : narrow (widen v k k') k' k = v := by
  unfold narrow widen
  have hp : (0 : Int) < 2 ^ (k' - k) := Int.pow_pos (by decide)
  rw [Int.mul_ediv_cancel _ (by omega)]

/-- The largest and smallest centred sample of `k` bits. -/
def hi (k : Nat) : Int := 2 ^ (k - 1) - 1
def lo (k : Nat) : Int := -(2 ^ (k - 1))

/-- A float sample as an integer sample of `k` bits: scaled by 2^(k-1), rounded to nearest,
clamped (NaN is silence). -/
def ofFloat (x : Float) (k : Nat) : Int :=
  let y := x * (2 ^ (k - 1) : Nat).toFloat
  if y.isNaN then 0
  else if y ≥ (hi k).toNat.toFloat then hi k
  else if y ≤ -(2 ^ (k - 1) : Nat).toFloat then lo k
  else y.round.toInt64.toInt

/-- An integer sample of `k` bits as a float: divided by 2^(k-1), rounded to `f32`. -/
def toFloat (v : Int) (k : Nat) : UInt32 :=
  (Float.ofInt v / (2 ^ (k - 1) : Nat).toFloat).toFloat32.toBits

/-- The bytes of an integer sample of the destination's width (centred; `u8` gets its bias). -/
def putInt (out : ByteArray) (s : Sample) (v : Int) : ByteArray :=
  match s with
  | .u8 => out.push (UInt8.ofNat (v + 128).toNat)
  | .s16 => let u := (v % 65536).toNat; (out.push (UInt8.ofNat u)).push (UInt8.ofNat (u / 256))
  | _ =>
    let u := (v % 4294967296).toNat
    (((out.push (UInt8.ofNat u)).push (UInt8.ofNat (u / 256))).push (UInt8.ofNat (u / 65536))).push (UInt8.ofNat (u / 16777216))

def putBits (out : ByteArray) (w : UInt32) : ByteArray :=
  let u := w.toNat
  (((out.push (UInt8.ofNat u)).push (UInt8.ofNat (u / 256))).push (UInt8.ofNat (u / 65536))).push (UInt8.ofNat (u / 16777216))

/-- One sample converted to the destination's sample type and appended. -/
def put (out : ByteArray) (d : Sample) (v : Value) (k : Nat) : ByteArray :=
  match v, d with
  | .float w, .f32 => putBits out w
  | .float w, _ => putInt out d (ofFloat (Float32.ofBits w).toFloat d.bits)
  | .int i, .f32 => putBits out (toFloat i k)
  | .int i, _ => putInt out d (rescale i k d.bits)

/-- The copy: `p.elements` samples of `p.dst`'s type, read from `data` (a `frames × channels`
`AudioData` of format `src`). -/
def copy (src : Format) (frames channels : Nat) (data : ByteArray) (p : Plan) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity p.size
  for e in [0:p.elements] do
    let (f, c) := if p.dst.planar then (p.offset + e, p.plane) else (p.offset + e / channels, e % channels)
    out := put out p.dst.sample (read src.sample data (srcIndex src frames channels f c)) src.sample.bits
  return out

/-! ## PCM decoders -/

/-- G.711 μ-law expansion (ITU-T G.711, as the reference decoder computes it). -/
def ulaw (b : Nat) : Int :=
  let u := 255 - b % 256
  let t : Nat := ((u % 16) * 8 + 132) * 2 ^ ((u / 16) % 8)
  if u ≥ 128 then 132 - (t : Int) else (t : Int) - 132

/-- G.711 A-law expansion. -/
def alaw (b : Nat) : Int :=
  let a := (b % 256) ^^^ 0x55
  let seg := (a / 16) % 8
  let m := a % 16
  let t : Nat := if seg = 0 then m * 16 + 8 else (m * 16 + 264) * 2 ^ (seg - 1)
  if a ≥ 128 then (t : Int) else -(t : Int)

set_option maxRecDepth 8000 in
/-- Bounds. Says: every μ-law code expands into a 16-bit sample, at most 32124 from zero. -/
theorem ulaw_range : ∀ b : Fin 256, -32124 ≤ ulaw b.val ∧ ulaw b.val ≤ 32124 := by decide

set_option maxRecDepth 8000 in
/-- Bounds. Says: every A-law code expands into a 16-bit sample, at most 32256 from zero. -/
theorem alaw_range : ∀ b : Fin 256, -32256 ≤ alaw b.val ∧ alaw b.val ≤ 32256 := by decide

/-- Symmetry. Says: the sign bit of a μ-law code only negates its sample. -/
theorem ulaw_odd : ∀ b : Fin 128, ulaw (b.val + 128) = -ulaw b.val := by decide

/-- Symmetry. Says: the sign bit of an A-law code only negates its sample. -/
theorem alaw_odd : ∀ b : Fin 128, alaw (b.val + 128) = -alaw b.val := by decide

/-- The PCM codecs: the bytes of one sample in a chunk, and the format of the `AudioData` the
decoder outputs (interleaved, as the chunk is). -/
def pcmIn : Codec.Named → Option (Nat × Format)
  | .pcmU8 => some (1, ⟨.u8, false⟩)
  | .pcmS16 => some (2, ⟨.s16, false⟩)
  | .pcmS24 => some (3, ⟨.s32, false⟩)
  | .pcmS32 => some (4, ⟨.s32, false⟩)
  | .pcmF32 => some (4, ⟨.f32, false⟩)
  | .ulaw => some (1, ⟨.s16, false⟩)
  | .alaw => some (1, ⟨.s16, false⟩)
  | _ => none

/-- A chunk of `codec` decoded: the `AudioData`'s format, its frames and its bytes. `none` (an
EncodingError) when the chunk is not whole frames of `channels` samples. -/
def pcmDecode (codec : Codec.Named) (channels : Nat) (chunk : ByteArray) : Option (Format × Nat × ByteArray) :=
  match pcmIn codec with
  | none => none
  | some (w, f) =>
  if channels = 0 ∨ chunk.size % (w * channels) ≠ 0 then none else
  let n := chunk.size / w
  let out := match codec with
    | .pcmS24 => Id.run do
      let mut out := ByteArray.emptyWithCapacity (n * 4)
      for i in [0:n] do
        out := (((out.push 0).push (chunk.get! (3 * i))).push (chunk.get! (3 * i + 1))).push (chunk.get! (3 * i + 2))
      return out
    | .ulaw | .alaw => Id.run do
      let mut out := ByteArray.emptyWithCapacity (n * 2)
      for i in [0:n] do
        let b := (chunk.get! i).toNat
        out := putInt out .s16 (if codec == .ulaw then ulaw b else alaw b)
      return out
    | _ => chunk
  some (f, n / channels, out)

/-! ## Tests (`webcodecs/audio-data.any.js`, `audioDecoder-pcm-output`) -/

private def f32s (xs : List UInt32) : ByteArray := xs.foldl putBits ByteArray.empty
private def asInts (s : Sample) (b : ByteArray) : List Int :=
  (List.range (b.size / s.bytes)).map fun i => match read s b (i * s.bytes) with
    | .int v => if s == .u8 then v + 128 else v
    | .float _ => 0
private def ints (s : Sample) (xs : List Int) : ByteArray := xs.foldl (fun o v => putInt o s (if s == .u8 then v - 128 else v)) ByteArray.empty

-- 100 frames at 8000 Hz (8000 = 1000 × 2^3): 12500 µs.
#guard initCheck ⟨.f32, true⟩ 100 2 (decodeDouble 0x40BF400000000000) 800 == some (800, 12500)
#guard initCheck ⟨.f32, true⟩ 100 2 (decodeDouble 0x40BF400000000000) 400 == none
#guard initCheck ⟨.f32, true⟩ 0 2 (decodeDouble 0x40BF400000000000) 800 == none
#guard initCheck ⟨.f32, true⟩ 100 2 (decodeDouble 0xBFF0000000000000) 800 == none
-- Interleaved source, planar copy of plane 1 is fine; an interleaved destination with plane 1 is a RangeError.
#guard (plan ⟨.f32, false⟩ 4 2 none 1 0 none).toOption.isNone
#guard (plan ⟨.f32, false⟩ 4 2 (some ⟨.f32, true⟩) 1 0 none).toOption.map (·.elements) == some 4
#guard (plan ⟨.f32, true⟩ 4 2 (some ⟨.s16, false⟩) 0 1 (some 2)).toOption.map Plan.size == some 8
#guard (plan ⟨.f32, true⟩ 4 2 none 0 4 none).toOption.isNone
#guard (plan ⟨.f32, true⟩ 4 2 none 0 1 (some 4)).toOption.isNone
-- The template of the conversion tests: s16 [MIN, BIAS, MAX, MIN, HALF, NEG_HALF, BIAS, MAX, BIAS, BIAS], 2 channels.
private def s16in : ByteArray := ints .s16 [-32768, 0, 32767, -32768, 16383, -16384, 0, 32767, 0, 0]
#guard asInts .s16 (copy ⟨.s16, false⟩ 5 2 s16in ⟨⟨.s16, true⟩, 0, 0, 5, 5⟩) == [-32768, 32767, 16383, 0, 0]
#guard asInts .s16 (copy ⟨.s16, false⟩ 5 2 s16in ⟨⟨.s16, true⟩, 1, 0, 5, 5⟩) == [0, -32768, -16384, 32767, 0]
#guard asInts .u8 (copy ⟨.s16, false⟩ 5 2 s16in ⟨⟨.u8, true⟩, 0, 0, 5, 5⟩) == [0, 255, 191, 128, 128]
#guard asInts .s32 (copy ⟨.s16, false⟩ 5 2 s16in ⟨⟨.s32, true⟩, 1, 0, 5, 5⟩) == [0, -2147483648, -1073741824, 2147418112, 0]
-- Planar source to interleaved: all channels, frame by frame.
#guard asInts .s16 (copy ⟨.s16, true⟩ 5 2 s16in ⟨⟨.s16, false⟩, 0, 0, 5, 10⟩) ==
  [-32768, -16384, 0, 0, 32767, 32767, -32768, 0, 16383, 0]
-- f32: -1, 1, 0.5, -0.5, 0 to s16 and u8; s16 to f32.
private def fin : ByteArray := f32s [0xBF800000, 0x3F800000, 0x3F000000, 0xBF000000, 0]
#guard asInts .s16 (copy ⟨.f32, true⟩ 5 1 fin ⟨⟨.s16, true⟩, 0, 0, 5, 5⟩) == [-32768, 32767, 16384, -16384, 0]
#guard asInts .u8 (copy ⟨.f32, true⟩ 5 1 fin ⟨⟨.u8, true⟩, 0, 0, 5, 5⟩) == [0, 255, 192, 64, 128]
#guard copy ⟨.f32, true⟩ 5 1 fin ⟨⟨.f32, true⟩, 0, 0, 5, 5⟩ == fin
#guard copy ⟨.s16, true⟩ 2 1 (ints .s16 [-32768, 16384]) ⟨⟨.f32, true⟩, 0, 0, 2, 2⟩ == f32s [0xBF800000, 0x3F000000]
-- G.711: code 0xFF is μ-law silence, 0x00 its most negative; 0xD5 is A-law's smallest positive step.
#guard ulaw 0xFF == 0 ∧ ulaw 0x00 == -32124 ∧ ulaw 0x80 == 32124
#guard alaw 0xD5 == 8 ∧ alaw 0x55 == -8 ∧ alaw 0xAA == 32256
-- s24 1, -1 (little-endian) as s32 256, -256; a chunk of a half sample is refused.
#guard (pcmDecode .pcmS24 1 ⟨#[1, 0, 0, 0xFF, 0xFF, 0xFF]⟩).map (fun (f, n, b) => (f.name, n, asInts .s32 b)) ==
  some ("s32", 2, [256, -256])
#guard (pcmDecode .pcmS16 2 ⟨#[1, 0, 2]⟩).isNone
#guard (pcmDecode .opus 1 ⟨#[]⟩).isNone

end L4Factoidal.WebCodecs.Audio
