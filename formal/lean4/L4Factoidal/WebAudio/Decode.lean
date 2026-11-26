import L4Factoidal.WebAudio.Buffer
import L4Factoidal.Media.Decode
import L4Factoidal.Media.Modules

/-!
# Web Audio: `decodeAudioData`

Stage C of https://github.com/danbri/factoidal-core/issues/1169 (plan:
`docs/designissues/2026-11-26-foafnaut-audio-plan.md`, sections 3, 4 and 12). Section "The
BaseAudioContext Interface", method `decodeAudioData`: the encoded audio is decoded, "the decoded
audio is resampled to the sample rate of the BaseAudioContext", and the result is an
`AudioBuffer`. Data that cannot be decoded gives an `EncodingError`.

## Steps

1. Sniff the format from the first bytes: `RIFF` (WAV), `OggS` (Ogg Opus or Ogg Vorbis), the EBML
   magic (WebM with an Opus or Vorbis track), otherwise MP3 (`Media.Mp3.read` finds the first
   frame; ID3v2, ID3v1 and APEv2 tags are skipped).
2. Decode to planar `Float` channels: WAV in Lean (`Media.Wav`); Opus, Vorbis and MP3 by the
   pinned WasmVM modules (`Media.Decode.opusF32`, `vorbisF32`, `mp3F32`). A module is used only
   after `Media.Modules.check` (size and SHA-256 of the bytes, then `mw_abi` is the pinned one is
   checked by the pin list). The host gives module bytes through the `modules` function, by file
   name (`opus-wasmvm.wasm`, `vorbis-wasmvm.wasm`, `mp3-wasmvm.wasm`); only the modules the file
   needs are asked for.
3. Vorbis channels are put in the order of Web Audio's channel layouts for 3 to 8 channels
   (`vorbisToSmpte`: L R C LFE ... as FFmpeg's decoder does); the order inside the Vorbis stream is
   Vorbis I section 4.3.9.
4. Resample every channel to the context's rate (`resample`, below).
5. Build the `AudioBuffer`: every sample rounded to binary32 (`Buffer.toF32`), the sample rate
   the context's rate rounded to binary32 as `AudioBuffer.create` does.

## The resampler

The specification does not give an algorithm for the resampling in `decodeAudioData`. This one is
a band-limited interpolator: each output sample is a weighted sum of the input samples around its
position, with weights from a Kaiser-windowed sinc.

* Output frame `k` is at input position `t = k * inRate / outRate` (frame 0 on frame 0: no delay).
* Cut-off: the lower of the two Nyquist frequencies: `fc = min 1 (outRate / inRate)` in units of
  the input Nyquist. Weight of input sample `j`: `fc * K(|j - t| * fc)`, where `K(u) =
  sinc(u) * I0(beta * sqrt(1 - (u / L)^2)) / I0(beta)` for `u < L` and 0 otherwise, with `L = 32`
  zero crossings on each side and Kaiser `beta = 9`. At `fc = 1` that is 64 taps. When
  downsampling the kernel is stretched by `1 / fc`: `2 * ceil(L / fc)` taps.
* `K` is read from a table of 2048 steps for each unit of `u`, with linear interpolation between
  entries (the interpolation error is at most `h^2 * max|K''| / 8` = 3e-7 of the peak, below -110 dB).
* The weights of one output frame are divided by their sum, so a constant signal stays constant
  (the weights alone sum to 1 within about 1e-3 for a Kaiser sinc; the division removes that
  ripple at DC). Input outside the clip is zero: the first and last `ceil(L / fc)` output
  samples are faded by the missing taps.
* When the rates are equal nothing is done. When both rates are whole numbers the weights depend
  only on `(k * inRate) mod outRate`, at most `outRate / gcd(inRate, outRate)` values, and are
  computed once for each (when there are at most 4096 of them).
* Output length: `ceil(frames * outRate / inRate)` (exact in natural numbers when `outRate` is a
  whole number). The last output frame is the last one at or after the end of the input.

Measured quality (the guards at the end of this file; `media-bench decode`): at 48 kHz to 8 kHz
the gain of a sine is 1 within 1e-4 up to 0.9 of the lower Nyquist (the pointwise error of a
440 Hz sine is 1e-5 to 3e-5, below -90 dB), 0.958 at 0.95 (-0.4 dB), 0.75 at 0.98, 0 at 1.0
(the sampled sine is 0), 0.042 at 1.05 (-27 dB, folded back) and 7e-6 at 1.1 (-103 dB). The
same figures hold at 44.1 kHz to 48 kHz. No claim is made between 0.9 and 1.1 of the lower
Nyquist other than these points.
-/

namespace L4Factoidal.WebAudio.Decode

open L4Factoidal.WebAudio.Buffer
open L4Factoidal.WebAudio.Kernels (mkChan)
open L4Factoidal.Media

/-! ## Errors -/

/-- What `decodeAudioData` signals. -/
inductive DecodeError where
  /-- `EncodingError`: the data is not a supported audio file, could not be decoded, or a decoder
  module that the file needs was not given or is not a pinned one (`detail` says which). -/
  | encoding (detail : String)
  /-- `NotSupportedError`: the context's sample rate is outside 3000 to 768000 Hz. -/
  | notSupported (detail : String)
  deriving Repr

/-- The `DOMException` name the page sees. -/
def DecodeError.name : DecodeError → String
  | .encoding _ => "EncodingError"
  | .notSupported _ => "NotSupportedError"

def DecodeError.detail : DecodeError → String
  | .encoding d => d
  | .notSupported d => d

/-! ## The resampler -/

/-- Zero crossings of the sinc on each side of the centre. -/
def zeroCrossings : Nat := 32
/-- Kaiser window parameter. -/
def kaiserBeta : Float := 9.0
/-- Table entries for each unit of `u`. -/
def tableSteps : Nat := 2048

/-- Modified Bessel function of the first kind, order 0: the series `sum ((x/2)^k / k!)^2`. -/
def besselI0 (x : Float) : Float := Id.run do
  let q := x * x / 4.0
  let mut term := 1.0
  let mut sum := 1.0
  for k in [1:200] do
    term := term * q / (k.toFloat * k.toFloat)
    sum := sum + term
    if term < sum * 1e-17 then break
  return sum

def pi : Float := 3.141592653589793

/-- `K(u)`, exactly (no table). -/
def kernelExact (u : Float) : Float :=
  let L := zeroCrossings.toFloat
  if u ≥ L then 0.0 else
  let s := if u == 0.0 then 1.0 else Float.sin (pi * u) / (pi * u)
  let r := u / L
  s * besselI0 (kaiserBeta * Float.sqrt (1.0 - r * r)) / besselI0 kaiserBeta

/-- `K` at `i / tableSteps`, for `i` from 0 to `zeroCrossings * tableSteps + 1`. -/
def kernelTable : FloatArray := Id.run do
  let mut a := FloatArray.emptyWithCapacity (zeroCrossings * tableSteps + 2)
  for i in [0:zeroCrossings * tableSteps + 2] do
    a := a.push (kernelExact (i.toFloat / tableSteps.toFloat))
  return a

/-- `K(u)` for `u ≥ 0` by linear interpolation in the table. -/
def kernelAt (u : Float) : Float :=
  let p := u * tableSteps.toFloat
  let i := p.floor.toUInt64.toNat
  if i ≥ zeroCrossings * tableSteps then 0.0 else
  let f := p - i.toFloat
  kernelTable.get! i * (1.0 - f) + kernelTable.get! (i + 1) * f

/-- Half the number of taps: `ceil(L / fc)`. -/
def halfTaps (fc : Float) : Nat := (zeroCrossings.toFloat / fc).ceil.toUInt64.toNat

/-- The `2 * hs` weights of an output sample whose position is `frac` after input sample `i0`:
tap `m` is input sample `i0 - hs + 1 + m`. Divided by their sum. -/
def weights (hs : Nat) (fc frac : Float) : FloatArray := Id.run do
  let mut w := FloatArray.emptyWithCapacity (2 * hs)
  let mut s := 0.0
  for m in [0:2 * hs] do
    let x := (m.toFloat - (hs.toFloat - 1.0)) - frac
    let v := fc * kernelAt (x.abs * fc)
    w := w.push v
    s := s + v
  if s > 0.0 then
    let mut n := FloatArray.emptyWithCapacity (2 * hs)
    for m in [0:2 * hs] do
      n := n.push (w.get! m / s)
    return n
  return w

/-- Number of output frames: `ceil(frames * outRate / inRate)`; exact in `Nat` when `outRate`
is a whole number below 2^32, otherwise computed in `Float` (a product within 1e-6 of a whole
number is taken as that number). -/
def outLength (frames inRate : Nat) (outRate : Float) : Nat :=
  if outRate == outRate.floor && outRate ≥ 1.0 && outRate < 4294967296.0 then
    (frames * outRate.toUInt64.toNat + inRate - 1) / inRate
  else
    let x := frames.toFloat * outRate / inRate.toFloat
    let r := x.round
    if (x - r).abs < 1e-6 then r.toUInt64.toNat else x.ceil.toUInt64.toNat

/-- Resample planar channels from `inRate` to `outRate`. -/
def resample (chans : Array FloatArray) (inRate : Nat) (outRate : Float) : Array FloatArray := Id.run do
  let inF := inRate.toFloat
  if outRate == inF || inRate == 0 || !(outRate > 0.0) then return chans
  let frames := (chans[0]?.map (·.size)).getD 0
  let n := outLength frames inRate outRate
  let fc := if outRate < inF then outRate / inF else 1.0
  let hs := halfTaps fc
  let whole := outRate == outRate.floor && outRate ≥ 1.0 && outRate < 4294967296.0
  let outR := outRate.toUInt64.toNat
  let g := Nat.gcd inRate outR
  let cache : Array FloatArray :=
    if whole && outR / g ≤ 4096 then
      (Array.range (outR / g)).map fun q => weights hs fc ((q * g).toFloat / outR.toFloat)
    else #[]
  let mut outs := Array.replicate chans.size (FloatArray.emptyWithCapacity n)
  for k in [0:n] do
    let (i0, frac, q) :=
      if whole then ((k * inRate) / outR, ((k * inRate) % outR).toFloat / outR.toFloat, ((k * inRate) % outR) / g)
      else
        let t := k.toFloat * (inF / outRate)
        let f := t.floor
        (f.toUInt64.toNat, t - f, 0)
    let w := if cache.isEmpty then weights hs fc frac else cache[q]!
    let base : Int := (i0 : Int) + 1 - hs
    let lim : Int := (frames : Int) - base
    let mLo := if base < 0 then (-base).toNat else 0
    let mHi := if lim ≤ 0 then 0 else min (2 * hs) lim.toNat
    for c in [0:chans.size] do
      let a := chans[c]!
      let mut acc := 0.0
      for m in [mLo:mHi] do
        acc := acc + w.get! m * a.get! (base + m).toNat
      outs := outs.modify c (·.push acc)
  return outs

/-! ## Format sniffing and decoding -/

inductive Kind where
  | wav | ogg | webm | mp3
  deriving DecidableEq, Repr

def sniff (b : ByteArray) : Kind :=
  if Wav.idAt b 0 == "RIFF" || Wav.idAt b 0 == "RIFX" || Wav.idAt b 0 == "RF64" then .wav
  else if Wav.idAt b 0 == "OggS" then .ogg
  else if b.size ≥ 4 && b[0]! == 0x1A && b[1]! == 0x45 && b[2]! == 0xDF && b[3]! == 0xA3 then .webm
  else .mp3

/-- The channel order of Web Audio's layouts from Vorbis order, for 3 to 8 channels: output
channel `i` is Vorbis channel `vorbisToSmpte[n-1][i]` (the permutations of FFmpeg's Vorbis
decoder). 1 and 2 channels and 4 (L R SL SR in both) are unchanged. -/
def vorbisToSmpte (n : Nat) : List Nat :=
  match n with
  | 3 => [0, 2, 1]
  | 5 => [0, 2, 1, 3, 4]
  | 6 => [0, 2, 1, 5, 3, 4]
  | 7 => [0, 2, 1, 6, 5, 3, 4]
  | 8 => [0, 2, 1, 7, 5, 6, 3, 4]
  | n => List.range n

def reorder (chans : Array FloatArray) (perm : List Nat) : Array FloatArray :=
  if perm.length != chans.size then chans
  else (perm.map fun i => chans[i]!).toArray

/-- Decoded audio before resampling. -/
structure Raw where
  /-- A name of the format: `wav-pcm16`, `opus`, `vorbis`, `mp3`, ... -/
  format : String
  rate : Nat
  samples : Array FloatArray
  nanReplaced : Nat

/-- The module `file`, checked against `Media.Modules.pins`. -/
def getModule (modules : String → Option ByteArray) (file : String) : IO ByteArray := do
  match modules file with
  | none => throw (IO.userError s!"decoder module {file} was not given")
  | some b =>
    match Modules.check file b with
    | .ok _ => pure b
    | .error e => throw (IO.userError e)

def wavName (f : Wav.Format) : String :=
  s!"wav-{match f.encoding with | .pcm => "pcm" | .float => "float" | .alaw => "alaw" | .mulaw => "mulaw"}{f.bits}"

/-- Decode (no resampling). -/
def decodeRaw (b : ByteArray) (modules : String → Option ByteArray) : IO (Except DecodeError Raw) := do
  let enc := fun (e : String) => (.error (.encoding e) : Except DecodeError Raw)
  try
    match sniff b with
    | .wav =>
      match Wav.read b with
      | .error e => return enc e.describe
      | .ok w => return .ok { format := wavName w.format, rate := w.format.rate, samples := w.samples, nanReplaced := w.nonFinite }
    | .mp3 =>
      match Mp3.read b with
      | .error e => return enc s!"not a supported audio file ({e})"
      | .ok s =>
        let p ← Decode.mp3F32 (← getModule modules "mp3-wasmvm.wasm") b s
        return .ok { format := "mp3", rate := p.rate, samples := p.samples, nanReplaced := p.nanReplaced }
    | .ogg =>
      let r := Ogg.demux b
      match r.streams.find? (fun s => s.codec == .opus || s.codec == .vorbis) with
      | none => return enc "Ogg file with no Opus or Vorbis stream"
      | some s =>
        let isOpus := s.codec == .opus
        let opusW ← if isOpus then getModule modules "opus-wasmvm.wasm" else pure .empty
        let vorbisW ← if isOpus then pure .empty else getModule modules "vorbis-wasmvm.wasm"
        let p ← Decode.oggAudioF32 opusW vorbisW b
        let ch := if isOpus then p.samples else reorder p.samples (vorbisToSmpte p.channels)
        return .ok { format := if isOpus then "ogg-opus" else "ogg-vorbis", rate := p.rate, samples := ch, nanReplaced := p.nanReplaced }
    | .webm =>
      match WebM.demux b with
      | .error e => return enc s!"not a supported audio file ({e})"
      | .ok r =>
        match r.tracks.find? (fun t => t.codec == "A_OPUS" || t.codec == "A_VORBIS") with
        | none => return enc "WebM file with no Opus or Vorbis audio track"
        | some t =>
          let isOpus := t.codec == "A_OPUS"
          let opusW ← if isOpus then getModule modules "opus-wasmvm.wasm" else pure .empty
          let vorbisW ← if isOpus then pure .empty else getModule modules "vorbis-wasmvm.wasm"
          let p ← Decode.webmAudioF32 opusW vorbisW r
          let ch := if isOpus then p.samples else reorder p.samples (vorbisToSmpte p.channels)
          return .ok { format := if isOpus then "webm-opus" else "webm-vorbis", rate := p.rate, samples := ch, nanReplaced := p.nanReplaced }
  catch e =>
    return enc e.toString

/-- A decoded buffer with what the decode found. -/
structure Decoded where
  buffer : AudioBuffer
  format : String
  /-- The sample rate of the file, before resampling. -/
  sourceRate : Nat
  /-- Frames of the file, before resampling. -/
  sourceFrames : Nat
  nanReplaced : Nat

/-- `decodeAudioData` with the details of the decode. `contextRate` is the sample rate of the
`BaseAudioContext`. -/
def decode (bytes : ByteArray) (contextRate : Float) (modules : String → Option ByteArray) :
    IO (Except DecodeError Decoded) := do
  match ← decodeRaw bytes modules with
  | .error e => return .error e
  | .ok raw =>
    let frames := (raw.samples[0]?.map (·.size)).getD 0
    if frames == 0 then return .error (.encoding "the file has no audio samples")
    let out := resample raw.samples raw.rate contextRate
    let len := (out[0]?.map (·.size)).getD 0
    match AudioBuffer.create out.size len contextRate with
    | .error _ =>
      return .error (.notSupported s!"cannot make a buffer of {out.size} channels, {len} frames at {contextRate} Hz")
    | .ok b0 =>
      let data := out.map fun a => (⟨a.data.map toF32⟩ : FloatArray)
      return .ok { buffer := { b0 with data }, format := raw.format, sourceRate := raw.rate,
                   sourceFrames := frames, nanReplaced := raw.nanReplaced }

/-- `BaseAudioContext.decodeAudioData`, the decoding and the resampling (the promise and the
callbacks are the page's). -/
def decodeAudioData (bytes : ByteArray) (contextRate : Float) (modules : String → Option ByteArray) :
    IO (Except DecodeError AudioBuffer) := do
  return (← decode bytes contextRate modules).map (·.buffer)

/-! ## Tests: the resampler -/

def sineChan (n : Nat) (rate freq amp : Float) : FloatArray :=
  mkChan n fun i => amp * Float.sin (2.0 * pi * freq * i.toFloat / rate)

/-- The largest difference from the ideal sine `amp * sin(2 pi freq k / outRate)` over the output
frames `[lo, n - lo)` (the frames away from the edges). -/
def sineError (out : FloatArray) (outRate freq amp : Float) (lo : Nat) : Float := Id.run do
  let mut e := 0.0
  for k in [lo:out.size - lo] do
    let d := (out.get! k - amp * Float.sin (2.0 * pi * freq * k.toFloat / outRate)).abs
    if d > e then e := d
  return e

def maxDev (out : FloatArray) (v : Float) (lo : Nat) : Float := Id.run do
  let mut e := 0.0
  for k in [lo:out.size - lo] do
    let d := (out.get! k - v).abs
    if d > e then e := d
  return e

-- The kernel: K(0) = 1, K at the integers is 0, the table follows the exact function.
#guard kernelExact 0.0 == 1.0
#guard (kernelExact 1.0).abs < 1e-12 && (kernelExact 7.0).abs < 1e-12 && kernelExact 32.0 == 0.0
#guard kernelAt 0.0 == 1.0
#guard (kernelAt 0.3333 - kernelExact 0.3333).abs < 3e-7
#guard (kernelAt 12.7071 - kernelExact 12.7071).abs < 3e-7
#guard kernelTable.size == 32 * 2048 + 2
-- I0(0) = 1, I0(1) = 1.2660658777520084.
#guard besselI0 0.0 == 1.0 && (besselI0 1.0 - 1.2660658777520084).abs < 1e-15
-- Output lengths.
#guard outLength 1000 44100 48000.0 == 1089
#guard outLength 44100 44100 48000.0 == 48000
#guard outLength 48000 48000 44100.0 == 44100
#guard outLength 1 8000 48000.0 == 6
#guard outLength 10 48000 8000.0 == 2
#guard outLength 1000 44100 48000.5 == 1089
-- The same rate is the identity.
#guard (resample #[sineChan 500 48000.0 1000.0 0.5] 48000 48000.0)[0]!.data == (sineChan 500 48000.0 1000.0 0.5).data
-- A constant stays constant away from the edges, and the output length is outLength.
#guard (resample #[mkChan 1000 fun _ => 0.5] 44100 48000.0)[0]!.size == 1089
#guard maxDev (resample #[mkChan 1000 fun _ => 0.5] 44100 48000.0)[0]! 0.5 40 < 1e-12
#guard maxDev (resample #[mkChan 4000 fun _ => -0.25] 48000 44100.0)[0]! (-0.25) 40 < 1e-12
#guard maxDev (resample #[mkChan 4000 fun _ => 0.75] 48000 8000.0)[0]! 0.75 40 < 1e-12
#guard maxDev (resample #[mkChan 1000 fun _ => 0.5] 44100 48000.5)[0]! 0.5 40 < 1e-12
-- A sine below Nyquist keeps its frequency, amplitude and phase.
#guard sineError (resample #[sineChan 4000 44100.0 1000.0 0.8] 44100 48000.0)[0]! 48000.0 1000.0 0.8 40 < 1e-5
#guard sineError (resample #[sineChan 4000 48000.0 1000.0 0.8] 48000 44100.0)[0]! 44100.0 1000.0 0.8 40 < 1e-5
#guard sineError (resample #[sineChan 4000 22050.0 440.0 0.8] 22050 48000.0)[0]! 48000.0 440.0 0.8 120 < 3e-5
#guard sineError (resample #[sineChan 12000 48000.0 440.0 0.8] 48000 8000.0)[0]! 8000.0 440.0 0.8 200 < 1e-5
#guard sineError (resample #[sineChan 4000 44100.0 1000.0 0.8] 44100 48000.5)[0]! 48000.5 1000.0 0.8 40 < 1e-5
-- Near the passband limit (0.8 of the lower Nyquist: 17.64 kHz at 44.1 kHz) the error is larger.
#guard sineError (resample #[sineChan 4000 44100.0 17640.0 0.8] 44100 48000.0)[0]! 48000.0 17640.0 0.8 40 < 1e-3
-- A tone above the new Nyquist is removed (stopband): 10 kHz at 48 kHz down to 8 kHz.
#guard maxDev (resample #[sineChan 12000 48000.0 10000.0 0.8] 48000 8000.0)[0]! 0.0 300 < 1e-5
-- 0.9 of the lower Nyquist (3.6 kHz at 8 kHz) is kept; 1.05 of it (4.2 kHz) is 27 dB down or more.
#guard sineError (resample #[sineChan 12000 48000.0 3600.0 0.8] 48000 8000.0)[0]! 8000.0 3600.0 0.8 300 < 3e-5
#guard maxDev (resample #[sineChan 12000 48000.0 4200.0 0.8] 48000 8000.0)[0]! 0.0 300 < 0.8 * 0.05
-- Every channel is resampled the same way; a short clip does not fail.
#guard (resample #[mkChan 10 fun _ => 0.5, mkChan 10 fun _ => -0.5] 8000 48000.0).map (·.size) == #[60, 60]
#guard (resample #[mkChan 1 fun _ => 0.5] 8000 48000.0)[0]!.size == 6
-- Vorbis channel orders.
#guard vorbisToSmpte 6 == [0, 2, 1, 5, 3, 4] && vorbisToSmpte 2 == [0, 1] && vorbisToSmpte 1 == [0]
#guard (reorder #[⟨#[0.0]⟩, ⟨#[1.0]⟩, ⟨#[2.0]⟩] (vorbisToSmpte 3)).map (·.data[0]!) == #[0.0, 2.0, 1.0]
-- Sniffing.
#guard sniff (Wav.ascii "RIFF....WAVE") == .wav && sniff (Wav.ascii "OggS....") == .ogg
#guard sniff (Wav.bytes [0x1A, 0x45, 0xDF, 0xA3, 0]) == .webm && sniff (Wav.ascii "ID3\x04") == .mp3
-- A WAV is decoded and resampled in Lean, with no decoder module (`#eval` that throws fails the build).
#eval show IO Unit from do
  let wavBytes := Wav.build 1 2 8000 16 (Wav.bytes ((List.range 40).flatMap fun i => [0, if i % 2 == 0 then 0x40 else 0xC0]))
  match ← decodeAudioData wavBytes 48000.0 (fun _ => none) with
  | .error e => throw (IO.userError s!"WAV decode: {e.detail}")
  | .ok b =>
    unless b.numberOfChannels == 2 && b.length == 120 && b.sampleRate == 48000.0 && b.data.size == 2 do
      throw (IO.userError s!"WAV decode: {b.numberOfChannels} channels, {b.length} frames")
  -- not audio: EncodingError; a module that is not given: EncodingError; a rate out of range: NotSupportedError.
  match ← decodeAudioData (Wav.ascii "not audio at all, just text") 48000.0 (fun _ => none) with
  | .error e => unless e.name == "EncodingError" do throw (IO.userError e.name)
  | .ok _ => throw (IO.userError "text decoded")
  match ← decodeAudioData (Wav.ascii "OggS\x00\x02") 48000.0 (fun _ => none) with
  | .error e => unless e.name == "EncodingError" do throw (IO.userError e.name)
  | .ok _ => throw (IO.userError "Ogg stub decoded")
  match ← decodeAudioData wavBytes 100.0 (fun _ => none) with
  | .error e => unless e.name == "NotSupportedError" do throw (IO.userError e.name)
  | .ok _ => throw (IO.userError "rate 100 accepted")

end L4Factoidal.WebAudio.Decode
