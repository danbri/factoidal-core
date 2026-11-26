/-
L4Factoidal.Media.Wav: a RIFF/WAVE reader (stage C of
https://github.com/danbri/factoidal-core/issues/1169; plan:
docs/designissues/2026-11-26-foafnaut-audio-plan.md sections 3 and 4).

Pure, total, no recursion: every loop is bounded by the size of the input.

## Accepted

* Container: `RIFF` with form type `WAVE`. `RIFX` (big-endian), `RF64` and `BW64` are refused with
  a named error.
* Chunks: each chunk is an id, a little-endian 32-bit size and the body; the next chunk starts
  after the body and, for an odd size, after one pad byte. Unknown chunks are skipped by size. A
  chunk whose declared size runs past the end of the file is read up to the end of the file
  (a truncated download still plays what is there). For the `data` chunk, a size of 0 or
  4294967295 followed by more bytes is read as "to the end of the file" (streaming writers
  that do not know the length write these).
* `fmt ` chunk: format tag 1 (integer PCM: 8 bits unsigned, 16, 24 and 32 bits signed), 3 (IEEE
  float: 32 and 64 bits), 6 (A-law) and 7 (mu-law) (both 8 bits), and 0xFFFE
  (`WAVE_FORMAT_EXTENSIBLE`) whose sub-format GUID is one of those four tags with the
  standard GUID tail. The bits per sample are the container size; `wValidBitsPerSample` and the
  channel mask are ignored (the samples are left-justified in their container, so the same
  scaling applies). The block alignment field is not trusted: the frame size is
  channels times bytes per sample.
* 1 to 32 channels (the limit of `AudioBuffer`), a sample rate of at least 1.

## Sample conversion (to `Float` in [-1, 1))

| Format | Value of a stored integer `v` |
|---|---|
| 8-bit PCM (unsigned) | `(v - 128) / 128` |
| 16-bit PCM | `v / 32768` |
| 24-bit PCM | `v / 8388608` |
| 32-bit PCM | `v / 2147483648` |
| A-law, mu-law | the G.711 decoded 16-bit value, divided by 32768 |
| float 32 and 64 | the stored value; NaN and infinity become 0 and are counted |

These are the conversions of FFmpeg's `pcm_s16le` and the other PCM decoders to float (divide by
2^(bits-1)). A frame cut off at the end of the `data` chunk is dropped.
-/

namespace L4Factoidal.Media.Wav

/-- The reasons a file is refused. -/
inductive Error where
  | tooShort
  | notRiff
  /-- `RIFX`, `RF64` or `BW64`. -/
  | unsupportedContainer (id : String)
  | notWave
  | noFmt
  | noData
  | fmtTooShort (size : Nat)
  | unsupportedTag (tag : Nat)
  | unsupportedSubFormat
  | badChannels (n : Nat)
  | badRate
  | badBits (tag bits : Nat)
  deriving DecidableEq, Repr

def Error.describe : Error → String
  | .tooShort => "WAV: fewer than 12 bytes"
  | .notRiff => "WAV: no RIFF header"
  | .unsupportedContainer id => s!"WAV: container {id} is not supported"
  | .notWave => "WAV: RIFF form type is not WAVE"
  | .noFmt => "WAV: no fmt chunk"
  | .noData => "WAV: no data chunk"
  | .fmtTooShort n => s!"WAV: fmt chunk of {n} bytes (16 at least)"
  | .unsupportedTag t => s!"WAV: format tag {t} is not supported"
  | .unsupportedSubFormat => "WAV: unsupported WAVE_FORMAT_EXTENSIBLE sub-format"
  | .badChannels n => s!"WAV: {n} channels (1 to 32 supported)"
  | .badRate => "WAV: sample rate 0"
  | .badBits t b => s!"WAV: {b} bits per sample is not supported for format tag {t}"

/-- Sample encodings. -/
inductive Encoding where
  | pcm | float | alaw | mulaw
  deriving DecidableEq, Repr

structure Format where
  encoding : Encoding
  channels : Nat
  rate : Nat
  /-- Bits of one stored sample (the container size). -/
  bits : Nat
  deriving DecidableEq, Repr

structure Wav where
  format : Format
  /-- Complete frames read. -/
  frames : Nat
  /-- One array of `frames` values in [-1, 1) for each channel. -/
  samples : Array FloatArray
  /-- Float samples that were NaN or infinite and became 0. -/
  nonFinite : Nat := 0

/-! ## Reading numbers -/

def byteAt (b : ByteArray) (i : Nat) : Nat := if h : i < b.size then b[i].toNat else 0

def u16 (b : ByteArray) (i : Nat) : Nat := byteAt b i + 256 * byteAt b (i + 1)
def u32 (b : ByteArray) (i : Nat) : Nat := u16 b i + 65536 * u16 b (i + 2)

/-- `n` bytes at `i`, little-endian, as a natural number. -/
def uN (b : ByteArray) (i n : Nat) : Nat := Id.run do
  let mut v := 0
  for k in [0:n] do
    v := v + byteAt b (i + k) * 256 ^ k
  return v

/-- The two's-complement value of the `bits`-bit number `v`. -/
def signed (v bits : Nat) : Int :=
  if v < 2 ^ (bits - 1) then (v : Int) else (v : Int) - (2 ^ bits : Nat)

def idAt (b : ByteArray) (i : Nat) : String :=
  String.ofList ((List.range 4).map fun k => Char.ofNat (byteAt b (i + k)))

/-! ## G.711 -/

/-- G.711 mu-law to 16-bit linear (ITU-T G.711, as in Sun's `g711.c`). -/
def mulawToS16 (v : Nat) : Int :=
  let u := (255 - v % 256)
  let exp := (u / 16) % 8
  let mant := u % 16
  let s : Int := (((mant * 8 + 0x84) * 2 ^ exp : Nat) : Int) - 0x84
  if u / 128 % 2 == 1 then -s else s

/-- G.711 A-law to 16-bit linear (ITU-T G.711, as in Sun's `g711.c`): the even bits are
inverted (XOR 0x55) and a set sign bit means positive. -/
def alawToS16 (v : Nat) : Int :=
  let a := (v % 256) ^^^ 0x55
  let seg := (a / 16) % 8
  let t := (a % 16) * 16
  let m : Nat := if seg == 0 then t + 8 else (t + 0x108) * 2 ^ (seg - 1)
  if a / 128 % 2 == 1 then (m : Int) else -(m : Int)

/-! ## The fmt chunk -/

/-- The standard tail of a sub-format GUID (after the two byte format tag):
`0000-0010-8000-00AA00389B71`. -/
def guidTail : List Nat := [0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xAA, 0x00, 0x38, 0x9B, 0x71]

def parseFmt (b : ByteArray) (off size : Nat) : Except Error Format := do
  if size < 16 then throw (.fmtTooShort size)
  let tag0 := u16 b off
  let channels := u16 b (off + 2)
  let rate := u32 b (off + 4)
  let bits := u16 b (off + 14)
  let tag ← if tag0 == 0xFFFE then
      if size < 40 then throw .unsupportedSubFormat
      else if (List.range 14).map (fun k => byteAt b (off + 26 + k)) == guidTail then pure (u16 b (off + 24))
      else throw .unsupportedSubFormat
    else pure tag0
  let enc ← match tag with
    | 1 => pure Encoding.pcm
    | 3 => pure Encoding.float
    | 6 => pure Encoding.alaw
    | 7 => pure Encoding.mulaw
    | t => throw (.unsupportedTag t)
  if channels < 1 || channels > 32 then throw (.badChannels channels)
  if rate == 0 then throw .badRate
  let okBits := match enc with
    | .pcm => bits == 8 || bits == 16 || bits == 24 || bits == 32
    | .float => bits == 32 || bits == 64
    | .alaw | .mulaw => bits == 8
  if !okBits then throw (.badBits tag bits)
  return { encoding := enc, channels, rate, bits }

/-! ## Samples -/

/-- One sample as `Float`, from its stored bytes at `i`. Second component: 1 when a float
sample was not finite (and is 0). -/
def sampleAt (f : Format) (b : ByteArray) (i : Nat) : Float × Nat :=
  match f.encoding with
  | .alaw => (Float.ofInt (alawToS16 (byteAt b i)) / 32768.0, 0)
  | .mulaw => (Float.ofInt (mulawToS16 (byteAt b i)) / 32768.0, 0)
  | .pcm =>
    if f.bits == 8 then ((Float.ofNat (byteAt b i) - 128.0) / 128.0, 0)
    else
      let v := signed (uN b i (f.bits / 8)) f.bits
      (Float.ofInt v / Float.ofNat (2 ^ (f.bits - 1)), 0)
  | .float =>
    let x := if f.bits == 32 then (Float32.ofBits (u32 b i).toUInt32).toFloat
      else Float.ofBits (uN b i 8).toUInt64
    if x.isNaN || x.isInf then (0.0, 1) else (x, 0)

/-- Samples of the `data` chunk bytes at `off`, `len` bytes long. -/
def readSamples (f : Format) (b : ByteArray) (off len : Nat) : Array FloatArray × Nat × Nat := Id.run do
  let bps := f.bits / 8
  let frameBytes := bps * f.channels
  let frames := len / frameBytes
  let mut chans : Array FloatArray := #[]
  let mut bad := 0
  for c in [0:f.channels] do
    let mut a : FloatArray := FloatArray.emptyWithCapacity frames
    for i in [0:frames] do
      let (x, n) := sampleAt f b (off + i * frameBytes + c * bps)
      a := a.push x
      bad := bad + n
    chans := chans.push a
  return (chans, frames, bad)

/-! ## The file -/

/-- Read a RIFF/WAVE file. -/
def read (b : ByteArray) : Except Error Wav := do
  if b.size < 12 then throw .tooShort
  match idAt b 0 with
  | "RIFF" => pure ()
  | "RIFX" => throw (.unsupportedContainer "RIFX")
  | "RF64" => throw (.unsupportedContainer "RF64")
  | "BW64" => throw (.unsupportedContainer "BW64")
  | _ => throw .notRiff
  if idAt b 8 != "WAVE" then throw .notWave
  -- Chunk walk: at most one chunk for each 8 bytes of the file.
  let mut off := 12
  let mut fmt : Option (Nat × Nat) := none
  let mut dat : Option (Nat × Nat) := none
  for _ in [0:b.size / 8 + 1] do
    if off + 8 > b.size || (fmt.isSome && dat.isSome) then break
    let id := idAt b off
    let size := u32 b (off + 4)
    let body := off + 8
    let avail := b.size - body
    let len := min size avail
    if id == "fmt " && fmt.isNone then fmt := some (body, len)
    if id == "data" && dat.isNone then
      let len := if (size == 0 || size == 4294967295) then avail else len
      dat := some (body, len)
    off := body + size + size % 2
  let some (fo, fs) := fmt | throw .noFmt
  let some (dOff, dLen) := dat | throw .noData
  let f ← parseFmt b fo fs
  let (samples, frames, bad) := readSamples f b dOff dLen
  return { format := f, frames, samples, nonFinite := bad }

/-! ## Building files (for tests) -/

def le16 (v : Nat) : ByteArray := ByteArray.mk #[(v % 256).toUInt8, (v / 256 % 256).toUInt8]
def le32 (v : Nat) : ByteArray := le16 (v % 65536) ++ le16 (v / 65536 % 65536)
def ascii (s : String) : ByteArray := s.toUTF8
def bytes (l : List Nat) : ByteArray := ByteArray.mk (l.map (·.toUInt8)).toArray

/-- A WAVE file with a plain 16-byte `fmt ` chunk and the given `data` bytes. -/
def build (tag ch rate bits : Nat) (data : ByteArray) : ByteArray :=
  let fmt := le16 tag ++ le16 ch ++ le32 rate ++ le32 (rate * ch * bits / 8) ++ le16 (ch * bits / 8) ++ le16 bits
  ascii "RIFF" ++ le32 (4 + 8 + 16 + 8 + data.size) ++ ascii "WAVE" ++ ascii "fmt " ++ le32 16 ++ fmt ++
    ascii "data" ++ le32 data.size ++ data

def chan (w : Except Error Wav) (c : Nat) : List Float :=
  match w with
  | .ok w => ((w.samples[c]?).getD ⟨#[]⟩).data.toList
  | .error _ => []

def frames (w : Except Error Wav) : Nat := match w with | .ok w => w.frames | .error _ => 0

def err (w : Except Error Wav) : Option Error := match w with | .ok _ => none | .error e => some e

/-! ## Tests -/

-- 16-bit, mono: sample / 32768.
#guard chan (read (build 1 1 8000 16 (bytes [0x00, 0x40, 0x00, 0xC0, 0xFF, 0x7F, 0x00, 0x80]))) 0
  == [0.5, -0.5, 32767.0 / 32768.0, -1.0]
-- 16-bit, stereo: two channels, frames interleaved.
#guard (read (build 1 2 44100 16 (bytes [0, 0x40, 0, 0xC0, 0, 0x20, 0, 0xE0]))).toOption.map (·.frames) == some 2
#guard chan (read (build 1 2 44100 16 (bytes [0, 0x40, 0, 0xC0, 0, 0x20, 0, 0xE0]))) 1 == [-0.5, -0.25]
-- 8-bit unsigned: 128 is silence.
#guard chan (read (build 1 1 8000 8 (bytes [128, 255, 0, 192]))) 0 == [0.0, 127.0 / 128.0, -1.0, 0.5]
-- 24-bit and 32-bit.
#guard chan (read (build 1 1 8000 24 (bytes [0, 0, 0x40, 0, 0, 0x80]))) 0 == [0.5, -1.0]
#guard chan (read (build 1 1 8000 32 (bytes [0, 0, 0, 0x40, 0, 0, 0, 0x80]))) 0 == [0.5, -1.0]
-- Float 32 and 64.
#guard chan (read (build 3 1 8000 32 (bytes [0, 0, 0x80, 0x3F, 0, 0, 0, 0xBF]))) 0 == [1.0, -0.5]
#guard chan (read (build 3 1 8000 64 (bytes [0, 0, 0, 0, 0, 0, 0xE0, 0x3F]))) 0 == [0.5]
-- A NaN and an infinity in float data become 0 and are counted.
#guard (read (build 3 1 8000 32 (bytes [0, 0, 0xC0, 0x7F, 0, 0, 0x80, 0x7F, 0, 0, 0x80, 0x3F]))).toOption.map
  (fun w => (w.samples[0]!.data.toList, w.nonFinite)) == some ([0.0, 0.0, 1.0], 2)
-- mu-law and A-law: 0xFF is the smallest positive mu-law value (0), 0x80 the largest (32124);
-- A-law 0xD5 is +8 (the smallest positive), 0x55 is -8, 0xAA is +32256.
#guard mulawToS16 0xFF == 0 && mulawToS16 0x7F == 0 && mulawToS16 0x80 == 32124 && mulawToS16 0x00 == -32124
#guard alawToS16 0xD5 == 8 && alawToS16 0x55 == -8 && alawToS16 0xAA == 32256 && alawToS16 0x2A == -32256
#guard chan (read (build 7 1 8000 8 (bytes [0x80, 0xFF]))) 0 == [32124.0 / 32768.0, 0.0]
#guard chan (read (build 6 1 8000 8 (bytes [0xAA, 0xD5]))) 0 == [32256.0 / 32768.0, 8.0 / 32768.0]
-- The format is reported.
#guard (read (build 1 2 22050 16 (bytes [0, 0, 0, 0]))).toOption.map (·.format) ==
  some { encoding := .pcm, channels := 2, rate := 22050, bits := 16 }
-- A trailing partial frame is dropped.
#guard frames (read (build 1 2 8000 16 (bytes [0, 0, 0, 0, 0, 0]))) == 1
-- A declared data size larger than the file: read what is there.
#guard frames (read (ascii "RIFF" ++ le32 0 ++ ascii "WAVE" ++ ascii "fmt " ++ le32 16 ++ le16 1 ++ le16 1 ++
    le32 8000 ++ le32 16000 ++ le16 2 ++ le16 16 ++ ascii "data" ++ le32 1000000 ++ bytes [1, 0, 2, 0, 3, 0])) == 3
-- Unknown chunks are skipped by size, with the pad byte after an odd size.
#guard frames (read (ascii "RIFF" ++ le32 100 ++ ascii "WAVE" ++ ascii "LIST" ++ le32 3 ++ bytes [1, 2, 3, 0] ++
    ascii "fmt " ++ le32 16 ++ le16 1 ++ le16 1 ++ le32 8000 ++ le32 16000 ++ le16 2 ++ le16 16 ++
    ascii "data" ++ le32 4 ++ bytes [1, 0, 2, 0])) == 2
-- data before fmt.
#guard frames (read (ascii "RIFF" ++ le32 100 ++ ascii "WAVE" ++ ascii "data" ++ le32 4 ++ bytes [1, 0, 2, 0] ++
    ascii "fmt " ++ le32 16 ++ le16 1 ++ le16 1 ++ le32 8000 ++ le32 16000 ++ le16 2 ++ le16 16)) == 2
-- A streaming writer's data size 0 and 4294967295: to the end of the file.
#guard frames (read (ascii "RIFF" ++ le32 0 ++ ascii "WAVE" ++ ascii "fmt " ++ le32 16 ++ le16 1 ++ le16 1 ++
    le32 8000 ++ le32 16000 ++ le16 2 ++ le16 16 ++ ascii "data" ++ le32 4294967295 ++ bytes [1, 0, 2, 0, 3, 0])) == 3
-- WAVE_FORMAT_EXTENSIBLE with the float sub-format.
#guard chan (read (ascii "RIFF" ++ le32 100 ++ ascii "WAVE" ++ ascii "fmt " ++ le32 40 ++ le16 0xFFFE ++ le16 1 ++
    le32 8000 ++ le32 32000 ++ le16 4 ++ le16 32 ++ le16 22 ++ le16 32 ++ le32 4 ++ le16 3 ++
    bytes [0x00, 0x00, 0x00, 0x00, 0x10, 0x00, 0x80, 0x00, 0x00, 0xAA, 0x00, 0x38, 0x9B, 0x71] ++
    ascii "data" ++ le32 4 ++ bytes [0, 0, 0x80, 0x3F])) 0 == [1.0]
-- Refusals.
#guard err (read (bytes [1, 2, 3])) == some .tooShort
#guard err (read (ascii "OggS" ++ le32 0 ++ le32 0)) == some .notRiff
#guard err (read (ascii "RIFX" ++ le32 0 ++ ascii "WAVE")) == some (.unsupportedContainer "RIFX")
#guard err (read (ascii "RIFF" ++ le32 0 ++ ascii "AVI ")) == some .notWave
#guard err (read (ascii "RIFF" ++ le32 0 ++ ascii "WAVE")) == some .noFmt
#guard err (read (ascii "RIFF" ++ le32 0 ++ ascii "WAVE" ++ ascii "fmt " ++ le32 16 ++ le16 1 ++ le16 1 ++
    le32 8000 ++ le32 16000 ++ le16 2 ++ le16 16)) == some .noData
#guard err (read (build 85 1 8000 16 (bytes [0, 0]))) == some (.unsupportedTag 85)
#guard err (read (build 1 0 8000 16 (bytes [0, 0]))) == some (.badChannels 0)
#guard err (read (build 1 33 8000 16 (bytes [0, 0]))) == some (.badChannels 33)
#guard err (read (build 1 1 0 16 (bytes [0, 0]))) == some .badRate
#guard err (read (build 1 1 8000 12 (bytes [0, 0]))) == some (.badBits 1 12)
#guard err (read (build 3 1 8000 16 (bytes [0, 0]))) == some (.badBits 3 16)
#guard err (read (build 7 1 8000 16 (bytes [0, 0]))) == some (.badBits 7 16)
-- An empty data chunk gives 0 frames, not an error.
#guard frames (read (build 1 1 8000 16 ByteArray.empty)) == 0

end L4Factoidal.Media.Wav
