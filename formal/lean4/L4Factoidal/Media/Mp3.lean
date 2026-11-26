/-
L4Factoidal.Media.Mp3: an MP3 stream read in Lean (record:
docs/designissues/2026-11-26-foafnaut-audio-plan.md, sections 3 and 4; issue
https://github.com/danbri/factoidal-core/issues/1169, stage C).

An MP3 file is a sequence of MPEG audio frames (ISO/IEC 11172-3 for MPEG-1; ISO/IEC 13818-3 for
MPEG-2 at half the sample rates; MPEG-2.5, an extension outside the standards, at a quarter),
after an optional ID3v2 tag and before optional APEv2 and ID3v1 tags. The first frame may be an
information frame (a "Xing" or "Info" header, or a "VBRI" header) that holds no audio; a LAME
extension in a Xing or Info header gives the encoder delay and padding, for gapless playback.

`read` skips the tags, checks each frame header, and lists the audio frames, so the decoder
module (`mp3-wasmvm.wasm`, minimp3) gets one whole frame per call and never searches for one.
Free-format streams (bit rate index 0) are refused. Pure; every loop is bounded by the input
size.
-/
namespace L4Factoidal.Media.Mp3

/-- One frame header (the four bytes that start a frame). -/
structure Header where
  /-- 10 for MPEG-1, 20 for MPEG-2, 25 for MPEG-2.5. -/
  version : Nat
  layer : Nat
  /-- A 16-bit CRC follows the header. -/
  crc : Bool
  /-- kbit/s. -/
  bitrate : Nat
  /-- Hz. -/
  rate : Nat
  padding : Bool
  /-- Channel mode 3 (single channel). -/
  mono : Bool
  frameBytes : Nat
  /-- Samples per channel in the frame. -/
  samples : Nat
  deriving Repr, BEq

def Header.channels (h : Header) : Nat := if h.mono then 1 else 2

/-- Bit rates in kbit/s by index 0 to 14 (ISO/IEC 11172-3 2.4.2.3, ISO/IEC 13818-3 2.4.2.3). -/
def bitrates (version layer : Nat) : Array Nat :=
  match version, layer with
  | 10, 1 => #[0, 32, 64, 96, 128, 160, 192, 224, 256, 288, 320, 352, 384, 416, 448]
  | 10, 2 => #[0, 32, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320, 384]
  | 10, _ => #[0, 32, 40, 48, 56, 64, 80, 96, 112, 128, 160, 192, 224, 256, 320]
  | _, 1 => #[0, 32, 48, 56, 64, 80, 96, 112, 128, 144, 160, 176, 192, 224, 256]
  | _, _ => #[0, 8, 16, 24, 32, 40, 48, 56, 64, 80, 96, 112, 128, 144, 160]

/-- Sample rates in Hz by index 0 to 2. -/
def rates (version : Nat) : Array Nat :=
  match version with
  | 10 => #[44100, 48000, 32000]
  | 20 => #[22050, 24000, 16000]
  | _ => #[11025, 12000, 8000]

def byteAt (b : ByteArray) (i : Nat) : Nat := if h : i < b.size then b[i].toNat else 0

/-- The frame header at `i`, or `none` when the four bytes there are not one (no sync, a
reserved version, layer, bit rate or sample rate, or free format). -/
def header? (b : ByteArray) (i : Nat) : Option Header := do
  if b.size < i + 4 then none
  let b1 := byteAt b (i + 1)
  let b2 := byteAt b (i + 2)
  let b3 := byteAt b (i + 3)
  if !(byteAt b i == 0xFF && b1 >>> 5 == 7) then none
  let version ← match (b1 >>> 3) &&& 3 with
    | 0 => some 25 | 2 => some 20 | 3 => some 10 | _ => none
  let layer ← match (b1 >>> 1) &&& 3 with
    | 1 => some 3 | 2 => some 2 | 3 => some 1 | _ => none
  let bi := b2 >>> 4
  let si := (b2 >>> 2) &&& 3
  if bi == 0 || bi == 15 || si == 3 then none
  let bitrate := (bitrates version layer)[bi]!
  let rate := (rates version)[si]!
  let padding := (b2 >>> 1) &&& 1 == 1
  let pad := if padding then 1 else 0
  let half := layer == 3 && version != 10
  let frameBytes :=
    if layer == 1 then (12 * bitrate * 1000 / rate + pad) * 4
    else if half then 72 * bitrate * 1000 / rate + pad
    else 144 * bitrate * 1000 / rate + pad
  let samples := if layer == 1 then 384 else if half then 576 else 1152
  pure { version, layer, crc := b1 &&& 1 == 0, bitrate, rate, padding, mono := b3 >>> 6 == 3,
         frameBytes, samples }

/-- Two headers belong to one stream: same version, layer and sample rate. -/
def Header.same (h k : Header) : Bool := h.version == k.version && h.layer == k.layer && h.rate == k.rate

/-- Bytes of ID3v2 tags at `i` (header, size as a synchsafe integer, footer when its flag is
set), repeated while one follows another; 0 when none. -/
def id3v2End (b : ByteArray) (i : Nat) : Nat := Id.run do
  let mut p := i
  for _ in [0:4] do
    if b.size ≥ p + 10 && byteAt b p == 0x49 && byteAt b (p + 1) == 0x44 && byteAt b (p + 2) == 0x33 then
      let s := ((byteAt b (p + 6) &&& 0x7F) <<< 21) ||| ((byteAt b (p + 7) &&& 0x7F) <<< 14) |||
               ((byteAt b (p + 8) &&& 0x7F) <<< 7) ||| (byteAt b (p + 9) &&& 0x7F)
      let footer := if byteAt b (p + 5) &&& 0x10 != 0 then 10 else 0
      p := p + 10 + s + footer
  return p

def tagAt (b : ByteArray) (i : Nat) (t : String) : Bool :=
  t.toUTF8.size ≤ b.size - i && (List.range t.toUTF8.size).all fun k => byteAt b (i + k) == t.toUTF8[k]!.toNat

/-- Where the audio ends: before an ID3v1 tag ("TAG", the last 128 bytes) and an APEv2 tag
("APETAGEX" footer of 32 bytes, its size field counting items and footer, plus a 32-byte header
when its flag says so). -/
def audioEnd (b : ByteArray) : Nat := Id.run do
  let mut e := b.size
  if e ≥ 128 && tagAt b (e - 128) "TAG" then e := e - 128
  if e ≥ 32 && tagAt b (e - 32) "APETAGEX" then
    let f := e - 32
    let size := byteAt b (f + 12) ||| (byteAt b (f + 13) <<< 8) ||| (byteAt b (f + 14) <<< 16) ||| (byteAt b (f + 15) <<< 24)
    let header := if byteAt b (f + 23) &&& 0x80 != 0 then 32 else 0
    if size + header ≤ e then e := e - size - header
  return e

/-- Big-endian 32-bit value at `i`. -/
def be32 (b : ByteArray) (i : Nat) : Nat :=
  (byteAt b i <<< 24) ||| (byteAt b (i + 1) <<< 16) ||| (byteAt b (i + 2) <<< 8) ||| byteAt b (i + 3)

/-- Side information bytes of a layer III frame (ISO/IEC 11172-3 2.4.1.7, 13818-3 2.4.1.7). -/
def sideInfo (h : Header) : Nat :=
  if h.version == 10 then (if h.mono then 17 else 32) else (if h.mono then 9 else 17)

/-- What an information frame says: its frame count (when present) and the LAME encoder delay
and padding (when present). -/
structure Info where
  frames : Option Nat
  delay : Option Nat
  padding : Option Nat
  deriving Repr, BEq

/-- The information frame at `off` (frame header `h`), or `none` when the frame holds audio.
A Xing or Info header sits after the side information; its flags say which fields follow (frame
count, byte count, 100-byte table, quality); a LAME extension after them ("LAME", or FFmpeg's
"Lavf"/"Lavc") holds the encoder delay and padding as two 12-bit numbers 21 bytes in. A VBRI
header sits 32 bytes after the header. -/
def info? (b : ByteArray) (off : Nat) (h : Header) : Option Info := do
  let stop := off + h.frameBytes
  let x := off + 4 + (if h.crc then 2 else 0) + sideInfo h
  if h.layer == 3 && (tagAt b x "Xing" || tagAt b x "Info") && x + 8 ≤ stop then
    let flags := be32 b (x + 4)
    let mut q := x + 8
    let frames := if flags &&& 1 != 0 then some (be32 b q) else none
    if flags &&& 1 != 0 then q := q + 4
    if flags &&& 2 != 0 then q := q + 4
    if flags &&& 4 != 0 then q := q + 100
    if flags &&& 8 != 0 then q := q + 4
    if q + 24 ≤ stop && (tagAt b q "LAME" || tagAt b q "Lavf" || tagAt b q "Lavc") then
      let d := byteAt b (q + 21)
      let e := byteAt b (q + 22)
      let f := byteAt b (q + 23)
      pure { frames, delay := some ((d <<< 4) ||| (e >>> 4)), padding := some (((e &&& 0x0F) <<< 8) ||| f) }
    else pure { frames, delay := none, padding := none }
  else if tagAt b (off + 36) "VBRI" then pure { frames := none, delay := none, padding := none }
  else none

/-- An MP3 stream: the audio frames (offset and length; an information frame is not listed),
the header of the first, and the samples to drop at the start and to keep for gapless playback. -/
structure Stream where
  frames : Array (Nat × Nat)
  header : Header
  info : Option Info
  /-- Samples per channel to drop at the start: encoder delay plus the 529 samples of decoder
  delay of layer III (the LAME convention, also FFmpeg's), when a LAME header gives the delay. -/
  skip : Nat
  /-- Samples per channel to keep after `skip`, when a LAME header gives the padding. -/
  keep : Option Nat
  deriving Repr

/-- How far `read` looks for the first frame after the tags (bytes). -/
def searchLimit : Nat := 65536

/-- A frame at `i` that the next header confirms (same stream), or that ends exactly at `stop`. -/
def confirmed? (b : ByteArray) (i stop : Nat) : Option Header := do
  let h ← header? b i
  if i + h.frameBytes > stop then none
  if i + h.frameBytes == stop then pure h
  else
    let k ← header? b (i + h.frameBytes)
    if h.same k then pure h else none

/-- Read an MP3 stream. Errors name what is wrong and where. -/
def read (b : ByteArray) : Except String Stream := do
  let start := id3v2End b 0
  let stop := audioEnd b
  -- The first frame: at `start`, else the first confirmed header within `searchLimit` bytes.
  let mut first : Option (Nat × Header) := none
  for k in [0:min searchLimit (stop - start)] do
    if first.isNone then
      if let some h := confirmed? b (start + k) stop then first := some (start + k, h)
  let some (p0, h0) := first | throw s!"mp3: no MPEG audio frame in the first {searchLimit} bytes after offset {start}"
  let inf := info? b p0 h0
  let mut frames : Array (Nat × Nat) := #[]
  let mut p := if inf.isSome then p0 + h0.frameBytes else p0
  -- Each step moves forward by a frame (at least 24 bytes) or ends the loop.
  for _ in [0:stop - p0 + 1] do
    if p < stop then
      match header? b p with
      | some h =>
        if h.same h0 && p + h.frameBytes ≤ stop then
          frames := frames.push (p, h.frameBytes)
          p := p + h.frameBytes
        else p := stop
      | none => p := stop
  if frames.isEmpty then throw s!"mp3: no audio frame after offset {p0}"
  let spf := h0.samples
  let (skip, keep) := match inf with
    | some { delay := some d, padding := some pd, frames := fs } =>
      let total := (fs.getD frames.size) * spf
      let skip := d + 529
      (skip, some ((total + 529 - pd) - skip))
    | _ => (0, none)
  pure { frames, header := h0, info := inf, skip, keep }

/-! ## Tests: headers of the standards' examples, sizes, tags -/

-- MPEG-1 layer III, 128 kbit/s, 44100 Hz, no padding: 144 * 128000 / 44100 = 417 bytes.
#guard (header? (ByteArray.mk #[0xFF, 0xFB, 0x90, 0x64]) 0).map (fun h => (h.version, h.layer, h.bitrate, h.rate, h.frameBytes, h.samples, h.mono)) ==
  some (10, 3, 128, 44100, 417, 1152, false)
-- The same with the padding bit: 418 bytes.
#guard (header? (ByteArray.mk #[0xFF, 0xFB, 0x92, 0x64]) 0).map (·.frameBytes) == some 418
-- MPEG-2 layer III, 48 kbit/s (index 6), 22050 Hz, single channel: 72 * 48000 / 22050 = 156.
#guard (header? (ByteArray.mk #[0xFF, 0xF3, 0x60, 0xC4]) 0).map (fun h => (h.version, h.bitrate, h.rate, h.frameBytes, h.samples, h.channels)) ==
  some (20, 48, 22050, 156, 576, 1)
-- MPEG-1 layer II, 192 kbit/s (index 10), 48000 Hz: 144 * 192000 / 48000 = 576.
#guard (header? (ByteArray.mk #[0xFF, 0xFD, 0xA4, 0x00]) 0).map (fun h => (h.layer, h.bitrate, h.frameBytes, h.samples)) == some (2, 192, 576, 1152)
-- MPEG-1 layer I, 384 kbit/s (index 12), 32000 Hz: (12 * 384000 / 32000) * 4 = 576.
#guard (header? (ByteArray.mk #[0xFF, 0xFF, 0xC8, 0x00]) 0).map (fun h => (h.layer, h.frameBytes, h.samples)) == some (1, 576, 384)
-- Refused: free format, bit rate index 15, sample rate index 3, reserved version, no sync.
#guard (header? (ByteArray.mk #[0xFF, 0xFB, 0x00, 0x64]) 0).isNone
#guard (header? (ByteArray.mk #[0xFF, 0xFB, 0xF0, 0x64]) 0).isNone
#guard (header? (ByteArray.mk #[0xFF, 0xFB, 0x9C, 0x64]) 0).isNone
#guard (header? (ByteArray.mk #[0xFF, 0xEB, 0x90, 0x64]) 0).isNone
#guard (header? (ByteArray.mk #[0xFE, 0xFB, 0x90, 0x64]) 0).isNone
#guard (header? (ByteArray.mk #[0xFF, 0xFB, 0x90]) 0).isNone
-- ID3v2: size 0x0201 as a synchsafe integer is 257; with the 10-byte header the audio starts at 267.
#guard id3v2End (ByteArray.mk (#[0x49, 0x44, 0x33, 4, 0, 0, 0, 0, 2, 1] ++ Array.replicate 300 0)) 0 == 267
#guard id3v2End (ByteArray.mk #[0xFF, 0xFB, 0x90, 0x64]) 0 == 0
-- ID3v1: a file that ends with "TAG" and 125 more bytes loses 128 bytes.
#guard audioEnd (ByteArray.mk (Array.replicate 200 0 ++ #[0x54, 0x41, 0x47] ++ Array.replicate 125 0)) == 200
-- An empty input is refused with a message.
#guard (read ByteArray.empty).toOption.isNone

end L4Factoidal.Media.Mp3
