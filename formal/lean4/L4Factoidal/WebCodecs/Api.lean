/-
L4Factoidal.WebCodecs.Api: the WebCodecs operations of the `web_api` import (ops 120 to 139;
record: docs/designissues/2026-11-14-webgl-webcodecs.md, section 4).

  * 120 `frameOfBuffer(format, codedWidth, codedHeight, dataSize, layout, visibleRect, display,
    rotation, flip)`: `Frame.ofBuffer`. Answers the resource size and the frame's values, the
    format's default colour space, and one line for each plane with the rows to copy from the
    page's buffer into the resource.
  * 121 `frameOfFrame(format, base, visibleRect, display, rotation, flip)`: `Frame.derive`.
  * 122 `copyPlan(format, codedWidth, codedHeight, rect, layout, destinationSize)`: `copyPlan`,
    refused when the destination is smaller than the allocation size ("" for no destination:
    `allocationSize()`).
  * 123 `dropAlpha(format, codedWidth, codedHeight)`: the format without its alpha channel and the
    bytes of its resource (the first bytes of the frame's own: `PixelFormat.dropAlpha_planes`).
  * 124 `toRgb(format, codedWidth, codedHeight, rect, destinationFormat, matrix, fullRange, bytes)`:
    `Convert.toRgb`: the rectangle of the frame as packed pixels of an RGB format (bytes); -23
    (NotSupportedError) for a frame this does not convert.
  * 125 `checkConfig(kind, codec, members, detached)`: `Config.check`.
  * 126 `orient(rotation, flip, width, height, bytes)`: `Orient.orient`: packed 4-byte pixels
    of a `width × height` rectangle turned by the rotation (degrees) and mirrored when `flip` is
    "1", as a frame is drawn (bytes); -20 when the bytes are not `width × height` pixels.
  * 127 `audioInit(format, frames, channels, sampleRate, dataSize)`: `Audio.initCheck`: the bytes
    an `AudioData` keeps and its duration in microseconds ("size duration"). The sample rate is
    the 8 bytes of the page's double.
  * 128 `audioPlan(format, frames, channels, destFormat, planeIndex, frameOffset, frameCount)`:
    `Audio.plan`: "elements bytes"; -21 (RangeError) for what §9.2.5 refuses.
  * 129 `audioCopy(the same, bytes)`: `Audio.copy`: the samples of the copy (bytes).
  * 130 `pcmDecode(codec, channels, chunk)`: `Audio.pcmDecode`: the decoded samples (bytes);
    131 `pcmFormat(codec, channels, chunk)`: their format and frames ("format frames"). -20 for
    a chunk that is not whole frames, or a codec that is not PCM.
  * 132 `convertColors(from, to, bgr, bytes)`: `Gamut.convert`: RGBA pixels (BGRA when `bgr` is
    "1") from one predefined colour space to another (bytes); -20 for a name that is not one.
  * 133 `imageType(type)`: `Image.typeVerdict`: "invalid", "unsupported" or "supported".
  * 134 `imageOrientation(bytes)`: `Image.exifOrientation` as the frame's "rotation flip".

Arguments are fields of text: numbers in decimal, lists of numbers separated by spaces, "" for a
member the page did not give. The rotation is the 8 bytes of the page's double, little-endian.
Errors: -20 TypeError (what the standard refuses), -2 not an op.
-/
import L4Factoidal.WebCodecs.Frame
import L4Factoidal.WebCodecs.Convert
import L4Factoidal.WebCodecs.Config
import L4Factoidal.WebCodecs.Orient
import L4Factoidal.WebCodecs.Audio
import L4Factoidal.WebCodecs.Gamut
import L4Factoidal.WebCodecs.Image

namespace L4Factoidal.WebCodecs.Api

def strArg (fs : Array ByteArray) (i : Nat) : String :=
  match fs[i]? with
  | some b => (String.fromUTF8? b).getD ""
  | none => ""

/-- The numbers of a field ("" has none); `none` when a part is not a number. -/
def nats (s : String) : Option (List Nat) :=
  if s.isEmpty then some [] else (s.splitOn " ").mapM (·.toNat?)

def natArg (fs : Array ByteArray) (i : Nat) : Option Nat := (strArg fs i).toNat?

def rectOf : List Nat → Option (Option Rect)
  | [] => some none
  | [x, y, w, h] => some (some ⟨x, y, w, h⟩)
  | _ => none

def layoutOf (xs : List Nat) : Option (Option (List PlaneLayout)) :=
  if xs.isEmpty then some none
  else if xs.length % 2 != 0 then none
  else some (some ((List.range (xs.length / 2)).map fun i => ⟨xs.getD (2 * i) 0, xs.getD (2 * i + 1) 0⟩))

/-- `"-"`: only one of the two was given. -/
def displayOfArg (s : String) : Option (Option (Option (Nat × Nat))) :=
  if s == "-" then some (some none) else
  match nats s with
  | some [] => some none
  | some [w, h] => some (some (some (w, h)))
  | _ => none

/-- The 8 bytes of a double, little-endian, as (mantissa, exponent); an empty field is no rotation.
The outer `none`: not a finite double. -/
def rotationOf (b : ByteArray) : Option (Option (Int × Int)) :=
  if b.size == 0 then some none
  else if b.size != 8 then none
  else
    let bits := (List.range 8).foldl (fun acc i => acc + (b.get! i).toNat * 256 ^ i) 0
    (decodeDouble bits).map some

def initOf (fs : Array ByteArray) (i : Nat) : Option Init := do
  let visibleRect ← (nats (strArg fs i)).bind rectOf
  let display ← displayOfArg (strArg fs (i + 1))
  let rotation ← rotationOf (fs[i + 2]?.getD ByteArray.empty)
  pure { visibleRect, display, rotation, flip := strArg fs (i + 3) == "1" }

def moveLine (m : Move) : String :=
  s!"{m.srcOffset} {m.srcStride} {m.dstOffset} {m.dstStride} {m.widthBytes} {m.rows}"

def metaLine (m : Meta) : String :=
  s!"{m.codedWidth} {m.codedHeight} {m.visible.x} {m.visible.y} {m.visible.width} {m.visible.height} " ++
  s!"{m.displayWidth} {m.displayHeight} {m.rotation} {if m.flip then 1 else 0}"

def metaOf : List Nat → Option Meta
  | [cw, ch, vx, vy, vw, vh, dw, dh, r, fl] =>
    some { codedWidth := cw, codedHeight := ch, visible := ⟨vx, vy, vw, vh⟩, displayWidth := dw, displayHeight := dh,
           rotation := r % 360, flip := fl == 1 }
  | _ => none

/-- "Pick Color Space" (§9.4.6): sRGB for the RGB formats, Rec. 709 for the others, as
`primaries transfer matrix fullRange`; then `1` when the format's fourth byte is padding (RGBX,
BGRX), which the frame keeps as 255: such a frame is opaque whatever bytes the page gave there. -/
def defaultColorSpace (f : PixelFormat) : String :=
  (if f.isRgb then "bt709 iec61966-2-1 rgb 1" else "bt709 bt709 bt709 0") ++
  (if f == .rgbx || f == .bgrx then " 1" else " 0")

def frameOfBuffer (fs : Array ByteArray) : Option String := do
  let f ← PixelFormat.ofName? (strArg fs 0)
  let cw ← natArg fs 1
  let ch ← natArg fs 2
  let size ← natArg fs 3
  let layout ← (nats (strArg fs 4)).bind layoutOf
  let init ← initOf fs 5
  let (mt, plan) ← ofBuffer f cw ch size layout init
  pure ("\n".intercalate ([s!"{plan.resourceSize}", metaLine mt, defaultColorSpace f] ++
    (plan.moves.map Move.swap).map moveLine))

def frameOfFrame (fs : Array ByteArray) : Option String := do
  let f ← PixelFormat.ofName? (strArg fs 0)
  let base ← (nats (strArg fs 1)).bind metaOf
  let init ← initOf fs 2
  let mt ← derive f base init
  pure (metaLine mt)

def copyPlanOp (fs : Array ByteArray) : Option String := do
  let f ← PixelFormat.ofName? (strArg fs 0)
  let cw ← natArg fs 1
  let ch ← natArg fs 2
  let rect ← (nats (strArg fs 3)).bind rectOf
  let layout ← (nats (strArg fs 4)).bind layoutOf
  let plan ← copyPlan f cw ch (rect.getD ⟨0, 0, cw, ch⟩) layout
  let fits ← if strArg fs 5 == "" then some true else (natArg fs 5).map (plan.allocationSize ≤ ·)
  if !fits then none else
  pure ("\n".intercalate (s!"{plan.allocationSize}" :: plan.moves.map moveLine))

def dropAlphaOp (fs : Array ByteArray) : Option String := do
  let f ← PixelFormat.ofName? (strArg fs 0)
  let cw ← natArg fs 1
  let ch ← natArg fs 2
  pure s!"{f.dropAlpha.name} {resourceSize f.dropAlpha cw ch}"

def toRgbOp (fs : Array ByteArray) : Option ByteArray := do
  let f ← PixelFormat.ofName? (strArg fs 0)
  let cw ← natArg fs 1
  let ch ← natArg fs 2
  let rect ← (nats (strArg fs 3)).bind rectOf
  let dst ← PixelFormat.ofName? (strArg fs 4)
  toRgb f cw ch (rect.getD ⟨0, 0, cw, ch⟩) (fs[7]?.getD ByteArray.empty) dst (strArg fs 5) (strArg fs 6 == "1")

def numsOf (s : String) : List (String × Nat) :=
  (s.splitOn "\n").filterMap fun line =>
    match line.splitOn "=" with
    | [k, v] => v.toNat?.map (k, ·)
    | _ => none

def checkConfig (fs : Array ByteArray) : Option String := do
  let k ← Config.Kind.ofName? (strArg fs 0)
  pure (Config.check k { codec := strArg fs 1, nums := numsOf (strArg fs 2), detached := strArg fs 3 == "1" }).name

def orientOp (fs : Array ByteArray) : Option ByteArray := do
  let r ← natArg fs 0
  let w ← natArg fs 2
  let h ← natArg fs 3
  Orient.orient (Orient.quarters r) (strArg fs 1 == "1") w h (fs[4]?.getD ByteArray.empty)

def audioInitOp (fs : Array ByteArray) : Option String := do
  let f ← Audio.Format.ofName? (strArg fs 0)
  let frames ← natArg fs 1
  let channels ← natArg fs 2
  let rate ← rotationOf (fs[3]?.getD ByteArray.empty)
  let size ← natArg fs 4
  let (keep, duration) ← Audio.initCheck f frames channels rate size
  pure s!"{keep} {duration}"

/-- The plan of a copy; the outer `none` is a TypeError (arguments), the inner refusal a
RangeError. -/
def audioPlanOf (fs : Array ByteArray) : Option (Audio.Format × Nat × Nat × Except Audio.Refusal Audio.Plan) := do
  let f ← Audio.Format.ofName? (strArg fs 0)
  let frames ← natArg fs 1
  let channels ← natArg fs 2
  let dst ← if strArg fs 3 == "" then some none else (Audio.Format.ofName? (strArg fs 3)).map some
  let plane ← natArg fs 4
  let offset ← natArg fs 5
  let count ← if strArg fs 6 == "" then some none else (natArg fs 6).map some
  pure (f, frames, channels, Audio.plan f frames channels dst plane offset count)

def audioPlanOp (fs : Array ByteArray) : Except Int ByteArray :=
  match audioPlanOf fs with
  | none => .error (-20)
  | some (_, _, _, .error _) => .error (-21)
  | some (_, _, _, .ok p) => .ok s!"{p.elements} {p.size}".toUTF8

def audioCopyOp (fs : Array ByteArray) : Except Int ByteArray :=
  match audioPlanOf fs with
  | none => .error (-20)
  | some (_, _, _, .error _) => .error (-21)
  | some (f, frames, channels, .ok p) =>
    let data := fs[7]?.getD ByteArray.empty
    if data.size < frames * channels * f.sample.bytes then .error (-20)
    else .ok (Audio.copy f frames channels data p)

def pcmOf (fs : Array ByteArray) : Option (Audio.Format × Nat × ByteArray) := do
  let c ← Codec.Named.ofName? (strArg fs 0)
  let channels ← natArg fs 1
  Audio.pcmDecode c channels (fs[2]?.getD ByteArray.empty)

def convertColorsOp (fs : Array ByteArray) : Option ByteArray := do
  let a ← Gamut.Space.ofName? (strArg fs 0)
  let b ← Gamut.Space.ofName? (strArg fs 1)
  pure (Gamut.convert a b (strArg fs 2 == "1") (fs[3]?.getD ByteArray.empty))

def op (code : Nat) (fs : Array ByteArray) : Except Int ByteArray :=
  let answer := fun (r : Option String) => match r with
    | some s => .ok s.toUTF8
    | none => .error (-20)
  match code with
  | 120 => answer (frameOfBuffer fs)
  | 121 => answer (frameOfFrame fs)
  | 122 => answer (copyPlanOp fs)
  | 123 => answer (dropAlphaOp fs)
  | 124 => match toRgbOp fs with
    | some b => .ok b
    | none => .error (-23)
  | 125 => answer (checkConfig fs)
  | 126 => match orientOp fs with
    | some b => .ok b
    | none => .error (-20)
  | 127 => answer (audioInitOp fs)
  | 128 => audioPlanOp fs
  | 129 => audioCopyOp fs
  | 130 => match pcmOf fs with
    | some (_, _, b) => .ok b
    | none => .error (-20)
  | 131 => answer ((pcmOf fs).map fun (f, n, _) => s!"{f.name} {n}")
  | 132 => match convertColorsOp fs with
    | some b => .ok b
    | none => .error (-20)
  | 133 => .ok (Image.typeVerdict (strArg fs 0)).name.toUTF8
  | 134 =>
    let (r, f) := Image.orientationOf (Image.exifOrientation (fs[0]?.getD ByteArray.empty))
    .ok s!"{r} {if f then 1 else 0}".toUTF8
  | _ => .error (-2)

/-! ## Tests -/

private def run (code : Nat) (xs : List String) (bin : List (Nat × ByteArray) := []) : String :=
  let fs := (xs.map (·.toUTF8)).toArray
  let fs := bin.foldl (fun fs (i, b) => fs.set! i b) fs
  match op code fs with
  | .ok b => (String.fromUTF8? b).getD "?"
  | .error e => s!"error {e}"

-- I420 4 × 2 from 12 bytes: the resource is 12 bytes; three planes copied as they are.
#guard run 120 ["I420", "4", "2", "12", "", "", "", "", ""] ==
  "12\n4 2 0 0 4 2 4 2 0 0\nbt709 bt709 bt709 0 0\n0 4 0 4 4 2\n8 2 8 2 2 1\n10 2 10 2 2 1"
-- The page's layout puts U and V first: rows come from there.
#guard ((run 120 ["I420", "4", "2", "12", "4 4 0 2 2 2", "", "", "", ""]).splitOn "\n").drop 3 ==
  ["4 4 0 4 4 2", "0 2 8 2 2 1", "2 2 10 2 2 1"]
#guard run 120 ["I420", "4", "2", "11", "", "", "", "", ""] == "error -20"
#guard run 120 ["ABCD", "4", "2", "12", "", "", "", "", ""] == "error -20"
#guard run 120 ["RGBA", "4", "2", "32", "", "", "-", "", ""] == "error -20"
-- A rotation of 90.0 (its bytes) turns the display size.
#guard ((run 120 ["RGBA", "4", "2", "32", "", "", "", "", "1"] [(7, ⟨#[0, 0, 0, 0, 0, 0x80, 0x56, 0x40]⟩)]).splitOn "\n").take 3 ==
  ["32", "4 2 0 0 4 2 2 4 90 1", "bt709 iec61966-2-1 rgb 1 0"]
-- NaN is refused.
#guard run 120 ["RGBA", "4", "2", "32", "", "", "", "", ""] [(7, ⟨#[0, 0, 0, 0, 0, 0, 0xF8, 0x7F]⟩)] == "error -20"
#guard run 121 ["I420", "4 2 0 0 4 2 8 2 0 0", "2 0 2 2", "", "", ""] == "4 2 2 0 2 2 4 2 0 0"
#guard run 122 ["I420", "4", "2", "2 0 2 2", "", "6"] == "6\n2 4 0 2 2 2\n9 2 4 1 1 1\n11 2 5 1 1 1"
#guard run 122 ["I420", "4", "2", "", "", "11"] == "error -20"
#guard run 122 ["I420", "4", "2", "", "", ""] == "12\n0 4 0 4 4 2\n8 2 8 2 2 1\n10 2 10 2 2 1"
#guard run 123 ["I420A", "4", "2"] == "I420 12"
#guard run 123 ["RGBA", "4", "2"] == "RGBX 32"
#guard (op 124 #["RGBX".toUTF8, "1".toUTF8, "1".toUTF8, "".toUTF8, "BGRA".toUTF8, "".toUTF8, "".toUTF8, ⟨#[1, 2, 3, 0]⟩]).toOption.map (·.toList) ==
  some [3, 2, 1, 255]
#guard run 124 ["I420P10", "4", "2", "", "RGBA", "", "", ""] == "error -23"
#guard run 125 ["VideoDecoder", "vp8", "", ""] == "unsupported"
#guard run 125 ["VideoEncoder", "vp8", "width=640\nheight=0", ""] == "invalid"
#guard run 125 ["AudioEncoder", "opus", "sampleRate=8000\nnumberOfChannels=2\nopus.complexity=11", ""] == "invalid"
-- A 2 × 1 image turned a quarter: 1 wide, 2 high, the left pixel at the top.
#guard (op 126 #["90".toUTF8, "".toUTF8, "2".toUTF8, "1".toUTF8, ⟨#[1, 1, 1, 1, 2, 2, 2, 2]⟩]).toOption.map (·.toList) ==
  some [1, 1, 1, 1, 2, 2, 2, 2]
#guard (op 126 #["0".toUTF8, "1".toUTF8, "2".toUTF8, "1".toUTF8, ⟨#[1, 1, 1, 1, 2, 2, 2, 2]⟩]).toOption.map (·.toList) ==
  some [2, 2, 2, 2, 1, 1, 1, 1]
#guard run 126 ["0", "", "2", "1", "abc"] == "error -20"
-- 100 frames of f32-planar, 2 channels, at 8000 Hz (its double's bytes).
#guard run 127 ["f32-planar", "100", "2", "", "800"] [(3, ⟨#[0, 0, 0, 0, 0, 0x40, 0xBF, 0x40]⟩)] == "800 12500"
#guard run 127 ["f32-planar", "100", "2", "", "799"] [(3, ⟨#[0, 0, 0, 0, 0, 0x40, 0xBF, 0x40]⟩)] == "error -20"
#guard run 128 ["f32", "4", "2", "", "1", "0", ""] == "error -21"
#guard run 128 ["f32", "4", "2", "f32-planar", "1", "0", ""] == "4 16"
#guard run 128 ["f32", "4", "2", "x", "1", "0", ""] == "error -20"
#guard (op 129 #["u8".toUTF8, "2".toUTF8, "1".toUTF8, "s16".toUTF8, "0".toUTF8, "0".toUTF8, "".toUTF8, ⟨#[128, 255]⟩]).toOption.map (·.toList) ==
  some [0, 0, 0, 127]
#guard run 131 ["pcm-s24", "1", "abcdef"] == "s32 2"
#guard run 131 ["pcm-s24", "2", "abcdef"] == "s32 1"
#guard run 131 ["pcm-s24", "2", "abcde"] == "error -20"
#guard run 131 ["opus", "1", ""] == "error -20"
#guard (op 132 #["srgb".toUTF8, "display-p3".toUTF8, "".toUTF8, ⟨#[255, 0, 0, 9]⟩]).toOption.map (·.toList) == some [234, 51, 35, 9]
#guard run 132 ["srgb", "rec2020", "", ""] == "error -20"
#guard run 133 ["image/gif"] == "supported"
#guard run 133 ["image/webp"] == "unsupported"
#guard run 134 ["abc"] == "0 0"
#guard run 135 [] == "error -2"

end L4Factoidal.WebCodecs.Api
