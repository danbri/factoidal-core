/-
L4Factoidal.WebCodecs.Convert: pixel format conversions of video frames (WebCodecs §9.4.5 `copyTo`
with a `format`, §9.8; ITU-R BT.601, BT.709 and BT.2020 for the matrices). Record:
docs/designissues/2026-11-14-webgl-webcodecs.md, section 4.

Two kinds:

  * Re-orderings that lose nothing. Each is a map from a byte position of the output to the byte
    position of the input it copies (`swapRB`: RGBA and BGRA; `nv12Src` and `i420Src`: the chroma
    planes of I420 and the interleaved plane of NV12). The round trips are theorems about these
    maps: `swapRB_involutive`, `nv12_i420_roundtrip`, `i420_nv12_roundtrip`.
  * Y'CbCr to R'G'B' (`yuvToRgb`), which rounds: exact integer arithmetic on the matrix
    coefficients in ten-thousandths, the result rounded to nearest and clamped. Tested against
    the Web Platform Tests' colours; nothing is proved about its values beyond their range
    (a `UInt8` each).

No conversion changes primaries or transfer characteristics: a frame's R'G'B' values are answered
as they are for an sRGB destination (the record lists this as open).
-/
import L4Factoidal.WebCodecs.Layout

namespace L4Factoidal.WebCodecs

/-! ## Re-orderings -/

/-- The input byte that output byte `i` of an RGBA ↔ BGRA conversion copies: bytes 0 and 2 of each
pixel change places. -/
def swapRB (i : Nat) : Nat :=
  if i % 4 = 0 then i + 2 else if i % 4 = 2 then i - 2 else i

/-- The I420 byte that byte `p` of an NV12 frame copies, for `n` luma bytes and `c` bytes in each
chroma plane: luma as it is; then U and V samples in turn. -/
def nv12Src (n c p : Nat) : Nat :=
  if p < n then p else if (p - n) % 2 = 0 then n + (p - n) / 2 else n + c + (p - n) / 2

/-- The NV12 byte that byte `q` of an I420 frame copies. -/
def i420Src (n c q : Nat) : Nat :=
  if q < n then q else if q < n + c then n + 2 * (q - n) else n + 2 * (q - n - c) + 1

/-- The bytes of `src` re-ordered: output byte `i` is input byte `f i` (0 for a position outside
the input, which the theorems below rule out for the maps used). -/
def permute (src : ByteArray) (size : Nat) (f : Nat → Nat) : ByteArray :=
  ⟨Array.ofFn (n := size) fun i => src.get! (f i.val)⟩

/-- Round trip, lossless. Says: RGBA to BGRA and back (or the reverse) copies every byte to where
it was: the map is its own inverse. -/
theorem swapRB_involutive (i : Nat) : swapRB (swapRB i) = i := by
  unfold swapRB
  repeat' split
  all_goals omega

/-- Bounds. Says: within a buffer of whole pixels, the byte `swapRB` reads is inside the buffer. -/
theorem swapRB_lt (i size : Nat) (h4 : size % 4 = 0) (h : i < size) : swapRB i < size := by
  unfold swapRB
  repeat' split
  all_goals omega

/-- Round trip, lossless. Says: I420 to NV12 and back gives each I420 byte its own value: byte `q`
of the result copies NV12 byte `i420Src q`, which copied I420 byte `q`. -/
theorem nv12_i420_roundtrip (n c q : Nat) : nv12Src n c (i420Src n c q) = q := by
  unfold nv12Src i420Src
  repeat' split
  all_goals omega

/-- Round trip, lossless. Says: NV12 to I420 and back gives each NV12 byte its own value. -/
theorem i420_nv12_roundtrip (n c p : Nat) (h : p < n + 2 * c) : i420Src n c (nv12Src n c p) = p := by
  unfold nv12Src i420Src
  repeat' split
  all_goals omega

/-- Bounds. Says: both maps read inside a frame of `n + 2c` bytes. -/
theorem nv12Src_lt (n c p : Nat) (h : p < n + 2 * c) : nv12Src n c p < n + 2 * c := by
  unfold nv12Src
  repeat' split
  all_goals omega

theorem i420Src_lt (n c q : Nat) (h : q < n + 2 * c) : i420Src n c q < n + 2 * c := by
  unfold i420Src
  repeat' split
  all_goals omega

/-! ## Y'CbCr to R'G'B' -/

/-- `VideoMatrixCoefficients`: the luma weights of red and blue, in ten-thousandths (BT.601 for
`smpte170m` and `bt470bg`, BT.2020, BT.709). -/
def matrixKrKb : String → Int × Int
  | "smpte170m" | "bt470bg" => (2990, 1140)
  | "bt2020-ncl" => (2627, 593)
  -- BT.709, and the default of a frame that names no matrix (§9.4.6 "Pick Color Space").
  | _ => (2126, 722)

/-- `a / b` rounded to nearest (a half up), for `b > 0`. -/
def divRound (a b : Int) : Int := (2 * a + b) / (2 * b)

def clamp8 (v : Int) : UInt8 := UInt8.ofNat (max 0 (min 255 v)).toNat

/-- One pixel: 8-bit Y', Cb, Cr to 8-bit R', G', B', with the matrix `(kr, kb)` and the range
(limited: luma 16 to 235, chroma 16 to 240). Exact arithmetic over a common denominator, rounded
once at the end. -/
def yuvToRgb (kr kb : Int) (full : Bool) (y u v : Nat) : UInt8 × UInt8 × UInt8 :=
  let kg := 10000 - kr - kb
  -- Luma and chroma in units of 1/(219 * 224) (limited) or 1 (full), times 255 where scaled.
  let (yn, cbn, crn, d) : Int × Int × Int × Int :=
    if full then ((y : Int), (u : Int) - 128, (v : Int) - 128, 1)
    else (((y : Int) - 16) * 255 * 224, ((u : Int) - 128) * 255 * 219, ((v : Int) - 128) * 255 * 219, 219 * 224)
  -- R = Y + 2(1 - Kr) Cr; B = Y + 2(1 - Kb) Cb; G = Y - (2 Kb (1 - Kb) Cb + 2 Kr (1 - Kr) Cr) / Kg.
  let r := divRound (yn * 10000 + 2 * (10000 - kr) * crn) (10000 * d)
  let b := divRound (yn * 10000 + 2 * (10000 - kb) * cbn) (10000 * d)
  let g := divRound (yn * 10000 * kg - 2 * kb * (10000 - kb) * cbn - 2 * kr * (10000 - kr) * crn) (10000 * kg * d)
  (clamp8 r, clamp8 g, clamp8 b)

/-- A frame's rectangle as packed pixels of an RGB format (`dst`): the bytes `copyTo` then lays
out. `src` is the frame's resource (`resourceSize` bytes of `f` at `cw` × `ch`). 8-bit formats only;
`none` for a format this does not convert (10 and 12-bit) or a resource of the wrong size. -/
def toRgb (f : PixelFormat) (cw ch : Nat) (rect : Rect) (src : ByteArray) (dst : PixelFormat) (matrix : String)
    (full : Bool) : Option ByteArray :=
  if src.size != resourceSize f cw ch || !dst.isRgb || !rectOk f.planes cw ch rect then none else
  let bgr := dst == .bgra || dst == .bgrx
  let keepAlpha := dst.hasAlpha
  let put := fun (out : ByteArray) (r g b a : UInt8) =>
    let out := if bgr then (out.push b).push g |>.push r else (out.push r).push g |>.push b
    out.push (if keepAlpha then a else 255)
  let (kr, kb) := matrixKrKb matrix
  match f with
  | .rgba | .rgbx | .bgra | .bgrx =>
    let srcBgr := f == .bgra || f == .bgrx
    let srcAlpha := f.hasAlpha
    some <| Id.run do
      let mut out := ByteArray.emptyWithCapacity (rect.width * rect.height * 4)
      for y in [rect.y:rect.y + rect.height] do
        for x in [rect.x:rect.x + rect.width] do
          let i := (y * cw + x) * 4
          let (r, b) := if srcBgr then (src.get! (i + 2), src.get! i) else (src.get! i, src.get! (i + 2))
          out := put out r (src.get! (i + 1)) b (if srcAlpha then src.get! (i + 3) else 255)
      return out
  | .yuv c alpha .d8 =>
    let sw := match c with | .c444 => 1 | _ => 2
    let sh := match c with | .c420 => 2 | _ => 1
    let cwid := ceilDiv cw sw
    let chgt := ceilDiv ch sh
    let uOff := cw * ch
    let vOff := uOff + cwid * chgt
    let aOff := vOff + cwid * chgt
    some <| Id.run do
      let mut out := ByteArray.emptyWithCapacity (rect.width * rect.height * 4)
      for y in [rect.y:rect.y + rect.height] do
        for x in [rect.x:rect.x + rect.width] do
          let ci := (y / sh) * cwid + x / sw
          let (r, g, b) := yuvToRgb kr kb full (src.get! (y * cw + x)).toNat (src.get! (uOff + ci)).toNat (src.get! (vOff + ci)).toNat
          out := put out r g b (if alpha then src.get! (aOff + y * cw + x) else 255)
      return out
  | .nv12 =>
    let cwid := ceilDiv cw 2
    let uvOff := cw * ch
    some <| Id.run do
      let mut out := ByteArray.emptyWithCapacity (rect.width * rect.height * 4)
      for y in [rect.y:rect.y + rect.height] do
        for x in [rect.x:rect.x + rect.width] do
          let ci := uvOff + ((y / 2) * cwid + x / 2) * 2
          let (r, g, b) := yuvToRgb kr kb full (src.get! (y * cw + x)).toNat (src.get! ci).toNat (src.get! (ci + 1)).toNat
          out := put out r g b 255
      return out
  | _ => none

/-! ## Tests (`webcodecs/videoFrame-copyTo-rgb.any.js`: the colours its `rgb2yuv` makes) -/

private def rgb (kr kb : Int) (full : Bool) (y u v : Nat) : Nat × Nat × Nat :=
  let (r, g, b) := yuvToRgb kr kb full y u v
  (r.toNat, g.toNat, b.toNat)
/-- |a - b| ≤ 1 on each channel. -/
private def near (a b : Nat × Nat × Nat) : Bool :=
  let d := fun (x y : Nat) => (x - y) + (y - x) ≤ 1
  d a.1 b.1 && d a.2.1 b.2.1 && d a.2.2 b.2.2

-- BT.709 limited: yellow, red, blue, green, magenta, black, white, pink.
#guard near (rgb 2126 722 false 219 16 138) (255, 255, 0)
#guard near (rgb 2126 722 false 63 102 240) (255, 0, 0)
#guard near (rgb 2126 722 false 32 240 118) (0, 0, 255)
#guard near (rgb 2126 722 false 173 42 26) (0, 255, 0)
#guard near (rgb 2126 722 false 78 214 230) (255, 0, 255)
#guard rgb 2126 722 false 16 128 128 == (0, 0, 0)
#guard rgb 2126 722 false 235 128 128 == (255, 255, 255)
#guard near (rgb 2126 722 false 152 174 182) (255, 120, 255)
-- BT.601 limited: red is (81, 90, 240); full range red is (76, 85, 255).
#guard near (rgb 2990 1140 false 81 90 240) (255, 0, 0)
#guard near (rgb 2990 1140 true 76 85 255) (255, 0, 0)
#guard near (rgb 2990 1140 false 145 54 34) (0, 255, 0)
private def bytes (xs : List Nat) : ByteArray := ⟨(xs.map (·.toUInt8)).toArray⟩
-- RGBX 2 × 1 to BGRA: the channels change places, padding becomes opaque alpha.
#guard ((toRgb .rgbx 2 1 ⟨0, 0, 2, 1⟩ (bytes [1, 2, 3, 0, 5, 6, 7, 0]) .bgra "rgb" true).map (·.toList.map (·.toNat))) ==
  some [3, 2, 1, 255, 7, 6, 5, 255]
-- RGBA to RGBX: alpha is not kept.
#guard ((toRgb .rgba 1 1 ⟨0, 0, 1, 1⟩ (bytes [9, 8, 7, 6]) .rgbx "rgb" true).map (·.toList.map (·.toNat))) == some [9, 8, 7, 255]
-- I420 4 × 2, limited BT.709 white: every pixel white, opaque.
#guard ((toRgb (.yuv .c420 false .d8) 4 2 ⟨0, 0, 4, 2⟩ (bytes ((List.replicate 8 235) ++ [128, 128, 128, 128])) .rgba "bt709" false).map
  (·.toList.map (·.toNat))) == some ((List.replicate 8 [255, 255, 255, 255]).flatten)
-- A crop of an I420 frame: 2 × 2 of the right half.
#guard ((toRgb (.yuv .c420 false .d8) 4 2 ⟨2, 0, 2, 2⟩ (bytes ((List.replicate 8 16) ++ [128, 128, 128, 128])) .rgbx "bt709" false).map (·.size)) == some 16
#guard (toRgb (.yuv .c420 false .d10) 4 2 ⟨0, 0, 4, 2⟩ (bytes (List.replicate 24 0)) .rgba "bt709" false).isNone
#guard (toRgb .rgba 2 2 ⟨0, 0, 2, 2⟩ (bytes [1, 2, 3]) .rgba "rgb" true).isNone
#guard matrixKrKb "smpte170m" == (2990, 1140)
#guard matrixKrKb "" == (2126, 722)
-- The re-ordering maps on a whole buffer: I420 to NV12 and back.
#guard (permute (permute (bytes [1, 2, 3, 4, 9, 10, 11, 12]) 8 (nv12Src 4 2)) 8 (i420Src 4 2)).toList.map (·.toNat) == [1, 2, 3, 4, 9, 10, 11, 12]
#guard (permute (bytes [1, 2, 3, 4, 9, 10, 11, 12]) 8 (nv12Src 4 2)).toList.map (·.toNat) == [1, 2, 3, 4, 9, 11, 10, 12]
#guard (permute (bytes [1, 2, 3, 4, 5, 6, 7, 8]) 8 swapRB).toList.map (·.toNat) == [3, 2, 1, 4, 7, 6, 5, 8]

end L4Factoidal.WebCodecs
