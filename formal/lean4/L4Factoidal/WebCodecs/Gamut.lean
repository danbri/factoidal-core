/-
L4Factoidal.WebCodecs.Gamut: 8-bit colours between the predefined colour spaces of HTML and CSS
Color 4 (`srgb`, `display-p3`, `srgb-linear`, `display-p3-linear`), for `getImageData`,
`putImageData`, `ImageData` and `createImageBitmap` of a 2D canvas, and `VideoFrame.copyTo` with a
`colorSpace`. Record: docs/designissues/2026-11-14-webgl-webcodecs.md, section 4.

A canvas here keeps 8-bit sRGB; a colour space other than sRGB is a conversion where pixels enter
or leave. One conversion: decode each channel to linear light (16 bits: the sRGB transfer function
as the table `linTable`, the same for Display P3; a linear space by `v × 257`), multiply by the
3 × 3 matrix between the sRGB and Display P3 primaries (both D65) in units of 1/16384, rounded to
nearest, clamped, and encode (the transfer function's inverse: the count of midpoints below the
value, `thrTable`, which rounds in the encoded scale; a linear space by division by 257, rounded).
Alpha is kept.

The tables and the matrix coefficients come from the definitions (IEC 61966-2-1 and SMPTE
EG 432-1) computed once in double precision; the theorems below are about these numbers: decoding
then encoding gives every 8-bit value back (`encodeGamma_decode`, `encodeLinear_decode`), each
matrix row sums to 16384 so a grey stays the same grey (`gray_srgb_p3`, `gray_p3_srgb`), and the
encoded value is a byte (`encodeGamma_lt`).
-/
namespace L4Factoidal.WebCodecs.Gamut

def linTable : Array Nat := #[
  0, 20, 40, 60, 80, 99, 119, 139, 159, 179, 199, 219, 241, 264, 288, 313, 340, 367, 396, 427, 458,
  491, 526, 562, 599, 637, 677, 718, 761, 805, 851, 898, 947, 997, 1048, 1101, 1156, 1212, 1270, 1330,
  1391, 1453, 1517, 1583, 1651, 1720, 1790, 1863, 1937, 2013, 2090, 2170, 2250, 2333, 2418, 2504,
  2592, 2681, 2773, 2866, 2961, 3058, 3157, 3258, 3360, 3464, 3570, 3678, 3788, 3900, 4014, 4129,
  4247, 4366, 4488, 4611, 4736, 4864, 4993, 5124, 5257, 5392, 5530, 5669, 5810, 5953, 6099, 6246,
  6395, 6547, 6700, 6856, 7014, 7174, 7335, 7500, 7666, 7834, 8004, 8177, 8352, 8528, 8708, 8889,
  9072, 9258, 9445, 9635, 9828, 10022, 10219, 10417, 10619, 10822, 11028, 11235, 11446, 11658, 11873,
  12090, 12309, 12530, 12754, 12980, 13209, 13440, 13673, 13909, 14146, 14387, 14629, 14874, 15122,
  15371, 15623, 15878, 16135, 16394, 16656, 16920, 17187, 17456, 17727, 18001, 18277, 18556, 18837,
  19121, 19407, 19696, 19987, 20281, 20577, 20876, 21177, 21481, 21787, 22096, 22407, 22721, 23038,
  23357, 23678, 24002, 24329, 24658, 24990, 25325, 25662, 26001, 26344, 26688, 27036, 27386, 27739,
  28094, 28452, 28813, 29176, 29542, 29911, 30282, 30656, 31033, 31412, 31794, 32179, 32567, 32957,
  33350, 33745, 34143, 34544, 34948, 35355, 35764, 36176, 36591, 37008, 37429, 37852, 38278, 38706,
  39138, 39572, 40009, 40449, 40891, 41337, 41785, 42236, 42690, 43147, 43606, 44069, 44534, 45002,
  45473, 45947, 46423, 46903, 47385, 47871, 48359, 48850, 49344, 49841, 50341, 50844, 51349, 51858,
  52369, 52884, 53401, 53921, 54445, 54971, 55500, 56032, 56567, 57105, 57646, 58190, 58737, 59287,
  59840, 60396, 60955, 61517, 62082, 62650, 63221, 63795, 64372, 64952, 65535]

def thrTable : Array Nat := #[
  10, 30, 50, 70, 90, 109, 129, 149, 169, 189, 209, 230, 252, 276, 300, 326, 353, 382, 411, 442, 475,
  508, 543, 580, 618, 657, 697, 739, 783, 828, 874, 922, 971, 1022, 1075, 1129, 1184, 1241, 1300,
  1360, 1422, 1485, 1550, 1617, 1685, 1755, 1826, 1900, 1975, 2051, 2130, 2210, 2292, 2375, 2460,
  2547, 2636, 2727, 2819, 2914, 3010, 3107, 3207, 3309, 3412, 3517, 3624, 3733, 3844, 3957, 4071,
  4188, 4306, 4427, 4549, 4673, 4800, 4928, 5058, 5190, 5325, 5461, 5599, 5739, 5881, 6026, 6172,
  6320, 6471, 6623, 6778, 6935, 7093, 7254, 7417, 7582, 7750, 7919, 8090, 8264, 8440, 8618, 8798,
  8980, 9165, 9351, 9540, 9731, 9925, 10120, 10318, 10518, 10720, 10924, 11131, 11340, 11551, 11765,
  11981, 12199, 12419, 12642, 12867, 13094, 13324, 13556, 13790, 14027, 14266, 14508, 14751, 14998,
  15246, 15497, 15750, 16006, 16264, 16525, 16788, 17053, 17321, 17591, 17864, 18139, 18416, 18696,
  18979, 19264, 19551, 19841, 20134, 20429, 20726, 21026, 21329, 21634, 21941, 22251, 22564, 22879,
  23197, 23517, 23840, 24165, 24493, 24824, 25157, 25493, 25831, 26172, 26516, 26862, 27211, 27562,
  27916, 28273, 28632, 28994, 29359, 29726, 30096, 30469, 30844, 31222, 31603, 31986, 32372, 32761,
  33153, 33547, 33944, 34344, 34746, 35151, 35559, 35970, 36383, 36799, 37218, 37640, 38064, 38492,
  38922, 39354, 39790, 40228, 40670, 41114, 41560, 42010, 42463, 42918, 43376, 43837, 44301, 44768,
  45237, 45709, 46185, 46663, 47144, 47628, 48114, 48604, 49097, 49592, 50091, 50592, 51096, 51603,
  52113, 52626, 53142, 53661, 54183, 54707, 55235, 55766, 56299, 56836, 57375, 57918, 58463, 59012,
  59563, 60118, 60675, 61235, 61799, 62365, 62935, 63507, 64083, 64661, 65243]

inductive Space where
  | srgb | p3 | srgbLinear | p3Linear
  deriving DecidableEq, Repr, Inhabited

def Space.ofName? : String → Option Space
  | "srgb" => some .srgb | "display-p3" => some .p3
  | "srgb-linear" => some .srgbLinear | "display-p3-linear" => some .p3Linear
  | _ => none

def Space.linear : Space → Bool
  | .srgbLinear | .p3Linear => true
  | _ => false

/-- Display P3 primaries. -/
def Space.wide : Space → Bool
  | .p3 | .p3Linear => true
  | _ => false

/-- The count of midpoints in `thrTable[lo:hi]` below `x` (plus `lo`), by halving. -/
def search (x : Nat) : Nat → Nat → Nat → Nat
  | lo, _, 0 => lo
  | lo, hi, fuel + 1 =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if thrTable.getD mid 0 < x then search x (mid + 1) hi fuel else search x lo mid fuel
    else lo

/-- Linear light (0 to 65535) to an 8-bit value of the sRGB transfer function, rounded. -/
def encodeGamma (x : Nat) : Nat := search x 0 255 9

def decode (s : Space) (v : Nat) : Nat := if s.linear then v * 257 else linTable.getD v 0

def encode (s : Space) (x : Nat) : Nat := if s.linear then (x + 128) / 257 else encodeGamma x

/-- sRGB to Display P3 and back, linear light, in units of 1/16384. -/
def toP3 : List (List Int) := [[13475, 2909, 0], [544, 15840, 0], [280, 1186, 14918]]
def fromP3 : List (List Int) := [[20069, -3685, 0], [-689, 17073, 0], [-322, -1288, 17994]]

/-- One row of a matrix on linear light, rounded to nearest and clamped to 0..65535. -/
def row (m : List Int) (r g b : Nat) : Nat :=
  let s := m.getD 0 0 * r + m.getD 1 0 * g + m.getD 2 0 * b
  let x := (s + 8192) / 16384
  if x < 0 then 0 else if x > 65535 then 65535 else x.toNat

def convertPixel (src dst : Space) (r g b : Nat) : Nat × Nat × Nat :=
  let (r, g, b) := (decode src r, decode src g, decode src b)
  let (r, g, b) :=
    if src.wide == dst.wide then (r, g, b)
    else let m := if dst.wide then toP3 else fromP3
      (row (m.getD 0 []) r g b, row (m.getD 1 []) r g b, row (m.getD 2 []) r g b)
  (encode dst r, encode dst g, encode dst b)

/-- RGBA (or BGRA when `bgr`) pixels from `src` to `dst`; alpha as it is; a trailing partial
pixel is copied. The same space is no change (`convert_same`). -/
def convert (src dst : Space) (bgr : Bool) (px : ByteArray) : ByteArray :=
  if src == dst then px else Id.run do
    let mut out := px
    for i in [0:px.size / 4] do
      let o := 4 * i
      let (ri, bi) := if bgr then (o + 2, o) else (o, o + 2)
      let (r, g, b) := convertPixel src dst (px.get! ri).toNat (px.get! (o + 1)).toNat (px.get! bi).toNat
      out := ((out.set! ri (UInt8.ofNat r)).set! (o + 1) (UInt8.ofNat g)).set! bi (UInt8.ofNat b)
    return out

/-! ## Theorems -/

theorem convert_same (s : Space) (bgr : Bool) (px : ByteArray) : convert s s bgr px = px := by
  simp [convert]

set_option maxRecDepth 8000 in
/-- Round trip. Says: every 8-bit sRGB value decoded to linear light encodes back to itself. -/
theorem encodeGamma_decode : ∀ v : Fin 256, encodeGamma (linTable.getD v.val 0) = v.val := by decide

/-- Round trip. Says: the same for a linear space. -/
theorem encodeLinear_decode (v : Nat) (h : v < 256) : (v * 257 + 128) / 257 = v := by omega

theorem search_le (x : Nat) : ∀ (f lo hi : Nat), lo ≤ hi → search x lo hi f ≤ hi := by
  intro f
  induction f with
  | zero => intro lo hi h; simp only [search]; exact h
  | succ f ih =>
    intro lo hi h
    simp only [search]
    split
    · split
      · exact ih _ _ (by omega)
      · have := ih lo ((lo + hi) / 2) (by omega); omega
    · exact h

/-- Bounds. Says: an encoded value is a byte. -/
theorem encodeGamma_lt (x : Nat) : encodeGamma x < 256 := by
  have := search_le x 9 0 255 (by decide)
  unfold encodeGamma; omega

theorem toP3_rows : toP3.map (fun r => r.foldl (· + ·) 0) = [16384, 16384, 16384] := by decide
theorem fromP3_rows : fromP3.map (fun r => r.foldl (· + ·) 0) = [16384, 16384, 16384] := by decide

set_option maxRecDepth 8000 in
/-- Policy. Says: a grey (equal channels) is the same grey in sRGB and in Display P3, both ways:
the two spaces share the white point and the transfer function. -/
theorem gray_srgb_p3 : ∀ v : Fin 256, convertPixel .srgb .p3 v v v = (v.val, v.val, v.val) := by decide

set_option maxRecDepth 8000 in
theorem gray_p3_srgb : ∀ v : Fin 256, convertPixel .p3 .srgb v v v = (v.val, v.val, v.val) := by decide

/-! ## Tests (`html/canvas/.../wide-gamut-canvas/canvas-display-p3.js` expectations) -/

#guard convertPixel .srgb .p3 255 0 0 == (234, 51, 35)
#guard convertPixel .srgb .p3 187 0 0 == (171, 35, 23)
#guard convertPixel .p3 .srgb 187 0 0 == (205, 0, 0)
#guard convertPixel .p3 .srgb 234 51 35 == (255, 0, 0)
#guard convertPixel .srgb .srgbLinear 255 128 0 == (255, 55, 0)
#guard (convert .srgb .p3 true ⟨#[0, 0, 255, 7]⟩).toList == [35, 51, 234, 7]
#guard (convert .srgb .p3 false ⟨#[255, 0, 0, 7]⟩).toList == [234, 51, 35, 7]

end L4Factoidal.WebCodecs.Gamut
