/-
L4Factoidal.HTML.ImageSize — the natural size of an image from the first bytes of its file
(HTML §4.8.4.3 "the image's natural dimensions"), for `img.naturalWidth`/`naturalHeight`
and whether an image fetch is usable as an image (its `load` or `error` event).

Read without decoding pixels: PNG (the IHDR chunk), GIF (the logical screen), JPEG (the
first SOFn marker), WebP (VP8, VP8L, VP8X), BMP (the info header). Anything else is not an
image here (`none`), which the element treats as broken.

## What is proved

`size?_short`: fewer than 10 bytes are never an image. `size?_png`: a PNG is read as a PNG.
The headers of each type are checked by `#guard`s.
-/
namespace L4Factoidal.HTML.ImageSize

/-- Byte `i` (0 when past the end). -/
def at! (b : ByteArray) (i : Nat) : Nat := match b.data[i]? with | some v => v.toNat | none => 0

def be16 (b : ByteArray) (i : Nat) : Nat := at! b i * 256 + at! b (i + 1)
def be32 (b : ByteArray) (i : Nat) : Nat := be16 b i * 65536 + be16 b (i + 2)
def le16 (b : ByteArray) (i : Nat) : Nat := at! b i + at! b (i + 1) * 256
def le24 (b : ByteArray) (i : Nat) : Nat := le16 b i + at! b (i + 2) * 65536
def le32 (b : ByteArray) (i : Nat) : Nat := le16 b i + le16 b (i + 2) * 65536

/-- The bytes at `i` are `pat`. -/
def bytesAt (b : ByteArray) (i : Nat) (pat : List Nat) : Bool :=
  i + pat.length ≤ b.size && (pat.zipIdx.all fun (v, k) => at! b (i + k) == v)

def png (b : ByteArray) : Option (Nat × Nat) :=
  if bytesAt b 0 [0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A] && bytesAt b 12 [0x49, 0x48, 0x44, 0x52] && b.size ≥ 24
  then some (be32 b 16, be32 b 20) else none

def gif (b : ByteArray) : Option (Nat × Nat) :=
  if (bytesAt b 0 [0x47, 0x49, 0x46, 0x38, 0x37, 0x61] || bytesAt b 0 [0x47, 0x49, 0x46, 0x38, 0x39, 0x61]) && b.size ≥ 10
  then some (le16 b 6, le16 b 8) else none

def bmp (b : ByteArray) : Option (Nat × Nat) :=
  if bytesAt b 0 [0x42, 0x4D] && b.size ≥ 26 then
    let h := le32 b 22
    -- a top-down bitmap stores a negative height
    some (le32 b 18, if h ≥ 2147483648 then 4294967296 - h else h)
  else none

/-- JPEG: the segments after SOI up to the first start-of-frame (SOF0 to SOF15 but DHT, JPG
and DAC). -/
def jpeg (b : ByteArray) : Option (Nat × Nat) := Id.run do
  if !bytesAt b 0 [0xFF, 0xD8] then return none
  let mut i := 2
  for _ in [0:b.size] do
    if i + 9 > b.size then return none
    if at! b i != 0xFF then return none
    let m := at! b (i + 1)
    if m == 0xFF then i := i + 1; continue
    if 0xC0 ≤ m && m ≤ 0xCF && m != 0xC4 && m != 0xC8 && m != 0xCC then
      return some (be16 b (i + 7), be16 b (i + 5))
    if m == 0xD8 || m == 0x01 || (0xD0 ≤ m && m ≤ 0xD7) then i := i + 2; continue
    let len := be16 b (i + 2)
    if len < 2 then return none
    i := i + 2 + len
  return none

def webp (b : ByteArray) : Option (Nat × Nat) :=
  if !(bytesAt b 0 [0x52, 0x49, 0x46, 0x46] && bytesAt b 8 [0x57, 0x45, 0x42, 0x50]) then none
  else if bytesAt b 12 [0x56, 0x50, 0x38, 0x20] && b.size ≥ 30 then
    some (le16 b 26 % 16384, le16 b 28 % 16384)
  else if bytesAt b 12 [0x56, 0x50, 0x38, 0x4C] && b.size ≥ 25 then
    let v := le32 b 21
    some (v % 16384 + 1, (v / 16384) % 16384 + 1)
  else if bytesAt b 12 [0x56, 0x50, 0x38, 0x58] && b.size ≥ 30 then
    some (le24 b 24 + 1, le24 b 27 + 1)
  else none

/-- The natural size of an image file, or `none` when the bytes are not one of these types. -/
def size? (b : ByteArray) : Option (Nat × Nat) :=
  if b.size < 10 then none else
  png b <|> gif b <|> jpeg b <|> webp b <|> bmp b

/-- A PNG header of `w` by `h`: the signature, the IHDR length and type, the size. -/
def pngHeader (w h : Nat) : ByteArray :=
  ⟨#[0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A, 0, 0, 0, 13, 0x49, 0x48, 0x44, 0x52,
     0, 0, (w / 256).toUInt8, (w % 256).toUInt8, 0, 0, (h / 256).toUInt8, (h % 256).toUInt8, 8, 6, 0, 0, 0]⟩

/-- A GIF header of `w` by `h`. -/
def gifHeader (w h : Nat) : ByteArray :=
  ⟨#[0x47, 0x49, 0x46, 0x38, 0x39, 0x61, (w % 256).toUInt8, (w / 256).toUInt8, (h % 256).toUInt8, (h / 256).toUInt8, 0, 0, 0]⟩

/-! ## Examples -/

#guard size? (pngHeader 300 150) == some (300, 150)
#guard size? (gifHeader 1 1) == some (1, 1)
#guard size? ⟨#[0xFF, 0xD8, 0xFF, 0xE0, 0, 16, 0x4A, 0x46, 0x49, 0x46, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0,
  0xFF, 0xC0, 0, 17, 8, 0, 20, 0, 40, 3, 1, 0x22, 0, 2, 0x11, 1, 3, 0x11, 1]⟩ == some (40, 20)
#guard size? "not an image at all".toUTF8 == none
#guard size? ⟨#[0x42, 0x4D, 0, 0, 0, 0, 0, 0, 0, 0, 54, 0, 0, 0, 40, 0, 0, 0, 7, 0, 0, 0, 0xFB, 0xFF, 0xFF, 0xFF]⟩ == some (7, 5)

/-! ## Theorems -/

/-- Kind: correctness theorem. Says: fewer than 10 bytes are never an image. -/
theorem size?_short (b : ByteArray) (h : b.size < 10) : size? b = none := by
  simp [size?, h]

/-- Kind: correctness theorem. Says: the size of an image is that of the first type whose
signature the bytes have, PNG first: a file that is a PNG is never read as another type. -/
theorem size?_png (b : ByteArray) (h : b.size ≥ 10) (p : Nat × Nat) (hp : png b = some p) : size? b = some p := by
  have : ¬ b.size < 10 := by omega
  simp [size?, this, hp]

end L4Factoidal.HTML.ImageSize
