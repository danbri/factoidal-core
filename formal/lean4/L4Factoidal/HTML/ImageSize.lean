import L4Factoidal.DOM.OfXml
/-
L4Factoidal.HTML.ImageSize — the natural size of an image from the first bytes of its file
(HTML §4.8.4.3 "the image's natural dimensions"), for `img.naturalWidth`/`naturalHeight`
and whether an image fetch is usable as an image (its `load` or `error` event).

Read without decoding pixels: PNG (the IHDR chunk), GIF (the logical screen), JPEG (the
first SOFn marker), WebP (VP8, VP8L, VP8X), BMP (the info header). An answer of type
`image/svg+xml` is an SVG document (`svg?`): its natural size comes from the root `svg`
element's `width`, `height` and `viewBox` and the default object size (CSS Images 3 §4.1).
Anything else is not an image here (`none`), which the element treats as broken.

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

/-! ## SVG images (HTML §4.8.4.3, SVG 2 §8.2, CSS Images 3 §4.1) -/

private def natOfDigits (ds : List Char) : Nat := ds.foldl (fun k c => k * 10 + (c.toNat - 48)) 0

/-- A number at the start of `cs` (CSS Syntax: sign, digits, fraction, exponent) and what
follows it. An `e` with no digits after it is not an exponent (`1em` is 1 and `em`). -/
def number? (cs : List Char) : Option (Float × List Char) :=
  let (neg, cs) := match cs with | '-' :: r => (true, r) | '+' :: r => (false, r) | r => (false, r)
  let ip := cs.takeWhile Char.isDigit
  let cs := cs.dropWhile Char.isDigit
  let (fp, cs) := match cs with
    | '.' :: r => if (r.takeWhile Char.isDigit).isEmpty then ([], cs) else (r.takeWhile Char.isDigit, r.dropWhile Char.isDigit)
    | r => ([], r)
  if ip.isEmpty && fp.isEmpty then none else
  let (ex, cs) : Int × List Char := match cs with
    | c :: r =>
      if c == 'e' || c == 'E' then
        let (eneg, r2) := match r with | '-' :: q => (true, q) | '+' :: q => (false, q) | q => (false, q)
        let ed := r2.takeWhile Char.isDigit
        if ed.isEmpty || ed.length > 4 then (0, cs) else ((if eneg then -1 else 1) * (natOfDigits ed : Int), r2.dropWhile Char.isDigit)
      else (0, cs)
    | [] => (0, [])
  let m := natOfDigits (ip ++ fp)
  let k : Int := ex - fp.length
  let v := if k ≥ 0 then Float.ofScientific m false k.toNat else Float.ofScientific m true (-k).toNat
  some (if neg then -v else v, cs)

/-- The length of an SVG root's `width` or `height` in CSS pixels when it is a natural size: a
number, alone or with an absolute unit (CSS Values 4 §6.2: `px`, `in`, `cm`, `mm`, `Q`, `pt`,
`pc`), not negative. A percentage, `auto`, a relative unit or anything else is none: the
image has no natural size on that axis. -/
def svgLength? (s : String) : Option Float := do
  let cs := (s.toList.dropWhile Char.isWhitespace).reverse.dropWhile Char.isWhitespace |>.reverse
  let (v, rest) ← number? cs
  let unit := String.ofList (rest.map Char.toLower)
  let scale ← match unit with
    | "" | "px" => some 1 | "in" => some 96 | "cm" => some (96 / 2.54) | "mm" => some (96 / 25.4)
    | "q" => some (96 / 101.6) | "pt" => some (4 / 3) | "pc" => some 16 | _ => none
  if v < 0 then none else some (v * scale)

/-- The width and height of a `viewBox` (four numbers, white space or commas between). -/
def viewBoxSize? (s : String) : Option (Float × Float) :=
  let parts := (s.toList.map fun c => if c == ',' || c.isWhitespace then ' ' else c)
    |> String.ofList |>.splitOn " " |>.filter (· != "")
  match parts.map fun p => (number? p.toList).bind fun (v, r) => if r.isEmpty then some v else none with
  | [some _, some _, some w, some h] => some (w, h)
  | _ => none

/-- The size an SVG image has for its element (CSS Images 3 §4.1, the default sizing
algorithm with no specified size, on a 300 by 150 default object size): a natural width and
height as they are; one of them with the `viewBox`'s ratio gives the other, without a ratio
the default's; a ratio alone fits in 300 by 150 (`contain`); nothing gives 300 by 150. A
`viewBox` with a zero or negative side gives no ratio. -/
def svgNatural (w h : Option Float) (vb : Option (Float × Float)) : Float × Float :=
  let r := vb.bind fun (a, b) => if a > 0 && b > 0 then some (a / b) else none
  match w, h, r with
  | some w, some h, _ => (w, h)
  | some w, none, some r => (w, w / r)
  | none, some h, some r => (h * r, h)
  | some w, none, none => (w, 150)
  | none, some h, none => (300, h)
  | none, none, some r => if r ≥ 2 then (300, 300 / r) else (150 * r, 150)
  | none, none, none => (300, 150)

/-- Most bytes of an SVG image read for its size (larger ones are read by the page's
renderer, which has its own limit, and are broken here). -/
def maxSvgBytes : Nat := 4194304

/-- A whole number of CSS pixels for a size (`naturalWidth` is an `unsigned long`). -/
def wholePx (v : Float) : Nat := if v.isNaN || v ≤ 0 then 0 else if v ≥ 1.0e9 then 1000000000 else v.round.toUInt64.toNat

/-- The natural size of an SVG image file: a well-formed XML document whose root element is
`svg` in the SVG namespace; none for anything else (the element is then broken). -/
def svg? (b : ByteArray) : Option (Nat × Nat) := do
  if b.size > maxSvgBytes then none
  let text ← String.fromUTF8? b
  let d ← (DOM.parseXmlDocument text).toOption
  let root ← (d.get 0).kids.find? fun k => (d.get k).type == .element
  let n := d.get root
  if n.ns != some DOM.svgNS || n.lname != "svg" then none
  let attr := fun (name : String) => (n.attrs.find? fun a => a.ns.isNone && a.lname == name).map (·.value)
  let (w, h) := svgNatural ((attr "width").bind svgLength?) ((attr "height").bind svgLength?) ((attr "viewBox").bind viewBoxSize?)
  some (wholePx w, wholePx h)

/-- The essence of a MIME type (MIME Sniffing §4.1): before any `;`, without white space, in
ASCII lower case. -/
def essence (t : String) : String :=
  String.ofList (((t.toList.takeWhile (· != ';')).filter fun c => !c.isWhitespace).map Char.toLower)

/-- The natural size of an image answer of MIME type `contentType`: an SVG document for
`image/svg+xml` (an SVG image is never sniffed from its bytes, HTML §4.8.4.3 "image type
sniffing"), else the raster types by their signatures (`size?`). -/
def natural (contentType : String) (b : ByteArray) : Option (Nat × Nat) :=
  if essence contentType == "image/svg+xml" then svg? b else size? b

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
-- SVG images: the cases of WPT the-img-element/naturalWidth-naturalHeight-width-height
private def svgOf (attrs : String) : ByteArray := ("<svg xmlns='http://www.w3.org/2000/svg'" ++ attrs ++ "></svg>").toUTF8
#guard natural "image/svg+xml" (svgOf "") == some (300, 150)
#guard natural "Image/SVG+XML; charset=utf-8" (svgOf " width='60'") == some (60, 150)
#guard natural "image/svg+xml" (svgOf " height='60'") == some (300, 60)
#guard natural "image/svg+xml" (svgOf " width='0'") == some (0, 150)
#guard natural "image/svg+xml" (svgOf " width='-5'") == some (300, 150)
#guard natural "image/svg+xml" (svgOf " width='400%' height='10%'") == some (300, 150)
#guard natural "image/svg+xml" (svgOf " viewBox='0 0 600 200'") == some (300, 100)
#guard natural "image/svg+xml" (svgOf " width='60' viewBox='0 0 600 200'") == some (60, 20)
#guard natural "image/svg+xml" (svgOf " height='60' viewBox='0 0 600 200'") == some (180, 60)
#guard natural "image/svg+xml" (svgOf " width='0' viewBox='0 0 600 200'") == some (0, 0)
#guard natural "image/svg+xml" (svgOf " viewBox='0 0 10 0'") == some (300, 150)
#guard natural "image/svg+xml" (svgOf " width='60' height='40' viewBox='0 0 600 200'") == some (60, 40)
#guard natural "image/svg+xml" (svgOf " width='1in' height='2em'") == some (96, 150)
#guard natural "image/svg+xml" (svgOf " viewBox='0,0,100,200'") == some (75, 150)
-- not SVG: another root, not XML, or not of the SVG type
#guard natural "image/svg+xml" "<html xmlns='http://www.w3.org/1999/xhtml'/>".toUTF8 == none
#guard natural "image/svg+xml" "<svg xmlns='http://www.w3.org/2000/svg'>".toUTF8 == none
#guard natural "image/png" (svgOf "") == none
#guard natural "image/png" (pngHeader 3 5) == some (3, 5)
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

/-- Kind: correctness theorem. Says: an answer that is not of type `image/svg+xml` is read by
its raster signature alone, as before SVG images were read. -/
theorem natural_raster (t : String) (b : ByteArray) (h : (essence t == "image/svg+xml") = false) :
    natural t b = size? b := by
  simp [natural, h]

/-- Kind: bound. Says: the natural size of an SVG image with a natural width and height is
those, whatever its `viewBox`. -/
theorem svgNatural_both (w h : Float) (vb : Option (Float × Float)) : svgNatural (some w) (some h) vb = (w, h) := by
  simp [svgNatural]

end L4Factoidal.HTML.ImageSize
