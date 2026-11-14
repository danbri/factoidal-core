import ImageJPEG
import ImageGIF
import Std.Data.HashMap

/- Raster image sources of a document.

   The strict reader runs many times for one document (`SVGForgiving.repair`), so
   decoding happens once, here, into a store keyed by the `xlink:href` text. A host
   gives the bytes of external references; a `data:` URI needs no host. -/
namespace NativeImage

open L4Factoidal.Rendering (Bitmap)

/-- Limit on the decoded pixels of one document: the paint table has one word for
    each pixel, and `NativeSVG.maxPaintTableWords` is the same number. -/
def maxDocumentPixels : Nat := 1048576

/-- A decoded image, or the refusal that names why it is not one. -/
abbrev Entry := Except String (Nat × Bitmap)
abbrev Store := Std.HashMap String Entry

/-- The format comes from the bytes, as for a browser; the media type does not change it. -/
def decode (bytes : ByteArray) : Except String Bitmap :=
  if bytes.size >= 2 && bytes.get! 0 == 0xFF && bytes.get! 1 == 0xD8 then decodeJPEG bytes
  else if bytes.size >= 8 && bytes.get! 0 == 137 && bytes.get! 1 == 80 then decodePNG bytes
  else if bytes.size >= 6 && bytes.get! 0 == 71 && bytes.get! 1 == 73 && bytes.get! 2 == 70 then decodeGIF bytes
  else .error "image is not PNG, JPEG or GIF"

private def base64Value (c : UInt8) : Option Nat :=
  if c >= 65 && c <= 90 then some (c.toNat-65)
  else if c >= 97 && c <= 122 then some (c.toNat-71)
  else if c >= 48 && c <= 57 then some (c.toNat+4)
  else if c == 43 then some 62
  else if c == 47 then some 63
  else none

/-- RFC 4648 §4. XML white space is skipped; anything else after the padding, or
    outside the alphabet, is a refusal. -/
def base64 (text : ByteArray) (start : Nat) : Except String ByteArray := do
  let mut out := ByteArray.emptyWithCapacity (text.size/4*3+3)
  let mut value := 0
  let mut bits := 0
  let mut ended := false
  for i in [start:text.size] do
    let c := text.get! i
    if c == 32 || c == 9 || c == 10 || c == 13 then continue
    if c == 61 then ended := true; continue
    if ended then throw "base64 data follows its padding"
    let some digit := base64Value c | throw "data URI is not valid base64"
    value := value*64+digit
    bits := bits+6
    if bits >= 8 then
      bits := bits-8
      out := out.push (value >>> bits).toUInt8
      value := value%(1 <<< bits)
  return out

/-- RFC 2397, with the base64 form only. -/
def dataBytes (href : String) : Except String ByteArray := do
  let bytes := href.toUTF8
  let some comma := (List.range bytes.size).find? (fun i => bytes.get! i == 44)
    | throw "data URI has no comma"
  let header := (String.fromUTF8? (bytes.extract 0 comma)).getD ""
  if !(header.toLower.endsWith ";base64") then throw "data URI is not base64"
  base64 bytes (comma+1)

/-! ### Images held at a reduced size (2026-11-14)

A document's images share one budget of pixels (`maxDocumentPixels`, the paint table of a
scene). A page of photographs passes it: lean-lang.org's nine screenshots have 3.1 million
pixels, and each image past the budget showed its `alt` text. When the images of a document
have more pixels than the budget, each image above `smallPixels` is held reduced by one
factor `k` for the document (`factorFor`): a pixel of the held bitmap is the mean of a `k`
by `k` block (`reduce`). Layout still takes the image's own size (`Store.natural`), so the
page is laid out as with the whole image; the picture is drawn softer. A document whose
images fit the budget takes none of this (`factorFor_fits_one`). -/

/-- An image of at most this many pixels is never reduced (icons, rules, spacers). -/
def smallPixels : Nat := 4096

/-- The largest reduction factor: an image is held with at least 1/256 of its pixels. -/
def maxFactor : Nat := 16

/-- The size of an image of `w` by `h` held at factor `k`: each side divided by `k`, rounded
up. An image of at most `smallPixels` keeps its size. -/
def reducedSize (w h k : Nat) : Nat × Nat :=
  if k ≤ 1 || w*h ≤ smallPixels then (w,h) else ((w+k-1)/k,(h+k-1)/k)

/-- The pixels that images of `sizes` take when held at factor `k`. -/
def heldPixels (sizes : List (Nat × Nat)) (k : Nat) : Nat :=
  sizes.foldl (fun n (w,h) => n + (reducedSize w h k).1*(reducedSize w h k).2) 0

/-- The factor for a document whose images have `sizes`: the smallest of 1 to `maxFactor`
at which they fit `budget`, else `maxFactor` (the images past the budget are then refused,
as before). -/
def factorFor (sizes : List (Nat × Nat)) (budget : Nat := maxDocumentPixels) : Nat :=
  ((List.range maxFactor).map (· + 1)).find? (fun k => heldPixels sizes k ≤ budget) |>.getD maxFactor

/-- The factor is at least 1 and at most `maxFactor`. -/
theorem factorFor_bounds (sizes : List (Nat × Nat)) (budget : Nat) :
    1 ≤ factorFor sizes budget ∧ factorFor sizes budget ≤ maxFactor := by
  unfold factorFor
  cases h : ((List.range maxFactor).map (· + 1)).find? (fun k => heldPixels sizes k ≤ budget) with
  | none => simp [maxFactor]
  | some k =>
    have mem := List.mem_of_find?_eq_some h
    simp only [List.mem_map, List.mem_range] at mem
    obtain ⟨i, hi, rfl⟩ := mem
    have hi' : i < 16 := hi
    show 1 ≤ i+1 ∧ i+1 ≤ 16
    omega

/-- Images that fit the budget as they are, are held as they are: factor 1. -/
theorem factorFor_fits_one (sizes : List (Nat × Nat)) (budget : Nat) (h : heldPixels sizes 1 ≤ budget) :
    factorFor sizes budget = 1 := by
  unfold factorFor
  have : (List.range maxFactor).map (· + 1) = 1 :: ((List.range (maxFactor-1)).map (· + 2)) := by decide
  rw [this, List.find?_cons]
  simp [h]

/-- When some factor up to `maxFactor` fits the budget, the images held at the factor
chosen fit it. -/
theorem factorFor_fits (sizes : List (Nat × Nat)) (budget : Nat)
    (h : ∃ k, 1 ≤ k ∧ k ≤ maxFactor ∧ heldPixels sizes k ≤ budget) :
    heldPixels sizes (factorFor sizes budget) ≤ budget := by
  unfold factorFor
  cases hf : ((List.range maxFactor).map (· + 1)).find? (fun k => heldPixels sizes k ≤ budget) with
  | some k =>
    have := List.find?_some hf
    simpa using this
  | none =>
    obtain ⟨k, h1, h2, h3⟩ := h
    have h2' : k ≤ 16 := h2
    have mem : k ∈ (List.range maxFactor).map (· + 1) := by
      simp only [List.mem_map, List.mem_range]
      exact ⟨k-1, (by show k-1 < 16; omega), by omega⟩
    have none' := List.find?_eq_none.mp hf k mem
    simp [h3] at none'

/-- At factor 1 an image keeps its size. -/
theorem reducedSize_one (w h : Nat) : reducedSize w h 1 = (w,h) := by simp [reducedSize]

/-- The pixels of `b` reduced by `k`: row by row, each the mean of its block of at most `k`
by `k` pixels of `b` (the blocks at the right and bottom edges are smaller). -/
def reducePixels (b : Bitmap) (k w h : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (w*h*4)
  for y in [0:h] do
    for x in [0:w] do
      let mut r := 0
      let mut g := 0
      let mut bl := 0
      let mut a := 0
      let mut n := 0
      for dy in [0:k] do
        let sy := y*k+dy
        if sy < b.height then
          for dx in [0:k] do
            let sx := x*k+dx
            if sx < b.width then
              let i := (sy*b.width+sx)*4
              r := r + (b.rgba.get! i).toNat
              g := g + (b.rgba.get! (i+1)).toNat
              bl := bl + (b.rgba.get! (i+2)).toNat
              a := a + (b.rgba.get! (i+3)).toNat
              n := n+1
      let count := max 1 n
      out := (((out.push (r/count).toUInt8).push (g/count).toUInt8).push (bl/count).toUInt8).push (a/count).toUInt8
  return out

/-- `b` held at factor `k` (`reducedSize`): `b` itself at factor 1 and when it is small. -/
def reduce (b : Bitmap) (k : Nat) : Bitmap :=
  let (w,h) := reducedSize b.width b.height k
  if w == b.width && h == b.height then b else {width := w, height := h, rgba := reducePixels b k w h}

/-- Factor 1 changes no bitmap. -/
theorem reduce_one (b : Bitmap) : reduce b 1 = b := by simp [reduce, reducedSize_one]

/-- The key under which a store keeps the size of the image `href` as it is, when it holds
the image reduced: an entry with that size and no pixels. No reference has this key: it
starts with U+0001, which no URL and no `data:` URI holds. -/
def naturalKey (href : String) : String := "\x01natural " ++ href

/-- The size of the image `href` as it is, when the store holds it reduced; none when the
held bitmap is the image. -/
def Store.natural (store : Store) (href : String) : Option (Nat × Nat) :=
  match store.get? (naturalKey href) with
  | some (.ok (_,b)) => some (b.width,b.height)
  | _ => none

/-- The size of an image from the start of its file, with no decoding: the IHDR chunk of a
PNG, the logical screen of a GIF, the first frame header (SOF) of a JPEG. None when the
bytes are none of these or stop early. -/
def naturalSize (bytes : ByteArray) : Option (Nat × Nat) :=
  let be16 := fun (i : Nat) => (bytes.get! i).toNat*256 + (bytes.get! (i+1)).toNat
  if bytes.size >= 24 && bytes.get! 0 == 137 && bytes.get! 1 == 80 then
    some (be16 16*65536 + be16 18,be16 20*65536 + be16 22)
  else if bytes.size >= 10 && bytes.get! 0 == 71 && bytes.get! 1 == 73 && bytes.get! 2 == 70 then
    some ((bytes.get! 6).toNat + (bytes.get! 7).toNat*256,(bytes.get! 8).toNat + (bytes.get! 9).toNat*256)
  else if bytes.size >= 4 && bytes.get! 0 == 0xFF && bytes.get! 1 == 0xD8 then Id.run do
    -- JPEG (ITU-T T.81 B.1.1.3): marker segments, each `FF`, a code, a two-byte length.
    let mut i := 2
    for _ in [0:bytes.size] do
      if i+9 >= bytes.size then return none
      if bytes.get! i != 0xFF then return none
      let code := (bytes.get! (i+1)).toNat
      if code == 0xFF then i := i+1
      else if code >= 0xC0 && code <= 0xCF && code != 0xC4 && code != 0xC8 && code != 0xCC then
        return some (be16 (i+7),be16 (i+5))
      else if code == 0xD8 || code == 0x01 || (code >= 0xD0 && code <= 0xD7) then i := i+2
      else i := i+2+be16 (i+2)
    return none
  else none

/-- A reader for bytes that are none of the raster formats: none when the bytes are not its
format; else the picture it drew and the size of the image in CSS pixels (an SVG document
drawn at twice its size has a picture with four times the pixels of its size). The SVG
reader is a later module, so a caller gives it (`WebRender.vectorPicture`). -/
abbrev VectorReader := ByteArray → Option (Except String (Bitmap × Nat × Nat))

/-- Bytes as a picture, and the size of the image when it is not the picture's: a raster
format (`decode`), else what `vector` reads. -/
def decodeWith (vector : VectorReader) (bytes : ByteArray) : Except String (Bitmap × Option (Nat × Nat)) :=
  match decode bytes with
  | .ok b => .ok (b,none)
  | .error message =>
    match vector bytes with
    | some (.ok (b,w,h)) => .ok (b,if w == b.width && h == b.height then none else some (w,h))
    | some (.error refusal) => .error refusal
    | none => .error message

/-- With no vector reader, `decodeWith` is `decode`. -/
theorem decodeWith_none (bytes : ByteArray) :
    decodeWith (fun _ => none) bytes = (decode bytes).map fun b => (b,none) := by
  unfold decodeWith
  cases decode bytes <;> rfl

/-- Add one image to the store under `href`, held at factor `k` (`reduce`). The document
    budget is checked from the pixels already held, so no later image can pass it. -/
def Store.addBytes (store : Store) (used : Nat) (href : String) (bytes : ByteArray) (k : Nat := 1)
    (vector : VectorReader := fun _ => none) : Store × Nat :=
  match decodeWith vector bytes with
  | .error message => (store.insert href (.error message),used)
  | .ok (whole,own) =>
    let bitmap := reduce whole k
    let size := bitmap.width*bitmap.height
    if used+size > maxDocumentPixels then
      (store.insert href (.error s!"image pixels of the document exceed {maxDocumentPixels}"),used)
    else
      let store := store.insert href (.ok (store.size,bitmap))
      -- The image's own size, when the held picture has another: a vector image's size, or
      -- the size of the whole bitmap of an image held reduced.
      let natural := match own with
        | some size => some size
        | none => if bitmap.width == whole.width && bitmap.height == whole.height then none else some (whole.width,whole.height)
      let store := match natural with
        | none => store
        | some (w,h) => store.insert (naturalKey href) (.ok (store.size,{width := w, height := h, rgba := ByteArray.empty}))
      (store,used+size)

/-- Add one `data:` reference, held at factor `k`. -/
def Store.addData (store : Store) (used : Nat) (href : String) (k : Nat := 1)
    (vector : VectorReader := fun _ => none) : Store × Nat :=
  match dataBytes href with
  | .error message => (store.insert href (.error message),used)
  | .ok bytes => store.addBytes used href bytes k vector

end NativeImage
