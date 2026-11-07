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

/-- Add one image to the store under `href`. The document budget is checked from
    the pixels already held, so no later image can pass it. -/
def Store.addBytes (store : Store) (used : Nat) (href : String) (bytes : ByteArray) : Store × Nat :=
  match decode bytes with
  | .error message => (store.insert href (.error message),used)
  | .ok bitmap =>
    let size := bitmap.width*bitmap.height
    if used+size > maxDocumentPixels then
      (store.insert href (.error s!"image pixels of the document exceed {maxDocumentPixels}"),used)
    else (store.insert href (.ok (store.size,bitmap)),used+size)

/-- Add one `data:` reference. -/
def Store.addData (store : Store) (used : Nat) (href : String) : Store × Nat :=
  match dataBytes href with
  | .error message => (store.insert href (.error message),used)
  | .ok bytes => store.addBytes used href bytes

end NativeImage
