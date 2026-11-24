/-!
A static WebP container index (RFC 9649, sections 2 and 3.4). The image and alpha
payloads remain in the input buffer; ranges carry a bound on their exclusive end.
This reads container metadata. Pixel reconstruction uses the VP8 or VP8L payload.
-/

namespace L4Factoidal.Codec.WebP

structure Span (limit : Nat) where
  offset : Nat
  size : Nat
  within : offset + size ≤ limit

/-- Every relative byte index in the span lies in the source buffer. -/
theorem Span.byteWithin {limit : Nat} (s : Span limit) {i : Nat} (h : i < s.size) :
    s.offset + i < limit := by
  have bounds := s.within
  omega

inductive Encoding where
  | vp8 | vp8l
  deriving Repr, DecidableEq

structure Image (limit : Nat) where
  encoding : Encoding
  width : Nat
  height : Nat
  /-- VP8L's alpha bit is a hint. VP8 uses a separate optional ALPH payload. -/
  alphaHint : Bool := false
  pixels : Span limit
  alpha : Option (Span limit) := none
  profile : Option (Span limit) := none

private def byte (src : ByteArray) (i : Nat) : Nat :=
  (src[i]?.getD 0).toNat

private def le16 (src : ByteArray) (i : Nat) : Nat :=
  byte src i + 256 * byte src (i+1)

private def le24 (src : ByteArray) (i : Nat) : Nat :=
  le16 src i + 65536 * byte src (i+2)

private def le32 (src : ByteArray) (i : Nat) : Nat :=
  le24 src i + 16777216 * byte src (i+3)

private def tagAt (src : ByteArray) (i : Nat) (tag : String) : Bool :=
  src.extract i (i+4) == tag.toUTF8

private def losslessHeader (src : ByteArray) (s : Span src.size) : Except String (Nat × Nat × Bool) := do
  if s.size < 5 || byte src s.offset != 0x2f then throw "invalid VP8L header"
  let packed := le32 src (s.offset+1)
  if packed / (2^29) != 0 then throw "unsupported VP8L version"
  return (packed % 16384 + 1, packed / 16384 % 16384 + 1, packed / (2^28) % 2 == 1)

private def lossyHeader (src : ByteArray) (s : Span src.size) : Except String (Nat × Nat) := do
  let start := s.offset
  if s.size < 10 || byte src start % 2 != 0 || le24 src (start+3) != 0x2a019d then
    throw "invalid VP8 key frame header"
  let width := le16 src (start+6) % 16384
  let height := le16 src (start+8) % 16384
  if width == 0 || height == 0 then throw "invalid VP8 dimensions"
  return (width, height)

/-- Index one static image without copying its compressed payload. Limits are part of
    the decoder's caller policy and are checked before any pixel buffer is needed. -/
def inspect (src : ByteArray) (maxBytes : Nat := 8388608) (maxPixels : Nat := 4194304) :
    Except String (Image src.size) := do
  if src.size < 12 || src.size > maxBytes || !tagAt src 0 "RIFF" || !tagAt src 8 "WEBP" then
    throw "invalid or oversized WebP container"
  let declared := le32 src 4
  let streamEnd := declared + 8
  if declared < 4 || declared % 2 != 0 then throw "invalid WebP file size"
  if fileBound : streamEnd ≤ src.size then
    let mut cursor := 12
    let mut canvas : Option (Nat × Nat) := none
    let mut alpha : Option (Span src.size) := none
    let mut profile : Option (Span src.size) := none
    let mut image : Option (Image src.size) := none
    -- Every chunk consumes at least its 8-byte header. Unknown chunks do not allocate.
    for _ in [0:declared/8+1] do
      if cursor == streamEnd then break
      if cursor + 8 > streamEnd then throw "truncated WebP chunk header"
      let size := le32 src (cursor+4)
      let offset := cursor+8
      let next := offset+size+(size%2)
      if chunkBound : next ≤ streamEnd then
        have payloadBound : offset+size ≤ src.size := by omega
        let span : Span src.size := ⟨offset, size, payloadBound⟩
        if size % 2 == 1 && byte src (offset+size) != 0 then throw "invalid WebP chunk padding"
        let tag := src.extract cursor (cursor+4)
        if tag == "VP8X".toUTF8 then
          if cursor != 12 || size != 10 then throw "invalid VP8X chunk"
          if byte src offset / 2 % 2 == 1 then throw "animated WebP needs a frame compositor"
          canvas := some (1+le24 src (offset+4), 1+le24 src (offset+7))
        else if tag == "ICCP".toUTF8 then
          if canvas.isNone || image.isSome || alpha.isSome then throw "misplaced WebP colour profile"
          if profile.isNone then profile := some span
        else if tag == "ALPH".toUTF8 then
          if canvas.isNone || image.isSome || alpha.isSome || size == 0 then throw "invalid WebP alpha chunk"
          alpha := some span
        else if tag == "VP8L".toUTF8 then
          if image.isSome || alpha.isSome then throw "invalid WebP lossless chunk order"
          let (width, height, alphaHint) ← losslessHeader src span
          image := some {encoding := .vp8l, width, height, alphaHint, pixels := span, profile}
        else if tag == "VP8 ".toUTF8 then
          if image.isSome then throw "duplicate WebP image chunk"
          let (width, height) ← lossyHeader src span
          image := some {encoding := .vp8, width, height, alphaHint := alpha.isSome, pixels := span, alpha, profile}
        else if tag == "ANIM".toUTF8 || tag == "ANMF".toUTF8 then
          throw "animated WebP needs a frame compositor"
        cursor := next
      else throw "truncated WebP chunk"
    if cursor != streamEnd then throw "incomplete WebP chunk index"
    let some result := image | throw "WebP has no image chunk"
    if canvas.any (· != (result.width, result.height)) then throw "WebP canvas and image dimensions differ"
    if result.width * result.height > maxPixels then throw "WebP exceeds pixel budget"
    return result
  else throw "truncated WebP file"

theorem inspect_payload_byte_within (src : ByteArray) (result : Image src.size) {i : Nat}
    (h : i < result.pixels.size) : result.pixels.offset + i < src.size :=
  result.pixels.byteWithin h

#print axioms Span.byteWithin
#print axioms inspect_payload_byte_within

-- The minimal VP8L header for 2 by 3; no image tokens are needed by the index.
private def losslessFixture : ByteArray :=
  "RIFF".toUTF8 ++ ⟨#[18,0,0,0]⟩ ++ "WEBPVP8L".toUTF8 ++
    ⟨#[5,0,0,0,0x2f,1,128,0,0,0]⟩

private def fixtureSize (result : Except String (Image n)) : Option (Nat × Nat) :=
  result.toOption.map fun i => (i.width,i.height)

#guard fixtureSize (inspect losslessFixture) == some (2,3)
#guard (inspect losslessFixture 1024 5).isOk == false
#guard (inspect (losslessFixture.extract 0 (losslessFixture.size-1))).isOk == false
#guard fixtureSize (inspect (losslessFixture ++ ⟨#[7,8]⟩)) == some (2,3)

end L4Factoidal.Codec.WebP
