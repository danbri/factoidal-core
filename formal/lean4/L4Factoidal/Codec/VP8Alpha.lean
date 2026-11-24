import L4Factoidal.Codec.VP8LDecode
import L4Factoidal.Codec.VP8Color

/-!
Lossy WebP alpha (RFC 9649 §2.7.1.2). Alpha filtering is independent of VP8
deblocking. The lossless mode supplies the frame dimensions to the VP8L
green-plane decoder rather than adding a synthetic bitstream header.
-/
namespace L4Factoidal.Codec.VP8

private def alphaSeed (decoded : @& ByteArray) (filter stride row col : Nat) : Nat :=
  let offset := row*stride+col
  let left := ((decoded[offset-1]?).getD 0).toNat
  let above := ((decoded[offset-stride]?).getD 0).toNat
  let corner := ((decoded[offset-stride-1]?).getD 0).toNat
  if filter == 0 || (row == 0 && col == 0) then 0
  else if row == 0 then left
  else if col == 0 || filter == 2 then above
  else if filter == 1 then left
  else (clipSample (Int.ofNat left + Int.ofNat above - Int.ofNat corner)).toNat

private def alphaAdd (seed delta : Nat) : UInt8 :=
  UInt8.ofNat (seed+delta)

/-- Alpha prediction uses byte addition modulo 256, including overflow. -/
theorem alphaAdd_mod256 (seed delta : Nat) :
    (alphaAdd seed delta).toNat = (seed+delta) % 256 :=
  UInt8.toNat_ofNat'

private def invertAlphaFilter (residual : ByteArray) (filter width height : Nat) : ByteArray :=
  if filter == 0 then residual else Id.run do
    let mut alpha := ByteArray.emptyWithCapacity (width*height)
    for row in [:height] do
      for col in [:width] do
        let seed := alphaSeed alpha filter width row col
        let delta := (residual[row*width+col]?.getD 0).toNat
        alpha := alpha.push (alphaAdd seed delta)
    return alpha

def readAlpha (src : ByteArray) (image : WebP.Image src.size) (maxPixels : Nat) :
    Except String (Option ByteArray) := do
  let some span := image.alpha | return none
  if span.size < 2 then throw "truncated WebP alpha"
  let header := (src[span.offset]?.getD 0).toNat
  let mode := header % 4
  let filter := header / 4 % 4
  -- Reserved bits are ignored and preprocessing is informational.
  if mode > 1 then throw "invalid WebP alpha compression method"
  let residue := src.extract (span.offset+1) (span.offset+span.size)
  let size := image.width*image.height
  if size > maxPixels then throw "WebP alpha exceeds pixel budget"
  let residual ← if mode == 0 then
      if residue.size < size then throw "truncated raw WebP alpha"
      else pure (residue.extract 0 size)
    else VP8L.decodeAlphaResidual residue image.width image.height maxPixels
  let alpha := invertAlphaFilter residual filter image.width image.height
  if alpha.size != size then throw "invalid WebP alpha size"
  return some alpha

def decodeInspected (src : ByteArray) (image : WebP.Image src.size) (maxPixels : Nat) :
    Except String RgbaImage := do
  if image.encoding != .vp8 then throw "expected lossy WebP"
  let alpha ← readAlpha src image maxPixels
  decodeColor src image alpha

/-- Decode a static lossy WebP with its matching alpha plane, if present. -/
def decode (src : ByteArray) (maxBytes : Nat := 8388608) (maxPixels : Nat := 4194304) :
    Except String RgbaImage := do
  let image ← WebP.inspect src maxBytes maxPixels
  decodeInspected src image maxPixels

#print axioms alphaAdd_mod256

end L4Factoidal.Codec.VP8
