import L4Factoidal.Codec.VP8Filter

/-!
Bilinear VP8 chroma reconstruction and straight RGBA output. The integer
weights and YUV-to-RGB coefficients match the libwebp scalar decoder.
-/
namespace L4Factoidal.Codec.VP8

private def chromaWeight (near horizontal vertical diagonal : Nat) : Nat :=
  (9*near + 3*horizontal + 3*vertical + diagonal + 8) / 16

/-- Chroma upsampling preserves a constant plane even at replicated edges. -/
theorem chromaWeight_constant (sample : Nat) :
    chromaWeight sample sample sample sample = sample := by
  unfold chromaWeight
  omega

private def adjacent (pixel bound : Nat) : Nat :=
  let center := pixel/2
  if pixel % 2 == 0 then center-1 else min (bound-1) (center+1)

private def chroma (plane : @& ByteArray) (stride cx cy ax ay : Nat) : Nat :=
  let sample := fun x y => (plane[y*stride+x]?.getD 0).toNat
  chromaWeight (sample cx cy) (sample ax cy) (sample cx ay) (sample ax ay)

private def rgb (y u v : Nat) : UInt8 × UInt8 × UInt8 :=
  let luma := Int.ofNat (y*19077/256)
  let red := luma + Int.ofNat (v*26149/256) - 14234
  let green := luma - Int.ofNat (u*6419/256) - Int.ofNat (v*13320/256) + 8708
  let blue := luma + Int.ofNat (u*33050/256) - 17685
  (clipSample (red/64), clipSample (green/64), clipSample (blue/64))

structure RgbaImage where
  width : Nat
  height : Nat
  pixels : ByteArray
  pixelBytes : pixels.size = width*height*4

/-- Crop and convert the filtered YUV420 planes. A supplied alpha plane is
already decoded and contains one byte per visible sample, in raster order. -/
def toRGBA (frame : Reconstructed) (width height : Nat)
    (alpha : Option ByteArray := none) : Except String RgbaImage := do
  if width == 0 || height == 0 || width > frame.columns*16 || height > frame.rows*16 then
    throw "VP8 output dimensions do not fit the reconstructed planes"
  if alpha.any (fun a => a.size != width*height) then throw "VP8 alpha plane size mismatch"
  let yStride := frame.columns*16
  let uvStride := frame.columns*8
  let uvWidth := (width+1)/2
  let uvHeight := (height+1)/2
  let mut pixels := ByteArray.emptyWithCapacity (width*height*4)
  for row in [:height] do
    let cy := row/2
    let ay := adjacent row uvHeight
    for col in [:width] do
      let cx := col/2
      let ax := adjacent col uvWidth
      let y := (frame.y[row*yStride+col]?.getD 0).toNat
      let u := chroma frame.u uvStride cx cy ax ay
      let v := chroma frame.v uvStride cx cy ax ay
      let (r,g,b) := rgb y u v
      let a := (alpha.bind fun bytes => bytes[row*width+col]?).getD 255
      pixels := (((pixels.push r).push g).push b).push a
  if length : pixels.size = width*height*4 then return ⟨width,height,pixels,length⟩
  throw "invalid VP8 RGBA output length"

def decodeColor (src : ByteArray) (image : WebP.Image src.size)
    (alpha : Option ByteArray := none) : Except String RgbaImage := do
  let frame ← reconstruct src image
  let frame ← loopFilter frame
  toRGBA frame image.width image.height alpha

#print axioms chromaWeight_constant

end L4Factoidal.Codec.VP8
