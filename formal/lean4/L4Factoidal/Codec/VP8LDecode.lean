import L4Factoidal.Codec.VP8LPlane
import L4Factoidal.Codec.WebP

/-! Reconstruct a VP8L ARGB image and export straight RGBA (RFC 9649 §3.5). -/
namespace L4Factoidal.Codec.VP8L

private def component (pixel : UInt32) (shift : UInt32) : Nat :=
  ((pixel >>> shift) &&& 255).toNat

private def alpha (p : UInt32) : Nat := component p 24
private def red (p : UInt32) : Nat := component p 16
private def green (p : UInt32) : Nat := component p 8
private def blue (p : UInt32) : Nat := component p 0

private def argb (a r g b : Nat) : UInt32 :=
  UInt32.ofNat (a%256 * 16777216 + r%256 * 65536 + g%256 * 256 + b%256)

private def addChannels (a b : UInt32) : UInt32 :=
  argb (alpha a + alpha b) (red a + red b) (green a + green b) (blue a + blue b)

private def average (a b : UInt32) : UInt32 :=
  argb ((alpha a + alpha b)/2) ((red a + red b)/2)
    ((green a + green b)/2) ((blue a + blue b)/2)

private def distance (a b : UInt32) : Nat :=
  let delta := fun (x y : Nat) => (Int.ofNat x - Int.ofNat y).natAbs
  delta (alpha a) (alpha b) + delta (red a) (red b) +
    delta (green a) (green b) + delta (blue a) (blue b)

private def clamp (n : Int) : Nat := min 255 n.toNat

private def full (a b c : UInt32) : UInt32 :=
  let channel := fun (f : UInt32 → Nat) =>
    clamp (Int.ofNat (f a) + Int.ofNat (f b) - Int.ofNat (f c))
  argb (channel alpha) (channel red) (channel green) (channel blue)

private def half (a b : UInt32) : UInt32 :=
  let channel := fun (f : UInt32 → Nat) =>
    let value := Int.ofNat (f a)
    clamp (value + (value - Int.ofNat (f b)).tdiv 2)
  argb (channel alpha) (channel red) (channel green) (channel blue)

private def predict (mode : Nat) (left top topLeft topRight : UInt32) : UInt32 :=
  match mode with
  | 0 => 0xff000000
  | 1 => left
  | 2 => top
  | 3 => topRight
  | 4 => topLeft
  | 5 => average (average left topRight) top
  | 6 => average left topLeft
  | 7 => average left top
  | 8 => average topLeft top
  | 9 => average top topRight
  | 10 => average (average left topLeft) (average top topRight)
  | 11 => if distance top topLeft < distance left topLeft then left else top
  | 12 => full left top topLeft
  | 13 => half (average left top) topLeft
  | _ => 0xff000000

private def ceilDiv (n d : Nat) : Nat := (n + d - 1) / d

private def tileIndex (width tile cols position : Nat) : Nat :=
  (position / width / tile) * cols + (position % width / tile)

private def undoPrediction (width tile : Nat) (modes residual : Array UInt32) :
    Except String (Array UInt32) := do
  let cols := ceilDiv width tile
  let mut out := residual
  for index in [:residual.size] do
    let x := index % width
    let expected ←
      if index == 0 then pure 0xff000000
      else if index < width then pure out[index-1]!
      else if x == 0 then pure out[index-width]!
      else do
        let some mode := modes[tileIndex width tile cols index]? | throw "missing VP8L predictor"
        let topRight := if x + 1 == width then index - x else index - width + 1
        pure (predict (green mode) out[index-1]! out[index-width]! out[index-width-1]! out[topRight]!)
    out := out.set! index (addChannels residual[index]! expected)
  return out

private def signed (byte : Nat) : Int :=
  if byte < 128 then Int.ofNat byte else Int.ofNat byte - 256

private def delta (coefficient channel : Nat) : Int := signed coefficient * signed channel / 32

private def wrapped (n : Int) : Nat := (n % 256).toNat

private def undoColor (width tile : Nat) (coefficients pixels : Array UInt32) :
    Except String (Array UInt32) := do
  let cols := ceilDiv width tile
  let mut out := pixels
  for index in [:pixels.size] do
    let some c := coefficients[tileIndex width tile cols index]? | throw "missing VP8L color transform"
    let p := pixels[index]!
    let g := green p
    let r := wrapped (Int.ofNat (red p) + delta (blue c) g)
    let b := wrapped (Int.ofNat (blue p) + delta (green c) g + delta (red c) r)
    out := out.set! index (argb (alpha p) r g b)
  return out

private def undoSubtractGreen (p : UInt32) : UInt32 :=
  let g := green p
  argb (alpha p) (red p + g) g (blue p + g)

private def unpackPalette (width height bundle : Nat) (palette pixels : Array UInt32) :
    Except String (Array UInt32) := do
  let packedWidth := ceilDiv width bundle
  if pixels.size != packedWidth*height then throw "invalid VP8L packed palette plane"
  let bits := 8 / bundle
  let mut out := Array.emptyWithCapacity (width*height)
  for y in [:height] do
    for x in [:width] do
      let word := green pixels[y*packedWidth + x/bundle]!
      let index := word / (2 ^ ((x % bundle)*bits)) % (2^bits)
      out := out.push (palette[index]?.getD 0)
  return out

private def restorePalette (deltas : Array UInt32) : Array UInt32 := Id.run do
  let mut out := Array.emptyWithCapacity deltas.size
  let mut last := 0
  for difference in deltas do
    last := addChannels last difference
    out := out.push last
  return out

private inductive Transform where
  | predictor (tile : Nat) (map : Array UInt32)
  | color (tile : Nat) (map : Array UInt32)
  | subtractGreen
  | palette (width bundle : Nat) (entries : Array UInt32)

private def readTransforms (width height maxPixels : Nat) :
    BitM (Nat × List Transform) := do
  let mut storedWidth := width
  let mut transforms : List Transform := []
  let mut seen := Array.replicate 4 false
  for _ in [:5] do
    if (← readBit) == 0 then return (storedWidth, transforms)
    let kind ← readBits 2
    if seen[kind]! then throw "duplicate VP8L transform"
    seen := seen.set! kind true
    let transform : Transform ← match kind with
      | 0 | 1 => do
        let tile := 2 ^ (2 + (← readBits 3))
        let plane ← readPlane (ceilDiv storedWidth tile) (ceilDiv height tile) false maxPixels
        if kind == 1 then pure (.color tile plane.pixels)
        else
          if plane.pixels.any (fun pixel => green pixel > 13) then throw "invalid VP8L predictor mode"
          pure (.predictor tile plane.pixels)
      | 2 => pure .subtractGreen
      | _ => do
        let count := (← readBits 8) + 1
        -- The output-image pixel cap does not constrain the maximum 256-entry palette.
        let plane ← readPlane count 1 false 256
        let bundle := if count ≤ 2 then 8 else if count ≤ 4 then 4 else if count ≤ 16 then 2 else 1
        pure (.palette storedWidth bundle (restorePalette plane.pixels))
    if let .palette _ bundle _ := transform then storedWidth := ceilDiv storedWidth bundle
    transforms := transform :: transforms
  throw "too many VP8L transforms"

private def readImage (width height maxPixels : Nat) : BitM (Array UInt32) := do
  let (storedWidth, transforms) ← readTransforms width height maxPixels
  let encoded ← readPlane storedWidth height true maxPixels
  let mut activeWidth := storedWidth
  let mut pixels := encoded.pixels
  for transform in transforms do
    match transform with
    | .predictor tile map => pixels ← ofExcept (undoPrediction activeWidth tile map pixels)
    | .color tile map => pixels ← ofExcept (undoColor activeWidth tile map pixels)
    | .subtractGreen => pixels := pixels.map undoSubtractGreen
    | .palette restoredWidth bundle entries =>
      pixels ← ofExcept (unpackPalette restoredWidth height bundle entries pixels)
      activeWidth := restoredWidth
  return pixels

structure Image where
  width : Nat
  height : Nat
  rgba : ByteArray
  exactSize : rgba.size = width*height*4

/-- Decode a static lossless WebP into straight (unpremultiplied) RGBA. -/
def decode (src : ByteArray) (maxBytes : Nat := 8388608) (maxPixels : Nat := 4194304) :
    Except String Image := do
  let info ← WebP.inspect src maxBytes maxPixels
  if info.encoding != .vp8l then throw "expected lossless WebP"
  let p := info.pixels
  let header := {data := src.extract (p.offset+5) (p.offset+p.size), pos := 0 : Bits}
  let (image, _) ← (readImage info.width info.height maxPixels).run header
  let mut rgba := ByteArray.emptyWithCapacity (info.width*info.height*4)
  for pixel in image do
    rgba := rgba.push (UInt8.ofNat (red pixel)) |>.push (UInt8.ofNat (green pixel))
      |>.push (UInt8.ofNat (blue pixel)) |>.push (UInt8.ofNat (alpha pixel))
  if exactSize : rgba.size = info.width*info.height*4 then
    return {width := info.width, height := info.height, rgba, exactSize}
  else throw "invalid decoded VP8L size"

theorem rgba_size (image : Image) : image.rgba.size = image.width*image.height*4 := image.exactSize

#guard undoSubtractGreen 0xfff612fe == 0xff081210
#guard half 0xff202020 0xff232323 == 0xff1f1f1f

#print axioms rgba_size

end L4Factoidal.Codec.VP8L
