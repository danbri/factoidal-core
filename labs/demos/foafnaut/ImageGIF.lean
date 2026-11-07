import ImagePNG

/- GIF decoder (GIF89a, CompuServe 1990; GIF87a is the same without extensions) for
   raster paint: every frame, composed on the logical screen as the disposal methods
   say, with its delay.

   The rules of `ImagePNG` apply: the screen size is checked before any allocation;
   every loop is over the input or over checked sizes, with no recursion; a read past
   the end is a refusal. The LZW table has at most 4096 entries and one code writes at
   most 4096 indices, so one code costs at most 4096 steps. -/
namespace NativeImage

open L4Factoidal
open L4Factoidal.Rendering (Bitmap)

/-- Limit on the frames of one animation, and on their pixels in all. -/
def maxGIFFrames : Nat := 256
def maxAnimationPixels : Nat := 16777216

/-- One frame: the whole logical screen after the frame is drawn, and how long it
    stays, in milliseconds. -/
structure GIFFrame where
  bitmap : Bitmap
  delayMs : Nat

private def le16 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat+(b.get! (i+1)).toNat*256

/-- The data sub-blocks from `start` (§15): their bytes, and the position after the
    block terminator. -/
private def subBlocks (b : ByteArray) (start : Nat) : Except String (ByteArray × Nat) := do
  let mut at_ := start
  let mut out := ByteArray.empty
  for _ in [0:b.size+1] do
    if at_ >= b.size then throw "GIF data sub-blocks run past the end"
    let n := (b.get! at_).toNat
    if n == 0 then return (out,at_+1)
    if at_+1+n > b.size then throw "GIF data sub-block runs past the end"
    out := out ++ b.extract (at_+1) (at_+1+n)
    at_ := at_+1+n
  throw "GIF data sub-blocks run past the end"

/-- Variable-length LZW (Appendix F): the colour indices of `count` pixels. Indices
    that the data does not give stay `none` (drawn as transparent). -/
def lzwDecode (data : ByteArray) (minimum count : Nat) : Except String (Array (Option UInt8)) := do
  if minimum < 2 || minimum > 8 then throw "GIF LZW minimum code size must be 2 to 8"
  let clear := 1 <<< minimum
  let eoi := clear+1
  let mut parent : Array Nat := Array.replicate 4096 0
  let mut suffix : Array UInt8 := Array.replicate 4096 0
  let mut first : Array UInt8 := Array.replicate 4096 0
  let mut length : Array Nat := Array.replicate 4096 0
  for i in [0:clear] do
    suffix := suffix.set! i i.toUInt8
    first := first.set! i i.toUInt8
    length := length.set! i 1
  let mut out : Array (Option UInt8) := Array.replicate count none
  let mut written := 0
  let mut size := minimum+1
  let mut next := eoi+1
  let mut previous : Option Nat := none
  let mut bits := 0
  let mut held := 0
  let mut ended := false
  for byte in data do
    if ended || written >= count then break
    bits := bits+(byte.toNat <<< held)
    held := held+8
    -- At least 3 bits a code, so at most 3 codes a byte.
    for _ in [0:3] do
      if ended || held < size then break
      let code := bits % (1 <<< size)
      bits := bits >>> size
      held := held-size
      if code == clear then
        size := minimum+1
        next := eoi+1
        previous := none
        continue
      if code == eoi then
        ended := true
        break
      -- The string of `code`, or of the previous code and its first index.
      let (from_,extra) ← match previous with
        | none => if code < clear then pure (code,none) else throw "GIF LZW data starts with an unknown code"
        | some p =>
          if code < next then pure (code,none)
          else if code == next then pure (p,some first[p]!)
          else throw "GIF LZW code is not yet in the table"
      let n := length[from_]!
      let total := n+(if extra.isSome then 1 else 0)
      -- Indices past the image are dropped.
      let mut c := from_
      for i in [0:n] do
        let at_ := written+n-1-i
        if at_ < count then out := out.set! at_ (some suffix[c]!)
        c := parent[c]!
      if let some e := extra then
        if written+n < count then out := out.set! (written+n) (some e)
      written := written+total
      if let some p := previous then
        if next < 4096 then
          parent := parent.set! next p
          suffix := suffix.set! next (if code == next then first[p]! else first[code]!)
          first := first.set! next first[p]!
          length := length.set! next (length[p]!+1)
          next := next+1
          if next == (1 <<< size) && size < 12 then size := size+1
      previous := some code
  return out

/-- The row of the image that decoded row `r` is, for interlaced data (Appendix E):
    every 8th row from 0, every 8th from 4, every 4th from 2, every 2nd from 1. -/
def interlacedRow (height r : Nat) : Nat :=
  let p1 := (height+7)/8
  let p2 := (height+3)/8
  let p3 := (height+1)/4
  if r < p1 then r*8
  else if r < p1+p2 then (r-p1)*8+4
  else if r < p1+p2+p3 then (r-p1-p2)*4+2
  else (r-p1-p2-p3)*2+1

private structure Control where
  disposal : Nat := 0
  transparent : Option Nat := none
  delay : Nat := 0

/-- Every frame of a GIF, at most `limit` of them. -/
def decodeGIFFrames (bytes : ByteArray) (limit : Nat := maxGIFFrames) : Except String (Array GIFFrame) := do
  if bytes.size > maxImageBytes then throw s!"GIF exceeds {maxImageBytes} bytes"
  if bytes.size < 13 then throw "GIF header is truncated"
  let tag := (String.fromUTF8? (bytes.extract 0 6)).getD ""
  if tag != "GIF89a" && tag != "GIF87a" then throw "image is not GIF87a or GIF89a"
  let width := le16 bytes 6
  let height := le16 bytes 8
  if width == 0 || height == 0 then throw "GIF screen has no pixels"
  if width*height > maxImagePixels then throw s!"GIF screen exceeds {maxImagePixels} pixels"
  let packed := (bytes.get! 10).toNat
  let mut at_ := 13
  let mut global := ByteArray.empty
  if packed >= 128 then
    let n := 3*(2 <<< (packed % 8))
    if at_+n > bytes.size then throw "GIF global colour table is truncated"
    global := bytes.extract at_ (at_+n)
    at_ := at_+n
  -- Browsers start from transparent black, not from the background colour.
  let mut canvas := zeroBytes (width*height*4)
  let mut frames : Array GIFFrame := #[]
  let mut control : Control := {}
  for _ in [0:bytes.size] do
    if frames.size >= limit then break
    -- A file cut before its trailer keeps the frames it has.
    if at_ >= bytes.size then break
    let kind := bytes.get! at_
    if kind == 0x3B then break
    if kind == 0x21 then
      if at_+2 > bytes.size then throw "GIF extension is truncated"
      let label := bytes.get! (at_+1)
      let (body,after) ← subBlocks bytes (at_+2)
      if label == 0xF9 then
        if body.size < 4 then throw "GIF graphic control extension is truncated"
        let flags := (body.get! 0).toNat
        let transparent := if flags % 2 == 1 then some (body.get! 3).toNat else none
        control := {disposal := (flags/4) % 8, delay := le16 body 1, transparent := transparent}
      at_ := after
    else if kind == 0x2C then
      if at_+10 > bytes.size then throw "GIF image descriptor is truncated"
      let left := le16 bytes (at_+1)
      let top := le16 bytes (at_+3)
      let w := le16 bytes (at_+5)
      let h := le16 bytes (at_+7)
      let flags := (bytes.get! (at_+9)).toNat
      at_ := at_+10
      let mut table := global
      if flags >= 128 then
        let n := 3*(2 <<< (flags % 8))
        if at_+n > bytes.size then throw "GIF local colour table is truncated"
        table := bytes.extract at_ (at_+n)
        at_ := at_+n
      if table.size == 0 then throw "GIF image has no colour table"
      if w*h > maxImagePixels then throw s!"GIF image exceeds {maxImagePixels} pixels"
      if at_ >= bytes.size then throw "GIF image data is truncated"
      let minimum := (bytes.get! at_).toNat
      let (data,after) ← subBlocks bytes (at_+1)
      at_ := after
      let indices ← lzwDecode data minimum (w*h)
      let before := canvas
      for row in [0:h] do
        let y := top+(if flags / 64 % 2 == 1 then interlacedRow h row else row)
        if y >= height then continue
        for column in [0:w] do
          let x := left+column
          if x >= width then continue
          let some index := indices[row*w+column]! | continue
          let index := index.toNat
          if control.transparent == some index || 3*index+2 >= table.size then continue
          let o := (y*width+x)*4
          canvas := canvas.set! o (table.get! (3*index)) |>.set! (o+1) (table.get! (3*index+1))
            |>.set! (o+2) (table.get! (3*index+2)) |>.set! (o+3) 255
      if (frames.size+1)*width*height > maxAnimationPixels then break
      -- A delay of 0 or 10 ms shows for 100 ms in the common browsers.
      let delay := if control.delay <= 1 then 100 else control.delay*10
      frames := frames.push {bitmap := {width,height,rgba := canvas},delayMs := delay}
      -- Disposal (§23): 2 clears the frame's rectangle, 3 restores the screen before it.
      if control.disposal == 2 then
        for row in [0:h] do
          for column in [0:w] do
            let x := left+column
            let y := top+row
            if x < width && y < height then
              let o := (y*width+x)*4
              canvas := canvas.set! o 0 |>.set! (o+1) 0 |>.set! (o+2) 0 |>.set! (o+3) 0
      else if control.disposal == 3 then canvas := before
      control := {}
    else throw s!"GIF block {kind} is not an extension, an image or the trailer"
  if frames.isEmpty then throw "GIF has no image"
  return frames

/-- The first frame, as a still image. -/
def decodeGIF (bytes : ByteArray) : Except String Bitmap := do
  let frames ← decodeGIFFrames bytes 1
  match frames[0]? with
  | some f => return f.bitmap
  | none => throw "GIF has no image"

end NativeImage
