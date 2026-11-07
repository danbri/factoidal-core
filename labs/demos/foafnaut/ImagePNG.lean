import L4Factoidal.Codec.Inflate
import L4Factoidal.Rendering.Scene

/- PNG decoder (ISO/IEC 15948, W3C PNG Second Edition) for raster paint.

   Image bytes are hostile input. Rules for this module and `ImageJPEG`:
   - `maxImagePixels` is checked from the header before any allocation, and each
     later allocation follows from the checked dimensions;
   - inflate stops at the exact size that the header gives;
   - every loop is over checked dimensions or over the input, with no recursion
     that grows with the input;
   - a read past the end, a wrong CRC and a wrong Adler-32 are refusals.
   This is the record for https://github.com/danbri/factoidal/issues/1120. -/
namespace NativeImage

open L4Factoidal
open L4Factoidal.Rendering (Bitmap)

/-- Limit on the pixels of one image: the paint table holds one word for each pixel. -/
def maxImagePixels : Nat := 1048576
/-- Limit on the encoded size of one image. -/
def maxImageBytes : Nat := 8388608

/-- `n` zero bytes. -/
def zeroBytes (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  for _ in [0:n] do out := out.push 0
  return out

private def u32 (b : ByteArray) (i : Nat) : Nat :=
  (b.get! i).toNat*16777216+(b.get! (i+1)).toNat*65536+(b.get! (i+2)).toNat*256+(b.get! (i+3)).toNat

private def signature : List UInt8 := [137,80,78,71,13,10,26,10]

/-- Adler-32, RFC 1950 §8.2. -/
def adler32 (b : ByteArray) : Nat := Id.run do
  let mut s1 := 1
  let mut s2 := 0
  for i in [0:b.size] do
    s1 := (s1+(b.get! i).toNat)%65521
    s2 := (s2+s1)%65521
  return s2*65536+s1

/-- Fields of IHDR and the chunks that change the meaning of a sample. -/
private structure Header where
  width : Nat := 0
  height : Nat := 0
  depth : Nat := 0
  colour : Nat := 0
  interlaced : Bool := false
  palette : ByteArray := .empty
  transparency : ByteArray := .empty
  /-- gAMA value times 100000, unless an sRGB chunk is present. -/
  gamma : Option Nat := none

private def Header.channels (h : Header) : Nat :=
  match h.colour with | 2 => 3 | 4 => 2 | 6 => 4 | _ => 1

private def Header.bitsPerPixel (h : Header) : Nat := h.channels*h.depth

/-- Bytes of one row of `width` pixels, with no filter byte. -/
private def Header.rowBytes (h : Header) (width : Nat) : Nat := (width*h.bitsPerPixel+7)/8

/-- Adam7: x start, y start, x step, y step of each pass. A plain image is one pass. -/
private def Header.passes (h : Header) : List (Nat × Nat × Nat × Nat) :=
  if h.interlaced then [(0,0,8,8),(4,0,8,8),(0,4,4,8),(2,0,4,4),(0,2,2,4),(1,0,2,2),(0,1,1,2)]
  else [(0,0,1,1)]

private def passSize (size start step : Nat) : Nat := (size+step-1-start)/step

private def Header.rawSize (h : Header) : Nat :=
  (h.passes.map fun (x0,y0,dx,dy) =>
    let w := if x0 < h.width then passSize h.width x0 dx else 0
    let rows := if y0 < h.height then passSize h.height y0 dy else 0
    if w == 0 then 0 else rows*(1+h.rowBytes w)).foldl (·+·) 0

private def validDepth (colour depth : Nat) : Bool :=
  match colour with
  | 0 => [1,2,4,8,16].contains depth
  | 3 => [1,2,4,8].contains depth
  | 2 | 4 | 6 => [8,16].contains depth
  | _ => false

private def readHeader (d : ByteArray) (at_ : Nat) : Except String Header := do
  let width := u32 d at_
  let height := u32 d (at_+4)
  if width == 0 || height == 0 then throw "PNG has no pixels"
  if width > maxImagePixels || height > maxImagePixels || width*height > maxImagePixels then
    throw s!"PNG exceeds {maxImagePixels} pixels"
  let depth := (d.get! (at_+8)).toNat
  let colour := (d.get! (at_+9)).toNat
  if !validDepth colour depth then throw "PNG colour type and bit depth are not valid"
  if d.get! (at_+10) != 0 || d.get! (at_+11) != 0 then throw "PNG compression or filter method is not valid"
  let interlace := d.get! (at_+12)
  if interlace > 1 then throw "PNG interlace method is not valid"
  return {width,height,depth,colour,interlaced:=interlace == 1}

/-- Chunk sequence (§5.3). Returns the header and the IDAT data. An unknown
    ancillary chunk is skipped; an unknown critical chunk is a refusal. -/
private def readChunks (d : ByteArray) : Except String (Header × ByteArray) := do
  if d.size > maxImageBytes then throw s!"PNG exceeds {maxImageBytes} bytes"
  if d.size < 8 || (List.range 8).any (fun i => some (d.get! i) != signature[i]?) then throw "not a PNG signature"
  let mut pos := 8
  let mut header : Option Header := none
  let mut data := ByteArray.empty
  let mut ended := false
  -- A chunk takes at least 12 bytes, so this bound is never the one that stops the loop.
  for _ in [0:d.size/12+1] do
    if pos+12 > d.size then throw "PNG ends inside a chunk"
    let length := u32 d pos
    if length > d.size || pos+12+length > d.size then throw "PNG chunk runs past the end of the data"
    let kind := String.ofList ((List.range 4).map fun i => Char.ofNat (d.get! (pos+4+i)).toNat)
    let crc := u32 d (pos+8+length)
    if (Codec.crc32 (d.extract (pos+4) (pos+8+length))).toNat != crc then throw s!"PNG CRC mismatch in {kind}"
    let body := pos+8
    if header.isNone && kind != "IHDR" then throw "PNG does not start with IHDR"
    match kind with
    | "IHDR" =>
      if header.isSome then throw "PNG has two IHDR chunks"
      if length != 13 then throw "PNG IHDR has the wrong length"
      header := some (← readHeader d body)
    | "PLTE" =>
      if length%3 != 0 || length == 0 || length > 768 then throw "PNG palette has the wrong length"
      header := header.map ({· with palette:=d.extract body (body+length)})
    | "tRNS" =>
      if length > 768 then throw "PNG tRNS is too long"
      header := header.map ({· with transparency:=d.extract body (body+length)})
    | "gAMA" =>
      if length != 4 then throw "PNG gAMA has the wrong length"
      header := header.map fun h => if h.gamma.isNone then {h with gamma:=some (u32 d body)} else h
    | "sRGB" =>
      -- §11.3.3.5: sRGB takes precedence over gAMA, and needs no correction here.
      header := header.map ({· with gamma:=some 45455})
    | "IDAT" => data := data ++ d.extract body (body+length)
    | "IEND" => ended := true
    | _ =>
      if (d.get! (pos+4)).toNat &&& 32 == 0 then throw s!"PNG critical chunk {kind} is not supported"
    if ended then break
    pos := pos+12+length
  let some h := header | throw "PNG has no IHDR"
  if !ended then throw "PNG has no IEND"
  if h.colour == 3 && h.palette.isEmpty then throw "PNG has no palette"
  return (h,data)

/-- zlib stream (RFC 1950): inflate exactly `size` bytes and check the Adler-32. -/
private def inflateExact (data : ByteArray) (size : Nat) : Except String ByteArray := do
  if data.size < 6 then throw "PNG image data is too short"
  let cmf := (data.get! 0).toNat
  let flg := (data.get! 1).toNat
  if cmf%16 != 8 || (cmf*256+flg)%31 != 0 || flg &&& 32 != 0 then throw "PNG zlib header is not valid"
  let (out,stop) ← Codec.inflateAt data 2 size
  if out.size != size then throw "PNG image data has the wrong size"
  if stop+4 > data.size then throw "PNG image data has no Adler-32"
  if adler32 out != u32 data stop then throw "PNG Adler-32 mismatch"
  return out

/-- §9.4 Paeth predictor. -/
@[inline] private def paeth (a b c : Nat) : Nat :=
  let p : Int := (a : Int)+b-c
  let pa := (p-a).natAbs
  let pb := (p-b).natAbs
  let pc := (p-c).natAbs
  if pa <= pb && pa <= pc then a else if pb <= pc then b else c

/-- Reverse the filters of `rows` rows of `row` bytes from `start`, in place. -/
private def unfilter (raw : ByteArray) (start rows row step : Nat) : Except String ByteArray := do
  let mut out := raw
  for y in [0:rows] do
    let line := start+y*(row+1)
    let filter := (out.get! line).toNat
    if filter > 4 then throw "PNG filter type is not valid"
    if filter == 0 then continue
    for i in [0:row] do
      let at_ := line+1+i
      let a := if i >= step then (out.get! (at_-step)).toNat else 0
      let b := if y > 0 then (out.get! (at_-row-1)).toNat else 0
      let c := if y > 0 && i >= step then (out.get! (at_-row-1-step)).toNat else 0
      let predicted := match filter with
        | 1 => a
        | 2 => b
        | 3 => (a+b)/2
        | _ => paeth a b c
      out := out.set! at_ ((out.get! at_)+predicted.toUInt8)
  return out

/-- Sample `index` of a row at byte `line`, at the depth of the image. -/
@[inline] private def sample (raw : ByteArray) (line depth index : Nat) : Nat :=
  match depth with
  | 8 => (raw.get! (line+index)).toNat
  | 16 => (raw.get! (line+index*2)).toNat*256+(raw.get! (line+index*2+1)).toNat
  | _ =>
    let bit := index*depth
    let byte := (raw.get! (line+bit/8)).toNat
    (byte >>> (8-depth-bit%8)) &&& ((1 <<< depth)-1)

/-- A sample as eight bits. -/
@[inline] private def eight (value depth : Nat) : Nat :=
  match depth with
  | 16 => value/256
  | 8 => value
  | _ => value*255/((1 <<< depth)-1)

/-- §12.1: sample^(1/(gamma*2.2)) for a display exponent of 2.2. `none` when the
    file gamma is within 2 percent of 1/2.2, where a byte hardly changes. -/
private def gammaTable (h : Header) : Option (Array UInt8) := do
  let value ← h.gamma
  if value == 0 then none
  let exponent := 1/(Float.ofNat value/100000*2.2)
  if (exponent-1).abs < 0.02 then none
  pure ((Array.range 256).map fun i =>
    (Float.pow (Float.ofNat i/255) exponent*255).round.toUInt8)

/-- Pixels of one pass into `out`, at `x0+dx*i`, `y0+dy*j`. -/
private def expandPass (h : Header) (raw : ByteArray) (start rows columns : Nat)
    (place : Nat × Nat × Nat × Nat) (table : Option (Array UInt8)) (out : ByteArray) : ByteArray := Id.run do
  let (x0,y0,dx,dy) := place
  let row := h.rowBytes columns
  let channels := h.channels
  let curve := fun (v : Nat) => match table with
    | some t => t[v]!
    | none => v.toUInt8
  let mut out := out
  let hasKey := h.transparency.size >= (if h.colour == 2 then 6 else 2)
  for y in [0:rows] do
    let line := start+y*(row+1)+1
    for x in [0:columns] do
      let first := x*channels
      let target := ((y0+y*dy)*h.width+x0+x*dx)*4
      let (r,g,b,a) : UInt8 × UInt8 × UInt8 × UInt8 := match h.colour with
        | 0 =>
          let v := sample raw line h.depth first
          let keyed := hasKey && (h.transparency.get! 0).toNat*256+(h.transparency.get! 1).toNat == v
          let c := curve (eight v h.depth)
          (c,c,c,if keyed then 0 else 255)
        | 2 =>
          let r := sample raw line h.depth first
          let g := sample raw line h.depth (first+1)
          let b := sample raw line h.depth (first+2)
          let key := fun (i : Nat) => (h.transparency.get! (i*2)).toNat*256+(h.transparency.get! (i*2+1)).toNat
          let keyed := hasKey && key 0 == r && key 1 == g && key 2 == b
          (curve (eight r h.depth),curve (eight g h.depth),curve (eight b h.depth),if keyed then 0 else 255)
        | 3 =>
          let v := sample raw line h.depth first
          let at_ := v*3
          let colour := fun (k : Nat) => if at_+k < h.palette.size then (h.palette.get! (at_+k)).toNat else 0
          (curve (colour 0),curve (colour 1),curve (colour 2),
            if v < h.transparency.size then h.transparency.get! v else 255)
        | 4 =>
          let c := curve (eight (sample raw line h.depth first) h.depth)
          (c,c,c,(eight (sample raw line h.depth (first+1)) h.depth).toUInt8)
        | _ =>
          (curve (eight (sample raw line h.depth first) h.depth),
           curve (eight (sample raw line h.depth (first+1)) h.depth),
           curve (eight (sample raw line h.depth (first+2)) h.depth),
           (eight (sample raw line h.depth (first+3)) h.depth).toUInt8)
      out := ((((out.set! target r).set! (target+1) g).set! (target+2) b).set! (target+3) a)
  return out

/-- Decode a PNG file to pixels. A refusal names what is wrong. -/
def decodePNG (bytes : ByteArray) : Except String Bitmap := do
  let (h,data) ← readChunks bytes
  let mut raw ← inflateExact data h.rawSize
  let table := gammaTable h
  let mut out := zeroBytes (h.width*h.height*4)
  let mut start := 0
  let step := max 1 (h.bitsPerPixel/8)
  for pass in h.passes do
    let (x0,y0,dx,dy) := pass
    let columns := if x0 < h.width then passSize h.width x0 dx else 0
    let rows := if y0 < h.height then passSize h.height y0 dy else 0
    if columns == 0 || rows == 0 then continue
    raw ← unfilter raw start rows (h.rowBytes columns) step
    out := expandPass h raw start rows columns pass table out
    start := start+rows*(1+h.rowBytes columns)
  return {width:=h.width,height:=h.height,rgba:=out}

end NativeImage
