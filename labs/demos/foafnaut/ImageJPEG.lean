import ImagePNG

/- JPEG decoder (ITU T.81), for raster paint. Baseline and extended sequential
   DCT with 8-bit samples, and progressive DCT with Huffman coding. One component
   (grey) or three (YCbCr, or RGB when Adobe APP14 or the component ids say so).
   Arithmetic coding, lossless, hierarchical, 12-bit and CMYK are refusals.

   Hostile input: see `ImagePNG`. Dimensions are checked before allocation, the
   coefficient store has a fixed limit, the scan count has a fixed limit, and each
   loop is over checked dimensions, so a small file can not ask for unbounded work. -/
namespace NativeImage

open L4Factoidal.Rendering (Bitmap)

/-- Limit on the coefficients of one image, over its components. Sampling factors
    pad a component to whole MCUs, so a narrow image needs more than its pixels: the
    worst case under `maxImagePixels` is 1 by 65535 at 4 by 4 sampling, which is
    this number (32*65536*3). The store takes 8 bytes for each coefficient. -/
def maxJpegCoefficients : Nat := 6291456
/-- Limit on the scans of one image. A progressive scan visits every block. -/
def maxJpegScans : Nat := 64

private def zigzag : Array Nat := #[
  0,1,8,16,9,2,3,10,17,24,32,25,18,11,4,5,12,19,26,33,40,48,41,34,27,20,13,6,7,14,21,28,
  35,42,49,56,57,50,43,36,29,22,15,23,30,37,44,51,58,59,52,45,38,31,39,46,53,60,61,54,47,55,62,63]

/-- One Huffman table (T.81 Annex C and F.2.2.3). -/
private structure Huffman where
  /-- Largest code of each length, or -1. -/
  maxCode : Array Int := Array.replicate 18 (-1)
  /-- First value index minus first code, for each length. -/
  delta : Array Int := Array.replicate 18 0
  values : ByteArray := .empty
  deriving Inhabited

private def Huffman.build (counts : Array Nat) (values : ByteArray) : Huffman := Id.run do
  let mut table : Huffman := {values}
  let mut code : Int := 0
  let mut index : Int := 0
  for length in [1:17] do
    let count := counts[length-1]!
    if count > 0 then
      table := {table with delta:=table.delta.set! length (index-code),maxCode:=table.maxCode.set! length (code+count-1)}
      index := index+count
      code := code+count
    code := code*2
  return table

private structure Component where
  id : Nat
  h : Nat
  v : Nat
  quant : Nat
  /-- Blocks across and down, padded to whole MCUs. -/
  across : Nat := 0
  down : Nat := 0
  /-- Blocks across and down of the component itself, for a scan of it alone. -/
  ownAcross : Nat := 0
  ownDown : Nat := 0
  /-- Index of its first coefficient. -/
  offset : Nat := 0
  deriving Inhabited

private structure Frame where
  width : Nat := 0
  height : Nat := 0
  progressive : Bool := false
  components : Array Component := #[]
  hMax : Nat := 1
  vMax : Nat := 1
  mcusAcross : Nat := 0
  mcusDown : Nat := 0

/-- Entropy-coded bits: stuffing and markers are handled here. -/
private structure BitReader where
  data : ByteArray
  pos : Nat
  bits : Nat := 0
  count : Nat := 0

/-- One bit. A marker or the end of the data here is a refusal. -/
@[inline] private def BitReader.bit (r : BitReader) : Except String (Nat × BitReader) := do
  if r.count > 0 then
    let count := r.count-1
    return ((r.bits >>> count) &&& 1,{r with count})
  if r.pos >= r.data.size then throw "JPEG entropy data ends early"
  let byte := (r.data.get! r.pos).toNat
  let next := if byte == 255 then
      if r.pos+1 >= r.data.size || r.data.get! (r.pos+1) != 0 then none else some (r.pos+2)
    else some (r.pos+1)
  let some pos := next | throw "JPEG entropy data ends early"
  return ((byte >>> 7) &&& 1,{r with pos,bits:=byte,count:=7})

private def BitReader.take (r : BitReader) (n : Nat) : Except String (Nat × BitReader) := do
  let mut value := 0
  let mut r := r
  for _ in [0:n] do
    let (b,next) ← r.bit
    value := value*2+b
    r := next
  return (value,r)

/-- T.81 Figure F.16: one Huffman value. -/
private def BitReader.symbol (r : BitReader) (t : Huffman) : Except String (Nat × BitReader) := do
  let mut code : Int := 0
  let mut r := r
  for length in [1:17] do
    let (b,next) ← r.bit
    r := next
    code := code*2+b
    if code <= t.maxCode[length]! then
      let index := (code+t.delta[length]!).toNat
      if index >= t.values.size then throw "JPEG Huffman table has no such value"
      return ((t.values.get! index).toNat,r)
  throw "JPEG Huffman code is not valid"

/-- T.81 F.2.2.1 EXTEND: `size` bits as a signed difference. -/
private def BitReader.signed (r : BitReader) (size : Nat) : Except String (Int × BitReader) := do
  if size == 0 then return (0,r)
  if size > 16 then throw "JPEG coefficient size is not valid"
  let (v,r) ← r.take size
  let value : Int := if v < (1 <<< (size-1)) then (v : Int)-((1 <<< size : Nat) : Int)+1 else v
  return (value,r)

/-- All tables and state of an image while its scans run. -/
private structure State where
  frame : Frame := {}
  quant : Array (Array Float) := Array.replicate 4 (Array.replicate 64 1)
  dc : Array Huffman := Array.replicate 4 {}
  ac : Array Huffman := Array.replicate 4 {}
  restart : Nat := 0
  coefficients : FloatArray := .empty
  scans : Nat := 0
  adobeTransform : Option Nat := none

/-- One component of one scan. -/
private structure ScanPart where
  index : Nat
  dc : Huffman
  ac : Huffman
  deriving Inhabited

/-- Spectral selection and successive approximation of a scan. -/
private structure Band where
  start : Nat
  stop : Nat
  high : Nat
  low : Nat

/-- State of a scan between blocks. -/
private structure Cursor where
  reader : BitReader
  predictors : Array Int
  eobRun : Nat := 0

@[inline] private def coefficientAt (c : FloatArray) (i : Nat) : Float := c.get! i

/-- Sequential block (T.81 F.2.2). -/
private def sequentialBlock (part : ScanPart) (slot : Nat) (block : Nat) (c : FloatArray) (cur : Cursor) :
    Except String (FloatArray × Cursor) := do
  let (size,r) ← cur.reader.symbol part.dc
  let (diff,r) ← r.signed size
  let dc := cur.predictors[slot]!+diff
  let mut c := c.set! block (Float.ofInt dc)
  let mut r := r
  let mut k := 1
  for _ in [0:64] do
    if k > 63 then break
    let (rs,next) ← r.symbol part.ac
    r := next
    let run := rs/16
    let size := rs%16
    if size == 0 then
      if run == 15 then k := k+16; continue
      break
    k := k+run
    if k > 63 then throw "JPEG coefficient index is not valid"
    let (value,next) ← r.signed size
    r := next
    c := c.set! (block+zigzag[k]!) (Float.ofInt value)
    k := k+1
  return (c,{cur with reader:=r,predictors:=cur.predictors.set! slot dc})

/-- Progressive first DC scan (T.81 G.1.2.1). -/
private def dcFirst (part : ScanPart) (slot block : Nat) (low : Nat) (c : FloatArray) (cur : Cursor) :
    Except String (FloatArray × Cursor) := do
  let (size,r) ← cur.reader.symbol part.dc
  let (diff,r) ← r.signed size
  let dc := cur.predictors[slot]!+diff
  return (c.set! block (Float.ofInt (dc*((1 <<< low : Nat) : Int))),{cur with reader:=r,predictors:=cur.predictors.set! slot dc})

/-- Progressive DC refinement: one bit. -/
private def dcRefine (block low : Nat) (c : FloatArray) (cur : Cursor) : Except String (FloatArray × Cursor) := do
  let (b,r) ← cur.reader.bit
  let add := Float.ofNat (b*(1 <<< low))
  return (c.set! block (c.get! block+add),{cur with reader:=r})

/-- Progressive first AC scan (T.81 G.1.2.2). -/
private def acFirst (part : ScanPart) (block : Nat) (band : Band) (c : FloatArray) (cur : Cursor) :
    Except String (FloatArray × Cursor) := do
  if cur.eobRun > 0 then return (c,{cur with eobRun:=cur.eobRun-1})
  let mut c := c
  let mut r := cur.reader
  let mut eobRun := 0
  let mut k := band.start
  for _ in [0:65] do
    if k > band.stop then break
    let (rs,next) ← r.symbol part.ac
    r := next
    let run := rs/16
    let size := rs%16
    if size == 0 then
      if run < 15 then
        let (extra,next) ← r.take run
        r := next
        eobRun := (1 <<< run)+extra-1
        break
      k := k+16
      continue
    k := k+run
    if k > 63 then throw "JPEG coefficient index is not valid"
    let (value,next) ← r.signed size
    r := next
    c := c.set! (block+zigzag[k]!) (Float.ofInt (value*((1 <<< band.low : Nat) : Int)))
    k := k+1
  return (c,{cur with reader:=r,eobRun})

/-- A refinement bit for a coefficient that is not zero. -/
@[inline] private def refineOne (at_ : Nat) (bitValue : Float) (c : FloatArray) (r : BitReader) :
    Except String (FloatArray × BitReader) := do
  let old := c.get! at_
  let (b,r) ← r.bit
  let units := (old.abs/bitValue).floor
  if b == 1 && units-2*(units/2).floor == 0 then
    return (c.set! at_ (if old > 0 then old+bitValue else old-bitValue),r)
  return (c,r)

/-- Progressive AC refinement (T.81 G.1.2.3 and Figure G.7). -/
private def acRefine (part : ScanPart) (block : Nat) (band : Band) (c : FloatArray) (cur : Cursor) :
    Except String (FloatArray × Cursor) := do
  let bitValue := Float.ofNat (1 <<< band.low)
  let mut c := c
  let mut r := cur.reader
  let mut eobRun := cur.eobRun
  let mut k := band.start
  if eobRun == 0 then
    for _ in [0:65] do
      if k > band.stop then break
      let (rs,next) ← r.symbol part.ac
      r := next
      let mut run := rs/16
      let size := rs%16
      let mut value : Float := 0
      if size == 0 then
        if run < 15 then
          let (extra,next) ← r.take run
          r := next
          eobRun := (1 <<< run)+extra
          break
      else
        if size != 1 then throw "JPEG refinement size is not valid"
        let (b,next) ← r.bit
        r := next
        value := if b == 1 then bitValue else -bitValue
      -- Skip `run` zero coefficients; refine each coefficient that is not zero.
      for _ in [0:64] do
        if k > band.stop then break
        let at_ := block+zigzag[k]!
        if c.get! at_ != 0 then
          let (next,reader) ← refineOne at_ bitValue c r
          c := next
          r := reader
        else
          if run == 0 then break
          run := run-1
        k := k+1
      if value != 0 then
        if k > 63 then throw "JPEG coefficient index is not valid"
        c := c.set! (block+zigzag[k]!) value
      k := k+1
  if eobRun > 0 then
    for _ in [0:65] do
      if k > band.stop then break
      let at_ := block+zigzag[k]!
      if c.get! at_ != 0 then
        let (next,reader) ← refineOne at_ bitValue c r
        c := next
        r := reader
      k := k+1
    eobRun := eobRun-1
  return (c,{cur with reader:=r,eobRun})

private def decodeBlock (progressive : Bool) (part : ScanPart) (slot block : Nat) (band : Band)
    (c : FloatArray) (cur : Cursor) : Except String (FloatArray × Cursor) :=
  if !progressive then sequentialBlock part slot block c cur
  else if band.start == 0 then
    if band.high == 0 then dcFirst part slot block band.low c cur else dcRefine block band.low c cur
  else if band.high == 0 then acFirst part block band c cur
  else acRefine part block band c cur

/-- Move past a restart marker (T.81 E.1.4). A missing one is a refusal. -/
private def nextRestart (cur : Cursor) : Except String Cursor := do
  let r := cur.reader
  let d := r.data
  if r.pos+1 >= d.size || d.get! r.pos != 255 || d.get! (r.pos+1) < 0xD0 || d.get! (r.pos+1) > 0xD7 then
    throw "JPEG restart marker is missing"
  return {reader:={data:=d,pos:=r.pos+2},predictors:=cur.predictors.map (fun _ => 0)}

/-- Run one scan over the blocks of its components. -/
private def runScan (state : State) (parts : Array ScanPart) (band : Band) (start : Nat) (data : ByteArray) :
    Except String (FloatArray × Nat) := do
  let f := state.frame
  let mut c := state.coefficients
  let mut cur : Cursor := {reader:={data,pos:=start},predictors:=Array.replicate parts.size 0}
  let single := parts.size == 1
  let first := f.components[(parts[0]!).index]!
  let units := if single then first.ownAcross*first.ownDown else f.mcusAcross*f.mcusDown
  let across := if single then first.ownAcross else f.mcusAcross
  for unit in [0:units] do
    if state.restart > 0 && unit > 0 && unit%state.restart == 0 then
      cur ← nextRestart cur
    let column := unit%across
    let row := unit/across
    if single then
      let block := first.offset+(row*first.across+column)*64
      let (next,after) ← decodeBlock f.progressive (parts[0]!) 0 block band c cur
      c := next
      cur := after
    else
      for slot in [0:parts.size] do
        let part := parts[slot]!
        let comp := f.components[part.index]!
        for v in [0:comp.v] do
          for h in [0:comp.h] do
            let block := comp.offset+((row*comp.v+v)*comp.across+column*comp.h+h)*64
            let (next,after) ← decodeBlock f.progressive part slot block band c cur
            c := next
            cur := after
  return (c,cur.reader.pos)

/-- Start of the next marker at or after `pos`: entropy data ends there. -/
private def nextMarker (d : ByteArray) (pos : Nat) : Nat := Id.run do
  for i in [pos:d.size] do
    if d.get! i == 255 && i+1 < d.size then
      let next := d.get! (i+1)
      if next != 0 && !(next >= 0xD0 && next <= 0xD7) && next != 255 then return i
  return d.size

private def u16 (d : ByteArray) (i : Nat) : Nat := (d.get! i).toNat*256+(d.get! (i+1)).toNat

private def readQuant (state : State) (d : ByteArray) (start stop : Nat) : Except String State := do
  let mut pos := start
  let mut quant := state.quant
  for _ in [0:5] do
    if pos >= stop then break
    let pq := (d.get! pos).toNat/16
    let tq := (d.get! pos).toNat%16
    if pq > 1 || tq > 3 then throw "JPEG quantisation table is not valid"
    pos := pos+1
    if pos+64*(pq+1) > stop then throw "JPEG quantisation table runs past its segment"
    let mut table : Array Float := Array.replicate 64 1
    for i in [0:64] do
      let value := if pq == 0 then (d.get! (pos+i)).toNat else u16 d (pos+i*2)
      table := table.set! zigzag[i]! (Float.ofNat value)
    quant := quant.set! tq table
    pos := pos+64*(pq+1)
  return {state with quant}

private def readHuffman (state : State) (d : ByteArray) (start stop : Nat) : Except String State := do
  let mut pos := start
  let mut s := state
  for _ in [0:9] do
    if pos >= stop then break
    if pos+17 > stop then throw "JPEG Huffman table runs past its segment"
    let kind := (d.get! pos).toNat/16
    let slot := (d.get! pos).toNat%16
    if kind > 1 || slot > 3 then throw "JPEG Huffman table is not valid"
    let counts := (Array.range 16).map fun i => (d.get! (pos+1+i)).toNat
    let total := counts.foldl (·+·) 0
    if total > 256 || pos+17+total > stop then throw "JPEG Huffman table runs past its segment"
    let table := Huffman.build counts (d.extract (pos+17) (pos+17+total))
    if kind == 0 then s := {s with dc:=s.dc.set! slot table}
    else s := {s with ac:=s.ac.set! slot table}
    pos := pos+17+total
  return s

/-- Frame header (T.81 B.2.2). All sizes are checked here, then the store is made. -/
private def readFrame (state : State) (d : ByteArray) (start stop : Nat) (progressive : Bool) : Except String State := do
  if !state.frame.components.isEmpty then throw "JPEG has two frames"
  if start+6 > stop then throw "JPEG frame header is too short"
  if d.get! start != 8 then throw "JPEG sample precision is not 8 bits"
  let height := u16 d (start+1)
  let width := u16 d (start+3)
  let count := (d.get! (start+5)).toNat
  if width == 0 || height == 0 then throw "JPEG has no pixels; a DNL marker is not supported"
  if width*height > maxImagePixels then throw s!"JPEG exceeds {maxImagePixels} pixels"
  if count != 1 && count != 3 then throw "JPEG component count is not 1 or 3"
  if start+6+count*3 > stop then throw "JPEG frame header is too short"
  let mut components : Array Component := #[]
  for i in [0:count] do
    let at_ := start+6+i*3
    let sampling := (d.get! (at_+1)).toNat
    let h := sampling/16
    let v := sampling%16
    let quant := (d.get! (at_+2)).toNat
    if h == 0 || v == 0 || h > 4 || v > 4 || quant > 3 then throw "JPEG component header is not valid"
    components := components.push {id:=(d.get! at_).toNat,h,v,quant}
  -- T.81 A.2.2: a single component has no MCU padding of its sampling factors.
  if count == 1 then components := components.map ({· with h:=1,v:=1})
  let hMax := components.foldl (fun m c => max m c.h) 1
  let vMax := components.foldl (fun m c => max m c.v) 1
  let mcusAcross := (width+8*hMax-1)/(8*hMax)
  let mcusDown := (height+8*vMax-1)/(8*vMax)
  let mut total := 0
  let mut sized : Array Component := #[]
  for c in components do
    let across := mcusAcross*c.h
    let down := mcusDown*c.v
    let ownAcross := ((width*c.h+hMax-1)/hMax+7)/8
    let ownDown := ((height*c.v+vMax-1)/vMax+7)/8
    sized := sized.push {c with across,down,ownAcross,ownDown,offset:=total}
    total := total+across*down*64
  if total > maxJpegCoefficients then throw s!"JPEG exceeds {maxJpegCoefficients} coefficients"
  let mut store := FloatArray.emptyWithCapacity total
  for _ in [0:total] do store := store.push 0
  return {state with coefficients:=store,frame:={width,height,progressive,components:=sized,hMax,vMax,mcusAcross,mcusDown}}

/-- Scan header (T.81 B.2.3), then the scan. Returns the position after it. -/
private def readScan (state : State) (d : ByteArray) (start stop : Nat) : Except String (State × Nat) := do
  let f := state.frame
  if f.components.isEmpty then throw "JPEG scan comes before its frame"
  if state.scans >= maxJpegScans then throw s!"JPEG exceeds {maxJpegScans} scans"
  if start >= stop then throw "JPEG scan header is too short"
  let count := (d.get! start).toNat
  if count == 0 || count > f.components.size || start+1+count*2+3 > stop then throw "JPEG scan header is not valid"
  let mut parts : Array ScanPart := #[]
  for i in [0:count] do
    let id := (d.get! (start+1+i*2)).toNat
    let tables := (d.get! (start+2+i*2)).toNat
    let some index := f.components.findIdx? (·.id == id) | throw "JPEG scan names an unknown component"
    if tables/16 > 3 || tables%16 > 3 then throw "JPEG scan names an unknown table"
    parts := parts.push {index,dc:=state.dc[tables/16]!,ac:=state.ac[tables%16]!}
  let tail := start+1+count*2
  let band : Band := ⟨(d.get! tail).toNat,(d.get! (tail+1)).toNat,(d.get! (tail+2)).toNat/16,(d.get! (tail+2)).toNat%16⟩
  if f.progressive then
    if band.start > band.stop || band.stop > 63 || band.low > 13 || (band.start == 0 && band.stop != 0) ||
        (band.start > 0 && count != 1) then
      throw "JPEG spectral selection is not valid"
  let (coefficients,pos) ← runScan state parts band stop d
  return ({state with coefficients,scans:=state.scans+1},nextMarker d pos)

/-- cos((2x+1)uπ/16)*C(u)/2, at index x*8+u (T.81 A.3.3). -/
private def cosines : Array Float := Id.run do
  let mut out : Array Float := #[]
  for x in [0:8] do
    for u in [0:8] do
      let scale : Float := if u == 0 then 0.5/Float.sqrt 2 else 0.5
      out := out.push (scale*Float.cos (Float.ofNat ((2*x+1)*u)*3.141592653589793/16))
  return out

/-- Dequantise and inverse-transform each block of a component into a plane of
    samples, `across*8` wide. -/
private def componentPlane (c : FloatArray) (comp : Component) (quant : Array Float) : ByteArray := Id.run do
  let stride := comp.across*8
  let mut plane := zeroBytes (stride*comp.down*8)
  let mut work := FloatArray.emptyWithCapacity 64
  for _ in [0:64] do work := work.push 0
  for by_ in [0:comp.down] do
    for bx in [0:comp.across] do
      let block := comp.offset+(by_*comp.across+bx)*64
      -- Rows first: `work[v*8+x]` sums over u.
      for v in [0:8] do
        for x in [0:8] do
          let mut sum : Float := 0
          for u in [0:8] do
            let value := c.get! (block+v*8+u)
            if value != 0 then sum := sum+cosines[x*8+u]!*value*quant[v*8+u]!
          work := work.set! (v*8+x) sum
      for y in [0:8] do
        for x in [0:8] do
          let mut sum : Float := 0
          for v in [0:8] do
            sum := sum+cosines[y*8+v]!*work.get! (v*8+x)
          plane := plane.set! ((by_*8+y)*stride+bx*8+x) (sum+128).round.toUInt8
  return plane

/-- Upsample by repetition and convert to RGB (JFIF §7, Adobe APP14). -/
private def assemble (s : State) : Bitmap := Id.run do
  let f := s.frame
  let planes := f.components.map fun comp => componentPlane s.coefficients comp s.quant[comp.quant]!
  let mut out := zeroBytes (f.width*f.height*4)
  let ids := f.components.map (·.id)
  let rgb := s.adobeTransform == some 0 || ids == #[82,71,66]
  let grey := f.components.size == 1
  for y in [0:f.height] do
    for x in [0:f.width] do
      let value := fun (i : Nat) =>
        let comp := f.components[i]!
        Float.ofNat ((planes[i]!).get! ((y*comp.v/f.vMax)*comp.across*8+x*comp.h/f.hMax)).toNat
      let at_ := (y*f.width+x)*4
      let (r,g,b) : Float × Float × Float :=
        if grey then let v := value 0; (v,v,v)
        else if rgb then (value 0,value 1,value 2)
        else
          let luma := value 0
          let cb := value 1-128
          let cr := value 2-128
          (luma+1.402*cr,luma-0.344136*cb-0.714136*cr,luma+1.772*cb)
      out := (((out.set! at_ r.round.toUInt8).set! (at_+1) g.round.toUInt8).set! (at_+2) b.round.toUInt8).set! (at_+3) 255
  return {width:=f.width,height:=f.height,rgba:=out}

/-- Decode a JPEG file to pixels. A refusal names what is wrong. -/
def decodeJPEG (d : ByteArray) : Except String Bitmap := do
  if d.size > maxImageBytes then throw s!"JPEG exceeds {maxImageBytes} bytes"
  if d.size < 4 || d.get! 0 != 0xFF || d.get! 1 != 0xD8 then throw "not a JPEG start of image"
  let mut state : State := {}
  let mut pos := 2
  -- A segment takes at least 2 bytes, so this bound does not stop a valid file.
  for _ in [0:d.size/2+1] do
    if pos+2 > d.size then break
    if d.get! pos != 0xFF then
      pos := nextMarker d pos
      continue
    let marker := (d.get! (pos+1)).toNat
    if marker == 0xFF then
      pos := pos+1
      continue
    if marker == 0xD9 then break
    if marker == 0xD8 || marker == 0x01 || (marker >= 0xD0 && marker <= 0xD7) || marker == 0 then
      pos := pos+2
      continue
    if pos+4 > d.size then throw "JPEG ends inside a segment"
    let length := u16 d (pos+2)
    let start := pos+4
    let stop := pos+2+length
    if length < 2 || stop > d.size then throw "JPEG segment runs past the end of the data"
    match marker with
    | 0xDB => state ← readQuant state d start stop
    | 0xC4 => state ← readHuffman state d start stop
    | 0xC0 | 0xC1 => state ← readFrame state d start stop false
    | 0xC2 => state ← readFrame state d start stop true
    | 0xDD =>
      if length != 4 then throw "JPEG restart interval segment is not valid"
      state := {state with restart:=u16 d start}
    | 0xEE =>
      if length >= 14 && (d.extract start (start+5)).toList == [65,100,111,98,101] then
        let transform := (d.get! (start+11)).toNat
        if transform > 1 then throw "JPEG YCCK is not supported"
        state := {state with adobeTransform:=some transform}
    | 0xDA =>
      let (next,after) ← readScan state d start stop
      state := next
      pos := after
      continue
    | _ =>
      if marker >= 0xC3 && marker <= 0xCF then
        throw s!"JPEG process with marker {marker} is not supported (arithmetic, lossless or hierarchical)"
    pos := stop
  if state.scans == 0 then throw "JPEG has no scan"
  return assemble state

end NativeImage
