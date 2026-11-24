import L4Factoidal.Codec.WebP

/-!
The lossy WebP key-frame control prefix (RFC 6386 §§7, 9, 19.2).
The arithmetic decoder reads only its indexed partition. Coefficient partitions
are returned as spans of the source; macroblock and pixel decoding follow them.
-/
namespace L4Factoidal.Codec.VP8

open WebP (Span)

private def arithmeticSplit (range probability : Nat) : Nat :=
  1 + (range-1) * probability / 256

/-- For a normalized range and byte probability, an arithmetic decision has two
nonempty subintervals, even at the extreme allowed probabilities. -/
theorem arithmeticSplit_between (range probability : Nat) (hr : 128 ≤ range)
    (hp : probability < 256) :
    0 < arithmeticSplit range probability ∧ arithmeticSplit range probability < range := by
  have positive : 0 < range-1 := by omega
  have product : (range-1) * probability < (range-1) * 256 :=
    Nat.mul_lt_mul_of_pos_left hp positive
  have divided : (range-1) * probability / 256 < range-1 :=
    (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).2 product
  unfold arithmeticSplit
  omega

private structure Input where
  bytes : ByteArray
  span : Span bytes.size

structure Cursor where
  nextBit : Nat
  range : Nat
  value : Nat
  deriving Repr

private abbrev Read := ReaderT Input (StateT Cursor (Except String))

private def bitAt (input : Input) (bit : Nat) : Except String Nat :=
  if h : bit / 8 < input.span.size then
    let index := input.span.offset + bit / 8
    let octet := input.bytes[index]'(input.span.byteWithin h)
    .ok (octet.toNat / 2 ^ (7 - bit % 8) % 2)
  else .error "truncated VP8 arithmetic partition"

private def readProb (probability : Nat) : Read Bool := do
  let input ← read
  let mut cursor ← get
  if cursor.range < 128 || cursor.range > 255 || probability > 255 ||
      cursor.value ≥ cursor.range * 256 then
    throw "invalid VP8 arithmetic cursor"
  let boundary := arithmeticSplit cursor.range probability
  let one := cursor.value ≥ boundary * 256
  cursor := if one then {cursor with
    range := cursor.range-boundary, value := cursor.value-boundary*256}
    else {cursor with range := boundary}
  for _ in [:7] do
    if cursor.range ≥ 128 then break
    let next ← ofExcept (bitAt input cursor.nextBit)
    cursor := {nextBit := cursor.nextBit+1, range := cursor.range*2, value := cursor.value*2+next}
  set cursor
  return one

private def readLiteral (width : Nat) : Read Nat := do
  let mut value := 0
  for _ in [:width] do
    value := 2*value + if (← readProb 128) then 1 else 0
  return value

private def readDelta (width : Nat) : Read Int := do
  if !(← readProb 128) then return 0
  let magnitude ← readLiteral width
  return if (← readProb 128) then -(Int.ofNat magnitude) else Int.ofNat magnitude

private def deltas (count width : Nat) : Read (Array Int) := do
  let mut out := #[]
  for _ in [:count] do
    out := out.push (← readDelta width)
  return out

structure Segmentation where
  mapUpdate : Bool
  dataUpdate : Bool
  absolute : Bool
  quant : Array Int
  filter : Array Int
  probabilities : Array Nat
  deriving Repr

private def readSegmentation : Read (Option Segmentation) := do
  if !(← readProb 128) then return none
  let mapUpdate ← readProb 128
  let dataUpdate ← readProb 128
  let (absolute, quant, filter) ← if dataUpdate then
      do pure (← readProb 128, ← deltas 4 7, ← deltas 4 6)
    else pure (false, Array.replicate 4 0, Array.replicate 4 0)
  let mut probabilities := #[]
  if mapUpdate then
    for _ in [:3] do
      let probability ← if (← readProb 128) then readLiteral 8 else pure 255
      probabilities := probabilities.push probability
  return some {mapUpdate, dataUpdate, absolute, quant, filter, probabilities}

structure ModeDeltas where
  updated : Bool
  reference : Array Int
  mode : Array Int
  deriving Repr

private def readModeDeltas : Read (Option ModeDeltas) := do
  if !(← readProb 128) then return none
  let updated ← readProb 128
  let (reference, mode) ← if updated then do pure (← deltas 4 6, ← deltas 4 6)
    else pure (Array.replicate 4 0, Array.replicate 4 0)
  return some {updated, reference, mode}

structure Control where
  colorSpace : Bool
  unclamped : Bool
  segmentation : Option Segmentation
  simpleFilter : Bool
  filterLevel : Nat
  sharpness : Nat
  modeDeltas : Option ModeDeltas
  coefficientCount : Nat
  baseQuant : Nat
  quantDeltas : Array Int
  refreshEntropy : Bool
  deriving Repr

private def readControl : Read Control := do
  let colorSpace ← readProb 128
  if colorSpace then throw "reserved VP8 color space"
  let unclamped ← readProb 128
  let segmentation ← readSegmentation
  let simpleFilter ← readProb 128
  let filterLevel ← readLiteral 6
  let sharpness ← readLiteral 3
  let modeDeltas ← readModeDeltas
  let coefficientCount := 2 ^ (← readLiteral 2)
  let baseQuant ← readLiteral 7
  let quantDeltas ← deltas 5 4
  let refreshEntropy ← readProb 128
  return {
    colorSpace, unclamped, segmentation, simpleFilter, filterLevel, sharpness
    modeDeltas, coefficientCount, baseQuant, quantDeltas, refreshEntropy
  }

private def byte (src : ByteArray) (index : Nat) : Nat :=
  (src[index]?.getD 0).toNat

private def le24 (src : ByteArray) (index : Nat) : Nat :=
  byte src index + 256 * byte src (index+1) + 65536 * byte src (index+2)

private def subspan {limit : Nat} (source : Span limit) (offset size : Nat) :
    Except String (Span limit) :=
  if bound : offset+size ≤ source.size then
    have within := source.within
    .ok ⟨source.offset+offset,size,by omega⟩
  else .error "VP8 partition outside payload"

structure Frame (limit : Nat) where
  profile : Nat
  shown : Bool
  controlSpan : Span limit
  control : Control
  continuation : Cursor
  coefficients : Array (Span limit)

/-- Read the static VP8 key-frame prefix and index its coefficient partitions. -/
def inspect (src : ByteArray) (image : WebP.Image src.size) : Except String (Frame src.size) := do
  if image.encoding != .vp8 then throw "VP8 control reader requires a lossy frame"
  let source := image.pixels
  if source.size < 10 || le24 src (source.offset+3) != 0x2a019d then
    throw "invalid VP8 key frame header"
  let tag := le24 src source.offset
  if tag % 2 != 0 then throw "VP8 control reader requires a key frame"
  let profile := tag / 2 % 8
  if profile > 3 then throw "reserved VP8 profile"
  let shown := tag / 16 % 2 == 1
  let controlSpan ← subspan source 10 (tag / 32)
  if controlSpan.size < 2 then throw "truncated VP8 control partition"
  let initial := 256 * byte src controlSpan.offset + byte src (controlSpan.offset+1)
  let (control, continuation) ← ((readControl.run ⟨src,controlSpan⟩).run ⟨16,255,initial⟩)
  let sizeTable := 10 + controlSpan.size
  let mut offset := sizeTable + 3 * (control.coefficientCount-1)
  if offset > source.size then throw "truncated VP8 partition sizes"
  let mut coefficients := #[]
  for i in [:control.coefficientCount-1] do
    let size := le24 src (source.offset+sizeTable+3*i)
    coefficients := coefficients.push (← subspan source offset size)
    offset := offset + size
  let last ← subspan source offset (source.size-offset)
  return {profile, shown, controlSpan, control, continuation, coefficients := coefficients.push last}

#print axioms arithmeticSplit_between

end L4Factoidal.Codec.VP8
