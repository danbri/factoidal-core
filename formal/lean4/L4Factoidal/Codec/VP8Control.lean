import L4Factoidal.Codec.WebP
import L4Factoidal.Codec.VP8Tables

/-!
The lossy WebP key-frame control partition (RFC 6386 §§7, 9, 11, 13, 19).
The arithmetic decoder reads only its indexed partition. The prefix indexes the
separate coefficient partitions, and the prediction reader decodes macroblock
modes and coefficient probabilities. The residual reader streams the decoded
coefficient blocks to a caller in raster order.
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

/-- A flattened coefficient table is ordered by block type, frequency band,
preceding coefficient context and entropy decision node. -/
def coefficientIndex (kind : Fin 4) (band : Fin 8) (context : Fin 3)
    (node : Fin 11) : Fin 1056 :=
  ⟨((kind.val * 8 + band.val) * 3 + context.val) * 11 + node.val, by
    have := kind.isLt
    have := band.isLt
    have := context.isLt
    have := node.isLt
    omega⟩

theorem coefficientIndex_injective
    {kind₁ kind₂ : Fin 4} {band₁ band₂ : Fin 8} {context₁ context₂ : Fin 3}
    {node₁ node₂ : Fin 11}
    (equal : coefficientIndex kind₁ band₁ context₁ node₁ =
      coefficientIndex kind₂ band₂ context₂ node₂) :
    kind₁ = kind₂ ∧ band₁ = band₂ ∧ context₁ = context₂ ∧ node₁ = node₂ := by
  have index := congrArg Fin.val equal
  simp only [coefficientIndex] at index
  have := kind₁.isLt
  have := kind₂.isLt
  have := band₁.isLt
  have := band₂.isLt
  have := context₁.isLt
  have := context₂.isLt
  have := node₁.isLt
  have := node₂.isLt
  refine ⟨Fin.ext ?_, Fin.ext ?_, Fin.ext ?_, Fin.ext ?_⟩ <;> omega

structure Entropy where
  probabilities : Array UInt8
  probabilityCount : probabilities.size = 1056
  skipProbability : Option Nat

def Entropy.probability (entropy : Entropy) (kind : Fin 4) (band : Fin 8)
    (context : Fin 3) (node : Fin 11) : UInt8 :=
  let index := coefficientIndex kind band context node
  entropy.probabilities[index.val]'(by simpa only [entropy.probabilityCount] using index.isLt)

private def readEntropy : Read Entropy := do
  let mut probabilities := #[]
  for i in List.finRange 1056 do
    let update := coefficientUpdateProbabilities[i.val]'(by
      simpa only [coefficientUpdateProbabilities_size] using i.isLt)
    let probability ← if (← readProb update.toNat) then
      pure (UInt8.ofNat (← readLiteral 8))
    else pure (coefficientDefaults[i.val]'(by
      simpa only [coefficientDefaults_size] using i.isLt))
    probabilities := probabilities.push probability
  let skipProbability ← if (← readProb 128) then pure (some (← readLiteral 8)) else pure none
  if count : probabilities.size = 1056 then
    return ⟨probabilities, count, skipProbability⟩
  throw "invalid VP8 coefficient probability count"

inductive IntraMode where
  | dc | trueMotion | vertical | horizontal | leftDown | rightDown | verticalRight
  | verticalLeft | horizontalDown | horizontalUp
  deriving Inhabited, Repr, BEq

/-- RFC 6386 §11.2 subblock context order. -/
def IntraMode.index : IntraMode → Nat
  | .dc => 0
  | .trueMotion => 1
  | .vertical => 2
  | .horizontal => 3
  | .leftDown => 4
  | .rightDown => 5
  | .verticalRight => 6
  | .verticalLeft => 7
  | .horizontalDown => 8
  | .horizontalUp => 9

private theorem IntraMode.index_lt (mode : IntraMode) : mode.index < 10 := by
  cases mode <;> decide

private def readSubblockMode (above left : IntraMode) : Read IntraMode := do
  let offset := (above.index * 10 + left.index) * 9
  let branch (i : Fin 9) := readProb (subblockProbabilities[offset+i.val]'(by
    rw [subblockProbabilities_size]
    have := above.index_lt
    have := left.index_lt
    have := i.isLt
    dsimp [offset]
    omega)).toNat
  if !(← branch 0) then return .dc
  if !(← branch 1) then return .trueMotion
  if !(← branch 2) then return .vertical
  if !(← branch 3) then
    if !(← branch 4) then return .horizontal
    return if (← branch 5) then .verticalRight else .rightDown
  if !(← branch 6) then return .leftDown
  if !(← branch 7) then return .verticalLeft
  return if (← branch 8) then .horizontalUp else .horizontalDown

inductive LumaPrediction where
  | whole (mode : IntraMode)
  | subblocks (modes : Array IntraMode)
  deriving Repr

structure Macroblock where
  segment : Nat
  skipCoefficients : Bool
  luma : LumaPrediction
  chroma : IntraMode
  deriving Repr

private def readSegmentIndex (segmentation : Option Segmentation) : Read Nat := do
  let some s := segmentation | return 0
  if !s.mapUpdate then return 0
  let high ← readProb (s.probabilities[0]?.getD 255)
  let low ← readProb (s.probabilities[if high then 2 else 1]?.getD 255)
  return (if high then 2 else 0) + (if low then 1 else 0)

private def readLumaWhole : Read IntraMode := do
  if (← readProb 156) then
    return if (← readProb 128) then .trueMotion else .horizontal
  return if (← readProb 163) then .vertical else .dc

private def readChroma : Read IntraMode := do
  if !(← readProb 142) then return .dc
  if !(← readProb 114) then return .vertical
  return if (← readProb 183) then .trueMotion else .horizontal

private def readMacroblock (segmentation : Option Segmentation) (skip : Option Nat)
    (above : Array IntraMode) (offset : Nat) (left : Array IntraMode) :
    Read (Macroblock × Array IntraMode × Array IntraMode) := do
  let segment ← readSegmentIndex segmentation
  let skipCoefficients ← match skip with | some probability => readProb probability | none => pure false
  let mut above := above
  let mut left := left
  let luma ← if (← readProb 145) then do
      let mode ← readLumaWhole
      for x in [:4] do
        above := above.set! (offset+x) mode
      left := Array.replicate 4 mode
      pure (.whole mode)
    else do
      let mut modes := #[]
      for y in [:4] do
        let mut previous := left[y]?.getD .dc
        for x in [:4] do
          let column := offset+x
          previous ← readSubblockMode (above[column]?.getD .dc) previous
          above := above.set! column previous
          modes := modes.push previous
        left := left.set! y previous
      pure (.subblocks modes)
  let chroma ← readChroma
  return (⟨segment, skipCoefficients, luma, chroma⟩, above, left)

private theorem macroblockExtent_le (extent : Nat) : (extent+15) / 16 ≤ extent := by
  apply Nat.lt_succ_iff.mp
  apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 16)).2
  omega

/-- The raster has at most one prediction record per source pixel, so the
existing WebP pixel budget also bounds the number of such records. -/
theorem macroblockGrid_capacity (width height : Nat) :
    ((height+15) / 16) * ((width+15) / 16) ≤ width * height := by
  simpa only [Nat.mul_comm height width] using
    Nat.mul_le_mul (macroblockExtent_le height) (macroblockExtent_le width)

structure Prediction (limit : Nat) where
  frame : Frame limit
  entropy : Entropy
  columns : Nat
  rows : Nat
  macroblocks : Array Macroblock
  macroblockCount : macroblocks.size = rows * columns

private def readMacroblocks (control : Control) (entropy : Entropy) (columns rows : Nat) :
    Read (Array Macroblock) := do
  let mut above := Array.replicate (4 * columns) IntraMode.dc
  let mut blocks := Array.emptyWithCapacity (rows * columns)
  for _ in [:rows] do
    let mut left := Array.replicate 4 IntraMode.dc
    for column in [:columns] do
      let (block, nextAbove, nextLeft) ← readMacroblock control.segmentation
        entropy.skipProbability above (4 * column) left
      above := nextAbove
      left := nextLeft
      blocks := blocks.push block
  return blocks

/-- Read entropy updates and prediction records from the first partition.
Residual decoding uses the separately indexed partitions in `frame`. -/
def inspectPrediction (src : ByteArray) (image : WebP.Image src.size) :
    Except String (Prediction src.size) := do
  let frame ← inspect src image
  let columns := (image.width+15) / 16
  let rows := (image.height+15) / 16
  let readPrediction := do
    let entropy ← readEntropy
    let blocks ← readMacroblocks frame.control entropy columns rows
    pure (entropy, blocks)
  let ((entropy, macroblocks), _) ←
    ((readPrediction.run ⟨src,frame.controlSpan⟩).run frame.continuation)
  if count : macroblocks.size = rows * columns then
    return ⟨frame, entropy, columns, rows, macroblocks, count⟩
  throw "invalid VP8 macroblock count"

/-- The coefficient order appearing in the stream is different from the
row-major order consumed by the inverse transforms. -/
def zigzag : Vector (Fin 16) 16 :=
  #v[0, 1, 4, 8, 5, 2, 3, 6, 9, 12, 13, 10, 7, 11, 14, 15]

private def unzigzag : Vector (Fin 16) 16 :=
  #v[0, 1, 5, 6, 2, 4, 7, 12, 3, 8, 11, 13, 9, 10, 14, 15]

private theorem unzigzag_zigzag :
    ∀ i : Fin 16, unzigzag.get (zigzag.get i) = i := by
  simp only [Fin.forall_fin_succ, Fin.forall_fin_zero]
  decide

/-- Decoding a later scan position cannot overwrite another coefficient. -/
theorem zigzag_injective {a b : Fin 16} (equal : zigzag.get a = zigzag.get b) : a = b := by
  have restored := congrArg unzigzag.get equal
  simpa only [unzigzag_zigzag] using restored

private def coefficientBand : Vector (Fin 8) 16 :=
  #v[0, 1, 2, 3, 6, 4, 5, 6, 6, 6, 6, 6, 6, 6, 6, 7]

private def categoryPayload (probabilities : Array Nat) : Read Nat := do
  let mut payload := 0
  for probability in probabilities do
    payload := 2*payload + if (← readProb probability) then 1 else 0
  return payload

private def largeCoefficient (branch : Fin 11 → Read Bool) : Read Nat := do
  if !(← branch 3) then
    if !(← branch 4) then return 2
    return 3 + if (← branch 5) then 1 else 0
  if !(← branch 6) then
    if !(← branch 7) then return 5 + (← categoryPayload #[159])
    return 7 + (← categoryPayload #[165,145])
  let upper ← branch 8
  let lower ← branch (if upper then 10 else 9)
  if !upper then
    if !lower then return 11 + (← categoryPayload #[173,148,140])
    return 19 + (← categoryPayload #[176,155,140,135])
  if !lower then return 35 + (← categoryPayload #[180,157,141,134,130])
  return 67 + (← categoryPayload #[254,254,243,230,196,177,153,140,133,130,129])

abbrev CoefficientBlock := Vector Int 16

private def readCoefficientBlock (entropy : Entropy) (kind : Fin 4) (first : Nat)
    (initialContext : Fin 3) : Read (CoefficientBlock × Bool) := do
  let mut values := Vector.replicate 16 (0 : Int)
  let mut context := initialContext
  let mut previousZero := false
  let mut occupied := false
  for position in List.finRange 16 do
    if position.val < first then continue
    let branch := fun node => readProb
      (entropy.probability kind (coefficientBand.get position) context node).toNat
    if !previousZero then
      if !(← branch 0) then break
    if !(← branch 1) then
      context := 0
      previousZero := true
    else
      let magnitude ← if (← branch 2) then largeCoefficient branch else pure 1
      let value := Int.ofNat magnitude
      let value := if (← readProb 128) then -value else value
      let index := zigzag.get position
      values := values.set index.val value index.isLt
      context := if magnitude == 1 then 1 else 2
      previousZero := false
      occupied := true
  return (values, occupied)

private structure Occupancy where
  y2 : Bool := false
  planes : Vector Bool 8 := Vector.replicate 8 false
  deriving Inhabited

private def occupiedContext (above left : Bool) : Fin 3 :=
  ⟨(if above then 1 else 0) + (if left then 1 else 0), by
    cases above <;> cases left <;> decide⟩

private def readPlane (entropy : Entropy) (kind : Fin 4) (first side offset : Nat)
    (above left : Vector Bool 8) :
    Read (Array CoefficientBlock × Vector Bool 8 × Vector Bool 8) := do
  let mut above := above
  let mut left := left
  let mut result := Array.emptyWithCapacity (side * side)
  for y in [:side] do
    for x in [:side] do
      let topIndex := offset+x
      let leftIndex := offset+y
      let context := occupiedContext (above.getD topIndex false) (left.getD leftIndex false)
      let (coefficients, occupied) ← readCoefficientBlock entropy kind first context
      above := above.setIfInBounds topIndex occupied
      left := left.setIfInBounds leftIndex occupied
      result := result.push coefficients
  return (result, above, left)

structure Residual where
  y2 : Option CoefficientBlock
  yuv : Array CoefficientBlock
  blockCount : yuv.size = 24

private def hasLumaDC : LumaPrediction → Bool
  | .whole _ => true
  | .subblocks _ => false

private def skipOccupancy (hasDC : Bool) (above : Occupancy) : Occupancy :=
  {y2 := !hasDC && above.y2}

private def readResidual (entropy : Entropy) (hasDC : Bool) (above left : Occupancy) :
    Read (Residual × Occupancy × Occupancy) := do
  let (y2, aboveDC, leftDC) ← if hasDC then do
    let (coefficients, occupied) ←
      readCoefficientBlock entropy 1 0 (occupiedContext above.y2 left.y2)
    pure (some coefficients, occupied, occupied)
  else pure (none, above.y2, left.y2)
  let (y, above, left) ← readPlane entropy (if hasDC then 0 else 3)
    (if hasDC then 1 else 0) 4 0 above.planes left.planes
  let (u, above, left) ← readPlane entropy 2 0 2 4 above left
  let (v, above, left) ← readPlane entropy 2 0 2 6 above left
  let yuv := y ++ u ++ v
  if count : yuv.size = 24 then
    return (⟨y2,yuv,count⟩, ⟨aboveDC,above⟩, ⟨leftDC,left⟩)
  throw "invalid VP8 residual block count"

private def beginResidual (src : ByteArray) (span : Span src.size) : Except String Cursor := do
  if span.size < 2 then throw "truncated VP8 coefficient partition"
  return ⟨16,255,256 * byte src span.offset + byte src (span.offset+1)⟩

/-- Decode keyframe residuals in raster order. The consumer sees one macroblock
at a time. Each coefficient partition has an independent cursor and the above
and left occupancy contexts follow the raster across partition boundaries. -/
def foldResiduals (src : ByteArray) (image : WebP.Image src.size) (initial : α)
    (visit : α → Control → Nat → Nat → Macroblock → Option Residual → Except String α) :
    Except String α := do
  let prediction ← inspectPrediction src image
  let partitions := prediction.frame.coefficients
  let mut cursors : Array (Option Cursor) := Array.replicate partitions.size none
  let mut above : Array Occupancy := Array.replicate prediction.columns {}
  let mut state := initial
  for row in [:prediction.rows] do
    let partIndex := row % partitions.size
    let some partition := partitions[partIndex]? | throw "missing VP8 coefficient partition"
    let mut cursor := cursors[partIndex]?.join
    let mut left : Occupancy := {}
    for column in [:prediction.columns] do
      let some block := prediction.macroblocks[row * prediction.columns + column]? |
        throw "missing VP8 prediction record"
      let top := above[column]?.getD {}
      let hasDC := hasLumaDC block.luma
      if block.skipCoefficients then
        above := above.set! column (skipOccupancy hasDC top)
        left := skipOccupancy hasDC left
        state ← visit state prediction.frame.control row column block none
      else
        let started ← match cursor with
          | some active => pure active
          | none => beginResidual src partition
        let ((residual, nextTop, nextLeft), nextCursor) ←
          ((readResidual prediction.entropy hasDC top left).run ⟨src,partition⟩).run started
        cursor := some nextCursor
        above := above.set! column nextTop
        left := nextLeft
        state ← visit state prediction.frame.control row column block (some residual)
    cursors := cursors.set! partIndex cursor
  return state

#print axioms zigzag_injective

#print axioms arithmeticSplit_between
#print axioms coefficientIndex_injective
#print axioms macroblockGrid_capacity

end L4Factoidal.Codec.VP8
