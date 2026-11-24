import L4Factoidal.Codec.VP8Transform

/-!
VP8 keyframe intra prediction and addition of spatial residuals (RFC 6386
§§12 and 14.5). The three padded planes retain unfiltered reconstruction;
the loop filter operates on those planes in a later stage.
-/
namespace L4Factoidal.Codec.VP8

def clipSample (value : Int) : UInt8 :=
  UInt8.ofNat (min 255 value.toNat)

theorem clipSample_toNat (value : Int) :
    (clipSample value).toNat = min 255 value.toNat := by
  have bounded : min 255 value.toNat < 256 := Nat.lt_of_le_of_lt (Nat.min_le_left _ _) (by decide)
  rw [clipSample, UInt8.toNat_ofNat']
  exact Nat.mod_eq_of_lt bounded

structure BlockEdges where
  above : Vector Int 8
  left : Vector Int 4
  corner : Int

private def boundary (edges : BlockEdges) (position : Int) : Int :=
  if position < 0 then edges.left.getD (-position-1).toNat 129
  else if position == 0 then edges.corner
  else edges.above.getD (position-1).toNat 127

private def average2 (a b : Int) : Int := (a+b+1)/2
private def average3 (a b c : Int) : Int := (a+2*b+c+2)/4

private def around (edge : Int → Int) (position : Int) : Int :=
  average3 (edge (position-1)) (edge position) (edge (position+1))

private def verticalRight (edge : Int → Int) (x y : Int) : Int :=
  let position := 2*x-y
  if position < 0 then average3 (edge position) (edge (position+1)) (edge (position+2))
  else
    let half := position / 2
    if position % 2 == 0 then average2 (edge half) (edge (half+1))
    else average3 (edge half) (edge (half+1)) (edge (half+2))

/-- The ten VP8 4×4 predictors, in row-major order. -/
def predict4 (mode : IntraMode) (edges : BlockEdges) (row col : Fin 4) : Int :=
  let x := Int.ofNat col.val
  let y := Int.ofNat row.val
  let top := fun i => edges.above.getD (min i 7) 127
  let left := fun i => edges.left.getD (min i 3) 129
  let ray := boundary edges
  match mode with
  | .dc =>
    let total := (List.finRange 4).foldl
      (fun sum i => sum + top i.val + left i.val) 0
    (total+4)/8
  | .trueMotion =>
    Int.ofNat (clipSample (top col.val + left row.val - edges.corner)).toNat
  | .vertical => around ray (x+1)
  | .horizontal =>
    let preceding := if row.val == 0 then edges.corner else left (row.val-1)
    average3 preceding (left row.val) (left (row.val+1))
  | .leftDown =>
    let index := col.val+row.val
    average3 (top index) (top (index+1)) (top (index+2))
  | .rightDown => around ray (x-y)
  | .verticalRight => verticalRight ray x y
  | .horizontalDown => verticalRight (fun i => ray (-i)) y x
  | .verticalLeft =>
    let index := col.val + row.val/2
    if col.val == 3 && row.val ≥ 2 then
      average3 (top (row.val+2)) (top (row.val+3)) (top (row.val+4))
    else if row.val % 2 == 0 then average2 (top index) (top (index+1))
    else average3 (top index) (top (index+1)) (top (index+2))
  | .horizontalUp =>
    let index := row.val + col.val/2
    if col.val % 2 == 0 then average2 (left index) (left (index+1))
    else average3 (left index) (left (index+1)) (left (index+2))

private def sample (plane : @& ByteArray) (stride x y : Nat) : Int :=
  Int.ofNat ((plane[y*stride+x]?.getD 0).toNat)

private def cornerSample (plane : @& ByteArray) (stride x y : Nat) : Int :=
  if y == 0 then 127 else if x == 0 then 129 else sample plane stride (x-1) (y-1)

private def fourEdges (plane : @& ByteArray) (stride mbX mbY subX subY : Nat) : BlockEdges :=
  let x := mbX+subX
  let y := mbY+subY
  let above := Vector.ofFn fun (i : Fin 8) =>
    if subX == 12 && i.val ≥ 4 then
      -- The four above-right samples for these rightmost subblocks are
      -- taken at the macroblock's top edge for every subblock row.
      if mbY == 0 then 127
      else sample plane stride (if mbX+16 == stride then mbX+15 else x+i.val) (mbY-1)
    else if y == 0 then 127 else sample plane stride (x+i.val) (y-1)
  let left := Vector.ofFn fun (i : Fin 4) =>
    if x == 0 then 129 else sample plane stride (x-1) (y+i.val)
  ⟨above,left,cornerSample plane stride x y⟩

private def wholePredictor (plane : @& ByteArray) (stride x y side : Nat) (mode : IntraMode) :
    Except String (Nat → Nat → Int) := do
  let top := (List.range side).toArray.map fun i =>
    if y == 0 then (127 : Int) else sample plane stride (x+i) (y-1)
  let left := (List.range side).toArray.map fun i =>
    if x == 0 then (129 : Int) else sample plane stride (x-1) (y+i)
  let corner := cornerSample plane stride x y
  match mode with
  | .vertical => return fun _ col => top[col]?.getD 127
  | .horizontal => return fun row _ => left[row]?.getD 129
  | .trueMotion =>
    return fun row col =>
      Int.ofNat (clipSample (top[col]?.getD 127 + left[row]?.getD 129 - corner)).toNat
  | .dc =>
    let total := (if y == 0 then 0 else top.foldl (·+·) 0) +
      (if x == 0 then 0 else left.foldl (·+·) 0)
    let count := (if y == 0 then 0 else side) + (if x == 0 then 0 else side)
    let dc := if count == 0 then 128 else (total + Int.ofNat (count/2)) / Int.ofNat count
    return fun _ _ => dc
  | _ => throw "invalid VP8 macroblock prediction mode"

private def writeBlock (plane : ByteArray) (stride x y : Nat) (predict : Nat → Nat → Int)
    (residual : Option CoefficientBlock) : ByteArray := Id.run do
  let mut plane := plane
  for row in [:4] do
    for col in [:4] do
      let delta := (residual.map fun block => block.getD (row*4+col) 0).getD 0
      let value := clipSample (predict row col + delta)
      plane := plane.set! ((y+row)*stride+x+col) value
  return plane

private def wholeBlock (plane : ByteArray) (stride x y blockSide blockOffset : Nat)
    (mode : IntraMode) (residual : Option SpatialResidual) : Except String ByteArray := do
  let predict ← wholePredictor plane stride x y (4*blockSide) mode
  let mut plane := plane
  for row in [:blockSide] do
    for col in [:blockSide] do
      let offset := blockOffset+row*blockSide+col
      let delta := residual.map fun blocks => blocks.getD offset (Vector.replicate 16 0)
      plane := writeBlock plane stride (x+col*4) (y+row*4)
        (fun j i => predict (row*4+j) (col*4+i)) delta
  return plane

private def subblocks (plane : ByteArray) (stride x y : Nat) (modes : Array IntraMode)
    (residual : Option SpatialResidual) : Except String ByteArray := do
  let mut plane := plane
  for row in [:4] do
    for col in [:4] do
      let offset := row*4+col
      let some mode := modes[offset]? | throw "missing VP8 luma subblock prediction"
      let edges := fourEdges plane stride x y (4*col) (4*row)
      let delta := residual.map fun blocks => blocks.getD offset (Vector.replicate 16 0)
      plane := writeBlock plane stride (x+4*col) (y+4*row)
        (fun j i => predict4 mode edges (Fin.ofNat 4 j) (Fin.ofNat 4 i)) delta
  return plane

structure FilterBlock where
  segment : Nat
  intra4 : Bool
  inner : Bool

structure Reconstructed where
  columns : Nat
  rows : Nat
  y : ByteArray
  u : ByteArray
  v : ByteArray
  control : Option Control := none
  filterBlocks : Array FilterBlock := #[]

private def zeroPlane (size : Nat) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity size
  for _ in [:size] do
    bytes := bytes.push 0
  return bytes

private def reconstructMacroblock (frame : Reconstructed) (control : Control) (row col : Nat)
    (macroblock : Macroblock) (prepared : Option PreparedResidual) : Except String Reconstructed := do
  let ⟨columns, rows, y, u, v, _, filterBlocks⟩ := frame
  let residual := prepared.map PreparedResidual.samples
  let y ← match macroblock.luma with
    | .whole mode => wholeBlock y (columns*16) (col*16) (row*16) 4 0 mode residual
    | .subblocks modes => subblocks y (columns*16) (col*16) (row*16) modes residual
  let u ← wholeBlock u (columns*8) (col*8) (row*8) 2 16 macroblock.chroma residual
  let v ← wholeBlock v (columns*8) (col*8) (row*8) 2 20 macroblock.chroma residual
  let intra4 := match macroblock.luma with
    | .whole _ => false
    | .subblocks _ => true
  let inner := intra4 || prepared.any PreparedResidual.hasCoefficients
  let filterBlocks := if control.filterLevel == 0 then filterBlocks
    else filterBlocks.push ⟨macroblock.segment,intra4,inner⟩
  return ⟨columns,rows,y,u,v,some control,filterBlocks⟩

/-- Reconstruct the padded YUV420 planes before filtering. -/
def reconstruct (src : ByteArray) (image : WebP.Image src.size) : Except String Reconstructed := do
  let columns := (image.width+15)/16
  let rows := (image.height+15)/16
  let blocks := columns*rows
  let y := zeroPlane (blocks*256)
  let u := zeroPlane (blocks*64)
  let v := zeroPlane (blocks*64)
  foldPreparedResiduals src image ⟨columns,rows,y,u,v,none,#[]⟩ reconstructMacroblock

#print axioms clipSample_toNat

end L4Factoidal.Codec.VP8
