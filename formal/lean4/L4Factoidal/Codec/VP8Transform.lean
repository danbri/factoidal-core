import L4Factoidal.Codec.VP8Control

/-!
Integer dequantisation and inverse 4×4 transforms for VP8 keyframes
(RFC 6386 §§9.6 and 14). The outputs are signed residual samples in
macroblock transform order, before adding the prediction or loop filtering.
-/
namespace L4Factoidal.Codec.VP8

private def dcQuant : Vector Int 128 := #v[
    4,   5,   6,   7,   8,   9,  10,  10,
   11,  12,  13,  14,  15,  16,  17,  17,
   18,  19,  20,  20,  21,  21,  22,  22,
   23,  23,  24,  25,  25,  26,  27,  28,
   29,  30,  31,  32,  33,  34,  35,  36,
   37,  37,  38,  39,  40,  41,  42,  43,
   44,  45,  46,  46,  47,  48,  49,  50,
   51,  52,  53,  54,  55,  56,  57,  58,
   59,  60,  61,  62,  63,  64,  65,  66,
   67,  68,  69,  70,  71,  72,  73,  74,
   75,  76,  76,  77,  78,  79,  80,  81,
   82,  83,  84,  85,  86,  87,  88,  89,
   91,  93,  95,  96,  98, 100, 101, 102,
  104, 106, 108, 110, 112, 114, 116, 118,
  122, 124, 126, 128, 130, 132, 134, 136,
  138, 140, 143, 145, 148, 151, 154, 157
]

private def acQuant : Vector Int 128 := #v[
    4,   5,   6,   7,   8,   9,  10,  11,
   12,  13,  14,  15,  16,  17,  18,  19,
   20,  21,  22,  23,  24,  25,  26,  27,
   28,  29,  30,  31,  32,  33,  34,  35,
   36,  37,  38,  39,  40,  41,  42,  43,
   44,  45,  46,  47,  48,  49,  50,  51,
   52,  53,  54,  55,  56,  57,  58,  60,
   62,  64,  66,  68,  70,  72,  74,  76,
   78,  80,  82,  84,  86,  88,  90,  92,
   94,  96,  98, 100, 102, 104, 106, 108,
  110, 112, 114, 116, 119, 122, 125, 128,
  131, 134, 137, 140, 143, 146, 149, 152,
  155, 158, 161, 164, 167, 170, 173, 177,
  181, 185, 189, 193, 197, 201, 205, 209,
  213, 217, 221, 225, 229, 234, 239, 245,
  249, 254, 259, 264, 269, 274, 279, 284
]

private def clampQuant (limit : Fin 128) (value : Int) : Fin 128 :=
  ⟨min value.toNat limit.val, Nat.lt_of_le_of_lt (Nat.min_le_right ..) limit.isLt⟩

structure QuantFactors where
  yDC : Int
  yAC : Int
  y2DC : Int
  y2AC : Int
  uvDC : Int
  uvAC : Int

def quantFactors (control : Control) (segment : Nat) : QuantFactors :=
  let base := Int.ofNat control.baseQuant
  let quant := match control.segmentation with
    | none => base
    | some s =>
      let delta := s.quant[segment]?.getD 0
      if s.absolute then delta else base + delta
  let delta := fun i => control.quantDeltas[i]?.getD 0
  let atDC := fun limit n => dcQuant.get (clampQuant limit n)
  let atAC := fun n => acQuant.get (clampQuant 127 n)
  ⟨atDC 127 (quant + delta 0), atAC quant,
   2 * atDC 127 (quant + delta 1), max 8 (atAC (quant + delta 2) * 155 / 100),
   atDC 117 (quant + delta 3), atAC (quant + delta 4)⟩

/-- Coefficients are stored as signed 16-bit values after dequantisation. -/
def signedCoefficient16 (value : Int) : Int :=
  (value + 32768) % 65536 - 32768

theorem signedCoefficient16_bounds (value : Int) :
    -32768 ≤ signedCoefficient16 value ∧ signedCoefficient16 value < 32768 := by
  unfold signedCoefficient16
  have low := Int.emod_nonneg (value + 32768) (by decide : (65536 : Int) ≠ 0)
  have high := Int.emod_lt_of_pos (value + 32768) (by decide : (0 : Int) < 65536)
  omega

theorem signedCoefficient16_exact (value : Int)
    (low : -32768 ≤ value) (high : value < 32768) : signedCoefficient16 value = value := by
  unfold signedCoefficient16
  rw [Int.emod_eq_of_lt (by omega : 0 ≤ value + 32768) (by omega : value + 32768 < 65536)]
  omega

private def dequantise (dc ac : Int) (block : CoefficientBlock) : CoefficientBlock :=
  Vector.ofFn fun i => signedCoefficient16 (block.get i * (if i.val == 0 then dc else ac))

private abbrev Line := Vector Int 4
private abbrev Butterfly := Int → Int → Int → Int → Line

private def dctButterfly : Butterfly := fun x0 x1 x2 x3 =>
  let mul1 := fun (x : Int) => x * 20091 / 65536 + x
  let mul2 := fun (x : Int) => x * 35468 / 65536
  let sum := x0 + x2
  let diff := x0 - x2
  let even := mul2 x1 - mul1 x3
  let odd := mul1 x1 + mul2 x3
  #v[sum + odd, diff + even, diff - even, sum - odd]

private def whtButterfly : Butterfly := fun x0 x1 x2 x3 =>
  let outerSum := x0 + x3
  let innerSum := x1 + x2
  let innerDiff := x1 - x2
  let outerDiff := x0 - x3
  #v[outerSum + innerSum, outerDiff + innerDiff, outerSum - innerSum, outerDiff - innerDiff]

private def blockIndex (row column : Fin 4) : Fin 16 :=
  ⟨row.val * 4 + column.val, by
    have := row.isLt
    have := column.isLt
    omega⟩

private def inverseTransform (pass : Butterfly) (rounding : Int)
    (block : CoefficientBlock) : CoefficientBlock :=
  let columns : Vector Line 4 := Vector.ofFn fun col =>
    let item := fun row => block.get (blockIndex row col)
    pass (item 0) (item 1) (item 2) (item 3)
  let rows : Vector Line 4 := Vector.ofFn fun row =>
    let item := fun col => (columns.get col).get row
    pass (item 0) (item 1) (item 2) (item 3)
  Vector.ofFn fun index =>
    let row : Fin 4 := ⟨index.val / 4, by have := index.isLt; omega⟩
    let col : Fin 4 := ⟨index.val % 4, by omega⟩
    ((rows.get row).get col + rounding) / 8

def inverseDCT (block : CoefficientBlock) : CoefficientBlock :=
  inverseTransform dctButterfly 4 block

def inverseWHT (block : CoefficientBlock) : CoefficientBlock :=
  (inverseTransform whtButterfly 3 block).map signedCoefficient16

theorem inverseDCT_zero :
    inverseDCT (Vector.replicate 16 0) = Vector.replicate 16 0 := by decide

theorem inverseWHT_zero :
    inverseWHT (Vector.replicate 16 0) = Vector.replicate 16 0 := by
  have zero : inverseTransform whtButterfly 3 (Vector.replicate 16 0) =
      Vector.replicate 16 0 := by decide
  rw [inverseWHT, zero, Vector.map_replicate] <;> rfl

abbrev SpatialResidual := Vector CoefficientBlock 24

structure PreparedResidual where
  samples : SpatialResidual
  hasCoefficients : Bool

/-- Apply the second-order luma transform, then the 16 Y, 4 U and 4 V DCTs.
Keep the decoder's nonzero flag for deciding whether to filter inner edges. -/
def prepareResidual (factors : QuantFactors) (residual : Residual) : PreparedResidual :=
  let dc := residual.y2.map (fun block => inverseWHT (dequantise factors.y2DC factors.y2AC block))
  let blocks : Vector (CoefficientBlock × Bool) 24 := Vector.ofFn fun i =>
    let raw := residual.yuv[i.val]'(by simpa only [residual.blockCount] using i.isLt)
    let input :=
      if isLuma : i.val < 16 then
        let block := dequantise factors.yDC factors.yAC raw
        match dc with
        | none => block
        | some values => block.set 0 (values.get ⟨i.val, isLuma⟩)
      else dequantise factors.uvDC factors.uvAC raw
    let nonzeroAC := raw.toArray.any (· != 0) (start := 1)
    (inverseDCT input, nonzeroAC || input.get 0 != 0)
  ⟨blocks.map Prod.fst, blocks.toArray.any Prod.snd⟩

/-- Feed one macroblock of spatial residuals at a time into reconstruction.
A skipped macroblock needs only its predicted samples. -/
def foldPreparedResiduals (src : ByteArray) (image : WebP.Image src.size) (initial : α)
    (visit : α → Control → Nat → Nat → Macroblock → Option PreparedResidual → Except String α) :
    Except String α :=
  foldResiduals src image initial fun state control row col macroblock residual =>
    let spatial := residual.map (prepareResidual (quantFactors control macroblock.segment))
    visit state control row col macroblock spatial

def foldSpatialResiduals (src : ByteArray) (image : WebP.Image src.size) (initial : α)
    (visit : α → Control → Nat → Nat → Macroblock → Option SpatialResidual → Except String α) :
    Except String α :=
  foldPreparedResiduals src image initial fun state control row col macroblock prepared =>
    visit state control row col macroblock (prepared.map PreparedResidual.samples)

#print axioms signedCoefficient16_bounds
#print axioms signedCoefficient16_exact
#print axioms inverseDCT_zero
#print axioms inverseWHT_zero

end L4Factoidal.Codec.VP8
