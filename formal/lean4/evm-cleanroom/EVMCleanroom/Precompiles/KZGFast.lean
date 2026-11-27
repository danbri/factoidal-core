import EVMCleanroom.Precompiles.KZG
import EVMCleanroom.Precompiles.BLS12381Map

/-!
# KZG point evaluation: helpers on limbs

Parts of `KZG.lean` (precompile 0x0a) on the six-limb Montgomery field, for the
fast pairing path to assemble; `KZG.lean` stays the definition.

* `decompressG1`: the 48-byte compressed encoding with the same rules as
  `KZG.decompressG1`; the square root is a windowed power on limbs and the
  subgroup check is the endomorphism test of `BLS12381Fast.lean` (a published
  criterion that is not proved here; see that module).
* `mulG1 k = [k]G₁` and `mulG2 k = [k]G₂` for the two generators, from
  tables of the multiples `d·16^i` (`d = 1 … 15`, `i = 0 … 63`) in affine
  form: at most 64 mixed additions and no doubling for a scalar below `2^256`.
  The tables are public constants. Each is built on first use (a thunk), in
  about a thousand point additions and one field inversion (Montgomery's
  trick, in `batchToAffine`), so a program that never verifies a KZG proof
  does not pay for them.
* `commitmentMinusY` and `setupMinusZ`: the two points `C − [y]G₁` and
  `[τ]G₂ − [z]G₂` of the pairing equation.

Tested against the definition, not proved equal: guards below and the
differential run of `evm-blsops`.

Proved: the table index stays inside the table for every digit.

Not constant-time.
-/

namespace EVMCleanroom.Precompiles.Curve

variable {F : Type}

@[specialize] def prefixLoop (O : FieldOps F) (points : Array (JPoint F)) (count : Nat) :
    Nat → F → Array F → Array F
  | 0, _, out => out
  | n+1, acc, out =>
    match points[count - (n + 1)]? with
    | none => out
    | some point =>
      let acc := O.mul acc point.z
      prefixLoop O points count n acc (out.push acc)

@[specialize] def backLoop (O : FieldOps F) (points : Array (JPoint F)) (prefixes : Array F) :
    Nat → F → Array (F × F) → Array (F × F)
  | 0, _, out => out
  | i+1, inverse, out =>
    match points[i]? with
    | none => out
    | some point =>
      let zi := if i = 0 then inverse else O.mul inverse (prefixes.getD (i - 1) O.one)
      let zi2 := O.sqr zi
      backLoop O points prefixes i (O.mul inverse point.z)
        (out.push (O.mul point.x zi2, O.mul point.y (O.mul zi2 zi)))

/-- Affine coordinates of Jacobian points, none of which is the point at infinity, with one
    field inversion (Montgomery's trick: invert the product of all `Z`, then peel off one
    factor per point). -/
@[specialize] def batchToAffine (O : FieldOps F) (points : Array (JPoint F)) : Array (F × F) :=
  let prefixes := prefixLoop O points points.size points.size O.one #[]
  (backLoop O points prefixes points.size (O.inv (prefixes.getD (points.size - 1) O.one)) #[]).reverse

/-- The multiples `[1]B, …, [15]B` appended to `out`; returns also `[16]B`. -/
@[specialize] def fixedRow (O : FieldOps F) (base : JPoint F) : Nat → JPoint F → Array (JPoint F) →
    JPoint F × Array (JPoint F)
  | 0, last, out => (add O last base, out)
  | count+1, last, out =>
    let next := add O last base
    fixedRow O base count next (out.push next)

@[specialize] def fixedRows (O : FieldOps F) : Nat → JPoint F → Array (JPoint F) → Array (JPoint F)
  | 0, _, out => out
  | windows+1, base, out =>
    let row := fixedRow O base 15 (infinity O) out
    fixedRows O windows row.1 row.2

/-- Position of the multiple `d·16^i` in a fixed-base table (`1 ≤ d ≤ 15`). -/
def fixedIndex (window digit : Nat) : Nat := 15 * window + (digit - 1)

/-- The affine multiples `d·16^i` of `(x, y)` for `i < windows`, `d = 1 … 15`, at `fixedIndex i d`.
    None of the multiples may be the point at infinity. -/
@[specialize] def fixedTable (O : FieldOps F) (x y : F) (windows : Nat) : Array (F × F) :=
  batchToAffine O (fixedRows O windows (ofAffine O x y) #[])

@[specialize] def fixedMulLoop (O : FieldOps F) (table : Array (F × F)) (k : Nat) : Nat → JPoint F → JPoint F
  | 0, acc => acc
  | i+1, acc =>
    let digit := (k >>> (4 * i)) % 16
    fixedMulLoop O table k i
      (if digit = 0 then acc
       else match table[fixedIndex i digit]? with
         | some entry => addMixed O acc entry.1 entry.2
         | none => acc)

/-- Kind: index bound.
    Says: for a window below `windows` and a digit from 1 to 15 the table position is
    below `15·windows`, the size of the table, and distinct (window, digit) pairs have
    distinct positions.
    Does not say: the table entries are the stated multiples. -/
theorem fixedIndex_lt (windows window digit : Nat) (hw : window < windows) (h1 : 1 ≤ digit) (h15 : digit ≤ 15) :
    fixedIndex window digit < 15 * windows := by
  unfold fixedIndex; omega

theorem fixedIndex_injective (w1 d1 w2 d2 : Nat) (h1 : 1 ≤ d1 ∧ d1 ≤ 15) (h2 : 1 ≤ d2 ∧ d2 ≤ 15)
    (h : fixedIndex w1 d1 = fixedIndex w2 d2) : w1 = w2 ∧ d1 = d2 := by
  unfold fixedIndex at h; omega

#print axioms fixedIndex_lt
#print axioms fixedIndex_injective

end EVMCleanroom.Precompiles.Curve

namespace EVMCleanroom.Precompiles.KZG.Fast

open BLS12381 (p r)
open BLS12381.Fast (M fp fp2 four inSubgroup1 toLimbs2 ofLimbs2 fmul fsqr fadd fneg toMont fromMont)

/-- `(p − 1)/2` as plain limbs: a canonical `y` above it is the larger of the two roots. -/
def halfP : U384 := U384.ofNat ((p - 1) / 2)

/-- Decompress a 48-byte `G1` point at `off`, in Montgomery form. Outer `none`: invalid
    encoding, off the curve, or outside the subgroup. Inner `none`: the point at infinity. -/
def decompressG1 (data : ByteArray) (off : Nat) : Option (Option (U384 × U384)) :=
  let first := byteAt data off
  let compressed := first &&& 0x80 != 0
  let infinity := first &&& 0x40 != 0
  let larger := first &&& 0x20 != 0
  let raw := U384.ofBE data off
  let x : U384 := { raw with l5 := raw.l5 &&& 0x1fffffffffffffff }
  if !compressed then none
  else if infinity then (if x.isZero && !larger then some none else none)
  else if !U384.lt x M.n then none
  else
    let xm := toMont x
    match BLS12381.Fast.sqrt1? (fadd (fmul (fsqr xm) xm) four) with
    | none => none
    | some root =>
      let y := if U384.lt halfP (fromMont root) == larger then root else fneg root
      if inSubgroup1 xm y then some (some (xm, y)) else none

/-- The generators in Montgomery form. -/
def g1x : U384 := M.ofNat BLS12381.g1Generator.1
def g1y : U384 := M.ofNat BLS12381.g1Generator.2
def g2x : Q2 U384 := toLimbs2 BLS12381.g2Generator.1
def g2y : Q2 U384 := toLimbs2 BLS12381.g2Generator.2

set_option compiler.extract_closed false in
/-- Fixed-base table of `G₁`, built on first use (closed-term extraction is off for this
    definition, so the table is not built when the program starts). -/
def table1 : Thunk (Array (U384 × U384)) := Thunk.mk fun _ => Curve.fixedTable fp g1x g1y 64

set_option compiler.extract_closed false in
/-- Fixed-base table of `G₂`, built on first use. -/
def table2 : Thunk (Array (Q2 U384 × Q2 U384)) := Thunk.mk fun _ => Curve.fixedTable fp2 g2x g2y 64

/-- `[k]G₁`. -/
def mulG1 (k : Nat) : JPoint U384 :=
  if k < 2 ^ 256 then Curve.fixedMulLoop fp table1.get k 64 (Curve.infinity fp)
  else Curve.windowMul fp k g1x g1y

/-- `[k]G₂`. -/
def mulG2 (k : Nat) : JPoint (Q2 U384) :=
  if k < 2 ^ 256 then Curve.fixedMulLoop fp2 table2.get k 64 (Curve.infinity fp2)
  else Curve.windowMul fp2 k g2x g2y

/-- `[τ]G₂` of the ceremony in Montgomery form. -/
def setupX : Q2 U384 := toLimbs2 KZG.setupG2.1
def setupY : Q2 U384 := toLimbs2 KZG.setupG2.2

/-- `C − [y]G₁` for a decoded commitment and a scalar below `r`. -/
def commitmentMinusY (commitment : Option (U384 × U384)) (y : Nat) : JPoint U384 :=
  let multiple := mulG1 ((r - y) % r)
  match commitment with
  | none => multiple
  | some point => Curve.addMixed fp multiple point.1 point.2

/-- `[τ]G₂ − [z]G₂` for a scalar below `r`. -/
def setupMinusZ (z : Nat) : JPoint (Q2 U384) :=
  Curve.addMixed fp2 (mulG2 ((r - z) % r)) setupX setupY

/-! ### Guards against the definition -/

private def toNat1 (point : JPoint U384) : Option (Nat × Nat) :=
  (Curve.toAffineFast fp point).map fun a => (M.toNat a.1, M.toNat a.2)
private def toNat2 (point : JPoint (Q2 U384)) : Option (Fp2 × Fp2) :=
  (Curve.toAffineFast fp2 point).map fun a => (ofLimbs2 a.1, ofLimbs2 a.2)
private def ref1 (k : Nat) : Option (Nat × Nat) :=
  Curve.toAffine BLS12381.field
    (Curve.mul BLS12381.field k (Curve.ofAffine BLS12381.field BLS12381.g1Generator.1 BLS12381.g1Generator.2))
private def ref2 (k : Nat) : Option (Fp2 × Fp2) :=
  Curve.toAffine BLS12381.field2
    (Curve.mul BLS12381.field2 k (Curve.ofAffine BLS12381.field2 BLS12381.g2Generator.1 BLS12381.g2Generator.2))
private def decompressAgrees (text : String) : Bool :=
  (decompressG1 (hex text) 0).map (fun inner => inner.map fun a => (M.toNat a.1, M.toNat a.2)) ==
    KZG.decompressG1 (hex text) 0
private def big : Nat := 0x5f0e1d2c3b4a5968778695a4b3c2d1e0f0123456789abcdeffedcba9876543210
/-- The compressed generator without its first hexadecimal digit (9: compressed, smaller root). -/
private def gTail : String :=
  "7f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb"
private def gCompressed : String := "9" ++ gTail

#guard table1.get.size == 960 && table2.get.size == 960
#guard [0, 1, 2, 15, 16, 17, r - 1, r, big, 2 ^ 255 + 12345, 2 ^ 256 - 1, 2 ^ 256 + 77].all fun k =>
  toNat1 (mulG1 k) == ref1 k
#guard [0, 1, 16, r - 1, big, 2 ^ 256 - 1, 2 ^ 256 + 77].all fun k => toNat2 (mulG2 k) == ref2 k
#guard decompressAgrees gCompressed && decompressAgrees ("b" ++ gTail) &&
  decompressAgrees ("1" ++ gTail) && decompressAgrees ("d" ++ gTail)
#guard decompressAgrees ("c0" ++ String.ofList (List.replicate 94 '0')) &&
  decompressAgrees ("40" ++ String.ofList (List.replicate 94 '0')) &&
  decompressAgrees ("e0" ++ String.ofList (List.replicate 94 '0')) &&
  decompressAgrees ("c0" ++ String.ofList (List.replicate 93 '0') ++ "1") &&
  decompressAgrees ("80" ++ String.ofList (List.replicate 93 '0') ++ "5") &&
  decompressAgrees ("a0" ++ String.ofList (List.replicate 93 '0') ++ "5") &&
  decompressAgrees ("80" ++ String.ofList (List.replicate 93 '0') ++ "1") &&
  decompressAgrees ("9a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab")
#guard (match decompressG1 (hex gCompressed) 0 with | some (some _) => true | _ => false)
-- x = 5 is on the curve and outside the subgroup: rejected.
#guard (match decompressG1 (hex ("80" ++ String.ofList (List.replicate 93 '0') ++ "5")) 0 with | none => true | _ => false)
#guard toNat1 (commitmentMinusY none 5) == ref1 (r - 5) && toNat1 (commitmentMinusY none 0) == none &&
  toNat1 (commitmentMinusY (some (g1x, g1y)) 1) == none && toNat1 (commitmentMinusY (some (g1x, g1y)) 3) == ref1 (r - 2)
#guard toNat2 (setupMinusZ 0) == some KZG.setupG2 &&
  toNat2 (setupMinusZ 9) ==
    Curve.toAffine BLS12381.field2 (Curve.add BLS12381.field2
      (Curve.ofAffine BLS12381.field2 KZG.setupG2.1 KZG.setupG2.2)
      (Curve.mul BLS12381.field2 (r - 9) (Curve.ofAffine BLS12381.field2 BLS12381.g2Generator.1 BLS12381.g2Generator.2)))

end EVMCleanroom.Precompiles.KZG.Fast
