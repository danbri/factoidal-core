import EVMCleanroom.Precompiles.BLS12381Fast

/-!
# BLS12-381 multi-scalar multiplication on limbs (0x0c, 0x0e)

The same contract as `BLS12381.runG1Msm` and `runG2Msm` (EIP-2537): every
item is decoded with the curve and subgroup checks (the endomorphism checks
of `BLS12381Fast.lean`), an invalid item fails the call, and the result is
`Σ [kᵢ]Pᵢ`. Scalars are used as given (up to `2^256 − 1`, not reduced).

The definition performs one double-and-add per item. Here every scalar is
reduced modulo `r` and split along the endomorphisms (two 129-bit parts on
`G1`, four 64-bit digits on `G2`; see below), and the sum over the parts is
computed with one shared doubling chain: for few items one table of sixteen
multiples per part (Straus), from 32 items (`G1`) or 12 items (`G2`) on by
the bucket method (Pippenger) with a window chosen by the number of parts. Items whose
point is at infinity or whose scalar is zero contribute nothing and are left
out after validation. The discount table of the price ends at 128 items;
longer inputs use the same code with wider windows.

Tested against the definition, not proved equal (group laws are not proved):
guards below, the differential run of `evm-blsops` for item counts on both
sides of the method switch, and the published vectors.

Proved: input-length rules, gas accounting, output lengths, that an empty
input fails, that every item is decoded exactly once (the decoding loops
recurse on the item count), the splitting identities and the sizes of the
parts, and the pass bounds of `CurveFast.lean`.

Not constant-time.
-/

namespace EVMCleanroom.Precompiles.BLS12381.Fast

/-! ### Scalars split along the endomorphisms

On the order-`r` subgroups the endomorphisms act as multiplications: on `G1`,
`φ'(x, y) = (β²x, y)` is the multiplication by `λ = z² − 1`, and on `G2`,
`ψ` is the multiplication by the curve parameter `−z` (the fact behind the
subgroup checks of `BLS12381Fast.lean`). A scalar is reduced modulo `r` and
written as `k₁ + k₂·λ` (Gallant, Lambert, Vanstone 2001), respectively in base
`z` as `d₀ + d₁z + d₂z² + d₃z³` (Galbraith, Lin, Scott 2009), so that
`[k]P = [k₁]P + [k₂]φ'(P)` and `[k]Q = [d₀]Q + [d₁](−ψQ) + [d₂]ψ²Q + [d₃](−ψ³Q)`
with scalars of 129 and 64 bits and a doubling chain of that length.

Proved below: the two splitting identities on natural numbers and the sizes
of the parts. Not proved: that the endomorphisms act as stated (guards on the
generators; the differential runs compare whole results with the definition).
Both splits are used only for points that passed the subgroup check. -/

/-- `z²`, with `λ = z² − 1`. -/
def zSquared : Nat := 0xac45a4010001a4020000000100000000
/-- `β²`: the cube root of unity with `(β²x, y) = [z² − 1](x, y)` on `G1`. -/
def beta2Nat : Nat :=
  0x1a0111ea397fe699ec02408663d4de85aa0d857d89759ad4897d29650fb85f9b409427eb4f49fffd8bfd00000000aaac
def beta2 : U384 := M.ofNat beta2Nat

/-- `λ = z² − 1`. -/
def lambda1 : Nat := 0xac45a4010001a40200000000ffffffff

/-- `(k₁, k₂)` with `k₁ + k₂·(z² − 1) = m`. -/
def lambdaSplit (m : Nat) : Nat × Nat :=
  (m % 0xac45a4010001a4020000000100000000 + m / 0xac45a4010001a4020000000100000000,
   m / 0xac45a4010001a4020000000100000000)

/-- The four digits of `m` in base `z`. -/
def zDigits (m : Nat) : Nat × Nat × Nat × Nat :=
  (m % 0xd201000000010000, m / 0xd201000000010000 % 0xd201000000010000,
   m / 0xd201000000010000 / 0xd201000000010000 % 0xd201000000010000,
   m / 0xd201000000010000 / 0xd201000000010000 / 0xd201000000010000)

/-- Kind: recoding identity.
    Says: the two parts of a scalar recombine to it with `λ = z² − 1`:
    `k₁ + k₂·λ = m` with the literal `λ = z² − 1` (`lambda1`), for every natural number `m`.
    Does not say: `φ'` acts as the multiplication by `λ` on `G1` (guard, not proved). -/
theorem lambdaSplit_spec (m : Nat) :
    (lambdaSplit m).1 + (lambdaSplit m).2 * 0xac45a4010001a40200000000ffffffff = m := by
  show m % 0xac45a4010001a4020000000100000000 + m / 0xac45a4010001a4020000000100000000 +
    m / 0xac45a4010001a4020000000100000000 * 0xac45a4010001a40200000000ffffffff = m
  omega

/-- Kind: size bound.
    Says: for a scalar below the group order the parts are below `2^129` and `2^128`, so
    33 four-bit windows (132 bits) cover them.
    Does not say: anything about the group. -/
theorem lambdaSplit_bound (m : Nat)
    (h : m < 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001) :
    (lambdaSplit m).1 < 2 ^ 129 ∧ (lambdaSplit m).2 < 2 ^ 128 := by
  show m % 0xac45a4010001a4020000000100000000 + m / 0xac45a4010001a4020000000100000000 < 2 ^ 129 ∧
    m / 0xac45a4010001a4020000000100000000 < 2 ^ 128
  omega

/-- Kind: recoding identity.
    Says: the four digits recombine to the scalar in base `z`:
    `d₀ + z·d₁ + z²·d₂ + z³·d₃ = m`, for every natural number `m`.
    Does not say: `ψ` acts as the multiplication by `−z` on `G2` (guard, not proved). -/
theorem zDigits_spec (m : Nat) :
    (zDigits m).1 + 0xd201000000010000 * (zDigits m).2.1 +
      0xd201000000010000 * 0xd201000000010000 * (zDigits m).2.2.1 +
      0xd201000000010000 * 0xd201000000010000 * 0xd201000000010000 * (zDigits m).2.2.2 = m := by
  show m % 0xd201000000010000 + 0xd201000000010000 * (m / 0xd201000000010000 % 0xd201000000010000) +
      0xd201000000010000 * 0xd201000000010000 *
        (m / 0xd201000000010000 / 0xd201000000010000 % 0xd201000000010000) +
      0xd201000000010000 * 0xd201000000010000 * 0xd201000000010000 *
        (m / 0xd201000000010000 / 0xd201000000010000 / 0xd201000000010000) = m
  omega

/-- Kind: size bound.
    Says: for a scalar below the group order all four digits are below `2^64`, so 16
    four-bit windows cover them.
    Does not say: anything about the group. -/
theorem zDigits_bound (m : Nat)
    (h : m < 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001) :
    (zDigits m).1 < 2 ^ 64 ∧ (zDigits m).2.1 < 2 ^ 64 ∧ (zDigits m).2.2.1 < 2 ^ 64 ∧ (zDigits m).2.2.2 < 2 ^ 64 := by
  show m % 0xd201000000010000 < 2 ^ 64 ∧ m / 0xd201000000010000 % 0xd201000000010000 < 2 ^ 64 ∧
    m / 0xd201000000010000 / 0xd201000000010000 % 0xd201000000010000 < 2 ^ 64 ∧
    m / 0xd201000000010000 / 0xd201000000010000 / 0xd201000000010000 < 2 ^ 64
  omega

/-- `φ'` on every entry of a table of Jacobian points. -/
def phiTable (table : Array (JPoint U384)) : Array (JPoint U384) :=
  table.map fun point => ⟨fmul beta2 point.x, point.y, point.z⟩

/-- `−ψ` on every entry of a table of Jacobian points. -/
def negPsiTable (table : Array (JPoint (Q2 U384))) : Array (JPoint (Q2 U384)) :=
  table.map fun point =>
    ⟨Q2.mul fp (Q2.conj fp point.x) psiX, Q2.neg fp (Q2.mul fp (Q2.conj fp point.y) psiY), Q2.conj fp point.z⟩

/-- Two table items per `G1` item: `(k₁, table of P)` and `(k₂, table of φ'P)`. -/
def g1Tables (items : Array (Curve.MsmItem U384)) :
    Nat → Array (Curve.StrausItem U384) → Array (Curve.StrausItem U384)
  | 0, out => out
  | j+1, out =>
    match items[j]? with
    | none => g1Tables items j out
    | some item =>
      let parts := lambdaSplit (item.1 % r)
      let table := Curve.table16 fp item.2.1 item.2.2
      g1Tables items j ((out.push (parts.1, table)).push (parts.2, phiTable table))

/-- Two affine points per `G1` item, for the bucket method. -/
def g1Halves (items : Array (Curve.MsmItem U384)) :
    Nat → Array (Curve.MsmItem U384) → Array (Curve.MsmItem U384)
  | 0, out => out
  | j+1, out =>
    match items[j]? with
    | none => g1Halves items j out
    | some item =>
      let parts := lambdaSplit (item.1 % r)
      g1Halves items j ((out.push (parts.1, item.2.1, item.2.2)).push (parts.2, fmul beta2 item.2.1, item.2.2))

/-- Four table items per `G2` item: the digits with the tables of `Q, −ψQ, ψ²Q, −ψ³Q`. -/
def g2Tables (items : Array (Curve.MsmItem (Q2 U384))) :
    Nat → Array (Curve.StrausItem (Q2 U384)) → Array (Curve.StrausItem (Q2 U384))
  | 0, out => out
  | j+1, out =>
    match items[j]? with
    | none => g2Tables items j out
    | some item =>
      let digits := zDigits (item.1 % r)
      let t0 := Curve.table16 fp2 item.2.1 item.2.2
      let t1 := negPsiTable t0
      let t2 := negPsiTable t1
      let t3 := negPsiTable t2
      g2Tables items j
        ((((out.push (digits.1, t0)).push (digits.2.1, t1)).push (digits.2.2.1, t2)).push (digits.2.2.2, t3))

/-- `−ψ` on an affine point. -/
def negPsi (point : G2Affine) : G2Affine :=
  (Q2.mul fp (Q2.conj fp point.1) psiX, Q2.neg fp (Q2.mul fp (Q2.conj fp point.2) psiY))

/-- Four affine points per `G2` item, for the bucket method. -/
def g2Quarters (items : Array (Curve.MsmItem (Q2 U384))) :
    Nat → Array (Curve.MsmItem (Q2 U384)) → Array (Curve.MsmItem (Q2 U384))
  | 0, out => out
  | j+1, out =>
    match items[j]? with
    | none => g2Quarters items j out
    | some item =>
      let digits := zDigits (item.1 % r)
      let q0 : G2Affine := (item.2.1, item.2.2)
      let q1 := negPsi q0
      let q2 := negPsi q1
      let q3 := negPsi q2
      g2Quarters items j
        ((((out.push (digits.1, q0.1, q0.2)).push (digits.2.1, q1.1, q1.2)).push (digits.2.2.1, q2.1, q2.2)).push
          (digits.2.2.2, q3.1, q3.2))

/-- Decode `count` items of 160 bytes from `off`. The result holds the items that
    contribute (point not at infinity, scalar not zero). `none`: some item is invalid. -/
def g1MsmItems (data : ByteArray) :
    Nat → Nat → Array (Curve.MsmItem U384) → Option (Array (Curve.MsmItem U384))
  | 0, _, items => some items
  | count+1, off, items =>
    match decodeG1 data off true with
    | none => none
    | some point =>
      let k := beNat data (off + 128) 32
      match point with
      | none => g1MsmItems data count (off + 160) items
      | some (x, y) =>
        if k = 0 then g1MsmItems data count (off + 160) items
        else g1MsmItems data count (off + 160) (items.push (k, x, y))

/-- Decode `count` items of 288 bytes from `off`, as `g1MsmItems`. -/
def g2MsmItems (data : ByteArray) :
    Nat → Nat → Array (Curve.MsmItem (Q2 U384)) → Option (Array (Curve.MsmItem (Q2 U384)))
  | 0, _, items => some items
  | count+1, off, items =>
    match decodeG2 data off true with
    | none => none
    | some point =>
      let k := beNat data (off + 256) 32
      match point with
      | none => g2MsmItems data count (off + 288) items
      | some (x, y) =>
        if k = 0 then g2MsmItems data count (off + 288) items
        else g2MsmItems data count (off + 288) (items.push (k, x, y))

/-- Below this many items one table per part and a shared doubling chain; from it on buckets. -/
def g1StrausLimit : Nat := 32
def g2StrausLimit : Nat := 12

/-- `Σ [kᵢ]Pᵢ` for subgroup points of `G1`: 33 windows over the split scalars. -/
def g1Sum (items : Array (Curve.MsmItem U384)) : JPoint U384 :=
  if items.size < g1StrausLimit then
    Curve.strausLoop fp (g1Tables items items.size #[]) 33 (Curve.infinity fp)
  else
    let halves := g1Halves items items.size #[]
    Curve.pippenger fp halves 132 (Curve.bucketWidth halves.size)

/-- `Σ [kᵢ]Qᵢ` for subgroup points of `G2`: 16 windows over the base-`z` digits. -/
def g2Sum (items : Array (Curve.MsmItem (Q2 U384))) : JPoint (Q2 U384) :=
  if items.size < g2StrausLimit then
    Curve.strausLoop fp2 (g2Tables items items.size #[]) 16 (Curve.infinity fp2)
  else
    let quarters := g2Quarters items items.size #[]
    Curve.pippenger fp2 quarters 64 (Curve.bucketWidth quarters.size)

def g1MsmBody (input : ByteArray) : Body :=
  match g1MsmItems input (input.size / 160) 0 #[] with
  | some items => .output (encodeG1 (g1Sum items))
  | none => .invalid

def g2MsmBody (input : ByteArray) : Body :=
  match g2MsmItems input (input.size / 288) 0 #[] with
  | some items => .output (encodeG2 (g2Sum items))
  | none => .invalid

/-- Precompile 0x0c on limbs. -/
def runG1Msm (gas : Nat) (input : ByteArray) : Result :=
  if input.size = 0 ∨ input.size % 160 ≠ 0 then .failure
  else charge gas (msmGas g1Discounts 519 12000 160 input.size) fun _ => g1MsmBody input

/-- Precompile 0x0e on limbs. -/
def runG2Msm (gas : Nat) (input : ByteArray) : Result :=
  if input.size = 0 ∨ input.size % 288 ≠ 0 then .failure
  else charge gas (msmGas g2Discounts 524 22500 288 input.size) fun _ => g2MsmBody input

/-- Kind: input-length rule, output contract and accounting.
    Says: a successful G1 multi-scalar multiplication on limbs had a non-empty input of
    whole 160-byte items, cost exactly the discounted price for that many items, and
    returned 128 bytes. Every item was decoded once (`g1MsmItems` recurses on the item count).
    Does not say: the bytes encode the group sum, or equal those of `BLS12381.runG1Msm`
    (differential runs and vectors, not proved). -/
theorem runG1Msm_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runG1Msm gas input = .success out left) :
    input.size ≠ 0 ∧ input.size % 160 = 0 ∧ out.size = 128 ∧
      left + msmGas g1Discounts 519 12000 160 input.size = gas := by
  unfold runG1Msm at h
  split at h
  · cases h
  · rename_i hLen
    have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
    refine ⟨by omega, by omega, ?_, hGas⟩
    simp only [g1MsmBody] at hBody
    split at hBody
    · exact Body.output.inj hBody ▸ encodeG1_size _
    · exact Body.noConfusion hBody

/-- Kind: input-length rule, output contract and accounting.
    Says: as `runG1Msm_success`, for 288-byte items and 256 output bytes.
    Does not say: the bytes encode the group sum (differential runs and vectors, not proved). -/
theorem runG2Msm_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runG2Msm gas input = .success out left) :
    input.size ≠ 0 ∧ input.size % 288 = 0 ∧ out.size = 256 ∧
      left + msmGas g2Discounts 524 22500 288 input.size = gas := by
  unfold runG2Msm at h
  split at h
  · cases h
  · rename_i hLen
    have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
    refine ⟨by omega, by omega, ?_, hGas⟩
    simp only [g2MsmBody] at hBody
    split at hBody
    · exact Body.output.inj hBody ▸ encodeG2_size _
    · exact Body.noConfusion hBody

/-- Kind: input-length rule.
    Says: an empty input fails for both multi-scalar operations on limbs, at any gas.
    Does not say: anything about non-empty input. -/
theorem msm_empty_input_fails (gas : Nat) (input : ByteArray) (h : input.size = 0) :
    runG1Msm gas input = .failure ∧ runG2Msm gas input = .failure := by
  simp [runG1Msm, runG2Msm, h]

/-- Kind: loop count.
    Says: decoding zero items returns the accumulated items unchanged, and a decoding
    step consumes exactly one item of the count (so `count` items mean `count` point
    decodings, each with its subgroup check, whatever the scalars are).
    Does not say: how long a subgroup check takes. -/
theorem g1MsmItems_zero (data : ByteArray) (off : Nat) (items : Array (Curve.MsmItem U384)) :
    g1MsmItems data 0 off items = some items := rfl

theorem g1MsmItems_invalid (data : ByteArray) (count off : Nat) (items : Array (Curve.MsmItem U384))
    (h : decodeG1 data off true = none) :
    g1MsmItems data (count + 1) off items = none := by
  simp [g1MsmItems, h]

theorem g2MsmItems_invalid (data : ByteArray) (count off : Nat) (items : Array (Curve.MsmItem (Q2 U384)))
    (h : decodeG2 data off true = none) :
    g2MsmItems data (count + 1) off items = none := by
  simp [g2MsmItems, h]

/-! ### Guards against the definition -/

private def fe (n : Nat) : ByteArray := natToBE 64 n
private def bytes1 (point : Nat × Nat) : ByteArray := fe point.1 ++ fe point.2
private def bytes2 (point : Fp2 × Fp2) : ByteArray :=
  fe point.1.c0 ++ fe point.1.c1 ++ fe point.2.c0 ++ fe point.2.c1
private def multiple1 (k : Nat) : Nat × Nat :=
  (Curve.toAffine field (Curve.mul field k (Curve.ofAffine field g1Generator.1 g1Generator.2))).getD (0, 0)
private def multiple2 (k : Nat) : Fp2 × Fp2 :=
  (Curve.toAffine field2 (Curve.mul field2 k (Curve.ofAffine field2 g2Generator.1 g2Generator.2))).getD
    (Fp2.zero, Fp2.zero)
private def item1 (point k : Nat) : ByteArray := bytes1 (multiple1 point) ++ natToBE 32 k
private def item2 (point k : Nat) : ByteArray := bytes2 (multiple2 point) ++ natToBE 32 k
private def agrees1 (input : ByteArray) : Bool :=
  (runG1Msm 100000000 input).same (BLS12381.runG1Msm 100000000 input)
private def agrees2 (input : ByteArray) : Bool :=
  (runG2Msm 100000000 input).same (BLS12381.runG2Msm 100000000 input)
private def big : Nat := 0xf0e1d2c3b4a5968778695a4b3c2d1e0f0123456789abcdeffedcba9876543210
private def many2 (count : Nat) : ByteArray :=
  (List.range count).foldl (fun acc i => acc ++ item2 (i + 2) ((i * 7919 + 13) * (i % 4))) ByteArray.empty
private def many1 (count : Nat) : ByteArray :=
  (List.range count).foldl (fun acc i => acc ++ item1 (i + 2) ((i * 7919 + 13) * (i % 4))) ByteArray.empty

-- Numeric facts behind the splits, on the definition's arithmetic.
#guard lambda1 == zSquared - 1 && zSquared == parameter ^ 2 && zSquared == 0xac45a4010001a4020000000100000000 && parameter == 0xd201000000010000 &&
  r == 0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001 && r < parameter ^ 4
#guard beta2Nat == betaNat ^ 2 % p && ((zSquared - 1) ^ 2 + (zSquared - 1) + 1) % r == 0 && p % r == r - parameter
-- φ'(G₁) = [z² − 1]G₁.
#guard (Fp.mul p beta2Nat g1Generator.1, g1Generator.2) == multiple1 (zSquared - 1)
#guard (lambdaSplit (r - 1)).1 < 2 ^ 129 && (zDigits (r - 1)).2.2.2 < parameter
-- One item: scalars 0, 1, 2, r − 1, r, r + 1, 2^256 − 1, a 256-bit one; the point at infinity.
#guard agrees1 (item1 5 0) && agrees1 (item1 5 1) && agrees1 (item1 5 2) && agrees1 (item1 7 (r - 1)) &&
  agrees1 (item1 7 r) && agrees1 (item1 7 (r + 1))
#guard agrees1 (item1 3 (2 ^ 256 - 1)) && agrees1 (item1 3 big) && agrees1 (natToBE 128 0 ++ natToBE 32 5) &&
  agrees1 (natToBE 160 0)
-- Several items: equal points, inverse scalars, items at infinity in between, an invalid item last.
#guard agrees1 (item1 5 3 ++ item1 5 4) && agrees1 (item1 5 3 ++ item1 5 (r - 3)) &&
  agrees1 (item1 2 big ++ natToBE 160 0 ++ item1 3 (2 ^ 255 + 1) ++ item1 4 0 ++ item1 5 99)
#guard agrees1 (item1 5 3 ++ bytes1 (5, 6) ++ natToBE 32 1) && agrees1 (item1 5 3 ++ natToBE 159 1) &&
  agrees1 ByteArray.empty && agrees1 (many1 9) && agrees1 (many1 33)
#guard (g1MsmBody (item1 5 3 ++ item1 2 4)).same (.output (bytes1 (multiple1 23)))
#guard agrees2 (item2 5 0) && agrees2 (item2 5 1) && agrees2 (item2 7 (r - 1)) && agrees2 (item2 7 r) &&
  agrees2 (item2 3 (2 ^ 256 - 1)) && agrees2 (natToBE 288 0)
#guard agrees2 (item2 5 3 ++ item2 5 (r - 3)) && agrees2 (item2 2 big ++ natToBE 288 0 ++ item2 3 (2 ^ 255 + 1)) &&
  agrees2 (item2 5 3 ++ natToBE 287 1) && agrees2 ByteArray.empty && agrees2 (many2 13)
#guard (g2MsmBody (item2 5 3 ++ item2 2 4)).same (.output (bytes2 (multiple2 23)))

#print axioms runG1Msm_success
#print axioms runG2Msm_success
#print axioms msm_empty_input_fails
#print axioms lambdaSplit_spec
#print axioms lambdaSplit_bound
#print axioms zDigits_spec
#print axioms zDigits_bound
#print axioms g1MsmItems_zero
#print axioms g1MsmItems_invalid
#print axioms g2MsmItems_invalid

end EVMCleanroom.Precompiles.BLS12381.Fast
