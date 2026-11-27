import EVMCleanroom.Precompiles.BLS12381Fast

/-!
# BLS12-381 multi-scalar multiplication on limbs (0x0c, 0x0e)

The same contract as `BLS12381.runG1Msm` and `runG2Msm` (EIP-2537): every
item is decoded with the curve and subgroup checks (the endomorphism checks
of `BLS12381Fast.lean`), an invalid item fails the call, and the result is
`Σ [kᵢ]Pᵢ`. Scalars are used as given (up to `2^256 − 1`, not reduced).

The definition performs one double-and-add per item. Here the sum is
computed by `Curve.msm`: below 80 points one table of sixteen multiples per
point and a shared doubling chain (Straus), from 80 points on the bucket
method (Pippenger) with a window chosen by the number of points. Items whose
point is at infinity or whose scalar is zero contribute nothing and are left
out after validation. The discount table of the price ends at 128 items;
longer inputs use the same code with wider windows.

Tested against the definition, not proved equal (group laws are not proved):
guards below, the differential run of `evm-blsops` for item counts on both
sides of the method switch, and the published vectors.

Proved: input-length rules, gas accounting, output lengths, that an empty
input fails, that every item is decoded exactly once (the decoding loops
recurse on the item count), and the pass bounds of `CurveFast.lean`.

Not constant-time.
-/

namespace EVMCleanroom.Precompiles.BLS12381.Fast

/-- Decode `count` items of 160 bytes from `off`. The result holds the items that
    contribute (point not at infinity, scalar not zero) and the largest scalar.
    `none`: some item is invalid. -/
def g1MsmItems (data : ByteArray) :
    Nat → Nat → Array (Curve.MsmItem U384) → Nat → Option (Array (Curve.MsmItem U384) × Nat)
  | 0, _, items, top => some (items, top)
  | count+1, off, items, top =>
    match decodeG1 data off true with
    | none => none
    | some point =>
      let k := beNat data (off + 128) 32
      match point with
      | none => g1MsmItems data count (off + 160) items top
      | some (x, y) =>
        if k = 0 then g1MsmItems data count (off + 160) items top
        else g1MsmItems data count (off + 160) (items.push (k, x, y)) (max top k)

/-- Decode `count` items of 288 bytes from `off`, as `g1MsmItems`. -/
def g2MsmItems (data : ByteArray) :
    Nat → Nat → Array (Curve.MsmItem (Q2 U384)) → Nat → Option (Array (Curve.MsmItem (Q2 U384)) × Nat)
  | 0, _, items, top => some (items, top)
  | count+1, off, items, top =>
    match decodeG2 data off true with
    | none => none
    | some point =>
      let k := beNat data (off + 256) 32
      match point with
      | none => g2MsmItems data count (off + 288) items top
      | some (x, y) =>
        if k = 0 then g2MsmItems data count (off + 288) items top
        else g2MsmItems data count (off + 288) (items.push (k, x, y)) (max top k)

def g1Sum (items : Array (Curve.MsmItem U384)) (top : Nat) : JPoint U384 :=
  Curve.msm fp items (Nat.log2 top + 1)

def g2Sum (items : Array (Curve.MsmItem (Q2 U384))) (top : Nat) : JPoint (Q2 U384) :=
  Curve.msm fp2 items (Nat.log2 top + 1)

def g1MsmBody (input : ByteArray) : Body :=
  match g1MsmItems input (input.size / 160) 0 #[] 0 with
  | some decoded => .output (encodeG1 (g1Sum decoded.1 decoded.2))
  | none => .invalid

def g2MsmBody (input : ByteArray) : Body :=
  match g2MsmItems input (input.size / 288) 0 #[] 0 with
  | some decoded => .output (encodeG2 (g2Sum decoded.1 decoded.2))
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
theorem g1MsmItems_zero (data : ByteArray) (off : Nat) (items : Array (Curve.MsmItem U384)) (top : Nat) :
    g1MsmItems data 0 off items top = some (items, top) := rfl

theorem g1MsmItems_invalid (data : ByteArray) (count off : Nat) (items : Array (Curve.MsmItem U384))
    (top : Nat) (h : decodeG1 data off true = none) :
    g1MsmItems data (count + 1) off items top = none := by
  simp [g1MsmItems, h]

theorem g2MsmItems_invalid (data : ByteArray) (count off : Nat) (items : Array (Curve.MsmItem (Q2 U384)))
    (top : Nat) (h : decodeG2 data off true = none) :
    g2MsmItems data (count + 1) off items top = none := by
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
private def many1 (count : Nat) : ByteArray :=
  (List.range count).foldl (fun acc i => acc ++ item1 (i + 2) ((i * 7919 + 13) * (i % 4))) ByteArray.empty

-- One item: scalars 0, 1, 2, r − 1, r, r + 1, 2^256 − 1, a 256-bit one; the point at infinity.
#guard agrees1 (item1 5 0) && agrees1 (item1 5 1) && agrees1 (item1 5 2) && agrees1 (item1 7 (r - 1)) &&
  agrees1 (item1 7 r) && agrees1 (item1 7 (r + 1))
#guard agrees1 (item1 3 (2 ^ 256 - 1)) && agrees1 (item1 3 big) && agrees1 (natToBE 128 0 ++ natToBE 32 5) &&
  agrees1 (natToBE 160 0)
-- Several items: equal points, inverse scalars, items at infinity in between, an invalid item last.
#guard agrees1 (item1 5 3 ++ item1 5 4) && agrees1 (item1 5 3 ++ item1 5 (r - 3)) &&
  agrees1 (item1 2 big ++ natToBE 160 0 ++ item1 3 (2 ^ 255 + 1) ++ item1 4 0 ++ item1 5 99)
#guard agrees1 (item1 5 3 ++ bytes1 (5, 6) ++ natToBE 32 1) && agrees1 (item1 5 3 ++ natToBE 159 1) &&
  agrees1 ByteArray.empty && agrees1 (many1 9)
#guard (g1MsmBody (item1 5 3 ++ item1 2 4)).same (.output (bytes1 (multiple1 23)))
#guard agrees2 (item2 5 0) && agrees2 (item2 5 1) && agrees2 (item2 7 (r - 1)) && agrees2 (item2 7 r) &&
  agrees2 (item2 3 (2 ^ 256 - 1)) && agrees2 (natToBE 288 0)
#guard agrees2 (item2 5 3 ++ item2 5 (r - 3)) && agrees2 (item2 2 big ++ natToBE 288 0 ++ item2 3 (2 ^ 255 + 1)) &&
  agrees2 (item2 5 3 ++ natToBE 287 1) && agrees2 ByteArray.empty
#guard (g2MsmBody (item2 5 3 ++ item2 2 4)).same (.output (bytes2 (multiple2 23)))

#print axioms runG1Msm_success
#print axioms runG2Msm_success
#print axioms msm_empty_input_fails
#print axioms g1MsmItems_zero
#print axioms g1MsmItems_invalid
#print axioms g2MsmItems_invalid

end EVMCleanroom.Precompiles.BLS12381.Fast
