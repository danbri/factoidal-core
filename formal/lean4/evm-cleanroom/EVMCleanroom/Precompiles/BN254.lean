import EVMCleanroom.Precompiles.Pairing

/-!
# alt_bn128 addition, scalar multiplication and pairing check (0x06, 0x07, 0x08)

EIP-196 and EIP-197, with the Istanbul prices of EIP-1108: 150, 6000 and
`45000 + 34000` per pair. Curve `y² = x³ + 3` over the 254-bit prime `p`;
`G2` on the twist `y² = x³ + 3/(9 + u)` over `Fp2 = Fp[u]/(u² + 1)`.

Encoding. A field element is 32 big-endian bytes and must be below `p`. A `G1`
point is `x ‖ y`, the point at infinity is 64 zero bytes. A `G2` point is
`x.c1 ‖ x.c0 ‖ y.c1 ‖ y.c0` (imaginary part first), infinity is 128 zero bytes.
Addition and multiplication read a zero-padded prefix (128 and 96 bytes) and
ignore the rest. The pairing input must be a multiple of 192 bytes. Any
non-canonical coordinate, any point off its curve, and any `G2` point outside
the order-`r` subgroup is an exceptional halt.

Proved: gas accounting, output lengths, prefix-only input handling, the
length rule of the pairing input. Not proved: group laws or bilinearity
(guards below and the published vectors).
-/

namespace EVMCleanroom.Precompiles.BN254

def p : Nat := 21888242871839275222246405745257275088696311157297823662689037894645226208583
def r : Nat := 21888242871839275222246405745257275088548364400416034343698204186575808495617
/-- The curve parameter `x`; `p` and `r` are the BN polynomials at `x`. -/
def parameter : Nat := 4965661367192848881

def field : FieldOps Nat := Fp.ops p
def field2 : FieldOps Fp2 := Fp2.ops p

def tower : Tower := Tower.make p ⟨9, 1⟩

/-- `3 / (9 + u)`. -/
def twistB : Fp2 := Fp2.scale p 3 (Fp2.inv p ⟨9, 1⟩)

def curve : PairingCurve :=
  { tower, r, twist := .divide, loop := 6 * parameter + 2, frobeniusSteps := true, negative := false,
    hardDigits := hardDigitsOf p r }

/-- A decoded `G1` point: `none` is the point at infinity. -/
abbrev Affine1 := Option (Nat × Nat)
abbrev Affine2 := Option (Fp2 × Fp2)

/-- Decode a `G1` point at `off`; the outer `none` is invalid input. -/
def decodeG1 (data : ByteArray) (off : Nat) : Option Affine1 :=
  let x := beNat data off 32
  let y := beNat data (off + 32) 32
  if x ≥ p ∨ y ≥ p then none
  else if x = 0 ∧ y = 0 then some none
  else if Curve.onCurve field 3 x y then some (some (x, y))
  else none

/-- Decode a `G2` point at `off` (imaginary parts first), with the subgroup check. -/
def decodeG2 (data : ByteArray) (off : Nat) : Option Affine2 :=
  let x1 := beNat data off 32
  let x0 := beNat data (off + 32) 32
  let y1 := beNat data (off + 64) 32
  let y0 := beNat data (off + 96) 32
  if x0 ≥ p ∨ x1 ≥ p ∨ y0 ≥ p ∨ y1 ≥ p then none
  else if x0 = 0 ∧ x1 = 0 ∧ y0 = 0 ∧ y1 = 0 then some none
  else
    let x : Fp2 := ⟨x0, x1⟩
    let y : Fp2 := ⟨y0, y1⟩
    if !Curve.onCurve field2 twistB x y then none
    else if Curve.isInfinity field2 (Curve.mul field2 r (Curve.ofAffine field2 x y)) then some (some (x, y))
    else none

def toJacobian (point : Affine1) : JPoint Nat :=
  match point with
  | none => Curve.infinity field
  | some (x, y) => Curve.ofAffine field x y

def encodeG1 (point : JPoint Nat) : ByteArray :=
  match Curve.toAffine field point with
  | none => natToBE 64 0
  | some (x, y) => natToBE 32 x ++ natToBE 32 y

theorem encodeG1_size (point : JPoint Nat) : (encodeG1 point).size = 64 := by
  unfold encodeG1
  split
  · exact natToBE_size _ _
  · simp [ByteArray.size_append, natToBE_size]

def addBody (data : ByteArray) : Body :=
  match decodeG1 data 0, decodeG1 data 64 with
  | some a, some b => .output (encodeG1 (Curve.add field (toJacobian a) (toJacobian b)))
  | _, _ => .invalid

def mulBody (data : ByteArray) : Body :=
  match decodeG1 data 0 with
  | some a => .output (encodeG1 (Curve.mul field (beNat data 64 32) (toJacobian a)))
  | none => .invalid

/-- Precompile 0x06. -/
def runAdd (gas : Nat) (input : ByteArray) : Result :=
  charge gas 150 fun _ => addBody (readPadded input 0 128)

/-- Precompile 0x07. -/
def runMul (gas : Nat) (input : ByteArray) : Result :=
  charge gas 6000 fun _ => mulBody (readPadded input 0 96)

def pairingGas (size : Nat) : Nat := 45000 + 34000 * (size / 192)

/-- Decode `count` pairs starting at `off`. Pairs with a point at infinity
    contribute one to the product and are dropped after validation. -/
def decodePairs (data : ByteArray) : Nat → Nat → List (Pairing.G1 × Pairing.G2) → Option (List (Pairing.G1 × Pairing.G2))
  | 0, _, acc => some acc
  | count+1, off, acc =>
    match decodeG1 data off, decodeG2 data (off + 64) with
    | some a, some b =>
      match a, b with
      | some a, some b => decodePairs data count (off + 192) ((a, b) :: acc)
      | _, _ => decodePairs data count (off + 192) acc
    | _, _ => none

def pairingBody (input : ByteArray) : Body :=
  if input.size % 192 ≠ 0 then .invalid
  else
    match decodePairs input (input.size / 192) 0 [] with
    | none => .invalid
    | some pairs => .output (natToBE 32 (if Pairing.productIsOne curve pairs then 1 else 0))

/-- Precompile 0x08. -/
def runPairing (gas : Nat) (input : ByteArray) : Result :=
  charge gas (pairingGas input.size) fun _ => pairingBody input

/-- Kind: output contract and accounting.
    Says: a successful addition costs exactly 150 gas and returns exactly 64 bytes.
    Does not say: the bytes encode the group sum (vectors, not proved). -/
theorem runAdd_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runAdd gas input = .success out left) : out.size = 64 ∧ left + 150 = gas := by
  have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
  refine ⟨?_, hGas⟩
  simp only [addBody] at hBody
  split at hBody
  · exact Body.output.inj hBody ▸ encodeG1_size _
  · exact Body.noConfusion hBody

/-- Kind: output contract and accounting.
    Says: a successful multiplication costs exactly 6000 gas and returns exactly 64 bytes.
    Does not say: the bytes encode the scalar multiple (vectors, not proved). -/
theorem runMul_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runMul gas input = .success out left) : out.size = 64 ∧ left + 6000 = gas := by
  have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
  refine ⟨?_, hGas⟩
  simp only [mulBody] at hBody
  split at hBody
  · exact Body.output.inj hBody ▸ encodeG1_size _
  · exact Body.noConfusion hBody

/-- Kind: input-length handling.
    Says: addition depends only on the zero-padded first 128 bytes, multiplication on
    the first 96.
    Does not say: anything about what those bytes mean. -/
theorem run_reads_prefix (gas : Nat) (x y : ByteArray) :
    (readPadded x 0 128 = readPadded y 0 128 → runAdd gas x = runAdd gas y) ∧
    (readPadded x 0 96 = readPadded y 0 96 → runMul gas x = runMul gas y) := by
  constructor <;> intro h <;> simp [runAdd, runMul, h]

/-- Kind: output contract, accounting and input-length rule.
    Says: a successful pairing check had an input of whole 192-byte pairs, cost exactly
    45000 + 34000 per pair, and returned exactly 32 bytes.
    Does not say: the 32 bytes are the correct verdict (vectors, not proved). -/
theorem runPairing_success (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : runPairing gas input = .success out left) :
    input.size % 192 = 0 ∧ out.size = 32 ∧ left + pairingGas input.size = gas := by
  have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
  simp only [pairingBody] at hBody
  split at hBody
  · exact Body.noConfusion hBody
  · rename_i hLen
    split at hBody
    · exact Body.noConfusion hBody
    · exact ⟨by omega, Body.output.inj hBody ▸ natToBE_size _ _, hGas⟩

/-- Kind: input-length rule.
    Says: a pairing input that is not a multiple of 192 bytes fails at any gas.
    Does not say: anything about well-sized input. -/
theorem runPairing_bad_length (gas : Nat) (input : ByteArray) (h : input.size % 192 ≠ 0) :
    runPairing gas input = .failure := by
  unfold runPairing charge
  split
  · rfl
  · simp [pairingBody, h]

/-- Kind: loop bound.
    Says: the number of pairs decoded is the input length divided by 192, so the
    34000 gas per pair pays for every Miller loop run.
    Does not say: how long a Miller loop takes. -/
theorem pairingGas_pays_pairs (size : Nat) : 34000 * (size / 192) ≤ pairingGas size := by
  simp only [pairingGas]; omega

private def g1 : Nat × Nat := (1, 2)
private def g2 : Fp2 × Fp2 :=
  (⟨10857046999023057135944570762232829481370756359578518086990519993285655852781,
    11559732032986387107991004021392285783925812861821192530917403151452391805634⟩,
   ⟨8495653923123431417604973247489272438418190587263600148770280649306958101930,
    4082367875863433681332203403145435568316851327593401208105741076214120093531⟩)

private def mul1 (k : Nat) : Nat × Nat :=
  (Curve.toAffine field (Curve.mul field k (Curve.ofAffine field g1.1 g1.2))).getD (0, 0)
private def mul2 (k : Nat) : Fp2 × Fp2 :=
  (Curve.toAffine field2 (Curve.mul field2 k (Curve.ofAffine field2 g2.1 g2.2))).getD (Fp2.zero, Fp2.zero)

-- The BN polynomials at the parameter give the two primes.
#guard p == 36 * parameter ^ 4 + 36 * parameter ^ 3 + 24 * parameter ^ 2 + 6 * parameter + 1
#guard r == 36 * parameter ^ 4 + 36 * parameter ^ 3 + 18 * parameter ^ 2 + 6 * parameter + 1
#guard (p ^ 4 - p ^ 2 + 1) % r == 0 && (p - 1) % 6 == 0
#guard Curve.onCurve field 3 g1.1 g1.2 && Curve.onCurve field2 twistB g2.1 g2.2
#guard Curve.isInfinity field (Curve.mul field r (Curve.ofAffine field 1 2))
#guard Curve.isInfinity field2 (Curve.mul field2 r (Curve.ofAffine field2 g2.1 g2.2))
-- Tower algebra: inverse, Frobenius as the p-th power on a line value, ξ^((p²−1)/6)... sample.
private def sample : Fp12 := Pairing.miller curve g1 g2
#guard Fp12.mul tower sample (Fp12.inv tower sample) == Fp12.one
#guard Fp12.mul tower (Fp12.mul tower sample sample) sample == Fp12.mul tower sample (Fp12.mul tower sample sample)
#guard Fp12.frobenius tower sample == Fp12.pow tower sample p
-- The pairing: order r, non-degenerate, bilinear in both arguments.
private def e11 : Fp12 := Pairing.pairing curve g1 g2
#guard e11 != Fp12.one
#guard Fp12.pow tower e11 r == Fp12.one
#guard Pairing.pairing curve (mul1 5) g2 == Fp12.pow tower e11 5
#guard Pairing.pairing curve g1 (mul2 7) == Fp12.pow tower e11 7
#guard Pairing.pairing curve (mul1 3) (mul2 11) == Fp12.pow tower e11 33
-- The hard part agrees with plain exponentiation by (p⁴ − p² + 1)/r.
#guard Pairing.hardPart curve sample == Fp12.pow tower sample ((p ^ 4 - p ^ 2 + 1) / r)
-- e(P, Q) · e(−P, Q) = 1.
#guard Pairing.productIsOne curve [(g1, g2), ((1, p - 2), g2)]
#guard !Pairing.productIsOne curve [(g1, g2), (g1, g2)]
#guard Pairing.productIsOne curve []

#print axioms encodeG1_size
#print axioms runAdd_success
#print axioms runMul_success
#print axioms run_reads_prefix
#print axioms runPairing_success
#print axioms runPairing_bad_length
#print axioms pairingGas_pays_pairs

end EVMCleanroom.Precompiles.BN254
