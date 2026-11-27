import EVMCleanroom.Precompiles.Basic

/-!
# Modular exponentiation (precompile 0x05)

Input: three 32-byte big-endian lengths (base, exponent, modulus) followed by
the three operands; all reads are zero-padded on the right. The output is
`base ^ exponent mod modulus` in exactly `modulus length` bytes (all zero for
a zero modulus).

Three price rules are implemented, each written from its EIP:

* EIP-198 (Byzantium): piecewise complexity, divisor 20;
* EIP-2565 (Berlin to Prague): `max(200, words² · iterations / 3)`;
* EIP-7883 with the EIP-7823 length bound (Osaka): minimum 500, doubled
  complexity above 32 bytes, 16 gas per exponent byte beyond the first 32,
  and failure when a declared length exceeds 1024 bytes.

Work bound. The exponent is consumed byte by byte from the input, so the
number of loop iterations is exactly eight per declared exponent byte. The
declared lengths are attacker-chosen 256-bit numbers. The gas rule already
makes large lengths unaffordable; independently of gas the implementation
refuses (never answers) when, after the gas check, the declared exponent
length exceeds `maxExponentBytes` or the base or modulus length exceeds
`maxOperandBytes`.
-/

namespace EVMCleanroom.Precompiles.ModExp

inductive Rule where
  | eip198
  | eip2565
  | eip7883
  deriving DecidableEq, Repr

/-- Local bounds, not Ethereum rules. -/
def maxExponentBytes : Nat := 1_048_576
def maxOperandBytes : Nat := 131_072

def bitLength (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- The "adjusted exponent length" of the EIPs before the `max(_, 1)`;
    `perByte` is 8 before Osaka and 16 from EIP-7883. -/
def iterations (perByte expLen expHead : Nat) : Nat :=
  if expLen ≤ 32 then bitLength expHead - 1
  else perByte * (expLen - 32) + (bitLength expHead - 1)

def complexity198 (x : Nat) : Nat :=
  if x ≤ 64 then x * x
  else if x ≤ 1024 then x * x / 4 + 96 * x - 3072
  else x * x / 16 + 480 * x - 199680

def gasCost (rule : Rule) (baseLen expLen modLen expHead : Nat) : Nat :=
  let maxLen := max baseLen modLen
  match rule with
  | .eip198 => complexity198 maxLen * max (iterations 8 expLen expHead) 1 / 20
  | .eip2565 =>
    let words := (maxLen + 7) / 8
    max 200 (words * words * max (iterations 8 expLen expHead) 1 / 3)
  | .eip7883 =>
    let words := (maxLen + 7) / 8
    let complexity := if maxLen ≤ 32 then 16 else 2 * words * words
    max 500 (complexity * max (iterations 16 expLen expHead) 1)

/-- Eight square-and-multiply steps for one exponent byte, most significant bit first. -/
def powByte (modulus base : Nat) (byte : UInt8) : Nat → Nat → Nat
  | 0, acc => acc
  | k+1, acc =>
    let square := acc * acc % modulus
    powByte modulus base byte k (if byte.toNat.testBit k then square * base % modulus else square)

/-- Consume `remaining` exponent bytes of the input starting at `off`. -/
def powBytes (modulus base : Nat) (input : ByteArray) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | remaining+1, off, acc =>
    powBytes modulus base input remaining (off + 1) (powByte modulus base (byteAt input off) 8 acc)

structure Header where
  baseLen : Nat
  expLen : Nat
  modLen : Nat

def header (input : ByteArray) : Header :=
  ⟨beNat input 0 32, beNat input 32 32, beNat input 64 32⟩

def expHead (input : ByteArray) (h : Header) : Nat :=
  beNat input (96 + h.baseLen) (min 32 h.expLen)

def price (rule : Rule) (input : ByteArray) : Nat :=
  let h := header input
  gasCost rule h.baseLen h.expLen h.modLen (expHead input h)

/-- EIP-7823: from Osaka each declared length is at most 1024 bytes. -/
def lengthsAllowed (rule : Rule) (h : Header) : Bool :=
  match rule with
  | .eip7883 => h.baseLen ≤ 1024 && h.expLen ≤ 1024 && h.modLen ≤ 1024
  | _ => true

def body (input : ByteArray) : Body :=
  let h := header input
  if h.modLen = 0 then .output ByteArray.empty
  else if h.expLen > maxExponentBytes ∨ h.baseLen > maxOperandBytes ∨ h.modLen > maxOperandBytes then .refuse
  else
    let modulus := beNat input (96 + h.baseLen + h.expLen) h.modLen
    if modulus = 0 then .output (natToBE h.modLen 0)
    else
      let base := beNat input 96 h.baseLen % modulus
      .output (natToBE h.modLen (powBytes modulus base input h.expLen (96 + h.baseLen) (1 % modulus)))

/-- Precompile 0x05 under the given price rule. -/
def run (rule : Rule) (gas : Nat) (input : ByteArray) : Result :=
  if !lengthsAllowed rule (header input) then .failure
  else charge gas (price rule input) fun _ => body input

/-- Kind: gas admission.
    Says: a call with less gas than the rule's price fails before any operand is read.
    Does not say: the price equals the EIP's (tested against published vectors). -/
theorem run_underfunded (rule : Rule) (gas : Nat) (input : ByteArray) (h : gas < price rule input) :
    run rule gas input = .failure := by
  unfold run
  split
  · rfl
  · exact charge_underfunded _ _ _ h

/-- Kind: output-length contract and accounting.
    Says: a successful call returns exactly the declared modulus length in bytes and
    the exact unspent gas.
    Does not say: the bytes are the modular power (see `powBytes` facts and vectors). -/
theorem run_success (rule : Rule) (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : run rule gas input = .success out left) :
    out.size = (header input).modLen ∧ left + price rule input = gas := by
  unfold run at h
  split at h
  · cases h
  · have ⟨hBody, hGas⟩ := charge_success _ _ _ _ _ h
    refine ⟨?_, hGas⟩
    unfold body at hBody
    simp only at hBody
    split at hBody
    · rename_i hZero; cases hBody; simp [hZero]
    · split at hBody
      · cases hBody
      · split at hBody
        · cases hBody; exact natToBE_size _ _
        · cases hBody; exact natToBE_size _ _

/-- Kind: work bound.
    Says: whenever a call succeeds with a non-empty result, the declared lengths were
    within the local bounds, so the exponent loop ran at most `8 * maxExponentBytes`
    steps on operands of at most `maxOperandBytes` bytes.
    Does not say: how long one step takes. -/
theorem run_success_bounded (rule : Rule) (gas : Nat) (input out : ByteArray) (left : Nat)
    (h : run rule gas input = .success out left) (hOut : out.size ≠ 0) :
    (header input).expLen ≤ maxExponentBytes ∧ (header input).baseLen ≤ maxOperandBytes ∧
      (header input).modLen ≤ maxOperandBytes := by
  unfold run at h
  split at h
  · cases h
  · have ⟨hBody, _⟩ := charge_success _ _ _ _ _ h
    unfold body at hBody
    simp only at hBody
    split at hBody
    · cases hBody; simp at hOut
    · split at hBody
      · cases hBody
      · rename_i hBound; omega

/-- Kind: local bound.
    Says: a funded call that declares a non-zero modulus length and an over-bound length
    is refused, not answered.
    Does not say: Ethereum has these limits. -/
theorem run_refuses_over_bound (rule : Rule) (gas : Nat) (input : ByteArray)
    (hAllowed : lengthsAllowed rule (header input) = true) (hGas : price rule input ≤ gas)
    (hMod : (header input).modLen ≠ 0)
    (hOver : (header input).expLen > maxExponentBytes ∨ (header input).baseLen > maxOperandBytes ∨
      (header input).modLen > maxOperandBytes) :
    run rule gas input = .refusal := by
  have hNot : ¬ gas < price rule input := by omega
  simp [run, hAllowed, charge, hNot, body, hMod, hOver]

/-- Kind: EIP-7823 bound.
    Says: under the Osaka rule a declared length above 1024 bytes fails at any gas.
    Does not say: anything for earlier rules, which have no such bound. -/
theorem run_osaka_length_bound (gas : Nat) (input : ByteArray)
    (h : (header input).baseLen > 1024 ∨ (header input).expLen > 1024 ∨ (header input).modLen > 1024) :
    run .eip7883 gas input = .failure := by
  have : lengthsAllowed .eip7883 (header input) = false := by
    simp only [lengthsAllowed, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega
  simp [run, this]

/-- Kind: algebraic fact about the representation.
    Says: one exponent byte keeps the accumulator reduced below the modulus.
    Does not say: the accumulator is the mathematical power. -/
theorem powByte_lt (modulus base : Nat) (byte : UInt8) (k acc : Nat) (hMod : 0 < modulus)
    (hAcc : acc < modulus) : powByte modulus base byte k acc < modulus := by
  induction k generalizing acc with
  | zero => simpa [powByte] using hAcc
  | succ k ih =>
    simp only [powByte]
    apply ih
    split <;> exact Nat.mod_lt _ hMod

/-- Kind: algebraic fact about the representation.
    Says: the whole exponent loop returns a value below a non-zero modulus.
    Does not say: the value is the mathematical power (tested against vectors and an
    independent oracle). -/
theorem powBytes_lt (modulus base : Nat) (input : ByteArray) (n off acc : Nat) (hMod : 0 < modulus)
    (hAcc : acc < modulus) : powBytes modulus base input n off acc < modulus := by
  induction n generalizing off acc with
  | zero => simpa [powBytes] using hAcc
  | succ n ih =>
    simp only [powBytes]
    exact ih _ _ (powByte_lt modulus base _ 8 acc hMod hAcc)

/-- Kind: gas formula.
    Says: the EIP-2565 price is never below 200 and the EIP-7883 price never below 500.
    Does not say: anything else about the formulas. -/
theorem gasCost_minimum (baseLen expLen modLen head : Nat) :
    200 ≤ gasCost .eip2565 baseLen expLen modLen head ∧
    500 ≤ gasCost .eip7883 baseLen expLen modLen head := by
  constructor <;> simp only [gasCost] <;> omega

private def w32 (n : Nat) : String := toHex (natToBE 32 n)

private def call (rule : Rule) (gas : Nat) (input : ByteArray) : String :=
  match run rule gas input with
  | .success out left => toHex out ++ ":" ++ toString (gas - left)
  | .failure => "failure"
  | .refusal => "refusal"

-- EIP-198 example 1: 3 ^ (p - 1) mod p = 1 for the secp256k1 field prime.
private def eip198a : ByteArray := hex (w32 1 ++ w32 32 ++ w32 32 ++ "03" ++
  "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e" ++
  "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f")
#guard call .eip198 100000 eip198a == w32 1 ++ ":13056"
#guard call .eip2565 100000 eip198a == w32 1 ++ ":1360"
#guard call .eip7883 100000 eip198a == w32 1 ++ ":4080"
-- EIP-198 example 2: zero base, same exponent and modulus.
private def eip198b : ByteArray := hex (w32 0 ++ w32 32 ++ w32 32 ++
  "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2e" ++
  "fffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f")
#guard call .eip198 100000 eip198b == w32 0 ++ ":13056"
-- EIP-198 example 3: absurd declared lengths are unaffordable, at any gas given here.
#guard call .eip198 (1 <<< 64) (hex (w32 0 ++ w32 32 ++
  "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff" ++
  "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe" ++
  "fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd")) == "failure"
-- EIP-198 examples 4 and 5: 3 ^ 0xffff mod 2^255, with the modulus right-padded.
#guard call .eip198 100000 (hex (w32 1 ++ w32 2 ++ w32 32 ++ "03" ++ "ffff" ++
  "8000000000000000000000000000000000000000000000000000000000000000" ++ "07")) ==
  "3b01b01ac41f2d6e917c6d6a221ce793802469026d9ab7578fa2e79e4da6aaab:768"
#guard call .eip198 100000 (hex (w32 1 ++ w32 2 ++ w32 32 ++ "03" ++ "ffff" ++ "80")) ==
  "3b01b01ac41f2d6e917c6d6a221ce793802469026d9ab7578fa2e79e4da6aaab:768"
-- Empty input: all lengths zero, empty output, minimum price.
#guard call .eip2565 200 ByteArray.empty == ":200"
#guard call .eip2565 199 ByteArray.empty == "failure"
#guard call .eip7883 500 ByteArray.empty == ":500"
#guard call .eip198 0 ByteArray.empty == ":0"
-- Zero modulus bytes give zero bytes; modulus one gives zero; 0 ^ 0 mod m = 1.
#guard call .eip2565 1000 (hex (w32 1 ++ w32 1 ++ w32 2 ++ "05" ++ "03" ++ "0000")) == "0000:200"
#guard call .eip2565 1000 (hex (w32 1 ++ w32 1 ++ w32 1 ++ "05" ++ "03" ++ "01")) == "00:200"
#guard call .eip2565 1000 (hex (w32 1 ++ w32 1 ++ w32 1 ++ "00" ++ "00" ++ "07")) == "01:200"
#guard call .eip2565 1000 (hex (w32 0 ++ w32 0 ++ w32 1 ++ "07")) == "01:200"
#guard call .eip2565 1000 (hex (w32 1 ++ w32 1 ++ w32 1 ++ "05" ++ "03" ++ "07")) == "06:200"
-- Exponent longer than 32 bytes: 2 ^ (2^256) mod 1000003, and the length term of the price.
#guard call .eip2565 100000 (hex (w32 1 ++ w32 33 ++ w32 3 ++ "02" ++ "01" ++ w32 0 ++ "0f4243")) ==
  toHex (natToBE 3 (2 ^ (2 ^ 256 % 1000002) % 1000003)) ++ ":200"
#guard gasCost .eip2565 1 33 3 1 == 200 && gasCost .eip2565 64 40 64 1 == 1365
#guard gasCost .eip7883 64 40 64 1 == 16384 && gasCost .eip7883 32 1 32 0 == 500
-- Osaka length bound, and the local refusal bound on the earlier rule.
#guard call .eip7883 (1 <<< 64) (hex (w32 1025 ++ w32 1 ++ w32 1)) == "failure"
#guard call .eip2565 (1 <<< 80) (hex (w32 1 ++ w32 (maxExponentBytes + 1) ++ w32 1 ++ "02")) == "refusal"
#guard call .eip2565 (1 <<< 80) (hex (w32 (maxOperandBytes + 1) ++ w32 1 ++ w32 1)) == "refusal"
#guard call .eip2565 (1 <<< 80) (hex (w32 (maxOperandBytes + 1) ++ w32 1 ++ w32 0)) ==
  ":" ++ toString (gasCost .eip2565 (maxOperandBytes + 1) 1 0 0)

#print axioms run_underfunded
#print axioms run_success
#print axioms run_success_bounded
#print axioms run_refuses_over_bound
#print axioms run_osaka_length_bound
#print axioms powByte_lt
#print axioms powBytes_lt
#print axioms gasCost_minimum

end EVMCleanroom.Precompiles.ModExp
