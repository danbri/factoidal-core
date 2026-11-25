import Lean

/-! Experimental pairing target field for BLS12-381.
Six coefficients of w, each an (Fp real, Fp imaginary) pair.
u² = -1 and w⁶ = 1+u. No signature verdict. -/
namespace EthereumConsensus.BLS.Target

def modulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab
def order : Nat :=
  0x73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001
def finalExponent : Nat := (modulus^12-1)/order

def canonical (a : Array Nat) : Bool :=
  (a.size == 12) && a.all (fun x => decide (x < modulus))

def zero : Array Nat := Array.replicate 12 0
def one : Array Nat := #[1,0,0,0,0,0,0,0,0,0,0,0]

private def addF (a b : Nat) : Nat := (a+b)%modulus
private def subF (a b : Nat) : Nat := (a+modulus-b%modulus)%modulus
private def mulF (a b : Nat) : Nat := (a*b)%modulus

/-- Convolution in Fp2[w], folding each degree >= 6 once using w^6 = 1+u. -/
def multiplyRaw (a b : Array Nat) : Array Nat := Id.run do
  let mut c := zero
  for i in [:6] do
    for j in [:6] do
      let ar := a[2*i]!
      let ai := a[2*i+1]!
      let br := b[2*j]!
      let bi := b[2*j+1]!
      let re := subF (mulF ar br) (mulF ai bi)
      let im := addF (mulF ar bi) (mulF ai br)
      let (re, im) := if i+j ≥ 6 then (subF re im, addF re im) else (re, im)
      let k := 2*((i+j)%6)
      c := c.set! k (addF c[k]! re)
      c := c.set! (k+1) (addF c[k+1]! im)
  return c

def powLoop : Nat → Array Nat → Nat → Array Nat → Array Nat
  | 0, _, _, acc => acc
  | n+1, b, e, acc =>
    if e = 0 then acc
    else powLoop n (multiplyRaw b b) (e/2)
      (if e%2 = 1 then multiplyRaw acc b else acc)

inductive FieldError where
  | width
  | noncanonical
  | exponentLimit
  | zeroFinalInput
  | internalInvariant
  deriving Repr, DecidableEq

private def admitInput (a : Array Nat) : Except FieldError Unit :=
  if a.size ≠ 12 then .error .width
  else if canonical a then .ok () else .error .noncanonical

private def checkedOutput (a : Array Nat) : Except FieldError (Array Nat) :=
  if canonical a then .ok a else .error .internalInvariant

def multiply (a b : Array Nat) : Except FieldError (Array Nat) := do
  admitInput a
  admitInput b
  checkedOutput (multiplyRaw a b)

def power (a : Array Nat) (e : Nat) : Except FieldError (Array Nat) := do
  admitInput a
  if e ≥ 2^4572 then throw .exponentLimit
  checkedOutput (powLoop 4572 a e one)

def finalPower (a : Array Nat) : Except FieldError (Array Nat) := do
  admitInput a
  if a = zero then throw .zeroFinalInput
  power a finalExponent

/-- Kind: admission. Says: wrong-width first operand refuses before multiplication.
Does not say: the transport bounds allocations before reading. -/
theorem multiply_width (a b : Array Nat) (h : a.size ≠ 12) :
    multiply a b = .error .width := by
  simp [multiply,admitInput,h]

/-- Kind: admission. Says: noncanonical input refuses before multiplication.
Does not say: field representation completeness. -/
theorem multiply_noncanonical (a b : Array Nat) (h : a.size = 12)
    (hc : canonical a ≠ true) : multiply a b = .error .noncanonical := by
  simp [multiply,admitInput,h,hc]

/-- Kind: output invariant. Says: the actual checked output is canonical and unchanged.
Does not say: the arithmetic is a mathematical field. -/
theorem checkedOutput_ok (a out : Array Nat) (h : checkedOutput a = .ok out) :
    out = a ∧ canonical out = true := by
  by_cases hc : canonical a = true
  · simp only [checkedOutput,if_pos hc,Except.ok.injEq] at h
    subst out
    exact ⟨rfl,hc⟩
  · simp only [checkedOutput,if_neg hc] at h
    cases h

/-- Kind: recurrence. Says: zero remaining exponent returns the accumulator.
Does not say: general exponentiation refinement. -/
theorem powLoop_zero_exp (n : Nat) (b acc : Array Nat) :
    powLoop n b 0 acc = acc := by
  cases n <;> simp [powLoop]

/-- Kind: recurrence. Says: one unit of fuel and exponent one computes one product.
Does not say: the multiplication algorithm is correct in the quotient field. -/
theorem powLoop_one (b acc : Array Nat) :
    powLoop 1 b 1 acc = multiplyRaw acc b := by
  simp [powLoop]

/-- Kind: admission. Says: an admitted operand with an oversized exponent refuses.
Does not say: an exact wall-clock resource bound. -/
theorem power_limit (a : Array Nat) (e : Nat) (h : a.size = 12)
    (hc : canonical a = true) (he : e ≥ 2^4572) :
    power a e = .error .exponentLimit := by
  simp [power,admitInput,h,hc,he]

#print axioms EthereumConsensus.BLS.Target.multiply_width
#print axioms EthereumConsensus.BLS.Target.multiply_noncanonical
#print axioms EthereumConsensus.BLS.Target.checkedOutput_ok
#print axioms EthereumConsensus.BLS.Target.powLoop_zero_exp
#print axioms EthereumConsensus.BLS.Target.powLoop_one
#print axioms EthereumConsensus.BLS.Target.power_limit

end EthereumConsensus.BLS.Target

open EthereumConsensus.BLS.Target

private def parseCoefficients (xs : List String) : Except String (Array Nat) := do
  if xs.length ≠ 12 then throw "width"
  let mut result := #[]
  for x in xs do
    match x.toNat? with
    | none => throw "invalid_decimal"
    | some n => result := result.push n
  return result

private def errorName : FieldError → String
  | .width => "width"
  | .noncanonical => "noncanonical"
  | .exponentLimit => "exponent_limit"
  | .zeroFinalInput => "zero_final_input"
  | .internalInvariant => "internal_invariant"

private def dispatch (s : String) : Except String String := do
  let parts := (s.splitOn " ").filter (· ≠ "")
  let result ← match parts with
    | "mul" :: xs => do
      if xs.length ≠ 24 then throw "width"
      let a ← parseCoefficients (xs.take 12)
      let b ← parseCoefficients (xs.drop 12)
      (multiply a b).mapError errorName
    | "pow" :: e :: xs => do
      let a ← parseCoefficients xs
      match e.toNat? with
      | none => throw "invalid_decimal"
      | some n => (power a n).mapError errorName
    | "final" :: xs => do
      let a ← parseCoefficients xs
      (finalPower a).mapError errorName
    | _ => throw "operation"
  return "ok " ++ String.intercalate " " (result.toList.map toString)

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := if line.utf8ByteSize > 4096 then .error "resource_limit"
                  else dispatch line.trimAscii.toString
    output.putStrLn (match result with
      | .ok value => value
      | .error error => "error " ++ error)
    output.flush
