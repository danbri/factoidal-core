import Lean
import L4Factoidal.Crypto.SHA2

/-! Experimental public-message hash-to-field for BLS12-381 G2.
RFC 9380 sections 5.2, 5.3.1, 8.8.2. No secret inputs, signing or
signature verdict. The fixed Ethereum entry accepts a 32-byte signing root. -/
namespace EthereumConsensus.BLS.HashField

open L4Factoidal.Crypto (sha256)

def modulus : Nat :=
  0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab

def maxMessage : Nat := 4096
def popDST : ByteArray := "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_".toUTF8

inductive HashError where
  | resourceLimit
  | dstWidth
  | signingRootWidth
  | internalInvariant
  deriving Repr, DecidableEq

private def singleton (n : Nat) : ByteArray := ByteArray.empty.push (UInt8.ofNat n)

private def xorDigest (a b : ByteArray) : ByteArray := Id.run do
  let mut out := ByteArray.empty
  for i in [:32] do
    out := out.push (a[i]! ^^^ b[i]!)
  return out

/-- Eight SHA-256 blocks for count=2, m=2, L=64.
Called only after message/DST admission. -/
private def expand256 (msg dst : ByteArray) : ByteArray := Id.run do
  let dstPrime := dst ++ singleton dst.size
  let zPad : ByteArray := ⟨Array.replicate 64 0⟩
  let b0 := sha256 (zPad ++ msg ++ singleton 1 ++ singleton 0 ++ singleton 0 ++ dstPrime)
  let mut previous := sha256 (b0 ++ singleton 1 ++ dstPrime)
  let mut out := previous
  for i in [:7] do
    previous := sha256 (xorDigest b0 previous ++ singleton (i+2) ++ dstPrime)
    out := out ++ previous
  return out

private def reduceChunk (data : ByteArray) (offset : Nat) : Nat := Id.run do
  let mut n := 0
  for i in [:64] do
    n := n*256 + data[offset+i]!.toNat
  return n % modulus

def canonical (a : Array Nat) : Bool :=
  (a.size == 4) && a.all (fun v => decide (v < modulus))

private def coefficients (data : ByteArray) : Array Nat :=
  #[reduceChunk data 0, reduceChunk data 64, reduceChunk data 128, reduceChunk data 192]

private def checkedCoefficients (data : ByteArray) : Except HashError (Array Nat) :=
  if data.size ≠ 256 then .error .internalInvariant
  else
    let result := coefficients data
    if canonical result then .ok result else .error .internalInvariant

/-- Generic short-DST test entry. The development bounds are not RFC invalidity.
The output is (u[0].re, u[0].im, u[1].re, u[1].im). -/
def hashToField (msg dst : ByteArray) : Except HashError (Array Nat) :=
  if msg.size > maxMessage then .error .resourceLimit
  else if dst.size = 0 ∨ dst.size > 255 then .error .dstWidth
  else checkedCoefficients (expand256 msg dst)

/-- Ethereum POP suite entry for public consensus signing roots. -/
def consensusHashToField (root : ByteArray) : Except HashError (Array Nat) :=
  if root.size ≠ 32 then .error .signingRootWidth
  else hashToField root popDST

/-- Kind: resource admission. Says: oversized messages refuse before expansion.
Does not say: host transport allocates only bounded memory. -/
theorem hashToField_over_limit (msg dst : ByteArray) (h : msg.size > maxMessage) :
    hashToField msg dst = .error .resourceLimit := by
  simp only [hashToField,if_pos h]

/-- Kind: admission. Says: the short-DST entry refuses empty or oversized DST.
Does not say: RFC long-DST preprocessing is implemented. -/
theorem hashToField_bad_dst (msg dst : ByteArray) (hm : ¬ msg.size > maxMessage)
    (hd : dst.size = 0 ∨ dst.size > 255) :
    hashToField msg dst = .error .dstWidth := by
  simp only [hashToField,if_neg hm,if_pos hd]

/-- Kind: linkage. Says: an admitted request uses the actual SHA expansion.
Does not say: that expansion refines the full RFC mathematical definition. -/
theorem hashToField_delegates (msg dst : ByteArray) (hm : ¬ msg.size > maxMessage)
    (hd : ¬ (dst.size = 0 ∨ dst.size > 255)) :
    hashToField msg dst = checkedCoefficients (expand256 msg dst) := by
  simp only [hashToField,if_neg hm,if_neg hd]

/-- Kind: output invariant. Says: success returns exactly the computed canonical coefficients.
Does not say: cryptographic security or completeness of expansion. -/
theorem checkedCoefficients_ok (data : ByteArray) (out : Array Nat)
    (h : checkedCoefficients data = .ok out) :
    out = coefficients data ∧ canonical out = true := by
  by_cases hw : data.size ≠ 256
  · simp only [checkedCoefficients,if_pos hw] at h
    cases h
  · by_cases hc : canonical (coefficients data) = true
    · simp only [checkedCoefficients,if_neg hw,if_pos hc,Except.ok.injEq] at h
      subst out
      exact ⟨rfl,hc⟩
    · simp only [checkedCoefficients,if_neg hw,if_neg hc] at h
      cases h

/-- Kind: linkage. Says: public hash-to-field success has canonical coefficients.
Does not say: the map to an elliptic curve or signature verification is implemented. -/
theorem hashToField_ok (msg dst : ByteArray) (out : Array Nat)
    (h : hashToField msg dst = .ok out) : canonical out = true := by
  by_cases hm : msg.size > maxMessage
  · simp only [hashToField,if_pos hm] at h
    cases h
  · by_cases hd : dst.size = 0 ∨ dst.size > 255
    · simp only [hashToField,if_neg hm,if_pos hd] at h
      cases h
    · rw [hashToField_delegates msg dst hm hd] at h
      exact (checkedCoefficients_ok (expand256 msg dst) out h).2

/-- Kind: admission. Says: the consensus entry refuses non-32-byte roots.
Does not say: the supplied root is authenticated. -/
theorem consensusHashToField_wrong_width (root : ByteArray) (h : root.size ≠ 32) :
    consensusHashToField root = .error .signingRootWidth := by
  simp only [consensusHashToField,if_pos h]

/-- Kind: linkage. Says: admitted consensus roots use the fixed POP domain.
Does not say: the domain proves possession or authenticates a signature. -/
theorem consensusHashToField_delegates (root : ByteArray) (h : root.size = 32) :
    consensusHashToField root = hashToField root popDST := by
  have hn : ¬ root.size ≠ 32 := fun hne => hne h
  simp only [consensusHashToField,if_neg hn]

#print axioms EthereumConsensus.BLS.HashField.hashToField_over_limit
#print axioms EthereumConsensus.BLS.HashField.hashToField_bad_dst
#print axioms EthereumConsensus.BLS.HashField.hashToField_delegates
#print axioms EthereumConsensus.BLS.HashField.checkedCoefficients_ok
#print axioms EthereumConsensus.BLS.HashField.hashToField_ok
#print axioms EthereumConsensus.BLS.HashField.consensusHashToField_wrong_width
#print axioms EthereumConsensus.BLS.HashField.consensusHashToField_delegates

end EthereumConsensus.BLS.HashField

-- Test-only byte transport. No host hash or field answer.
open EthereumConsensus.BLS.HashField
private def nibble (b : UInt8) : Except String UInt8 :=
  if 48 ≤ b && b ≤ 57 then .ok (b-48)
  else if 97 ≤ b && b ≤ 102 then .ok (b-97+10)
  else .error "invalid_hex"

private def readHex (s : String) : Except String ByteArray := do
  if s = "-" then return ByteArray.empty
  let b := s.toUTF8
  if b.size % 2 != 0 then throw "invalid_hex"
  let mut out := ByteArray.empty
  for i in [:b.size/2] do
    let hi ← nibble b[2*i]!
    let lo ← nibble b[2*i+1]!
    out := out.push (16*hi+lo)
  return out

private def errorName : HashError → String
  | .resourceLimit => "resource_limit"
  | .dstWidth => "dst_width"
  | .signingRootWidth => "signing_root_width"
  | .internalInvariant => "internal_invariant"

private def dispatch (s : String) : Except String String := do
  let result ← match s.splitOn " " with
    | ["pop", root] => do
      let bytes ← readHex root
      (consensusHashToField bytes).mapError errorName
    | ["field", msg, dst] => do
      let m ← readHex msg
      let d ← readHex dst
      (hashToField m d).mapError errorName
    | _ => throw "operation"
  return "ok " ++ String.intercalate " " (result.toList.map toString)

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let result := if line.utf8ByteSize > 9000 then .error "resource_limit"
                  else dispatch line.trimAscii.toString
    output.putStrLn (match result with
      | .ok value => value
      | .error error => "error " ++ error)
    output.flush
