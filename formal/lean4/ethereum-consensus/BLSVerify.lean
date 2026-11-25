import G1PublicKey
import G2Signature
import PairingTarget
import HashToField

namespace EthereumConsensus.BLS.Verify

inductive VerifyError where
  | keyAdmission (reason : AggregateError)
  | signatureAdmission (reason : G2.SignatureError)
  | hashFailure (reason : G2Map.MapError)
  | hashInfinity
  | pairingFailure (reason : String)
  deriving Repr, DecidableEq

def generator : AffinePoint :=
  ⟨0x17f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb,
   0x08b3f481e3aaa0f1a09e30ed741d8ae4fcf5e095d5d00af600db18cb2c04b3edd03cc744a2888ae40caa232946c5e7e1⟩

def messagePair (pk : AffinePoint) (h : G2Map.Point) : Array Nat :=
  #[pk.x, pk.y, h.x.re, h.x.im, h.y.re, h.y.im]

def signaturePair (sig : G2.Point) : Array Nat :=
  #[generator.x, generator.y, sig.x.re, sig.x.im, sig.y.re, sig.y.im]

def pairingEquation (pk : AffinePoint) (h : G2Map.Point) (sig : G2.Point) :
    Except VerifyError Bool :=
  match Target.tate (messagePair pk h) with
  | .error e => .error (.pairingFailure e)
  | .ok a =>
    match Target.tate (signaturePair sig) with
    | .error e => .error (.pairingFailure e)
    | .ok b => .ok (decide (a = b))

/-- Finite hash points only. Infinity and internal failures are not signature mismatches. -/
def verifyHash (pk : AffinePoint) (sig : G2.Point) (root : ByteArray) :
    Except VerifyError Bool :=
  match G2Map.hashSigningRoot root with
  | .error e => .error (.hashFailure e)
  | .ok none => .error .hashInfinity
  | .ok (some h) => pairingEquation pk h sig

/-- POP fast aggregate verification of one 32-byte signing root.
Caller must establish POP for every supplied key. This function does not establish
registry membership or possession. No private-key operation or external oracle. -/
def verifySigningRoot (keys : List ByteArray) (root signature : ByteArray) :
    Except VerifyError Bool :=
  match aggregatePublicKeys keys with
  | .error e => .error (.keyAdmission e)
  | .ok pk =>
    match G2.decodeSignature signature with
    | .error e => .error (.signatureAdmission e)
    | .ok sig => verifyHash pk sig root

/-- Kind: resource. Says: oversized key lists are refused before pairing.
Does not say: bounded wall-clock time of admitted lists. -/
theorem verify_over_limit (keys : List ByteArray) (root signature : ByteArray)
    (h : keys.length > maxAggregateKeys) :
    verifySigningRoot keys root signature = .error (.keyAdmission .resourceLimit) := by
  rw [verifySigningRoot, aggregatePublicKeys_over_limit keys h]

/-- Kind: linkage. Says: aggregate admission error is propagated.
Does not say: mathematical completeness of key validation. -/
theorem verify_key_error (keys : List ByteArray) (root signature : ByteArray)
    (e : AggregateError) (h : aggregatePublicKeys keys = .error e) :
    verifySigningRoot keys root signature = .error (.keyAdmission e) := by
  simp [verifySigningRoot, h]

/-- Kind: linkage. Says: admitted keys and failed signature admission propagate the error.
Does not say: completeness of G2 admission. -/
theorem verify_signature_error (keys : List ByteArray) (root signature : ByteArray)
    (pk : AffinePoint) (e : G2.SignatureError)
    (hk : aggregatePublicKeys keys = .ok pk) (hs : G2.decodeSignature signature = .error e) :
    verifySigningRoot keys root signature = .error (.signatureAdmission e) := by
  simp [verifySigningRoot, hk, hs]

/-- Kind: linkage. Says: admitted finite hash delegates to the actual two pairing computations.
Does not say: universal BLS/Tate refinement. -/
theorem verify_delegates (keys : List ByteArray) (root signature : ByteArray)
    (pk : AffinePoint) (sig : G2.Point) (h : G2Map.Point)
    (hk : aggregatePublicKeys keys = .ok pk)
    (hs : G2.decodeSignature signature = .ok sig)
    (hh : G2Map.hashSigningRoot root = .ok (some h)) :
    verifySigningRoot keys root signature = pairingEquation pk h sig := by
  simp [verifySigningRoot, verifyHash, hk, hs, hh]

/-- Kind: linkage. Says: both successful pairing results determine exact equality verdict.
Does not say: pairing mathematics is fully refined. -/
theorem pairingEquation_results (pk : AffinePoint) (h : G2Map.Point) (sig : G2.Point)
    (a b : Array Nat)
    (ha : Target.tate (messagePair pk h) = .ok a)
    (hb : Target.tate (signaturePair sig) = .ok b) :
    pairingEquation pk h sig = .ok (decide (a = b)) := by
  simp [pairingEquation, ha, hb]

/-- Kind: rejection. Says: hash error remains distinct from a false equation.
Does not say: hash refinement. -/
theorem verify_hash_error (pk : AffinePoint) (sig : G2.Point) (root : ByteArray)
    (e : G2Map.MapError) (h : G2Map.hashSigningRoot root = .error e) :
    verifyHash pk sig root = .error (.hashFailure e) := by
  simp [verifyHash, h]

/-- Kind: linkage. Says: true implies both exact executable pairings returned equal values.
Does not say: subgroup checks imply the normative mathematical BLS theorem. -/
theorem pairingEquation_true (pk : AffinePoint) (h : G2Map.Point) (sig : G2.Point)
    (hv : pairingEquation pk h sig = .ok true) :
    ∃ a : Array Nat, Target.tate (messagePair pk h) = .ok a ∧
      Target.tate (signaturePair sig) = .ok a := by
  cases ha : Target.tate (messagePair pk h) with
  | error e => simp [pairingEquation, ha] at hv
  | ok a =>
    cases hb : Target.tate (signaturePair sig) with
    | error e => simp [pairingEquation, ha, hb] at hv
    | ok b =>
      have he : a = b := by simpa [pairingEquation, ha, hb] using hv
      exact ⟨a, rfl, hb.trans (congrArg Except.ok he.symm)⟩

#print axioms EthereumConsensus.BLS.Verify.verify_over_limit
#print axioms EthereumConsensus.BLS.Verify.verify_key_error
#print axioms EthereumConsensus.BLS.Verify.verify_signature_error
#print axioms EthereumConsensus.BLS.Verify.verify_delegates
#print axioms EthereumConsensus.BLS.Verify.pairingEquation_results
#print axioms EthereumConsensus.BLS.Verify.verify_hash_error
#print axioms EthereumConsensus.BLS.Verify.pairingEquation_true

end EthereumConsensus.BLS.Verify
