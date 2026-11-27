import L4Factoidal.Crypto.Hmac

/-!
# PBKDF2 (RFC 8018 section 5.2) over HMAC-SHA-512 and HMAC-SHA-256

The HMAC key pads are computed once per derivation (`HmacKey`), and
`HmacKey.mac512_eq` / `mac256_eq` prove the prepared form equal to
`L4Factoidal.Crypto.hmacSha512` / `hmacSha256`.

Bounds: `derive` refuses zero iterations, more than `maxIterations`, a zero output
length and more than `maxDkLen` bytes; each refusal is a theorem. The loops are
structural and tail recursive on the iteration and block counts.

Not constant-time claims: the hash works on fixed-width words and its control flow does
not depend on data values, at source level; the Lean compiler and runtime are trusted
and no machine-level timing was measured. The password, pads and intermediate blocks
are immutable heap values, freed by reference counting, not zeroised.
-/

namespace EthereumWallet.Keys

open L4Factoidal.Crypto

/-- The two HMAC pad blocks for a key, computed once. -/
structure HmacKey where
  ipad : ByteArray
  opad : ByteArray

def HmacKey.ofSha512 (key : ByteArray) : HmacKey :=
  let k0 := hmacKey0With sha512 128 key
  ⟨xorPadWith 128 k0 0x36, xorPadWith 128 k0 0x5c⟩

def HmacKey.mac512 (k : HmacKey) (msg : ByteArray) : ByteArray :=
  sha512 (k.opad ++ sha512 (k.ipad ++ msg))

def HmacKey.ofSha256 (key : ByteArray) : HmacKey :=
  let k0 := hmacKey0With sha256 64 key
  ⟨xorPadWith 64 k0 0x36, xorPadWith 64 k0 0x5c⟩

def HmacKey.mac256 (k : HmacKey) (msg : ByteArray) : ByteArray :=
  sha256 (k.opad ++ sha256 (k.ipad ++ msg))

/-- Kind: equality with the reference form.
    Says: the prepared-key HMAC-SHA-512 is `hmacSha512`, for every key and message.
    Does not say: that `hmacSha512` is HMAC-SHA-512 (RFC 4231 vectors test that). -/
theorem HmacKey.mac512_eq (key msg : ByteArray) :
    (HmacKey.ofSha512 key).mac512 msg = hmacSha512 key msg := by
  rw [hmacSha512_eq_hmacWith]; rfl

/-- Kind: equality with the reference form. Says: the same for HMAC-SHA-256. -/
theorem HmacKey.mac256_eq (key msg : ByteArray) :
    (HmacKey.ofSha256 key).mac256 msg = hmacSha256 key msg := by
  rw [hmacSha256_eq_hmacWith]; rfl

namespace Pbkdf2

inductive Error where
  | zeroIterations
  | tooManyIterations (iterations : Nat)
  | zeroLength
  | tooLong (dkLen : Nat)
  deriving DecidableEq, Repr

/-- Largest iteration count accepted (2^26, about 67 million). -/
def maxIterations : Nat := 67108864

/-- Largest derived key accepted, in bytes. -/
def maxDkLen : Nat := 65536

/-- `U_2 xor ... xor U_c` folded onto `acc`; `count` is what is left to do. -/
def fold (prf : ByteArray → ByteArray) (u acc : ByteArray) : Nat → ByteArray
  | 0 => acc
  | count + 1 =>
    let u' := prf u
    fold prf u' (xorBytes acc u') count

/-- `F (P, S, c, i)`. -/
def block (prf : ByteArray → ByteArray) (salt : ByteArray) (iterations index : Nat) : ByteArray :=
  let u1 := prf (salt ++ int32BE index)
  fold prf u1 u1 (iterations - 1)

/-- `T_i ‖ T_{i+1} ‖ ...`, `count` blocks from block number `index`. -/
def blocks (prf : ByteArray → ByteArray) (salt : ByteArray) (iterations : Nat) :
    Nat → Nat → ByteArray → ByteArray
  | 0, _, acc => acc
  | count + 1, index, acc =>
    blocks prf salt iterations count (index + 1) (acc ++ block prf salt iterations index)

/-- PBKDF2 without parameter checks; `hLen` is the PRF output size and must not be 0. -/
def raw (prf : ByteArray → ByteArray) (hLen : Nat) (salt : ByteArray)
    (iterations dkLen : Nat) : ByteArray :=
  (blocks prf salt iterations ((dkLen + hLen - 1) / hLen) 1 ByteArray.empty).extract 0 dkLen

/-- PBKDF2 with the parameter bounds checked first. -/
def derive (prf : ByteArray → ByteArray) (hLen : Nat) (salt : ByteArray)
    (iterations dkLen : Nat) : Except Error ByteArray :=
  if iterations = 0 then .error .zeroIterations
  else if maxIterations < iterations then .error (.tooManyIterations iterations)
  else if dkLen = 0 then .error .zeroLength
  else if maxDkLen < dkLen then .error (.tooLong dkLen)
  else .ok (raw prf hLen salt iterations dkLen)

/-- PBKDF2-HMAC-SHA-512. -/
def hmacSha512 (password salt : ByteArray) (iterations dkLen : Nat) : Except Error ByteArray :=
  derive (HmacKey.ofSha512 password).mac512 64 salt iterations dkLen

/-- PBKDF2-HMAC-SHA-256. -/
def hmacSha256 (password salt : ByteArray) (iterations dkLen : Nat) : Except Error ByteArray :=
  derive (HmacKey.ofSha256 password).mac256 32 salt iterations dkLen

/-- Kind: refusal. Says: zero iterations are refused. -/
theorem derive_zero_iterations (prf : ByteArray → ByteArray) (hLen : Nat) (salt : ByteArray)
    (dkLen : Nat) : derive prf hLen salt 0 dkLen = .error .zeroIterations := by
  simp [derive]

/-- Kind: refusal (work bound).
    Says: more than `maxIterations` iterations are refused, before any hashing.
    Does not say: how long `maxIterations` iterations take on a given machine. -/
theorem derive_too_many (prf : ByteArray → ByteArray) (hLen : Nat) (salt : ByteArray)
    (iterations dkLen : Nat) (h : maxIterations < iterations) :
    derive prf hLen salt iterations dkLen = .error (.tooManyIterations iterations) := by
  have h0 : iterations ≠ 0 := by intro h0; rw [h0] at h; exact absurd h (by decide)
  simp [derive, h0, h]

/-- Kind: refusal (memory bound).
    Says: a derived key of more than `maxDkLen` bytes is refused. -/
theorem derive_too_long (prf : ByteArray → ByteArray) (hLen : Nat) (salt : ByteArray)
    (iterations dkLen : Nat) (h : maxDkLen < dkLen) :
    (∃ e, derive prf hLen salt iterations dkLen = .error e) := by
  unfold derive
  have h0 : dkLen ≠ 0 := by intro h0; rw [h0] at h; exact absurd h (by decide)
  by_cases h1 : iterations = 0
  · exact ⟨_, by rw [if_pos h1]⟩
  · by_cases h2 : maxIterations < iterations
    · exact ⟨_, by rw [if_neg h1, if_pos h2]⟩
    · exact ⟨_, by rw [if_neg h1, if_neg h2, if_neg h0, if_pos h]⟩

/-- Kind: bound on accepted parameters.
    Says: an accepted derivation used between 1 and `maxIterations` iterations and
    asked for between 1 and `maxDkLen` bytes. -/
theorem derive_ok_bounds (prf : ByteArray → ByteArray) (hLen : Nat) (salt out : ByteArray)
    (iterations dkLen : Nat) (h : derive prf hLen salt iterations dkLen = .ok out) :
    0 < iterations ∧ iterations ≤ maxIterations ∧ 0 < dkLen ∧ dkLen ≤ maxDkLen := by
  unfold derive at h
  by_cases h1 : iterations = 0
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : maxIterations < iterations
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      by_cases h3 : dkLen = 0
      · rw [if_pos h3] at h; cases h
      · rw [if_neg h3] at h
        by_cases h4 : maxDkLen < dkLen
        · rw [if_pos h4] at h; cases h
        · omega

end Pbkdf2

end EthereumWallet.Keys

open EthereumWallet.Keys in
#print axioms HmacKey.mac512_eq
open EthereumWallet.Keys in
#print axioms HmacKey.mac256_eq
open EthereumWallet.Keys in
#print axioms Pbkdf2.derive_zero_iterations
open EthereumWallet.Keys in
#print axioms Pbkdf2.derive_too_many
open EthereumWallet.Keys in
#print axioms Pbkdf2.derive_too_long
open EthereumWallet.Keys in
#print axioms Pbkdf2.derive_ok_bounds
