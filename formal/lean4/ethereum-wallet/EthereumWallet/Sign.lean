import EthereumWallet.SignSecp
import EthereumWallet.SignRfc6979

/-!
# ECDSA signing on secp256k1 for Ethereum

`signHash` signs a 32-byte message hash with RFC 6979 nonces, normalises `s`
to the low half of the group order (EIP-2) and returns `(r, s, yParity)`.

Every signature is checked before it is returned: the shared recovery
function `Secp256k1.recover` is run on the result and must give back the
signer's public key, and the ranges are re-examined. A signature that fails
is not returned (`selfCheckFailed`). This costs one recovery per signature
and buys two things: the round-trip and range theorems below hold for every
returned signature without any group-law proof, and a fault in the scalar
multiplication cannot leak a wrong signature made with the right nonce.

Defined refusals: a key outside `[1, n-1]`, a hash that is not 32 bytes, an
all-zero hash (never the Keccak digest of a real payload; treated as a caller
error), fuel exhaustion in the nonce search, a nonce point whose abscissa is
at least `n` (probability about 2⁻¹²⁸; Ethereum's one-bit `yParity` cannot
express it), and a failed self-check.

Proved (each by the check that precedes the return): low `s`, `r` and `s` in
range, `yParity` a bit, recovery of the signer's key and address, the nonce
in `[1, n-1]`, and the refusals. Tested only: that signing succeeds for valid
input, that `r` and `s` are the RFC 6979 values, and agreement of the shared
recovery with the affine `SecpRecovery` used by transaction admission.

Signing is not constant-time (see `SignSecp.lean` and the design note); the
caller passes `Risk.Accepted .variableTimeSigning`.
-/

namespace EthereumWallet.Sign

open EVMCleanroom.Precompiles
open EVMCleanroom.Precompiles.Secp256k1 (n)
open EthereumWallet.Secp

inductive Error where
  | invalidKey
  | hashLength
  | zeroHash
  | nonceExhausted
  | highAbscissa
  | selfCheckFailed
  deriving DecidableEq, Repr

structure Signature where
  r : Nat
  s : Nat
  yParity : Nat
  deriving DecidableEq, Repr

/-- A private scalar with its public key. No `Repr`: a key pair is never printed. -/
structure KeyPair where
  secret : Nat
  x : Nat
  y : Nat

/-- The key pair of a private scalar; refused outside `[1, n-1]`. -/
def KeyPair.ofSecret (t : BaseTable) (d : Nat) : Option KeyPair :=
  if d = 0 ∨ n ≤ d then none
  else
    match mulBaseSecret t d with
    | some point => some ⟨d, point.1, point.2⟩
    | none => none

def KeyPair.address (kp : KeyPair) : Nat := addressOf kp.x kp.y

/-- EIP-2: replace `s` by `n − s` when it is in the high half; the parity bit flips with it. -/
def normalizeS (s parity : Nat) : Nat × Nat :=
  if n / 2 < s then (n - s, 1 - parity) else (s, parity)

/-- One ECDSA attempt with nonce `k` (SEC 1, section 4.1.3). `none` asks for the next nonce. -/
def attempt (t : BaseTable) (d z k : Nat) : Option (Except Error Signature) :=
  match mulBaseSecret t k with
  | none => none
  | some point =>
    if n ≤ point.1 then some (.error .highAbscissa)
    else if point.1 = 0 then none
    else if invFixed n k * ((z + point.1 * d) % n) % n = 0 then none
    else
      some (.ok ⟨point.1,
        (normalizeS (invFixed n k * ((z + point.1 * d) % n) % n) (point.2 % 2)).1,
        (normalizeS (invFixed n k * ((z + point.1 * d) % n) % n) (point.2 % 2)).2⟩)

/-- The check every signature passes before it is returned. -/
def finalCheck (kp : KeyPair) (z : Nat) (sig : Signature) : Except Error Signature :=
  if 0 < sig.r ∧ sig.r < n ∧ 0 < sig.s ∧ sig.s ≤ n / 2 ∧ sig.yParity < 2 ∧
      Secp256k1.recover z sig.yParity sig.r sig.s = some (kp.x, kp.y) then .ok sig
  else .error .selfCheckFailed

def nonceFuel : Nat := 64

/-- Sign a 32-byte hash. -/
def signHash (_ : Risk.Accepted .variableTimeSigning) (t : BaseTable) (kp : KeyPair)
    (hash : ByteArray) : Except Error Signature :=
  if hash.size ≠ 32 then .error .hashLength
  else if bytesToNat hash = 0 then .error .zeroHash
  else if kp.secret = 0 ∨ n ≤ kp.secret then .error .invalidKey
  else
    match Rfc6979.search n (attempt t kp.secret (bytesToNat hash)) nonceFuel
        (Rfc6979.init n kp.secret hash) with
    | none => .error .nonceExhausted
    | some (.error e) => .error e
    | some (.ok sig) => finalCheck kp (bytesToNat hash) sig

/-- The address recovered from a signature on a hash, by the shared recovery. -/
def recoverAddress (z : Nat) (sig : Signature) : Option Nat :=
  (Secp256k1.recover z sig.yParity sig.r sig.s).map fun point => addressOf point.1 point.2

/-- Kind: arithmetic (EIP-2).
    Says: for `s` in `[1, n-1]` the normalised `s` is in `[1, n/2]`.
    Does not say: the normalised pair is a valid signature (group law, not proved). -/
theorem normalizeS_low (s parity : Nat) (hpos : 0 < s) (hlt : s < n) :
    0 < (normalizeS s parity).1 ∧ (normalizeS s parity).1 ≤ n / 2 := by
  unfold normalizeS
  split <;> simp only <;> omega

/-- Kind: checked output.
    Says: a signature that passes the final check is unchanged, in range, has low `s`,
    and the shared recovery returns the key pair's public key from it.
    Does not say: the recovery function is the mathematical one. -/
theorem finalCheck_ok (kp : KeyPair) (z : Nat) (sig out : Signature)
    (h : finalCheck kp z sig = .ok out) :
    out = sig ∧ 0 < out.r ∧ out.r < n ∧ 0 < out.s ∧ out.s ≤ n / 2 ∧ out.yParity < 2 ∧
      Secp256k1.recover z out.yParity out.r out.s = some (kp.x, kp.y) := by
  unfold finalCheck at h
  split at h
  · rename_i hc
    cases h
    exact ⟨rfl, hc⟩
  · cases h

/-- Kind: round trip and EIP-2, for every returned signature.
    Says: if `signHash` returns a signature for a hash, then the hash has 32 bytes, `r` is in
    `[1, n-1]`, `s` is in `[1, n/2]`, `yParity` is 0 or 1, and `Secp256k1.recover` on that
    hash and signature gives exactly the key pair's public key.
    Does not say: signing succeeds for valid input, the public key is `[secret]G`, or the
    recovery is the mathematical ECDSA recovery (all tested, not proved). -/
theorem signHash_sound (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable)
    (kp : KeyPair) (hash : ByteArray) (sig : Signature)
    (h : signHash risk t kp hash = .ok sig) :
    hash.size = 32 ∧ 0 < sig.r ∧ sig.r < n ∧ 0 < sig.s ∧ sig.s ≤ n / 2 ∧ sig.yParity < 2 ∧
      Secp256k1.recover (bytesToNat hash) sig.yParity sig.r sig.s = some (kp.x, kp.y) := by
  unfold signHash at h
  split at h
  · cases h
  · rename_i hsize
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
        · exact ⟨Decidable.of_not_not hsize, (finalCheck_ok kp _ _ sig h).2⟩

/-- Kind: round trip at the address level.
    Says: the address recovered from a returned signature is the key pair's address.
    Does not say: more than `signHash_sound`. -/
theorem signHash_recovers_address (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable)
    (kp : KeyPair) (hash : ByteArray) (sig : Signature)
    (h : signHash risk t kp hash = .ok sig) :
    recoverAddress (bytesToNat hash) sig = some kp.address := by
  have hs := (signHash_sound risk t kp hash sig h).2.2.2.2.2.2
  simp [recoverAddress, hs, KeyPair.address]

/-- Kind: nonce range.
    Says: for a returned signature there is some `k` in `[1, n-1]` on which the ECDSA attempt
    produced it (before the final check).
    Does not say: that this `k` is the RFC 6979 candidate for this key and hash (`search_range`
    does not carry that; the nonce values are tested against vectors), or anything about
    its secrecy. -/
theorem signHash_nonce_range (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable)
    (kp : KeyPair) (hash : ByteArray) (sig : Signature)
    (h : signHash risk t kp hash = .ok sig) :
    ∃ k raw, 0 < k ∧ k < n ∧ attempt t kp.secret (bytesToNat hash) k = some (.ok raw) ∧
      finalCheck kp (bytesToNat hash) raw = .ok sig := by
  unfold signHash at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h
        · rename_i raw hsearch
          obtain ⟨k, hpos, hlt, hacc⟩ := Rfc6979.search_range n _ _ _ _ hsearch
          exact ⟨k, raw, hpos, hlt, hacc, h⟩

/-- Kind: refusal.
    Says: a hash that is not 32 bytes is refused.
    Does not say: anything else. -/
theorem signHash_hash_length (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable)
    (kp : KeyPair) (hash : ByteArray) (h : hash.size ≠ 32) :
    signHash risk t kp hash = .error .hashLength := by
  simp [signHash, h]

/-- Kind: refusal.
    Says: a 32-byte hash whose value is zero is refused, before the key is used.
    Does not say: such a hash could not be signed in ECDSA; refusing it is this package's rule. -/
theorem signHash_zero_hash (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable)
    (kp : KeyPair) (hash : ByteArray) (hsize : hash.size = 32) (hzero : bytesToNat hash = 0) :
    signHash risk t kp hash = .error .zeroHash := by
  simp [signHash, hsize, hzero]

/-- Kind: refusal.
    Says: with a private scalar outside `[1, n-1]`, a 32-byte non-zero hash is refused with
    `invalidKey`. (Other hashes are refused by `signHash_hash_length` and
    `signHash_zero_hash`, so such a key never signs.)
    Does not say: every scalar in range is a good key. -/
theorem signHash_invalid_key (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable)
    (kp : KeyPair) (hash : ByteArray) (hkey : kp.secret = 0 ∨ n ≤ kp.secret)
    (hsize : hash.size = 32) (hnz : bytesToNat hash ≠ 0) :
    signHash risk t kp hash = .error .invalidKey := by
  simp [signHash, hsize, hnz, hkey]

/-- Kind: refusal.
    Says: no key pair is made from a scalar outside `[1, n-1]`.
    Does not say: anything about scalars in range. -/
theorem ofSecret_invalid (t : BaseTable) (d : Nat) (h : d = 0 ∨ n ≤ d) :
    KeyPair.ofSecret t d = none := by
  simp [KeyPair.ofSecret, h]

/-- Kind: range and on-curve (checked at run time).
    Says: a key pair made by `ofSecret` holds the given scalar, which is in `[1, n-1]`, and
    its public point satisfies the curve equation.
    Does not say: the point is `[d]G` (tested against the shared `mulBase` and vectors). -/
theorem ofSecret_valid (t : BaseTable) (d : Nat) (kp : KeyPair)
    (h : KeyPair.ofSecret t d = some kp) :
    kp.secret = d ∧ 0 < d ∧ d < n ∧ Secp256k1.onCurve kp.x kp.y = true := by
  unfold KeyPair.ofSecret at h
  split at h
  · cases h
  · rename_i hrange
    split at h
    · rename_i point hmul
      cases h
      exact ⟨rfl, by omega, by omega, mulBaseSecret_onCurve t d point.1 point.2 hmul⟩
    · cases h

#print axioms normalizeS_low
#print axioms finalCheck_ok
#print axioms signHash_sound
#print axioms signHash_recovers_address
#print axioms signHash_nonce_range
#print axioms signHash_hash_length
#print axioms signHash_zero_hash
#print axioms signHash_invalid_key
#print axioms ofSecret_invalid
#print axioms ofSecret_valid

end EthereumWallet.Sign
