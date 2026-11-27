import L4Factoidal.Crypto.Hmac
import EVMCleanroom.Precompiles.Basic

/-!
# RFC 6979 deterministic nonces (HMAC-SHA-256)

The nonce generation of RFC 6979 section 3.2, written from the RFC, for a
group order `q` of any bit length and SHA-256 as the hash (so `hlen = 256`).
HMAC and SHA-256 are the repository's pure `L4Factoidal.Crypto` modules.

`search` walks the candidate sequence of step (h): a candidate outside
`[1, q-1]` is skipped, and the caller's `accept` may also reject a candidate
(ECDSA rejects one that gives `r = 0` or `s = 0`), in which case the next one
is taken, as the RFC prescribes. The walk has an explicit fuel; running out is
a defined refusal (`none`), not a hang. For a 256-bit order a candidate is
out of range with probability below 2⁻¹²⁷, so the fuel is never reached in
practice.

Proved: any accepted candidate lies in `[1, q-1]`. Tested: the nonce values,
against RFC 6979 appendix A.2.5 (P-256 order, SHA-256) and published
secp256k1 signatures.

Secrets: the private key enters HMAC as bytes. The SHA-256 here works on
`UInt32` words with no secret-dependent branch in its source; the conversion
of the key from `Nat` to bytes is not constant-time. See the design note.
-/

namespace EthereumWallet.Rfc6979

open L4Factoidal.Crypto (hmacSha256)
open EVMCleanroom.Precompiles (natToBE)

def beNat (b : ByteArray) : Nat := b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- Bit length of the group order (`qlen`). -/
def qlen (q : Nat) : Nat := Nat.log2 q + 1

/-- Byte length of the group order (`rlen / 8`). -/
def rolen (q : Nat) : Nat := (qlen q + 7) / 8

/-- RFC 6979 section 2.3.2: the leftmost `qlen` bits as an integer. -/
def bits2int (q : Nat) (b : ByteArray) : Nat :=
  if 8 * b.size > qlen q then beNat b >>> (8 * b.size - qlen q) else beNat b

/-- Section 2.3.3. -/
def int2octets (q x : Nat) : ByteArray := natToBE (rolen q) x

/-- Section 2.3.4. -/
def bits2octets (q : Nat) (b : ByteArray) : ByteArray := int2octets q (bits2int q b % q)

structure State where
  k : ByteArray
  v : ByteArray

/-- Steps (b) to (g) of section 3.2 for private key `x` and message hash `h1`. -/
def init (q x : Nat) (h1 : ByteArray) : State :=
  let v0 : ByteArray := ⟨Array.replicate 32 1⟩
  let k0 : ByteArray := ⟨Array.replicate 32 0⟩
  let seed := int2octets q x ++ bits2octets q h1
  let k1 := hmacSha256 k0 (v0 ++ ⟨#[0]⟩ ++ seed)
  let v1 := hmacSha256 k1 v0
  let k2 := hmacSha256 k1 (v1 ++ ⟨#[1]⟩ ++ seed)
  ⟨k2, hmacSha256 k2 v1⟩

/-- Step (h.2): extend `T` by `blocks` HMAC outputs. Returns the last `V` and `T`. -/
def genT (k : ByteArray) : Nat → ByteArray → ByteArray → ByteArray × ByteArray
  | 0, v, t => (v, t)
  | blocks+1, v, t => genT k blocks (hmacSha256 k v) (t ++ hmacSha256 k v)

/-- One round of step (h): the candidate, and the state for the next round. -/
def step (q : Nat) (st : State) : Nat × State :=
  let vt := genT st.k ((qlen q + 255) / 256) st.v ByteArray.empty
  let k' := hmacSha256 st.k (vt.1 ++ ⟨#[0]⟩)
  (bits2int q vt.2, ⟨k', hmacSha256 k' vt.1⟩)

/-- The first candidate in `[1, q-1]` that `accept` takes, within `fuel` rounds. -/
def search {α : Type} (q : Nat) (accept : Nat → Option α) : Nat → State → Option α
  | 0, _ => none
  | fuel+1, st =>
    if 0 < (step q st).1 ∧ (step q st).1 < q then
      match accept (step q st).1 with
      | some a => some a
      | none => search q accept fuel (step q st).2
    else search q accept fuel (step q st).2

/-- The first in-range candidate (the nonce when ECDSA accepts it). -/
def nonce (q x : Nat) (h1 : ByteArray) : Option Nat :=
  search q (fun k => some k) 64 (init q x h1)

/-- Kind: range.
    Says: whatever `search` returns was produced by `accept` on a candidate in `[1, q-1]`.
    Does not say: the candidates are those of RFC 6979 (tested), or that one is found. -/
theorem search_range {α : Type} (q : Nat) (accept : Nat → Option α) (fuel : Nat) (st : State)
    (a : α) (h : search q accept fuel st = some a) :
    ∃ k, 0 < k ∧ k < q ∧ accept k = some a := by
  induction fuel generalizing st with
  | zero => simp [search] at h
  | succ fuel ih =>
    rw [search] at h
    by_cases hr : 0 < (step q st).1 ∧ (step q st).1 < q
    · rw [if_pos hr] at h
      cases hacc : accept (step q st).1 with
      | some b =>
        rw [hacc] at h
        exact ⟨_, hr.1, hr.2, by rw [hacc]; exact h⟩
      | none =>
        rw [hacc] at h
        exact ih _ h
    · rw [if_neg hr] at h
      exact ih _ h

/-- Kind: range.
    Says: a nonce returned by `nonce` lies in `[1, q-1]`.
    Does not say: it is unpredictable (that rests on HMAC-SHA-256) or always found. -/
theorem nonce_range (q x : Nat) (h1 : ByteArray) (k : Nat) (h : nonce q x h1 = some k) :
    0 < k ∧ k < q := by
  obtain ⟨k', hpos, hlt, hacc⟩ := search_range q _ 64 _ k h
  cases hacc
  exact ⟨hpos, hlt⟩

/-- Kind: resource bound.
    Says: with no fuel left the search refuses.
    Does not say: how much fuel a given input needs. -/
theorem search_zero {α : Type} (q : Nat) (accept : Nat → Option α) (st : State) :
    search q accept 0 st = none := rfl

#print axioms search_range
#print axioms nonce_range
#print axioms search_zero

end EthereumWallet.Rfc6979
