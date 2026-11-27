import EthereumWallet.Keys.Bip32

/-!
# BIP-32: theorems

The invalid-child rule, refusals, and the shape of derived keys. Axioms are printed at
the end. Agreement of public with private derivation is tested (BIP-32 vectors), not proved.
-/

namespace EthereumWallet.Keys.Bip32

/-- Kind: refusal (BIP-32 invalid child).
    Says: when `I_L` is the group order or more, there is no child key at this index. -/
theorem childKey?_il_out_of_range (il parentKey : Nat) (h : Secp.n ≤ il) :
    childKey? il parentKey = none := by
  simp [childKey?, h]

/-- Kind: refusal (BIP-32 invalid child).
    Says: when `I_L + k_par` is zero modulo the group order, there is no child key. -/
theorem childKey?_zero (il parentKey : Nat) (h : (il + parentKey) % Secp.n = 0) :
    childKey? il parentKey = none := by
  unfold childKey?
  by_cases h1 : Secp.n ≤ il
  · rw [if_pos h1]
  · rw [if_neg h1, if_pos h]

/-- Kind: range and value of an accepted child key.
    Says: an accepted child key is `(I_L + k_par) mod n`, is not zero, is below `n`, and
    `I_L` was below `n`.
    Does not say: that `n` is the true group order or that the key has a public point. -/
theorem childKey?_some (il parentKey k : Nat) (h : childKey? il parentKey = some k) :
    k = (il + parentKey) % Secp.n ∧ 0 < k ∧ k < Secp.n ∧ il < Secp.n := by
  unfold childKey? at h
  by_cases h1 : Secp.n ≤ il
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : (il + parentKey) % Secp.n = 0
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      injection h with h
      have hn : 0 < Secp.n := by omega
      have hlt := Nat.mod_lt (il + parentKey) hn
      omega

/-- Kind: refusal.
    Says: `I_L ≥ n` gives no child point either. -/
theorem childPoint?_il_out_of_range (il : Nat) (parent : Secp.Pub) (h : Secp.n ≤ il) :
    childPoint? il parent = none := by
  simp [childPoint?, h]

/-- Kind: refusal.
    Says: seeds shorter than 16 or longer than 64 bytes are refused with their length. -/
theorem master_seed_length (seed : ByteArray) (h : seed.size < 16 ∨ 64 < seed.size) :
    master seed = .error (.seedLength seed.size) := by
  unfold master
  rw [if_pos h]

/-- Kind: refusal (BIP-32 invalid master).
    Says: HMAC bytes whose left half is zero or the group order or more give no master key. -/
theorem masterOfI_invalid (i : ByteArray)
    (h : bytesToNatBE (i.extract 0 32) = 0 ∨ Secp.n ≤ bytesToNatBE (i.extract 0 32)) :
    masterOfI i = .error .invalidMaster := by
  unfold masterOfI
  rw [if_pos h]

theorem masterOfI_ok (i : ByteArray) (k : ExtPriv) (h : masterOfI i = .ok k) :
    0 < k.key ∧ k.key < Secp.n ∧ k.depth = 0 ∧ k.childNumber = 0 := by
  unfold masterOfI at h
  by_cases h2 : bytesToNatBE (i.extract 0 32) = 0 ∨ Secp.n ≤ bytesToNatBE (i.extract 0 32)
  · rw [if_pos h2] at h; cases h
  · rw [if_neg h2] at h
    injection h with h
    subst h
    exact ⟨by show 0 < bytesToNatBE (i.extract 0 32); omega,
      by show bytesToNatBE (i.extract 0 32) < Secp.n; omega, rfl, rfl⟩

/-- Kind: range.
    Says: an accepted master key is in `1 .. n-1`, at depth 0 with child number 0. -/
theorem master_ok (seed : ByteArray) (k : ExtPriv) (h : master seed = .ok k) :
    0 < k.key ∧ k.key < Secp.n ∧ k.depth = 0 ∧ k.childNumber = 0 := by
  unfold master at h
  by_cases h1 : seed.size < 16 ∨ 64 < seed.size
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    exact masterOfI_ok _ k h

/-- Kind: refusal.
    Says: a hardened child (index 2^31 or more) is never derived from a public key. -/
theorem ckdPub_hardened (parent : ExtPub) (index : Nat) (h : hardened ≤ index) :
    ckdPub parent index = .error .hardenedFromPublic := by
  unfold ckdPub
  rw [if_pos h]

/-- Kind: refusal. Says: an index of 2^32 or more is refused. -/
theorem ckdPriv_index_range (parent : ExtPriv) (index : Nat) (h : indexLimit ≤ index) :
    ckdPriv parent index = .error (.indexRange index) := by
  unfold ckdPriv
  rw [if_pos h]

/-- Kind: refusal. Says: a key at depth 255 has no children (the depth byte would wrap). -/
theorem ckdPriv_depth (parent : ExtPriv) (index : Nat) (hi : index < indexLimit)
    (h : 255 ≤ parent.depth) : ckdPriv parent index = .error .depthOverflow := by
  unfold ckdPriv
  rw [if_neg (by omega), if_pos h]

theorem childOfI_ok (parent child : ExtPriv) (pub : Secp.Pub) (index : Nat) (i : ByteArray)
    (h : childOfI parent pub index i = .ok child) :
    0 < child.key ∧ child.key < Secp.n ∧ child.depth = parent.depth + 1
      ∧ child.childNumber = index := by
  unfold childOfI at h
  cases hk : childKey? (bytesToNatBE (i.extract 0 32)) parent.key with
  | none => rw [hk] at h; cases h
  | some k =>
    rw [hk] at h
    injection h with h
    subst h
    have ⟨_, hk1, hk2, _⟩ := childKey?_some _ _ _ hk
    exact ⟨hk1, hk2, rfl, rfl⟩

/-- Kind: refusal (BIP-32 invalid child).
    Says: when the child-key rule refuses, derivation reports `invalidChild` for that index,
    whatever the HMAC bytes were. -/
theorem childOfI_invalid (parent : ExtPriv) (pub : Secp.Pub) (index : Nat) (i : ByteArray)
    (h : childKey? (bytesToNatBE (i.extract 0 32)) parent.key = none) :
    childOfI parent pub index i = .error (.invalidChild index) := by
  unfold childOfI
  rw [h]

/-- Kind: shape of a derived key.
    Says: a child from `ckdPriv` has a key in `1 .. n-1`, depth one more than its parent
    (at most 255) and the index asked for as its child number.
    Does not say: that the key equals what another implementation derives (vectors test that). -/
theorem ckdPriv_ok (parent child : ExtPriv) (index : Nat) (h : ckdPriv parent index = .ok child) :
    0 < child.key ∧ child.key < Secp.n ∧ child.depth = parent.depth + 1 ∧ child.depth ≤ 255
      ∧ child.childNumber = index ∧ index < indexLimit := by
  unfold ckdPriv at h
  by_cases h1 : indexLimit ≤ index
  · rw [if_pos h1] at h; cases h
  · rw [if_neg h1] at h
    by_cases h2 : 255 ≤ parent.depth
    · rw [if_pos h2] at h; cases h
    · rw [if_neg h2] at h
      cases hp : Secp.pubOfSecret parent.key with
      | none => rw [hp] at h; cases h
      | some pub =>
        rw [hp] at h
        have ⟨a, b, c, d⟩ := childOfI_ok parent child pub index _ h
        exact ⟨a, b, c, by omega, d, by omega⟩

/-- Kind: the proceeding rule (BIP-32 invalid child).
    Says: when the child at `index` is invalid and `index + 1` is in the same half of the
    index space, `ckdPrivNext` continues with `index + 1` and one attempt fewer. -/
theorem ckdPrivNext_skips (parent : ExtPriv) (attempts index j : Nat)
    (h : ckdPriv parent index = .error (.invalidChild j)) (hs : sameHalfNext index = true) :
    ckdPrivNext parent (attempts + 1) index = ckdPrivNext parent attempts (index + 1) := by
  simp [ckdPrivNext, h, hs]

/-- Kind: the proceeding rule.
    Says: a valid child at `index` is returned as it is; nothing is skipped. -/
theorem ckdPrivNext_ok (parent child : ExtPriv) (attempts index : Nat)
    (h : ckdPriv parent index = .ok child) :
    ckdPrivNext parent (attempts + 1) index = .ok child := by
  simp [ckdPrivNext, h]

/-- Kind: bound.
    Says: with no attempts left the answer is a refusal, so at most `attempts` derivations run. -/
theorem ckdPrivNext_zero (parent : ExtPriv) (index : Nat) :
    ckdPrivNext parent 0 index = .error (.invalidChild index) := rfl

/-- Kind: the proceeding rule, public side. -/
theorem ckdPubNext_skips (parent : ExtPub) (attempts index j : Nat)
    (h : ckdPub parent index = .error (.invalidChild j)) (hs : sameHalfNext index = true) :
    ckdPubNext parent (attempts + 1) index = ckdPubNext parent attempts (index + 1) := by
  simp [ckdPubNext, h, hs]

/-- Kind: refusal (work bound). Says: a path text over 256 bytes is refused unread. -/
theorem parsePath_too_long (s : String) (h : maxPathBytes < s.toUTF8.size) :
    parsePath s = .error .badPath := by
  show (if maxPathBytes < s.toUTF8.size then Except.error Error.badPath else _) = _
  rw [if_pos h]

/-- Kind: shape.
    Says: the Ethereum BIP-44 path has purpose 44', coin type 60', a hardened account,
    change 0 and a normal address index, for account and index below 2^31. -/
theorem ethereumPath_ok (account index : Nat) (ha : account < hardened) (hi : index < hardened) :
    ethereumPath account index
      = .ok [44 + hardened, 60 + hardened, account + hardened, 0, index] := by
  unfold ethereumPath
  rw [if_neg (by omega)]

/-- Kind: refusal. Says: bytes that are not 78 long are not an extended key. -/
theorem ofBytes_size (b : ByteArray) (h : b.size ≠ 78) :
    ExtKey.ofBytes b = .error (.badExtendedKey "not 78 bytes") := by
  unfold ExtKey.ofBytes
  rw [if_pos h]

end EthereumWallet.Keys.Bip32

open EthereumWallet.Keys.Bip32 in
#print axioms childKey?_il_out_of_range
open EthereumWallet.Keys.Bip32 in
#print axioms childKey?_zero
open EthereumWallet.Keys.Bip32 in
#print axioms childKey?_some
open EthereumWallet.Keys.Bip32 in
#print axioms childPoint?_il_out_of_range
open EthereumWallet.Keys.Bip32 in
#print axioms master_seed_length
open EthereumWallet.Keys.Bip32 in
#print axioms masterOfI_invalid
open EthereumWallet.Keys.Bip32 in
#print axioms childOfI_invalid
open EthereumWallet.Keys.Bip32 in
#print axioms master_ok
open EthereumWallet.Keys.Bip32 in
#print axioms ckdPub_hardened
open EthereumWallet.Keys.Bip32 in
#print axioms ckdPriv_index_range
open EthereumWallet.Keys.Bip32 in
#print axioms ckdPriv_depth
open EthereumWallet.Keys.Bip32 in
#print axioms ckdPriv_ok
open EthereumWallet.Keys.Bip32 in
#print axioms ckdPrivNext_skips
open EthereumWallet.Keys.Bip32 in
#print axioms ckdPrivNext_ok
open EthereumWallet.Keys.Bip32 in
#print axioms ckdPrivNext_zero
open EthereumWallet.Keys.Bip32 in
#print axioms ckdPubNext_skips
open EthereumWallet.Keys.Bip32 in
#print axioms parsePath_too_long
open EthereumWallet.Keys.Bip32 in
#print axioms ethereumPath_ok
open EthereumWallet.Keys.Bip32 in
#print axioms ofBytes_size
