/-
L4Factoidal.Crypto.OaepEncoding — the EME-OAEP encoding of RFC 8017 §7.1 (hash parameter,
MGF1, `emeEncode`, the constant-shape `emeDecode` and their round-trip theorem), with no
RSA operation and no `@[extern]`.

These definitions were the middle of `Crypto/RsaOaep.lean` until 2026-11-14 and are moved
here unchanged, in the same namespace (`L4Factoidal.Crypto.RsaOaep`), so every name is as
before. `Crypto/RsaOaep.lean` imports this module and keeps the RSA private operation (an
extern over HACL*) and RSAES-OAEP over it. The split lets a consumer that brings its own RSA
operation (the web engine's `Crypto/WebCryptoKeys.lean`, over `WebHacl.rsaPublic?` and
`rsaPrivate?`) take the encoding without the other module's externs.

What this module is: an encoding, not a primitive. It calls a hash given as a parameter and
does list arithmetic. What it does not show: constant time. `emeDecode` is written in a
constant shape (one pass, no early exit, masks), but Lean lists allocate, so its timing is
not claimed secret-independent (see the header of `Crypto/RsaOaep.lean`, and
`skills/lean-risk-flags`).

No `sorry`, no `axiom`, no `partial`.
-/
import L4Factoidal.Crypto.SHA1
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Crypto.RsaOaep

open L4Factoidal.Crypto

/-! ## Hash parameter -/

/-- The hash of an OAEP instance: the function and its output length
`hLen` in octets. One hash serves as the label hash and as the MGF1 hash in
every instance this tree uses. -/
structure OaepHash where
  hash : ByteArray → ByteArray
  hLen : Nat

/-- SHA-1, for XML Encryption `rsa-oaep-mgf1p` and JWE `RSA-OAEP`. -/
def oaepSha1 : OaepHash := ⟨sha1, 20⟩

/-- SHA-256, for JWE `RSA-OAEP-256`. -/
def oaepSha256 : OaepHash := ⟨sha256, 32⟩

/-! ## Octet-list helpers -/

def toBA (l : List UInt8) : ByteArray := ⟨l.toArray⟩

def ofBA (b : ByteArray) : List UInt8 := b.data.toList

theorem ofBA_toBA (l : List UInt8) : ofBA (toBA l) = l := by
  simp [ofBA, toBA]

theorem toBA_ofBA (b : ByteArray) : toBA (ofBA b) = b := by
  simp [ofBA, toBA]

/-- I2OSP(c, 4), RFC 8017 §4.1, for the MGF1 counter. -/
def i2osp4 (c : Nat) : List UInt8 :=
  [UInt8.ofNat (c / 16777216 % 256), UInt8.ofNat (c / 65536 % 256),
   UInt8.ofNat (c / 256 % 256), UInt8.ofNat (c % 256)]

/-! ## MGF1 (RFC 8017 Appendix B.2.1) -/

/-- MGF1: `T = Hash(Z || I2OSP(0, 4)) || Hash(Z || I2OSP(1, 4)) || ...`,
the first `maskLen` octets. The RFC's "mask too long" error
(`maskLen > 2^32 hLen`) cannot occur for a modulus of at most 4096 bits. -/
def mgf1 (H : OaepHash) (seed : List UInt8) (maskLen : Nat) : List UInt8 :=
  let blocks := (maskLen + H.hLen - 1) / H.hLen
  ((List.range blocks).flatMap fun c => ofBA (H.hash (toBA (seed ++ i2osp4 c)))).take maskLen

/-- `a XOR m`, octet by octet, over the length of `a`. When `m` is shorter
than `a` the missing mask octets are zero. With that convention the
involution `xorMask_xorMask` holds for every mask. -/
def xorMask (a m : List UInt8) : List UInt8 :=
  List.zipWith (· ^^^ ·) a (m ++ List.replicate a.length 0)

theorem zipWith_xor_length (a b : List UInt8) (h : a.length ≤ b.length) :
    (List.zipWith (· ^^^ ·) a b).length = a.length := by
  simp [List.length_zipWith]; omega

theorem xorMask_length (a m : List UInt8) : (xorMask a m).length = a.length := by
  unfold xorMask
  apply zipWith_xor_length
  simp

theorem zipWith_xor_twice :
    ∀ (a b : List UInt8), a.length ≤ b.length →
      List.zipWith (· ^^^ ·) (List.zipWith (· ^^^ ·) a b) b = a
  | [], _, _ => by simp
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
      simp only [List.zipWith_cons_cons, List.cons.injEq]
      refine ⟨by simp [UInt8.xor_assoc], ?_⟩
      exact zipWith_xor_twice xs ys (by simp at h; omega)

/-- Applying the same mask twice gives the input back. -/
theorem xorMask_xorMask (a m : List UInt8) : xorMask (xorMask a m) m = a := by
  have hl := xorMask_length a m
  unfold xorMask at hl ⊢
  rw [hl]
  exact zipWith_xor_twice a _ (by simp)

/-! ## EME-OAEP encoding (RFC 8017 §7.1.1 step 2) -/

/-- EME-OAEP encoding of `msg` under `label` for a `k`-octet modulus, with
the seed given by the caller:

```
DB         = lHash || PS || 0x01 || M
maskedDB   = DB XOR MGF(seed, k - hLen - 1)
maskedSeed = seed XOR MGF(maskedDB, hLen)
EM         = 0x00 || maskedSeed || maskedDB
```

`none` when the message is too long (`mLen > k - 2 hLen - 2`, §7.1.1 step
1.b), when the seed is not `hLen` octets, or when the hash does not give
`hLen` octets. The seed must be random; that is the caller's obligation. -/
def emeEncode (H : OaepHash) (k : Nat) (label msg seed : List UInt8) :
    Option (List UInt8) :=
  let hLen := H.hLen
  let lHash := ofBA (H.hash (toBA label))
  if lHash.length = hLen ∧ seed.length = hLen ∧ msg.length + 2 * hLen + 2 ≤ k then
    let db := lHash ++ (List.replicate (k - msg.length - 2 * hLen - 2) 0 ++ (0x01 :: msg))
    let maskedDB := xorMask db (mgf1 H seed (k - hLen - 1))
    let maskedSeed := xorMask seed (mgf1 H maskedDB hLen)
    some (0x00 :: (maskedSeed ++ maskedDB))
  else none

/-- An encoded message is exactly `k` octets and starts with `0x00`. The
leading zero is what keeps `EM` numerically below the modulus. -/
theorem emeEncode_length {H : OaepHash} {k : Nat} {label msg seed em : List UInt8}
    (h : emeEncode H k label msg seed = some em) :
    em.length = k ∧ em.head? = some 0x00 := by
  unfold emeEncode at h
  dsimp only at h
  split at h
  · next hc =>
      obtain ⟨hl, hs, hm⟩ := hc
      cases h
      refine ⟨?_, rfl⟩
      simp only [List.length_cons, List.length_append, xorMask_length,
        List.length_replicate]
      omega
  · simp at h

/-! ## Constant-shape checks for decoding -/

/-- `0xFF` when `x = 0`, else `0x00`, with no branch: for `x = 0`,
`x - 1` wraps to `0xFFFFFFFF` in `UInt32`; for `1 ≤ x ≤ 255` the top byte
of `x - 1` is zero. -/
def ctIsZero (x : UInt8) : UInt8 := ((x.toUInt32 - 1) >>> 24).toUInt8

/-- `0xFF` when `a = b`, else `0x00`. -/
def ctEq (a b : UInt8) : UInt8 := ctIsZero (a ^^^ b)

/-- The OR of the XOR of all octet pairs: zero exactly when the two lists
agree on their common length. It reads every pair. -/
def ctDiff (a b : List UInt8) : UInt8 :=
  (List.zipWith (· ^^^ ·) a b).foldl (· ||| ·) 0

/-- The state of the separator scan. `looking` is `0xFF` until the first
`0x01` octet and `0x00` after it; `bad` is non-zero when an octet other
than `0x00` or `0x01` came before the separator; `start` is the index of
the first message octet (one past the separator); `pos` counts octets. -/
structure ScanState where
  looking : UInt8
  bad : UInt8
  start : Nat
  pos : Nat
  deriving DecidableEq, Repr

def scanInit : ScanState := ⟨0xFF, 0, 0, 0⟩

/-- One octet of the scan. Every field is updated on every octet; the
separator position enters `start` as a product with the mask bit. -/
def scanStep (s : ScanState) (b : UInt8) : ScanState :=
  let one := ctEq b 1
  let zero := ctIsZero b
  let found := s.looking &&& one
  { looking := s.looking &&& ~~~one,
    bad := s.bad ||| (s.looking &&& ~~~zero &&& ~~~one),
    start := s.start + (found &&& 1).toNat * (s.pos + 1),
    pos := s.pos + 1 }

/-- The scan over `PS || 0x01 || M`: it reads every octet. -/
def scan (l : List UInt8) : ScanState := l.foldl scanStep scanInit

/-! ## EME-OAEP decoding (RFC 8017 §7.1.2 step 3) -/

/-- EME-OAEP decoding of a `k`-octet encoded message. `some M` exactly when
`Y = 0x00`, the recovered label hash equals `Hash(label)`, and the octets
between the label hash and the first `0x01` are all `0x00`. Every failure
of those three checks gives the same `none`, and all three are computed on
every input before the one `if` that combines them. See the module header
for the public checks that come first. -/
def emeDecode (H : OaepHash) (k : Nat) (label em : List UInt8) :
    Option (List UInt8) :=
  let hLen := H.hLen
  let lHash := ofBA (H.hash (toBA label))
  if em.length = k ∧ 2 * hLen + 2 ≤ k ∧ lHash.length = hLen then
    let y := em.headD 0
    let maskedSeed := (em.drop 1).take hLen
    let maskedDB := em.drop (hLen + 1)
    let seed := xorMask maskedSeed (mgf1 H maskedDB hLen)
    let db := xorMask maskedDB (mgf1 H seed (k - hLen - 1))
    let rest := db.drop hLen
    let st := scan rest
    let flags := y ||| ctDiff (db.take hLen) lHash ||| st.bad ||| st.looking
    if flags = 0 then some (rest.drop st.start) else none
  else none

/-! ## Theorems about the scan and the round trip -/

theorem ctDiff_self (a : List UInt8) : ctDiff a a = 0 := by
  unfold ctDiff
  have : List.zipWith (· ^^^ ·) a a = List.replicate a.length (0 : UInt8) := by
    induction a with
    | nil => rfl
    | cons x xs ih => rw [List.zipWith_cons_cons, ih]; simp [List.replicate_succ]
  rw [this]
  generalize a.length = n
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem scan_zeros (z p : Nat) :
    (List.replicate z (0 : UInt8)).foldl scanStep ⟨0xFF, 0, 0, p⟩ = ⟨0xFF, 0, 0, p + z⟩ := by
  induction z generalizing p with
  | zero => rfl
  | succ z ih =>
      rw [List.replicate_succ, List.foldl_cons]
      have : scanStep ⟨0xFF, 0, 0, p⟩ 0 = ⟨0xFF, 0, 0, p + 1⟩ := by
        simp [scanStep, ctEq, ctIsZero]; decide
      rw [this, ih]; congr 1; omega

theorem scan_done (bad : UInt8) (st : Nat) :
    ∀ (l : List UInt8) (p : Nat),
      l.foldl scanStep ⟨0, bad, st, p⟩ = ⟨0, bad, st, p + l.length⟩
  | [], p => by simp
  | b :: bs, p => by
      rw [List.foldl_cons]
      have : scanStep ⟨0, bad, st, p⟩ b = ⟨0, bad, st, p + 1⟩ := by
        simp [scanStep]
      rw [this, scan_done bad st bs (p + 1)]
      simp; omega

theorem scan_padded (z : Nat) (msg : List UInt8) :
    scan (List.replicate z 0 ++ (0x01 :: msg)) = ⟨0, 0, z + 1, z + 1 + msg.length⟩ := by
  unfold scan scanInit
  rw [List.foldl_append, scan_zeros, Nat.zero_add, List.foldl_cons]
  have : scanStep ⟨0xFF, 0, 0, z⟩ 1 = ⟨0, 0, z + 1, z + 1⟩ := by
    simp [scanStep, ctEq, ctIsZero]; decide
  rw [this, scan_done]

/-- **Round trip.** For every hash, every label, every seed: decoding an
encoded message gives the message back. -/
theorem emeDecode_emeEncode {H : OaepHash} {k : Nat} {label msg seed em : List UInt8}
    (h : emeEncode H k label msg seed = some em) :
    emeDecode H k label em = some msg := by
  have hlen := (emeEncode_length h).1
  unfold emeEncode at h
  dsimp only at h
  split at h
  · next hc =>
      obtain ⟨hl, hs, hm⟩ := hc
      cases h
      -- names for the encoder's intermediate values
      generalize hdb : (ofBA (H.hash (toBA label)) ++
          (List.replicate (k - msg.length - 2 * H.hLen - 2) 0 ++ (0x01 :: msg))) = db at hlen ⊢
      generalize hmdb : xorMask db (mgf1 H seed (k - H.hLen - 1)) = maskedDB at hlen ⊢
      have hms : (xorMask seed (mgf1 H maskedDB H.hLen)).length = H.hLen := by
        rw [xorMask_length, hs]
      unfold emeDecode
      have hk : 2 * H.hLen + 2 ≤ k := by omega
      rw [if_pos ⟨hlen, hk, hl⟩]
      simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero]
      rw [List.take_left' hms, List.drop_left' hms, xorMask_xorMask, ← hmdb, xorMask_xorMask, ← hdb]
      have htake : (ofBA (H.hash (toBA label)) ++
          (List.replicate (k - msg.length - 2 * H.hLen - 2) 0 ++ (0x01 :: msg))).take H.hLen
          = ofBA (H.hash (toBA label)) := List.take_left' hl
      have hdrop2 : (ofBA (H.hash (toBA label)) ++
          (List.replicate (k - msg.length - 2 * H.hLen - 2) 0 ++ (0x01 :: msg))).drop H.hLen
          = List.replicate (k - msg.length - 2 * H.hLen - 2) 0 ++ (0x01 :: msg) :=
        List.drop_left' hl
      rw [htake, hdrop2, scan_padded, ctDiff_self]
      simp only [UInt8.or_zero, if_true]
      generalize k - msg.length - 2 * H.hLen - 2 = z
      have hsplit : List.replicate z (0 : UInt8) ++ (0x01 :: msg)
          = (List.replicate z 0 ++ [0x01]) ++ msg := by simp
      rw [hsplit, List.drop_left' (by simp)]
  · simp at h

end L4Factoidal.Crypto.RsaOaep
