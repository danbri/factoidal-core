/-
L4Factoidal.Crypto.RsaOaep — RSAES-OAEP (RFC 8017 §7.1): MGF1 (Appendix
B.2.1), EME-OAEP encoding (§7.1.1 step 2) and decoding (§7.1.2 step 3) in
pure Lean, over the RSA public and private operations of HACL*.

Consumers: XML Encryption `rsa-oaep-mgf1p` (SHA-1, MGF1 with SHA-1) and JWE
`RSA-OAEP` (SHA-1) and `RSA-OAEP-256` (SHA-256, MGF1 with SHA-256), RFC 7518
§4.3. Tracking: https://github.com/danbri/factoidal/issues/1082.

## Why this module is under `Crypto/` and not under `JOSE/`

RSAES-OAEP is used by two formats (XML Encryption and JWE). The JWS-only
padding EMSA-PKCS1-v1_5 is in `JOSE/Pkcs1.lean` because only JWS and XML
Signature RS256 use it through the JOSE code. OAEP has no JOSE-specific
part, so it is beside the primitive it pads.

## What is pure Lean and what is HACL*

  * HACL*: the RSA public operation `m^e mod n` (RSAEP, RFC 8017 §5.1.1;
    `Rsa.rsaPublicOp`, `Crypto/RsaNative.lean`) and the private operation
    `c^d mod n` (RSADP, RFC 8017 §5.1.2; `rsaPrivateOp` here), both through
    `ffi/hacl_rsa.c`. The private operation uses
    `Hacl_Bignum64_mod_exp_consttime`. We write no modular arithmetic.
  * Pure Lean: MGF1, EME-OAEP encoding and decoding, and the length checks.
    These are a padding construction over an unmodified hash (SHA-1 from
    `Crypto/SHA1.lean`, SHA-256 from `Crypto/SHA2.lean`), the same class as
    `Crypto/Hmac.lean` and `JOSE/Pkcs1.lean` under
    `skills/crypto-policy/SKILL.md`.

Every function and theorem here takes the RSA operations and the hash as
PARAMETERS (`RsaOp`, `OaepHash`). So each theorem holds for any function of
that type, and no theorem depends on an `opaque`. The `@[extern]` functions
are passed in only by the named instances at the end of this file.

## Manger's attack (CRYPTO 2001) and the single refusal

An OAEP decoder that tells the caller WHICH check failed (the leading octet
`Y` is not zero; the label hash differs; no `0x01` separator) gives an
attacker an oracle that decrypts any ciphertext in about `log2 n` queries.
Wycheproof marks these vectors `InvalidOaepPadding` (CVE-2020-26939).

`emeDecode` computes every check on every input, in the same order, with no
early return:

  * the leading octet `Y` goes into an accumulator as a byte;
  * the label hash comparison is an OR over the XOR of all `hLen` octet
    pairs (`ctDiff`);
  * the scan for the `0x01` separator (`scan`) reads every octet of `DB`
    after the label hash; its state is byte masks (`0xFF` or `0x00`) built
    with `ctIsZero`, and the position of the separator is added with a
    multiplication by the mask bit, not chosen with a branch.

Then one `if` on the OR of the four accumulators gives `some M` or `none`.
`none` is the only failure value, and the type has no other. The checks
that come before that `if` and can return `none` early (`em.length = k`,
`2 hLen + 2 ≤ k`, the label-hash length, and in `oaepDecrypt` the
ciphertext length and the refusal of the private operation, which happens
when `c ≥ n`) depend only on public values: lengths, the key and the
ciphertext.

Limit of this statement: Lean's compiler does not promise constant-time
code. The design above removes the data-dependent early exits and the
distinguishable errors, which are the oracle Manger's attack needs. It
does not prove that the compiled C has no timing difference (for example
in `Nat` arithmetic or allocation). No theorem here says so.

## Theorems

  * `xorMask_xorMask`: applying a mask twice gives the input back.
  * `emeEncode_length`: an encoded message is exactly `k` octets and starts
    with `0x00`.
  * `emeDecode_emeEncode`: decoding an encoded message gives the message
    back, for every hash function and every seed.
  * `oaepDecrypt_oaepEncrypt`: the same through the RSA operations, under
    the hypothesis that the private operation inverts the public one (RSA
    correctness, which is a property of the key, not of this code).

Test vectors: `L4Factoidal/Crypto/RsaOaepTests.lean` (build-time `#guard`s
with a pure Lean reference modular exponentiation) and section `rsa-oaep`
of `Harness/CryptoProbe.lean` (`lake exe l4crypto-probe`, the HACL*
operations, the RSA Laboratories `oaep-vect.txt` and Wycheproof vectors).

## Trust statement

`rsaPrivateOp` is `opaque`: Lean knows its type and nothing about its value.
What is trusted: HACL*'s bignum arithmetic
(`Hacl_Bignum64_mod_exp_consttime`, `third_party/hacl/`, cryspen/
hacl-packages commit 05c3d8fb321ed65e3db3a6a8b853019e86fb40a2, Apache-2.0)
and the shim `ffi/hacl_rsa.c` (length checks, one right-alignment copy,
the zeroisation of its copies of `d`). Not checked: that `(n, d)` is a real
RSA key pair; that the caller's seed is random (the seed is a parameter;
the host gives it).
-/
import L4Factoidal.Crypto.SHA1
import L4Factoidal.Crypto.SHA2
import L4Factoidal.Crypto.RsaNative

namespace L4Factoidal.Crypto.RsaOaep

open L4Factoidal.Crypto

/-! ## The RSA private operation (HACL*) -/

/-- The RSA private operation `c^d mod n` (RFC 8017 §5.1.2 RSADP, the
`(n, d)` key form) via HACL* `Hacl_Bignum64_mod_exp_consttime`, over
big-endian octet strings. The result, when present, is `n.size` octets. The
EMPTY `ByteArray` is every refusal: a modulus that is not 2048, 3072 or 4096
bits, a ciphertext whose length is not `n.size` or that is not less than
`n`, an empty `d` or a `d` longer than `n`, an even modulus, an allocation
failure. This is not a decryption: see `oaepDecrypt`. -/
@[extern "l4_hacl_rsa_private_op"]
opaque rsaPrivateOpRaw (n : @& ByteArray) (d : @& ByteArray)
    (c : @& ByteArray) : ByteArray

/-- `rsaPrivateOpRaw` with the empty-means-refusal convention read into
`Option`. -/
def rsaPrivateOp (n d c : ByteArray) : Option ByteArray :=
  let r := rsaPrivateOpRaw n d c
  if r.size == 0 then none else some r

/-- The type of an RSA operation: `op n x y` is `y^x mod n` as `n.size`
big-endian octets, or `none` when the operation is refused. Both
`Rsa.rsaPublicOp` (with `x = e`) and `rsaPrivateOp` (with `x = d`) have
this type. -/
abbrev RsaOp := ByteArray → ByteArray → ByteArray → Option ByteArray

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

/-! ## RSAES-OAEP (RFC 8017 §7.1.1 and §7.1.2) -/

/-- RSAES-OAEP-ENCRYPT((n, e), M, L) with the seed given by the caller (the
host's random source). `pubOp` is the RSA public operation; the result is
the `k`-octet ciphertext. -/
def oaepEncrypt (H : OaepHash) (pubOp : RsaOp) (n e msg label seed : ByteArray) :
    Option ByteArray :=
  match emeEncode H n.size (ofBA label) (ofBA msg) (ofBA seed) with
  | none => none
  | some em => pubOp n e (toBA em)

/-- RSAES-OAEP-DECRYPT((n, d), C, L). `privOp` is the RSA private
operation. One failure value, `none`, for every failure. -/
def oaepDecrypt (H : OaepHash) (privOp : RsaOp) (n d c label : ByteArray) :
    Option ByteArray :=
  if c.size ≠ n.size then none
  else
    match privOp n d c with
    | none => none
    | some em => (emeDecode H n.size (ofBA label) (ofBA em)).map toBA

/-- **Round trip through RSA.** If the private operation inverts the public
one on the outputs of the public one (RSA correctness for the key pair, a
property of `(n, e, d)` and of the two operations, never of this code),
then decryption of an encryption gives the message back. -/
theorem oaepDecrypt_oaepEncrypt {H : OaepHash} {pubOp privOp : RsaOp}
    {n e d msg label seed c : ByteArray}
    (hrsa : ∀ x y, pubOp n e x = some y → y.size = n.size ∧ privOp n d y = some x)
    (h : oaepEncrypt H pubOp n e msg label seed = some c) :
    oaepDecrypt H privOp n d c label = some msg := by
  unfold oaepEncrypt at h
  split at h
  · simp at h
  · next em hem =>
      obtain ⟨hsz, hpriv⟩ := hrsa _ _ h
      unfold oaepDecrypt
      rw [if_neg (by omega), hpriv]
      simp only [ofBA_toBA]
      rw [emeDecode_emeEncode hem]
      simp [toBA_ofBA]

/-! ## Named instances at the executable edge -/

/-- XML Encryption `rsa-oaep-mgf1p` and JWE `RSA-OAEP`: SHA-1, MGF1-SHA-1,
HACL* private operation. -/
def rsaOaepSha1Decrypt (n d c label : ByteArray) : Option ByteArray :=
  oaepDecrypt oaepSha1 rsaPrivateOp n d c label

/-- JWE `RSA-OAEP-256`: SHA-256, MGF1-SHA-256, HACL* private operation. -/
def rsaOaepSha256Decrypt (n d c label : ByteArray) : Option ByteArray :=
  oaepDecrypt oaepSha256 rsaPrivateOp n d c label

/-- `rsa-oaep-mgf1p` / `RSA-OAEP` encryption with the HACL* public
operation. `seed` must be 20 random octets from the host. -/
def rsaOaepSha1Encrypt (n e msg label seed : ByteArray) : Option ByteArray :=
  oaepEncrypt oaepSha1 Rsa.rsaPublicOp n e msg label seed

/-- `RSA-OAEP-256` encryption with the HACL* public operation. `seed` must
be 32 random octets from the host. -/
def rsaOaepSha256Encrypt (n e msg label seed : ByteArray) : Option ByteArray :=
  oaepEncrypt oaepSha256 Rsa.rsaPublicOp n e msg label seed

end L4Factoidal.Crypto.RsaOaep
