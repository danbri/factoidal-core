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
import L4Factoidal.Crypto.OaepEncoding

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
