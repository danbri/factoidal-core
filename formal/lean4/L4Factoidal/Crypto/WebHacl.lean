/-
L4Factoidal.Crypto.WebHacl — the web engine's boundary to HACL*: the externs that
`crypto.subtle` of page scripts calls, each guarded by HACL*'s own precondition.

Record: docs/designissues/2026-11-09-hacl-web-crypto.md. C side: `ffi/hacl_webcrypto.c`
(the only C between page scripts and HACL*), over the vendored HACL* C of
`third_party/hacl/` (hacl-star/hacl-star f557259007db9933442dde10aa995c1b00bd3446,
Apache-2.0; `third_party/hacl/PROVENANCE.md`).

## The boundary, as types

Every extern takes a PROOF of its precondition as an argument. Proofs are erased when
Lean compiles, so the C function receives only the buffers; but no call site anywhere in
the tree type-checks unless it has established the precondition first. The
preconditions (`HashPre`, `HmacPre`, …) restate the F* preconditions of the HACL*
functions (Spec.Hash.Definitions, Hacl.HMAC, Hacl.Ed25519, Hacl.Curve25519, Hacl.P256,
Hacl.AEAD.Chacha20Poly1305): exact key, nonce, tag, signature and point lengths, and the
uint32_t bounds of the C API. So:

  * "no call passes a buffer shorter than the primitive's precondition" is a property
    of the TYPES of `hashRaw` … `chachaOpenRaw`, checked by Lean's kernel at every call;
  * the C glue checks the same lengths again (defence in depth for a caller outside
    Lean) and allocates each output itself, fresh, so outputs never alias inputs;
  * the wrappers (`hash?`, `hmac?`, …) decide the precondition (`if h : Pre then`), call
    the extern with that proof, and check the answer's size; `*_size` theorems prove the
    size of every answer they give, and `*_none_of_not` that they refuse (without a call)
    whatever fails the precondition.

## What is trusted (the TCB at this boundary)

The externs are `opaque`: Lean knows their types and nothing about their values. No
theorem here depends on what they compute, except the AGREEMENT theorems, which take
HACL*'s functional correctness as an explicit hypothesis (`HashAgrees`, `HmacAgrees`,
`CtEqAgrees`): HACL*'s F* proofs establish exactly these facts about the C, which Lean
trusts at the FFI boundary. Given them, `haclHash_eq_pure` proves the HACL* hash
records equal to the pure-Lean specification records of `Crypto.WebCrypto`, so HKDF,
PBKDF2 and HMAC_DRBG over HACL* ARE the specification functions.

The curves and the AEAD have no pure-Lean twin (the crypto policy forbids one: they
touch secrets); they are checked against the standard vectors at run time (record,
"Vectors").

SHA-3 and SHAKE (`sha3Raw`, HACL*'s `Hacl_Hash_SHA3`, added 2026-11-14) have no pure-Lean
twin either, so there is no agreement theorem for them and no fallback: where HACL*
cannot answer, `sha3?` answers `none` and the API refuses. Trusted: HACL*'s proof of
`Hacl_Hash_SHA3` against FIPS 202. Not checked in Lean: any value it computes (the FIPS 202
vectors are run at the C level, `tests/crypto/run-kat.sh`, and through WPT).

No `sorry`, no `axiom`, no `partial`.
-/
import L4Factoidal.Crypto.WebCrypto

namespace L4Factoidal.Crypto.WebHacl

open L4Factoidal.Crypto

/-- 2^32: HACL*'s C API takes every length as a `uint32_t`. -/
def u32Bound : Nat := 4294967296

/-! ## The hash family at the boundary -/

inductive HashAlg where
  | sha1 | sha256 | sha384 | sha512
  deriving DecidableEq, Repr, Inhabited

/-- The code `ffi/hacl_webcrypto.c` reads. -/
def HashAlg.code : HashAlg → UInt8
  | .sha1 => 1 | .sha256 => 2 | .sha384 => 3 | .sha512 => 4

def HashAlg.size : HashAlg → Nat
  | .sha1 => 20 | .sha256 => 32 | .sha384 => 48 | .sha512 => 64

def HashAlg.block : HashAlg → Nat
  | .sha1 => 64 | .sha256 => 64 | .sha384 => 128 | .sha512 => 128

/-- The pure-Lean specification record (`Crypto.WebCrypto`). -/
def HashAlg.pure : HashAlg → WebCrypto.Hash
  | .sha1 => WebCrypto.sha1H | .sha256 => WebCrypto.sha256H
  | .sha384 => WebCrypto.sha384H | .sha512 => WebCrypto.sha512H

def HashAlg.ofName? (n : String) : Option HashAlg :=
  match WebCrypto.asciiUpper n with
  | "SHA-1" => some .sha1 | "SHA-256" => some .sha256
  | "SHA-384" => some .sha384 | "SHA-512" => some .sha512
  | _ => none

def HashAlg.name (a : HashAlg) : String := a.pure.name

theorem HashAlg.pure_size (a : HashAlg) : a.pure.size = a.size := by cases a <;> rfl
theorem HashAlg.pure_block (a : HashAlg) : a.pure.block = a.block := by cases a <;> rfl

/-! ## Preconditions (HACL*'s F* preconditions, restated) -/

/-- Spec.Hash: `input_len ≤ max_input_length`, and the C API's `uint32_t`. -/
abbrev HashPre (msg : ByteArray) : Prop := msg.size < u32Bound
/-- The block size of a boundary code (`HashAlg.code`). -/
def blockOfCode (c : UInt8) : Nat := if c ≤ 2 then 64 else 128

theorem blockOfCode_code (a : HashAlg) : blockOfCode a.code = a.block := by cases a <;> rfl

/-- Hacl.HMAC.compute_st: `keysized a key_len` and `data_len + block_length a < 2^32`. -/
abbrev HmacPre (alg : UInt8) (key msg : ByteArray) : Prop :=
  key.size < u32Bound ∧ msg.size + blockOfCode alg < u32Bound
/-- Hacl.Ed25519.secret_to_public: a 32-byte private key. -/
abbrev Ed25519SkPre (sk : ByteArray) : Prop := sk.size = 32
/-- Hacl.Ed25519.sign: a 32-byte key and `msg_len + 64 ≤ max_size_t`. -/
abbrev Ed25519SignPre (sk msg : ByteArray) : Prop := sk.size = 32 ∧ msg.size + 64 < u32Bound
/-- Hacl.Ed25519.verify: a 32-byte public key, a 64-byte signature, `msg_len + 64 ≤ max_size_t`. -/
abbrev Ed25519VerifyPre (pk msg sig : ByteArray) : Prop :=
  pk.size = 32 ∧ sig.size = 64 ∧ msg.size + 64 < u32Bound
/-- Hacl.Curve25519: 32-byte scalar and u-coordinate. -/
abbrev X25519SkPre (sk : ByteArray) : Prop := sk.size = 32
abbrev X25519Pre (sk pk : ByteArray) : Prop := sk.size = 32 ∧ pk.size = 32
/-- Hacl.P256: a 32-byte private key (HACL* checks `0 < d < n` itself). -/
abbrev P256SkPre (sk : ByteArray) : Prop := sk.size = 32
/-- Hacl.P256: a 64-byte raw public key `x ‖ y` (HACL* checks the point itself). -/
abbrev P256PubPre (xy : ByteArray) : Prop := xy.size = 64
/-- SEC 1 compressed point: 33 bytes. -/
abbrev P256CompressedPre (c : ByteArray) : Prop := c.size = 33
/-- Hacl.P256.ecdsa_sign_p256_without_hash: `msg_len ≥ 32` (we pass exactly 32), 32-byte
key and nonce. -/
abbrev P256SignPre (sk e nonce : ByteArray) : Prop := sk.size = 32 ∧ e.size = 32 ∧ nonce.size = 32
/-- Hacl.P256.ecdsa_verif_without_hash: 64-byte key, `msg_len ≥ 32`, two 32-byte halves. -/
abbrev P256VerifyPre (xy e rs : ByteArray) : Prop := xy.size = 64 ∧ e.size = 32 ∧ rs.size = 64
/-- Hacl.P256.dh_responder: a 64-byte public key and a 32-byte private key. -/
abbrev P256EcdhPre (xy sk : ByteArray) : Prop := xy.size = 64 ∧ sk.size = 32
/-- Hacl.AEAD.Chacha20Poly1305.encrypt: 32-byte key, 12-byte nonce, lengths below 2^32
(and the sealed length too). -/
abbrev ChaChaSealPre (key nonce aad plain : ByteArray) : Prop :=
  key.size = 32 ∧ nonce.size = 12 ∧ aad.size < u32Bound ∧ plain.size + 16 < u32Bound
/-- Hacl.AEAD.Chacha20Poly1305.decrypt: as encrypt, and a 16-byte tag at the end. -/
abbrev ChaChaOpenPre (key nonce aad sealed : ByteArray) : Prop :=
  key.size = 32 ∧ nonce.size = 12 ∧ aad.size < u32Bound ∧ 16 ≤ sealed.size ∧ sealed.size < u32Bound + 16

/-- An RSA modulus at this boundary: big-endian with no leading zero octet, 1024 to 4096
bits in whole 64-bit limbs (Hacl_Bignum64's `len` limbs). -/
abbrev RsaModPre (n : ByteArray) : Prop := n.size % 8 = 0 ∧ 128 ≤ n.size ∧ n.size ≤ 512 ∧ n.get! 0 ≠ 0
/-- Hacl_Bignum64.mod_exp: the operand is |n| octets, the exponent 1 to |n| octets. -/
abbrev RsaOpPre (n ex x : ByteArray) : Prop := RsaModPre n ∧ 1 ≤ ex.size ∧ ex.size ≤ n.size ∧ x.size = n.size
/-- Hacl_RSAPSS.rsapss_sign: SHA-256/384/512 (codes 2-4), e with no leading zero octet,
the salt at most |n| octets, `msgLen` within the hash's bound. -/
abbrev RsaPssSignPre (alg : UInt8) (n e d salt msg : ByteArray) : Prop :=
  RsaModPre n ∧ 2 ≤ alg.toNat ∧ alg.toNat ≤ 4 ∧ 1 ≤ e.size ∧ e.size ≤ n.size ∧ e.get! 0 ≠ 0 ∧
    1 ≤ d.size ∧ d.size ≤ n.size ∧ salt.size ≤ n.size ∧ msg.size + 128 < u32Bound
abbrev RsaPssVerifyPre (alg : UInt8) (n e : ByteArray) (saltLen : USize) (sig msg : ByteArray) : Prop :=
  RsaModPre n ∧ 2 ≤ alg.toNat ∧ alg.toNat ≤ 4 ∧ 1 ≤ e.size ∧ e.size ≤ n.size ∧ e.get! 0 ≠ 0 ∧
    saltLen.toNat ≤ n.size ∧ sig.size = n.size ∧ msg.size + 128 < u32Bound

/-! ## SHA-3 and SHAKE (FIPS 202) at the boundary -/

/-- The FIPS 202 functions HACL* has at the pin (`Hacl_Hash_SHA3`). cSHAKE with a function
name or a customization, KMAC, TurboSHAKE and KangarooTwelve are not among them. -/
inductive Sha3Alg where
  | sha3_256 | sha3_384 | sha3_512 | shake128 | shake256
  deriving DecidableEq, Repr, Inhabited

/-- The code `ffi/hacl_webcrypto.c` reads (after the SHA-1 and SHA-2 codes 1-4). -/
def Sha3Alg.code : Sha3Alg → UInt8
  | .sha3_256 => 5 | .sha3_384 => 6 | .sha3_512 => 7 | .shake128 => 8 | .shake256 => 9

/-- The digest size in octets of the fixed-length functions; `none` for the two
extendable-output functions. -/
def Sha3Alg.fixed : Sha3Alg → Option Nat
  | .sha3_256 => some 32 | .sha3_384 => some 48 | .sha3_512 => some 64 | _ => none

/-- The most output asked of SHAKE in one call: 16 MiB (a bound on memory, not HACL*'s). -/
def maxXofBytes : Nat := 16777216

/-- Hacl.Hash.SHA3: the input and output lengths are `uint32_t`; the shim also wants a
known code and 1 to `maxXofBytes` octets of output. -/
abbrev Sha3Pre (alg : UInt8) (outLen : UInt32) (msg : ByteArray) : Prop :=
  5 ≤ alg.toNat ∧ alg.toNat ≤ 9 ∧ msg.size < u32Bound ∧ 1 ≤ outLen.toNat ∧ outLen.toNat ≤ maxXofBytes

/-! ## The externs (`ffi/hacl_webcrypto.c`). Each takes its precondition's proof. -/

@[extern "l4_web_hacl_hash"]
opaque hashRaw (alg : UInt8) (msg : @& ByteArray) (h : HashPre msg) : ByteArray
@[extern "l4_web_hacl_hmac"]
opaque hmacRaw (alg : UInt8) (key msg : @& ByteArray) (h : HmacPre alg key msg) : ByteArray
/-- Constant-time equality (KaRaMeL's `FStar_UInt8_eq_mask` fold); lengths are public. -/
@[extern "l4_web_hacl_ct_eq"]
opaque ctEqRaw (a b : @& ByteArray) : UInt8
@[extern "l4_web_hacl_ed25519_public"]
opaque ed25519PublicRaw (sk : @& ByteArray) (h : Ed25519SkPre sk) : ByteArray
@[extern "l4_web_hacl_ed25519_sign"]
opaque ed25519SignRaw (sk msg : @& ByteArray) (h : Ed25519SignPre sk msg) : ByteArray
@[extern "l4_web_hacl_ed25519_verify"]
opaque ed25519VerifyRaw (pk msg sig : @& ByteArray) (h : Ed25519VerifyPre pk msg sig) : UInt8
@[extern "l4_web_hacl_x25519_public"]
opaque x25519PublicRaw (sk : @& ByteArray) (h : X25519SkPre sk) : ByteArray
@[extern "l4_web_hacl_x25519"]
opaque x25519Raw (sk pk : @& ByteArray) (h : X25519Pre sk pk) : ByteArray
@[extern "l4_web_hacl_p256_public"]
opaque p256PublicRaw (sk : @& ByteArray) (h : P256SkPre sk) : ByteArray
@[extern "l4_web_hacl_p256_valid_public"]
opaque p256ValidPublicRaw (xy : @& ByteArray) (h : P256PubPre xy) : UInt8
@[extern "l4_web_hacl_p256_valid_private"]
opaque p256ValidPrivateRaw (sk : @& ByteArray) (h : P256SkPre sk) : UInt8
@[extern "l4_web_hacl_p256_decompress"]
opaque p256DecompressRaw (c : @& ByteArray) (h : P256CompressedPre c) : ByteArray
@[extern "l4_web_hacl_p256_sign"]
opaque p256SignRaw (sk e nonce : @& ByteArray) (h : P256SignPre sk e nonce) : ByteArray
@[extern "l4_web_hacl_p256_verify"]
opaque p256VerifyRaw (xy e rs : @& ByteArray) (h : P256VerifyPre xy e rs) : UInt8
@[extern "l4_web_hacl_p256_ecdh"]
opaque p256EcdhRaw (xy sk : @& ByteArray) (h : P256EcdhPre xy sk) : ByteArray
@[extern "l4_web_hacl_chachapoly_seal"]
opaque chachaSealRaw (key nonce aad plain : @& ByteArray) (h : ChaChaSealPre key nonce aad plain) : ByteArray
@[extern "l4_web_hacl_chachapoly_open"]
opaque chachaOpenRaw (key nonce aad sealed : @& ByteArray) (h : ChaChaOpenPre key nonce aad sealed) : ByteArray

@[extern "l4_web_hacl_sha3"]
opaque sha3Raw (alg : UInt8) (outLen : UInt32) (msg : @& ByteArray) (h : Sha3Pre alg outLen msg) : ByteArray

@[extern "l4_web_hacl_rsa_public"]
opaque rsaPublicRaw (n e x : @& ByteArray) (h : RsaOpPre n e x) : ByteArray
@[extern "l4_web_hacl_rsa_private"]
opaque rsaPrivateRaw (n d x : @& ByteArray) (h : RsaOpPre n d x) : ByteArray
@[extern "l4_web_hacl_rsapss_sign"]
opaque rsaPssSignRaw (alg : UInt8) (n e d salt msg : @& ByteArray) (h : RsaPssSignPre alg n e d salt msg) : ByteArray
@[extern "l4_web_hacl_rsapss_verify"]
opaque rsaPssVerifyRaw (alg : UInt8) (n e : @& ByteArray) (saltLen : USize) (sig msg : @& ByteArray) (h : RsaPssVerifyPre alg n e saltLen sig msg) : UInt8

/-! ## The wrappers: decide the precondition, call, check the answer's size -/

/-- The answer of an extern when it has the size the primitive writes; `none` (a refusal
the C made: an empty array) otherwise. -/
def checkSize (out : ByteArray) (n : Nat) : Option ByteArray := if out.size = n then some out else none

theorem checkSize_size {out r : ByteArray} {n : Nat} (h : checkSize out n = some r) : r.size = n := by
  unfold checkSize at h; split at h <;> simp_all

theorem checkSize_getD (out : ByteArray) (n : Nat) : (checkSize out n).getD out = out := by
  unfold checkSize; split <;> rfl

/-- A hash by HACL*; `none` only when the message is over HACL*'s bound (the API's
arguments are at most 64 MiB, so never in a page). -/
def hash? (a : HashAlg) (msg : ByteArray) : Option ByteArray :=
  if h : HashPre msg then
    checkSize (hashRaw a.code msg h) a.size
  else none

def hmac? (a : HashAlg) (key msg : ByteArray) : Option ByteArray :=
  if h : HmacPre a.code key msg then
    checkSize (hmacRaw a.code key msg h) a.size
  else none

/-- SHA-3 or SHAKE by HACL*, `outLen` octets of it. `none` when HACL* cannot answer: a
message over its bound, more output than `maxXofBytes`, or a fixed-length function asked
for another length. There is no second implementation to answer instead
(`skills/lean-risk-flags` §4: a verified path that cannot answer refuses). No octets of
output is the empty string, with no call. -/
def sha3? (a : Sha3Alg) (outLen : Nat) (msg : ByteArray) : Option ByteArray :=
  if (a.fixed.map (· != outLen)).getD false then none
  else if outLen = 0 then some ByteArray.empty
  else if outLen > maxXofBytes then none
  else if h : Sha3Pre a.code outLen.toUInt32 msg then checkSize (sha3Raw a.code outLen.toUInt32 msg h) outLen
  else none

/-- Kind: boundary guarantee (output size). Says: an answer of `sha3?` has exactly the
length asked for. Does not say: that the bytes are the FIPS 202 digest (that is HACL*'s
proof, trusted at the boundary). -/
theorem sha3?_size {a : Sha3Alg} {n : Nat} {m out : ByteArray} (h : sha3? a n m = some out) : out.size = n := by
  unfold sha3? at h
  split at h
  · cases h
  · split at h
    · rename_i hn; cases h; simp [hn]
    · split at h
      · cases h
      · split at h
        · exact checkSize_size h
        · cases h

/-- Kind: boundary guarantee (refusal). Says: a fixed-length SHA-3 function asked for any
length but its own answers nothing, so SHA3-256 can never be answered truncated or
extended. Does not say: anything of SHAKE, whose length is the caller's. -/
theorem sha3?_fixed {a : Sha3Alg} {k n : Nat} {m : ByteArray} (hf : a.fixed = some k) (hn : n ≠ k) :
    sha3? a n m = none := by
  unfold sha3?
  simp [hf, Ne.symm hn]

/-- The hash used by the API: HACL*'s, and the specification where HACL* refuses (never,
for an argument the API can give; see `hashFast_eq_pure`). -/
def hashFast (a : HashAlg) (msg : ByteArray) : ByteArray := (hash? a msg).getD (a.pure.run msg)
def hmacFast (a : HashAlg) (key msg : ByteArray) : ByteArray := (hmac? a key msg).getD (a.pure.mac key msg)

/-- The HACL* record of `a`: what the web engine computes with. -/
def haclHash (a : HashAlg) : WebCrypto.Hash :=
  { name := a.pure.name, run := hashFast a, block := a.pure.block, size := a.pure.size, mac := hmacFast a }

/-- Constant-time equality, in C (no secret-dependent branch in Lean or C). -/
def ctEq (a b : ByteArray) : Bool := a.size == b.size && ctEqRaw a b == 1

def ed25519Public? (sk : ByteArray) : Option ByteArray :=
  if h : Ed25519SkPre sk then
    checkSize (ed25519PublicRaw sk h) 32
  else none

def ed25519Sign? (sk msg : ByteArray) : Option ByteArray :=
  if h : Ed25519SignPre sk msg then
    checkSize (ed25519SignRaw sk msg h) 64
  else none

/-- A wrong-length key or signature verifies false, as WebCrypto §24 verify asks. -/
def ed25519Verify (pk msg sig : ByteArray) : Bool :=
  if h : Ed25519VerifyPre pk msg sig then ed25519VerifyRaw pk msg sig h == 1 else false

def x25519Public? (sk : ByteArray) : Option ByteArray :=
  if h : X25519SkPre sk then
    checkSize (x25519PublicRaw sk h) 32
  else none

/-- X25519; `none` also for the all-zero secret of a small-order point (HACL*'s
constant-time check, `Hacl_Curve25519_51_ecdh`). -/
def x25519? (sk pk : ByteArray) : Option ByteArray :=
  if h : X25519Pre sk pk then
    checkSize (x25519Raw sk pk h) 32
  else none

def p256Public? (sk : ByteArray) : Option ByteArray :=
  if h : P256SkPre sk then
    checkSize (p256PublicRaw sk h) 64
  else none

/-- HACL*'s public key validation: not infinity, coordinates below p, on the curve. -/
def p256ValidPublic (xy : ByteArray) : Bool :=
  if h : P256PubPre xy then p256ValidPublicRaw xy h == 1 else false

/-- `0 < d < n`. -/
def p256ValidPrivate (sk : ByteArray) : Bool :=
  if h : P256SkPre sk then p256ValidPrivateRaw sk h == 1 else false

def p256Decompress? (c : ByteArray) : Option ByteArray :=
  if h : P256CompressedPre c then
    checkSize (p256DecompressRaw c h) 64
  else none

def p256Sign? (sk e nonce : ByteArray) : Option ByteArray :=
  if h : P256SignPre sk e nonce then
    checkSize (p256SignRaw sk e nonce h) 64
  else none

def p256Verify (xy e rs : ByteArray) : Bool :=
  if h : P256VerifyPre xy e rs then p256VerifyRaw xy e rs h == 1 else false

/-- The x-coordinate of `d·Q` (32 bytes); HACL* checks `d` and `Q`. -/
def p256Ecdh? (xy sk : ByteArray) : Option ByteArray :=
  if h : P256EcdhPre xy sk then
    checkSize (p256EcdhRaw xy sk h) 32
  else none

def chachaSeal? (key nonce aad plain : ByteArray) : Option ByteArray :=
  if h : ChaChaSealPre key nonce aad plain then
    checkSize (chachaSealRaw key nonce aad plain h) (plain.size + 16)
  else none

/-- `some plaintext`, or `none` when the tag does not verify (HACL*'s check). -/
def chachaOpen? (key nonce aad sealed : ByteArray) : Option ByteArray :=
  if h : ChaChaOpenPre key nonce aad sealed then
    let out := chachaOpenRaw key nonce aad sealed h
    if out.size = sealed.size - 16 + 1 && out.get! 0 == 1 then some (out.extract 1 out.size) else none
  else none

/-- `x^e mod n` (RSAEP, RSAVP1); `none` unless the sizes fit and HACL* accepts (n odd,
x < n). -/
def rsaPublic? (n e x : ByteArray) : Option ByteArray :=
  if h : RsaOpPre n e x then checkSize (rsaPublicRaw n e x h) n.size else none

/-- `x^d mod n` (RSADP, RSASP1), constant time in d. -/
def rsaPrivate? (n d x : ByteArray) : Option ByteArray :=
  if h : RsaOpPre n d x then checkSize (rsaPrivateRaw n d x h) n.size else none

def rsaPssSign? (a : HashAlg) (n e d salt msg : ByteArray) : Option ByteArray :=
  if h : RsaPssSignPre a.code n e d salt msg then checkSize (rsaPssSignRaw a.code n e d salt msg h) n.size else none

def rsaPssVerify (a : HashAlg) (n e : ByteArray) (saltLen : Nat) (sig msg : ByteArray) : Bool :=
  if h : RsaPssVerifyPre a.code n e saltLen.toUSize sig msg then rsaPssVerifyRaw a.code n e saltLen.toUSize sig msg h == 1
  else false

theorem rsaPublic?_size {n e x out : ByteArray} (h : rsaPublic? n e x = some out) : out.size = n.size := by
  unfold rsaPublic? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem rsaPrivate?_size {n d x out : ByteArray} (h : rsaPrivate? n d x = some out) : out.size = n.size := by
  unfold rsaPrivate? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem rsaPssSign?_size {a : HashAlg} {n e d s m out : ByteArray} (h : rsaPssSign? a n e d s m = some out) :
    out.size = n.size := by
  unfold rsaPssSign? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem rsaPssVerify_false_of_bad_sig {a : HashAlg} {n e : ByteArray} {sl : Nat} {sig m : ByteArray}
    (h : sig.size ≠ n.size) : rsaPssVerify a n e sl sig m = false := by
  unfold rsaPssVerify; rw [dif_neg (fun hp => h hp.2.2.2.2.2.2.2.1)]

/-! ## The ECDSA message representative (FIPS 186-4 §6.4) -/

/-- The leftmost 256 bits of the hash, or a shorter hash (SHA-1) as a 256-bit integer:
left-padded with zero octets. HACL* reads exactly 32 bytes. -/
def p256MsgRep (digest : ByteArray) : ByteArray :=
  if digest.size ≥ 32 then digest.extract 0 32
  else ByteArray.mk (Array.replicate (32 - digest.size) 0) ++ digest

theorem p256MsgRep_size (d : ByteArray) : (p256MsgRep d).size = 32 := by
  unfold p256MsgRep
  split
  · simp [ByteArray.size_extract]; omega
  · rw [ByteArray.size_append]
    show (Array.replicate (32 - d.size) (0 : UInt8)).size + d.size = 32
    rw [Array.size_replicate]; omega

/-! ## Erasure -/

/-- Drop a secret. At run time, when this is the array's only reference, its bytes are
zeroed in place (Lib_Memzero0) before it is freed; the answer is its size either way.
Lean's reference counting decides "only reference": a secret still shared (for example a
key exported a moment ago, whose bytes are also in that answer) is released, not zeroed.
Lean knows nothing of the value (no theorem uses it); the caller adds it to a count so
the compiler keeps the call. -/
@[extern "l4_web_hacl_wipe"] opaque wipe (b : ByteArray) : Nat

/-- Bytes zeroed in place so far (tests). -/
@[extern "l4_web_hacl_wiped"] opaque wipedSoFar : BaseIO Nat

/-! ## Theorems: sizes and refusals -/

theorem hash?_size {a : HashAlg} {m out : ByteArray} (h : hash? a m = some out) : out.size = a.size := by
  unfold hash? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem hash?_none_of_not {a : HashAlg} {m : ByteArray} (h : ¬ HashPre m) : hash? a m = none := by
  simp [hash?, h]

theorem hmac?_size {a : HashAlg} {k m out : ByteArray} (h : hmac? a k m = some out) : out.size = a.size := by
  unfold hmac? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem hmac?_none_of_not {a : HashAlg} {k m : ByteArray} (h : ¬ HmacPre a.code k m) : hmac? a k m = none := by
  simp only [hmac?, dif_neg h]

theorem ed25519Sign?_size {sk m out : ByteArray} (h : ed25519Sign? sk m = some out) : out.size = 64 := by
  unfold ed25519Sign? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem ed25519Sign?_pre {sk m out : ByteArray} (h : ed25519Sign? sk m = some out) : sk.size = 32 := by
  unfold ed25519Sign? at h; split at h
  · rename_i hp; exact hp.1
  · simp at h

theorem ed25519Public?_size {sk out : ByteArray} (h : ed25519Public? sk = some out) : out.size = 32 := by
  unfold ed25519Public? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem ed25519Verify_false_of_bad_sig {pk m sig : ByteArray} (h : sig.size ≠ 64) : ed25519Verify pk m sig = false := by
  unfold ed25519Verify; rw [dif_neg (fun hp => h hp.2.1)]

theorem x25519?_size {sk pk out : ByteArray} (h : x25519? sk pk = some out) : out.size = 32 := by
  unfold x25519? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem x25519?_pre {sk pk out : ByteArray} (h : x25519? sk pk = some out) : sk.size = 32 ∧ pk.size = 32 := by
  unfold x25519? at h; split at h
  · rename_i hp; exact hp
  · simp at h

theorem x25519Public?_size {sk out : ByteArray} (h : x25519Public? sk = some out) : out.size = 32 := by
  unfold x25519Public? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem p256Public?_size {sk out : ByteArray} (h : p256Public? sk = some out) : out.size = 64 := by
  unfold p256Public? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem p256Decompress?_size {c out : ByteArray} (h : p256Decompress? c = some out) : out.size = 64 := by
  unfold p256Decompress? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem p256Sign?_size {sk e n out : ByteArray} (h : p256Sign? sk e n = some out) : out.size = 64 := by
  unfold p256Sign? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem p256Sign?_pre {sk e n out : ByteArray} (h : p256Sign? sk e n = some out) :
    sk.size = 32 ∧ e.size = 32 ∧ n.size = 32 := by
  unfold p256Sign? at h; split at h
  · rename_i hp; exact hp
  · simp at h

theorem p256Verify_false_of_bad_sig {xy e rs : ByteArray} (h : rs.size ≠ 64) : p256Verify xy e rs = false := by
  unfold p256Verify; rw [dif_neg (fun hp => h hp.2.2)]

theorem p256Ecdh?_size {xy sk out : ByteArray} (h : p256Ecdh? xy sk = some out) : out.size = 32 := by
  unfold p256Ecdh? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem p256Ecdh?_pre {xy sk out : ByteArray} (h : p256Ecdh? xy sk = some out) : xy.size = 64 ∧ sk.size = 32 := by
  unfold p256Ecdh? at h; split at h
  · rename_i hp; exact hp
  · simp at h

theorem chachaSeal?_size {k n a p out : ByteArray} (h : chachaSeal? k n a p = some out) : out.size = p.size + 16 := by
  unfold chachaSeal? at h; split at h
  · exact checkSize_size h
  · simp at h

theorem chachaSeal?_pre {k n a p out : ByteArray} (h : chachaSeal? k n a p = some out) : k.size = 32 ∧ n.size = 12 := by
  unfold chachaSeal? at h; split at h
  · rename_i hp; exact ⟨hp.1, hp.2.1⟩
  · simp at h

theorem chachaOpen?_pre {k n a c out : ByteArray} (h : chachaOpen? k n a c = some out) :
    k.size = 32 ∧ n.size = 12 ∧ 16 ≤ c.size := by
  unfold chachaOpen? at h; split at h
  · rename_i hp; exact ⟨hp.1, hp.2.1, hp.2.2.2.1⟩
  · simp at h

/-! ## Agreement with the specification, given HACL*'s correctness

These hypotheses are what HACL*'s F* proofs establish about the C (functional
correctness of SHA-1, SHA-2 and HMAC against their F* specifications, which are FIPS
180-4 and RFC 2104), stated against the pure-Lean specification of this tree. They are
hypotheses, not axioms: nothing in the tree assumes them; the run-time vector checks
(record, "Vectors") test them on the standard vectors. -/

def HashAgrees : Prop := ∀ (a : HashAlg) (m : ByteArray) (h : HashPre m), hashRaw a.code m h = a.pure.run m
def HmacAgrees : Prop := ∀ (a : HashAlg) (k m : ByteArray) (h : HmacPre a.code k m), hmacRaw a.code k m h = a.pure.mac k m
def CtEqAgrees : Prop := ∀ a b : ByteArray, a.size = b.size → (ctEqRaw a b == 1) = decide (a = b)

theorem hashFast_eq_pure (hc : HashAgrees) (a : HashAlg) (m : ByteArray) : hashFast a m = a.pure.run m := by
  unfold hashFast hash?
  split
  · rename_i h; rw [hc a m h, checkSize_getD]
  · rfl

theorem hmacFast_eq_pure (hc : HmacAgrees) (a : HashAlg) (k m : ByteArray) : hmacFast a k m = a.pure.mac k m := by
  unfold hmacFast hmac?
  split
  · rename_i h; rw [hc a k m h, checkSize_getD]
  · rfl

/-- The HACL* records ARE the specification records. So `WebCrypto.hkdf`,
`WebCrypto.pbkdf2`, `WebCrypto.hmacVerify` and HMAC_DRBG over `haclHash a` are, as
functions, those over the pure-Lean `a.pure`. -/
theorem haclHash_eq_pure (hh : HashAgrees) (hm : HmacAgrees) (a : HashAlg) : haclHash a = a.pure := by
  have e1 : hashFast a = a.pure.run := funext (hashFast_eq_pure hh a)
  have e2 : hmacFast a = a.pure.mac := funext fun k => funext (hmacFast_eq_pure hm a k)
  unfold haclHash; rw [e1, e2]

theorem hkdf_hacl_eq (hh : HashAgrees) (hm : HmacAgrees) (a : HashAlg) (ikm salt info : ByteArray) (len : Nat) :
    WebCrypto.hkdf (haclHash a) ikm salt info len = WebCrypto.hkdf a.pure ikm salt info len := by
  rw [haclHash_eq_pure hh hm]

theorem pbkdf2_hacl_eq (hh : HashAgrees) (hm : HmacAgrees) (a : HashAlg) (pw salt : ByteArray) (it len : Nat) :
    WebCrypto.pbkdf2 (haclHash a) pw salt it len = WebCrypto.pbkdf2 a.pure pw salt it len := by
  rw [haclHash_eq_pure hh hm]

theorem ctEq_eq (hc : CtEqAgrees) (a b : ByteArray) : ctEq a b = decide (a = b) := by
  unfold ctEq
  by_cases h : a.size = b.size
  · simp [h, hc a b h]
  · have : a ≠ b := fun e => h (congrArg ByteArray.size e)
    simp [h, this]

/-! ## Checks (the interpreter cannot call an extern: these check the pure parts) -/

#guard (p256MsgRep (ByteArray.mk (Array.replicate 20 7))).size == 32
#guard (p256MsgRep (ByteArray.mk (Array.replicate 48 7))).toList == List.replicate 32 7
#guard (p256MsgRep (ByteArray.mk #[1, 2])).toList == List.replicate 30 0 ++ [1, 2]
#guard HashAlg.ofName? "sha-384" == some .sha384
#guard HashAlg.ofName? "MD5" == none

end L4Factoidal.Crypto.WebHacl
