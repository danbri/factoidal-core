/-
L4Factoidal.Crypto.P256Native — NIST P-256 ECDSA verification bound to
HACL* through Lean's C FFI. THE THIRD MEMBER OF THE LEAN TREE'S
`@[extern]` CRYPTO FAMILY (the first is `Crypto/Ed25519.lean`, the second
`Crypto/SHA2Native.lean`).

It exists for JWS `ES256` (RFC 7518 §3.4), which Solid-OIDC access
tokens and RFC 9449 DPoP proofs use.

## Crypto policy

`skills/crypto-policy/SKILL.md`, Lean 4 tree amendment, item 2:
signature primitives come from HACL* via FFI ONLY, never a hand-written
Lean implementation. This module adds a member to that family and
follows the same three obligations it names: a module-header trust
statement (below), a shim with no arithmetic (`ffi/hacl_p256.c`), and a
run-time vector check in a probe (`lake exe l4jose-probe`, which runs
Wycheproof `ecdsa_secp256r1_sha256_p1363_test.json` and the RFC 7515
Appendix A.3 example).

## Trust statement

`p256VerifySha256` is `opaque`: Lean knows its TYPE and nothing about its
VALUE. NO THEOREM IN THIS TREE DEPENDS ON WHAT IT COMPUTES. The JOSE
theorems (`JOSE/Theorems.lean`) are about which verifier is REACHED for a
given header and key — algorithm confusion, key-type confusion, the
allowlist — and they hold whatever the verifier returns; the verifier is
a parameter or an opaque leaf in every one of them. `#print axioms` on
each still reports only `propext`, `Classical.choice`, `Quot.sound`.

What is trusted, and by whom:

  * ECDSA over NIST P-256 with SHA-256, as implemented by HACL*
    (`third_party/hacl/src/Hacl_P256.c`, entry point
    `Hacl_P256_ecdsa_verif_p256_sha2`, with `Hacl_Hash_SHA2.c` for the
    digest), extracted by KaRaMeL from F*/Low* code proved memory-safe
    and functionally correct against the specification by Project
    Everest. Vendored unmodified from hacl-star/hacl-star commit
    f557259007db9933442dde10aa995c1b00bd3446 (2026-10-29), Apache-2.0 —
    `third_party/hacl/PROVENANCE.md`.
  * `formal/lean4/ffi/hacl_p256.c`: two length checks and one pointer
    offset, containing no arithmetic.
  * The Lean C FFI convention: a `@&` (borrowed) `ByteArray` is a
    `b_lean_obj_arg`, a `Bool` is a `uint8_t`.

What we do NOT check, and where it is checked instead:

  * That the message bytes are the JWS signing input
    `ASCII(BASE64URL(protected) || '.' || BASE64URL(payload))`. That
    assembly is `JOSE/Jws.lean`, in Lean, with theorems.
  * That the caller MEANT ES256. The algorithm allowlist and the
    key-type match are `JOSE/Jws.lean`; this module is reached only
    through `Alg.es256` with a `Jwk.ec` key.
  * Signature malleability (`s` and `n - s` both verifying). ECDSA is
    malleable by design and JWS does not require a low-`s` form, so this
    is not a check we may add. A caller that needs signature uniqueness
    must not use ECDSA.

## Calling-convention match, stated because guessing here is a bug

RFC 7518 §3.4 fixes the ES256 signature as `R || S`, two 32-byte
big-endian integers, 64 bytes total — NOT the ASN.1 DER `SEQUENCE` that
X.509 and TLS use. HACL* takes `signature_r` and `signature_s` as two
32-byte big-endian buffers, so the conversion is a pointer offset and
there is no DER parser anywhere in this path. The public key is `x || y`,
64 raw bytes, which is the concatenation of the base64url-decoded JWK
`x` and `y` members (`JOSE/Jwk.lean` builds it, and a `#guard` there
pins the RFC 7515 Appendix A.3 key). HACL* hashes the message itself
with SHA-256; the caller passes the signing input, never a digest.

## Contract

  * `p256VerifySha256 pubXY msg sig`: `true` only when `pubXY` is 64
    bytes and a valid curve point, `sig` is 64 bytes, and HACL* accepts
    `(r, s)` over SHA-256 of `msg`. Every length refusal is `false`.
    There is no "unknown" answer and no success-by-default path.
  * `p256ValidatePublicKey pubXY`: `true` when `pubXY` is 64 bytes and
    the point is on the curve and is not the point at infinity.
  * `p256SignSha256 sk msg nonce` (added for the authorization server,
    https://github.com/danbri/factoidal/issues/916): HACL*
    `Hacl_P256_ecdsa_sign_p256_sha2`. 64 bytes `r || s`, or EMPTY when `sk`
    or `nonce` is not 32 bytes or HACL* refuses it (outside `[1, n-1]`).
    The nonce comes from the host's random source; this tree derives no
    nonce (no RFC 6979 code here: that would be signature logic).
  * `p256SecretToPublic sk`: HACL* `Hacl_P256_dh_initiator`, the raw
    64-byte `x || y`, or EMPTY for an invalid private key.
  * `p256CompressedToRaw pk`: HACL* `Hacl_P256_compressed_to_raw`, the raw
    64-byte `x || y` of a 33-byte SEC 1 compressed point, or EMPTY when the
    prefix is not 0x02/0x03 or the point is not on the curve.

  * `p256EcdhRaw theirXY sk` (added for JWE `ECDH-ES` and XML Encryption
    1.1 ECDH-ES, https://github.com/danbri/factoidal/issues/1083): HACL*
    `Hacl_P256_dh_responder`, the 64-byte point `x || y` of `sk * Q`, or
    EMPTY when `theirXY` is not 64 bytes, `sk` is not 32 bytes, `sk` is
    outside `[1, n-1]`, or `Q` is not on the curve or is the point at
    infinity. HACL*'s header (`third_party/hacl/include/Hacl_P256.h`,
    `Hacl_P256_dh_responder`): "The function also checks whether
    `private_key` and `their_pubkey` are valid." So an invalid-curve point
    is refused in HACL*, before any scalar multiplication.
  * `p256Ecdh theirXY sk`: the 32-byte shared secret `Z`, the x coordinate
    of `sk * Q` (SP 800-56A §5.7.1.2, the ECC CDH primitive: `Z = x_P`;
    SEC 1 §3.3.1; RFC 7518 §4.6.2: "Z  This is set to the representation of
    the shared secret Z as an octet sequence."), or `none`.
    The selection of x is this Lean definition, not the C shim.

The run-time checks of the three: `lake exe l4crypto-probe`, sections
`p256-sign-rfc6979` (RFC 6979 A.2.5), `p256-secret-to-public` (RFC 6979
A.2.5 and the Wycheproof `ecdh_secp256r1_webcrypto_test.json` keys) and
`p256-compressed` (Wycheproof `ecdh_secp256r1_ecpoint_test.json`). The run-time check of
`p256Ecdh` is section `p256-ecdh`: Wycheproof
`ecdh_secp256r1_ecpoint_test.json` and `ecdh_secp256r1_webcrypto_test.json`,
and the NIST CAVP ECC CDH P-256 vectors
(`third_party/nist-cavs-ecccdh/`). A differential run against node:crypto is
`tests/crypto/ecdh-diff.mjs`.
-/

namespace L4Factoidal.Crypto.P256

/-- ECDSA-P256-SHA256 verification (RFC 6979 / FIPS 186-4, as used by JWS
`ES256`, RFC 7518 §3.4) via HACL* `Hacl_P256_ecdsa_verif_p256_sha2`.

`pubXY` is the raw 64-byte `x || y` public key; `sig` is the raw 64-byte
`r || s` JWS signature; `msg` is the JWS signing input, unhashed. `false`
on any length refusal, on an invalid public key, and on a rejected
signature. -/
@[extern "l4_hacl_p256_verify_sha256"]
opaque p256VerifySha256 (pubXY : @& ByteArray) (msg : @& ByteArray)
    (sig : @& ByteArray) : Bool

/-- Point validity of a raw 64-byte `x || y` P-256 public key, via HACL*
`Hacl_P256_validate_public_key`. `false` on a wrong length, a point off
the curve, or the point at infinity. -/
@[extern "l4_hacl_p256_validate_public_key"]
opaque p256ValidatePublicKey (pubXY : @& ByteArray) : Bool

/-- ECDSA-P256-SHA256 signing via HACL* `Hacl_P256_ecdsa_sign_p256_sha2`:
the 64-byte JWS `r || s`, or the EMPTY array on any refusal. -/
@[extern "l4_hacl_p256_sign_sha256"]
opaque p256SignSha256Raw (sk : @& ByteArray) (msg : @& ByteArray)
    (nonce : @& ByteArray) : ByteArray

/-- The raw `x || y` public key of a private key via HACL*
`Hacl_P256_dh_initiator`, or the EMPTY array. -/
@[extern "l4_hacl_p256_secret_to_public"]
opaque p256SecretToPublicRaw (sk : @& ByteArray) : ByteArray

/-- SEC 1 point decompression via HACL* `Hacl_P256_compressed_to_raw`, or
the EMPTY array. -/
@[extern "l4_hacl_p256_compressed_to_raw"]
opaque p256CompressedToRawRaw (pk : @& ByteArray) : ByteArray

/-- `p256SignSha256Raw` with its refusal as `none`. -/
def p256SignSha256 (sk msg nonce : ByteArray) : Option ByteArray :=
  let s := p256SignSha256Raw sk msg nonce
  if s.size == 64 then some s else none

/-- `p256SecretToPublicRaw` with its refusal as `none`. -/
def p256SecretToPublic (sk : ByteArray) : Option ByteArray :=
  let p := p256SecretToPublicRaw sk
  if p.size == 64 then some p else none

/-- `p256CompressedToRawRaw` with its refusal as `none`. -/
def p256CompressedToRaw (pk : ByteArray) : Option ByteArray :=
  let p := p256CompressedToRawRaw pk
  if p.size == 64 then some p else none

/-- ECDH over P-256 via HACL* `Hacl_P256_dh_responder`: the 64-byte point
`x || y` of `sk * theirXY`, or the EMPTY array on any refusal (a wrong
length, a private key outside `[1, n-1]`, a public key off the curve). -/
@[extern "l4_hacl_p256_ecdh"]
opaque p256EcdhRaw (theirXY : @& ByteArray) (sk : @& ByteArray) : ByteArray

/-- The P-256 ECDH shared secret `Z` (SP 800-56A §5.7.1.2): the 32-byte x
coordinate of `sk * theirXY`, or `none` when HACL* refuses the key pair.
`theirXY` is the raw 64-byte `x || y` (the JWK `x` and `y` members, or an
uncompressed SEC 1 point without its 0x04 prefix); `sk` is the 32-byte
big-endian private scalar. -/
def p256Ecdh (theirXY sk : ByteArray) : Option ByteArray :=
  let p := p256EcdhRaw theirXY sk
  if p.size == 64 then some (p.extract 0 32) else none

/-! ## ECDSA over a message representative computed in Lean

FIPS 186-4 §6.4 (signature generation, step 4; verification, step 3): the
integer `e` is the leftmost `min(N, outlen)` bits of the hash, with `N = 256`
for P-256. `p256MsgRep` gives `e` as 32 big-endian octets: the first 32
octets of a hash of 32 octets or more (SHA-256, SHA-384, SHA-512), or a
shorter hash (SHA-1, SHA-224) left-padded with zero octets, which keeps its
integer value. HACL* `Hacl_P256_ecdsa_verif_without_hash` and
`Hacl_P256_ecdsa_sign_p256_without_hash` take this `e`; HACL*'s own
`..._sha384` and `..._sha512` entries take the first 32 octets of the hash in
the same way (`third_party/hacl/src/Hacl_P256.c`). Added for XML Signature
1.1 §6.4.3 (https://github.com/danbri/factoidal/issues/1223). -/

/-- The 32-octet message representative of a hash for P-256 (FIPS 186-4 §6.4). -/
def p256MsgRep (h : ByteArray) : ByteArray :=
  if 32 ≤ h.size then h.extract 0 32
  else ⟨(List.replicate (32 - h.size) (0 : UInt8)).toArray⟩ ++ h

theorem p256MsgRep_size (h : ByteArray) : (p256MsgRep h).size = 32 := by
  unfold p256MsgRep
  split
  · simp [ByteArray.size_extract]; omega
  · rename_i hlt
    simp only [ByteArray.size_append]
    show (List.replicate (32 - h.size) (0 : UInt8)).toArray.size + h.size = 32
    simp only [List.size_toArray, List.length_replicate]
    omega

/-- A 32-octet hash (SHA-256) is its own representative, so the
`..._without_hash` path checks the same integer as `Hacl_P256_ecdsa_verif_p256_sha2`. -/
theorem p256MsgRep_of_size32 (h : ByteArray) (hs : h.size = 32) : p256MsgRep h = h := by
  unfold p256MsgRep
  simp only [hs, Nat.le_refl, if_true]
  rw [← hs]
  exact ByteArray.extract_zero_size

#guard p256MsgRep ⟨#[1, 2]⟩ == ⟨(List.replicate 30 (0 : UInt8) ++ [1, 2]).toArray⟩
#guard (p256MsgRep ⟨(List.range 48).toArray.map UInt8.ofNat⟩).data.toList ==
  (List.range 32).map UInt8.ofNat

/-- ECDSA P-256 verification of `sig = r || s` with the representative `e`
(32 octets) via HACL* `Hacl_P256_ecdsa_verif_without_hash`. `false` on a
length refusal, an invalid public key, or a rejected signature. -/
@[extern "l4_hacl_p256_verify_prehashed"]
opaque p256VerifyPrehashed (pubXY : @& ByteArray) (e : @& ByteArray)
    (sig : @& ByteArray) : Bool

/-- ECDSA P-256 signing with the representative `e` via HACL*
`Hacl_P256_ecdsa_sign_p256_without_hash`: `r || s`, or EMPTY on a refusal. -/
@[extern "l4_hacl_p256_sign_prehashed"]
opaque p256SignPrehashedRaw (sk : @& ByteArray) (e : @& ByteArray)
    (nonce : @& ByteArray) : ByteArray

/-- ECDSA P-256 verification over the hash `h` of the message (any length). -/
def p256VerifyHash (pubXY h sig : ByteArray) : Bool :=
  p256VerifyPrehashed pubXY (p256MsgRep h) sig

/-- ECDSA P-256 signing over the hash `h`, with its refusal as `none`. -/
def p256SignHash (sk h nonce : ByteArray) : Option ByteArray :=
  let s := p256SignPrehashedRaw sk (p256MsgRep h) nonce
  if s.size == 64 then some s else none

end L4Factoidal.Crypto.P256
