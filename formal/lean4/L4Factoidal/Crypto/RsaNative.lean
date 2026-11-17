/-
L4Factoidal.Crypto.RsaNative — the RSA PUBLIC operation (RFC 8017 §5.2.2,
RSAVP1) bound to HACL*'s generic 64-bit bignum field through Lean's C
FFI. THE FOURTH MEMBER OF THE LEAN TREE'S `@[extern]` CRYPTO FAMILY
(`Crypto/Ed25519.lean`, `Crypto/SHA2Native.lean`, `Crypto/P256Native.lean`
are the others).

It exists for JWS `RS256` (RFC 7518 §3.3), which Solid-OIDC identity
providers still issue.

## What this module is, and what it deliberately is not

It is modular exponentiation `s^e mod n` over public data, and nothing
else. It is NOT an RSA signature verifier. The padding — EMSA-PKCS1-v1_5,
RFC 8017 §9.2 — is generated and compared in pure Lean
(`JOSE/Pkcs1.lean`), where it carries theorems, and this module makes no
decision about whether a signature is valid.

That split is the point. The Bleichenbacher 2006 forgery class (and its
2019/2021 repetitions) comes from a verifier that PARSES the padding and
skips trailing bytes. Nothing in this project parses PKCS#1 padding:
`Pkcs1.emsaEncode` builds the whole `k`-byte template and
`Pkcs1.rs256Verify` compares the full `k` bytes for equality. There is
no code path that could be lenient, and `Pkcs1.rs256Verify_iff_template`
states that as a theorem.

There is no private operation, no key generation and no signing entry
point in this module, so no secret reaches this path. The RSA PRIVATE
operation for RSA-OAEP decryption (2026-10-27,
https://github.com/danbri/factoidal/issues/1082) is a separate extern,
`RsaOaep.rsaPrivateOp` in `Crypto/RsaOaep.lean`, in the same C file
`ffi/hacl_rsa.c` over `Hacl_Bignum64_mod_exp_consttime`.

## Crypto policy

`skills/crypto-policy/SKILL.md`, Lean 4 tree amendment, item 2. The
arithmetic is HACL*'s; we never write our own. Variable-time modular
exponentiation (`Hacl_Bignum64_mod_exp_vartime`) is used deliberately:
the exponent is the RSA PUBLIC exponent and the base is the published
signature, so a timing observer learns only values already carried in the
token. The private exponent of `Crypto/RsaOaep.lean` uses the
constant-time variant.

## Trust statement

`rsaPublicOp` is `opaque`: Lean knows its TYPE and nothing about its
VALUE. NO THEOREM IN THIS TREE DEPENDS ON WHAT IT COMPUTES.
`Pkcs1.rs256Verify` takes the public operation as a PARAMETER, so every
theorem about RS256 verification is stated over an arbitrary function of
that type and holds whatever HACL* returns; the opaque is passed in only
at the executable edge. `#print axioms` reports only the three standard
axioms on all of them.

What is trusted, and by whom:

  * HACL*'s verified bignum arithmetic (`third_party/hacl/src/
    Hacl_Bignum64.c` and `Hacl_Bignum.c`, entry points
    `Hacl_Bignum64_new_bn_from_bytes_be`, `Hacl_Bignum64_mod_exp_vartime`,
    `Hacl_Bignum64_bn_to_bytes_be`), extracted by KaRaMeL from F*/Low*
    code proved memory-safe and functionally correct by Project Everest.
    Vendored unmodified from hacl-star/hacl-star commit
    f557259007db9933442dde10aa995c1b00bd3446 (2026-10-29), Apache-2.0 —
    `third_party/hacl/PROVENANCE.md`.
  * `formal/lean4/ffi/hacl_rsa.c`: length checks, a big-endian bit-length
    count over the PUBLIC exponent, one right-alignment `memcpy`, and the
    three HACL* calls. No modular arithmetic of its own.

What we do NOT check:

  * That `n` is a real RSA modulus (a product of two primes). A caller
    who trusts a hostile JWK gets a hostile answer; key trust is the
    Solid-OIDC issuer-pinning layer's job (`JOSE/Jwt.lean`), not this
    one.
  * That `e` is one of the common exponents. RFC 8017 does not require
    it. A pathological `e` costs time, not soundness.
  * Anything about the padding. See above.

## Contract

`rsaPublicOp n e s`, with `k = n.size`:

  * `some res` with `res.size = k` when `k` is 256, 384 or 512 bytes
    (2048, 3072 or 4096 bits), `s.size = k`, `e` is non-empty, at most
    `k` bytes and has a set bit, and HACL*'s own preconditions hold
    (`n` odd, `n > 1`, `s < n`).
  * `none` otherwise. `s ≥ n` is RFC 8017's "signature representative
    out of range" and lands here, which is the specified rejection.

Modulus sizes below 2048 bits are REFUSED rather than supported. RFC 7518
§3.3 requires a key of at least 2048 bits for RS256, and a verifier that
accepts a 1024-bit modulus is a downgrade target.

## The 1024-bit exception (https://github.com/danbri/factoidal/issues/1227)

`rsaPublicOp1024` is the same HACL* operation for a 1024-bit modulus, and
for no other size. It takes a `Risk.Accepted .rsa1024Verify`, so only a
caller that accepted that risk by name reaches it (skills/lean-risk-flags).
It exists for XML Signature 1.1 verification of legacy signatures (§6.4.2
permits 1024-bit keys; the W3C interop vectors of 2012 and 2001 use them).
`rsaPublicOp` above still refuses 1024 bits, so JWS `RS256` and every other
caller keep the 2048-bit floor.
-/

import L4Factoidal.Risk

namespace L4Factoidal.Crypto.Rsa

/-- The RSA public operation `s^e mod n` (RFC 8017 §5.2.2 RSAVP1) via
HACL* `Hacl_Bignum64_mod_exp_vartime`, over big-endian byte strings.

`n`, `e` and `s` are big-endian unsigned integers; the result, when
present, is `n.size` bytes big-endian. `none` is every refusal: a modulus
that is not 2048, 3072 or 4096 bits, a signature of the wrong length or
not less than the modulus, an empty or zero exponent, an even modulus, or
an allocation failure. This is NOT a signature check — see
`JOSE/Pkcs1.lean`. -/
@[extern "l4_hacl_rsa_public_op"]
opaque rsaPublicOpRaw (n : @& ByteArray) (e : @& ByteArray)
    (s : @& ByteArray) : ByteArray

/-- `rsaPublicOpRaw` with its empty-means-refusal convention read into
`Option`. A successful result is always exactly `n.size` bytes, and
`n.size` is never zero for an accepted modulus, so the empty `ByteArray`
is unambiguously a refusal. -/
def rsaPublicOp (n e s : ByteArray) : Option ByteArray :=
  let r := rsaPublicOpRaw n e s
  if r.size == 0 then none else some r

/-- `l4_hacl_rsa_public_op_1024`: `rsaPublicOpRaw` for a modulus of exactly
128 bytes (1024 bits); the empty `ByteArray` for every other size and every
refusal of `rsaPublicOpRaw`. Reached only through `rsaPublicOp1024`. -/
@[extern "l4_hacl_rsa_public_op_1024"]
opaque rsaPublicOp1024Raw (n : @& ByteArray) (e : @& ByteArray)
    (s : @& ByteArray) : ByteArray

/-- The RSA public operation for a 1024-bit modulus, for a caller that
accepted `Risk.rsa1024Verify`. `none` for every other modulus size. -/
def rsaPublicOp1024 (_ : Risk.Accepted .rsa1024Verify) (n e s : ByteArray) : Option ByteArray :=
  if n.size != 128 then none else
  let r := rsaPublicOp1024Raw n e s
  if r.size == 0 then none else some r

/-- `rsaPublicOp1024` refuses every modulus that is not 1024 bits, whatever
HACL* computes. -/
theorem rsaPublicOp1024_only_1024 (tok : Risk.Accepted .rsa1024Verify) (n e s : ByteArray)
    (h : n.size ≠ 128) : rsaPublicOp1024 tok n e s = none := by
  simp [rsaPublicOp1024, h]

end L4Factoidal.Crypto.Rsa
