# XML Signature 1.1 core validation in Lean

Date: 2026-11-01. Tracking: https://github.com/danbri/factoidal/issues/1165
(track B, item 4). Code: `formal/lean4/L4Factoidal/XML/DSig11.lean`,
`XML/DSig11Native.lean`, runner `Harness/XmlDsigRun.lean`
(`lake exe l4xmldsig`).

## What it does

`DSig11.validate` does core validation (XML Signature 1.1 §3.2) of one
`ds:Signature` element:

1. Parse `ds:SignedInfo`: the canonicalization method, the signature
   method (with `HMACOutputLength`), and one or more `ds:Reference`.
2. For each reference (§3.2.1): dereference the `URI` (§4.4.3.3), apply
   the transforms in order, convert a node-set to octets by Canonical XML
   1.0 without comments, and compare the digest with `ds:DigestValue`.
3. Canonicalize `ds:SignedInfo` by its method and check
   `ds:SignatureValue` over those octets (§3.2.2).

The result names the URI and the octets of each reference. These octets are
what was signed. A caller that reads a part of the document must check that
the part is one of them (the `wrapChild` SAML fixture is a valid signature
over an assertion that is not the document element).

## Reuse

- Node-sets and canonicalization: `XML/C14n.lean` (the six methods over
  XPath 1.0 node-sets) and `XML/C14nXPath.lean` (the XPath filtering
  transform, by the XPath 4.0 evaluator).
- Digests: `Crypto.sha1`, `Crypto.sha256`, `Crypto.sha384`,
  `Crypto.sha512`, and `Crypto.sha224` (new: the SHA-256 compression with
  the SHA-224 initial value, FIPS 180-4 §6.3).
- HMAC: `Crypto.hmacWith` (new, RFC 2104 over any hash). The theorems
  `hmacSha256_eq_hmacWith` and `hmacSha512_eq_hmacWith` say that the two
  fixed forms of `Crypto/Hmac.lean` are its instances.
- RSA: `JOSE.Pkcs1.rsaPkcs1Verify` (new, RFC 8017 §9.2 for the five
  DigestInfo values). `emsaEncodeGen_sha256` and `rsaPkcs1Verify_sha256`
  say that the JWS `RS256` functions are its SHA-256 case, so the theorems
  that exclude the Bleichenbacher 2006 forgery apply to it.
- RSA public operation and ECDSA P-256 SHA-256: HACL\* through
  `Crypto.Rsa.rsaPublicOp` and `Crypto.P256.p256VerifySha256`. They are
  the fields of `DSig11.Backend`, so every theorem holds for any backend.
- The SAML 2.0 profile verifier `XML/DSig.lean` is not changed.
  `dsig11_saml_profile_algorithms` and `dsig11_saml_profile_rsa` state
  that its algorithm choices are entries of the 1.1 tables and that its RSA
  check is the 1.1 RSA check at SHA-256. The runner compares the two
  verifiers on the 8 SAML fixtures.

## Decisions

- An ID is an attribute that the DTD declares `ID`, `xml:id`, or an
  unqualified `Id`, `ID` or `id`. A value that two elements carry is
  refused, because the reference would not name one element.
- `#ID` gives the element without comments; `#xpointer(id('ID'))` and
  `#xpointer(/)` keep comments (§4.4.3.3). signxml 4 digests the comments
  of a `#ID` reference when the transform is a WithComments method; its
  three such fixtures are refused, as the specification requires.
- `HMACOutputLength` below max(80, half the hash output) is refused
  (§6.3.1).
- A key from `ds:KeyInfo` only tells which key verifies the signature.
  `Validated.key` returns it; trust is the caller's decision. With
  `Config.key` the caller gives the key and `ds:KeyInfo` is not read.
- An external URI is refused unless the caller gives a resolver.

## Theorems

- `checkRefsAcc_ok`, `dsig11_validateParsed_ok`: core validation succeeds
  only when every reference digest matched and the signature value checked
  over the canonical `ds:SignedInfo`.
- `dsig11_hmac_short_refused`: a truncation below the §6.3.1 minimum is
  refused whatever the value.
- `dsig11_rsa_template`: an accepted RSA signature is
  `rsaPkcs1Verify = true` under the key that is returned.

## Open (each with an issue and an expected failure, or a refusal)

- ECDSA other than P-256 with SHA-256:
  https://github.com/danbri/factoidal/issues/1223 (25 interop cases).
- DSA: https://github.com/danbri/factoidal/issues/1224.
- XSLT and XPath Filter 2.0 transforms:
  https://github.com/danbri/factoidal/issues/1225.
- `ds:X509Data`: https://github.com/danbri/factoidal/issues/1226 (1 case).
- RSA keys of 1024 bits: https://github.com/danbri/factoidal/issues/1227
  (10 cases; decision needed).
- Signature generation through the one signer component
  (`docs/web/hub/webdav-lws-design.md`, custodian principle), the 2001
  interop vectors, and a wasm op: open items of item 4 of
  https://github.com/danbri/factoidal/issues/1165.
