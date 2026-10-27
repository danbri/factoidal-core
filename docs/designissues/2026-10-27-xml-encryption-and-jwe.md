# XML Encryption 1.1 and JWE: primitives, the AES call-out, and the layers

Date: 2026-10-27. Epic: https://github.com/danbri/factoidal/issues/1081
(XML Encryption 1.1 and JWE over HACL\* primitives). Sub-issues:
https://github.com/danbri/factoidal/issues/1082 (RSA-OAEP),
https://github.com/danbri/factoidal/issues/1083 (ECDH-ES and Concat KDF),
https://github.com/danbri/factoidal/issues/677 (AES-GCM),
https://github.com/danbri/factoidal/issues/1086 (AES Key Wrap, AES-CBC with
HMAC), https://github.com/danbri/factoidal/issues/1084 (XML Encryption),
https://github.com/danbri/factoidal/issues/1085 (JWE),
https://github.com/danbri/factoidal/issues/1073 (SAML encrypted assertions).

Owner, 2026-10-27, verbatim: "We need XML Encryption in Factoidal generally,
so JSE too - add all those missing primitives but using HACL*." Then, on AES:
"Why not just WebCrypto everywhere (browser/node or wasm fallback?)" and "Ok
for now: “My proposal is HACL* Vale on x86-64 and a refusal on other CPU”".
Rule text: `skills/crypto-policy/SKILL.md` § "AES through WebCrypto".

## Where each primitive comes from

| primitive | native (Lean executables) | wasm (npm, hub, Node hosts) | status |
| --- | --- | --- | --- |
| RSA-OAEP (SHA-1, SHA-256) | HACL\* bignum, `ffi/hacl_rsa.c`; padding in Lean (`Crypto/RsaOaep.lean`) | the same C, compiled into the wasm | landed 2026-10-27 |
| ECDH P-256 | HACL\* `Hacl_P256_dh_responder`, `ffi/hacl_p256.c` | the same C in the wasm | landed 2026-10-27 |
| X25519 | HACL\* Curve25519 (`Crypto/X25519.lean`) | the same C in the wasm | before this work |
| Concat KDF | pure Lean over SHA-2 (`Crypto/ConcatKdf.lean`) | the same | landed 2026-10-27 |
| AES-GCM | HACL\* Vale, x86-64 with AES-NI and PCLMULQDQ; refused on other CPUs | host WebCrypto | in progress |
| AES Key Wrap, AES-CBC | refused natively (Vale has GCM only, no AES block or decryption entry) | host WebCrypto (`AES-KW`, `AES-CBC`) | after AES-GCM |
| HMAC-SHA-2 (for CBC-HMAC) | pure Lean and HACL\* | the same | before this work |

## The AES call-out on JavaScript hosts

WebCrypto is asynchronous and the engine is synchronous wasm, so AES on the
wasm surface uses the request-and-resume step that the authorization server
uses for fetches (`Authz/Fetch.lean`, `Need`):

1. The host calls an operation, for example `xmlDecrypt(handle, document,
   keys)`.
2. Lean parses the document, checks the algorithm allowlist, unwraps the
   content key with RSA-OAEP or derives it with ECDH-ES and Concat KDF (all
   inside the wasm), and either finishes or answers one request:
   `{need: {op: "aes-gcm-decrypt", key, iv, aad, data}}`, also
   `aes-gcm-encrypt`, `aes-kw-unwrap`, `aes-kw-wrap`, `aes-cbc-decrypt`,
   `aes-cbc-encrypt`. The bytes are base64.
3. The host runs exactly that WebCrypto call and passes back
   `{ok: bytes}` or `{refused: true}`. It passes no reason: an AEAD tag
   failure, a padding failure and a wrong length all become the same
   refusal, so no error text from the host reaches the caller (padding
   oracle, Jager and Somorovsky 2011).
4. Lean continues from its saved state. A document needs at most a fixed
   number of requests (one key unwrap and one content decryption per
   `EncryptedData`, and a bound on the number of `EncryptedData` elements),
   and the host refuses to answer more than that bound.

The host makes no decision: it does not read the document, choose an
algorithm or build a key. `tools/host-purity-lint.sh` is extended to cover
the call-out module.

On native executables the same Lean code receives an `AeadOps` record
(`Crypto/Aead.lean`) whose AES-GCM is the Vale extern, and whose Key Wrap
and CBC refuse with a message that names
https://github.com/danbri/factoidal/issues/677. The decision code is
written once over the record, and the wasm instance of the record is "ask
the host".

## XML Encryption 1.1 profile

Accepted, by allowlist; everything else is refused, never skipped:

* `xenc:EncryptedData` with `Type` Element or Content, and
  `xenc:EncryptedKey`; `ds:KeyInfo` holding an `xenc:EncryptedKey`, an
  `xenc:AgreementMethod` (ECDH-ES with ConcatKDF), or a `ds:KeyName` the
  caller maps to a key; a `ds:RetrievalMethod` only to a same-document
  `EncryptedKey`; no remote retrieval;
* data encryption: `xmlenc11#aes128-gcm`, `xmlenc11#aes256-gcm`;
  `xmlenc#aes128-cbc` and `xmlenc#aes256-cbc` only when the caller opts in,
  because CBC without a MAC is malleable (Jager and Somorovsky, "How to Break
  XML Encryption", CCS 2011);
* key transport: `xmlenc#rsa-oaep-mgf1p` (SHA-1 digest and MGF1),
  `xmlenc11#rsa-oaep` with SHA-256; refused: `xmlenc#rsa-1_5`
  (Bleichenbacher);
* key wrap: `xmlenc#kw-aes128`, `xmlenc#kw-aes256`;
* key agreement: `xmlenc11#ECDH-ES` on P-256 and X25519, with
  `xmlenc11#ConcatKDF` over SHA-256 (OtherInfo not a whole number of octets:
  https://github.com/danbri/factoidal/issues/1097).

After decryption the plaintext is parsed with the same limits as
`SAML.decodeToken` (no DTD, bounded size and nesting).

SAML (https://github.com/danbri/factoidal/issues/1073): an
`EncryptedAssertion` is decrypted first, then the decrypted `saml:Assertion`
must carry its own valid signature (`SAML.validate`). An encrypted assertion
whose content is not signed is refused.

## JWE profile

Compact serialization. A fixed allowlist decided before any key is read, in
the style of `JOSE/Jws.lean` `preKey`:

* `alg`: `RSA-OAEP`, `RSA-OAEP-256`, `ECDH-ES`, `ECDH-ES+A128KW`,
  `ECDH-ES+A256KW`, `A128KW`, `A256KW`, `dir`; refused: `RSA1_5`,
  `PBES2-*`, every other value;
* `enc`: `A128GCM`, `A256GCM`, `A128CBC-HS256`, `A256CBC-HS512`;
* refused: `zip` (compression oracle), any `crit`;
* ECDH-ES: the `epk` point is checked by HACL\* (off-curve and invalid-curve
  points are refused; Wycheproof cases in `l4crypto-probe` section
  `p256-ecdh`);
* nested JWT (RFC 7519 §5.2): decrypt, then the inner JWS through
  `JOSE.verifyCompact`.

## Tests

* Primitives: `lake exe l4crypto-probe` sections `rsa-oaep`, `p256-ecdh`,
  `aes-gcm` (Wycheproof, NIST CAVP, RFC vectors).
* Differential runs: `tests/crypto/rsa-oaep-diff.mjs` and
  `tests/crypto/ecdh-diff.mjs` (Lean with HACL\* against node:crypto); an
  AES run that sends the same random keys, IVs and data to Node (OpenSSL),
  headless Chromium (BoringSSL), Firefox (NSS) where installed, and the
  native Vale probe, and fails on any difference in output or in
  accept/refuse.
* Formats: RFC 7520 §5 and RFC 7516 Appendix A for JWE; the W3C XML
  Encryption 1.1 interop cases and round trips with the JDK (Apache
  Santuario) for XML Encryption, as `tests/saml/MakeFixtures.java` does for
  signatures.

## Measured so far (2026-10-27, branch `claude/factoidal-saml-xml-security-ve00xs`)

* `l4crypto-probe`: RSA Laboratories `oaep-vect.txt` 187 pass, 0 fail (out
  of 187); Wycheproof RSA-OAEP 2048 SHA-1 70 pass, 0 fail (out of 70); 2048,
  3072 and 4096 SHA-256 each 73 pass, 0 fail (out of 73); `p256-ecdh` 771
  pass, 0 fail, 1 acceptable (out of 772). TOTAL 3329 pass, 0 fail, 256
  acceptable, 316 not run (out of 3901); the 316 are AES-GCM.
* `tests/crypto/rsa-oaep-diff.mjs`: 200 pass, 0 fail (out of 200).
  `tests/crypto/ecdh-diff.mjs 300`: 905 agree, 0 differ (out of 905).
