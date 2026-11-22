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
* key transport uses `xmlenc#rsa-oaep-mgf1p` or `xmlenc11#rsa-oaep`. The
  reader accepts the digest and MGF combinations described below. The writer
  produces the SHA-1 or SHA-256 equal-hash configurations. The profile
  refuses `xmlenc#rsa-1_5` (Bleichenbacher).
* key wrap: `xmlenc#kw-aes128`, `xmlenc#kw-aes256`;
* key agreement: `xmlenc11#ECDH-ES` on P-256 and X25519, with
  `xmlenc11#ConcatKDF` over SHA-256 (OtherInfo not a whole number of octets:
  https://github.com/danbri/factoidal/issues/1097).

After decryption the plaintext is parsed with the same limits as
`SAML.decodeToken` (no DTD, bounded size and nesting).

SAML (https://github.com/danbri/factoidal/issues/1073): an
`EncryptedAssertion` is decrypted first, then the decrypted `saml:Assertion`
must carry its own valid signature (`SAML.validate`). An encrypted assertion
whose content is not signed is refused. The authorization server takes the
decryption keys as `samlKeys` (`authz-serve --saml-decrypt-key FILE`); its
AES requests go to the host as `Need.cipher` in the same request and resume
loop as fetches (`Authz/SubjectToken.lean` `validateSaml`,
`Authz/Server.lean` `AuthzState.recordCipher`, `npm/factoidal/authz/server.mjs`).

## XML Encryption 1.1: as built (https://github.com/danbri/factoidal/issues/1084)

Code: `formal/lean4/L4Factoidal/XML/Enc.lean` (decrypt, encrypt, the
allowlist above), `XML/EncTests.lean` (`#guard`s over a stub cipher and stub
public-key primitives), `SAML/Assertion.lean` (`validateWith`,
`decryptSubjectIds`, theorem `validateWith_ok`), `Wasm/Ops/XmlEnc.lean`
(ops `xmlDecrypt`, `xmlEncrypt`), `Harness/XmlEncProbe.lean`
(`lake exe l4xmlenc-probe`, the native run), `tests/xmlenc/` (Santuario
fixtures both ways, the W3C cases, the wasm run).

Decisions made while building it (Claude-inferred defaults, not owner
rulings):

* Format code takes a `Cipher` (AES) and a `Prims` record (RSA, P-256,
  X25519). Natively both are HACL\*; in the wasm the cipher is
  `replayCipher answers` and the primitives are HACL\* in the wasm.
* One failure value after the structure check, `decryptionError`
  ("XML decryption failed"): a wrong or failed key unwrap, a failed GCM
  tag, a wrong content key length, a CBC padding error, a plaintext that is
  not UTF-8, not well-formed, deeper than the bound, or that holds another
  `EncryptedData`. Structure and allowlist refusals keep their own message,
  given before any key is used for that element.
* The plaintext is parsed in the parent's context by wrapping it in one
  element that declares the parent's in-scope bindings (§4.4 step 3.4).
  A decrypted element made a document element (SAML) gets those bindings
  as attributes (`Enc.withScope`), so exclusive canonicalization sees the
  same names.
* AES-CBC needs two requests: WebCrypto removes PKCS #7 padding only and
  XML Encryption §5.2 pads with arbitrary octets (Santuario uses
  `ISO10126Padding`). The first request encrypts the empty message under
  the last ciphertext block as IV, which gives one block of PKCS #7 padding
  chained to the ciphertext; the second decrypts the ciphertext with that
  block appended; Lean removes the §5.2 padding. Checked against Santuario's
  `aes128-cbc` in `tests/xmlenc/wasm.mjs`.
* RSA-OAEP with the same hash for the digest and MGF1 only (SHA-1 or
  SHA-256) until 2026-11-17. Since then (track B item 5, part 1, of
  https://github.com/danbri/factoidal/issues/1165): every digest of §5.5.2
  and §5.7 (SHA-1, SHA-224, SHA-256, SHA-384, SHA-512) with either
  algorithm, and for `xmlenc11#rsa-oaep` any `mgf1sha*` MGF, independent of
  the digest. `Enc.oaepHashOf` describes the pure specification. The XML
  runtime supplies HACL* through `Enc.Prims.oaepProvider` for both digests.
  It refuses a missing or wrong-sized digest before applying that mask.
  W3C WRAP.3 and WRAP.4 exercise mixed digests. WRAP.2 also needs AES-192.
  [Checked hash provider and fixture provenance](../20261119-xmlenc-oaep-hacl.md).
* X25519 key agreement: `xmlenc11#ECDH-ES` with an X25519 originator key,
  and `http://www.w3.org/2021/04/xmldsig-more#x25519` (RFC 9231), which
  Santuario 4 writes; the originator key is a `dsig11:DEREncodedKeyValue`
  (RFC 8410 SubjectPublicKeyInfo).
* An empty `ConcatKDFParams` attribute value is the empty bit string, as
  an absent one is (W3C AGRMNT.1 writes `AlgorithmID=""`). Lean writes
  `AlgorithmID` only: Santuario 4.0.4 refuses the one-octet value `00`
  ("ConcatKDF parameter is to short").
* `ds:X509Data` and `ds:KeyValue` in an `EncryptedKey`'s `KeyInfo` are not
  read: the key is the caller's key named by `ds:KeyName`, or the caller's
  only key of that kind. W3C WRAP.1 and AGRMNT.1 name their keys only by
  certificate.
* `EncryptedData` without `Type` is refused by `decrypt`, which replaces
  elements in a document. Since 2026-11-22 (track B item 5, part 3):
  `decryptOctets`, the `xmlDecrypt` member `octets: true`, gives the
  plaintext octets of a document element `EncryptedData` with any or no
  `Type` (§4.4 step 3). W3C SYM.1 passes this way.
* PBKDF2 key derivation (§5.4.2), since 2026-11-22 (track B item 5, part
  2, of https://github.com/danbri/factoidal/issues/1165): `kdfOf` reads
  `xmlenc11#ConcatKDF` (§5.4.1, unchanged: theorem
  `xmlenc11_kdfOf_concatKdf`) or `xmlenc11#pbkdf2` in an
  `xenc:AgreementMethod`. The password is the shared secret Z. Accepted:
  `PBKDF2-params` with its four children in schema order, a `Specified`
  salt (`OtherSource` defines no algorithm and is refused), an
  `IterationCount` of at most `Opts.maxPbkdf2Iterations` (1,000,000, so a
  document cannot ask for unbounded work), a `KeyLength` equal to the length
  of the key it makes (a structure refusal, before any key is used), and the
  PRF HMAC-SHA-1 or HMAC-SHA-256/384/512 (no HACL* HMAC-SHA-224 here).
  `Prims.pbkdf2` is `WebCrypto.pbkdf2` over `WebHacl.haclHash`; theorem
  `xmlenc11_pbkdf2_native_eq_rfc8018` makes it the pure RFC 8018 function
  given `HashAgrees` and `HmacAgrees`, and
  `xmlenc11_derive_pbkdf2_eq_webcrypto` states the derived key for a
  document. Tests: `tests/xmlenc/pbkdf2.json`, made by Node's crypto
  (`tests/xmlenc/make-pbkdf2.mjs`): 5 documents that decrypt (P-256 and
  X25519; key wrap and direct agreement; each PRF) and 6 refusals; the
  native probe compares the key encryption key Lean derives with Node's.
  The writer still uses Concat KDF only.
* The published PBKDF2 vectors do not decrypt as written. W3C AGRMNT.9
  (Oracle, ECDH-ES with PBKDF2): no derivation tried gives a key that
  unwraps its key; an expected failure,
  https://github.com/danbri/factoidal/issues/1303. IBM and Microsoft DRV.2
  and DRV.4 (PBKDF2 in `xenc11:DerivedKey`): the derived key decrypts them,
  but their AES-256-CBC ciphertexts have no padding block, which §5.2
  requires. Microsoft DRV.1 (Concat KDF) has the same defect.
* Finite-field Diffie-Hellman `xmlenc11#dh-es` (§5.6.3), since 2026-11-22
  (track B item 5, part 5), reader only. Originator key `xenc:DHKeyValue`
  (§5.6.1: `(P, Q, Generator)?, Public, (seed, pgenCounter)?`); recipient key
  `DhKey` (`p`, `g`, `q`, `x`; the Wasm op takes `{"kty": "DH", …}`, because
  RFC 7518 has no JWK type for it). Before `x` is used: the prime is 1024 to
  4096 bits in 64-bit steps, and fewer than 2048 bits only with
  `Opts.dh1024` (risk token `Risk.dh1024Agreement`, option
  `dangerouslyAndRegrettablyAcceptDh1024`; NIST SP 800-131A Rev. 2); the
  key must have `q`; the originator's `P`, `Q`, `Generator`, when present,
  must be the key's; `2 ≤ y ≤ p − 2` and `y^q mod p = 1` (RFC 2631 §2.1.5,
  NIST SP 800-56A Rev. 3 §5.6.2.3.1). Each is a refusal with a reason; none
  depends on `x`. `Z = y^x mod p` as `|p|` octets by HACL*
  `Hacl_Bignum64_mod_exp_consttime` (`ffi/hacl_rsa.c` `l4_hacl_dh_modexp`,
  `Crypto/DhNative.lean`), with `Z ≤ 1` a decryption failure. Then the same
  `agreeDerive` (Concat KDF or PBKDF2) as ECDH-ES. Theorems:
  `xmlenc11_dhZ_eq_rfc2631` (given `Dh.ModExpAgrees`, HACL*'s correctness as
  a hypothesis), `xmlenc11_dhZ_size`, `xmlenc11_dh1024_needs_token`,
  `xmlenc11_dh1024_with_token`, `xmlenc11_dh_2048_no_token`,
  `xmlenc11_dhes_concat`. W3C AGRMNT.7 (Oracle DH-1024, Concat KDF): the key
  encryption key Lean derives equals Node's, and the case decrypts on the
  host. W3C AGRMNT.10 (DH-1024, PBKDF2) does not decrypt, like AGRMNT.9
  (https://github.com/danbri/factoidal/issues/1303). The legacy
  `xmlenc#dh` (§5.6.2, with its own key derivation and `KA-Nonce`) is
  refused, and `xmlEncrypt` does not write `dh-es`: both are listed as next
  parts of item 5 in https://github.com/danbri/factoidal/issues/1165.
* `xenc11:DerivedKey` (§5.4.3), since 2026-11-22 (track B item 5, part
  3): in `ds:KeyInfo` of `EncryptedData` (the content key) or of
  `EncryptedKey` (the key encryption key of AES Key Wrap; RSA-OAEP with a
  derived key is refused). One `KeyDerivationMethod` (Concat KDF or PBKDF2,
  through the same `kdfSized` as key agreement), optional
  `xenc:ReferenceList` and `DerivedKeyName` (read as labels only), and
  `MasterKeyName`, which names the caller's symmetric master key (else the
  caller's only symmetric key). The master key takes the place of Z.
  Theorems: `xmlenc11_deriveFromMaster_size`, `xmlenc11_derivedKey_concat`
  (§5.4.1 over the master key), `xmlenc11_derivedKey_pbkdf2_eq_rfc8018`.
  The npm `oct` key may have 1 to 1024 octets, for a master key or a
  password. W3C DRV.1 and DRV.2 are vendored and counted apart as defective
  test data (no padding block); the harnesses check that the key Lean
  derives equals the key Node derives.

## JWE profile

Compact serialization. A fixed allowlist decided before any key is read, in
the style of `JOSE/Jws.lean` `preKey`:

* `alg`: `RSA-OAEP`, `RSA-OAEP-256`, `ECDH-ES`, `ECDH-ES+A128KW`,
  `ECDH-ES+A256KW`, `A128KW`, `A256KW`, `dir`; refused: `RSA1_5`,
  `PBES2-*`, every other value;
* `enc`: `A128GCM`, `A256GCM`, `A128CBC-HS256`, `A256CBC-HS512`;
* refused: `zip` (compression oracle), any `crit`;
* after the allowlist, every failure is one error with no reason; an
  RSA-OAEP failure or a CEK of the wrong length continues with a substitute
  CEK (an HMAC of `d` and the encrypted key), so it shows only at the tag
  (RFC 7516 §11.5); CBC-HMAC checks the MAC in Lean, in constant time, before
  the `aes-cbc-decrypt` request;
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
* JWE (https://github.com/danbri/factoidal/issues/1085; `JOSE/Jwe.lean`,
  `JOSE/JweKey.lean`, wasm ops `jweDecrypt` and `jweEncrypt`):
  `lake exe l4jwe-probe 20` (native, HACL\* Vale AES-GCM): vectors 9 pass,
  0 fail, 3 NOT RUN (out of 12; RFC 7516 A.3 and RFC 7520 5.5 and 5.8 need
  AES Key Wrap or AES-CBC, which the native cipher does not have, issue 677);
  RFC 7518 Appendix C 5 pass, 0 fail (out of 5); random round trips and
  one-bit changes 520 pass, 0 fail (out of 520). `tests/jose/jwe-wasm.mjs 3`
  (wasm, WebCrypto answers every AES request): vectors 12 pass, 0 fail (out
  of 12); RFC 7518 Appendix B AES-CBC half 4 pass, 0 fail (out of 4);
  Appendix C 4 pass, 0 fail (out of 4); round trips 690 pass, 0 fail (out of
  690). `tests/jose/jwe-diff.mjs 5` (the wasm against a JWE written from
  WebCrypto calls in the test): 661 agree, 0 differ (out of 661). Structure
  (allowlist refusals, one error after it, `.need` replay, the CBC-HMAC MAC
  before the request, Appendix B HMAC half): 64 `#guard`s in
  `JOSE/JweTests.lean` over a stub cipher. Theorems:
  `decrypt_independent_of_key_before_key_stage`, `decrypt_refused_only_pre_key`,
  `cbc_mac_failure_makes_no_request`, `keyAlg_refused`,
  `epk_no_private_member`.
* XML Encryption 1.1 (https://github.com/danbri/factoidal/issues/1084) and
  SAML encrypted assertions (https://github.com/danbri/factoidal/issues/1073):
  `lake exe l4xmlenc-probe` (HACL\* RSA-OAEP, P-256, X25519, Vale AES-GCM)
  25 pass, 0 fail, 6 host-only (out of 31): 5 Santuario `EncryptedData`
  cases (RSA-OAEP mgf1p and SHA-256, Element and Content, RetrievalMethod)
  plus an altered ciphertext, `rsa-1_5` and CBC refusals, 2 Lean encrypt
  round trips, W3C WRAP.1 decrypted and 9 W3C cases refused by the
  allowlist, 5 SAML checks (Santuario `EncryptedAssertion` and `EncryptedID`
  with signatures verified, an unsigned inside refused, both refused with no
  key); the 6 host-only cases need AES Key Wrap or CBC and must fail natively.
  `node --test tests/xmlenc/wasm.mjs` (the wasm, WebCrypto answering through
  `runWithCipher`) 30 pass, 0 fail (out of 30), including AES Key Wrap with
  ECDH-ES P-256, X25519 and named keys, Santuario `aes128-cbc`
  (ISO 10126 padding), W3C WRAP.1 and AGRMNT.1. Santuario decrypts Lean's
  output (`tests/xmlenc/CheckLeanOutput.java`): 5 pass, 0 fail (out of 5).
  `#guard`s: `XML/EncTests.lean` 54, `SAML/Tests.lean` 18 new (two of them
  expected failures naming issue 1073). The server wiring replaced the
  first expected failure with 6 positive `#guard`s (the replay loop through
  `validateSubject` with AES Key Wrap, a refused answer, `recordCipher`);
  `saml:EncryptedAttribute` stays an expected failure.
