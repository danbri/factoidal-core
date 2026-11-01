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

## Signature generation (§3.1)

Code: `formal/lean4/L4Factoidal/XML/DSig11Sign.lean`; signers in
`XML/DSig11Native.lean`. Added 2026-11-01.

`DSig11.sign be signer spec rand src` makes one `ds:Signature`:

1. §3.1.1: the signature, with empty digest and signature values, is put
   in its place (`enveloped`: the last child of the document element;
   `enveloping`: the signature is the document and the content is in a
   `ds:Object` with an `Id`). Each reference is digested by
   `DSig11.referenceOctets`, the function core validation uses, in that
   document.
2. §3.1.2: `ds:SignedInfo` with the digests is put in place and
   canonicalized by `DSig11.signedInfoOctets`, the function core validation
   uses. An inclusive method takes the namespaces of the ancestors, so the
   octets must come from the document that is returned, not from the
   `ds:SignedInfo` text alone.
3. The signer signs those octets. The value goes into `ds:SignatureValue`,
   and `ds:KeyInfo` gets the public key as `ds:KeyValue`.
4. Self-check: the result must pass core validation with the signer's
   public key and `ds:KeyInfo` not read (for HMAC: the references, and the
   MAC recomputed by the custodian). `dsig11_sign_validates` states this
   for every backend. A request whose reference covers the signature value
   (`URI=""` without the enveloped-signature transform) is refused here.

### Signer component

`Signer` is the custodian of one key (`docs/web/hub/webdav-lws-design.md`,
"One custodian per privileged resource"). It gives its algorithm, its
public key and signature values; the key stays in the closure of
`hmacSigner`, `rsaSigner` or `p256Signer`. Decisions:

- `rsaSigner` makes the EMSA-PKCS1-v1_5 block with
  `JOSE.Pkcs1.emsaEncodeGen` (the function the verifier compares with) and
  uses the constant-time HACL\* private operation of `Crypto/RsaOaep.lean`
  (2048, 3072 and 4096-bit moduli; a smaller modulus is refused when the
  signer is made). It verifies its value with the public operation before
  it gives it out (fault attacks on RSA signing, Boneh, DeMillo and Lipton
  1997).
- `p256Signer`: the ECDSA nonce is the `rand` argument of each `sign` call
  (32 octets from the host's random source), not a value fixed when the
  signer is made, so one signer cannot sign two messages with one nonce.
  `VC.Cryptosuite.diSigner` takes its nonce when it is made; the wasm op
  `vcDiSecure` makes a new signer for each call (`Wasm/Ops/Vc.lean`).
- XML Encryption (item 5) will take its private keys through the same kind
  of component.

### Round trips

`lake exe l4xmldsig` signs the document of the signxml fixtures in 15 cases
(`signCases`) with the test keys of `tests/xmldsig/signing-keys.tsv`
(published; for tests only). Each result must validate with the key of its
`ds:KeyInfo` and be refused after one character of the signed content
changes. With `--sign-out DIR` the documents are written for
`tests/xmldsig/verify_lean_signed.py`, which verifies them with signxml 5.2.
Result of 2026-11-01: 15 pass, 0 fail (out of 15) in both. Two signxml
differences are handled by name in that script:

- `rsa-sha256-c14n10c`: `URI=""` gives the document "minus any comment
  nodes" (§4.4.3.3), also before a WithComments method. signxml digests the
  comments, so it refuses this signature, as expected; the case fails if
  signxml starts to accept it.
- signxml's copy of the XML Signature schema has no declaration of
  `ec:InclusiveNamespaces`, which the strict wildcard of
  `ds:CanonicalizationMethod` needs. The PrefixList case is verified again
  without that schema check, and the output line says so.

## ECDSA P-256 with every digest (2026-11-01, part 3)

FIPS 186-4 §6.4 makes the integer `e` from the leftmost `min(N, outlen)`
bits of the hash (`N = 256` for P-256). The digest is computed in Lean
(`DigestAlg.digest`), and `Crypto.P256.p256MsgRep` gives `e` as 32
big-endian octets: the first 32 octets of a hash of 32 octets or more, or a
shorter hash (SHA-1, SHA-224) left-padded with zero octets. HACL\*
`Hacl_P256_ecdsa_verif_without_hash` and
`Hacl_P256_ecdsa_sign_p256_without_hash` take `e` (`ffi/hacl_p256.c`,
`l4_hacl_p256_verify_prehashed` and `l4_hacl_p256_sign_prehashed`; the shim
refuses an `e` that is not 32 octets, because HACL\* reads 32 octets of its
input whatever its length argument is). HACL\*'s own `..._sha384` and
`..._sha512` entries take the first 32 octets of the hash in the same way.

- Theorems: `p256MsgRep_size` (32 octets), `p256MsgRep_of_size32` (a
  SHA-256 hash is its own representative), `dsig11_native_ecdsa_p256` (each
  `ecdsa-sha*` method at P-256 is the HACL\* check over the representative
  of the Lean digest), `dsig11_native_ecdsa_other_curves` (P-384 and P-521
  stay `none`).
- `p256Signer sk h` signs with any of the five digests and checks the value
  with the verifier before it gives it out.
- Measured by: the 7 P-256 interop vectors with SHA-1, SHA-224, SHA-384 and
  SHA-512 (RFC 4050 key form included), which now pass; Wycheproof
  `ecdsa_secp256r1_sha256_p1363_test.json` and
  `ecdsa_secp256r1_sha512_p1363_test.json` through
  `nativeBackend.ecdsaVerify`; four new generation cases.

## XPath Filter 2.0 (2026-11-01, part 4)

Code: `formal/lean4/L4Factoidal/XML/DSigFilter2.lean` (XML-Signature XPath
Filter 2.0, W3C Recommendation 08 November 2002, algorithm
`http://www.w3.org/2002/06/xmldsig-filter2`), called from
`DSig11.applyTransform`.

- §3.4: the filter node-set F starts as every node of the input document.
  For each `XPath` element in order, the expression is evaluated once, with
  the root node as the context node (`C14nXPath.xpathSelect`, the XPath 4.0
  engine), the result is subtree-expanded (`expandArr`, one pass in node
  table order, because a parent is always before its children, attributes
  and namespace nodes), and F becomes F ∩ S', F − S' or F ∪ S'. The output
  is the input node-set ∩ F.
- `here()` (§3.3 of Filter 2.0, §6.6.3.1 of XML Signature) is a host
  function of the XPath 4.0 engine (`C14nXPath.hereHost`). It names the
  `XPath` element when the input is a node-set of the signature's document,
  and is an error otherwise, as both specifications say. The XPath
  filtering transform of §6.6.3 now has it too.
- Theorems (2002 in the name): `filter2_2002_single_pass` (F equals the
  flag Z of the single-pass method that §3.4 describes, for every operation
  list), `filter2_2002_output_subset`, `filter2_2002_empty_input`,
  `filter2_2002_union_only` (a transform of only `union` filters gives its
  input, §4), `expandSpec_self` and `expandSpec_parent`.
- Measured by: Merlin Hughes's vectors `merlin-xpath-filter2-three`
  (`third_party/testing/xmldsig-filter2-interop`, provenance there). The
  runner compares the octets of each reference with the published
  canonical output and checks each digest. The signatures are DSA, so core
  validation is an expected failure that names
  https://github.com/danbri/factoidal/issues/1224.
- XSLT stayed refused in this part (part 5 below adds it).

## The XSLT transform and the 2001 interop vectors (2026-11-01, part 5)

Code: `formal/lean4/L4Factoidal/XML/DSigXslt.lean` (§6.6.5, algorithm
`http://www.w3.org/TR/1999/REC-xslt-19991116`), called from
`DSig11.applyTransform`.

- Input: octets. A node-set input is first written by Canonical XML 1.0
  without comments (`DSig11.toOctets`, §4.4.3.2).
- Stylesheet: the one element child of `ds:Transform`, which must be
  `xsl:stylesheet` or `xsl:transform`. It is written out as text by
  Canonical XML 1.0 over its subtree (`C14n.canonicalize`), so it keeps
  every namespace binding that is in scope in the signature document. Any
  other content is refused with the reason.
- Processor: the XSLT 4.0 processor of `L4Factoidal/XSLT4/`
  (`compileStylesheet`, `transform`). A `version="1.0"` stylesheet runs in
  the backwards-compatible mode of XSLT 4.0. The XSLT 4.0 processor was
  chosen over the XSLT 1.0 module of `L4Factoidal/XSLT/` because it applies
  `xsl:output` (XSLT 1.0 §16) when it writes the result, and the octets of
  the result are what the next transform or the digest reads. A relative
  URI in the stylesheet (`xsl:import`, `document()`) gets no resource.
- Output: the UTF-8 octets of the serialized principal result. §6.6.5
  recommends a canonicalization after XSLT; that is the next transform of
  the reference, not part of this one.
- Theorems (1999 is the XSLT version of the algorithm URI):
  `dsig11_xslt_1999_output` (the output is the UTF-8 encoding of the
  serialized result of the named stylesheet on the input, with nothing
  added), `dsig11_xslt_1999_no_stylesheet` (a `ds:Transform` with no
  element child is refused).
- Measured by: Merlin Hughes's `merlin-xmldsig-twenty-three`
  (`third_party/testing/xmldsig-merlin-2001`, provenance there), the
  interop vectors of XML Signature 1.0 (2001-2002). The runner checks the
  digest of every `ds:Reference` of each file, those in `ds:Manifest`
  included (36 references; reference 20 of `signature.xml` is the XSLT
  transform, `c7wq5XKos6RqNVJyFy7/fl6+sAs=`, which libxslt also gives on the
  same input), then core validation of the 16 signatures. The two external
  references resolve to the vendored `xml-stylesheet.b64` and to its decoded
  octets (the 1999 text of `http://www.w3.org/TR/xml-stylesheet`), never to
  the network. Core validation: the HMAC-SHA1 signature passes; the
  HMAC-SHA1 signature with `HMACOutputLength` 40 is refused, because XML
  Signature 1.1 §6.3.1 requires it (the 2002 vectors were valid under 1.0);
  13 DSA signatures are expected failures that name
  https://github.com/danbri/factoidal/issues/1224, and the RSA signature
  (a 1024-bit key) names https://github.com/danbri/factoidal/issues/1227.

## Open (each with an issue and an expected failure, or a refusal)

- ECDSA P-384 and P-521:
  https://github.com/danbri/factoidal/issues/1223 (18 interop cases). HACL\*
  has no P-384 or P-521 (https://github.com/danbri/factoidal/issues/1166).
- DSA: https://github.com/danbri/factoidal/issues/1224.
- `ds:X509Data`: https://github.com/danbri/factoidal/issues/1226 (1 case).
- RSA keys of 1024 bits: https://github.com/danbri/factoidal/issues/1227
  (10 cases; decision needed).
- `ds:KeyName`, `ds:RetrievalMethod` and the X.509 forms of the 2001
  vectors are not reached, because their signatures are DSA; they are part
  of https://github.com/danbri/factoidal/issues/1224 and
  https://github.com/danbri/factoidal/issues/1226.
- A wasm op: an open item of item 4 of
  https://github.com/danbri/factoidal/issues/1165.
