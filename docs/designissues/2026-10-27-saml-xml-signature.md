# SAML 2.0 subject tokens and the XML Signature profile under them

Date: 2026-10-27. Tracking: https://github.com/danbri/factoidal/issues/926
(SAML subject tokens need an XML Signature verifier), part of
https://github.com/danbri/factoidal/issues/916 (authorization server).
Gap: https://github.com/danbri/factoidal/issues/1073 (XML Encryption is
refused).

Owner request, 2026-10-27, verbatim: "Implement for factoidal. SAML and
enough xml security and encryption to do this. Be minimal and secure."

## What landed

| module | job |
| --- | --- |
| `formal/lean4/L4Factoidal/XML/ExcC14n.lean` | Exclusive XML Canonicalization 1.0, without comments, of one element subtree of the `XML.Parser` tree, with the InclusiveNamespaces PrefixList |
| `formal/lean4/L4Factoidal/XML/DSig.lean` | verification of one enveloped XML Signature over the document element, in the profile of SAML Core §5.4; theorem `verifyEnveloped_ok` |
| `formal/lean4/L4Factoidal/SAML/Assertion.lean` | decoding (RFC 8693 §3 base64url), trust by issuer, signature, conditions, audience, bearer subject confirmation; theorem `validate_ok` |
| `formal/lean4/L4Factoidal/Authz/SubjectToken.lean` | `validateSaml`, the fourth subject-token suite; theorem `validateSaml_valid` |
| `formal/lean4/L4Factoidal/SAML/Fixtures.lean`, `Tests.lean` | assertions made by the JDK's XML Signature API (`tests/saml/MakeFixtures.java`), checked by `#guard` |
| `formal/lean4/Wasm/Ops/Authz.lean` | config member `samlIdps` |
| `npm/factoidal/bin/factoidal.mjs` | `authz-serve --saml-idp FILE` (also `lws-serve --authz`) |

## How a token is checked, in order

1. Decode. At most 65,536 characters of base64url (RFC 4648 §5); UTF-8;
   element nesting at most 32 levels, counted on the text before the parse
   (so every recursive walk below has a constant depth); well-formed XML 1.0;
   an XML declaration names UTF-8 or no encoding.
2. Choose the key. The document element is `saml:Assertion`, `Version="2.0"`,
   one `saml:Issuer`. The issuer must be an `entityId` of the configuration
   (`samlIdps`); its RSA public key is used. A key in `ds:KeyInfo` is never
   read. lws10-authn-saml leaves trust out of band; this is the band.
3. Structure of the document (`DSig.signedParts`):
   * no document type declaration (so no entity expansion and no defaulted
     attribute), no comment, no processing instruction, every prefix bound;
   * the document element has an `ID`, and no other element has that value;
   * exactly one `ds:Signature` in the document, a child of the document
     element;
   * `ds:Signature` = `SignedInfo`, `SignatureValue`, optional `KeyInfo`;
     `SignedInfo` = `CanonicalizationMethod` (exc-c14n), `SignatureMethod`
     (rsa-sha256), one `Reference`; the `Reference` `URI` is `#` and the
     `ID`; its transforms are enveloped-signature then exc-c14n; its digest
     method SHA-256.
4. Digest. SHA-256 (pure Lean) of the exclusive canonical form of the
   document element without its `ds:Signature` equals `DigestValue`.
5. Signature. `JOSE.Pkcs1.rs256Verify` over HACL*'s RSA public operation, on
   the exclusive canonical form of `ds:SignedInfo` (its namespace context is
   that of `ds:Signature`). Moduli below 2048 bits are refused, by the
   primitive and again when the configuration is read.
6. Claims, read from the same parsed element that was digested:
   `saml:Conditions` (`NotOnOrAfter` required, `NotBefore` optional, UTC,
   60 seconds of skew; only `saml:AudienceRestriction` children, each of
   which names this server's issuer); `saml:Subject` = one `saml:NameID` and
   one bearer `saml:SubjectConfirmation` whose data has `Recipient` and
   `NotOnOrAfter` and no `NotBefore` (Profiles §4.1.4.2). The subject is the
   NameID text, the client the Recipient (lws10-authn-saml "Serialization").

## Choices made for minimal and secure, and their costs

* One signature profile only. A signature that uses inclusive C14N, SHA-1,
  RSA-PSS, ECDSA, two references, an XPath transform or `ds:Object` is
  refused. Cost: an identity provider that signs differently is refused
  with a message that names the rule. Touchstone's harness and the JDK's
  default SAML signing use this profile.
* The reference resolves to the document element by construction: the
  verifier never looks an element up by `ID`, and a reader of the claims
  reads that element. This closes the signature wrapping class (Somorovsky
  et al., "On Breaking SAML: Be Whoever You Want to Be", USENIX Security
  2012). The `wrapChild` and `wrapObject` fixtures are two of its forms.
* No comments anywhere. The "omits comments" canonical form drops a comment
  from the digested octets, so a NameID of `a<!---->b` would be signed as
  `ab` while a reader that took the first text node read `a` (the 2018
  CVE-2017-11427 family). The tree reader here concatenates text and would
  read `ab`, but the refusal removes the question. Cost: an identity provider
  that writes comments into assertions is refused.
* No DTD. Refused before the key is chosen.
* A subject token is an assertion, not a SAML `Response`. RFC 8693 §3 says
  so for this token type.
* `OneTimeUse` and `ProxyRestriction` are refused: they need a replay cache
  and a delegation model that the server does not have. An unknown condition
  is refused (SAML Core §2.5.1.1: the assertion is then not valid).
* XML Encryption is refused, not skipped:
  https://github.com/danbri/factoidal/issues/1073. Decryption needs RSA-OAEP
  with a private key and AES-GCM, and the use case does not need it.

## What is proved and what is tested

* `DSig.verifyEnveloped_ok`: `ok` implies the structural checks passed, the
  SHA-256 of the canonical document element equals the DigestValue, and the
  RSA verifier returned true on the canonical SignedInfo. Stated for any
  verifier.
* `SAML.validate_ok`: valid claims imply a trusted provider of the policy,
  whose `entityId` is the claimed issuer, and `verifyEnveloped` under its key.
* `Authz.validateSaml_valid`: the token endpoint's `valid` for a SAML token
  implies the same.
* Not proved: that `ExcC14n` meets the Recommendation. It is tested: its own
  `#guard`s from the Recommendation's rules, and agreement with the JDK
  (Apache Santuario) on every fixture, because a digest or a signature
  computed by the JDK over its canonical form verifies here only when the
  two canonical forms are the same octets.

Tests: `L4Factoidal/SAML/Tests.lean` (built by `lake build`; RSA through a
`Nat` reference public operation and the production padding check),
`node tests/authz/server.mjs` (the wasm module, HACL* RSA, assertions
signed by node:crypto), `bash tools/lws-touchstone.sh --config auth --authz
factoidal` (Touchstone `auth/saml`, 3 tests, with `SamlTrust`).

Measured 2026-10-27 on this change (full `lake build` 2388 jobs green;
`lean-unbuilt-modules`, `lean-tail-recursion-audit` and `lean-hygiene-audit`
gates pass): `node tests/authz/server.mjs` 39 pass, 0 fail, 0 xfail,
0 skipped (out of 39), of which 9 are SAML checks; Touchstone
`--config auth --authz factoidal` 215 passed, 0 failed, 6 inapplicable (out
of 221), auth/saml 3 pass, 0 fail (out of 3). Before this change the same
run gave 212 passed, 0 failed, 9 inapplicable, with auth/saml 3
inapplicable.
