# XML Signature versions, configurations and reusable operations

Date: 2026-10-31. Source audit before the broader implementation. This record
is not a claim that the requested configurations already work.

The machine-readable inventory is
[`tests/crypto/xml-signature-coverage.json`](../../tests/crypto/xml-signature-coverage.json).
It separates required/recommended/optional algorithms from observed source
support, and separates signature integration from reusable library code.
No whole-edition conformance is claimed. Newly added modules must update this
snapshot with test and proof evidence before being advertised as supported.

## Standards baseline

The core editions are XML Signature 1.0
([2002 Recommendation](https://www.w3.org/TR/2002/REC-xmldsig-core-20020212/)),
its [2008 Second Edition](https://www.w3.org/TR/2008/REC-xmldsig-core-20080610/),
[1.1, 2013 Recommendation](https://www.w3.org/TR/2013/REC-xmldsig-core1-20130411/),
and [2.0, 2015 Working Group Note](https://www.w3.org/TR/2015/NOTE-xmldsig-core2-20150723/).
The second edition is not version 2.0. Its major addition is mandatory
Canonical XML 1.1. Historical drafts remain useful regression inputs; they
must not be counted as extra completed W3C standards.

The 1.0 baseline includes SHA-1, HMAC-SHA1, DSA-SHA1, base64, inclusive
canonicalization and enveloped-signature processing. RSA-SHA1 and XPath
filtering are recommended; XSLT is optional. The 1.1 algorithm table adds
SHA-256, HMAC-SHA256, RSA-SHA256, ECDSA-SHA256 and Exclusive C14N requirements.
The JSON records other algorithms separately rather than treating every
algorithm identifier as mandatory.

There is a DSA interpretation detail to preserve: 1.1 section 6.1 lists
DSA-SHA1 verification as required, but section 6.4.1 describes legacy
1024-bit verification as MAY. Do not silently resolve this discrepancy with
a single `supports11` flag. The current RSA-only verifier cannot claim full
1.1 support regardless of that interpretation.

Version 2.0 stopped on the Recommendation track and received no WG
interoperability testing. Its indicative conformance model requires 2.0
processing, while compatibility mode is optional. Implementing compatibility
alone does not implement 2.0. Its reference processing has explicit selection,
canonicalization and verification stages; arbitrary transform chains are not
allowed in 2.0 mode. A Reference has no URI attribute and exactly one 2.0
Transform; selection carries its URI. See the Note's sections 3 and 6.

[Canonical XML 2.0](https://www.w3.org/TR/xml-c14n2/) and the
[streaming XPath profile](https://www.w3.org/TR/xmldsig-xpath/) are also
informative Notes. C14N2 applies to XML 1.0, not XML 1.1.
[XPath Filter 2.0](https://www.w3.org/TR/xmldsig-filter2/) is a separate 2002
Recommendation; its name means neither XML Signature 2.0 nor XPath 2.0.

## Existing code that can be reused

- `XML/DSig.lean`: restricted verification over one uniquely identified root,
  one enveloped signature, RSA-SHA256/SHA256 and Exclusive C14N without
  comments. `verifyEnveloped_ok` describes successful results relative to its
  supplied RSA verifier. Preserve this profile's acceptance rules.
- `XML/C14n.lean`: shared document-subset machinery for inclusive C14N 1.0,
  inclusive C14N 1.1 and Exclusive 1.0, with or without comments. This is
  broader than the subtree `XML/ExcC14n.lean` path currently used by DSig.
- `XML/C14nXPath.lean`: namespace-node mapping and per-node filtering, currently
  evaluated by XPath4. Audit XPath1 conversion rules, `here()`, context and
  arbitrary input subsets before exposing it as a general signature transform.
- `Crypto/SHA1.lean`, `Crypto/SHA2.lean`, `Crypto/Hmac.lean`,
  `Crypto/P256Native.lean`, `Crypto/RsaNative.lean`, and `JOSE/Pkcs1.lean`:
  digest and crypto building blocks. Pkcs1 is currently RS256-specific.
  No DSA primitive was located in this audit. A primitive cannot be replaced
  by a stub that reports successful verification.
- `XSLT4/FnTransform.lean`: existing transformation entry point. XSLT processing
  outside signing, as demonstrated in the compositor, does not implement the
  XML Signature XSLT transform. Its XSLT1 contract needs separate testing.

## Configuration is a product of independent choices

Expose edition/mode separately from an application policy. A supported
legacy algorithm can still be refused by a modern application policy. A
policy refusal, unsupported feature and invalid signature are distinct
results. Never fall back from an unsupported URI to another algorithm.

Other axes are signing versus verification; enveloped, enveloping or detached
placement; reference count, URI and ID semantics; Manifest traversal; transform
chains; canonicalization parameters; algorithm and key formats; HMAC output
length; XML/DTD/entity/schema processing; resource limits; trust; expected
application coverage; and execution target. A closed resource map supports
external-reference fixtures reproducibly without ambient network access.

Capabilities must describe actual callable implementations for each target.
A parser accepting an algorithm identifier does not establish execution
support. Use explicit configuration records to drive tests and publish their
measured cells, including refusals and unsupported combinations. Do not claim
that sampling a few combinations covers the whole product.

## Functional dataflow decomposition

Use typed Lean operations with explicit inputs and error results:

1. Parse XML and validate the selected signature grammar/profile.
2. Resolve a reference from the document or an explicit resource snapshot.
3. Apply typed node-set/octet transforms (1.x), or select data (2.0).
4. Canonicalize with a versioned method and explicit parameters.
5. Calculate and compare each reference digest; return the exact digest input.
6. Canonicalize SignedInfo, then verify using an explicit algorithm/key adapter.
7. Check trust and expected application coverage as separate predicates.
8. Assemble a report with per-reference evidence and a checked acceptance result.

The pure stages must have no file or network reads. Resolution requests can
be returned to a host and resumed with immutable results. Trust is not
inferred merely because KeyInfo supplied a key. Keep the signed document,
node identities, selection description and canonical bytes tied together so
that later stages cannot swap in a different object after verification.

Useful composition theorems relate the actual returned results: acceptance
implies every required reference digest matches, the signature predicate
holds over the emitted SignedInfo bytes, and the declared application policy
holds for this same input. Prove policy strengthening preserves refusals.
Crypto correctness and FFI refinement remain explicit assumptions unless
separately established; a coverage comparison does not prove human intent.

## Implementation order and evidence

First reuse C14n in typed 1.x reference operations, keeping restricted-profile
regressions. Then integrate existing P256 and hash facilities and add
algorithm/key-format fixtures. Generalize references and transforms with
explicit resource inputs. Add C14N2 and 2.0 selection/verification separately;
do not label a C14N1 result as C14N2. Finally add signing and remaining
primitives through the project's crypto policy, and expose each operation
through the registry/native/WASM APIs with identical semantics.

Official test sources:

- [Original interoperability report](https://www.w3.org/Signature/2001/04/05-xmldsig-interop.html)
  and its linked fixtures.
- [Second-edition/C14N1.1 tests](https://www.w3.org/TR/xmldsig2ed-tests/),
  including legacy cases. Their publication explicitly says test passage is
  neither necessary nor sufficient for a conformance claim.
- [1.1 interoperability report](https://www.w3.org/TR/xmldsig-core1-interop/)
  for added features, including EC keys, hashes and HMAC truncation.
- [C14N2 test cases](https://www.w3.org/TR/xml-c14n2-testcases/), with input,
  parameter and expected-byte files. These are not a complete end-to-end
  XML Signature 2.0 interoperability suite.

`Harness/C14nRun.lean` already reads the canonicalization corpus under
`third_party/testing/xml-c14n/`. It compares canonical reference/SignedInfo
bytes, not complete signatures. The compositor's generated Java fixtures are
independent-oracle fixtures, not W3C tests. This audit ran no conformance
suite and introduces no numerical passage claim. The JSON was parsed and all
listed local reusable source paths were checked for existence.
