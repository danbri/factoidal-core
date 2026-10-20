---
title: Canonical form and credentials
description: RDFC-1.0 canonical N-Quads, content hashes of graphs, and eddsa-rdfc-2022 Data Integrity proofs signed and verified in the page.
layout: hub.njk
tests: tests/hub/hub_canonical_test.mjs
---

# Canonical form and credentials

[Hub](../) · RDFC-1.0, VC Data Integrity (eddsa-rdfc-2022), did:key

## RDFC-1.0

Two documents that differ only in blank node labels and statement order
have the same RDFC-1.0 canonical form.

```observable-js
first = Factoidal.parse(`@prefix ex: <http://example.org/> .
ex:report ex:author _:a . _:a ex:name "Ada" ; ex:knows _:b . _:b ex:name "Bo" .`, { format: 'turtle' })
```

```observable-js
second = Factoidal.parse(`_:x <http://example.org/name> "Bo" .
_:y <http://example.org/knows> _:x .
<http://example.org/report> <http://example.org/author> _:y .
_:y <http://example.org/name> "Ada" .`, { format: 'ntriples' })
```

```observable-js
canonical = first.canonicalize()
```

```observable-js
sameGraph = (await second.canonicalize()) === canonical
```

A SHA-256 of the canonical form identifies the graph:

```observable-js
digest = Factoidal.vcSha256Hex(canonical)
```

## A Data Integrity proof (eddsa-rdfc-2022)

The proof value is an Ed25519 signature over the SHA-256 hashes of the
canonical proof configuration and the canonical document
([VC Data Integrity EdDSA Cryptosuites](https://www.w3.org/TR/vc-di-eddsa/),
section 3.3). The key below is the first test vector of RFC 8032; use it
only for examples.

```observable-js
secretKey = '9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60'
```

```observable-js
publicKey = Factoidal.vcEd25519SecretToPublic(secretKey)
```

```observable-js
credential = Factoidal.parse(`@prefix ex: <http://example.org/> .
@prefix cred: <https://www.w3.org/2018/credentials#> .
<urn:uuid:58172aac-d8ba-11ed-83dd-0b3aef56cc33> a cred:VerifiableCredential ;
  cred:issuer <did:example:issuer> ;
  cred:credentialSubject ex:ada .
ex:ada ex:completed ex:course101 .`, { format: 'turtle' })
```

```observable-js
proofConfig = Factoidal.parse(`@prefix sec: <https://w3id.org/security#> .
_:proof a sec:DataIntegrityProof ;
  sec:cryptosuite "eddsa-rdfc-2022"^^sec:cryptosuiteString ;
  sec:proofPurpose sec:assertionMethod ;
  sec:verificationMethod <did:example:issuer#key-1> ;
  <http://purl.org/dc/terms/created> "2026-10-20T00:00:00Z"^^<http://www.w3.org/2001/XMLSchema#dateTime> .`, { format: 'turtle' })
```

```observable-js
proofValue = Factoidal.vcEddsaCreateFromCanonical(secretKey, await credential.canonicalize(), await proofConfig.canonicalize())
```

```observable-js
verified = Factoidal.vcEddsaVerifyFromCanonical(publicKey, await credential.canonicalize(), await proofConfig.canonicalize(), proofValue)
```

Change one triple and the same proof no longer verifies:

```observable-js
afterTamper = {
  const changed = credential.clone();
  await changed.update('DELETE DATA { <http://example.org/ada> <http://example.org/completed> <http://example.org/course101> } ; INSERT DATA { <http://example.org/ada> <http://example.org/completed> <http://example.org/course999> }');
  return Factoidal.vcEddsaVerifyFromCanonical(publicKey, await changed.canonicalize(), await proofConfig.canonicalize(), proofValue);
}
```

## did:key

A `did:key` identifier holds an Ed25519 public key. Resolving it builds
the DID document locally; no network request is made.

```observable-js
didDocument = Factoidal.didKeyResolve('did:key:z6MkhaXgBZDvotDkL5257faiztiGiC2QtKLGpbnnEGta2doK')
```

## Limits

- RDFC-1.0 refuses a dataset that holds an RDF 1.2 triple term or a
  directional language-tagged string, because RDFC-1.0 defines labels for
  RDF 1.1 datasets only: <https://github.com/danbri/factoidal/issues/873>.
  Expected-failure test: `tests/hub/hub_canonical_test.mjs`.
- The Hash N-Degree Quads step uses one native stack frame per blank node
  of a path; about 2,000 blank nodes in one path overflow a 512 KB stack:
  <https://github.com/danbri/factoidal/issues/817>.
- The page signs canonical RDF directly. It does not expand a JSON-LD
  credential with remote contexts, which the package does not fetch:
  <https://github.com/danbri/factoidal/issues/667>.
