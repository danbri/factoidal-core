---
name: authz-server
description: Run, test and extend Factoidal's OAuth 2.0 authorization server component (factoidal authz-serve) - RFC 8414 metadata, the JWK Set, RFC 8693 token exchange for LWS access tokens, the subject-token suites (OpenID Connect, CID with https and did:key subjects, SAML 2.0 from configured identity providers), the private-address fetch guard, signing keys and rotation, the wasm ABI, the host tests and the Touchstone configuration that runs against it. Use when issuing tokens for lws-serve or another resource server, adding a credential suite, or reading a score from these suites.
---

# The authorization server component

Tracking: https://github.com/danbri/factoidal/issues/916. Design record:
`docs/designissues/2026-10-22-authorization-server.md`. Owner, 2026-10-22,
verbatim: "Do auth server (as a component other servers might use too)."

## Where each piece lives

| path | what it is |
| --- | --- |
| `formal/lean4/L4Factoidal/Authz/Keys.lean` | `Crypto` record (HACL\* instance `hacl`), keys, RFC 7638 `kid`, JWK Set, rotation, key file |
| `formal/lean4/L4Factoidal/Authz/Fetch.lean` | https/http rule, private-address guard, document and name cache |
| `formal/lean4/L4Factoidal/Authz/SubjectToken.lean` | the credential suites |
| `formal/lean4/L4Factoidal/SAML/Assertion.lean` | the SAML 2.0 assertion checks (issue 926) |
| `formal/lean4/L4Factoidal/XML/DSig.lean`, `XML/ExcC14n.lean` | the XML Signature profile of SAML Core §5, exclusive canonicalization |
| `formal/lean4/L4Factoidal/SAML/Tests.lean`, `Fixtures.lean`, `tests/saml/MakeFixtures.java` | `#guard`s over assertions made by the JDK's XML Signature API |
| `formal/lean4/L4Factoidal/Authz/Server.lean` | metadata, token endpoint, issuing with the self-check, `step` |
| `formal/lean4/L4Factoidal/Authz/Theorems.lean`, `Tests.lean` | theorems; `#guard`s with a stub signer |
| `formal/lean4/Wasm/Ops/Authz.lean` | the `authz*` ops |
| `formal/lean4/ffi/hacl_p256.c`, `L4Factoidal/Crypto/P256Native.lean` | HACL\* P-256 sign, secret-to-public, decompression (added for this component) |
| `npm/factoidal/authz/server.mjs` | Node host; `@factoidal/core/authz` |
| `tests/authz/server.mjs`, `tests/authz/e2e.mjs`, `tests/authz/fixtures.mjs` | host tests |

## Run it

```
factoidal authz-serve DIR --resource IRI[,IRI...] [--issuer IRI] [--port N] [--host ADDRESS]
                          [--alg ES256|EdDSA] [--token-lifetime SECONDS] [--rotate-after SECONDS]
                          [--allow-http] [--allow-private-fetch]
                          [--cors-origin ORIGIN]... [--no-cors] [--saml-idp FILE]...
factoidal authz-keys DIR [--private]
```

`--saml-idp FILE` (repeatable; config member `samlIdps`) trusts one SAML 2.0
identity provider: `{"entityId": "<saml:Issuer value>", "jwk": <RSA public
JWK, 2048 bits or more, no private member>}`.

With lws-serve (the storage IRI is the storage description):

```
factoidal authz-serve as-dir --port 4000 --resource http://127.0.0.1:3000/.well-known/lws-storage
factoidal lws-serve store-dir --port 3000 --issuer http://127.0.0.1:4000 --owner did:key:zDn...
```

lws-serve needs no other setting: it reads `<issuer>/.well-known/lws-configuration`,
then `jwks_uri`, and fetches the set again when a token names an unknown
`kid` (key rotation). Any other resource server reads the same RFC 8414
metadata (also at `/.well-known/oauth-authorization-server`) and RFC 7517 JWK
Set, and validates RFC 9068 tokens. From JavaScript:

```js
import { listen, openAuthorizationServer } from '@factoidal/core/authz'
const as = await listen({ dir: 'as-dir', port: 4000, resources: ['http://127.0.0.1:3000/.well-known/lws-storage'] })
```

### On the storage's port: `lws-serve --authz`

```
factoidal lws-serve store-dir --authz as-dir --owner did:key:zDn... [--base IRI]
```

One process, one port. The issuer is the storage root without its trailing
slash; the token endpoint and the JWK Set are at `BASE.well-known/lws-token`
and `BASE.well-known/lws-jwks`, beside the storage's other services, so no
name a client may give a storage resource is taken. The engine decides which
request is whose (`authzOwns`, `L4Factoidal/Authz/Mount.lean`, theorem
`endpointOf?_mem`: the authorization server takes only the paths of
`endpointPaths`); the storage trusts the issuer with the JWK Set from
`authzOpen`, so it never fetches its own URL. With `--rotate-after` the
storage fetches the metadata again when it meets an unknown `kid`. Every
well-known path is read in two forms, whole and with the base path removed,
so a reverse proxy may serve the storage at a path prefix and strip it
(`tests/authz/mounted.mjs` runs both). Docker target for third-party
testing: `deploy/lws-target/`.

## What it decides (all in Lean)

* Token endpoint (lws10-core "Token Exchange"): form parameters once each;
  `grant_type` token exchange or `unsupported_grant_type`; `resource`,
  `subject_token`, `subject_token_type` required (`invalid_request`); a
  resource outside `--resource` or an `audience` different from it is
  `invalid_target`; `actor_token` is `invalid_request`; a subject token that
  does not validate is `invalid_request` (RFC 8693 §2.2.2). 400, JSON,
  `Cache-Control: no-store`. A token: 200, `access_token`, `issued_token_type`,
  `token_type: Bearer`, `expires_in`.
* Access token (RFC 9068): `typ: at+jwt`, `kid`; `iss`, `sub`, `aud` = exactly
  `[resource]`, `client_id`, `iat`, `exp` = `iat` + lifetime (at most 300),
  `jti` from host random bytes. ES256 by default (HACL\*
  `Hacl_P256_ecdsa_sign_p256_sha2` with a host nonce); `--alg EdDSA` uses the
  Ed25519 binding. Touchstone and Nimbus verify only ES256 and RS256.
* Suites: OpenID Connect ID token (`sub` document names `iss` as an
  `lws#OpenIdProvider` service; discovery `issuer` equals `iss`; key by
  `kid` from `jwks_uri`); CID suite, https subject: the CID 1.0 module
  `L4Factoidal/CID/` (https://github.com/danbri/factoidal/issues/1100),
  §2 data-model checks of the whole document, §3.3 Retrieve Verification
  Method with `authentication` (document `id` = `sub`; method embedded or
  referenced; `controller` = `sub`), then not revoked or expired (§2.2);
  record `docs/designissues/2026-10-27-cid-1.0.md`; CID suite, did:key subject (P-256
  compressed via HACL\*, or Ed25519; `kid` = `did#z…` or `z…`). SAML 2.0
  (https://github.com/danbri/factoidal/issues/926): base64url
  `saml:Assertion` from a configured provider; one enveloped signature,
  exc-c14n, rsa-sha256, the reference `#` + the document element's `ID`,
  verified under the CONFIGURED key (never `ds:KeyInfo`); no DTD, comment or
  PI; nesting at most 32; `Conditions` times and every `AudienceRestriction`
  naming this issuer; bearer confirmation with `Recipient` (the client) and
  `NotOnOrAfter`; `NameID` is the subject. Encrypted elements are refused
  (https://github.com/danbri/factoidal/issues/1073). Advertised only when
  `samlIdps` is not empty. Record:
  `docs/designissues/2026-10-27-saml-xml-signature.md`.
* Fetches: `https` only unless `--allow-http`; every address of the host
  (literal, `localhost` name, or the host's resolution) must be outside
  loopback, unspecified, link-local, RFC 1918 and RFC 4193 unless
  `--allow-private-fetch`; the host connects to the address the engine names
  and follows no redirect. Both flags are for tests (Touchstone fixtures are
  `http://localhost`).
* Keys: `DIR/authz-keys.json`, mode 0600, sealed with `FACTOIDAL_LWS_KEY`
  (as the LWS snapshot). `--rotate-after` makes a new key; the old one stays
  published for lifetime + leeway.
* CORS (https://github.com/danbri/factoidal/issues/923): `stepCors` answers a
  preflight 204 before `step` (no key rotation) and adds the fields of
  `L4Factoidal/HTTP/Cors.lean` to every other answer, with `corsProfile`
  (methods `GET, HEAD, OPTIONS, POST`; exposed `Allow, WWW-Authenticate`; no
  credentials). Default: echo a valid `Origin`; `--cors-origin ORIGIN`
  (repeatable) or `--no-cors`; config member `cors`. Theorems
  `stepCors_preflight`, `stepCors_off`. Host check: `tests/lws/cors.mjs`.

## Theorems, and what they rest on

`issueToken_verifies_published`, `issueToken_audience_exact` and their
endpoint forms hold BECAUSE OF A RUN-TIME CHECK: `issueToken` verifies its
own token under the key parsed from its own published JWK Set text, and
checks `aud`, `iss`, `sub`, before it answers; otherwise 500 and no token.
The round-trip proof that would remove the check:
https://github.com/danbri/factoidal/issues/927.

Structural: `tokenOutcome_issued`, `exchange_refused_no_token` (a subject
token that fails validation never yields an access token),
`validateSubject_valid_verified`, `didKey_valid_verified`, `validateSaml_valid`
(with `SAML.validate_ok` and `XML.DSig.verifyEnveloped_ok`),
`cid_valid_verified`, `cidKey_method`, `oidc_valid_named_provider`,
`jwks_no_private_member`, `metadata_issuer_eq`, `rotate_keeps_previous`,
`chooseAddress_refuses_private`, `lookup_http_refused`. Axioms: `propext`,
`Classical.choice`, `Quot.sound`.

## Tests

```
node tests/authz/server.mjs     # the host over the wasm module
node tests/authz/e2e.mjs        # authz-serve + lws-serve + solid-serve processes
lake exe l4crypto-probe         # sections p256-sign-rfc6979, p256-secret-to-public, p256-compressed
bash tools/lws-touchstone.sh --config both --authz factoidal
```

Scores, 2026-10-22: `tests/authz/server.mjs` 30 pass, 0 fail, 1 xfail,
0 skipped (out of 31); `tests/authz/e2e.mjs` 7 pass, 0 fail, 1 xfail,
0 skipped (out of 8); `Authz/Tests.lean` 93 `#guard`s; l4crypto-probe
p256-sign-rfc6979 12 pass, 0 fail (out of 12), p256-secret-to-public 357
pass, 0 fail (out of 357), p256-compressed 341 pass, 0 fail, 1 acceptable
(out of 342). Touchstone `--config auth --authz factoidal`: 212 passed,
0 failed, 9 inapplicable (out of 221); our server's groups:
core/authorization_server 9 pass, 0 fail (out of 9), auth/oidc 6 pass,
0 fail (out of 6), auth/cid 22 pass, 0 fail (out of 22), auth/saml 3
inapplicable (out of 3). Record:
`docs/designissues/2026-10-21-lws-touchstone-run.md`.

Scores, 2026-10-27 (SAML landed): `tests/authz/server.mjs` 39 pass, 0 fail,
0 xfail, 0 skipped (out of 39); `tests/authz/e2e.mjs` 7 pass, 0 fail,
1 xfail, 0 skipped (out of 8); `tests/authz/mounted.mjs` 6 pass, 0 fail
(out of 6). Touchstone `--config auth --authz factoidal`: 215 passed,
0 failed, 6 inapplicable (out of 221); auth/saml 3 pass, 0 fail (out of 3);
our server's 40 tests 40 pass, 0 fail (out of 40).

SAML (https://github.com/danbri/factoidal/issues/926) since 2026-10-27:
`L4Factoidal/SAML/Tests.lean` (`lake build`), the SAML checks in
`server.mjs`, and Touchstone `auth/saml` with `SamlTrust` under
`--authz factoidal` (the script makes the identity provider key).

Expected failures: solid-serve accepting these tokens
(https://github.com/danbri/factoidal/issues/928) in `e2e.mjs`. An unexpected
pass turns the run red.

## Adding a suite

1. Write its validation in `SubjectToken.lean`: claim checks returning the
   subject and client, and a key selection returning `KeyFound`; reach
   `valid` only through `withKey` (and so `finish`).
2. Name every document it needs through `lookup`, so the address guard
   applies.
3. Advertise its token type in `metadataJson` only when it works.
4. `#guard`s in `Tests.lean`, a host check in `tests/authz/server.mjs`, and a
   theorem in the shape of `cid_valid_verified`.
