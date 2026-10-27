# An authorization server as a component (issue 916)

Tracking: https://github.com/danbri/factoidal/issues/916. Written before the
code, 2026-10-22.

Owner, 2026-10-22, verbatim: "Approved. Do auth server (as a component other
servers might use too). Then LWS client."

Coordinator decisions of the same day, within that approval: ES256 signing
through three new `@[extern]` wrappers over the vendored HACL\* P-256 code;
theorems by checked construction (below); solid-serve in stage 2
(https://github.com/danbri/factoidal/issues/928); `http` subjects only with
`--allow-http`; a private-address guard on every fetch in stage 1; SAML as an
expected failure (https://github.com/danbri/factoidal/issues/926; landed
2026-10-27, see `2026-10-27-saml-xml-signature.md`); no token introspection.

## What the drafts require

Sources: the W3C Linked Web Storage Working Group editor's drafts, read from
`w3c/lws-protocol` (checkout of 2026-10-22).

lws10-core, section "Authorization":

* "Authorization Server Metadata": "An authorization server MUST provide a
  metadata resource to allow clients to discover endpoint locations and
  capabilities as described in [RFC8414]. This metadata resource MUST be
  available at a URL with the path /.well-known/lws-configuration." Two more
  members: `subject_token_types_supported` and
  `subject_identifier_types_supported` (each "SHOULD advertise"; the second
  defaults to `["https"]`).
* "Token Exchange", "Request": "The authorization server's token endpoint
  MUST support the urn:ietf:params:oauth:grant-type:token-exchange grant
  type"; "The resource parameter is REQUIRED [...] will be used to populate
  the aud (audience) claim [...] The authorization server MUST reject any
  request in which the resource parameter identifies an unknown or untrusted
  storage"; "The subject_token parameter is REQUIRED"; "Before returning an
  access token to the client, the authorization server MUST successfully
  validate all presented tokens."
* "Token Exchange", "Response": RFC 6749 §5.1, an RFC 9068 JWT, with `sub`,
  `iss`, `client_id`, `aud` ("MUST include the URI supplied by the client in
  the resource parameter"), `exp` ("RECOMMENDED: 300 seconds or less"), `iat`,
  `jti`. "All invalid or unauthorized requests MUST result in an error
  response as described in Section 5.2" of RFC 6749.
* "Protocol Flow": "The interaction between the authorization server and the
  storage server is out of scope of this specification."

lws10-core, section "Authentication": "Authentication Credential Data Model"
(subject, issuer and client are URIs), "Authentication Credential
Validation" ("An authentication credential MUST be signed"),
"Authentication Credential Type Identifiers".

lws10-authn-openid: "Authentication Credential Serialization" (no `none`;
`sub`, `iss`, `azp`, `aud`); "Authentication Credential Validation" ("the
validator MUST dereference the sub (subject) claim", a controlled identifier
document whose `id` is the subject, "a service object whose serviceEndpoint
value is equal to the value of the iss claim [...] and whose type value is
equal to https://www.w3.org/ns/lws#OpenIdProvider", OpenID Connect Discovery
for the key, OpenID Connect Core §3.1.3.7); "Token Type Identifier"
(`urn:ietf:params:oauth:token-type:id_token`).

lws10-authn-ssi-cid: "Authentication Credential Serialization" (`sub`, `iss`
and `client_id` "MUST all use the same URI value", `aud` "MUST include the
target authorization server", `exp` and `iat` required); "Authentication
Credential Validation" (dereference `sub`, "use the kid (key ID) value from
the signed JWT header to identify a verification method" per CID 1.0 §3.3,
RFC 7515 §5.2, `exp`); "Token Type Identifier"
(`urn:ietf:params:oauth:token-type:jwt`). It covers HTTPS and DID subjects.

lws10-authn-ssi-did-key: discontinued in favour of lws10-authn-ssi-cid; its
"Authentication Credential Validation" takes the key from the identifier
(did:key §3.1.3). We read a did:key subject under the CID suite, as
Touchstone does.

lws10-authn-saml: "Authentication Credential Validation": "the signature of
the credential MUST be validated as described in SAML Core, section 5". The
tree has NO XML Signature verifier (it has inclusive Canonical XML in
`XML/Canonical.lean`, exclusive canonicalization in `RDF/XmlCanon`, and the
RSA PKCS#1 v1.5 check in `JOSE/Pkcs1`, but no XML-DSig reference processing).
So SAML is not accepted and not advertised; expected failures name
https://github.com/danbri/factoidal/issues/926.

Update, 2026-10-27: SAML is accepted from the identity providers the
configuration names (`samlIdps`, `--saml-idp`), through exclusive
canonicalization (`XML/ExcC14n.lean`) and the SAML Core §5 signature profile
(`XML/DSig.lean`). Record: `2026-10-27-saml-xml-signature.md`.

## The component

Lean: `formal/lean4/L4Factoidal/Authz/`. Host: `npm/factoidal/authz/`.
CLI: `factoidal authz-serve DIR`. JavaScript: `@factoidal/core/authz`. It
knows nothing about LWS storage: it issues tokens for the resource IRIs it is
configured with. Any resource server that reads RFC 8414 metadata and a JWK
Set can use it.

### Endpoints

The issuer is an absolute `http(s)` IRI with no query and no fragment
(`--issuer`, default the bound origin). With a path, RFC 8414 §3.1 puts the
metadata at `/.well-known/lws-configuration` followed by the path.

| method | path | answer |
| --- | --- | --- |
| GET, HEAD | `/.well-known/lws-configuration` | RFC 8414 metadata |
| GET, HEAD | `/.well-known/oauth-authorization-server` | the same document (the RFC 8414 default name, for third-party resource servers) |
| GET, HEAD | `<issuer>/jwks` | the JWK Set: public keys only |
| POST | `<issuer>/token` | RFC 8693 token exchange |

Another method on a known path: 405 with `Allow`. Another path: 404.
Metadata members: `issuer`, `token_endpoint`, `jwks_uri`,
`grant_types_supported` (token exchange only), `response_types_supported`
(empty: there is no authorization endpoint), `token_endpoint_auth_methods_supported`
(`none`), `claims_supported`, `subject_token_types_supported` (`jwt`,
`id_token`), `subject_identifier_types_supported` (`https`, `did:key`).

No token introspection (RFC 7662): the access token is a JWT that a resource
server validates with the JWK Set.

### Token endpoint

`application/x-www-form-urlencoded`. A parameter given twice is
`invalid_request` (RFC 6749 §3.2). `grant_type` other than token exchange:
`unsupported_grant_type`. Missing `resource`, `subject_token` or
`subject_token_type`: `invalid_request`. A `resource` not in the configured
list: `invalid_target` (RFC 8693 §2.2.2). An `audience` parameter different
from `resource`: `invalid_target`. An `actor_token`: `invalid_request` (not
supported). A subject token that does not validate: `invalid_request`
(RFC 8693 §2.2.2). Every error: 400, JSON `{"error","error_description"}`,
`Cache-Control: no-store`. A success: 200, `access_token`,
`issued_token_type` (`urn:ietf:params:oauth:token-type:access_token`),
`token_type` `Bearer`, `expires_in`; `Cache-Control: no-store`,
`Pragma: no-cache` (RFC 6749 §5.1).

### Credential suites, in order

1. OpenID Connect ID token (`id_token`): `iss`, `sub`, `azp` strings; `aud`
   contains this issuer; `exp`, `iat`, `nbf` with 60 s leeway. Fetch the
   subject's document: its `id` is `sub` and a `service` has type
   `https://www.w3.org/ns/lws#OpenIdProvider` and `serviceEndpoint` equal to
   `iss`. Fetch `<iss>/.well-known/openid-configuration`; its `issuer` must be
   `iss` (OpenID Connect Discovery §4.3). Fetch its `jwks_uri`; the `kid`
   selects the key. Subject `sub`, client `azp`.
2. CID suite, HTTPS subject (`jwt`): `sub` = `iss` = `client_id`; `aud`
   contains this issuer; `exp` and `iat` required. Fetch the document at
   `sub`: `id` = `sub`; the method is the one `authentication` names (embedded,
   or referenced and defined under `verificationMethod`) whose `id` resolves
   to `kid` (a fragment is resolved against `sub`); its `controller` is
   `sub`; no `revoked` or `expires` time at or before now (CID 1.0 §2.2);
   the key is its `publicKeyJwk` (or a `Multikey` `publicKeyMultibase`).
3. CID suite, `did:key` subject (`jwt`): the same claim checks; the key is
   decoded from the identifier: multicodec `0x1200` (P-256, 33-byte
   compressed point, decompressed by HACL\*) or `0xed` (Ed25519). `kid` is
   `did:key:z…#z…` or `z…`.
4. SAML 2.0 assertion (`saml2`): refused, not advertised. Issue 926.

`alg: none` and every algorithm outside ES256, RS256, EdDSA are refused by
`JOSE.preKey` before any key is chosen.

### Fetches and the private-address guard

The engine names every document it needs; the host fetches. A URL must be
`https` (or `http` with `--allow-http`, off by default). Before a fetch the
engine needs the host's addresses: a literal is read directly; for a name
the engine answers `resolve {host}` and the host passes every address back
(`authzFetched {host, addresses}`). Unless `--allow-private-fetch` is set,
the engine refuses the fetch when ANY resolved address is loopback
(127.0.0.0/8, ::1), unspecified (0.0.0.0, ::), link-local (169.254.0.0/16,
fe80::/10), private (10.0.0.0/8, 172.16.0.0/12, 192.168.0.0/16, RFC 1918;
fc00::/7, RFC 4193), or a `localhost` name. The fetch answer names the
address the host must connect to, so the host does not resolve the name a
second time. The host does not follow redirects. Address parsing is
`LWS/InboxGuard.lean` (`addr?`, `authority?`, `localhostName`).

Documents are cached for `docTtl` seconds (default 60), failures too; a JWK
Set that lacks the token's `kid` is fetched again at most once per second.
The cache holds at most 256 entries.

### Token format and keys

RFC 9068: header `{"alg":"ES256","typ":"at+jwt","kid":…}`; claims `iss`,
`sub`, `aud` (an array holding exactly the requested resource), `client_id`,
`iat`, `exp` (`iat` + lifetime, default 300 s, at most 300), `jti` (16
random bytes, hex). `kid` is the RFC 7638 thumbprint.

Default algorithm ES256: HACL\* `Hacl_P256_ecdsa_sign_p256_sha2` with a
32-byte nonce from the host's random source (a second candidate when HACL\*
refuses the first). New private keys: 32 random bytes, checked by
`Hacl_P256_dh_initiator`. `--alg EdDSA` signs with the existing Ed25519
binding; Touchstone and the Nimbus library it uses verify only ES256 and
RS256, so EdDSA is not the default. The three new externs
(`l4_hacl_p256_sign_sha256`, `l4_hacl_p256_secret_to_public`,
`l4_hacl_p256_compressed_to_raw`) each call exactly one HACL\* function; the
C shim checks lengths only.

Rotation: with `--rotate-after SECONDS` (0, the default, never), the next
request after that age makes a new key from host random bytes. The old key
stays in the JWK Set until its retirement time plus lifetime plus leeway, so
tokens it signed still validate. `authzRotate` rotates at once (tests). A
storage server (`LWS/Authorization.lean`) fetches the JWK Set again when it
meets an unknown `kid`, so it follows a rotation with no configuration.

Persistence: `DIR/authz-keys.json`, written by temporary file, fsync, rename,
mode 0600. With `FACTOIDAL_LWS_KEY` set it is sealed exactly as the LWS
snapshot (`LWS/SnapshotSeal.lean`, ChaCha20-Poly1305 from HACL\*); a sealed
file without the key, a clear file with a key, or a wrong key: the server
refuses to start. The file holds private keys: in clear form it is protected
only by its mode.

### Theorems, by checked construction

Before it answers with a token, the issuer checks its own output: it parses
the token, finds the key with the token's `kid` in the JWK Set text it
publishes (parsed by the same `parseJwks?` the storage server uses), checks
the signature with the same `JOSE.verifyCompact` and verifiers, and checks
that `aud` is exactly `[resource]`, `iss` the issuer and `sub` the subject.
If any check fails it answers 500 `server_error` and no token. So these
theorems hold for every token the server gives out BECAUSE OF THAT RUN-TIME
CHECK, not because the serializer and the parser were proved to agree:

* `issue_verifies_published`: an issued token verifies under a key of the
  published JWK Set with the token's `kid`.
* `issue_audience_exact`: its claims carry `aud = [resource]`, `iss` the
  issuer, `sub` the validated subject.
* `exchange_issued_valid_subject`, `exchange_refused_no_token`: a token is
  issued only after the subject token validated, for a configured resource
  equal to the requested one; a subject token that fails validation never
  yields an access token.
* `didKey_valid_verified`, `cid_valid_verified`, `oidc_valid_named_provider`:
  what a valid subject token established, per suite.
* `jwks_no_private_member`, `metadata_issuer_eq`, `rotate_keeps_previous`,
  `fetchDecision_refuses_private`.

The proof that the check never fails (a JSON print/parse and compact JWS
round trip), which would let it be removed:
https://github.com/danbri/factoidal/issues/927.

### How a resource server uses it

* `factoidal lws-serve DIR --issuer <issuer>`: nothing else. lws-serve reads
  `<issuer>/.well-known/lws-configuration`, then `jwks_uri`, and checks `aud`
  against its storage IRI (`<base>.well-known/lws-storage`). Start the
  authorization server with `--resource <base>.well-known/lws-storage`.
* Any other resource server: RFC 8414 metadata and RFC 7517 JWK Set, RFC 9068
  tokens.
* Lean: `L4Factoidal.Authz.Server.step` and the pure functions it calls.
* solid-serve: stage 2. Solid-OIDC expects a DPoP-bound token with
  `aud: solid` and a WebID profile check, so solid-serve refuses these Bearer
  tokens today; an expected failure in `tests/authz/e2e.mjs` names
  https://github.com/danbri/factoidal/issues/928.

### Wasm ABI

| op | arguments | answer |
| --- | --- | --- |
| `authzOpen` | config JSON | `{ok, handle, changed}` |
| `authzStep` | handle, request JSON | `{ok, response, changed?}`, `{ok, fetch: {url, accept, address}}` or `{ok, resolve: {host}}` |
| `authzFetched` | handle, `{url, status, body, now}` or `{host, addresses}` | `{ok}` |
| `authzKeys` | handle, `{nonce?, private?}` | `{ok, keys}` (the file document) or `{ok, jwks}` with private keys, for the test harness only |
| `authzRotate` | handle, `{now, random}` | `{ok, changed, kid}` |
| `authzClose` | handle | `{ok}` |

The request carries `now` (seconds) and `random` (base64, 112 bytes: two
nonce candidates, a key candidate, a `jti`). The host passes data only.

## Touchstone

`tools/lws-touchstone.sh --authz factoidal` runs the `auth` and alternative
configurations with OUR authorization server in place of Touchstone's
reference one (default `--authz touchstone` is unchanged). The harness gets
our current private key as `as.signingKey` (from `factoidal authz-keys DIR
--private`) so its storage tests mint tokens as before, and the tests of
`core/authorization_server` and `auth/*` reach our token endpoint.
