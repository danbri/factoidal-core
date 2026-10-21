# LWS server against Touchstone, 2026-10-21

A third-party conformance run of `factoidal lws-serve` (core `main`
f89c9910) with Touchstone, the Linked Web Storage conformance harness of
<https://github.com/ebremer/touchstone> at commit
106087234aed2aab3f6bbf0485bd64095cc00fe5 (221 test definitions, format
0.14.0, which follows the LWS drafts of 19 October 2026). Spec text below is
quoted from the w3c/lws-protocol clone at 9a08ff65 and from RFC 9110.
Tracking: https://github.com/danbri/factoidal/issues/659.

Repeat the run with `bash tools/lws-touchstone.sh` (official) or
`bash tools/lws-touchstone.sh --shim` (diagnostic, see below). Reports:
`docs/test-results/lws-touchstone-2026-10-21/`.

## Result

Our server runs no Touchstone test. Touchstone first creates a run root
with `POST` to the storage root, with `Link: <https://www.w3.org/ns/lws#Container>; rel="type"`,
`Content-Length: 0` and no `Content-Type`. Our server answers 400
`"POST with content requires a Content-Type header field"`. Touchstone then
stops with exit code 2. This is our defect (failure F1 below), in both
configurations.

To see the rest of the suite, a diagnostic proxy (the "shim") adds
`Content-Type: application/octet-stream` to a POST that has no content and
no `Content-Type`, and changes nothing else. The numbers made through the
shim are diagnostic. They are not a conformance score.

| configuration | tests | passed | failed | cantTell | inapplicable | MUST failures |
|---|---:|---:|---:|---:|---:|---:|
| Touchstone reference server, open (self-check) | 221 | 78 | 0 | 0 | 143 | 0 |
| Touchstone secured reference deployment (self-check) | 221 | 218 | 0 | 0 | 3 | 0 |
| ours, `--insecure-no-auth`, direct | 0 run | - | - | - | - | run root refused (F1) |
| ours, default authorization, direct | 0 run | - | - | - | - | run root refused (F1) |
| ours, `--insecure-no-auth`, through the shim | 221 | 58 | 3 | 0 | 160 | 2 |
| ours, default authorization, through the shim | 221 | 117 | 3 | 0 | 101 | 2 |

Read the shim rows with these corrections:

* Six of the passes in each shim row pass only because the shim changed
  the request under test: the step "create a sub-container" of
  `core/containers#createContainer` (MUST), `#createContainer-type-link`
  (SHOULD), `#contained-resource-type-values` (MUST),
  `#delete-empty-container` (MUST), `#delete-non-empty-container-409`
  (MUST) and `#delete-container-recursive` (MAY). Without the shim they
  fail on F1. Counted that way, the open row is 52 pass, 9 fail, and the
  authorization row is 111 pass, 9 fail; MUST failures 6 and 6.
* In the authorization row, 40 passes test Touchstone's reference
  authorization server, not our storage server. Our server has no
  authorization server; it trusts one (see "Authorization setup"). The
  passes are `core/authorization_server` (9: 8 send requests only to the
  authorization server; `authz-issued-token-accepted-by-storage` also sends
  one GET to our storage), `auth/cid` (22), `auth/oidc` (6) and
  `auth/saml` (3). Without them, the tests that send requests to our
  storage server are 78 pass (72 after the six above), 3 fail.

Two runs of the open configuration through the shim gave the same three
failures. In the authorization run, `delete-updates-parent-strong-etag`
passed, because that run was slower (failure F3 depends on two changes in
the same second).

## Failures

Each entry: the test, the requirement and its level, our request and
response, the spec text, and the diagnosis: (i) our defect, (ii) Touchstone
reads the spec differently from the text, (iii) setup or harness problem.
All failures are (i). No test was found to read the spec differently from
the text.

### (i) Our defects

**F1. POST without content and without Content-Type is refused.**
Tests: none can run (the run root); through the shim, the six tests listed
above depend on it. Requirement: create a container, MUST.

* Request: `POST /` with `Link: <https://www.w3.org/ns/lws#Container>; rel="type"`,
  `Content-Length: 0`, no `Content-Type`.
* Response: `400`, `application/problem+json`,
  `"detail":"POST with content requires a Content-Type header field"`.
* Spec, lws10-core `Operations/create-resource.md`: "To create a
  **Container**, the client MUST include a `Link` header with `rel="type"`
  pointing to the Container type". The example that follows is exactly
  Touchstone's request: `POST /alice/ HTTP/1.1`, `Content-Length: 0`,
  `Link: <https://www.w3.org/ns/lws#Container>; rel="type"`, and no
  `Content-Type`. RFC 9110 §8.3 asks for `Content-Type` only on a message
  that contains content.
* Lean: `L4Factoidal/LWS/Operations.lean`, `step`, case `"POST"` (line 509):
  `match r.header? "content-type" with | none => problem 400 …`. The test is
  on the header alone; the message says "with content" but the code does not
  look at the content.

**F2. The Turtle form of a container uses `https://schema.org/size`.**
Test: `core/containers#container-lws-profile-turtle`. Requirement
`conneg-lws-profile-isomorphic`, MUST.

* Request: `GET` of a container with
  `Accept: text/turtle; profile="https://www.w3.org/ns/lws/v1"`.
* Response: `200`, `Content-Type: text/turtle; profile="https://www.w3.org/ns/lws/v1"`,
  body with `@prefix schema: <https://schema.org/>` and `schema:size "14"^^xsd:long`.
  Touchstone: "not isomorphic: 10 quads against 9; only in this response:
  `<…/res1792595512> <https://schema.org/size> "14"^^xsd:long`; only in the
  other: `<…/res1792595512> <http://schema.org/size> "14"^^xsd:long`".
* Spec, lws10-core `lws-media-type.md` §LWS Profile: "If the server selects
  such a media type, the response MUST conform to the LWS profile, that is,
  it MUST be RDF isomorphic to the `application/lws+json` representation".
  The RDF of the `application/lws+json` form is fixed by the context
  `https://www.w3.org/ns/lws/v1`. That URL answers 404 today; the core
  draft's example of the same container (`container-representation.md`,
  Turtle and N-Triples tabs) gives `@prefix schema: <http://schema.org/>`
  and `<http://schema.org/size>`. Touchstone's copy of the context uses
  `http://schema.org/size` too.
* Upstream inconsistency: `lws10-vocab/vocabulary.yml` in the same
  repository declares `schema: https://schema.org/`. Our Lean followed the
  vocabulary, the core draft and Touchstone follow `http`. Both are W3C LWS
  WG documents; the core draft is the one under test. Raise the conflict
  with the WG.
* Lean: `L4Factoidal/LWS/Binding.lean`, `containerTurtle` (line 485, the
  `@prefix schema:` line).

**F3. A container's entity tag does not change when a member is deleted
in the same second.** Test: `core/conditional_requests#delete-updates-parent-strong-etag`.
Requirements `containment-delete-atomic-items`,
`delete-removes-from-parent-listing`, MUST.

* Requests and responses: `GET` container, `ETag: "1792595514"`, one item;
  `DELETE` the item with `If-Match`, `204`; `GET` container,
  `ETag: "1792595514"`, `"totalItems":0,"items":[]`. Reproduced with curl:
  delete in the same second, same tag; delete two seconds later, new tag.
* Spec: lws10-core `Operations/read-resource.md`: "Responses MUST include
  an `ETag` header as defined in [RFC9110]". RFC 9110 §8.8.1: 'A "strong
  validator" is representation metadata that changes value whenever a
  change occurs to the representation data that would be observable in the
  content of a 200 (OK) response to GET.' The tag has no `W/`, so it is
  strong.
* Lean: `L4Factoidal/LWS/Binding.lean`, `etagFor`: for a container the tag
  is `e.mtime` and a media suffix, and `mtime` is whole seconds under the
  host's real clock (`touchContainer` in `Operations.lean` sets it to
  `S.now st`). A data resource's tag also carries the FNV-1a digest of its
  bytes, so it does not have this defect. The same cause will break
  lws10-core `Operations/moving-resources.md`: "the ETag of both
  containers MUST be updated to reflect the change".

**F4. 401 links the storage to a different IRI from every other response.**
Test: `core/discovery#discovery-unauthorized-response-headers` (authorization
run only; the test requires Authentication). Requirements
`authz-401-storage-link`, `create-401-storage-link`, MUST.

* Request: anonymous `GET /touchstone-run-…/discovery-unauthorized-response-headers/`.
* Response: `401`, `WWW-Authenticate: Bearer resource_metadata="…"`,
  `Link: <http://127.0.0.1:4723/>; rel="https://www.w3.org/ns/lws#storage"`.
  Every 200 response links `<http://127.0.0.1:4723/.well-known/lws-storage>`,
  and the storage description at that URL has
  `"id":"http://127.0.0.1:4723/.well-known/lws-storage"`.
* Spec, lws10-core `Discovery.html`: "`id` … Its value MUST be the canonical
  URI of the storage", and "All responses to GET and HEAD requests targeting
  storage resources MUST include a Link header whose target is the canonical
  URI of the storage". `Authorization.html`: "The response MUST also include
  a Link header identifying the storage that contains the requested
  resource … A client supplies this URI as the resource parameter when
  requesting an access token". A storage has one canonical URI; we give two.
* Lean: `L4Factoidal/LWS/Authorization.lean` line 302 (the 401 `Link` uses
  `cfg.baseIri`) and `storageIri` (line 141: the token audience and the
  protected resource metadata `resource` default to `cfg.baseIri`), against
  `Binding.lean` line 444 (`iriOfPath baseIri storagePath`). The fix must
  move the 401 link, the metadata `resource` and the default audience
  together, because the harness asks for a token with the 401's IRI as
  `resource`.

**F5. `If-Unmodified-Since` is ignored.** Test:
`core/conditional_requests#conditional-get-if-unmodified-since-412`.
Requirement `conditional-requests-supported`, SHOULD (LWS); the RFC rule it
applies is a MUST.

* Request: `GET` of a data resource with
  `If-Unmodified-Since: Thu, 01 Jan 1970 00:00:00 GMT`; its `Last-Modified`
  is `Wed, 21 Oct 2026 15:11:53 GMT`.
* Response: `200` with the content.
* Spec, lws10-core `Operations/read-resource.md`: "Servers SHOULD support
  conditional requests as defined in [RFC9110], including mechanisms such as
  entity tags (`ETags`) and date-based validators". RFC 9110 §13.1.4: "When
  an origin server receives a request that selects a representation and
  that request includes an If-Unmodified-Since header field without an
  If-Match header field, the origin server MUST evaluate the
  If-Unmodified-Since condition … An origin server that evaluates an
  If-Unmodified-Since condition MUST NOT perform the requested method if the
  condition evaluates to false."
* Lean: `L4Factoidal/LWS/Binding.lean`, `preconditionFailure` (line 301) has
  no `if-unmodified-since` branch, for any method, so PUT, PATCH and DELETE
  ignore it too. Seen in the same function, not failed by any Touchstone
  test: `If-Modified-Since` gives 304 only when the field value is the same
  string as `Last-Modified`; RFC 9110 §13.1.3 compares dates.

### (ii) Touchstone reads the spec differently from the text

None found.

### (iii) Setup or harness problems

None caused a failure. Two setup choices change which tests apply:

* The shim (see "Result"). It changes only POSTs with no content and no
  `Content-Type`; `run.json` shows the six test steps it changed.
* Pagination: our page size is 100 (`Config.pageSize` in
  `L4Factoidal/LWS/Operations.lean`) and `lws-serve` has no flag for it, so
  the four pagination tests, which page a five-member container, are
  inapplicable.

## Inapplicable tests (features we do not offer)

Inapplicable is not a pass and not a fail. Through the shim, the
authorization run has 101: index services (40: no Type Index or Type
Search Service), access grants (17: no AccessGrantService), notifications
(15 core and 11 webhook: no NotificationService), moving resources (11: 10
because we describe no `MoveResource` capability, 1 that is inapplicable on
the reference too; the test that a storage without the capability refuses a
move passes), pagination (5: the 4 above, and 1 that is inapplicable on the
reference too),
`linkset-put-405-when-unsupported` (1: we support PUT on the linkset),
`storage-root-same-origin` (1: under authorization an anonymous client
cannot read our storage description, and the test needs that), and
`core/discovery` items that need Authentication in the open run. Several of
these drafts' features are tracked in
https://github.com/danbri/factoidal/issues/890 (notifications).

## Authorization setup (configuration b)

Our server is told which issuers to trust with `--issuer IRI` (or
`--auth-config FILE`); it then fetches `<issuer>/.well-known/lws-configuration`
and the `jwks_uri` it names (`skills/lws-solid/SKILL.md`, "LWS
authorization"). Touchstone's `HarnessIssuedTokens` capability needs a
storage that trusts an authorization server whose signing key the harness
holds. `tools/lws-touchstone.sh` therefore:

1. starts Touchstone's `RefAuthorizationServer` (from `harness-fixtures`)
   on a free port, registers our storage IRI as a resource it issues tokens
   for, and writes a target registry with its private key as
   `as.signingKey`, a SAML identity provider key as `saml.idpKey`,
   `webid.alice` and `webid.bob` on the harness fixture host, and the
   capabilities `Authentication`, `HarnessIssuedTokens`,
   `ReachableFixtures`, `SamlTrust`;
2. starts `factoidal lws-serve DIR --issuer http://localhost:<as-port> --owner <alice's WebID>`,
   so the new storage's root ACL gives alice Read, Write and Control and bob
   nothing.

Every harness-minted token (RFC 9068, RS256, `typ: at+jwt`) was accepted or
refused as the storage-authorization tests expect: `core/storage_authorization`
18 pass, 0 fail (expired, not yet valid, issued in the future, wrong
audience, two audiences, wrong issuer, corrupted signature, unknown key,
`alg: none`, the 401 challenge, owner and non-owner).

## Run details

* Host: Linux, OpenJDK 21.0.12, Maven 3.9.11, Node 22.22.0. No Docker
  daemon, so Touchstone's `targetservers/run-all.sh` was not used.
* Touchstone was built from a copy of the clone
  (`mvn -B -q clean install -DskipTests`, 255 MB of Maven downloads through
  the session proxy, no settings change needed).
* Report directories: `docs/test-results/lws-touchstone-2026-10-21/open-insecure-no-auth/`
  (run f3d59a86) and `…/default-authorization/` (run 5d0229bf), each with
  `report.md`, `report.json`, `earl.ttl`, and `unshimmed-run.txt` (the
  Touchstone output of the direct run). The self-check reports were not
  copied; they contain the throwaway tokens of the reference servers.
