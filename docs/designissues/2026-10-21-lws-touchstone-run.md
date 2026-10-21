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

This section and "Failures" describe the first run. After the repairs, both
configurations run every test with no failure: see "Rerun after fixes".

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

## Rerun after fixes

Rerun 2026-10-21 on branch `claude/wt-lws911` (the repairs of
https://github.com/danbri/factoidal/issues/911, merged with `main` at
6ef53014, which adds the notifications of
https://github.com/danbri/factoidal/issues/890), with
`bash tools/lws-touchstone.sh --config both` (no `--shim`), Touchstone at
the same pinned commit 106087234aed2aab3f6bbf0485bd64095cc00fe5. The
script now starts `lws-serve` with `--page-size 4` (`LWS_PAGE_SIZE`), so
the pagination tests apply. Reports:
`docs/test-results/lws-touchstone-2026-10-21-rerun/` (`report.md` and
`earl.ttl` per configuration, `run.txt` the script output).

| configuration | tests | passed | failed | cantTell | inapplicable | MUST failures |
|---|---:|---:|---:|---:|---:|---:|
| ours, `--insecure-no-auth`, direct | 221 | 70 | 0 | 0 | 151 | 0 |
| ours, default authorization, direct | 221 | 146 | 0 | 0 | 75 | 0 |

The script exits 0. Touchstone's report says CONFORMANT for both. In the
authorization row, 40 passes test Touchstone's reference authorization
server (`core/authorization_server` 9, `auth/cid` 22, `auth/oidc` 6,
`auth/saml` 3), as before; the tests that send requests to our storage
server are 106 pass, 0 fail. The same branch before the merge (no
notifications) gave open 65 pass, 0 fail, 156 inapplicable and
authorization 125 pass, 0 fail, 96 inapplicable (out of 221 each).

What changed, per failure (all in `formal/lean4/L4Factoidal/LWS/`):

| failure | repair | `#guard` (Tests.lean, AuthorizationTests.lean) | host check (`tests/lws/`) |
|---|---|---|---|
| F1, POST without content and Content-Type | `Operations.writeMediaType`: no content and no `Content-Type` stores an empty container (`text/turtle`) or an empty data resource (`application/octet-stream`); content without `Content-Type` stays 400. Applies to PUT too. | `lwsGuardPostWithoutContent` and three negatives | draft-binding "Create: POST with no content" (2) |
| F2, `https://schema.org/size` | `Binding.containerTurtle`: `schema:` is `http://schema.org/`. The comment names `lws10-core/container-representation.md`, `lws10-core/Operations/read-resource.md`, the 2026-07-14 vocabulary snapshot and `lws10-vocab/vocabulary.yml` (which says `https://`). | `lwsGuardTurtleSchemaNamespace` and a negative | draft-binding "LWS Profile" |
| F3, container ETag in one second | `Binding.containerTag`, `Operations.tagIn`/`tagsIn`: the clock, the media suffix and the FNV-1a digest of the listing. `Last-Modified` unchanged. | `lwsGuardContainerTagSameSecond`, two more | draft-binding "Read: a container ETag changes ... same second" |
| F4, two storage IRIs | `Authorization.storageIri` defaults to the storage description IRI `<base>.well-known/lws-storage`; the 401 `Link` uses it. The protected resource metadata `resource` stays the requested resource: `Authorization.html`, "The resource value in a protected resource metadata document identifies the requested resource, not the storage that contains it". | `storageIri` guards; a token for `<base>` is refused | authorization.mjs (2 new); draft-binding "Authorization: the 401 lws#storage link" |
| F5, If-Unmodified-Since | `HttpDate.lean` (new): civil dates both ways and `parseHttpDate` for IMF-fixdate, rfc850-date and asctime-date; `Binding.preconditionFailure` evaluates If-Unmodified-Since for every method and If-Modified-Since as an instant, in the order of RFC 9110 §13.2.2. Theorems `eraDaysOfCivil_civilOfDays` and `unixOfCivil_civilOfUnix`: every `Last-Modified` the server formats parses back to its instant. | `lwsGuardIfUnmodifiedSince`, three more; 23 guards in `HttpDate.lean` | draft-binding "Conditional requests" (2) |

The first rerun after F1 to F5 gave open 60 pass, 1 fail, 160
inapplicable and authorization 120 pass, 1 fail, 100 inapplicable (out of
221 each): `core/containers#container-lws-profile-turtle` failed again, and
the pagination tests were still inapplicable. It found two more defects,
repaired before the run in the table above:

* **F6. A POST could replace another resource.** `childPathFor` gave a
  clashing name one suffix, the clock, on the assumption that the clock
  never repeats. Under a host's real clock it repeats within a second: the
  pagination prerequisites POST five members in one second, the first got
  `res<t>`, the second `res<t>-<t>`, and the third, fourth and fifth were
  written OVER the second (two members, not five). lws10-core
  `Operations/create-resource.md`: the server assigns the name "while
  ensuring uniqueness and validity within the container". Repair:
  `Operations.freeName` tries `name`, `name-1`, `name-2`, ... (one more
  candidate than the store has paths); theorem `childPathFor_fresh`: the
  assigned path holds nothing. Guard `lwsGuardPostSameSecondUnique`; host
  check draft-binding "Create: five POSTs to one container in one second".
* **F2, second part.** The Turtle form gave a contained container
  `dcterms:modified`. The vocabulary gives `dcterms:modified` the domain
  `lws:DataResource`, so the context defines `modified` only in the
  type-scoped context of `DataResource`, and a `Container` item's
  `modified` member maps to no triple (Touchstone: "10 quads against 9;
  only in this response: `<…/inner/> dcterms:modified …`"). The Turtle form
  now leaves it out for a contained container; the JSON item keeps
  `modified` (§Contained Resource Description, SHOULD).

Remaining failures: none in either configuration.

Inapplicable tests (inapplicable is not a pass and not a fail):

* default authorization, 75: index services (40), access grants (17),
  moving resources (11: we describe no `MoveResource` capability),
  notifications (4 core, 1 webhook: each first grants bob read access
  through an AccessGrantService, which we do not offer,
  https://github.com/danbri/factoidal/issues/913),
  `linkset-put-405-when-unsupported` (1: we support PUT on the linkset),
  `pagination-single-page` (1: it applies only to a server that does NOT
  split a five-member container, and the four multi-page tests apply only
  to one that does).
* open, 151: the same 70 without the notification five, plus 81 tests
  whose target capabilities the open configuration does not declare:
  `Authentication` (`core/storage_authorization` 19,
  `core/authorization_server` 9, `auth/*` 31, `core/discovery` 1) and
  `ReachableFixtures` or `Authentication` (notifications, 10 core and 11
  webhook).

Gates on the merged branch: full `lake build` exit 0 (1774 jobs);
`tools/lean-unbuilt-modules.py --gate` 817 of 817 modules reached;
`Wasm/native-smoke.sh` 375 pass, 0 fail (out of 375); `npm test` 536
pass, 0 fail, 2 skipped (out of 538); `tests/lws/server.mjs` 8 pass,
0 fail (out of 8); `authorization.mjs` 21 pass, 0 fail (out of 21);
`binary-bodies.mjs` 20 pass, 0 fail (out of 20); `draft-binding.mjs` 43
pass, 0 fail, 1 xfail (out of 44; the xfail is
https://github.com/danbri/factoidal/issues/913); `scaling.mjs` 6 pass,
0 fail (out of 6); `tests/solid/server/protocol.mjs` 12 pass, 0 fail (out of 12);
`tests/solid/client/against-own-server.mjs` 7 pass, 0 fail (out of 7);
`tests/solid/server/oidc.mjs` 21 pass, 0 fail (out of 21);
`tools/solid-server-interop.sh` solid-crud-tests 27 pass, 0 fail, 8
expected fail, 41 skipped (out of 76), web-access-control-tests not run
(exit 2, external OIDC, as before); `tools/host-purity-lint.sh` 35 pass,
0 fail (out of 35).

## Moving resources (issue 914)

Run 2026-10-21 on branch `claude/wt-lws914` (moving resources,
https://github.com/danbri/factoidal/issues/914, merged with the issue 911
branch at a5daa19c), `bash tools/lws-touchstone.sh --config both`, no
`--shim`, same Touchstone commit. The script exits 0.

| configuration | tests | passed | failed | cantTell | inapplicable |
|---|---:|---:|---:|---:|---:|
| ours, `--insecure-no-auth`, direct | 221 | 75 | 0 | 0 | 146 |
| ours, default authorization, direct | 221 | 152 | 0 | 0 | 69 |

`core/moving` (11 tests): open 6 pass, 0 fail, 5 inapplicable;
authorization 7 pass, 0 fail, 4 inapplicable (out of 11 each). Passed:
`discovery-move-capability`, `move-data-resource`,
`move-updates-container-etags`, `move-invalid-destination-refused`,
`move-container`, `move-container-into-itself-refused`, and in the
authorization run `move-notification` (it needs `ReachableFixtures`, which
the open run does not declare). Inapplicable in both:

* three tests whose preconditions exclude one another, so no one server
  applies all three: `move-keeps-identifier-content-and-links` needs
  `preservesIdentifier: true` (our identifiers are paths, so a moved
  resource gets a new one and we say `false`);
  `move-container-refused-without-container-support` needs a capability
  WITHOUT `Container` in `appliesTo` (we move containers);
  `move-refused-without-capability` needs NO capability.
* `move-needs-create-in-destination` and `move-needs-delete-of-resource`:
  their prerequisites grant bob access through an AccessGrantService
  (https://github.com/danbri/factoidal/issues/913), and Touchstone's `env`
  provisioning adapter cannot grant access out of band. The rule they test
  is in `Authorization.decide` and is checked by `MoveTests.lean`
  "Authorization" (allowed, 403 without create in the destination, 403
  without delete of the resource or of one resource of a moved subtree).

## Type index and type search (issue 912)

Run 2026-10-21 on branch `claude/wt-lws912` (the Type Index and Type Search
services, https://github.com/danbri/factoidal/issues/912, merged with the
moving-resources branch `claude/wt-lws914` and with `main` at 0f7e25a3),
`bash tools/lws-touchstone.sh --config both`, no `--shim`, same Touchstone
commit. The script exits 0. Reports:
`docs/test-results/lws-touchstone-2026-10-21-index/` (`report.md` and
`earl.ttl` per configuration, `run.txt` the script output).

| configuration | tests | passed | failed | cantTell | inapplicable |
|---|---:|---:|---:|---:|---:|
| ours, `--insecure-no-auth`, direct | 221 | 75 | 0 | 0 | 146 |
| ours, default authorization, direct | 221 | 186 | 0 | 0 | 35 |

`index/manifest` (40 tests): open 0 pass, 0 fail, 40 inapplicable (every
test requires `Authentication`, which the open configuration does not
declare); authorization 34 pass, 0 fail, 6 inapplicable (out of 40 each).
Inapplicable under authorization:

* `type-index-lists-readable-types`, `type-index-omits-unreadable-type`,
  `type-search-authorization-filtered` (prerequisite grants bob read access),
  `type-search-revoked-not-shown`, `type-search-content-types-identical`
  (a step POSTs to the AccessGrantService): access grants,
  https://github.com/danbri/factoidal/issues/913. The rules they test are
  checked with Web Access Control in place of a grant:
  `L4Factoidal/LWS/SearchTests.lean` "Authorization" and
  `tests/lws/authorization.mjs` "Type search: results, totalItems and the
  type index ...".
* `type-search-content-location-protected`: applies only when a search
  answer carries `Content-Location`. lws10-index §QUERY: "this
  specification does not define such a resource"; this server sends none.

Spec and test text read together, no disagreement found between a test and
the draft. One tension between two drafts, which the test
`type-search-reflects-update` exercises: lws10-core §Metadata lists `type`
as "System Managed; Read-Only", and lws10-index §Type and Relation
Derivation says "servers SHOULD derive resource types from HTTP Link headers
provided by the client during resource creation or modification". The
reading used here, and the draft issue text, are in
`docs/designissues/2026-10-21-lws-draft-inconsistencies.md` (Issue 2).

## Access requests and grants (issue 913)

Run 2026-10-21 on branch `claude/wt-lws913` (access requests and grants,
https://github.com/danbri/factoidal/issues/913, merged with the type index
branch `claude/wt-lws912` at a7a00af9), `bash tools/lws-touchstone.sh
--config both`, no `--shim`, same Touchstone commit. The script exits 0.
Reports: `docs/test-results/lws-touchstone-2026-10-21-access/` (`report.md`
and `earl.ttl` per configuration, `run.txt` the script output).

| configuration | tests | passed | failed | cantTell | inapplicable |
|---|---:|---:|---:|---:|---:|
| ours, `--insecure-no-auth`, direct | 221 | 76 | 0 | 0 | 145 |
| ours, default authorization, direct | 221 | 215 | 0 | 0 | 6 |

In the authorization row, 40 passes test Touchstone's reference
authorization server, as before; the tests that send requests to our storage
server are 175 pass, 0 fail.

Per definition file (out of the file's test count, both configurations):

| file | open | authorization |
|---|---|---|
| `core/access_grants` (17) | 1 pass, 0 fail, 16 inapplicable | 17 pass, 0 fail, 0 inapplicable |
| `core/notifications` (15) | 5 pass, 0 fail, 10 inapplicable | 15 pass, 0 fail, 0 inapplicable |
| `notifications/webhook` (11) | 0 pass, 0 fail, 11 inapplicable | 11 pass, 0 fail, 0 inapplicable |
| `index` (40) | 0 pass, 0 fail, 40 inapplicable | 39 pass, 0 fail, 1 inapplicable |
| `core/moving` (12) | 6 pass, 0 fail, 6 inapplicable | 9 pass, 0 fail, 3 inapplicable |

What became applicable: every test whose prerequisite grants bob (or the
public) access through the AccessGrantService. Before this branch, under
authorization: access grants 17 inapplicable; the five index tests
`type-index-lists-readable-types`, `type-index-omits-unreadable-type`,
`type-search-authorization-filtered`, `type-search-revoked-not-shown`,
`type-search-content-types-identical`; the five notification tests
`subscription-unreadable-topic-refused`, `subscription-after-revocation-refused`,
`notification-not-delivered-for-unreadable-resource`,
`notification-stops-after-revocation` and the webhook test
`webhook-subscription-listed`; and the two moving tests
`move-needs-create-in-destination`, `move-needs-delete-of-resource`. All
pass.

The open configuration declares no `Authentication`, so 16 of the 17
access-grant tests are inapplicable there by Touchstone's own rule
(EXECUTION.md §4.2 item 1); `access-grant-endpoint-is-container` needs no
token and passes.

The six inapplicable tests under authorization are the same as before
except that no access-grant test remains: `linkset-put-405-when-unsupported`
(we support PUT on the linkset), `pagination-single-page` (applies only to a
server that does not page a five-member container), the three moving tests
whose preconditions exclude one another (§ Moving resources), and
`type-search-content-location-protected` (§ Type index and type search; it applies and passes with the unstable option of § Search results resource).

How each test is met (all in `formal/lean4/L4Factoidal/LWS/`):

* Discovery and the endpoints (`access-grant-endpoint-is-container`,
  `access-grant-create`, `access-request-create`, `access-grant-document-shape`):
  `Binding.storageDescription` with `conformsTo` the Access Profile;
  `AccessGrants.accessStep`; the served document is the posted one with
  `@context` as an array and `id` added.
* Validation (`access-grant-incomplete-refused`,
  `access-grant-extra-properties-accepted`, `access-grant-left-operands-accepted`):
  `AccessPolicy.parseDoc`. The draft gives no status for a document that
  breaks a MUST; we answer 400, which the test accepts as `4xx`.
* Enforcement (`access-grant-authenticated-agent`, `access-grant-revoke`,
  `getContainer-public-read`, `readDataResource-public-read`, the constraint
  tests, `container-listing-filtered-metadata`): `AccessPolicy.grantAllows`
  in `Authorization.decide`. The `client` constraint compares the token's
  `client_id` (RFC 9068 §2.2), which the Touchstone harness sets to its own
  client.
* `access-grant-inbox-notified`: `AccessGrants.announce`, one `Create`
  notification to the grant's `inbox`.

Spec and test text read together: no disagreement between a test and the
draft was found. Three points where the draft is silent and the test and
this server agree: the draft does not say whether a grant on a container
reaches its members (Touchstone's `readDataResource-public-read` comment;
here it does not); it gives no status for a malformed grant (here 400); and
it gives a request no way to state a `purpose` (Touchstone tests only that a
`purpose` constraint is accepted; here no request satisfies one). One SHOULD
is not done: "Access Request creation: When a new access request is
submitted, the storage controller SHOULD be notified", because the draft
names no inbox for the controller
(https://github.com/danbri/factoidal/issues/920, an xfail in
`tests/lws/draft-binding.mjs`); no Touchstone test covers it.

Gates on the branch (after the merge of `claude/wt-lws912`): full `lake
build` exit 0 (1788 jobs); `tools/lean-unbuilt-modules.py --gate` 825 of 825
modules reached; `Wasm/native-smoke.sh` 375 pass, 0 fail (out of 375);
`npm test` 536 pass, 0 fail, 2 skipped (out of 538); `tests/lws/server.mjs`
8 pass, 0 fail (out of 8); `authorization.mjs` 28 pass, 0 fail (out of 28);
`binary-bodies.mjs` 20 pass, 0 fail (out of 20); `draft-binding.mjs` 64
pass, 0 fail, 4 xfail (out of 68); `scaling.mjs` 12 pass, 0 fail (out of
12); `tests/solid/server/protocol.mjs` 12 pass, 0 fail (out of 12);
`tests/solid/server/oidc.mjs` 21 pass, 0 fail (out of 21);
`tests/solid/client/against-own-server.mjs` 7 pass, 0 fail (out of 7);
`tools/host-purity-lint.sh` 35 pass, 0 fail (out of 35); `lake exe
l4lws-probe` guarded checks 17 pass, 0 fail (out of 17).

## Search results resource (issue 922, ANTICIPATORY AND UNSTABLE)

Run 2026-10-21 on branch `claude/wt-lws922` (merged with the encryption at
rest branch `claude/wt-lws921` at aea19bf7), no `--shim`, same Touchstone
commit. Reports: `docs/test-results/lws-touchstone-2026-10-21-results/`
(`report.md` and `earl.ttl` per configuration with the option on;
`run.txt` and `run-default.txt` the script output).

Owner, 2026-10-21: "what do we think a Content-Location results resource
looks like? Can we draft an anticipatory impl flagged as likely unstable?"
lws10-index defines no such resource; `L4Factoidal/LWS/SearchResults.lean`
implements one, off by default. The design and the RFC 10008 text it follows
are in `docs/lws-solid-conformance.md` § Search results resource.

| configuration | tests | passed | failed | cantTell | inapplicable |
|---|---:|---:|---:|---:|---:|
| ours, `--insecure-no-auth`, default (`bash tools/lws-touchstone.sh`) | 221 | 76 | 0 | 0 | 145 |
| ours, default authorization, default | 221 | 215 | 0 | 0 | 6 |
| ours, `--insecure-no-auth`, `--unstable-search-results` | 221 | 76 | 0 | 0 | 145 |
| ours, default authorization, `--unstable-search-results` | 221 | 216 | 0 | 0 | 5 |

Both default runs are the same as § Access requests and grants: the option
is off by default, and with it off every request passes to the storage as
before (theorem `SearchResults.serverStep_off`). Both runs exit 0.

With the option on, `index/manifest#type-search-content-location-protected`
(MUST, status Proposed) applies under authorization and passes: alice's QUERY
answer carries `Content-Location`, and bob's GET of that URL answers 404 with
no part of her result. In the open configuration it stays inapplicable (it
requires Authentication). The five tests still inapplicable under
authorization are `linkset-put-405-when-unsupported`,
`pagination-single-page` and the three moving tests whose preconditions
exclude one another.

Test text and RFC text read together. The test accepts a refusal, an empty
answer or a filtered page for bob; this server refuses (404), because a
results resource answers only the agent and client that made it. The test
does not check the creator's GET; `tests/lws/authorization.mjs` does (200
for alice, 404 for another client of alice, 404 anonymous, 410 after the
lifetime).

Script defect found on the way: with a reused `TOUCHSTONE_WORK`, the second
`--config auth` run read the previous run's `targets-auth.yaml` and stopped
with "unknown target 'factoidal-auth-unstable'" (exit 2). The script now
removes `as.log` and `targets-auth.yaml` before the authorization server
starts.

Gates on the branch (after the merge of `claude/wt-lws921`): full `lake
build` exit 0; `tools/lean-unbuilt-modules.py --gate` 829 of 829 modules
reached; `Wasm/native-smoke.sh` 375 pass, 0 fail (out of 375); `npm test`
536 pass, 0 fail, 2 skipped (out of 538); `tests/lws/authorization.mjs` 29
pass, 0 fail (out of 29); `binary-bodies.mjs` 20 pass, 0 fail (out of 20);
`draft-binding.mjs` 69 pass, 0 fail, 4 xfail (out of 73); `encryption.mjs`
28 pass, 0 fail (out of 28); `scaling.mjs` 12 pass, 0 fail (out of 12);
`server.mjs` 8 pass, 0 fail (out of 8); `tests/solid/server/protocol.mjs` 12
pass, 0 fail (out of 12); `tests/solid/server/oidc.mjs` 21 pass, 0 fail (out
of 21); `tests/solid/client/against-own-server.mjs` 7 pass, 0 fail (out of
7); `tools/host-purity-lint.sh` 35 pass, 0 fail (out of 35); `lake exe
l4lws-probe` guarded checks 17 pass, 0 fail (out of 17), registry 11 proved,
17 guarded, 0 host-verified, 5 open (out of 33).

## Alternative configurations: every test one configuration can satisfy

Owner, 2026-10-21: "full Touchstone conformance asap please". Run 2026-10-21
on branch `claude/wt-lwsalt` (from `main` 5e17bb90), same Touchstone commit,
no `--shim`. Reports: `docs/test-results/lws-touchstone-2026-10-21-alt/`
(`report.md` and `earl.ttl` per configuration, `union.tsv` one row per
test, `run-all.txt` and `run-default.txt` the script output).

After § Search results resource, five tests were inapplicable under
authorization. Their preconditions exclude one another, so no one server
configuration applies all of them. The default server is not changed. Three
server options were added, each decided in Lean configuration
(`L4Factoidal/LWS/Operations.lean` `Config`, parsed in `Wasm/Ops/Lws.lean`)
and exposed as an `lws-serve` flag, and `tools/lws-touchstone.sh` runs one
more configuration per option, each with authorization on:

| configuration | `lws-serve` flags | the test it makes apply | precondition (Touchstone text) |
|---|---|---|---|
| `alt-nomove` | `--moves off` (config `moves: false`, which existed) | `core/moving#move-refused-without-capability` | "the storage describes no MoveResource capability" |
| `alt-datamove` | `--moves data` (`Config.moveContainers` false) | `core/moving#move-container-refused-without-container-support` | "the storage moves data resources but not containers": `appliesTo` without `Container` |
| `alt-linkset-noput` | `--no-linkset-put` (`Config.linksetPut` false) | `core/linksets#linkset-put-405-when-unsupported` | "the linkset does not advertise PUT": `Allow` without PUT |
| `alt-onepage` | `--page-size 100 --paginate-always` (`Config.paginateAlways`) | `core/pagination#pagination-single-page` | "the listing is paginated and holds all five members on its page": `rel="first"` and `/items/4` |

What each option does, with the spec text:

* `--moves data`: lws10-core `Operations/moving-resources.md`, "A server
  that supports moving data resources but not containers MUST reject such a
  request with an appropriate 4xx status code, such as 409 Conflict, and
  MUST NOT include Container in the `appliesTo` property." The capability's
  `appliesTo` is `["DataResource"]`; a change of a container's `up` link
  answers 409 and moves nothing (`Move.movable`, used by the linkset
  operation and by `movePlanOf?` in `Authorization.decide`).
* `--no-linkset-put`: lws10-core `Operations/metadata.md`, "Servers MAY
  support PUT or alternative patch formats; if supported, these MUST be
  included in the Allow and Accept-Patch headers respectively" and
  "Replacement (PUT): If advertised in the Allow header, a client MAY replace
  the entire linkset. If the server does not support PUT, it MUST reject the
  request with 405 Method Not Allowed." `Allow` is `GET, HEAD, OPTIONS,
  PATCH`; a PUT answers 405 with that `Allow` and changes nothing
  (`Operations.linksetAllow`, `linksetStep`).
* `--paginate-always`: our default paginates only above the page size
  (`Pagination.paginated`), so a page size of 5 or more gives the
  five-member container no `rel="first"` and the test stays inapplicable; a
  page size flag alone cannot make it apply. With the option, a listing that
  fits on one page is one paginated page: `rel="first"` and `rel="last"`
  ("MUST be present on paginated responses"), no `rel="next"` ("MUST be
  omitted on the last page") and no `rel="prev"` ("MUST be omitted on the
  first page") (`Pagination.paginatedWith`, theorems `paginatedWith_false`
  and `pageCount_le_one`).

One defect found on the way and repaired for every configuration: on a
paginated container, `If-Match` with the `ETag` of its first page failed
with 412, because `tagsIn` held only the unpaged listing tags while a GET of
the container URI answers the first page with a page tag. Touchstone's
`ifMatch: current` reads that tag before a conditional DELETE, so
`alt-onepage` would have failed the conditional container deletes. RFC 9110
§13.1.1 compares `If-Match` with "the current representation of the target
resource", which is that page. `tagsIn` now also holds the first page's
tags (`Operations.pageTag`); a stale tag still answers 412 (guards in
`PaginationLinksTests.lean`). The default runs did not reach it: no
conditional write there targets a container with more than 4 members.

`bash tools/lws-touchstone.sh --config all --unstable-search-results`
(exit 0):

| configuration | tests | passed | failed | cantTell | inapplicable |
|---|---:|---:|---:|---:|---:|
| `open` (`--insecure-no-auth`) | 221 | 76 | 0 | 0 | 145 |
| `auth` (authorization on) | 221 | 216 | 0 | 0 | 5 |
| `alt-nomove` | 221 | 208 | 0 | 0 | 13 |
| `alt-datamove` | 221 | 215 | 0 | 0 | 6 |
| `alt-linkset-noput` | 221 | 217 | 0 | 0 | 4 |
| `alt-onepage` | 221 | 212 | 0 | 0 | 9 |

Union over the six configurations (out of 221 tests):

| union verdict | tests |
|---|---:|
| passed in at least one configuration | 220 |
| failed in any configuration | 0 |
| cantTell only | 0 |
| never applied | 1 |

Each alternative configuration adds exactly its test, and loses only tests
whose precondition it negates: `alt-nomove` loses the 9 `core/moving` tests
that need a `MoveResource` capability; `alt-datamove` loses `move-container`
and `move-container-into-itself-refused`; `alt-onepage` loses the four
multi-page pagination tests and `index/manifest#type-search-next-page` (it
"Applies when the server's page holds fewer than five"; at page size 100 a
search answer of five is one page). Each authorization configuration holds
the same 40 passes that test Touchstone's reference authorization server,
as before (§ Rerun after fixes).

The default `bash tools/lws-touchstone.sh` (`--config both`, no option) is
unchanged: open 76 pass, 0 fail, 0 cantTell, 145 inapplicable; authorization
215 pass, 0 fail, 0 cantTell, 6 inapplicable (out of 221 each), as in § Search
results resource. Exit 0.

Gates on the branch (`origin/main` had not moved from 5e17bb90): full `lake
build` exit 0 (1796 jobs); `tools/lean-unbuilt-modules.py --gate` 829 of 829
modules reached; `Wasm/native-smoke.sh` 375 pass, 0 fail (out of 375); `npm
test` 536 pass, 0 fail, 2 skipped (out of 538; a first run under load average
23 failed the timing test `dataset-iterate-speed`, which passed alone twice
and in the full rerun); `tests/lws/server.mjs` 8 pass, 0 fail (out of 8);
`authorization.mjs` 29 pass, 0 fail (out of 29); `binary-bodies.mjs` 20
pass, 0 fail (out of 20); `draft-binding.mjs` 73 pass, 0 fail, 4 xfail (out
of 77; 4 new host checks for the three options); `encryption.mjs` 28 pass, 0
fail (out of 28); `scaling.mjs` 12 pass, 0 fail (out of 12);
`tests/solid/server/protocol.mjs` 12 pass, 0 fail (out of 12);
`tests/solid/server/oidc.mjs` 21 pass, 0 fail (out of 21);
`tests/solid/client/against-own-server.mjs` 7 pass, 0 fail (out of 7);
`tools/host-purity-lint.sh` 35 pass, 0 fail (out of 35).

### The one test that never applies: `move-keeps-identifier-content-and-links`

Its precondition: "the storage's MoveResource says it preserves identifiers
(otherwise this test does not apply)", that is `"preservesIdentifier":
true`. lws10-core `Discovery.html`, §Storage Capabilities:
"`preservesIdentifier` - the `preservesIdentifier` property is OPTIONAL. If
present, its value MUST be a boolean indicating whether the storage
preserves the identifier of a moved resource. If the property is absent,
clients MUST NOT assume that identifiers are preserved, and MUST rely on the
response to the update to determine the identifier of the resource."
`Operations/moving-resources.md`: "Servers SHOULD therefore preserve the
identifier of a moved resource [...] A server that derives identifiers from
the containment hierarchy, and that therefore advertises
`"preservesIdentifier": false`, cannot preserve the identifier."

Our identifiers are paths, and a resource's path is its parent's path and
its name (`L4Factoidal/LWS/Model.lean`), so this server is the second kind:
it advertises `"preservesIdentifier": false` and answers a move with 200,
the new linkset and `Content-Location`, as the draft requires of such a
server. The test is not applicable to this design. Identifiers are not
redesigned for it; that would be a change of the resource model, not a
configuration. The SHOULD itself (preserve the identifier) is not met; its
neighbour, 301 from the previous identifier, is the open expected failure
of https://github.com/danbri/factoidal/issues/914 in
`tests/lws/draft-binding.mjs`.

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
