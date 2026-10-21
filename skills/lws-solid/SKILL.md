---
name: lws-solid
description: Run, test and extend Factoidal's Linked Web Storage 1.0 and Solid Protocol support - the Node hosts, the wasm ABI they call, the host test suites, the three community interop scripts and the conformance ledger. Use when serving a storage, driving a Solid client, adding a protocol rule, or reading a score from one of these suites.
---

# Linked Web Storage 1.0 and the Solid Protocol

Two standards, one engine, four hosts.

* **LWS 1.0 core** — <https://w3c.github.io/lws-protocol/lws10-core/>,
  W3C Linked Web Storage Working Group editor's draft. Its HTTP bindings
  and status codes are still headings with no content, and it defines no
  test suite.
* **Solid Protocol v0.11.0** — <https://solidproject.org/TR/protocol>.
  It has an HTTP binding, two conformance classes (server and client) and
  three community test suites.

Solid defers to LWS **in the engine**: `Solid/Server/*` instantiates
`LWS.Store` and refines `LWS.Operations.step`. Where the LWS draft is
still "todo", the Solid binding is used and the ledger row says so, so
the day LWS fixes its binding the row is the difference.

Read first:

* design record —
  [`docs/designissues/2026-09-06-lws-and-solid-protocols.md`](../../docs/designissues/2026-09-06-lws-and-solid-protocols.md)
* conformance ledger —
  [`docs/lws-solid-conformance.md`](../../docs/lws-solid-conformance.md);
  its "wasm ABI" section is the contract every host codes against, and
  its "host tests" section says what each host test covers
* tracking issue — <https://github.com/danbri/factoidal/issues/659>

## Where each piece lives

| path | what it is |
| --- | --- |
| `formal/lean4/L4Factoidal/LWS/` | the LWS resource model, store, operations, patch, discovery, conformance registry |
| `formal/lean4/L4Factoidal/Solid/Server/` | storage, containment, auxiliaries, methods, N3 Patch, WAC, CORS, LDN |
| `formal/lean4/L4Factoidal/Solid/Client/` | discovery, request building, response interpretation, WebID profile |
| `formal/lean4/Wasm/Ops/Lws.lean`, `Solid.lean` | the handle ops |
| `npm/factoidal/lws/server.mjs` | Node `http` host over `lwsStep` |
| `npm/factoidal/solid/server/index.mjs` | Node `http` host over `solidStep` |
| `npm/factoidal/solid/client/index.mjs` | `fetch` host over `solidClientRequest`/`solidClientResponse` |
| `tests/lws/`, `tests/solid/server/`, `tests/solid/client/` | the host suites |
| `tools/solid-server-interop.sh`, `solid-client-interop.sh`, `solid-conformance-harness.sh` | the three interop scripts |
| `third_party/testing/solid-crud-tests`, `web-access-control-tests`, `solid-specification-tests` | the community suites, as submodules |

**Iron rule 7 applies without exception.** A host accepts a socket, turns
one request into the ABI's JSON record, calls one op, and writes the
answer back. Any status code, `Link` relation, media type, containment
triple or access decision found in a `.mjs` under `npm/factoidal/lws/` or
`npm/factoidal/solid/` is a rule violation. The only status a host writes
is `500`, for a failure of the host itself.

## Run the servers

```
factoidal lws-serve   DIR (--issuer IRI[,IRI…] | --auth-config FILE | --insecure-no-auth)
                          [--owner WEBID] [--root-acl FILE] [--audience IRI]
                          [--port N] [--host ADDRESS] [--base IRI]
factoidal solid-serve DIR (--issuer IRI[,IRI…] | --auth-config FILE | --insecure-no-auth)
                          [--port N] [--host ADDRESS] [--base IRI] [--owner WEBID]
```

`--port 0` takes an ephemeral port and the command prints the origin it
got on stdout, which is what the interop scripts read.

A third server has the same host contract: `factoidal serve STORE [--port N]
[--host ADDRESS]` serves SPARQL 1.1 Protocol, the Graph Store HTTP Protocol
and the Service Description over an activated Shardborough collection. Its
host (`npm/factoidal/bin/serve.mjs`) carries raw TCP bytes to the
`storeServe*` ops and is in both groups of `tools/host-purity-lint.sh`.
Operating manual, scores and measurements:
[`skills/shardborough-storage/SKILL.md`](../shardborough-storage/SKILL.md)
§ Serving. `--base` sets
`baseIri`, defaulting to the bound origin.

`DIR` names the storage directory. The engine handle holds the storage;
after every step whose envelope says `"changed": true` the host writes
`lwsSnapshot`/`solidSnapshot` to `DIR/lws-state.json` (temporary file,
fsync, rename: `npm/factoidal/lws/persist.mjs`) and reads it back at start.
`L4Factoidal/LWS/Snapshot.lean` decides the format and refuses traversal
paths; request paths with dot segments or encoded traversal get 400
(`validTarget`). Persisting into the Shardborough store is a later step.

The LWS binding of the 2026-10-19 editor's draft (ETag, conditional
requests, ranges, `application/lws+json` listings, linksets, the
`application/lws+cid` storage description at `/.well-known/lws-storage`,
JSON Patch, RFC 9457 errors) is `L4Factoidal/LWS/Binding.lean`; the audit
table is in the ledger, section "LWS editor's draft 2026-10-19 audit", and
`node tests/lws/draft-binding.mjs` is its host suite (with an xfail for
https://github.com/danbri/factoidal/issues/890, notifications).

### Pagination and client links (https://github.com/danbri/factoidal/issues/887, 888)

* `L4Factoidal/LWS/Pagination.lean`: the listing order (increasing path,
  `String` order, each path once: `orderPaths`, theorems `orderPaths_sorted`,
  `orderPaths_nodup`, `mem_orderPaths`) and the pages (`pageAt`,
  `pageCount`, theorem `pages_concat`). `Operations.pagedRead` serves a
  container with more than `Config.pageSize` members (default 100; config
  member `pageSize`, 0 turns it off): page URIs `C?page=N`, `Link` `first`,
  `last`, `next` (not on the last page), `prev` (not on the first), 404 for
  a page that does not exist, `totalItems` over the full membership, an
  `ETag` per page led by the container's clock. Theorem `pageItems_concat`
  in `Operations.lean`: for an unchanged container, pages 1 to
  `memberPageCount` concatenate to `listedMembers`. The draft says nothing
  about change between page requests; the record of that choice is the
  module header.
* `L4Factoidal/LWS/Linkset.lean`: `Entry.links` holds the client links.
  `Link` with `Prefer: set-linkset` replaces them on PUT and adds to them on
  PATCH; `Link` on POST sets them (server-managed relations dropped); the
  linkset resource accepts JSON Patch and PUT of `application/linkset+json`.
  `serverManagedRels` (`linkset`, `type`, `format`, `size`, `modified`, `up`,
  `items`, `lws#storage`) answer 409; a malformed link (RFC 8288 relation
  syntax, URI-reference target, token attribute names, no `anchor`) answers
  400. A linkset change advances the store clock (so the host persists it)
  but not the resource's `Last-Modified` or `ETag`. The snapshot keeps the
  links (`entryOfJson_entryJson` covers them).
* Build-time checks through `step`: `L4Factoidal/LWS/PaginationLinksTests.lean`.
  Host checks: `tests/lws/draft-binding.mjs`, the "Pagination" and
  "Metadata" rows.

### Bodies are bytes (https://github.com/danbri/factoidal/issues/889)

`LWS.Entry.body` is a `ByteArray`. The hosts call `lwsStep` and `solidStep`
through `callBlobIO` (the `l4_call_blob_io` entry): request content in the
IN region, response content in the OUT region, no encoding; the string entry
`l4_call` carries `body` (text) or `bodyBase64` (RFC 4648 §4). A host never
reads a body as text. Rules, all in Lean:

* A data resource is stored and returned byte for byte; `Content-Range`,
  `size` in listings and `schema:size` count bytes.
* `Range` is a byte range at any offset, also inside a UTF-8 sequence: 206
  with `Content-Range`, 416 with `bytes */len` (`rangeBytes`; theorem
  `range_selection_exact` in `Binding.lean`).
* The ETag of a data resource is its clock and the FNV-1a digest of its
  bytes (`etagFor`).
* Content whose media type is read as text (`rdfTextMedia`: Turtle,
  N-Triples, N-Quads, TriG, JSON-LD, N3, JSON Patch) and whose bytes are not
  UTF-8 gets 400 and is not stored (`rdfContentRefused`).
* The snapshot is format `lws-snapshot-2`, bodies as `bodyBase64`; format 1
  is still read (`Snapshot.lean`, theorems `Base64.decode_encode` and
  `entryOfJson_entryJson`).

Cost: one PUT and one GET of a body must stay linear in its bytes.
`node tests/lws/scaling.mjs` checks n, 2n, 4n (25,000 to 100,000 triples)
for time, peak memory and byte identity
(https://github.com/danbri/factoidal/issues/903: a `Nat` FNV-1a fold made
heap numbers per byte on wasm32; a 100,000-triple PUT took 17 s). Any
per-byte fold in this path runs in machine-word types, with a theorem that
it equals the `Nat` reference (`fnv1a32_eq_spec`).

Test: `node tests/lws/binary-bodies.mjs` (both servers: a PNG-like body with
NUL and 0xFF, every byte range of a small body, restart persistence, a
format-1 snapshot, invalid UTF-8 as Turtle).

### LWS authorization (https://github.com/danbri/factoidal/issues/886)

`L4Factoidal/LWS/Authorization.lean` implements the storage-server half of
the draft's "Authorization" section (w3c/lws-protocol 9a08ff65):

* A request without a valid token gets 401, `WWW-Authenticate: Bearer
  resource_metadata="<origin>/.well-known/oauth-protected-resource<path>"`
  (plus `error="invalid_token"` or `"invalid_request"` when a credential
  was presented and refused) and `Link: <storage>; rel="…lws#storage"`.
* `GET /.well-known/oauth-protected-resource<path>` is the RFC 9728
  document: `resource`, `authorization_servers`, `bearer_methods_supported`.
* `Authorization: Bearer <JWT>` (RFC 6750). The engine verifies the JWS
  under the trusted issuer's keys (ES256, RS256, EdDSA through the vendored
  HACL\* code), then `iss`, `aud` contains the storage IRI, `exp`, `nbf`,
  and `iat` not in the future, each with `leeway` (60 s).
* Access is Web Access Control over the storage's `.acl` resources, with
  the token's `sub` as the agent: allowed, 403 `insufficient_scope` for an
  authenticated agent, or 401 for an anonymous one.
* Keys: the engine answers `{"fetch":{issuer,url}}` from `lwsStep`; the host
  fetches `<issuer>/.well-known/lws-configuration`, passes it to
  `lwsFetched`, fetches the `jwks_uri` it names, passes that too, and steps
  again. At most one key fetch per issuer per `refreshInterval` (default
  60 s, minimum 1 s); that is the key-rotation path.
* Default is enforcement. `--insecure-no-auth` (`insecureNoAuth: true`) is
  the only way to serve without it, and the CLI refuses to start with none
  of `--issuer`, `--auth-config`, `--insecure-no-auth`. `--owner WEBID`
  gives a new storage a root ACL with Read, Write and Control for the owner.
* The LWS draft defines no DPoP binding, so the LWS host takes Bearer only.

Test: `node tests/lws/authorization.mjs` runs a local authorization server
(RFC 8414 metadata and a JWK Set, ES256 keys from `node:crypto`) and checks
the positive and negative cases; `L4Factoidal/LWS/AuthorizationTests.lean`
holds the `#guard`s with a stub verifier.

From JavaScript:

```js
import { listen } from '@factoidal/core/lws'
import { listen as solidListen } from '@factoidal/core/solid/server'
```

## Run the client

```
factoidal solid-client <get|put|post|delete|discover> URL [--body TEXT|--file PATH]
                       [--content-type M] [--interpret KIND]
```

The five verbs are aliases for the ABI's request kinds — `get`→`read`,
`put`→`replace`, `post`→`create`, `delete`→`delete`,
`discover`→`discoverStorage` — and a kind name is accepted directly.

```js
import { createSolidClient } from '@factoidal/core/solid/client'
const client = await createSolidClient({ baseIri: 'https://pod.example/' })
```

`solidClientRequest` and `solidClientResponse` take **different** kind
vocabularies and the host never derives one from the other. Which
interpretation a reply wants is a protocol decision: the host uses the
`interpret` kind the request envelope named, then the one the caller
passed, and otherwise returns the reply uninterpreted.

## Run the tests

```
node tests/lws/server.mjs
node tests/solid/server/protocol.mjs
node tests/solid/client/against-own-server.mjs
```

Each also runs under Deno (`deno run --allow-read --allow-net --allow-env
<file>`), and the Node run drives the Deno run when `deno` is on PATH.
`tools/internal-tests.sh` runs all three as `node-tests/...` suites.

Each prints `N pass, M fail, S skipped (out of T)`.

**The wasm module is rebuilt by whoever owns the Lean side, not by these
tests.** A module without the new ops answers `unknown op`; each suite
probes with one call and then SKIPS every check by name with that reason
printed. A skip is never a pass (anti-pattern 3), and the score line
always carries the skip count.

## Run the interop scripts

```
bash tools/solid-server-interop.sh        # solid-crud-tests + WAC vs our server
bash tools/solid-client-interop.sh        # our client vs Community Solid Server
bash tools/solid-conformance-harness.sh   # the Gherkin harness (Docker)
```

Exit codes are the same in all three: `0` passed, `1` something failed,
`2` could not run here with the reason printed. **`2` is never a green
skip** — a suite that could not run reports `0 pass, 0 fail (out of 0) -
not run`.

What makes each one exit 2 today:

| script | why it does not run |
| --- | --- |
| `solid-server-interop.sh` | `web-access-control-tests` logs in through an external Solid-OIDC issuer before its first request: `solid-auth-fetcher` posts a login cookie of a Node Solid Server style issuer (`POST /login/password`) to `/authorize` and expects a redirect with a code. `solid-serve` verifies the tokens (issue 899); what is missing is that issuer with two accounts. Community Solid Server 7 has no `/login/password` and its `/authorize` asks for consent, so it cannot stand in (measured 2026-10-21, see below) |
| `solid-client-interop.sh` | the module carries no Solid client ops; also refuses to start the ~250 MB Community Solid Server download below 2 GB free |
| `solid-conformance-harness.sh` | no Docker daemon, or no `SOLID_HARNESS_ENV` credentials file |

Measured 2026-10-21 (https://github.com/danbri/factoidal/issues/892):

* `solid-server-interop.sh`: solid-crud-tests 27 pass, 0 fail, 8 expected
  fail, 41 skipped (out of 76); web-access-control-tests not run (external
  OIDC), so the script exits 2. Before the repairs of that day the same
  run gave 20 pass, 15 fail. The expected failures are the rows of
  `tests/solid/server/crud-xfail.tsv`, each with its open issue
  (895: the test POSTs to a missing container, §5.3 requires 404; 896: the
  test's N3 Patch is not N3; 897: no RDFa reader, a MAY; 898: no
  notification channels). A listed test that passes turns the run red.
  The 41 skips: 32 websockets-pubsub checks (`SKIP_WPS`), 8 behind the
  suite's own `describe.only`, 1 `describe.skip`.
* The earlier figure "2 pass, 6 fail (out of 8)" counted one of nine test
  files: the other seven failed to LOAD, because the suite's notification
  client reads `/tls/server.key` (present only in its Docker image) unless
  `SKIP_WPS` is set. The script now sets it and counts a test file that
  does not load as a failure. Check the denominator against the suite's
  file list before quoting a score.
* The script copies each suite to a temporary directory before `npm ci`
  (`SOLID_INTEROP_FIXTURES` names another fixture checkout,
  `SOLID_INTEROP_WORK` keeps the installed copy between runs), so no
  `node_modules` is written into a checkout.
* `solid-client-interop.sh`: 10 pass, 0 fail, 0 skipped (out of 10) against
  Community Solid Server 7.2 with `tests/solid/client/css-public-write.json`
  (file-root with allow-all authorization: TEST ONLY). With
  `@css:config/file.json` every unauthenticated write answered 401.
  `SOLID_CSS_BIN` runs a CSS installed outside the checkout instead of
  `npx`.
* `solid-conformance-harness.sh`: not run — the Docker client is installed
  but no daemon runs.

`tests/solid/client/against-own-server.mjs` puts our client and our
server on two ends of one socket, so a shared misreading of the
specification passes it. That is what
`tests/solid/client/against-community-server.mjs` (driven by
`solid-client-interop.sh`) and the two Jest suites are for.

## What is stubbed, and what is a stated boundary

Not in the first slice, recorded so nobody assumes it: Solid-OIDC token
issuance, Access Control Policy, Solid Notifications channels,
persistence into Shardborough, and the LWS `authn-openid`, `authn-saml`,
`authn-ssi` and `searchindex` drafts.

**Authentication is decided in Lean.** The JOSE layer
(`L4Factoidal/JOSE/`) verifies ES256, RS256 and EdDSA through the vendored
HACL\* P-256, RSA and Ed25519 code (`L4Factoidal/Crypto/*Native.lean`), in
the native build and in the wasm module. The LWS host uses it for Bearer
access tokens (above). The Solid server has the Solid-OIDC decision with
DPoP (`Solid/Server/Auth.lean`), and `Solid/Server/Oidc.lean` wires it
into the server (https://github.com/danbri/factoidal/issues/899):
`Oidc.authenticatedStep` decides the requester and calls `Methods.stepAs`.
It keeps the trusted issuers' keys, found by OpenID Connect Discovery
(`/.well-known/openid-configuration`, issuer identity check of §4.3, then
`jwks_uri`); checks `aud` contains `solid`, the `webid` claim, `exp`,
`cnf.jkt` against the DPoP key, the proof's `htm`, `htu`, `iat`, `ath` and
signature, and a `jti` replay cache; and checks that the WebID profile
lists the issuer with `solid:oidcIssuer` (Solid-OIDC §8.1.1, §6.1). A
refused credential answers 401 with `WWW-Authenticate: DPoP algs=…,
error=…` (RFC 9449 §7.1). The host fetches only the URLs a `fetch` answer
names. Host test: `node tests/solid/server/oidc.mjs`.

## Adding a rule

1. Write it in Lean, under `L4Factoidal/LWS/` or
   `L4Factoidal/Solid/Server/`, with its `#guard` in the neighbouring
   `Tests.lean`.
2. Add its row to the conformance registry: statement id, verbatim quote,
   module, status.
3. If it is visible over HTTP, add a check to the matching host suite in
   `tests/`, naming the specification section in the check name.
4. Rebuild the wasm module (`skills/lean4-wasm-export`) so the host
   suites stop skipping.
5. Nothing goes in a host. If a rule seems to need host code, the ABI is
   missing a field — extend the ABI record in the ledger instead.
