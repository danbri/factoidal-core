# LWS 1.0 Core and Solid Protocol — conformance ledger

Design record: [`docs/designissues/2026-09-06-lws-and-solid-protocols.md`](designissues/2026-09-06-lws-and-solid-protocols.md).
Tracking issue: <https://github.com/danbri/factoidal/issues/659>.

The Lean modules are `formal/lean4/L4Factoidal/LWS/` and
`formal/lean4/L4Factoidal/Solid/`. Every row below names one normative
statement of a specification, quotes it verbatim, names the Lean module that
decides it, and gives its status.

Status values (`L4Factoidal.LWS.Conformance.Status`):

| value | meaning |
|---|---|
| `proved` | a Lean theorem discharges the statement; the row names the theorem |
| `guarded` | a `#guard` in `Tests.lean` evaluates the statement at build time; the row names the guard |
| `hostVerified` | the decision needs bytes, a socket, a clock or a token the Lean side does not hold; a host test decides it |
| `open` | not decided yet |

Scores are always written "N pass, M fail (out of T)".

## wasm ABI

The host agent codes against this section. The operations are registered in
`formal/lean4/Wasm/Dispatch.lean` and reachable through `L4Wasm.callIO`
(they hold state, so the pure `L4Wasm.call` answers `unknown op` for them).
Arguments arrive as the dispatch ABI's JSON array of strings; every answer is
one envelope, `{"ok":true,…}` or `{"ok":false,"error":"…"}`.

### Request and response documents

A request is a JSON object:

```json
{"method":"PUT",
 "target":"/alice/card",
 "headers":[["content-type","text/turtle"]],
 "body":"<#me> <http://xmlns.com/foaf/0.1/name> \"Alice\" ."}
```

* `method` — an HTTP method token, upper case.
* `target` — the request target as a path within the storage, beginning with
  `/`. A path that ends with `/` names a container (Solid Protocol §3.1).
* `headers` — an array of two-element arrays. Names are compared case
  insensitively; the engine lower-cases them on the way in.
* `body` — the content as text, through the string entry (`l4_call`).
* `bodyBase64` — the content in the base64 encoding of RFC 4648 §4, through
  the string entry, for content that is not UTF-8.

**Bodies are bytes** (https://github.com/danbri/factoidal/issues/889). The
hosts call `lwsStep` and `solidStep` through the byte-region entry
`l4_call_blob_io` (`callBlobIO(op, args, bytes)` in `l4factoidal.js`): the IN
region is the request content and the OUT region is the response content.
The request document then carries no `body` or `bodyBase64` (the engine
refuses one), and the response document carries `bodyBytes`, the length of
the OUT region, in place of `body`. Through the string entry `l4_call` the
response carries `body` when the content is UTF-8 and `bodyBase64` when it is
not, so neither entry alters a byte.

Why the byte region and not base64 in the document: the module's rule for
bytes (`skills/lean4-wasm-export`, "Moving BYTES, not text" and "Moving bytes
OUT") is one contiguous region copied once into a Lean `ByteArray`, with no
encoding; base64 costs a third more bytes and a character walk each way,
and was refused for byte transport by the owner on 2026-09-03. The region is
copied on entry and on exit, so Lean never holds a host pointer and the host
may free its buffer when the call returns.

Every member is optional except `method` and `target`.

A response is a JSON object with the same shape minus the method:

```json
{"status":201,
 "headers":[["location","/alice/card"],["last-modified","Thu, 01 Jan 1970 00:00:01 GMT"]],
 "body":""}
```

### Operations

| op | arguments | answer |
|---|---|---|
| `lwsOpen` | `[configJson]` | `{"ok":true,"handle":"lws1","root":"/"}` |
| `lwsStep` | `[handle, requestJson]` | `{"ok":true,"response":{…},"changed":B}`, with `"deliveries":[{"id","url","headers":[[n,v],…],"body"},…]` when the step causes notifications |
| `lwsClose` | `[handle]` | `{"ok":true}` |
| `lwsSnapshot` | `[handle, optionsJson?]` | `{"ok":true,"snapshot":{"format":"lws-snapshot-2","clock":N,"entries":[…]}}`; each entry's body is `bodyBase64`. A `lws-snapshot-1` document (body as the string `body`) is still read. With a `storageKey` the snapshot is the sealed document `{"format":"lws-snapshot-sealed-1","cipher":"chacha20-poly1305","keyId","nonce","ciphertext"}`, and `optionsJson` must be `{"nonce":"<base64 of 12 random bytes>"}` (https://github.com/danbri/factoidal/issues/921). |
| `lwsFetched` | `[handle, documentJson]` | `{"ok":true,"fetch":{"issuer":…,"url":…}}`, `{"ok":true,"installed":N}` or `{"ok":true,"refused":"…"}` |
| `lwsDelivered` | `[handle, {"id","status","now"?}]` | `{"ok":true,"changed":B}`, with `"retry":{"delivery":{…},"after":SECONDS}` when the engine wants the delivery made again |
| `solidOpen` | `[configJson]` | `{"ok":true,"handle":"solid1","root":"/","storage":"…"}` |
| `solidStep` | `[handle, requestJson]` | `{"ok":true,"response":{…}}` |
| `solidClose` | `[handle]` | `{"ok":true}` |
| `solidSnapshot` | `[handle, optionsJson?]` | as `lwsSnapshot` |
| `solidFetched` | `[handle, documentJson]` | `{"ok":true,"fetch":{"kind":…,"key":…,"url":…}}`, `{"ok":true,"installed":N}` or `{"ok":true,"refused":"…"}` |
| `solidClientRequest` | `[kind, argsJson]` | `{"ok":true,"request":{…}}` |
| `solidClientResponse` | `[kind, responseJson]` | `{"ok":true,"interpretation":{…}}` |

`configJson` is a JSON object. Members, all optional:

| member | default | meaning |
|---|---|---|
| `baseIri` | `"http://localhost/"` | the absolute IRI the storage root maps to. A request target `/a/b` denotes `baseIri` + `a/b`. |
| `now` | `0` | the clock, in seconds since the Unix epoch. Every mutation stamps `Last-Modified` from it and then advances it by one second, so the writes of one request have increasing modification times with no call to a real clock. A host with a real clock sets it on every request, so across requests in one second it repeats; entity tags and POST names do not depend on it (https://github.com/danbri/factoidal/issues/911). |
| `owner` | absent | the WebID the storage advertises through `Link: rel="http://www.w3.org/ns/solid/terms#owner"`. |
| `agent` | absent | the WebID of the requesting agent for every request on this handle. A handle with no `agent` is an unauthenticated agent. It stands only when authentication is off: for `lwsOpen` with `insecureNoAuth`, for `solidOpen` with `insecureNoAuth` or with neither `auth` nor `insecureNoAuth`. |
| `enforceWac` | `false` | `solidOpen` only. With it false the Web Access Control decision is computed and reported in `WAC-Allow` but never refuses a request, which is the first slice's public storage. With it true the decision is enforced and a target with no effective ACL resource is denied, as Web Access Control §5.3 requires. |
| `snapshot` | absent | a document from `lwsSnapshot`/`solidSnapshot`; the storage continues from it. `L4Factoidal/LWS/Snapshot.lean` refuses a snapshot with a path that has a dot segment, an empty segment, a backslash, an encoded slash or a NUL, a repeated path, or no storage root. |
| `auth` (`solidOpen`) | absent | Solid-OIDC with DPoP (`L4Factoidal/Solid/Server/Oidc.lean`, https://github.com/danbri/factoidal/issues/899): `{"issuers":[{"issuer":IRI,"jwks":{…}?}],"leeway":S?,"iatWindow":S?,"refreshInterval":S?,"checkProfileIssuer":B?}`. Turns `enforceWac` on unless the configuration sets it. `solidStep` may then answer `{"fetch":{"kind":"issuer"\|"profile","key":…,"url":…}}`: the host fetches that URL, passes `{kind,key,url,status,body,now?}` to `solidFetched`, follows any `fetch` in the answer, and steps the request again. With neither `auth` nor `insecureNoAuth` authentication is off; `factoidal solid-serve` refuses to start in that state. |
| `auth` (`lwsOpen`) | absent | `lwsOpen` only. The authorization configuration of `L4Factoidal/LWS/Authorization.lean`: `{"issuers":[{"issuer":IRI,"jwks":{"keys":[…]}?}],"audience":IRI?,"leeway":S?,"refreshInterval":S?}`. With neither `auth` nor `insecureNoAuth`, authorization is ENFORCED with no trusted issuer: only what the ACLs give to the public is served. |
| `insecureNoAuth` | `false` | `lwsOpen` and `solidOpen`. `true` is the development mode with no authorization (`factoidal lws-serve --insecure-no-auth`); then `agent` stands as before. `auth` and `insecureNoAuth` together are refused. |
| `moves` | `true` | `lwsOpen` only. `false` turns moving resources off: no `MoveResource` capability, and a change of an `up` link is refused with 409 (`L4Factoidal/LWS/Move.lean`). |
| `notifications` | `true` | `lwsOpen` only. `false` turns LWS notifications off: no `NotificationService` in the storage description and no subscription endpoint (`L4Factoidal/LWS/Notifications.lean`). |
| `typeIndex` | `true` | `lwsOpen` only. `false` turns the Type Index and Type Search services off: no `TypeIndexService` or `TypeSearchService` in the storage description, and their endpoints are ordinary storage paths (`L4Factoidal/LWS/Search.lean`). |
| `searchResults` | `false` | `lwsOpen` only. ANTICIPATORY AND UNSTABLE (https://github.com/danbri/factoidal/issues/922). `true` makes a QUERY answer of the Type Search Service by an authenticated agent carry `Content-Location` naming a search results resource (`L4Factoidal/LWS/SearchResults.lean`); the storage description then carries the extension member `https://github.com/danbri/factoidal/issues/922#unstableResultsResource` on the `TypeSearchService` entry. Needs `typeIndex`. `factoidal lws-serve --unstable-search-results`. Likely to change. |
| `searchResultsTtl` | `600` | `lwsOpen` only, with `searchResults`. Seconds a results resource answers; then 410. |
| `searchResultsMax` | `100` | `lwsOpen` only, with `searchResults`. The most results resources kept; the oldest is removed first (then 404). |
| `merkle` | `false` | `lwsOpen` only. Merkle hashes, an option of this server (https://github.com/danbri/factoidal/issues/919; the LWS drafts define no integrity mechanism). `true` keeps a SHA-256 digest of every resource and a Merkle digest of every container (`L4Factoidal/LWS/Merkle.lean`) and shows them (`MerkleHttp.lean`): `Repr-Digest` (RFC 9530) on a 200 or 206 GET or HEAD of a resource with its stored media type, `Factoidal-Merkle-Root` and the listing member `https://github.com/danbri/factoidal/issues/919#merkleRoot` on a container, the member `https://github.com/danbri/factoidal/issues/919#storageMerkleRoot` in the storage description; under authorization the roots to the storage controller only. Entity tags do not change. No hash is in a snapshot; they are rebuilt at open. `factoidal lws-serve --merkle`. |
| `entropy` | absent | `lwsOpen` only. At least 16 random bytes, base64, from the host. The seed of the notification signing key (Ed25519) when the snapshot holds none, and of the run tag in activity identifiers. Without it deliveries are not signed. `npm/factoidal/lws/server.mjs` passes 32 bytes from `crypto.getRandomValues`. |
| `storageKey` | absent | `lwsOpen` and `solidOpen`. The storage key text, 32 bytes as 64 hex digits or base64url (the hosts read it from the environment variable `FACTOIDAL_LWS_KEY`). With it, `snapshot` must be a sealed document under this key and is authenticated before use, and every snapshot is sealed with ChaCha20-Poly1305 (HACL*). A wrong key, a changed or truncated sealed document, a clear-text `snapshot` with a key and a sealed one without a key are refused (`L4Factoidal/LWS/SnapshotSeal.lean`, https://github.com/danbri/factoidal/issues/921). The LWS drafts and the Solid Protocol say nothing about encryption at rest; this is an option of this server, off by default. |
| `rootAcl` | absent | the ACL document (Turtle) of the storage root, written when the storage is created. Web Access Control §3.2 requires the root container's ACL resource to have a representation, and under enforcement a storage cannot write its own: the request that would write it is the first request it would authorize. It is therefore a host provisioning input. |

`lwsStep` and `solidStep` answer `"changed": true` when the step changed the
storage (every mutation advances the clock). `factoidal lws-serve DIR` and
`solid-serve DIR` then write the snapshot to `DIR/lws-state.json`
(temporary file, fsync, rename; `npm/factoidal/lws/persist.mjs`) and read it
back at start. No request target becomes a file name. The LWS snapshot also
carries a member `notifications` (the subscriptions, the counter and the
signing key), which `lwsOpen` reads back; a subscription change answers
`"changed": true` as well.

When an LWS step causes notifications (https://github.com/danbri/factoidal/issues/890),
`lwsStep` answers `deliveries`: each one is an HTTP request the engine
decided to make. The host POSTs `body` to `url` with exactly the header
pairs given, and reports the answer's status (0 when none came) with
`lwsDelivered(handle, {"id","status","now"?})`. When that answers `retry`,
the host waits `after` seconds and makes the request in `delivery`, which
carries a new signature. The engine decides which changes are announced,
to whom, the body, the signature, whether to retry and when a subscription
is deactivated.

A request document may override the clock and the agent for one step with the
members `now` and `agent` beside `method`. An LWS request document may also
carry `random`: at least 16 random bytes, base64, from the host's random
source. The engine uses them only to name a search results resource (the
base64url form of the first 16 bytes) when `searchResults` is on; without
them no results resource is made. `npm/factoidal/lws/server.mjs` passes 16
bytes from `crypto.getRandomValues` with every request. When `searchResults`
is on and a record exists, the snapshot carries one more member,
`searchResults` (format `lws-search-results-unstable-1`: each record's `id`,
`filter`, `agent`, `client`, `created`, `expires` and `paths`), which
`lwsOpen` reads back and checks; a QUERY that makes a record answers
`"changed": true`. On an LWS handle the `agent`
override stands only under `insecureNoAuth`; with authorization on, the agent
is the `sub` of the access token the engine validated, and nothing else.

On an LWS handle with authorization on, `lwsStep` may answer
`{"ok":true,"fetch":{"issuer":…,"url":…}}` instead of a response: the engine
needs the authorization server's metadata (`<issuer>/.well-known/lws-configuration`,
RFC 8414) or its JWK Set (`jwks_uri`) before it can decide. The host fetches
exactly that URL and calls `lwsFetched(handle, {"issuer","url","status","body","now"})`.
The engine checks the metadata `issuer` (RFC 8414 §3.3), takes the `jwks_uri`,
answers the next `fetch`, and installs the keys; the host then steps the same
request again. The engine fetches an issuer's keys at most once per
`refreshInterval` (at least one second), which is how a token under a
rotated key is accepted and how an unknown `kid` cannot make the server
fetch on every request.

`solidClientRequest` kinds: `read`, `create`, `replace`, `patch`, `delete`,
`discoverStorage`, `readProfile`. `argsJson` is a JSON object whose members
depend on the kind; `target` is required by all of them, `body` and
`contentType` by `create`, `replace` and `patch`, and `state` by the second
and later steps of a multi-step operation (see below).

`solidClientResponse` kinds: `storage`, `containment`, `auxiliaries`,
`profile`, `wacAllow`, `created`. The interpretation object is documented
per kind in `formal/lean4/L4Factoidal/Solid/Client/Responses.lean`.

The response document carries members some kinds need beside `status`,
`headers` and `body`: `webId` and `baseIri` for `profile`, `target` —
the request target the reply answers — for `storage`, and `requestUri` —
the absolute URL the request was sent to — for `containment`, which
resolves relative references in the listing against it (RFC 3986 §5.1.3;
Community Solid Server writes members as `<one>`).

### Multi-step operations

An interpretation may answer `"continue": true` with a `"state"`. The host
then calls `solidClientRequest` again for the SAME kind, with `state` added
to the arguments, sends the request it gets back, and interprets the reply
the same way. The loop ends on the first interpretation with
`"continue": false`. The host attaches no meaning to `state`; it passes the
value through.

`discoverStorage` is the operation that uses it. Solid Protocol §4.1:
"Clients can determine the storage of a resource by moving up the URI path
hierarchy until the response includes a `Link` header field with
`rel="type"` targeting `http://www.w3.org/ns/pim/space#Storage`." The
`storage` interpretation of a reply that carries no such link answers
`"continue": true` and a `state` naming the parent container of the reply's
`target` — the last path segment dropped, the trailing slash kept. The
status code does not end the walk: a 404 or a 403 on a resource that does
not exist yet, or that this agent may not read, says nothing about where the
storage is.

The walk ends in one of two ways, both with `"continue": false`:

* the reply carries the storage type link, and the `storage` member is the
  `target` of that reply — the storage the resource belongs to;
* the `target` is `/`, which has no parent, and `storage` is `null`.

The `storage` interpretation therefore has these members:

| member | meaning |
|---|---|
| `isStorage` | does THIS reply carry the storage type link |
| `storage` | the resource whose reply carried it, `null` until then |
| `storageDescription` | the `solid:storageDescription` link target |
| `owner` | the `solid:owner` link target |
| `lastModified` | the `Last-Modified` field value |
| `allow` | the methods the `Allow` field named |
| `continue` | is a further request part of this operation |
| `state` | the resource to ask about next, `null` when `continue` is false |

A caller that names no `target` gets the facts of one reply, `storage` null
and `continue` false: §4.1's rule is about the path hierarchy of a named
resource, so with no name there is no walk.

### Errors

An operation that cannot answer at all — an unknown handle, a request
document that is not JSON, an unknown client kind — answers
`{"ok":false,"error":"…"}`. A request the protocol REFUSES is not an error:
it answers `{"ok":true,"response":{"status":405,…}}`, because the status code
is the protocol's own answer.

## LWS editor's draft 2026-10-19 audit

Read 2026-10-20: <https://w3c.github.io/lws-protocol/lws10-core/>, source
w3c/lws-protocol commit `9a08ff65a6670cc5d308ed5e531032f23af30fcc`
(2026-10-19). The draft now has an HTTP binding (Operations, Metadata,
Container Representation, LWS Media Type, Discovery, Authorization,
Notifications, Access Requests). The registry below this section was read
2026-09-06, when those sections were empty; it is older than the draft. The
draft has 256 sentences with MUST, SHOULD, REQUIRED or SHALL; this table
groups the server requirements by rule. Client-only rules, authorization
server rules and examples are left out.

Status: **tested** = implemented with a `#guard` in
`formal/lean4/L4Factoidal/LWS/Tests.lean` and a host check in
`tests/lws/draft-binding.mjs` or `tests/lws/server.mjs`; **missing** = an
open issue and an xfail host check; **n/a** = conditional on a feature this
server does not advertise.

| section | requirement | status | test |
|---|---|---|---|
| Operations | the four operations create, read, update, delete | tested | `lwsGuardCreateReadUpdateDelete`; server.mjs CRUD |
| Read | 200 with the stored media type | tested | `lwsGuardCreateReadUpdateDelete` |
| Read | MUST include `ETag` on GET/HEAD (also §Metadata); a strong tag changes whenever the representation does (RFC 9110 §8.8.1) | tested (clock and FNV-1a digest of the bytes of a data resource, of the listing of a container, so two changes in one second give two tags: https://github.com/danbri/factoidal/issues/911 F3) | `lwsGuardEtagOnRead`, `lwsGuardContainerTagSameSecond`; draft-binding "Read: GET carries ETag", "Read: a container ETag changes when a member is deleted in the same second" |
| Read | Last-Modified on GET and HEAD (CG delta) | tested | `lwsGuardLastModifiedOnGet/Head`; server.mjs |
| Read | MUST support range requests | tested (single byte range at any offset, 206 with `Content-Range`, 416 with `bytes */len`; theorem `range_selection_exact`) | `lwsGuardRange`, `lwsGuardEveryRange`, `lwsGuardRangeInsideSequence`; draft-binding "Read: a byte Range"; `tests/lws/binary-bodies.mjs` |
| Read | SHOULD support conditional requests; 304 | tested (ETag; If-Modified-Since and If-Unmodified-Since compared as HTTP-dates in the three RFC 9110 §5.6.7 formats, If-Unmodified-Since for every method with 412, in the order of RFC 9110 §13.2.2; theorem `unixOfCivil_civilOfUnix`: https://github.com/danbri/factoidal/issues/911 F5) | `lwsGuardNotModified`, `lwsGuardIfUnmodifiedSince`, `HttpDate.lean` guards; draft-binding "Conditional requests" |
| Read | MUST support HEAD with the same headers | tested | `lwsGuardEtagOnRead`, `lwsGuardLastModifiedOnHead` |
| Read | Link `linkset`, `up`, `type` on every response | tested | `lwsGuardLwsLinks` |
| Containment | MUST `rel="up"` on non-root GET/HEAD | tested | `lwsGuardLwsLinks` |
| Containment | integrity on create and delete; no orphans; no cycles | tested | `lwsGuardContainerEnumerates`, `lwsGuardRecursiveDelete`; PUT creates ancestors |
| Container Representation | `id`, `type`, `totalItems`, `items` (empty array when empty); item `id`, `type`, `format` (MUST for data), `size`, `modified` | tested | `lwsGuardContainerListing`; draft-binding |
| Container Membership | listing includes all readable members | tested (no access control on LWS host) | `lwsGuardContainerListing` |
| LWS Media Type | container MUST support `application/lws+json` | tested | `lwsGuardContainerListing` |
| Content Negotiation | profile media types RDF-isomorphic to lws+json; `Content-Type` with profile; SHOULD `Vary: Accept` | tested (Turtle, JSON-LD; `size` is `http://schema.org/size`, as the core draft's examples and the context give it; `lws10-vocab/vocabulary.yml` says `https://schema.org/`; a contained container has no `dcterms:modified`, because the context defines `modified` for a DataResource only: https://github.com/danbri/factoidal/issues/911 F2) | `lwsGuardContainerTurtle`, `lwsGuardTurtleSchemaNamespace`; draft-binding "LWS Profile" |
| Pagination | SHOULD paginate; `first` (MUST), `next` (MUST, not on the last page), `prev` (not on the first page), `last`; 200; `totalItems` over the full membership | tested (threshold and page size `pageSize`, default 100; increasing path order, each member once; an `ETag` per page; theorem `pageItems_concat`) | `PaginationLinksTests`; draft-binding "Pagination" (https://github.com/danbri/factoidal/issues/887) |
| Create | POST to container, 201 + `Location`; `Link` up, linkset, type | tested | `lwsGuardPostCreates` |
| Create | container via `Link rel="type"` lws:Container | tested (also with no content and no `Content-Type`, the draft's own example: https://github.com/danbri/factoidal/issues/911 F1) | `lwsGuardPostCreates`, `lwsGuardPostWithoutContent`; draft-binding "Create: POST with no content" |
| Create | identity hint used, unique | tested (the first free name of `hint`, `hint-1`, `hint-2`, ...; theorem `childPathFor_fresh`: a POST never replaces a resource, also for POSTs in one second under a real clock: https://github.com/danbri/factoidal/issues/911 F6) | Slug guards in `Tests.lean`, `lwsGuardPostSameSecondUnique`; draft-binding "Create: five POSTs to one container in one second" |
| Create | 404 when the target container does not exist | tested | POST guards |
| Create | client `Link` headers as user metadata; server metadata not overridable | tested (client links stored; server-managed relations not stored) | `PaginationLinksTests` "POST stores the client links" (https://github.com/danbri/factoidal/issues/888) |
| Update | PUT replaces; 412 on failed `If-Match` | tested | `lwsGuardIfMatch` |
| Update | MUST minimally support JSON Patch | tested | `lwsGuardJsonPatch` |
| Update | `Prefer: set-linkset` MUST interpret `Link` headers (replacement for PUT, partial update for PATCH) | tested (server-managed relation 409, malformed link 400) | `PaginationLinksTests`; draft-binding "Metadata" (https://github.com/danbri/factoidal/issues/888) |
| Delete | 204; atomically removes from parent; 409 non-empty | tested | `lwsGuardCreateReadUpdateDelete`, `lwsGuardRecursiveDelete` |
| Delete | `Depth: infinity` recursive (MAY) | tested | `lwsGuardRecursiveDelete` |
| Delete | linkset removed with the resource | tested | `lwsGuardLinkset` |
| Metadata | linkset resource per resource, RFC 9264, `application/linkset+json` | tested | `lwsGuardLinkset` |
| Metadata | `Allow` lists GET and PATCH; `Accept-Patch: application/json-patch+json` | tested | `lwsGuardLinkset` |
| Metadata | PATCH on linkset with JSON Patch; preserve links the client may not modify | tested (client links added or removed; a change to a server-managed link gives 409) | `lwsGuardLinkset`, `PaginationLinksTests`; draft-binding "Metadata: PATCH on the linkset" |
| Metadata | PUT on linkset: if advertised in `Allow`, replaces the linkset (otherwise 405) | tested (advertised; server-managed relations kept, a change to one gives 409) | `lwsGuardLinkset`, `PaginationLinksTests` |
| Metadata | 412 on failed precondition for linkset PUT/PATCH | tested (If-Match) | `linksetStep` |
| Discovery | `lws#storage` link on every GET/HEAD | tested | `lwsGuardLwsLinks` |
| Discovery | storage description, `application/lws+cid`, `@context` array, `id`, `type`, StorageRoot service | tested | `lwsGuardStorageDescription` |
| Discovery | MoveResource capability when `up` is modifiable; `appliesTo` a set of strings, `preservesIdentifier` a boolean | tested (`appliesTo` DataResource and Container, `preservesIdentifier` false; config `moves: false` turns it off) | `MoveTests` "Discovery"; draft-binding "Moving Resources: the storage description" |
| Moving Resources | a change of the `up` link by JSON Patch on the linkset moves the resource; MUST describe `MoveResource`; without it MUST refuse with 4xx | tested (PUT of the linkset too; without the capability 409) | `MoveTests`; draft-binding "Moving Resources" (https://github.com/danbri/factoidal/issues/914) |
| Moving Resources | MUST atomically remove from the former parent's `items` and add to the destination's; MUST update the ETag of both containers | tested (one function from store to store; both containers stamped; theorems `move_unmoved`, `move_moved`, `move_vacated`) | `MoveTests`; draft-binding "moves a data resource" |
| Moving Resources | destination MUST be an existing container; MUST reject removal of `up` | tested (409) | `MoveTests` "Refusals"; draft-binding "answers 409" |
| Moving Resources | containment integrity: a container MUST NOT move into itself or a descendant | tested (409; theorem `move_tree` with `tree_acyclic`) | `MoveTests`; draft-binding |
| Moving Resources | content and user-defined metadata unaffected; links the client may not modify preserved; auxiliary resources stay bound | tested (theorem `move_moved`; ACL and description resources move with their primary resource) | `MoveTests` "Client links travel" |
| Moving Resources | a server that does not preserve identifiers MUST answer 200 with the updated linkset (new `anchor`) and `Content-Location` | tested | `MoveTests`; draft-binding |
| Moving Resources | SHOULD answer the previous identifiers with 301 and `Location` | missing | https://github.com/danbri/factoidal/issues/914; draft-binding xfail |
| Moving Resources | containers MAY move (descendants with them), indicated by `Container` in `appliesTo` | tested | `MoveTests` "A container moves"; draft-binding "a container moves" |
| Moving Resources | MUST NOT move unless the agent may delete the resource (the whole subtree for a container) and create in the destination | tested (Web Access Control: Write, or Control for an ACL resource, on every moved resource; Append on the destination) | `MoveTests` "Authorization" |
| Status mappings | SHOULD use RFC 9457 problem details | tested | `lwsGuardProblemDetails` |
| Authorization Server Discovery | 401 MUST carry `WWW-Authenticate` with `resource_metadata` (RFC 9728 §5.1) and a `Link` to the storage (`rel` lws#storage) | tested (the link names the storage's canonical URI, the storage description `id`, as every other response does, and the default token audience is the same IRI: https://github.com/danbri/factoidal/issues/911 F4) | `AuthorizationTests` "Missing token", `storageIri` guards; authorization.mjs "Discovery"; draft-binding "Authorization" |
| Protected Resource Metadata | RFC 9728 document; `authorization_servers` REQUIRED with at least one issuer; `resource` is the requested resource | tested (served at `/.well-known/oauth-protected-resource<path>`, RFC 9728 §3.1) | `AuthorizationTests` "The metadata document"; authorization.mjs |
| Token Validation: Presentation | Bearer in `Authorization` (RFC 6750 §2.1) | tested (another scheme: 401 `invalid_request`) | `AuthorizationTests`; authorization.mjs "Presentation" |
| Token Validation: signature | verify with the key from the issuer's `jwks_uri`; SHOULD cache; MUST support key rotation | tested (ES256, RS256, EdDSA over vendored HACL*; cache with refetch at most once per `refreshInterval`) | `validateToken_valid_verified`; authorization.mjs "bad signature", "key rotation" |
| Token Validation: claims | `iss` is the expected issuer; `aud` includes the storage; `exp`, `nbf`, `iat` not in the future, with clock skew | tested | `checkClaims_valid`; `AuthorizationTests`; authorization.mjs "expired", "another audience", "untrusted issuer", "iat in the future" |
| Token Validation: failure | 401 with `resource_metadata` and an `error` parameter | tested (`invalid_token`, `invalid_request`) | authorization.mjs |
| Token Validation: policy | a valid token whose agent the policy does not allow is rejected | tested (403, `error="insufficient_scope"`, Web Access Control over the storage's ACL resources) | `AuthorizationTests` "Another agent"; authorization.mjs "Policy" |
| (server choice) | authorization is on unless the deployment opts out (`--insecure-no-auth`) | tested | `decide_insecure`, `default_not_insecure`; authorization.mjs "Default", "Development mode", "CLI" |
| Authentication | credential suites (authorization server side: token exchange, subject tokens) | n/a (storage server only; the authorization server is out of scope of a storage server) | none |
| Notification Discovery | MUST advertise a `NotificationService` with `serviceEndpoint` and a `subscriptionType` array | tested | `NotificationsTests` "Discovery"; draft-binding "Notifications: the storage description" |
| Envelope Properties | `type` Notification, `storage`, `activity` (object or array) | tested | `NotificationsTests` "Deliveries"; draft-binding "Create, Update and Delete" |
| Activity Properties | `id`, `type` array, `object` with `id` and `type` array (`Container`, `DataResource`), `published` RFC 3339; `target` on Create, `origin` on Delete | tested (`id` a `urn:uuid`) | `NotificationsTests`; draft-binding |
| Activity Types | MUST support Create, Update, Delete | tested (type decided from the store before and after the step, theorem `classify_sound`) | `NotificationsTests`; draft-binding |
| Activity Types | Move, for a server that moves resources between containers (`origin`, `target`, `object` after the move); SHOULD be one Move, not Delete and Create | tested (one Move per move, theorem `mem_changesOf_sound`) | `MoveTests` "The Move notification"; draft-binding "one Move activity" |
| Batching | MAY combine activities in one envelope | tested (one envelope per subscription per request) | `NotificationsTests` "Recursive scope and batching" |
| Subscriptions | authenticated POST, body `application/lws+json`; `type` one of the advertised types; `topic` an array of URIs | tested (401 with no token, 415 for another media type, 400 for a missing or unadvertised `type` or a missing `topic`) | `NotificationsTests` "Negative requests"; draft-binding; authorization.mjs "anonymous" |
| Subscription Scope | a container subscription is recursive; a data resource subscription covers only itself | tested | `NotificationsTests`; draft-binding "a change outside the topic" |
| Subscription Authorization | MUST reject a subscription when the agent cannot read every topic | tested (403, Web Access Control) | `NotificationsTests` "Subscribe-time authorization"; authorization.mjs |
| Subscription Authorization | MUST NOT deliver about a resource the subscriber cannot read at the time of the event; stop for revoked access; SHOULD NOT end the whole subscription | tested (store after the step for Create and Update, before it for Delete; theorem `routed_authorized`) | `NotificationsTests` "Delivery-time authorization"; authorization.mjs "never of a member it may not read" |
| Subscription Response | `application/lws+json` with `type` and `subscription` | tested (201 with `Location`) | `NotificationsTests`; draft-binding |
| Privacy | `actor` SHOULD be omitted by default | tested (always omitted) | `NotificationsTests`; draft-binding |
| Webhook: Creating a Subscription | `type` WebhookSubscription; `inbox` REQUIRED; `expires` OPTIONAL; response `type`, `subscription`, `expires` | tested (`expires` must be a future RFC 3339 date-time, echoed) | `NotificationsTests` |
| Webhook: Authentication | SHOULD sign with RFC 9421; the key in the storage description as a `verificationMethod` referenced from `authentication` | tested (Ed25519, HACL*) | draft-binding "HTTP Message Signature verifies under the published key" |
| Webhook: Signature Requirements | covers `@method`, `@scheme`, `@authority`, `@path`, `content-type`, `content-digest` (RFC 9530); `created` and `keyid` | tested | `NotificationsTests` "Signatures"; draft-binding |
| Webhook: Subscription Management | the endpoint lists the subscriber's subscriptions as an LWS container (SHOULD page); GET and DELETE on each | tested (paged at `pageSize`; another agent's subscription is 404) | `NotificationsTests` "Subscription management"; draft-binding; authorization.mjs |
| Webhook: Notification Delivery | POST to the inbox, body `application/lws+json`; MAY retry; MAY deactivate after repeated failures | tested (3 attempts for no answer, 408, 425, 429, 5xx; 410 or 3 failed deliveries deactivate) | `NotificationsTests` "Delivery outcomes"; draft-binding "503 is tried again" |
| Access Requests: Discovery | MAY advertise; `AccessRequestService` and `AccessGrantService` service objects; SHOULD `conformsTo` the access profiles | tested (both, with `conformsTo` the Access Profile) | `lwsGuardAccessDiscovery`; draft-binding "Access Requests and Grants: the storage description advertises" |
| Access Requests: Protocol | the endpoints are LWS containers; GET and POST, DELETE RECOMMENDED; JSON-LD payloads both ways | tested (paged listing with `Link` type Container; 415 for another media type) | `AccessGrantsTests` "The endpoints are LWS containers"; draft-binding "the grant endpoint is an LWS container" |
| Access Requests: Protocol | an agent POSTs an access request; a storage controller POSTs an access grant; a successful POST MUST answer with `Location` | tested (201 with `Location`; a grant from an agent that is not the controller is 403; theorem `accessStep_grant_needs_controller`) | `lwsGuardAccessCreate`; draft-binding; authorization.mjs "only the storage controller" |
| Access Requests: Types, Storage, Inbox, Access | `type` MUST include `AccessRequest`/`AccessGrant`; `storage` REQUIRED, a URI; `inbox` OPTIONAL, a URI; `access` REQUIRED, one or more objects; `@context` MUST include the LWS context | tested (400 otherwise; `storage` must name this storage) | `AccessGrantsTests` "Incomplete or malformed grants"; draft-binding "a grant missing type..." |
| Access Profile: Types, Actions, Assignee, Targets | policy `type` MUST include `AccessPolicy`; `action` one or more of read, modify, create, delete (MUST be supported); `assignee` a URI, `foaf:Agent` MAY give public access; `target` an object with `type` and `value` | tested (400 otherwise; a grant permits exactly its actions on exactly its targets: theorems `grantsPermit_sound`, `grantAllows_sound`, `grantAllows_acl`) | `AccessGrantsTests` "Creating, reading, enforcing"; authorization.mjs "Access grants" |
| Access Profile: Constraints | each constraint has `leftOperand`, `operator`, `rightOperand`; all MUST be satisfied; MUST support `client`, `format`, `type`, `purpose`, `dateTime` | tested (`purpose` is accepted and no request satisfies it; a window that does not hold permits nothing: theorems `policyPermits_excluded`, `recordPermits_expired`) | `lwsGuardAccessConstraints`; authorization.mjs "constraints must all hold" |
| Access Requests (overview) | when a grant is created or revoked the server adjusts the access policy | tested (grants are part of `Authorization.decide`, notification checks and the type index; theorem `grantsPermit_revoke`) | authorization.mjs "revoking it ends the access", "subscribe after the revocation" |
| Access Requests: Notifications | with an `inbox`, SHOULD notify; on grant creation SHOULD notify the inbox of the associated request | tested (one `Create` notification to the grant's inbox and to the inbox of each request naming one of its assignees) | `AccessGrantsTests` "Access requests"; draft-binding "are announced there" |
| Access Requests: Notification Events | on access request creation the storage controller SHOULD be notified | missing (the draft names no controller inbox) | https://github.com/danbri/factoidal/issues/920; draft-binding xfail |
| Data resource | any bytes (images, documents) | tested: stored and returned byte for byte; RDF media types are read as UTF-8 and content that is not UTF-8 gets 400 | `lwsGuardBinaryRoundTrip`, `lwsGuardInvalidUtf8Turtle`; draft-binding "Data resources: a non-UTF-8 body round-trips byte for byte"; `tests/lws/binary-bodies.mjs` (https://github.com/danbri/factoidal/issues/889) |
| (server choice) | request paths with dot segments or encoded traversal are refused | tested | `lwsGuardTraversalRefused`; draft-binding "Paths" |
| (server choice) | storage persists under `DIR` | tested | `lwsGuardSnapshotRoundTrip`, `lwsGuardSnapshotRefusesTraversal`; draft-binding "Persistence" |

Counts: 78 tested, 2 missing, 1 not applicable (out of 81 rows). Updated
2026-10-21 for https://github.com/danbri/factoidal/issues/913: the Access Requests
row became nine rows of §Access Requests and Grants (eight tested; the
notification of the controller for a new request is missing, with an xfail,
https://github.com/danbri/factoidal/issues/920). The count line before this
update said 70 tested, 2 missing, 1 not applicable (out of 73 rows). Updated
2026-10-21 for https://github.com/danbri/factoidal/issues/914: the Discovery
`MoveResource` row and the Move activity row became tested, and nine rows of
§Moving Resources were added (eight tested; the 301 SHOULD is missing, with
an xfail). The count line before this update said 60 tested, 1 missing,
3 not applicable (out of 64 rows). The rows
Read (ETag, conditional requests), Content Negotiation, Create (container,
identity hint) and Authorization Server Discovery were made exact on
2026-10-21 for the defects the Touchstone harness found
(https://github.com/danbri/factoidal/issues/911,
`docs/designissues/2026-10-21-lws-touchstone-run.md`); the counts did not
change. Updated 2026-10-21 for https://github.com/danbri/factoidal/issues/890: the
Notifications row became 17 rows of the core "Notifications" section and the
webhook notification suite (`lws10-notifications-webhook`), 16 tested and 1
not applicable (Move); the Access Requests row is now counted as missing,
with an xfail, because it is a feature this server does not have, not a
conditional rule. The count line before this update said 44 tested, 0
missing, 4 not applicable (out of 48 rows). Updated earlier on
2026-10-21 for https://github.com/danbri/factoidal/issues/887 and
https://github.com/danbri/factoidal/issues/888: the Pagination, Create
`Link` and `Prefer: set-linkset` rows became tested, and the linkset PUT row
now states the draft's condition ("If advertised in the Allow header").
Counted with
`awk '/^## LWS editor.s draft 2026-10-19 audit/{f=1} /^Counts:/{f=0} f' docs/lws-solid-conformance.md | grep '^| ' | tail -n +3 | awk -F'|' '{print $4}' | awk '{print $1}' | sort | uniq -c`
("tested" and "tested:" are both tested; "n/a" and "n/a," are both not
applicable). The command given here before (`sed -n '/2026-10-19 audit/,/^Counts/p'`)
starts its range again at its own text after the count line, so it counted
rows of later tables too. The count line before this update said 40 tested,
4 missing, 4 not applicable; the same table counted with the command above
gives 41 tested, 3 missing, 4 not applicable (out of 48 rows).

## LWS Search and Type Index Services (lws10-index)

Source: "LWS Search and Type Index Services", W3C Linked Web Storage Working
Group editor's draft, "an unofficial proposal", w3c/lws-protocol commit
`9a08ff65` (`lws10-index/index.html`; the implementations page names it
`lws10-searchindex`). Tracking: https://github.com/danbri/factoidal/issues/912.
Lean: `L4Factoidal/LWS/TypeIndex.lean` (the index the store keeps),
`L4Factoidal/LWS/Search.lean` (the two services); `#guard`s in
`L4Factoidal/LWS/SearchTests.lean`; host checks in
`tests/lws/draft-binding.mjs` (rows "Type index", "Type search"),
`tests/lws/authorization.mjs` (row "Type search: results, totalItems and the
type index ...") and `tests/lws/scaling.mjs` (rows "type index: ...").

Endpoints (a server choice): Type Index Service
`<base>.well-known/lws-type-index`, Type Search Service
`<base>.well-known/lws-type-search`.

| section | requirement | status | test |
|---|---|---|---|
| Discovery | a storage that supports a service MUST advertise it with a service object of type `TypeIndexService` / `TypeSearchService`, with a `serviceEndpoint` | tested | `lwsGuardIndexDiscovery`; draft-binding "Type index: the storage description advertises ..." |
| Discovery | the set of indexed relations is not enumerated | tested (no response names it) | `SearchTests` "unindexed relation" guards |
| Type and Relation Derivation | types SHOULD be derived from client `Link` headers on creation or modification and from the server's native classes | tested: `rel="type"` on POST, on PUT or PATCH with `Prefer: set-linkset`, and in the linkset document; the native class of the kind | `SearchTests` §Type derivation; draft-binding "Type search: QUERY finds a type from a Link header ..." |
| Type and Relation Derivation | MAY derive types from content; content types MUST be treated identically | tested: `rdf:type` of the resource in `text/turtle` content up to 1 MiB, the same fact shape as a link (theorem `ixSearch_eq_specSearch` covers both) | `SearchTests` `/c/b`; draft-binding "Type search: QUERY finds ... from Turtle content" |
| Type and Relation Derivation | a write SHOULD be reflected within a bounded interval | tested: at once, the index is updated inside every `put` and `remove` of the store (`IndexedStore`); create, update, delete, recursive delete and move | `SearchTests` §Changes; draft-binding "Type search: a set-linkset update, a delete and a move ..." |
| GET [TypeIndexService] | a paginated `TypeIndex` in `application/lws+json`, page URIs in `Link` headers, the types the client may see | tested (theorem `visibleTypes_eq_specTypes`) | `SearchTests` type index guards; draft-binding "Type index: GET lists the types ..." |
| QUERY [TypeSearchService] | Content-Type MUST be present; `application/lws-query+json` MUST be supported; `@` members MUST be ignored | tested | `SearchTests` errors; draft-binding "Type search: Cache-Control private, ..." |
| QUERY | SHOULD advertise `Accept-Query` (OPTIONS) | tested | `SearchTests` OPTIONS guard |
| QUERY | CNF semantics of `type`: AND across elements, OR inside a nested array; an absent or empty key is no constraint; the native classes are ordinary types | tested (theorem `ixSearch_eq_specSearch`: the index answer is the filter `selects` over every path of the store) | `lwsGuardTypeSearch` |
| QUERY | MUST NOT extend the grammar; a type that matches nothing is not an error; duplicate groups MUST be ignored; an empty group MUST be 400 | tested | `SearchTests` |
| QUERY | indexed relations with the same CNF semantics; an unindexed relation and an unmatched target MUST be indistinguishable; structural or protocol relations MUST NOT be indexed | tested (`structuralRels`; the two answers are byte-identical) | `SearchTests`; draft-binding "Type search: a describedby link is an indexed relation ..." |
| QUERY | 200 with an `application/lws+json` ContainerPage by default; another format MAY be honoured; 406 when none is acceptable | tested (`application/ld+json` also) | `SearchTests`; draft-binding |
| QUERY | each item MUST carry `id` and `type` | tested (`type`: the native class name, then the declared types) | `SearchTests` item guard |
| QUERY | the result set is paginated, page URIs in `Link` headers | tested (the page URI carries the filter, base64url; each page is computed and authorized again) | `SearchTests` §Pagination; draft-binding "Type search: rel=next ..." |
| QUERY | a `Content-Location` results resource MUST be authorization-filtered on every access and MUST NOT be reused across clients | tested, OFF BY DEFAULT and UNSTABLE (option `searchResults`, https://github.com/danbri/factoidal/issues/922; see below). Theorems `resultsAnswer_authorized`, `resultsAnswer_sublist_query`, `resultsGet_creator_only` | `SearchResultsTests` (`lwsGuardResultsFiltered`, `lwsGuardResultsNotReused`); draft-binding "Type search results (unstable, issue 922): ..."; authorization.mjs "Type search results resource (unstable, issue 922): ..." |
| Errors | 400 for a body that is not well-formed, `type` not an array, an element that is neither a string nor a non-empty array of strings, a value that is not an IRI (RFC 3987); 415 with `Accept-Query`; 400 without Content-Type; 406; 422 above the limit, never narrowed (64 IRIs); 404 for an unrecognized page reference | tested | `lwsGuardSearchErrors`; draft-binding "Type search: Cache-Control private, ..." |
| Errors | a server that negotiates on Accept MUST list Accept in Vary | tested (`Vary: accept, authorization` on every answer) | `SearchTests` |
| Security and Authorization | MUST enforce authorization; unauthorized entries MUST be omitted; no type or resource disclosed without authorization | tested (theorems `searchAnswer_authorized`, `searchPagePaths_authorized`, `visibleTypes_eq_specTypes`) | `lwsGuardSearchAuthorized`; authorization.mjs "Type search: results, totalItems ..." |
| Security and Authorization | counts over the client-specific view | tested (`totalItems` is the length of the filtered answer) | `SearchTests`; authorization.mjs |
| Security and Authorization | current access on every request; revocation takes effect at once | tested (Web Access Control over the state the request is served from) | `SearchTests` revocation guard; authorization.mjs |
| Security and Authorization | MUST mark responses against reuse across clients and vary on the credential | tested (`Cache-Control: private`, `Vary: accept, authorization`) | `SearchTests`; draft-binding |
| Security and Authorization | a search is safe | proved (`serverStep_index_safe`: the state is returned unchanged). With `searchResults` on, a QUERY adds a results record and changes no resource of the storage (`SearchResults.serverStep` returns no store) | `SearchTests` "A search changes nothing" |

Counts: 22 tested, 0 missing, 0 not applicable (out of 22 rows). The
`Content-Location` row is tested only with the option on; by default no such
resource is exposed.

### Search results resource (ANTICIPATORY AND UNSTABLE, off by default)

Owner, 2026-10-21: "what do we think a Content-Location results resource
looks like? Can we draft an anticipatory impl flagged as likely unstable?"
Tracking: https://github.com/danbri/factoidal/issues/922. Lean:
`L4Factoidal/LWS/SearchResults.lean`; `#guard`s in
`L4Factoidal/LWS/SearchResultsTests.lean`. lws10-index defines no such
resource; everything in this section is likely to change.

RFC 10008 (June 2026), the text this design follows:

* §2.3: "A successful response (2xx, Section 15.3 of [HTTP]) can include a
  Content-Location header field containing an identifier for a resource
  corresponding to the results of the operation [...] This represents a
  claim from the server that a client can send a GET request for the
  indicated URI to retrieve the results of the query operation just
  performed. The indicated resource might be temporary."
* §2.4: a URI in Location "represents a claim that a client can send a GET
  request to the indicated URI to repeat the query operation just performed
  without resending the query content."
* §4: "If a server creates a temporary resource to represent the results of
  a QUERY request [...] that URI SHOULD be chosen such that it does not
  include any sensitive portions of the original request content."

So the RFC changed the design proposed in issue 922. The issue proposed a
GET that re-runs the filter; RFC 10008 gives that to the Location resource
(the equivalent resource). The Content-Location resource holds the results
of the QUERY just performed. As built:

| decision | value |
|---|---|
| when | QUERY by an authenticated agent, answer 200, option on, 16 random bytes from the host; never for an anonymous QUERY |
| name | `<base>.well-known/lws-type-search/results/<id>`, `<id>` the base64url form of 16 random bytes (128 bits); nothing of the filter is in the URI |
| record | filter, agent (token `sub`), client (token `client_id`), created, expires, the result paths of the QUERY |
| GET, HEAD | the recorded paths that a QUERY with the same filter and the same agent's current read access answers now, paged as the search (`?page=N`), `Cache-Control: private`, `Vary: accept, authorization`. A resource made after the QUERY is never listed; a deleted, retyped or no longer readable one disappears |
| other agent, other client, anonymous, unknown name | 404 (one answer for all) |
| after `searchResultsTtl` (600 s) | 410 for the creator, 404 for everyone else |
| more than `searchResultsMax` (100) records | the oldest is removed (then 404) |
| other methods | 405, `Allow: GET, HEAD, OPTIONS` |
| Location | not sent: the search's page URIs (`?q=<filter>&page=N`) already repeat the query by GET |
| discovery | extension member `https://github.com/danbri/factoidal/issues/922#unstableResultsResource` (a string saying it is unstable) on the `TypeSearchService` entry, only when on |

Theorems: `resultsAnswer_sublist_query` (the answer is a sublist of the
answer a QUERY with the same filter and the same read access gets on the same
state), `resultsAnswer_authorized`, `resultsAnswer_recorded`,
`resultsPage_mem_query`, `resultsAnswer_eq_spec`, `findFor_creator`,
`resultsGet_creator_only` (any answer other than 404 comes from a record of
this agent and this client), `resultsGet_anonymous`, `create_anonymous`,
`create_owner`, `insertBounded_length_le`, `insertBounded_mem`,
`serverStep_off` (option off: every request passes to the storage as before).

Touchstone: `type-search-content-location-protected` applies only with the
option on (`tools/lws-touchstone.sh --unstable-search-results`); record in
`docs/designissues/2026-10-21-lws-touchstone-run.md` § Search results
resource.

## Merkle hashes (optional, off by default)

Owner, 2026-10-21: "As an optional, probably default off until we settle on
stronger motivating usecase but good to have the fundamentals there".
Tracking: https://github.com/danbri/factoidal/issues/919. Design record:
`docs/designissues/2026-10-21-lws-merkle.md`. Lean:
`L4Factoidal/LWS/Merkle.lean` (hashes, maintenance, theorems),
`L4Factoidal/LWS/MerkleHttp.lean` (fields and members); `#guard`s in
`L4Factoidal/LWS/MerkleTests.lean` and `MerkleHttp.lean`.

| decision | value |
|---|---|
| resource digest | SHA-256 of the stored bytes (HACL* at run time, pure Lean FIPS 180-4 in every `#guard`) |
| container digest | SHA-256 of tag 2, the member count (8 bytes, big-endian), and the `BlockMerkle` root over the leaves `digest ++ path` of the listed members in increasing path order |
| members | the listing's: direct members that are not auxiliary resources (and longer than the container's path, true of every path `validTarget` admits) |
| maintenance | in the store (`MerkleStore`, under the type index); a write recomputes the containers above it and stops at the first unchanged digest |
| `Repr-Digest` | `sha-256=:<base64>:` on a 200 or 206 GET or HEAD of a resource answered with its stored media type and no query; the digest of the whole representation also for a range (RFC 9530 §3.1) |
| container | field `Factoidal-Merkle-Root` (the listing and every page) and the member `…/919#merkleRoot` (JSON) or the triple `<container> <…/919#merkleRoot> "sha-256=:…:"` (Turtle) |
| storage description | member `https://github.com/danbri/factoidal/issues/919#storageMerkleRoot`: the digest of the storage root container |
| who sees roots | everyone with `insecureNoAuth`; under authorization the storage controller only (`acl:Control` on the root), because a root is computed from resources a reader of the listing may not read |
| entity tags | unchanged (expected failure in `tests/lws/merkle.mjs`: a listing whose root member changed keeps its strong ETag, RFC 9110 §8.8.1) |
| snapshot | holds no hash; the hashes are rebuilt at open in one pass |

Theorems: `MkOk.dig_eq_recompute`, `MkState.dig_eq_recompute`, `rebuild_ok`,
`walk_ok`, `MkOk.upd`, `merkleStoreLaws`, `containerDigest_inj`,
`dataDigest_changes`, `parent_digest_changes`, `change_reaches_ancestor`,
`decorate_off`, and in `Storage/BlockMerkle.lean` `rootWith_inj`,
`nextLevelWith_inj`. Collision-freedom of SHA-256 is a hypothesis
(`NoCollision`, over the byte strings hashed at one path in two states).

## LWS 1.0 Core

Source: <https://w3c.github.io/lws-protocol/lws10-core/>, W3C Linked Web
Storage Working Group editor's draft, read 2026-09-06.

The draft's `Operations`, `Containers`, `Discovery`, `Authentication` and
`Authorization` sections are headings with no content, and it defines no HTTP
binding, no status codes and no test suite. Where a row needs a binding, the
Solid Protocol's binding is used and the row says so.

Score, from `lake exe l4lws-probe`:

```
guarded checks: 17 pass, 0 fail (out of 17)
registry: 11 proved, 17 guarded, 0 host-verified, 5 open (out of 33)
```

Table generated by `lake exe l4lws-probe -- --markdown`.

| id | section | statement | module | status | decided by |
|---|---|---|---|---|---|
| `lws-core-01` | Resource Access | A LWS Server is an HTTP server [RFC9112] that complies with all of the relevant "MUST" statements in this specification. | `L4Factoidal.LWS.Operations` | open | the draft's Operations, Containers, Discovery, Authentication and Authorization sections have empty bodies, so the class is not yet closed |
| `lws-core-02` | Resource Access | An LWS Client is an HTTP client [RFC9112] that complies with all of the relevant "MUST" statements in this specification. | `L4Factoidal.Solid.Client` | open | same empty sections as lws-core-01 |
| `lws-core-03` | For Editors (CG-to-ED delta) | HTTP Server MUST generate a Last-Modified header field in response to GET and HEAD requests. | `L4Factoidal.LWS.Operations.step` | guarded | lwsGuardLastModifiedOnGet, lwsGuardLastModifiedOnHead |
| `lws-core-04` | For Editors (CG-to-ED delta) | The PATCH ?insertions formulae MUST NOT contain blank nodes. | `L4Factoidal.LWS.Patch.wellFormed` | guarded | lwsGuardInsertionsRefuseBlankNodes |
| `lws-core-05` | Terminology | container — an LWS resource that is able to enumerate a collection of LWS resources, conforming to the conventions described in Section 8. Containers. | `L4Factoidal.LWS.Operations.containedPaths` | guarded | lwsGuardContainerEnumerates |
| `lws-core-06` | Terminology | storage root — a container at the root of a containment hierarchy of a storage. The storage root is the only LWS resource that does not have a parent in the LWS containment hierarchy nor a primary resource. | `L4Factoidal.LWS.Model.parent?` | proved | L4Factoidal.LWS.Tests.rootHasNoParent |
| `lws-core-07` | Terminology | auxiliary resource — an LWS resource that plays a particular role with respect to a LWS resource, called its primary resource, and whose lifetime is bound to the primary resource. | `L4Factoidal.Solid.Server.Auxiliary` | proved | L4Factoidal.Solid.Server.auxiliariesDeletedWithSubject |
| `lws-core-08` | Terminology | Auxiliary resources are discovered using web links [RFC8288] of a specific type (see Section ). | `L4Factoidal.LWS.Discovery.discoveryLinks` | guarded | lwsGuardAuxiliaryLinksAdvertised |
| `lws-core-09` | Terminology | linkset resource — a type of auxiliary resource whose representation conforms to [RFC9264]. | `L4Factoidal.LWS.Model.ResourceKind` | open | the kind and its linkset link relation exist; RFC 9264 linkset serialisation is not implemented |
| `lws-core-10` | Terminology | metadata resource — an auxiliary resource, managed by a storage, that describes an LWS resource and conforms to the conventions described in TBD. | `L4Factoidal.LWS.Model.ResourceKind` | open | the draft marks the metadata-resource conventions TBD; the kind and its describedby link exist |
| `lws-core-11` | Resource Access | An operation is any of the following actions that can be performed on a served resource: create resource, read resource, update resource, delete resource. | `L4Factoidal.LWS.Operations.step` | guarded | lwsGuardCreateReadUpdateDelete |
| `lws-core-12` | Resource Access | success - the operation is believed to have completed. This may be accompanied by a resource representation conveying the contents of a served resource. A success response is not defined for the create resource operation. See instead created. | `L4Factoidal.LWS.Operations.step` | guarded | lwsGuardCreatedIsNotSuccess |
| `lws-core-13` | Resource Access | not permitted | `L4Factoidal.Solid.Server.WAC` | guarded | solidGuardWacDenies |
| `lws-core-14` | Resource Access | unknown requester | `L4Factoidal.Solid.Server.Auth` | guarded | solidGuardSolidOidcDpop |
| `lws-core-15` | Authentication | LWS makes use of user authentication as defined in specifications for OpenID Connect, SAML 2.0, and self-signed controlled identifiers (CIDs), for example. | `L4Factoidal.Solid.Server.Auth` | guarded | solidGuardSolidOidcDpop |
| `lws-core-16` | Notifications | notification — a message describing an event that has occurred on a resource. | `L4Factoidal.LWS.Notifications` | guarded | lwsGuardNotificationsDelivered |
| `lws-core-17` | Access Requests and Grants | access grant — a data object created by a storage controller, expressing an ability for an agent to perform specific actions on storage resources within certain defined constraints. | `L4Factoidal.LWS.AccessPolicy.grantsPermit` | proved | L4Factoidal.LWS.AccessPolicy.grantsPermit_sound |
| `lws-core-18` | Terminology | storage description — an LWS resource, conforming to the requirements of a W3C Controlled Identifier document [CID-1.0], that describes a storage along with its services and capabilities. | `L4Factoidal.LWS.Discovery.storageDescriptionPath` | open | the link is advertised; the description document does not yet conform to CID 1.0 |
| `lws-core-19` | Moving Resources | On a successful update, the server MUST atomically remove the resource from the items list of its former parent container and add it to the items list of the destination container. | `L4Factoidal.LWS.Move.move` | proved | L4Factoidal.LWS.move_tree |
| `lws-index-01` | lws10-index: Discovery | A storage that supports one of these services MUST advertise it with a service object in the service array of its storage description resource: the entry for the Type Index Service MUST have a type equal to TypeIndexService, and the entry for the Type Search Service MUST have a type equal to TypeSearchService. | `L4Factoidal.LWS.Binding.storageDescription` | guarded | L4Factoidal.LWS.SearchTests.lwsGuardIndexDiscovery |
| `lws-index-02` | lws10-index: QUERY [TypeSearchService] | The type key is the mandatory baseline and MUST be supported by every server that implements the TypeSearchService. | `L4Factoidal.LWS.Search.searchStep` | guarded | L4Factoidal.LWS.SearchTests.lwsGuardTypeSearch |
| `lws-index-03` | lws10-index: Errors | A request body that is not well-formed application/lws-query+json, or whose type is not an array, or any of whose elements is neither a string nor a non-empty array of strings, MUST be rejected with 400 (Bad Request). | `L4Factoidal.LWS.Search.parseFilter` | guarded | L4Factoidal.LWS.SearchTests.lwsGuardSearchErrors |
| `lws-index-04` | lws10-index: Security and Authorization | Unauthorized entries MUST be omitted entirely. | `L4Factoidal.LWS.Search.searchAnswer` | proved | L4Factoidal.LWS.Search.searchAnswer_authorized |
| `lws-index-05` | lws10-index: Security and Authorization | A server MAY maintain a derived index for performance, but it MUST apply current authorization as a filter over that index on every request. | `L4Factoidal.LWS.Search.serverStep` | guarded | L4Factoidal.LWS.SearchTests.lwsGuardSearchAuthorized |
| `lws-index-06` | lws10-index: Type and Relation Derivation | When a server enriches the type index from resource content, the types it surfaces MUST be treated identically to those derived from Link headers for the purposes of indexing, search, and authorization filtering. | `L4Factoidal.LWS.TypeIndex.entryFacts` | proved | L4Factoidal.LWS.Search.ixSearch_eq_specSearch |
| `lws-index-07` | lws10-index: QUERY (a results resource; ANTICIPATORY AND UNSTABLE, off by default, issue 922) | this specification does not define such a resource; a server that nonetheless exposes one MUST subject it to the same authorization filtering on every access [...] | `L4Factoidal.LWS.SearchResults.resultsAnswer` | proved | L4Factoidal.LWS.SearchResults.resultsAnswer_authorized |
| `lws-index-08` | lws10-index: QUERY (a results resource; ANTICIPATORY AND UNSTABLE, off by default, issue 922) | a server that nonetheless exposes one [...] MUST prevent its reuse across clients. | `L4Factoidal.LWS.SearchResults.resultsGet` | proved | L4Factoidal.LWS.SearchResults.resultsGet_creator_only |
| `lws-access-01` | Access Requests and Grants: Discovery | When such support is advertised, a service object describing an endpoint for access requests MUST have a type equal to the string AccessRequestService, and a service object describing an endpoint for access grants MUST have a type equal to the string AccessGrantService. | `L4Factoidal.LWS.Binding.storageDescription` | guarded | L4Factoidal.LWS.AccessGrantsTests.lwsGuardAccessDiscovery |
| `lws-access-02` | Access Requests and Grants: Protocol | A successful POST operation MUST respond with a Location header set to the URL of the new resource. | `L4Factoidal.LWS.AccessGrants.accessStep` | guarded | L4Factoidal.LWS.AccessGrantsTests.lwsGuardAccessCreate |
| `lws-access-03` | Access Requests and Grants: Constraints | When multiple constraint objects are present, all of them MUST be satisfied. | `L4Factoidal.LWS.AccessPolicy.policyPermits` | guarded | L4Factoidal.LWS.AccessGrantsTests.lwsGuardAccessConstraints |
| `lws-access-04` | Access Requests and Grants | When an access grant is created or revoked (deleted), it is the responsibility of the server to adjust any underlying access policy to account for the change. | `L4Factoidal.LWS.AccessPolicy.revoke` | proved | L4Factoidal.LWS.AccessPolicy.grantsPermit_revoke |
| `lws-access-05` | Access Requests and Grants: Temporal Constraints | The gteq operator defines the start of the window and the lteq operator defines the end. | `L4Factoidal.LWS.AccessPolicy.satisfied` | proved | L4Factoidal.LWS.AccessPolicy.recordPermits_expired |
| `lws-access-06` | Access Requests and Grants: Protocol | A storage controller creates an access grant by submitting a POST request to the access grant endpoint. | `L4Factoidal.LWS.AccessGrants.accessStep` | proved | L4Factoidal.LWS.AccessGrants.accessStep_grant_needs_controller |

## Solid Protocol

Source: <https://solidproject.org/TR/protocol>, version 0.11.0, modified
2024-05-12, read 2026-09-06. Web Access Control:
<https://solidproject.org/TR/wac>.

Score, from `lake exe l4solid-probe`:

```
guarded checks: 64 pass, 0 fail (out of 64)
registry: 3 proved, 64 guarded, 3 host-verified, 7 open (out of 77)
```

Table generated by `lake exe l4solid-probe -- --markdown`.

| id | section | statement | module | status | decided by |
|---|---|---|---|---|---|
| `solid-02-01` | Solid Protocol §2.1 HTTP Server | Servers MUST conform to HTTP Semantics [RFC9110]. […] Servers MUST conform to HTTP/1.1 [RFC9112]. | `L4Factoidal.HTTP.Server (message framing) plus the Node host` | host-verified | tests/solid/server/protocol.mjs — the framing is the host's; the engine sees a parsed request |
| `solid-02-02` | Solid Protocol §2.1 HTTP Server | Server MUST reject PUT, POST, and PATCH requests that contain content but lack the Content-Type header field, with a status code of 400. | `L4Factoidal.Solid.Server.Methods.step` | guarded | solidGuardContentTypeRequired400 |
| `solid-02-03` | Solid Protocol §2.1 HTTP Server | When a client does not provide valid credentials when requesting a resource that requires it (see WebID), servers MUST send a response with a 401 status code (unless 404 is preferred for security reasons). | `L4Factoidal.Solid.Server.Methods.step` | guarded | solidGuardWacEnforced |
| `solid-02-04` | Solid Protocol §2.1 HTTP Server | When both http and https URI schemes are supported, the server MUST redirect all http URIs to their https counterparts using a response with a 301 status code and a Location header. | `(the host)` | host-verified | tests/solid/server/protocol.mjs — the scheme is the listener's, not the engine's |
| `solid-02-05` | Solid Protocol §2.1 HTTP Server | Server MUST generate a Content-Type header field in a message that contains content. | `L4Factoidal.LWS.Operations.readHeaders` | guarded | solidGuardAcceptHeaders |
| `solid-02-06` | Solid Protocol §2.2 HTTP Client | Clients MUST use the Content-Type HTTP header field in PUT, POST, and PATCH requests that contain content [RFC9110]. | `L4Factoidal.Solid.Client.Requests.buildRequest` | proved | L4Factoidal.Solid.Client.buildRequest_contentTypePresent |
| `solid-03-01` | Solid Protocol §3.1 URI Slash Semantics | Paths ending with a slash denote a container resource. | `L4Factoidal.LWS.Model.pathIsContainer` | guarded | solidGuardContainment |
| `solid-03-02` | Solid Protocol §3.1 URI Slash Semantics | If two URIs differ only in the trailing slash, and the server has associated a resource with one of them, then the other URI MUST NOT correspond to another resource. Instead, the server MAY respond to requests for the latter URI with a 301 redirect to the former. | `L4Factoidal.Solid.Server.Storage.slashRedirect?` | guarded | solidGuardSlashRedirect |
| `solid-03-03` | Solid Protocol §3.1 URI Slash Semantics | Servers MUST authorize prior to this optional redirect. | `L4Factoidal.Solid.Server.Methods.step` | guarded | solidGuardWacEnforced |
| `solid-04-01` | Solid Protocol §4.1 Storage Resource | Servers MUST provide one or more storages. | `L4Factoidal.Solid.Server.Storage.storageRootPath` | guarded | solidGuardStorageTypeLink |
| `solid-04-02` | Solid Protocol §4.1 Storage Resource | When a server supports multiple storages, the URIs MUST be allocated to non-overlapping space. | `Wasm/Ops/Solid.lean (one storage per handle)` | host-verified | tests/solid/server/protocol.mjs — two storages are two handles with different base IRIs |
| `solid-04-03` | Solid Protocol §4.1 Storage Resource | Servers MUST advertise the storage resource by including the HTTP Link header field with rel="type" targeting http://www.w3.org/ns/pim/space#Storage when responding to storage's request URI. | `L4Factoidal.LWS.Discovery.discoveryLinks` | guarded | solidGuardStorageTypeLink |
| `solid-04-04` | Solid Protocol §4.1 Storage Resource | Servers MUST include the Link header field with rel="http://www.w3.org/ns/solid/terms#storageDescription" targeting the URI of the storage description resource in the response of HTTP GET, HEAD and OPTIONS requests targeting a resource in a storage. | `L4Factoidal.LWS.Discovery.discoveryLinks` | guarded | solidGuardStorageDescriptionLink |
| `solid-04-05` | Solid Protocol §4.1 Storage Resource | Servers MUST include statements about the storage as part of the storage description resource. | `L4Factoidal.Solid.Server.Storage.storageDescriptionGraph` | open | the graph is built; the storage description resource is not yet served at its own path |
| `solid-04-06` | Solid Protocol §4.1 Storage Resource | Servers MUST keep track of at least one owner of a storage in an implementation defined way. | `L4Factoidal.LWS.Operations.Config.owner` | guarded | solidGuardOwnerLink |
| `solid-04-07` | Solid Protocol §4.1 Storage Resource | When a server wants to advertise the owner of a storage, the server MUST include the Link header field with rel="http://www.w3.org/ns/solid/terms#owner" targeting the URI of the owner in the response of HTTP HEAD or GET requests targeting the root container. | `L4Factoidal.LWS.Discovery.discoveryLinks` | guarded | solidGuardOwnerLink |
| `solid-04-15` | Solid Protocol §4.1 Storage Resource | Clients can determine the storage of a resource by moving up the URI path hierarchy until the response includes a Link header field with rel="type" targeting http://www.w3.org/ns/pim/space#Storage. | `L4Factoidal.Solid.Client.Discovery.storageStepOf, Responses.storageReading` | guarded | solidGuardClientStorageWalkSteps |
| `solid-04-08` | Solid Protocol §4.2 Resource Containment | There is a 1-1 correspondence between containment triples and relative reference within the path name hierarchy. | `L4Factoidal.Solid.Server.Containment` | proved | L4Factoidal.Solid.Server.containerOfChildUnique, containedByParent, memContainedPaths_iff |
| `solid-04-09` | Solid Protocol §4.2 Resource Containment | The representation and behaviour of containers in Solid corresponds to LDP Basic Container and MUST be supported by server. | `L4Factoidal.Solid.Server.Containment.containerGraph` | guarded | solidGuardContainment |
| `solid-04-10` | Solid Protocol §4.2.1 Contained Resource Metadata | Servers SHOULD include resource metadata about contained resources as part of the container description, unless that information is inapplicable to the server. | `L4Factoidal.Solid.Server.Containment.containedMetadata` | guarded | solidGuardContainment |
| `solid-04-11` | Solid Protocol §4.3 Auxiliary Resources | Servers MUST support auxiliary resources defined by this specification and manage the association between a subject resource and auxiliary resources. When a subject resource is deleted its auxiliary resources are also deleted by the server. | `L4Factoidal.Solid.Server.Auxiliary` | proved | L4Factoidal.Solid.Server.auxiliariesDeletedWithSubject |
| `solid-04-12` | Solid Protocol §4.3 Auxiliary Resources | Servers MUST advertise auxiliary resources associated with a subject resource by responding to HEAD and GET requests by including the HTTP Link header field with the rel parameter [RFC8288]. | `L4Factoidal.LWS.Discovery.discoveryLinks` | guarded | solidGuardAuxiliaryLinks |
| `solid-04-13` | Solid Protocol §4.3.2 Description Resource | Servers MUST NOT directly associate more than one description resource to a subject resource. | `L4Factoidal.Solid.Server.Auxiliary.auxiliaryPaths` | guarded | solidGuardDescriptionAuthorizedAsSubject |
| `solid-04-14` | Solid Protocol §4.3.2 Description Resource | When an HTTP request targets a description resource, the server MUST apply the authorization rule that is used for the subject resource with which the description resource is associated. | `L4Factoidal.Solid.Server.Auxiliary.authorizationSubject` | guarded | solidGuardDescriptionAuthorizedAsSubject |
| `solid-05-01` | Solid Protocol §5 Reading and Writing Resources | Servers MUST respond with the 405 status code to requests using HTTP methods that are not supported by the target resource. | `L4Factoidal.LWS.Operations.step` | guarded | solidGuardUnsupportedMethod405 |
| `solid-05-02` | Solid Protocol §5.1 Resource Type Heuristics | When a successful POST request creates a resource, the server MUST assign a URI to that resource. | `L4Factoidal.LWS.Operations.assignedName` | guarded | solidGuardPostAssignsName |
| `solid-05-03` | Solid Protocol §5.2 Reading Resources | Servers MUST support the HTTP GET, HEAD and OPTIONS methods [RFC9110] for clients to read resources or to determine communication options. | `L4Factoidal.LWS.Operations.step` | guarded | solidGuardAllowHeader |
| `solid-05-04` | Solid Protocol §5.2 Reading Resources | Servers MUST indicate the HTTP methods supported by the target resource by generating an Allow header field in successful responses. | `L4Factoidal.LWS.Operations.allowFor` | guarded | solidGuardAllowHeader |
| `solid-05-05` | Solid Protocol §5.2 Reading Resources | When responding to authorized requests, servers MUST indicate supported media types in the HTTP Accept-Patch [RFC5789], Accept-Post [LDP] and Accept-Put [The Accept-Put Response Header] response header fields that correspond to acceptable HTTP methods listed in Allow header field value in response to HTTP GET, HEAD and OPTIONS requests. | `L4Factoidal.LWS.Operations.readHeaders` | guarded | solidGuardAcceptHeaders |
| `solid-05-06` | Solid Protocol §5.3 Writing Resources | Servers MUST support the HTTP PUT, POST and PATCH methods [RFC9110]. | `L4Factoidal.Solid.Server.Methods.step` | guarded | solidGuardPostAssignsName |
| `solid-05-07` | Solid Protocol §5.3 Writing Resources | Servers MUST create intermediate containers and include corresponding containment triples in container representations derived from the URI path component of PUT and PATCH requests. | `L4Factoidal.LWS.Operations.ensureAncestors` | guarded | solidGuardIntermediateContainers |
| `solid-05-08` | Solid Protocol §5.3 Writing Resources | Servers MUST allow creation of new resources by a POST request to a URI path ending with /. Servers MUST create resources with URI paths ending with /{id} in container /. | `L4Factoidal.LWS.Operations.step` | guarded | solidGuardPostAssignsName |
| `solid-05-09` | Solid Protocol §5.3 Writing Resources | When a POST method request targets a resource without an existing representation, the server MUST respond with the 404 status code. | `L4Factoidal.LWS.Operations.step` | guarded | solidGuardPostMissingTarget404 |
| `solid-05-10` | Solid Protocol §5.3 Writing Resources | When a PUT or PATCH request targets an auxiliary resource, the server MUST create or update it. | `L4Factoidal.Solid.Server.Methods.step` | guarded | solidGuardPutAuxiliary |
| `solid-05-11` | Solid Protocol §5.3 Writing Resources | Servers MUST NOT allow HTTP PUT or PATCH on a container to update its containment triples; if the server receives such a request, it MUST respond with a 409 status code. | `L4Factoidal.Solid.Server.Methods.bodyEditsContainment` | guarded | solidGuardPutRefusesContainmentEdit409 |
| `solid-05-12` | Solid Protocol §5.3 Writing Resources | Servers MUST NOT allow HTTP POST, PUT and PATCH to update a container's resource metadata statements; if the server receives such a request, it MUST respond with a 409 status code. | `L4Factoidal.Solid.Server.Methods.step` | open | the containment-triple half of the rule is decided; server-managed metadata statements of a container are not yet distinguished from author-supplied ones |
| `solid-05-13` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | Servers MUST accept a PATCH request with an N3 Patch body when the target of the request is an RDF document [RDF11-CONCEPTS]. | `L4Factoidal.Solid.Server.N3Patch` | guarded | solidGuardN3PatchApplies |
| `solid-05-14` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | Servers MUST indicate support of N3 Patch by listing text/n3 as a field value of the Accept-Patch header field [RFC5789] of relevant responses. | `L4Factoidal.LWS.Operations.readHeaders` | guarded | solidGuardN3PatchAcceptPatch |
| `solid-05-15` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | When present, ?deletions, ?insertions, and ?conditions MUST be non-nested cited formulae [N3] consisting only of triples and/or triple patterns [SPARQL11-QUERY]. | `L4Factoidal.Solid.Server.N3Patch.takeToBrace` | guarded | solidGuardN3PatchBlankNode422 |
| `solid-05-16` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | A patch resource MUST contain a triple ?patch rdf:type solid:InsertDeletePatch. | `L4Factoidal.Solid.Server.N3Patch.parseN3Patch` | guarded | solidGuardPatchMediaType415 |
| `solid-05-17` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | The ?insertions and ?deletions formulae MUST NOT contain variables that do not occur in the ?conditions formula. | `L4Factoidal.LWS.Patch.wellFormed` | guarded | lwsGuardInsertionsRefuseBlankNodes (L4Factoidal.LWS.Tests) |
| `solid-05-18` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | The ?insertions and ?deletions formulae MUST NOT contain blank nodes. | `L4Factoidal.LWS.Patch.wellFormed` | guarded | solidGuardN3PatchBlankNode422 |
| `solid-05-19` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | Servers MUST respond with a 422 status code [RFC4918] if a patch document does not satisfy all of the above constraints. | `L4Factoidal.Solid.Server.N3Patch.N3PatchError.status` | guarded | solidGuardN3PatchBlankNode422 |
| `solid-05-20` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | When ?conditions is non-empty, servers MUST treat the request as a Read operation. When ?insertions is non-empty, servers MUST (also) treat the request as an Append operation. When ?deletions is non-empty, servers MUST treat the request as a Read and Write operation. | `L4Factoidal.LWS.Patch.patchOperations` | guarded | solidGuardN3PatchOperations |
| `solid-05-21` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | If no such mapping exists, or if multiple mappings exist, the server MUST respond with a 409 status code. | `L4Factoidal.LWS.Patch.applyPatch` | guarded | solidGuardN3PatchNoMatch409, solidGuardN3PatchMultipleMatch409 |
| `solid-05-22` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | If the set of triples resulting from ?deletions is non-empty and the dataset does not contain all of these triples, the server MUST respond with a 409 status code. | `L4Factoidal.LWS.Patch.applyPatch` | guarded | solidGuardN3PatchDeletionsAbsent409 |
| `solid-05-30` | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches, with RFC 3986 §5.1.3 | The base URI of a representation is the URI used to retrieve it. (RFC 3986 §5.1.3 Base URI from the Retrieval URI; the Solid Protocol states no base of its own, and its own N3 Patch examples and every client use relative references such as <> and <#it>.) | `L4Factoidal.Solid.Server.N3Patch.parseFormula` | guarded | solidGuardN3PatchRelativeIri |
| `solid-05-23` | Solid Protocol §5.4 Deleting Resources | Servers MUST support the HTTP DELETE method [RFC9110]. | `L4Factoidal.LWS.Operations.step` | guarded | solidGuardDeleteRemovesContainment |
| `solid-05-24` | Solid Protocol §5.4 Deleting Resources | When a DELETE request targets storage's root container or its associated ACL resource, the server MUST respond with the 405 status code. Server MUST exclude the DELETE method in the field value of the Allow header field, in response to requests to these resources. | `L4Factoidal.Solid.Server.Methods.step` | guarded | solidGuardDeleteRootRefused405 |
| `solid-05-25` | Solid Protocol §5.4 Deleting Resources | When a contained resource is deleted, the server MUST also remove the corresponding containment triple. | `L4Factoidal.Solid.Server.Containment.containmentTriples` | guarded | solidGuardDeleteRemovesContainment |
| `solid-05-26` | Solid Protocol §5.4 Deleting Resources | When a contained resource is deleted, the server MUST also delete the associated auxiliary resources. | `L4Factoidal.Solid.Server.Auxiliary.deleteWithAuxiliaries` | guarded | solidGuardDeleteRemovesAuxiliaries |
| `solid-05-27` | Solid Protocol §5.4 Deleting Resources | When a DELETE request targets a container, the server MUST delete the container if it contains no resources. If the container contains resources, the server MUST respond with the 409 status code. | `L4Factoidal.LWS.Operations.step` | guarded | solidGuardDeleteNonEmptyContainer409 |
| `solid-05-28` | Solid Protocol §5.5 Resource Representations | When a server creates an RDF source on HTTP PUT, POST, or PATCH requests, the server MUST satisfy GET requests on this resource when the Accept header field requests text/turtle or application/ld+json. | `L4Factoidal.Solid.Server.Representation.convertRdfSource` | guarded | solidGuardTurtleAsJsonLd, solidGuardJsonLdAsTurtle, solidGuardContainerNegotiated |
| `solid-05-29` | Solid Protocol §5.5 Resource Representations | When a PUT, POST, PATCH or DELETE method request targets a representation URL that is different than the resource URL, the server MUST respond with a 307 or 308 status code. | `(none)` | open | this server has no separate representation URLs, so the condition never arises; it becomes a rule when content negotiation adds them |
| `solid-06-01` | Solid Protocol §6 Linked Data Notifications | A Solid server MUST conform to the LDN specification by implementing the Receiver parts to receive notifications, and MAY implement the Sender or Consumer parts. | `L4Factoidal.Solid.Server.Ldn` | guarded | solidGuardInboxAcceptsPost |
| `solid-06-02` | Solid Protocol §6 Linked Data Notifications | A Solid client MUST conform to the LDN specification by implementing the Sender or Consumer parts to send or read notifications. | `L4Factoidal.Solid.Client.Discovery.inboxOf?` | guarded | solidGuardClientReadsLinks |
| `solid-06-03` | Linked Data Notifications §3.1 Discovery | make an HTTP HEAD or GET request on the target URL, and use the Link header with a rel value of http://www.w3.org/ns/ldp#inbox […] A resource MUST advertise only one Inbox. | `L4Factoidal.Solid.Server.Ldn.inboxLinks` | guarded | solidGuardInboxAdvertised |
| `solid-07-01` | Solid Protocol §7.1 Solid Notifications Protocol | Servers MUST conform to the Solid Notifications Protocol by implementing the Resource Server, Subscription Server, Notification Sender and Notification Receiver. | `(none)` | open | not in the first slice; the design record lists notification channels as later work |
| `solid-08-01` | Solid Protocol §8.1 CORS Server | A server MUST implement the CORS protocol [FETCH] such that browsers allow Solid apps to send any request and combination of request headers to the server, and allow the app to read any response and response headers received from the server. | `L4Factoidal.Solid.Server.Cors` | guarded | solidGuardCorsHeaders |
| `solid-08-02` | Solid Protocol §8.1 CORS Server | The server MUST set the Access-Control-Allow-Origin header field value to the valid Origin header field value from the request and list Origin in the Vary header field value. | `L4Factoidal.Solid.Server.Cors.corsHeaders` | guarded | solidGuardCorsHeaders |
| `solid-08-03` | Solid Protocol §8.1 CORS Server | The server MUST make all used response headers readable for the Solid app through Access-Control-Expose-Headers. | `L4Factoidal.Solid.Server.Cors.exposedHeaders` | guarded | solidGuardCorsHeaders |
| `solid-08-04` | Solid Protocol §8.1 CORS Server | A server MUST also support the HTTP OPTIONS method such that it can respond appropriately to CORS preflight requests. | `L4Factoidal.Solid.Server.Cors.isPreflight` | guarded | solidGuardCorsPreflight |
| `solid-09-01` | Solid Protocol §9.1 WebID | When a WebID is dereferenced, server provides a representation of the WebID Profile in an RDF document. | `L4Factoidal.Solid.Client.Profile` | guarded | solidGuardClientProfile |
| `solid-10-01` | Solid Protocol §10.1 Solid-OIDC | Servers MUST conform to the Solid-OIDC specification. | `L4Factoidal.Solid.Server.Auth` | guarded | solidGuardSolidOidcDpop |
| `solid-11-01` | Solid Protocol §11 Authorization | Servers MUST conform to either or both Web Access Control and Access Control Policy specifications. | `L4Factoidal.Solid.Server.WAC` | guarded | solidGuardWacEnforced |
| `solid-wac-01` | Web Access Control §5.3 Authorization Evaluation | Access is granted when conforming Authorizations are matched, otherwise access is denied. | `L4Factoidal.Solid.Server.WAC.decideAccess` | guarded | solidGuardWacDenies |
| `solid-wac-02` | Web Access Control §5.3.3 Authorization Matching | Match an Authorization with a specific resource, agent and access mode. | `L4Factoidal.Solid.Server.WAC.decideAccess` | guarded | solidGuardWacAccessToAgentMode |
| `solid-wac-03` | Web Access Control §5.3.3 Authorization Matching | Match an Authorization with a specific container resource, agent class membership and access mode. | `L4Factoidal.Solid.Server.WAC.decideAccess` | guarded | solidGuardWacDefaultAgentClassSuperclassMode |
| `solid-wac-04` | Web Access Control §5.3.3 Authorization Matching | Match an Authorization with a specific resource, agent with any group membership, and specific access mode. | `L4Factoidal.Solid.Server.WAC.subjectMatches` | guarded | solidGuardWacAgentGroup |
| `solid-wac-05` | Web Access Control §5.1 Effective ACL Resource Algorithm | If resource has an associated aclResource with a representation, return aclResource. Otherwise, repeat the steps using the container resource of resource. | `L4Factoidal.Solid.Server.WAC.effectiveAcl` | guarded | solidGuardWacEnforced |
| `solid-wac-06` | Web Access Control §5.3.2 Web Origin Authorization | When a server participates in the CORS protocol [FETCH] and authorization is granted to an HTTP request including the Origin header, the server MUST include the HTTP Access-Control-Allow-Origin and Access-Control-Allow-Headers headers in the response of the HTTP request. | `L4Factoidal.Solid.Server.WAC.subjectMatches, Cors.corsHeaders` | open | the CORS fields are generated; the acl:origin CONDITION on the access decision is read into the model but not applied |
| `solid-wac-07` | Web Access Control §5.3.4 Access Privileges | Servers MUST advertise client's access privileges on a resource by including the WAC-Allow HTTP header in the response of HTTP GET and HEAD requests. | `L4Factoidal.Solid.Server.WAC.wacAllow` | guarded | solidGuardWacAllowHeader |
| `solid-wac-08` | Web Access Control §5.3.4 Access Privileges | Clients MUST discover access privileges on a resource by making an HTTP GET or HEAD request on the target resource, and checking the WAC-Allow header value for access parameters listing the allowed access modes per permission group. | `L4Factoidal.Solid.Client.Responses.parseWacAllow` | guarded | solidGuardClientWacAllowParsing |
| `solid-wac-09` | Web Access Control §3.1 ACL Resource Discovery | Clients MUST discover the ACL resource associated with a resource by making an HTTP request on the target URL, and checking the HTTP Link header with the rel parameter. […] Clients MUST NOT derive the URI of the ACL resource through string operations on the URI of the resource. | `L4Factoidal.Solid.Client.Discovery.aclOf?` | guarded | solidGuardClientReadsLinks |
| `solid-wac-10` | Web Access Control §3.2 ACL Resource Representation | Root container ACL resources MUST have representations. The ACL resource of the root container MUST include an Authorization allowing the acl:Control access privilege. | `(none)` | open | a storage is created without a root ACL; enforcement is therefore off by default (ServerConfig.enforceWac) and a root ACL is a host provisioning step |
| `solid-cl-01` | Solid Protocol §4.1 Storage Resource | Clients can determine the storage of a resource by moving up the URI path hierarchy until the response includes a Link header field with rel="type" targeting http://www.w3.org/ns/pim/space#Storage. | `L4Factoidal.Solid.Client.Discovery.storageWalk` | guarded | solidGuardClientStorageWalk |
| `solid-cl-02` | RFC 9110 §5.1 Field Names, RFC 8288 §3 Link Serialisation in HTTP Headers | Field names are case-insensitive. […] The Link header field provides a means for serialising one or more links into HTTP headers, [where] each link-value is separated by a comma and the parameters of a link-value by a semicolon; a comma or semicolon inside a URI-Reference or a quoted-string is not a separator. | `L4Factoidal.Solid.Client.Discovery.linksOf, Responses.headerOf` | guarded | solidGuardClientLinkFieldShapes |

## Host tests

The host side of both protocols is `npm/factoidal/lws/`,
`npm/factoidal/solid/server/` and `npm/factoidal/solid/client/`. Those
files decide nothing: they accept a socket, turn one request into the
JSON record above, call one operation, and write the answer back. What
the suites below gate is therefore the ROUND TRIP — that a request
reaching a socket arrives at the engine as the record this ABI states,
and that the engine's answer reaches the wire with its status, its
repeated headers and its body intact. The engine's decisions in
isolation are the `#guard`s of `Tests.lean`.

Scores are "N pass, M fail, S skipped (out of T)". The WebAssembly module
is rebuilt by whoever owns the Lean side; a module without these
operations answers `unknown op`, and every suite then probes once and
SKIPS each check by name with that reason printed. A skip is never a pass.

| file | runtimes | what it covers |
|---|---|---|
| `tests/lws/server.mjs` | Node, Deno | the server binds an ephemeral port; PUT creates a data resource; GET reads it back with `Last-Modified`; HEAD carries `Last-Modified` and no body; PUT updates it and `Last-Modified` moves; DELETE removes it; GET after DELETE answers 404; a PATCH whose insertion formula holds a blank node is refused with a 4xx |
| `tests/solid/server/protocol.mjs` | Node, Deno | the storage root advertises `pim:Storage` by `Link rel=type` (§4.1); OPTIONS reports `Allow`, `Accept-Post`, `Accept-Patch`, `Accept-Put` (§4.3); PUT creates a resource and its container gains the containment triple (§5.3); POST assigns a name and reports it in `Location` (§5.4); a PUT that edits a containment triple is refused with 409 (§5.3); DELETE on the storage root is refused with 405 (§5.5); a resource advertises its `describedby` auxiliary and the auxiliary dies with its subject (§4.2); PATCH applies an N3 Patch (§5.6); a CORS preflight is answered with the allow headers (§6); the LDN inbox is advertised and accepts a notification (§7) |
| `tests/lws/encryption.mjs` | Node | encryption at rest (https://github.com/danbri/factoidal/issues/921), for `lws-serve` and `solid-serve`: the sealed file names the key id and holds no clear text; restart with the key (hex and base64url forms); a new nonce per write; a wrong key, every one-byte change of the file, a truncated file, a shortened ciphertext, a clear-text file with a key, a sealed file without one and a key of the wrong length are each refused at open; with no key a clear-text storage behaves as before; the CLI with `FACTOIDAL_LWS_KEY` |
| `tests/lws/merkle.mjs` | Node | the optional Merkle hashes (https://github.com/danbri/factoidal/issues/919): `Repr-Digest` against `node:crypto` SHA-256 (text, binary, range, HEAD); the container field equals its JSON member and its Turtle statement; the storage description root; a deep write, a move and a delete change the roots above them and no other; a restart rebuilds the same hashes and the snapshot holds none; off by default nothing is added; ETags equal with the option on and off; under authorization only the controller sees roots; `lws-serve --merkle`. One xfail (issue 919): a container ETag does not follow its root |
| `tests/solid/client/against-own-server.mjs` | Node, Deno | our client at an in-process instance of our server: `discoverStorage`, `replace`, `read`, `create` with a `Location`, `delete`, that a deleted resource is gone while its POSTed sibling survives, and that every request reached the socket through the engine |
| `tests/solid/client/against-community-server.mjs` | Node | the same five operations with the far end replaced by Community Solid Server, so a misreading our own two sides share cannot pass. Driven by `tools/solid-client-interop.sh` |

Interop scripts, all three exiting `0` passed, `1` failed, `2` could not
run here with the reason printed — never a green skip:

| script | suite | condition it needs |
|---|---|---|
| `tools/solid-server-interop.sh` | `solid-crud-tests`, `web-access-control-tests` | the Solid server operations; `npm ci` for each suite; the access-control suite additionally logs in through an external Solid-OIDC issuer before its first request |
| `tools/solid-client-interop.sh` | our client against Community Solid Server | the Solid client operations; `npx`; 2 GB free for the ~250 MB download |
| `tools/solid-conformance-harness.sh` | `solid-specification-tests` | a Docker daemon and a `SOLID_HARNESS_ENV` credentials file |

Measured 2026-09-06 against the committed WebAssembly module, which does
not carry these operations: `tests/lws/server.mjs` 0 pass, 0 fail, 8
skipped (out of 8); `tests/solid/server/protocol.mjs` 0 pass, 0 fail, 12
skipped (out of 12); `tests/solid/client/against-own-server.mjs` 0 pass,
0 fail, 7 skipped (out of 7); all three interop scripts exit 2.

## F* statement list

The F* tree states the same requirement identifiers over an abstract
resource store: [`formal/fstar/LWS.Core.Spec.fsti`](../formal/fstar/LWS.Core.Spec.fsti)
with its model and proofs in `LWS.Core.Spec.fst`, and
[`formal/fstar/Solid.Protocol.Spec.fsti`](../formal/fstar/Solid.Protocol.Spec.fsti)
which imports it and adds the Solid layer, its server statements in Part 8
and its client statements in Part 9. The list below is generated from
[`formal/fstar/LWS.Solid.Registry.fst`](../formal/fstar/LWS.Solid.Registry.fst),
whose rows carry the same identifiers and the same verbatim statements as the
Lean registries, and which proves that no identifier appears twice.

The F* modules are specifications, not an engine: each one declares the
operations over an abstract store and states the requirement as a `val` or a
lemma, and the accompanying `.fst` gives one model that discharges every law.
The engine is the Lean tree. A row with no F* statement is one the F* side
does not state yet; the Lean rows above say how that row is decided.

Verified with z3 4.13.3, no `--lax` and no `--admit_smt_queries`:
`fstar.exe --z3version 4.13.3 --cache_checked_modules <module>`.

51 of the 91 rows carry an F* statement (18 LWS rows: 10 stated;
73 Solid rows: 41 stated).

| requirement | source | section | F* statement |
|---|---|---|---|
| `lws-core-01` | LWS | Resource Access | - |
| `lws-core-02` | LWS | Resource Access | - |
| `lws-core-03` | LWS | For Editors (CG-to-ED delta) | `LWS.Core.Spec.lws_core_03_last_modified_on_get`, `LWS.Core.Spec.lws_core_03_last_modified_on_head` |
| `lws-core-04` | LWS | For Editors (CG-to-ED delta) | `LWS.Core.Spec.lws_core_04_insertions_no_blank_nodes`, `LWS.Core.Spec.lws_core_04_ill_formed_patch_refused` |
| `lws-core-05` | LWS | Terminology | `LWS.Core.Spec.lws_core_05_create_updates_containment`, `LWS.Core.Spec.lws_core_05_delete_updates_containment`, `LWS.Core.Spec.contained_are_children` |
| `lws-core-06` | LWS | Terminology | `LWS.Core.Spec.lws_core_06_root_has_no_parent`, `LWS.Core.Spec.lws_core_06_only_root_has_no_parent`, `LWS.Core.Spec.containment_acyclic`, `LWS.Core.Spec.containment_single_parent`, `LWS.Core.Spec.lws_core_root_not_deleted` |
| `lws-core-07` | LWS | Terminology | `Solid.Protocol.Spec.solid_04_11_auxiliaries_deleted_with_subject` |
| `lws-core-08` | LWS | Terminology | `LWS.Core.Spec.lws_core_08_auxiliary_links_advertised` |
| `lws-core-09` | LWS | Terminology | - |
| `lws-core-10` | LWS | Terminology | - |
| `lws-core-11` | LWS | Resource Access | `LWS.Core.Spec.lws_core_11_four_operations` |
| `lws-core-12` | LWS | Resource Access | `LWS.Core.Spec.lws_core_12_created_is_not_success` |
| `lws-core-13` | LWS | Resource Access | `Solid.Protocol.Spec.solid_wac_01_no_acl_denies` |
| `lws-core-14` | LWS | Resource Access | - |
| `lws-core-15` | LWS | Authentication | - |
| `lws-core-16` | LWS | Notifications | - |
| `lws-core-17` | LWS | Access Requests and Grants | - |
| `lws-core-18` | LWS | Terminology | `LWS.Core.Spec.lws_core_18_storage_description_link` |
| `solid-02-01` | Solid | Solid Protocol §2.1 HTTP Server | - |
| `solid-02-02` | Solid | Solid Protocol §2.1 HTTP Server | `Solid.Protocol.Spec.solid_02_02_content_type_required` |
| `solid-02-03` | Solid | Solid Protocol §2.1 HTTP Server | - |
| `solid-02-04` | Solid | Solid Protocol §2.1 HTTP Server | - |
| `solid-02-05` | Solid | Solid Protocol §2.1 HTTP Server | - |
| `solid-02-06` | Solid | Solid Protocol §2.2 HTTP Client | `Solid.Protocol.Spec.solid_02_06_client_content_type` |
| `solid-03-01` | Solid | Solid Protocol §3.1 URI Slash Semantics | `Solid.Protocol.Spec.solid_03_01_slash_denotes_container` |
| `solid-03-02` | Solid | Solid Protocol §3.1 URI Slash Semantics | `Solid.Protocol.Spec.solid_03_02_slash_pair_distinct` |
| `solid-03-03` | Solid | Solid Protocol §3.1 URI Slash Semantics | - |
| `solid-04-01` | Solid | Solid Protocol §4.1 Storage Resource | - |
| `solid-04-02` | Solid | Solid Protocol §4.1 Storage Resource | - |
| `solid-04-03` | Solid | Solid Protocol §4.1 Storage Resource | `Solid.Protocol.Spec.solid_04_03_storage_type_link` |
| `solid-04-04` | Solid | Solid Protocol §4.1 Storage Resource | `Solid.Protocol.Spec.solid_04_04_storage_description_link` |
| `solid-04-05` | Solid | Solid Protocol §4.1 Storage Resource | - |
| `solid-04-06` | Solid | Solid Protocol §4.1 Storage Resource | - |
| `solid-04-07` | Solid | Solid Protocol §4.1 Storage Resource | `Solid.Protocol.Spec.solid_04_07_owner_link` |
| `solid-04-08` | Solid | Solid Protocol §4.2 Resource Containment | `Solid.Protocol.Spec.solid_04_08_containment_iff_enumerated`, `Solid.Protocol.Spec.solid_04_08_containment_is_hierarchy` |
| `solid-04-09` | Solid | Solid Protocol §4.2 Resource Containment | - |
| `solid-04-10` | Solid | Solid Protocol §4.2.1 Contained Resource Metadata | - |
| `solid-04-11` | Solid | Solid Protocol §4.3 Auxiliary Resources | `Solid.Protocol.Spec.solid_04_11_auxiliaries_deleted_with_subject` |
| `solid-04-12` | Solid | Solid Protocol §4.3 Auxiliary Resources | `Solid.Protocol.Spec.solid_04_12_auxiliary_links_advertised` |
| `solid-04-13` | Solid | Solid Protocol §4.3.2 Description Resource | `Solid.Protocol.Spec.solid_04_13_at_most_one_description` |
| `solid-04-14` | Solid | Solid Protocol §4.3.2 Description Resource | `Solid.Protocol.Spec.solid_04_14_description_authorized_as_subject` |
| `solid-05-01` | Solid | Solid Protocol §5 Reading and Writing Resources | `Solid.Protocol.Spec.solid_05_01_unsupported_method_405` |
| `solid-05-02` | Solid | Solid Protocol §5.1 Resource Type Heuristics | `Solid.Protocol.Spec.solid_05_02_post_assigns_uri` |
| `solid-05-03` | Solid | Solid Protocol §5.2 Reading Resources | - |
| `solid-05-04` | Solid | Solid Protocol §5.2 Reading Resources | `Solid.Protocol.Spec.solid_05_04_allow_header` |
| `solid-05-05` | Solid | Solid Protocol §5.2 Reading Resources | `Solid.Protocol.Spec.solid_05_05_accept_headers` |
| `solid-05-06` | Solid | Solid Protocol §5.3 Writing Resources | - |
| `solid-05-07` | Solid | Solid Protocol §5.3 Writing Resources | `Solid.Protocol.Spec.solid_05_07_intermediate_container` |
| `solid-05-08` | Solid | Solid Protocol §5.3 Writing Resources | `Solid.Protocol.Spec.solid_05_02_post_assigns_uri` |
| `solid-05-09` | Solid | Solid Protocol §5.3 Writing Resources | `Solid.Protocol.Spec.solid_05_09_post_missing_target_404` |
| `solid-05-10` | Solid | Solid Protocol §5.3 Writing Resources | - |
| `solid-05-11` | Solid | Solid Protocol §5.3 Writing Resources | `Solid.Protocol.Spec.solid_05_11_containment_edit_409` |
| `solid-05-12` | Solid | Solid Protocol §5.3 Writing Resources | - |
| `solid-05-13` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_13_n3_patch_accepted`, `LWS.Core.Spec.lws_patch_not_refused`, `LWS.Core.Spec.lws_patch_applied` |
| `solid-05-14` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_05_accept_headers` |
| `solid-05-15` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | - |
| `solid-05-16` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_19_ill_formed_patch_422` |
| `solid-05-17` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_19_ill_formed_patch_422` |
| `solid-05-18` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `LWS.Core.Spec.lws_core_04_insertions_no_blank_nodes` |
| `solid-05-19` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_19_ill_formed_patch_422` |
| `solid-05-20` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | `Solid.Protocol.Spec.solid_05_20_patch_operations` |
| `solid-05-21` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | - |
| `solid-05-22` | Solid | Solid Protocol §5.3.1 Modifying Resources Using N3 Patches | - |
| `solid-05-23` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_05_25_delete_removes_containment` |
| `solid-05-24` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_05_24_delete_root_405` |
| `solid-05-25` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_05_25_delete_removes_containment` |
| `solid-05-26` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_04_11_auxiliaries_deleted_with_subject` |
| `solid-05-27` | Solid | Solid Protocol §5.4 Deleting Resources | `Solid.Protocol.Spec.solid_05_27_delete_non_empty_container_409` |
| `solid-05-28` | Solid | Solid Protocol §5.5 Resource Representations | - |
| `solid-05-29` | Solid | Solid Protocol §5.5 Resource Representations | - |
| `solid-06-01` | Solid | Solid Protocol §6 Linked Data Notifications | - |
| `solid-06-02` | Solid | Solid Protocol §6 Linked Data Notifications | - |
| `solid-07-01` | Solid | Solid Protocol §7.1 Solid Notifications Protocol | - |
| `solid-08-01` | Solid | Solid Protocol §8.1 CORS Server | - |
| `solid-08-02` | Solid | Solid Protocol §8.1 CORS Server | - |
| `solid-08-03` | Solid | Solid Protocol §8.1 CORS Server | - |
| `solid-08-04` | Solid | Solid Protocol §8.1 CORS Server | - |
| `solid-09-01` | Solid | Solid Protocol §9.1 WebID | - |
| `solid-10-01` | Solid | Solid Protocol §10.1 Solid-OIDC | - |
| `solid-11-01` | Solid | Solid Protocol §11 Authorization | `Solid.Protocol.Spec.solid_wac_01_no_acl_denies` |
| `solid-wac-01` | Solid | Web Access Control §5.3 Authorization Evaluation | `Solid.Protocol.Spec.solid_wac_01_no_acl_denies` |
| `solid-wac-02` | Solid | Web Access Control §5.3.3 Authorization Matching | `Solid.Protocol.Spec.solid_wac_02_match_resource_agent_mode` |
| `solid-wac-03` | Solid | Web Access Control §5.3.3 Authorization Matching | `Solid.Protocol.Spec.solid_wac_03_default_is_inherited` |
| `solid-wac-04` | Solid | Web Access Control §5.3.3 Authorization Matching | `Solid.Protocol.Spec.solid_wac_04_agent_group` |
| `solid-wac-05` | Solid | Web Access Control §5.1 Effective ACL Resource Algorithm | - |
| `solid-wac-06` | Solid | Web Access Control §5.3.2 Web Origin Authorization | - |
| `solid-wac-07` | Solid | Web Access Control §5.3.4 Access Privileges | `Solid.Protocol.Spec.solid_wac_07_wac_allow_header` |
| `solid-wac-08` | Solid | Web Access Control §5.3.4 Access Privileges | `Solid.Protocol.Spec.solid_wac_08_client_reads_wac_allow` |
| `solid-wac-09` | Solid | Web Access Control §3.1 ACL Resource Discovery | `Solid.Protocol.Spec.solid_wac_09_client_acl_from_links` |
| `solid-wac-10` | Solid | Web Access Control §3.2 ACL Resource Representation | - |
| `solid-cl-01` | Solid | Solid Protocol §4.1 Storage Resource | `Solid.Protocol.Spec.solid_cl_01_storage_walk_sound` |
