---
name: lws-solid
description: Run, test and extend Factoidal's Linked Web Storage 1.0 and Solid Protocol support - the Node hosts, the wasm ABI they call, the host test suites, the three community interop scripts, the conformance ledger, and the WebDAV server that shows LWS storages to file browsers. Use when serving a storage, driving a Solid client, adding a protocol rule, mounting a storage in Finder or Explorer, or reading a score from one of these suites.
---

# Linked Web Storage 1.0 and the Solid Protocol

Two standards, one engine, four hosts.

One-page overview (what LWS is, what the server does, strengths, gaps):
`docs/designissues/2026-10-21-lws-overview.md`. Landing gates for a change: `bash tools/land-gates.sh` (exit 0 only if every
gate passes), then the two Touchstone runs it names. External conformance:
`docs/designissues/2026-10-21-lws-touchstone-run.md` (`tools/lws-touchstone.sh`).

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
| `formal/lean4/L4Factoidal/HTTP/Cors.lean` | the CORS protocol (Fetch Standard) as a policy and `preflight?`/`decorate`, shared by LWS and `authz-serve` |
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

## Docker target for other testers

`deploy/lws-target/` (README there): `lws-serve` and `authz-serve` in one
container that keeps the target contract of Touchstone's `targetservers/`, so
that another party can test our server with Docker alone. Owner, 2026-10-26,
verbatim: "Idea is we write dockerfiles for our lws server and they or someone
hammer it in a docker based server". Our job is the container for OUR server.
Do not build or run the other implementations in `targetservers/` unless the
owner asks for that run. (2026-10-26: a pasted Touchstone README was read as a
request to run `run-all.sh` against all six other servers; the owner
corrected it. Cost: one turn and a Docker setup that was not needed.)

## Run the servers

```
factoidal lws-serve   DIR (--issuer IRI[,IRI…] | --auth-config FILE | --insecure-no-auth)
                          [--owner WEBID] [--root-acl FILE] [--audience IRI]
                          [--port N] [--host ADDRESS] [--base IRI] [--page-size N]
                          [--paginate-always] [--moves all|data|off]
                          [--no-linkset-put] [--unstable-search-results] [--merkle]
                          [--controller-inbox URL] [--delivery-limit N]
                          [--delivery-window SECONDS] [--redirects-max N]
                          [--storage snapshot|files]
                          [--cors-origin ORIGIN]... [--no-cors]
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
With `FACTOIDAL_LWS_KEY` set the file is sealed (section "Encryption at
rest" below).
`L4Factoidal/LWS/Snapshot.lean` decides the format and refuses traversal
paths; request paths with dot segments or encoded traversal get 400
(`validTarget`). Persisting into the Shardborough store is a later step.
`lws-serve --storage files` keeps `DIR` as one file per body and a journal
instead (section "Storage on disk" below).

### Storage on disk, stages 1 and 2 (https://github.com/danbri/factoidal/issues/918)

Design record: `docs/designissues/2026-10-22-lws-storage-on-disk.md`. Off by
default: config `storage: "files"` (`listen({ storage: 'files' })`,
`lws-serve --storage files`, `tools/lws-touchstone.sh --storage files`). With
a DIR and no `storage` option the host passes the environment variable
`FACTOIDAL_LWS_STORAGE` (unread; the engine checks it), so
`FACTOIDAL_LWS_STORAGE=files node tests/lws/<suite>.mjs` runs a suite's
restart checks on a storage kept in files. `tests/lws/encryption.mjs` deletes
the variable: it tests the sealed snapshot file.

* Layout (`L4Factoidal/LWS/FileLayout.lean`): `lws-files.json` (metadata of
  every resource and the other state, format `lws-files-1`), `lws-journal`
  (one framed record per step that changed the storage), `bodies/XX/N` (one
  file per body VERSION, numbered; the name holds no part of the path). A new
  body gets a new number; the old file is removed after the record is on disk.
* Journal frame (`L4Factoidal/LWS/Journal.lean`): `LWJ1`, payload length
  (4 bytes), SHA-256 of the payload, the payload. A frame is valid only when
  complete and its digest matches; replay stops at the first that is not. When
  the journal would pass max(1 MiB, the size of `lws-files.json`) a step writes
  a new metadata file and an empty journal (compaction). A start with records
  compacts too.
* What the store records: `JournalStore` sits under the Merkle store and the
  type index (`LwsBackend` in `MerkleHttp.lean`) and records the path of every
  `put` and `remove`, with a proof (`JState.ok`) that no other path changed
  since the last persist. A snapshot handle forgets them after every step.
* Host contract (`npm/factoidal/lws/persist.mjs`): `lwsOpen` answers `load:
  {read: [...]}`; the host reads those files (relative to DIR), calls `lwsLoad`
  with the bytes until it answers `ready`, then performs its `plan`. After a
  step with `changed: true` it calls `lwsPersist` and performs that plan before
  it answers. Plan operations: `write` (temp, fsync, rename, fsync of the
  directory), `append` (fsync), `remove`, `rename`. The host makes no other
  decision; the file is in group 2 of `tools/host-purity-lint.sh`.
* Encryption at rest: `lws-files.json` sealed as the snapshot is
  (`Seal.sealSnapshot`); every body file and journal payload sealed with the
  binary format `LWE1` (`Files.sealBin`), the file's own name (or
  `lws-journal`) in the associated data, so a body file moved to another name
  does not open. Nonces from the host's `seed` per call.
* Migration: a start that finds only `lws-state.json` writes every body file,
  `lws-files.json` and an empty journal, then renames the snapshot to
  `lws-state.json.migrated`.
* Stage 2 (`L4Factoidal/LWS/Bodies.lean`): an entry with bytes holds a
  `BodyStub` (body file number, length, FNV-1a, SHA-256 with `merkle`, the
  types of a Turtle body) and no bytes in memory; ACL resources keep their
  bytes (every access decision reads them). A step that needs bytes (GET body
  or range, JSON Patch, a PUT a subscription may hear of, a move of a Turtle
  resource) makes `lwsStep` answer `read: [PATH, ...]`; the host passes the
  files to `lwsRead` (`Files.readBodies` checks seal, length, FNV-1a,
  SHA-256) and steps again; the bytes leave memory after the step. A start
  reads no body file unless the metadata lacks a fact (`Files.needsRead`).
  A changed body file is found when it is read (the request answers 500),
  not at start.
* The LWS handles run `TreeStore` (`Std.TreeMap` keyed by path,
  `treeStoreLaws`) and a type index in `Std.TreeMap`/`Std.TreeSet`: one step
  costs a logarithm of the store (a hash set shared with the state before the
  step was copied whole on every insert). Still linear: a container listing,
  a recursive DELETE and a move list every path; the Merkle data are hash
  maps.
* Theorems: `journalStoreLaws`, `replay_record`, `replay_jstate`,
  `replay_records` (replaying the records of a sequence of steps gives the
  metadata of the store after them), `persist_replay`, `bodiesOut_journal`,
  `projE_toEntry`, `decodeFrames_encodeFrames`, `decodeFrames_torn` (a journal
  whose last frame is cut at any byte reads back as the frames before it),
  `fileMetaOfJson_fileMetaJson`, `recordOfJson_recordJson`, `openBin_sealBin`,
  `openBin_keyId`; stage 2: `treeStoreLaws`, `etagFor_dehydrate`,
  `itemJson_dehydrate`, `entryFacts_dehydrate`, `leafDigest_dehydrate`,
  `entryFacts_withBody`, `leafDigest_withBody`, `IndexOk.congr`,
  `MkOk.congr_key`, `JState.replaceAt_prior`, `stubAt_journal`,
  `recordedDigest_changes`. Not proved: `parseJson` inverts `Json.toString`
  (as for the snapshot).
* `solid-serve` keeps the snapshot: an expected failure in
  `tests/solid/server/protocol.mjs` names issue 918.

Tests: `L4Factoidal/LWS/FileLayoutTests.lean` (`#guard`s that play the host on
a table of files: round trips clear and sealed, every step compacting, a
journal cut at every byte of its last record, a changed or missing body file,
a wrong key, a record out of order, migration); `node tests/lws/storage-files.mjs`
(14 pass, 0 fail, 0 skipped (out of 14), 2026-10-22, stage 2); `tests/lws/scaling.mjs`
rows "storage". Measured 2026-10-22 after stage 2: the engine's step and
persist 0.304, 0.267, 0.278, 0.285 ms at 1,000, 2,000, 4,000, 16,000
resources (stage 1: 0.21 ms at 1,000, about 3 ms at 16,000); a PUT through
the host (fsync most of it) 5.75, 4.65, 4.39, 4.46 ms; the peak RSS of a start
and one GET of 1,000, 2,000, 4,000 resources of 16 KiB 230.3, 229.6,
210.5 MiB (stage 1: 258 MiB at 1,000, 515 MiB at 4,000), asserted: growth
<= 16 MiB from s to 4s. `lws scaling`: 21 pass, 0 fail (out of 21). The
median of five repeats is used for the host PUT row: fsync varies both ways
and one minimum of three read a ratio of 1.72. Touchstone with `--storage files`: the same
totals as the default (open 76 pass, authorization 215 pass, 0 fail; `--config
all --unstable-search-results` 220 passed, 0 failed, 1 never applied, out of
221). Every LWS suite also passes with `FACTOIDAL_LWS_STORAGE=files`.

The LWS binding of the 2026-10-19 editor's draft (ETag, conditional
requests, ranges, `application/lws+json` listings, linksets, the
`application/lws+cid` storage description at `/.well-known/lws-storage`,
JSON Patch, RFC 9457 errors) is `L4Factoidal/LWS/Binding.lean`; the audit
table is in the ledger, section "LWS editor's draft 2026-10-19 audit", and
`node tests/lws/draft-binding.mjs` is its host suite.

### Notifications (https://github.com/danbri/factoidal/issues/890)

`L4Factoidal/LWS/Notifications.lean` implements the core draft's
"Notifications" section and the webhook notification suite
(`lws10-notifications-webhook`, both at w3c/lws-protocol 9a08ff65). The module
header quotes each section it decides.

* Discovery: the storage description's `service` array holds a
  `NotificationService` with `serviceEndpoint`
  `<base>/.well-known/lws-subscriptions/` and `subscriptionType`
  `["WebhookSubscription"]` (`Config.notifications`; the wasm handle turns it
  on, config `notifications: false` turns it off). With a signing key the
  description also has a `JsonWebKey` (Ed25519) `verificationMethod`
  referenced from `authentication`; the key id is
  `<base>/.well-known/lws-storage#notification-key-<digest>`.
* Subscribe: an authenticated POST (`application/lws+json`) with `type`
  `WebhookSubscription`, `topic` (IRIs in this storage), `inbox` (`http` or
  `https`) and optional `expires` (RFC 3339, in the future). 201 with
  `Location`, `type`, `subscription`. 400 for a missing or unadvertised
  `type`, a missing `topic` or `inbox`, a bad `expires`; 415 for another
  media type; 401 with no token (`Authorization.decide`); 403 when the agent
  cannot read EVERY topic (Web Access Control, `wacCanRead`).
* Manage: GET on the endpoint lists the agent's own subscriptions as an LWS
  container (paged at `pageSize`); GET on a subscription gives its state
  (`active` false when expired or deactivated); DELETE cancels it. Another
  agent's subscription answers 404.
* Changes: `serverStep` runs `step`, then `changesOf` names the paths the
  request may have changed and `classify` decides Create, Update or Delete
  from the store before and after (theorem `classify_sound`). Auxiliary
  resources give no activity; a linkset change is an Update. With no
  subscription nothing is computed.
* Routing: a subscription hears of a change in its scope (a container topic
  is recursive) when it is live and its agent may read the resource after
  the step (Create, Update) or before it (Delete) (`eligible`, theorem
  `routed_authorized`). One envelope per subscription per request; an
  `activity` array when there is more than one. No `actor`.
* Delivery: `lwsStep` answers `deliveries: [{id, url, headers, body}]`; the
  host POSTs each one exactly as given and reports the status (0 for no
  answer) to `lwsDelivered`, which answers `retry: {delivery, after}` (seconds)
  or nothing. Retry for 0, 408, 425, 429, 5xx, at most 3 attempts (waits 1 s,
  2 s); 410 deactivates at once; 3 failed deliveries in a row deactivate.
* Signing: RFC 9421 over `@method`, `@scheme`, `@authority`, `@path`,
  `content-type`, `content-digest` (RFC 9530 `sha-256`), `created`, `keyid`,
  `alg="ed25519"`, with the vendored HACL* Ed25519. The key is derived from
  `entropy` that the host passes to `lwsOpen` (32 random bytes) and kept in
  the snapshot with the subscriptions (member `notifications`).

* This server under another name (https://github.com/danbri/factoidal/issues/915,
  `L4Factoidal/LWS/InboxGuard.lean`): an inbox whose authority is the base
  IRI's, or whose host (an IP literal, `localhost`, or a name the HOST
  resolved) is an address of this server at its port, is refused with 400.
  Every loopback address counts as one address; another port is another
  server. The host passes `listen: {address, port, addresses}` to `lwsOpen`
  (`server.mjs` `listen()` does); for an inbox host that is a name `lwsStep`
  answers `resolve: {host}` first (`Notifications.resolveNeeded?`, only for an
  authorized subscription POST), the host runs `dns.lookup(host, {all: true})`
  and steps the request again with `resolved: [{host, addresses}]`.
* Rate limit (issue 915): at most `deliveryLimit` deliveries (default 10) per
  subscription in a window of `deliveryWindow` seconds (default 60; `0` turns
  it off; `lws-serve --delivery-limit N --delivery-window S`). Activities over
  the limit wait (`NotifState.held`, at most 1,024, kept in the snapshot) and
  go in ONE envelope with an `activity` array when the window ends (core
  §Batching Notifications): with the subscription's next change, or when the
  host calls `lwsFlush` after the `wake` seconds an answer named. Theorems
  `admits_le` (at most `limit` deliveries in one window) and `admit_count_le`.
  With the test clock (`now` set, one second per mutation) a `wake` flush
  finds nothing due; use `realClock: true` to see a flush.
* Endpoint verification: the webhook draft only says "Rate limiting and
  endpoint verification are suggested to prevent abuse of the subscription
  mechanism" and defines no procedure, so there is no behaviour to implement.

Tests: `L4Factoidal/LWS/NotificationsTests.lean` (`#guard`s through
`serverStep`, positive and negative, also "Delivery rate" and "An inbox that
is this server"); `L4Factoidal/LWS/InboxGuard.lean` guards (IP parsing,
authorities, `loops`, `toResolve?`); `tests/lws/draft-binding.mjs` rows
"Notifications" (a local receiver; signatures verified with `node:crypto`
against the published key; the 400 for `localhost`, `127.0.0.2`, `[::1]` at
the server's port, 201 for another port; 30 changes give 10 POSTs; a
real-clock server with `deliveryLimit: 2, deliveryWindow: 2` sends the rest
in one batched envelope); `tests/lws/authorization.mjs` rows
"Notifications" (401, 403, delivery-time filtering with real tokens and
ACLs). Not done: the Solid server's channels
(https://github.com/danbri/factoidal/issues/898).

### Moving resources (https://github.com/danbri/factoidal/issues/914)

`L4Factoidal/LWS/Move.lean` implements the core draft's "Moving Resources"
(w3c/lws-protocol 9a08ff65). The module header quotes each statement.

* Discovery: the storage description has `capability: [{type: MoveResource,
  appliesTo: [DataResource, Container], preservesIdentifier: false}]`
  (`Config.moves`; the wasm handle turns it on, config `moves: false` or
  `"off"` (`lws-serve --moves off`) turns it off, and then a change of `up`
  is 409). Config `moves: "data"` (`--moves data`, `Config.moveContainers`
  false) moves data resources only: `appliesTo: [DataResource]`, and a
  change of a container's `up` is 409 (`Move.movable`, also used by
  `movePlanOf?`). Another `moves` value stops the start.
* Request: a JSON Patch (or PUT) of `<path>?linkset` that changes the `up`
  target (`requestedUp`). The target is an IRI below `baseIri` or a
  path-absolute reference. Answer: 200, the new linkset (new `anchor`),
  `Content-Location: <new path>?linkset`, because identifiers are paths and
  a moved resource gets a new one (destination path and old name).
* Effect (`move`): one function from store to store. Every moved path
  (`movedPath`: the resource, the descendants of a container, the `.acl` and
  `.meta` of a data resource) is removed and written at its new path; the
  former parent and the destination are stamped, so both ETags change.
* Refusals, all 409 (404 when the resource is missing): destination missing
  or not a container, the container itself or a descendant, the storage
  root, an auxiliary resource, a name already taken in the destination,
  another storage, a removed `up`, two `up` targets.
* Authorization (`Authorization.decide`, `movePlanOf?`): Write on every
  moved resource (Control for an ACL resource) and Append on the
  destination, before the move.
* Notifications: one `Move` activity (`origin` the former parent, `target`
  the destination, `object` the new identifier), heard by a subscription
  whose scope holds the old or the new path (`moveChange?`, `changeInScope`).
* Theorems: `move_tree` (a containment tree stays a tree), `tree_acyclic`,
  `parentOf_unique`, `tree_parent`, `move_unmoved`, `move_moved`,
  `move_vacated`. Two path facts are checked at run time, not proved for
  every string (`moveChecks`); a failed check is a 409 with the store
  unchanged.
* 301 at the previous identifiers (`L4Factoidal/LWS/MoveRedirect.lean`, a
  SHOULD of §Moving Resources): the wasm layer keeps (previous path, current
  path) pairs for every moved path (`MovePlan.moves`), at most
  `redirectsMax` (256, `lws-serve --redirects-max N`), in the snapshot as
  member `moved`. Before a step, a request whose path names nothing and has
  a pair answers 301 with `Location` of the current IRI (query kept, so
  `?linkset` too), when `Authorization.decide` allows the same request at the
  current path (§Privacy Considerations, "Redirects"); else it is stepped as
  before. After every step the table is pruned (`after`): a pair goes when a
  new resource is created at its previous path (POST with that name; a PUT
  there is a request to the moved resource and answers 301) or the moved
  resource is deleted; a later move follows the current path. Theorems
  `redirect_current`, `prune_ok`, `record_ok`, `after_ok`, `record_length`,
  `redirect_after_move`.

Tests: `L4Factoidal/LWS/MoveTests.lean`, `MoveRedirectTests.lean`;
`tests/lws/draft-binding.mjs`, the "Moving Resources" rows. Touchstone: `definitions/lws10/core/moving.yamlld`;
three of its 11 tests have preconditions this server cannot meet at once
(`move-keeps-identifier-content-and-links` needs `preservesIdentifier: true`,
`move-container-refused-without-container-support` needs no `Container` in
`appliesTo`, `move-refused-without-capability` needs no capability); the
last two apply and pass in `tools/lws-touchstone.sh --config alt-datamove`
and `alt-nomove`.
Measured 2026-10-21 without `--shim`: open 6 pass, 0 fail, 5 inapplicable;
authorization 7 pass, 0 fail, 4 inapplicable (out of 11 each). With the
AccessGrantService (https://github.com/danbri/factoidal/issues/913) the two
`move-needs-*` tests apply and pass: authorization 9 pass, 0 fail, 3
inapplicable (out of 12, measured 2026-10-21); record:
`docs/designissues/2026-10-21-lws-touchstone-run.md` § Moving resources and
§ Access requests and grants.

### Type index and type search (https://github.com/danbri/factoidal/issues/912)

`L4Factoidal/LWS/TypeIndex.lean` and `L4Factoidal/LWS/Search.lean` implement
the LWS Search and Type Index Services draft (`lws10-index`, w3c/lws-protocol
9a08ff65; the module headers quote each section they decide).

* The index lives in the STORE. `IndexedStore S L` wraps any lawful `Store`:
  every `put` and `remove` updates the facts of the one path it touches, and
  the state `IxState` carries the proof `IndexOk` that the index describes
  the store. So every create, update, delete, recursive delete, linkset
  change and move (`Move.lean` uses `put`/`remove`) is indexed with no hook
  in `Operations.step`, and a later change to `step` cannot make the index
  stale. `StoreLaws.lookupTick` (shared with `Move.lean`) is what lets
  `tick` keep the proof.
* Facts of a resource (`entryFacts`): its native class (`lws:Container` or
  `lws:DataResource`), its declared `type` links, its client links with a
  relation not in `structuralRels` (for example `describedby`), and the
  `rdf:type` objects of the resource in `text/turtle` content up to 1 MiB.
  ACL and `.meta` resources have none.
* Declared types: a `Link: <T>; rel="type"` whose target is not an LWS or LDP
  class (`Linkset.declaredType`) is a client link, kept on POST, on a
  `Prefer: set-linkset` PUT or PATCH (which now answer
  `Preference-Applied: set-linkset`) and in the linkset document's `type`
  member after the server's class link. A `type` link naming a native class
  still answers 409. Core §Metadata calls `type` "System Managed"; the index
  draft says types SHOULD come from client Link headers; this reading keeps
  both (the record is in the Linkset module header).
* Services: `GET <base>.well-known/lws-type-index` (TypeIndex, paged by
  `?page=N`) and `QUERY <base>.well-known/lws-type-search` with
  `application/lws-query+json` (ContainerPage, paged by GET of
  `?q=<base64url filter>&page=N`). `Cache-Control: private`,
  `Vary: accept, authorization`, `Accept-Query`. Errors 400, 415, 406, 422
  (more than 64 IRIs), 404 for an unrecognized page reference.
* Authorization: `Authorization.decide` lets any client ask (anonymous gets
  what the public may read; a refused token is 401); the answer is filtered
  by Web Access Control read access over the current state on every request.
* Theorems: `ixSearch_eq_specSearch` (the index answer is the same list as
  filtering every path of the store), `searchAnswer_eq_spec`,
  `searchAnswer_authorized`, `searchPagePaths_authorized`,
  `visibleTypes_eq_specTypes`, `search_after_step`, `serverStep_index_safe`,
  `rebuildEntries_ok` (one-pass rebuild when a snapshot is opened),
  `indexedStoreLaws`.
* Config: `typeIndex` (default on; `false` turns it off), `listen({ typeIndex: false })`.

Tests: `L4Factoidal/LWS/SearchTests.lean`; `tests/lws/draft-binding.mjs` rows
"Type index" and "Type search"; `tests/lws/authorization.mjs` (filtering with
real tokens and ACLs); `tests/lws/scaling.mjs` rows "type index" (a rare-type
search, a whole-store search and a reopen at 500, 1,000 and 2,000 resources).
Touchstone `index/manifest.yamlld` (40 tests), measured 2026-10-21 without
`--shim`: authorization 34 pass, 0 fail, 6 inapplicable; open 40
inapplicable (every test needs Authentication). Five of the six needed an
AccessGrantService; with https://github.com/danbri/factoidal/issues/913
they pass (authorization 39 pass, 0 fail, 1 inapplicable). The last one
needs a `Content-Location` results resource, which the draft does not
define; it applies with the unstable option below. Whole runs: open 75 pass, 0 fail, 146 inapplicable; authorization
186 pass, 0 fail, 35 inapplicable (out of 221 each);
`docs/designissues/2026-10-21-lws-touchstone-run.md`, "Type index and type
search".

### Search results resource: ANTICIPATORY AND UNSTABLE, off by default (https://github.com/danbri/factoidal/issues/922)

`L4Factoidal/LWS/SearchResults.lean`. lws10-index defines no such resource;
it only says a server that exposes one "MUST subject it to the same
authorization filtering on every access and MUST prevent its reuse across
clients". Everything here is likely to change.

* On: config `searchResults: true` (`listen({ searchResults: true })`,
  `lws-serve --unstable-search-results`, `tools/lws-touchstone.sh
  --unstable-search-results`). Off: the step is `.pass` (theorem
  `serverStep_off`) and no extension member is advertised.
* RFC 10008 §2.3 makes the Content-Location resource "the results of the
  query operation just performed"; §2.4 gives a re-run to Location. So the
  record keeps the QUERY's result paths, and a GET lists those that a QUERY
  with the same filter and the agent's current read access answers now (a
  later resource never appears; a deleted, retyped or unreadable one
  disappears). Theorem `resultsAnswer_sublist_query`.
* Name `<base>.well-known/lws-type-search/results/<id>`, `<id>` the base64url
  of 16 random bytes that the host passes as request member `random`
  (`server.mjs` sends 16 bytes from `crypto.getRandomValues` with every
  request). An anonymous QUERY, or one with no `random`, names nothing.
* Only the creating agent with the same token `client_id`: everyone else
  gets 404, the creator gets 410 after `searchResultsTtl` (600 s). At most
  `searchResultsMax` (100) records; the oldest is removed first. Theorems
  `resultsGet_creator_only`, `resultsGet_anonymous`, `insertBounded_length_le`.
* Discovery: extension member
  `https://github.com/danbri/factoidal/issues/922#unstableResultsResource`
  on the `TypeSearchService` entry. Snapshot member `searchResults` (format
  `lws-search-results-unstable-1`), sealed with the rest of the snapshot
  under a storage key (issue 921).

Tests: `L4Factoidal/LWS/SearchResultsTests.lean`; `tests/lws/draft-binding.mjs`
rows "Type search results (unstable, issue 922)"; `tests/lws/authorization.mjs`
row "Type search results resource (unstable, issue 922)" (bob cannot read
alice's results URL; alice can; another client and an anonymous request get
404; 410 after the lifetime); `tests/lws/encryption.mjs` (sealed and kept
across a restart). Touchstone `type-search-content-location-protected`:
`docs/designissues/2026-10-21-lws-touchstone-run.md` § Search results resource.

### Access requests and grants (https://github.com/danbri/factoidal/issues/913)

`L4Factoidal/LWS/AccessPolicy.lean` (data model, Access Profile, what a grant
permits, theorems) and `L4Factoidal/LWS/AccessGrants.lean` (the two
endpoints, the notification of a new grant) implement core §Access Requests
and Grants (w3c/lws-protocol 9a08ff65, `lws10-core/lws-access-requests.html`).
The module headers quote each statement and list the server choices.

* Discovery: `AccessRequestService` at `<base>.well-known/lws-access-requests/`
  and `AccessGrantService` at `<base>.well-known/lws-access-grants/`, each
  with `conformsTo: ["https://www.w3.org/ns/lws#AccessProfile"]`
  (`Config.accessGrants`; the wasm handle turns it on, config
  `accessGrants: false` turns it off).
* Endpoints (LWS containers): GET lists (paged at `pageSize`, `Link` type
  Container), POST (`application/lws+json`, `ld+json` or `json`; else 415)
  answers 201 with `Location`, GET and DELETE of one member. Under
  authorization every request needs a token (401). Any agent makes access
  requests; only the storage controller (`acl:Control` on the root,
  `isController`) makes and revokes grants (403). A request is visible to its
  maker and the controller, a grant to its assignees and the controller;
  others get 404.
* Validation (`parseDoc`): `@context` with the LWS context, `type` with
  `AccessGrant`/`AccessRequest`, `storage` naming THIS storage, optional
  `inbox` URI, `access` with one or more policies (`type` with
  `AccessPolicy`, `action` from read/modify/create/delete, `assignee` URI,
  optional `target` {type matcher, values in this storage, not ACL or
  `.well-known`}, optional constraints). Anything else is 400. Extra members
  are kept.
* Enforcement: `Authorization.decide` allows a request when Web Access
  Control OR `AccessPolicy.grantAllows` does. `actionOf` maps the request:
  GET/HEAD/OPTIONS read, POST create (in the container), PUT/PATCH modify (or
  create in the parent for a missing resource), DELETE delete; `.meta` and
  linkset writes are modify of the resource; ACL resources never. A move
  needs delete of every moved resource and create in the destination.
  Notification subscribe and delivery checks and the type index use the same
  rule (`Notifications.wacCanRead`). Constraints: `dateTime`
  (eq/gt/gteq/lt/lteq, the request clock), `format`, `type` (the kind and the
  client type links), `client` (the token's `client_id`) with eq/isAnyOf;
  `purpose` is accepted and never satisfied (the draft gives a request no way
  to state one). A container grant does not reach its members.
* Notification: a new grant gives one `Create` notification to its `inbox`
  and to the inbox of each access request naming one of its assignees.
* Controller notification (https://github.com/danbri/factoidal/issues/920):
  core §Access Requests and Grants says "When a new access request is
  submitted, the storage controller SHOULD be notified", and names no inbox
  for the controller. Server choice: config `controllerInbox`
  (`listen({ controllerInbox })`, `lws-serve --controller-inbox URL`). When
  set, each new access request gives one `Create` notification there
  (`announceRequest`, the same signed and retried delivery path); when
  unset, nothing. A value that is not an `http` or `https` URL stops the
  start; one inside this storage is not used.
* Persistence: snapshot member `access` (`stateJson`); every stored document
  is parsed again at open (`stateOfJson`).
* Theorems: `grantsPermit_sound`, `grantAllows_sound`, `grantAllows_acl`,
  `satisfied_excluded`, `policyPermits_excluded`, `recordPermits_expired`,
  `grantsPermit_revoke`, `grantsPermit_revoke_only`,
  `accessStep_grant_needs_controller`.

Tests: `L4Factoidal/LWS/AccessGrantsTests.lean` (`#guard`s through
`AccessGrants.serverStep` under enforcement with a stub verifier);
`tests/lws/draft-binding.mjs` rows "Access Requests and Grants";
`tests/lws/authorization.mjs` rows "Access grants" (real tokens: read only,
controller only, public, constraints, move, subscribe after revocation).
Touchstone `core/access_grants.yamlld` (17 tests), measured 2026-10-21
without `--shim`: authorization 17 pass, 0 fail, 0 inapplicable; open 1
pass, 0 fail, 16 inapplicable (16 need Authentication). Whole runs: open 76
pass, 0 fail, 145 inapplicable; authorization 215 pass, 0 fail, 6
inapplicable (out of 221 each);
`docs/designissues/2026-10-21-lws-touchstone-run.md` § Access requests and
grants.

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
  module header. Config `paginateAlways` (`lws-serve --paginate-always`,
  `Pagination.paginatedWith`) paginates every listing: one that fits is one
  page with `first` and `last` and no `next` or `prev`. A paginated
  container's first-page tags are current tags for `If-Match`
  (`Operations.tagsIn`, `pageTag`), because GET of the container URI answers
  that page.
* `L4Factoidal/LWS/Linkset.lean`: `Entry.links` holds the client links.
  `Link` with `Prefer: set-linkset` replaces them on PUT and adds to them on
  PATCH; `Link` on POST sets them (server-managed relations dropped); the
  linkset resource accepts JSON Patch and PUT of `application/linkset+json`
  (config `linksetPut: false`, `lws-serve --no-linkset-put`: `Allow` without
  PUT and a PUT answers 405 with `Allow`; `Operations.linksetAllow`).
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
  bytes (`etagFor`). The ETag of a container is its clock, the media suffix
  and the FNV-1a digest of its listing in that media type (`containerTag`,
  `Operations.tagIn`): a host with a real clock sets the clock to the
  current second, so a tag from the clock alone did not change for two
  changes in one second (https://github.com/danbri/factoidal/issues/911).
* A POST takes the first free name of the hint (or `res<clock>`), `-1`,
  `-2`, ... (`childPathFor`, theorem `childPathFor_fresh`). Never derive
  uniqueness from the clock: under a real clock it repeats within a second,
  and until 2026-10-21 the third POST in one second replaced the second
  resource (issue 911, F6).
* `If-Modified-Since` and `If-Unmodified-Since` are compared as instants,
  in the three HTTP-date formats (`L4Factoidal/LWS/HttpDate.lean`, theorem
  `unixOfCivil_civilOfUnix`); `If-Unmodified-Since` applies to every method.
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

### Encryption at rest (https://github.com/danbri/factoidal/issues/921)

Owner, 2026-10-21, verbatim: "Yes env var please. Again off by default but
good to show we can." The LWS drafts say nothing about encryption at rest.

* Turn it on: set `FACTOIDAL_LWS_KEY` to a 32-byte key, as 64 hex digits or
  43 characters of base64url (`openssl rand -hex 32`). Both `lws-serve` and
  `solid-serve` read it (`npm/factoidal/lws/persist.mjs`,
  `storageKeyText`); `listen({ storageKey })` takes the text directly, and
  `storageKey: null` reads no key. With the variable unset nothing changes.
* Format `lws-snapshot-sealed-1` (`L4Factoidal/LWS/SnapshotSeal.lean`):
  `{"format","cipher":"chacha20-poly1305","keyId","nonce","ciphertext"}`.
  `keyId` is the first 8 bytes of SHA-256 of the key (hex); `nonce` is 12
  bytes from the host's random source, new for every write (the host passes
  `{"nonce":…}` as the second argument of `lwsSnapshot`/`solidSnapshot`);
  the plaintext is the clear-text snapshot document; the four header fields
  are the AEAD's associated data.
* Cipher: ChaCha20-Poly1305 (RFC 8439) from HACL* through
  `Crypto/ChaChaPoly.lean`, in the native build and in the wasm module. It is
  the only AEAD the tree has: `skills/crypto-policy` forbids a cipher of our
  own, and the pinned HACL* has no portable AES-GCM (issue 677).
* Open (`Seal.openSnapshot`, from `openConfigOfJson`): the key text is
  checked first (other lengths refused); then a wrong key (key id differs), a
  changed format or cipher, base64 that is not canonical, and a tag that does
  not authenticate are each refused with their own message, and so are a
  clear-text file with a key and a sealed file without one. The CLI prints
  the message on one line and exits 1. A file that is not JSON (for example
  truncated) is refused by the host.
* Theorems (over any AEAD with RFC 8439 correctness; the HACL* binding is
  opaque): `unsealDoc_sealDoc`, `unsealDoc_format`, `unsealDoc_cipher`,
  `unsealDoc_keyId`, `unsealDoc_wrongKey`, `unsealDoc_authenticated`,
  `openSnapshot_clear`, `openSnapshot_clear_with_key`,
  `openSnapshot_sealed_without_key`, `checkingModel_correct` (the hypothesis
  is satisfiable). That a changed nonce or ciphertext fails is the AEAD's
  authentication property, checked at run time: `lake exe l4crypto-probe`
  section `lws-snapshot-seal` (every one-character change and every
  truncation of a sealed document refused) and `node tests/lws/encryption.mjs`.

Threat model, in plain words. The key protects the snapshot FILE on disk:
a copy of `DIR` (a stolen disk, a backup, another user of the machine) cannot
be read without the key, and a changed byte stops the server from starting.
It does not protect the storage in the memory of a running server, the key in
the server's environment (anyone who can read the process environment or the
shell history has it), the answers the server gives to clients, or the size
and the write times of the file. It does not replace authorization. A lost
key loses the storage. To encrypt an existing clear-text storage, or to
change the key, copy its resources into a new storage started with the new
key. With random 96-bit nonces, one key is good for about 2^32 writes.

Cost, measured 2026-10-21 (wasm in Node, about 1,050 small resources): a
PUT that writes the snapshot takes 133 to 143 ms sealed against 49 to 54 ms
clear, the file is 1.33 times larger, a restart 378 to 437 ms against 183 to
190 ms. `node tests/lws/scaling.mjs` with the variable set: 12 pass, 0 fail
(out of 12); its reopen at 2,000 resources is 439 ms sealed against 241 ms
clear, ratio 4m/m 5.56 against 4.81 (bound 6.0). Host test:
`node tests/lws/encryption.mjs`, 27 pass, 0 fail, 0 skipped (out of 27).

### Merkle hashes (optional) (https://github.com/danbri/factoidal/issues/919)

Owner, 2026-10-21, verbatim: "After, yes. As an optional, probably default
off until we settle on stronger motivating usecase but good to have the
fundamentals there". The LWS drafts define no integrity mechanism; this is a
server extension. Design record:
`docs/designissues/2026-10-21-lws-merkle.md`.

* Turn it on: config `merkle: true` (`listen({ merkle: true })`,
  `factoidal lws-serve --merkle`, `tools/lws-touchstone.sh --merkle`). Off:
  no field, no member, nothing computed (`MkState.hasher = none`, theorem
  `decorate_off`).
* What is hashed (`L4Factoidal/LWS/Merkle.lean`): a resource that is not a
  container, SHA-256 of its bytes; a container, SHA-256 of tag 2, its member
  count (8 bytes) and the `Storage/BlockMerkle.lean` root over the leaves
  `digest ++ path` of its listed members in path order. The member count is
  bound beside the root because a Bitcoin-style tree gives `[a, b, c]` and
  `[a, b, c, c]` one root. Auxiliary resources (`.acl`, `.meta`) have digests
  but are not members, so they change no root.
* Hasher: `Merkle.haclHasher` (`Crypto.sha256Hacl`, the vendored HACL* code,
  native and wasm) at run time; `pureHasher` (FIPS 180-4 in Lean) in every
  `#guard`; the theorems hold for every hasher.
* Maintenance: `MerkleStore S L` wraps the backend store, UNDER
  `TypeIndex.IndexedStore` (`LwsBackend` in `MerkleHttp.lean`); its state
  carries the invariant `MkOk` as a proof, so every state `step` reaches is
  correct with no hook in `Operations.step`. A write recomputes the digest of
  the written path and then of each container above it (`walk`), and stops at
  the first container whose digest did not change. A container's digest is
  computed from its member list, so a write costs time linear in the members
  of each container above it.
* What the server shows (`L4Factoidal/LWS/MerkleHttp.lean`, `decorate`):
  `Repr-Digest: sha-256=:<base64>:` (RFC 9530) on a 200 or 206 GET or HEAD of a
  resource with its stored media type; `Factoidal-Merkle-Root` and the listing
  member `https://github.com/danbri/factoidal/issues/919#merkleRoot` (JSON) or
  the same statement (Turtle) on a container; the member
  `https://github.com/danbri/factoidal/issues/919#storageMerkleRoot` in the
  storage description. Under authorization the roots go to the storage
  controller only (a root is computed from resources a reader of the listing
  may not read). Entity tags do not change in this step: an expected failure
  in `tests/lws/merkle.mjs` names issue 919.
* Snapshot: no hash is stored; the hashes are rebuilt when a storage is
  opened, in one pass after one sort (`rebuild`, theorem `rebuild_ok`).
* Theorems: `MkOk.dig_eq_recompute` and `MkState.dig_eq_recompute` (the
  maintained digests equal a recomputation from the store), `rebuild_ok`,
  `walk_ok`, `MkOk.upd`, `merkleStoreLaws`, `containerDigest_inj`,
  `dataDigest_changes`, `parent_digest_changes`, `change_reaches_ancestor`
  (a change reaches every container above it unless SHA-256 has a collision
  among the byte strings hashed at one path in the two states; a HYPOTHESIS,
  `BlockMerkle.NoCollision`, never an axiom), `BlockMerkle.rootWith_inj`.

Tests: `L4Factoidal/LWS/MerkleTests.lean`, the checks in `MerkleHttp.lean`;
`node tests/lws/merkle.mjs` (18 pass, 0 fail, 1 xfail, 0 skipped (out of 19),
2026-10-21); `tests/lws/scaling.mjs` rows "merkle". Cost, measured
2026-10-21: one write into a container of 2,000 members takes about 6.3 ms on
against 0.9 ms off (linear in the members of each container above the
write); a reopen of 2,000 resources with the hashes rebuilt, 246 ms.

### CORS (https://github.com/danbri/factoidal/issues/923)

A page on another origin (for example GitHub Pages) calls `lws-serve`
directly. Ledger section "CORS" in `docs/lws-solid-conformance.md` has every
field value.

* Lean: `L4Factoidal/HTTP/Cors.lean` (the policy `off | echo | allow`, the
  origin syntax of RFC 6454 §6.2, `preflight?`, `decorate`, `around`) and
  `L4Factoidal/LWS/Cors.lean` (the LWS profile). `Wasm/Ops/Lws.lean`
  `lwsStepWith` calls `Cors.preflight?` FIRST: a preflight (`OPTIONS` with
  `Access-Control-Request-Method` and `Origin`) is answered 204 before body
  files, redirects, inbox resolution, authentication and Web Access Control
  (theorem `around_preflight`). Every other answer goes through
  `Cors.decorate` (status and content unchanged, `decorate_status`). A new
  answer path in `lwsStepWith` must call `Cors.decorate` too.
* Default: echo a valid request `Origin` (Solid §8.1), never `null`, no
  `Access-Control-Allow-Credentials` (the token is in `Authorization`), and
  `Vary: Origin` on every answer, merged into the answer's own `Vary`.
  Config `cors`: `false` (`--no-cors`) or a list (`--cors-origin ORIGIN`,
  repeatable); a malformed origin stops the start.
* `authz-serve` has the same config and flags (`Authz.stepCors`, its own
  profile). `solid-serve` keeps its Solid §8.1 module
  (`Solid/Server/Cors.lean`, with credentials, no flags: §8.1 requires the
  echo); its preflight is now answered before Web Access Control.
* A new response field that a page must read goes in `exposedHeaders` of
  `LWS/Cors.lean`, and a new request field in `requestHeaders`; the `#guard`s
  compare the lists with `tests/lws/cors.mjs`.

Tests: `#guard`s in `HTTP/Cors.lean`, `LWS/Cors.lean`, `Authz/Tests.lean`,
`Solid/Tests.lean`; `node tests/lws/cors.mjs`; `node tests/lws/cors-browser.mjs`
(Chromium through Playwright, `PLAYWRIGHT_BROWSERS_PATH=/opt/pw-browsers`,
never `playwright install`; exit 2 when it cannot run).

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
  HACL\* code), then `iss`, `aud` contains the storage IRI (the storage
  description `<base>.well-known/lws-storage`, the IRI of every
  `lws#storage` link and of the 401's link; `storageIri`), `exp`, `nbf`,
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

An authorization server for these tokens is its own component, `factoidal
authz-serve` (https://github.com/danbri/factoidal/issues/916): start it with
`--resource <base>.well-known/lws-storage` and give lws-serve `--issuer
<its issuer>`. Operating manual: [`skills/authz-server/SKILL.md`](../authz-server/SKILL.md).

Test: `node tests/lws/authorization.mjs` runs a local authorization server
(RFC 8414 metadata and a JWK Set, ES256 keys from `node:crypto`) and checks
the positive and negative cases; `L4Factoidal/LWS/AuthorizationTests.lean`
holds the `#guard`s with a stub verifier.

From JavaScript:

```js
import { listen } from '@factoidal/core/lws'
import { listen as solidListen } from '@factoidal/core/solid/server'
```

## Third-party conformance: Touchstone

`bash tools/lws-touchstone.sh [--config open|auth|both]` builds Touchstone
(https://github.com/ebremer/touchstone, pinned commit; JDK 21 and Maven)
and runs its 221 LWS tests against `lws-serve`, with `--insecure-no-auth`
(`open`) and with authorization through Touchstone's reference
authorization server (`auth`). It passes `--page-size 4`
(`LWS_PAGE_SIZE`), so the pagination tests apply. `TOUCHSTONE_SRC` names
an existing clone to copy. `--unstable-search-results` starts the server
with the anticipatory results resource (issue 922; target ids get the
suffix `-unstable`); a default run never sets it. `--authz factoidal` runs the
authorization-on configurations with OUR `authz-serve` in place of the reference
authorization server (ids get the suffix `-fas`; `skills/authz-server`). `--merkle` starts the server with the
optional Merkle hashes (issue 919; ids get the suffix `-merkle`).

Five tests have preconditions that exclude one another, so no one server
configuration applies all of them. `--config alt-nomove` (`--moves off`),
`alt-datamove` (`--moves data`), `alt-linkset-noput` (`--no-linkset-put`)
and `alt-onepage` (`--page-size 100 --paginate-always`) each run with
authorization on; `--config alt` runs the four, `--config all` runs open,
auth and the four, and then prints a union line (per test: passed in at
least one configuration, failed in any, never applied; `union.tsv` in
`TOUCHSTONE_OUT`). A failure in any configuration is exit 1. Measured
2026-10-21 with `--config all --unstable-search-results`: 220 passed in at
least one configuration, 0 failed, 1 never applied (out of 221); the same on
2026-10-22 after issues 914, 915 and 920. Touchstone subscribes with
`inbox: "${storage}"` (the storage description), so an inbox check must not
refuse a non-container path of this server. The one is
`core/moving#move-keeps-identifier-content-and-links`: it needs
`"preservesIdentifier": true`, and our identifiers are paths (not
applicable to this design; the record quotes lws10-core Discovery). Delete the Maven repository after a run (the
script's work directory, about 260 MB). Results and every failure with its
spec text: `docs/designissues/2026-10-21-lws-touchstone-run.md`.

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

## The LWS client (https://github.com/danbri/factoidal/issues/917)

Design record: `docs/designissues/2026-10-22-lws-client.md` (requirements
table: each client statement of the drafts, the Lean definition that decides
it, the Touchstone rule that observes it).

One pure state machine decides everything:
`L4Factoidal.LWS.Client.step : Verifiers → ClientState → Event → ClientState × Action`
(`L4Factoidal/LWS/Client/Machine.lean`). The caller gives an operation
(`Op`, kinds `discover`, `read`, `head`, `create`, `update`, `patch`,
`delete`, `readLinkset`, `updateLinkset`, `move`, `list`, `typeIndex`,
`search`, `subscribe`, `unsubscribe`, `requestAccess`, `grantAccess`,
`getAccess`, `revokeAccess`, `verifyNotification`); `step` names each
request (`fetch`) and ends with `done` or `fail`. In Lean: the 401 flow
(the three checks of §Discovery Validation by a Client, RFC 8414 metadata
at `/.well-known/lws-configuration`, RFC 8693 token exchange, `Bearer`
only to URLs under the StorageRoot of the token's storage or under a
`serviceEndpoint` of its storage description on the requested URI's origin),
preconditions
(`update`, `patch`, `updateLinkset`, `move` default to the current ETag),
the 412, 405/415 and 5xx retry rules, paging by `rel="next"` only, linkset
writes only in advertised methods and formats, and the RFC 9421 check of a
webhook notification (keyid with a fragment, document id, digest,
signature by HACL*).

401 handling (`on401`): the current challenge (`resource_metadata` and a
`Link rel=lws#storage`) takes the three checks. A 401 with only `Bearer
as_uri="AS", realm="STORAGE"` (the drafts before 2026-10-19; css and
sparq-lws still send it) is followed only with the session option
`legacyChallenge` (npm `createLwsClient({ legacyChallenge: true })`, CLI
`--legacy-challenge`; off by default): the realm must have the scheme and
authority of the requested URL and contain it; `as_uri` is the authorization
server and the realm is the token's storage and root. That path skips checks
1 and 2 of §Discovery Validation by a Client, which is why it is off by
default; the driver adapter turns it on, as the Java and JS clients follow
it always (https://github.com/danbri/factoidal/issues/1115). `subscribe`
with `endpoint` (CLI `--endpoint`) POSTs to the named notification endpoint
with no storage-link discovery.

Three options of https://github.com/danbri/factoidal/issues/1116:

- Session option `requireHttps` (npm `createLwsClient({ requireHttps: true })`,
  CLI `--require-https`; off by default): `enforce` refuses, before it is sent,
  every request whose URL scheme is not `https`, in every phase (the
  operation, discovery, the protected resource metadata, the authorization
  server metadata, the token endpoint). The failure has code
  `insecureTransport` with the URL; the driver error kind is `TransportError`.
  Theorems `step_requireHttps`, `start_requireHttps`. The driver adapter maps
  `allowInsecureHttp: false` to it (stricter than the lws-client design,
  which asks https only of the authorization server and excepts loopback).
- Operation member `ifNoneMatchTags` (CLI `--if-none-match TAG[,TAG]`; for
  `read` the CLI flag sets the GET's `ifNoneMatch`): `If-None-Match` with
  entity tags on a write (RFC 9110 §13.1.2), read by `entityTagList?` (each
  member may be a list; `*` only alone). With no `precondition` it is
  `ifNoneMatch` (the field alone); with `ifMatch`, `ifMatchCurrent` or
  `ifUnmodifiedSince` both fields go (RFC 9110 §13.2.2 orders their
  evaluation). Refused with `none` and `ifNoneMatchStar`. Every conditional
  kind takes it, `patch` included.
- Operation member `policies` (CLI `--policies JSON`): an access request or
  grant with N policies, each `{actions, assignee, targets, constraint}`, in
  the caller's order. The single-policy members stay as one policy; giving
  both is `badArguments`.

| path | what it is |
| --- | --- |
| `formal/lean4/L4Factoidal/LWS/Client/Wire.lean` | requests, responses, `Link`, `WWW-Authenticate`, `Allow`, `Accept-Patch`, form bodies, JSON forms |
| `formal/lean4/L4Factoidal/LWS/Client/Machine.lean` | `Op`, `ClientState`, `step`, `enforce`, state JSON |
| `formal/lean4/L4Factoidal/LWS/Client/Theorems.lean` | `walk_concat`, `walk_paths`, `walk_members_once`, `walk_listedMembers`, `step_write_precondition`, `step_no_token_request_without_validation`, `step_no_blind_create_retry`, `step_no_retry_after_lost_post`, `step_no_repeat_after_refusal`, `step_requireHttps`, `start_requireHttps` |
| `formal/lean4/L4Factoidal/LWS/Client/Tests.lean` | `#guard`s: canned responses (decoys, stale tags, 405, 503, forged notifications) and a loopback against `LWS.step MemStore` |
| `formal/lean4/Wasm/Ops/LwsClient.lean` | `lwsClientStart(opJson, sessionJson)`, `lwsClientStep(stateJson, eventJson)` → `{ok, state, action}` |
| `npm/factoidal/lws/client.mjs` | `createLwsClient({ fetch, subjectToken, subjectTokenType, session, legacyChallenge, requireHttps })`, `createNotificationReceiver({ client })` |
| `tests/lws/client/own-server.mjs` | our client against our server, open and with authorization |
| `tools/lws-touchstone-client.sh` | our client in Touchstone's client lab (53 rules) |

The `step_*` theorems hold because `step` ends with `enforce`, which turns a
violating action into `fail`; the `#guard`s show the ordinary flows never
reach it. The state crosses the ABI as JSON; bodies as `bodyBase64`.

```
factoidal lws-client <op> URL [--body TEXT|--file PATH] [--content-type M]
    [--if-match TAG|--if-match-current|--if-none-match-star|--no-precondition]
    [--if-none-match TAG[,TAG]] [--require-https]
    [--retry-412 N] [--recursive] [--container] [--slug S] [--type IRI]
    [--subject-token-file F --subject-token-type URI] [--query JSON]
    [--inbox URL] [--topic URL] [--endpoint URL] [--legacy-challenge]
    [--action A,B --assignee URI --target URL | --policies JSON]
```

```js
import { createLwsClient } from '@factoidal/core/lws/client'
const c = await createLwsClient({ fetch, subjectToken, subjectTokenType })
const { location } = await c.create(containerUrl, { slug: 'a.txt', mediaType: 'text/plain', body: 'x' })
```

`fetch` is injected: Node's, a browser's, or one that carries requests over
XMPP. A credential is a subject token (`subjectToken`, `subjectTokenType`,
for example a SAML assertion) or a P-256 key (`selfIssued: { subject, keyId,
jwk }`), from which the engine signs a self-issued credential (ES256, HACL*;
the host gives `now` and 48 random bytes with each response event).
`step` takes `Authz.Crypto` (the verifiers and signers of
https://github.com/danbri/factoidal/issues/916). Gap, an expected failure in
`tests/lws/client/touchstone-xfail.tsv`: OpenID sign-in (code flow with
PKCE) for `client-oidc-token-type-id-token` (issue to open; the row names
https://github.com/danbri/factoidal/issues/917).

The driver adapter (https://github.com/danbri/factoidal/issues/1065,
`deploy/lws-client-adapter/`, check it with `driver/adapters/check.mjs` of
ebremer/lws-client: 37 passed, 0 failed, 0 skipped) only translates JSON.
Each `done` document has a `report` (the driver's Metadata, Item, Page, Storage
and Subscription shapes, `Client/Report.lean`) and each `fail` a `report` with
the error kind. A session key may be P-256 or Ed25519; `createDidKey({
algorithm })` (wasm op `lwsClientNewKey`, `Client/Keys.lean`) makes a
`did:key` agent. An operation can name its linkset (`linksetUrl`), service
endpoint (`endpoint`) or storage description (`storage`) directly. Rule:
the adapter reads no response; `tools/host-purity-lint.sh` group 4 checks it.

## WebDAV for file browsers (https://github.com/danbri/factoidal/issues/1066)

Design record: `docs/designissues/2026-10-27-webdav.md` (mount file format,
the WebDAV and LWS mapping, statuses, limits, what each client needs).

```
factoidal webdav-serve CONFIGDIR [--port N] [--host ADDRESS]   # default 127.0.0.1:8090
```

CONFIGDIR holds one Markdown file per mount (`README.md` is not one):

```
# Alice's files
- kind: local
- path: ./alice-storage

# (another file) Bob's remote storage
- kind: lws
- url: https://storage.example/bob/
- auth: did-key
- key-file: ./bob.jwk
- writable: true
```

* `local`: an `lws-serve` storage directory, opened with the same ops
  (`openLwsStorage`, `insecureNoAuth`: the WebDAV server is the owner,
  pagination off). Do not serve the directory with `lws-serve` at the same
  time. `storage: snapshot|files` defaults to what the directory holds.
* `lws`: the LWS client (`L4Factoidal/LWS/Client/`); `did-key` signs a
  self-issued credential with the P-256 key file (made, mode 0600, when it
  does not exist; the start line prints the `did:key`), `bearer` sends the
  token file's access token. To give a key access, start `lws-serve DIR
  --authz ASDIR --owner <that did:key>`.
* Connect: macOS Finder, Go > Connect to Server, `http://127.0.0.1:8090/`;
  Windows, Map network drive, `http://127.0.0.1:8090/`; GNOME Files,
  `dav://127.0.0.1:8090/`; KDE Dolphin, `webdav://127.0.0.1:8090/`. Not yet
  checked with these clients: https://github.com/danbri/factoidal/issues/1079.
  rclone and cadaver are: `node tests/webdav/clients.mjs` (11 pass, 0 fail,
  out of 11, on 2026-10-28; `apt-get install rclone cadaver`).

| path | what it is |
| --- | --- |
| `formal/lean4/L4Factoidal/WebDAV/Config.lean` | mount files (one loop; theorem `scan_known`) |
| `formal/lean4/L4Factoidal/WebDAV/Server.lean` | every method as a program over six storage operations (`Backend.Prog`); theorem `refused_keeps_state` |
| `formal/lean4/L4Factoidal/WebDAV/Local.lean`, `Remote.lean` | an operation as one LWS request; as one LWS client operation (the one module that uses the client API) |
| `formal/lean4/L4Factoidal/WebDAV/Xml.lean`, `If.lean`, `Path.lean` | XML bodies (depth limit 256, work-list serializer), the `If` header, targets |
| `formal/lean4/L4Factoidal/WebDAV/State.lean` | `DavState` (dead properties, locks) as the JSON text of `CONFIGDIR/.webdav-state.json`, and back; refuses an unknown format or version |
| `formal/lean4/L4Factoidal/WebDAV/Tests.lean`, `Theorems.lean` | `#guard`s of every method against `LWS.step MemStore`, directly and through the client; `browse_no_write` |
| `formal/lean4/Wasm/Ops/WebDAV.lean` | `webdavOpen`, `webdavLoad`, `webdavStep`, `webdavResume`, `webdavClose` |
| `npm/factoidal/webdav/server.mjs` | the host: sockets, the files the engine names, `lws` requests to the storage handle, `fetch`es |

Tests: `node tests/webdav/server.mjs` (every method through a local and a
remote mount on `lws-serve --authz`; dead properties and locks survive a
restart: the engine reads and names writes of `CONFIGDIR/.webdav-state.json`,
form in `L4Factoidal/WebDAV/State.lean`,
https://github.com/danbri/factoidal/issues/1078), `node tests/webdav/litmus.mjs` (needs `apt-get install
litmus`; expected failures in `tests/webdav/litmus-xfail.tsv`; 2026-10-27:
208 pass, 0 fail, 0 xfail (out of 208)), `node tests/webdav/scaling.mjs`
(the decoders at n, 2n, 4n through the wasm module).

## Run the tests

```
node tests/lws/server.mjs
node tests/solid/server/protocol.mjs
node tests/solid/client/against-own-server.mjs
node tests/lws/client/own-server.mjs
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

## Our LWS client against other servers (Touchstone interop)

Touchstone's `targetservers/interop-all.sh` builds the six LWS target servers
and drives each client through one scenario against each
(`targetservers/tools/interop.mjs`; results in `targetservers/runs/<time>-interop/`).
Our client takes part through `deploy/lws-client-adapter/adapter.mjs`
(lws-driver/1), registered as an extra language of the lws-client driver.
The stock `clients` image builds eleven client toolchains and does not fit a
session disk of about 16 GB: build a small clients image with only the driver,
the Java and JS adapters and ours, and pass `--languages java,js,factoidal`.
In a cloud session every Dockerfile also needs the proxy CA (`/root/.ccr/`)
and a git HTTPS rewrite; keep those changes in local copies, never in
Touchstone's tree. Start `dockerd` first. Results of 2026-10-28 and the three
client defects they found: `docs/designissues/2026-10-21-lws-touchstone-run.md`
§ "Client interop", https://github.com/danbri/factoidal/issues/1115.

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
issuance (the LWS authorization server, `authz-serve`, issues LWS access
tokens, which solid-serve does not accept yet:
https://github.com/danbri/factoidal/issues/928), Access Control Policy, Solid Notifications channels on the Solid
server (the LWS server has the webhook suite, above),
and persistence into Shardborough. The LWS `authn-openid`, `authn-ssi`
and `authn-saml` drafts are implemented by the authorization server
(`skills/authz-server`; SAML: https://github.com/danbri/factoidal/issues/926,
record `docs/designissues/2026-10-27-saml-xml-signature.md`).

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
