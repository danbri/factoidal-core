# `L4Factoidal.LWS` — Linked Web Storage Protocol 1.0 Core

Source specification:
<https://w3c.github.io/lws-protocol/lws10-core/> — W3C Linked Web Storage
Working Group editor's draft, read 2026-09-06.

Design record:
[`docs/designissues/2026-09-06-lws-and-solid-protocols.md`](../../../../docs/designissues/2026-09-06-lws-and-solid-protocols.md).
Ledger: [`docs/lws-solid-conformance.md`](../../../../docs/lws-solid-conformance.md).
Tracking issue: <https://github.com/danbri/factoidal/issues/659>.

## What the draft states, and what it does not

The draft defines the resource model (LWS resource, container, data
resource, storage root, metadata resource, linkset resource, auxiliary
resource, containment, storage, storage root, storage description) and names
the four operations. Its `Operations`, `Containers`, `Discovery`,
`Authentication` and `Authorization` sections are headings with empty
bodies. It states two MUST statements about behaviour, both in the
CG-to-ED delta list:

* "HTTP Server MUST generate a Last-Modified header field in response to GET
  and HEAD requests."
* "The PATCH ?insertions formulae MUST NOT contain blank nodes."

It defines no HTTP binding, no status codes and no test suite. Wherever a
binding is needed, this implementation uses the Solid Protocol v0.11.0
binding, which the draft's Acknowledgements name as its source, and the
conformance registry row carries both citations. The day the draft fixes its
own binding, those rows are the difference.

## Files

| file | what it holds |
|---|---|
| `Model.lean` | `ResourceKind`, path and containment functions, `Link`, `Entry`. Identifiers are `RDF.WfIri`. |
| `Store.lean` | `Store σ`, a structure of pure operations over an abstract state; `StoreLaws`, what a backend must satisfy; `MemStore`, the reference instance, with `memStoreLaws` proving it does. |
| `Discovery.lean` | the RFC 8288 links a storage advertises: `type`, `acl`, `describedby`, `storageDescription`, `owner`. |
| `Operations.lean` | `step : Store σ → Config → Request → σ → Response × σ` — create, read, update, delete, `Last-Modified`, `Allow`, `Accept-*`, and the HTTP-date conversion. |
| `Pagination.lean` | container pagination: the listing order (increasing path, each path once), pages, page names `page=N`; theorems `orderPaths_sorted`, `orderPaths_nodup`, `pages_concat` (https://github.com/danbri/factoidal/issues/887). `Operations.pageItems_concat` applies them to `step`'s listing. |
| `Linkset.lean` | client-managed links: the `Link` request field parser, `Prefer: set-linkset`, the server-managed relations (409), link validation (400), and the linkset document read and written (https://github.com/danbri/factoidal/issues/888). |
| `PaginationLinksTests.lean` | `#guard`s of both through `step`, positive and negative. |
| `Authorization.lean` | storage-server authorization of the 2026-10-19 draft: Bearer tokens, RFC 9728 metadata, Web Access Control (https://github.com/danbri/factoidal/issues/886). |
| `Notifications.lean` | notifications: the core draft's "Notifications" section and the webhook notification suite (`lws10-notifications-webhook`), both at w3c/lws-protocol 9a08ff65 — discovery, subscriptions (subscribe-time and delivery-time authorization), the changes of a step (`changesOf`, theorem `classify_sound`), routing (theorem `routed_authorized`), Activity Streams 2.0 envelopes, RFC 9421 signatures, retry and deactivation, and `serverStep`, which the wasm handle runs (https://github.com/danbri/factoidal/issues/890). |
| `NotificationsTests.lean` | `#guard`s through `serverStep`, positive and negative, and `lwsGuardNotificationsDelivered` for the registry row `lws-core-16`. |
| `Move.lean` | moving resources (LWS §Moving Resources, https://github.com/danbri/factoidal/issues/914): the `up` link of a linkset changed by JSON Patch or PUT, the refusals (409: destination missing or not a container, a cycle, the storage root, a name already taken, another storage), `move` as one function from store to store, and the theorems `move_tree` (the store stays a containment tree; with `tree_acyclic`, `parentOf_unique`, `tree_parent`), `move_unmoved`, `move_moved`, `move_vacated`. |
| `MoveRedirect.lean` | 301 Moved Permanently at the previous identifiers of a moved resource (LWS §Moving Resources SHOULD, issue 914): a bounded table of (previous path, current path), pruned after every request and kept in the snapshot; the 301 only when the same request at the current path is authorized. Theorems `redirect_current`, `after_ok`, `redirect_after_move`. Guards: `MoveRedirectTests.lean`. |
| `InboxGuard.lean` | refuses a webhook inbox that names this server under another host name, an IP address or `localhost` (issue 915): IPv4 and IPv6 literals, the base IRI authority, the bound address and interface addresses, names the host resolved. |
| `MoveTests.lean` | `#guard`s through `step`, `Authorization.decide` and `Notifications.serverStep`, positive and negative, and `lwsGuardMoveResource`. |
| `Patch.lean` | the `?conditions` / `?insertions` / `?deletions` formula patch, its constraints, and `applyPatch`. Matching is `SPARQL.evalBgp` and instantiation is `SPARQL.instantiateTemplate` — no second matcher. |
| `DatasetView.lean` | the dataset view of a snapshot (issue 1011; Factoidal's definition, LWS does not define one): `ldp:contains` in the default graph, one named graph per RDF resource; theorems `view_names_nodup`, `view_replace`. The source theorem is `Dataflow/LwsSource.lean`. |
| `DatasetViewRead.lean` | the crawl plan of a listing and each read, over the client's `done` documents (wasm ops `lwsViewPlan`, `lwsDatasetView`); guards in `DatasetViewTests.lean`. |
| `Conformance.lean` | the registry: id, section, verbatim statement, module, binding, status. |
| `Tests.lean` | one `#guard` per `guarded` row, and the theorems the `proved` rows name. |

## What is pure and what is not

Everything in this directory is a total function. There is no socket, no
file read and no clock: the time comes from `Store.now`, which the host
sets, and every mutation calls `Store.tick`, so the modification times of a
request sequence are strictly increasing and the server-assigned names of
POST are distinct without a counter beside the clock.

The wasm entry layer (`Wasm/Ops/Lws.lean`) holds the state in a handle table
and is the only part that performs `IO`.

## Running it

```
cd formal/lean4
lake build L4Factoidal.LWS.Tests      # every #guard runs during the build
lake exe l4lws-probe                  # prints the registry counts
```
