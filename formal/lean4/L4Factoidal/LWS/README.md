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
| `RootAclInstall.lean` | the first root ACL of an EXISTING storage (a storage made with `insecureNoAuth` has no `/.acl`). At open, with authorization on and a root ACL given (`rootAcl`, or `Authorization.ownerRootAcl` of `owner`), a storage with no `/.acl` gets the given one, before any request is answered; the op layer (`Wasm/Ops/Lws.lean`, `installRootAcl`) runs it in `lwsOpen` (a snapshot) and at the end of `lwsLoad` (a storage kept in files), and answers `changed` and `rootAclNotice`. Theorems below. |
| `NoLockout.lean` | no request leaves a storage without an agent that has `acl:Control` on its root: `RootControl` (WAC's `Solid.Server.allowed`, mode `control`, on the root, for some requester), the decision `hasRootControl` (equal to it), the guard `lockout`, and the offline operator reset `reset` (`factoidal lws-acl-reset`). Theorems below. |
| `NoLockoutTheorems.lean` | the guard in `Handler.step` (`Handler.lockoutGuard`): `step_keeps_root_control`, `decided_served_guarded`. |
| `Notifications.lean` | notifications: the core draft's "Notifications" section and the webhook notification suite (`lws10-notifications-webhook`), both at w3c/lws-protocol 9a08ff65 — discovery, subscriptions (subscribe-time and delivery-time authorization), the changes of a step (`changesOf`, theorem `classify_sound`), routing (theorem `routed_authorized`), Activity Streams 2.0 envelopes, RFC 9421 signatures, retry and deactivation, and `serverStep`, which the wasm handle runs (https://github.com/danbri/factoidal/issues/890). |
| `NotificationsTests.lean` | `#guard`s through `serverStep`, positive and negative, and `lwsGuardNotificationsDelivered` for the registry row `lws-core-16`. |
| `Move.lean` | moving resources (LWS §Moving Resources, https://github.com/danbri/factoidal/issues/914): the `up` link of a linkset changed by JSON Patch or PUT, the refusals (409: destination missing or not a container, a cycle, the storage root, a name already taken, another storage), `move` as one function from store to store, and the theorems `move_tree` (the store stays a containment tree; with `tree_acyclic`, `parentOf_unique`, `tree_parent`), `move_unmoved`, `move_moved`, `move_vacated`. |
| `MoveRedirect.lean` | 301 Moved Permanently at the previous identifiers of a moved resource (LWS §Moving Resources SHOULD, issue 914): a bounded table of (previous path, current path), pruned after every request and kept in the snapshot; the 301 only when the same request at the current path is authorized. Theorems `redirect_current`, `after_ok`, `redirect_after_move`. Guards: `MoveRedirectTests.lean`. |
| `InboxGuard.lean` | refuses a webhook inbox that names this server under another host name, an IP address or `localhost` (issue 915): IPv4 and IPv6 literals, the base IRI authority, the bound address and interface addresses, names the host resolved. |
| `MoveTests.lean` | `#guard`s through `step`, `Authorization.decide` and `Notifications.serverStep`, positive and negative, and `lwsGuardMoveResource`. |
| `Handler.lean` | `Handler.step`, the LWS request handler: one request against one storage (the guard, CORS, body files, inbox host, moved resources, search results, access grants, index services, notifications, the storage operation). The op `lwsStep` runs it. |
| `AccessTheorems.lean` | the 0.21.0 access theorem `lws_data_only_through_authorized_step`: every outcome of `Handler.step` either reads no state or comes from `Authorization.decide`, and a refused request changes nothing. The module doc lists the one exception (`insecureNoAuth`, `lws-serve --insecure-no-auth`) and what is not covered. |
| `Patch.lean` | the `?conditions` / `?insertions` / `?deletions` formula patch, its constraints, and `applyPatch`. Matching is `SPARQL.evalBgp` and instantiation is `SPARQL.instantiateTemplate` — no second matcher. |
| `DatasetView.lean` | the dataset view of a snapshot (issue 1011, version 2; Factoidal's definition, LWS does not define one): an empty default graph; a table-of-contents graph named by the storage description IRI (`lws:items`, the listing members, the link from each resource to its linkset); one named graph per RDF document and one per linkset (`relIri`: LWS vocabulary, else the IANA relation base); theorems `view_names_nodup`, `view_toc_first`, `view_replace`. The source theorem is `Dataflow/LwsSource.lean`. |
| `DatasetViewRead.lean` | the crawl plan of a listing (members to list, to read, and whose linksets to read), each read and each linkset read (RFC 9264 §4.2), over the client's `done` documents (wasm ops `lwsViewPlan`, `lwsDatasetView`); guards in `DatasetViewTests.lean`. |
| `Conformance.lean` | the registry: id, section, verbatim statement, module, binding, status. |
| `Tests.lean` | one `#guard` per `guarded` row, and the theorems the `proved` rows name. |

## The first root ACL of an existing storage (`RootAclInstall.lean`)

Before this, a storage made with `lws-serve --insecure-no-auth` and started
later with `--authz --root-acl FILE` refused every agent, its owner too,
because `--root-acl` was written only into a NEW storage; the way out was to
serve it with authorization off for a moment and PUT `/.acl`. Now the open
installs it. `install S i r s` is stated over every store with `StoreLaws`
(`i` is `insecureNoAuth`, `r` the root ACL given, `rootAclPath` is `/.acl`):

| theorem | statement |
|---|---|
| `install_only_when_absent` | `(install S i r s).2 = .installed → S.lookup s rootAclPath = none ∧ i = false ∧ r.isSome`: the open writes only when the storage has no root ACL, authorization is on and a root ACL is given. |
| `install_keeps_existing` | `S.lookup s rootAclPath = some e → (install S i r s).1 = s`: an existing root ACL is never replaced (the storage is returned unchanged). |
| `install_off_unchanged` | `install S true r s = (s, .none)`: with authorization off, nothing changes. |
| `install_no_acl_given_unchanged` | `(install S i none s).1 = s`. |
| `install_has_root_acl` | `StoreLaws S → (S.lookup (install S false (some b) s).1 rootAclPath).isSome`: after an open with authorization and a root ACL, the storage has a root ACL. |
| `install_writes_given` | `StoreLaws S → S.lookup s rootAclPath = none → S.lookup (install S false (some b) s).1 rootAclPath = some (rootAclEntry b (S.now s))`: what is written is the given body. |
| `install_other_paths` | `StoreLaws S → p ≠ rootAclPath → S.lookup (install S i r s).1 p = S.lookup s p`: no other resource changes. |
| `allowed_without_acl` | `(∀ q, S.lookup s (aclPathOf q) = none) → Solid.Server.allowed S parseAcl b s t who m = false`: the authorization decision is unchanged and fails closed; with no ACL resource, Web Access Control allows no agent any mode (WAC §5.3). |

`#guard`s at the end of the module check the three outcomes on `MemStore`.
The host prints `rootAclNotice` on standard error and persists when the open
says `changed`. The socket of `lws-serve` is bound before the open (the port
names `baseIri`), but every request waits for the open, which includes the
install; and before the install, authorization is already on and fails
closed. `L4Factoidal/Solid` (`solid-serve`) is not changed.

## No lockout of the root ACL (`NoLockout.lean`, `NoLockoutTheorems.lean`)

With authorization on, a request that changes the root ACL (the texts of the
ACL resources WAC reads for the root, `rootTexts`: `/.acl`) and leaves no
agent with `acl:Control` on the root is refused with 409, and changes
nothing. `RootControl S parseAcl b st` is `∃ who, Solid.Server.allowed S
parseAcl b st rootPath who .control = true`: the WAC decision every request
is checked with, not a second reader. 409, not 403: the requester was
allowed the request; it is refused for the state it would leave, and a 403
of this server carries `error="insufficient_scope"`, which tells a client to
get another token.

| theorem | statement |
|---|---|
| `hasRootControl_iff` | `hasRootControl S parseAcl b st = true ↔ RootControl S parseAcl b st`: the decision (WAC asked for `candidates` of the root ACL graph: the public, any authenticated agent, each `acl:agent` and `vcard:hasMember`) is the meaning. From `hasRootControl_sound`, `hasRootControl_complete` and `decideAccess_candidates`. |
| `allowed_of_texts` | `rootTexts S st = rootTexts S st' → allowed S parseAcl b st rootPath who m = allowed S parseAcl b st' rootPath who m`: WAC on the root reads only `rootTexts`. |
| `lockout_iff` | `lockout S parseAcl b before after = true ↔ rootTexts S before ≠ rootTexts S after ∧ ¬ RootControl S parseAcl b after`: exactly the lockouts are refused. |
| `accepted_keeps_control` | `lockout S parseAcl b before after = false → RootControl S parseAcl b before → RootControl S parseAcl b after`. |
| `guard_refused_unchanged` | `lockout … = true → guard S parseAcl b t before resp after = (refusal t, before)`: a refused request changes nothing. |
| `guard_keeps_control` | `RootControl S parseAcl b before → RootControl S parseAcl b (guard S parseAcl b t before resp after).2`. |
| `decided_served_guarded` | with `s.authz.insecureNoAuth = false`, a `served` outcome of `Handler.decided` is either the refusal (`resp.status = 409 ∧ s' = { s with mem := mem } ∧ ch = false ∧ ds = []`) or `lockout IS aclGraphOf baseIri mem s'.mem = false`. |
| `step_keeps_root_control` | `s.authz.insecureNoAuth = false → Handler.step V env s r x = .served resp s' ch ds → RootControl IS aclGraphOf env.cfg.baseIri (memOf s x) → RootControl IS aclGraphOf env.cfg.baseIri s'.mem`: for every request handled with authorization on, control of the root is kept. |
| `reset_has_control` | `reset S parseAcl b body st = .ok st' → RootControl S parseAcl b st'`: the operator reset leaves a Control agent. |
| `reset_writes` | `StoreLaws S → reset … = .ok st' → S.lookup st' rootAclPath = some (rootAclEntry body (S.now st))`. |
| `reset_other_paths` | `StoreLaws S → reset … = .ok st' → p ≠ rootAclPath → S.lookup st' p = S.lookup st p`: only `/.acl` changes. |
| `reset_refuses` | `¬ RootControl S parseAcl b (resetState S body st) → reset … = .error resetRefusal`. |

The NoLockout theorems hold for every `Store σ` (with `StoreLaws` where
stated); the handler theorems are about the store an LWS handle runs.
`#guard`s at the end of `NoLockout.lean` check, on `MemStore`, that a write
that removes the last Control agent is refused, a DELETE of `/.acl` is
refused, a write that keeps one is accepted, a write that swaps the owner for
another Control agent is accepted, public and group control count, control
of another resource does not, and the reset accepts and refuses.

The operator reset (`lwsAclReset`) runs only on a handle opened with
`"operator": true`, which opens only an existing storage and answers no
request; the host (`factoidal lws-acl-reset DIR FILE --operator`) takes the
storage directory lock first (`DirLock.decide`; theorems
`decide_alive_refuses`, `decide_otherHost_refuses`,
`decide_sameInstance_refuses`). That the host takes the lock before it opens
the storage, and reads the lock file honestly, is host code, not proved.

## What is pure and what is not

Everything in this directory is a total function. There is no socket, no
file read and no clock: the time comes from `Store.now`, which the host
sets, and every mutation calls `Store.tick`, so the modification times of a
request sequence are strictly increasing and the server-assigned names of
POST are distinct without a counter beside the clock.

The wasm entry layer (`Wasm/Ops/Lws.lean`) holds the state in a handle table
and is the only part that performs `IO`. The table is `private` to that file:
its ops (`lwsOpRole`) are the only engine code that reaches a storage handle,
and `lwsStep` is the only one that answers a request with resource content.

## Running it

```
cd formal/lean4
lake build L4Factoidal.LWS.Tests      # every #guard runs during the build
lake exe l4lws-probe                  # prints the registry counts
```
