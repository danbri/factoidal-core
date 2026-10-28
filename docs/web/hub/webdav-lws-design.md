---
title: WebDAV, LWS and custodians
description: What the 0.21.0 WebDAV and LWS theorems say and do not say, the principle behind them (one custodian per privileged resource), and the plan for careful read-write LWS mounts and read-only projections of SPARQL, SKOS, feeds and public pods.
layout: hub.njk
tests: tests/hub/hub_webdav-lws-design_test.mjs
---

# WebDAV, LWS and custodians

<p class="warning"><strong>⚠️ EXPERIMENTAL UNREVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.</strong> This covers the whole core
library and every command line tool, and in particular all protocol,
authentication and security code.</p>

[Hub](../) · [WebDAV](../webdav/) · [Servers](../servers/) · what changed, WebDAV within LWS, the theorems, custodians, read-write, projections, status

This page is a design note, not a tutorial: it has no live cells.
`tests/hub/hub_webdav-lws-design_test.mjs` checks that every theorem it names
is declared in the Lean sources. Issue:
<https://github.com/danbri/factoidal/issues/1147>.

## What changed in 0.21.0

Up to 0.20.0, `webdav-serve` had two ways around the access rules of the LWS
storages it served:

1. Whoever reached the listener got the rights of a mount's LWS agent: macOS
   "Guest", or any name and password, acted as the agent whose key the mount
   names, the storage owner included.
2. A `kind: local` mount opened a storage with no authorization at all, so
   it could read and replace the storage's ACL.

`solid-serve` had a third: over a directory that held an LWS storage, it served
that data under Solid rules, with no authentication through the library path.

In 0.21.0:

* `webdav-serve` is **read only**, and every request acts as **one named
  user**: a `--users` login, or the `--guest NAME` user for a request with no
  credentials (no `--guest`: 401). Each mount names the users that may use it
  (`users:`); anyone else gets 404 for that mount, as for a mount that does
  not exist.
* `kind: local` mounts are refused. `auth: bearer` with a token file from
  outside the installation needs `allow-external-token: true`.
* `solid-serve` refuses a directory that holds an LWS storage.

## "WebDAV stays within LWS"

In one sentence: **WebDAV only gets to LWS data through LWS's standard data
interface; it does not have a parallel path to LWS-controlled data.**

1. **No back door.** Every mount that `webdav-serve` accepts points at an LWS
   server. The local path, which opened a storage's files with authorization
   off, cannot be configured.
2. **Every storage operation is an LWS request.** Whatever a WebDAV request
   causes, each storage operation leaves `webdav-serve` only as a request of
   Factoidal's LWS client to that mount's LWS server, with that mount's agent.
   The LWS server makes its usual decision (token check, ACL).
3. **Reads only**, for now: head, list or get.
4. **Listed users only.** Anyone not in the mount's `users:` causes no storage
   operation.

So through WebDAV a person can only read what the mount's LWS agent could read
over LWS directly, and only if the configuration lists them for that mount.

**Not yet:** every user listed for a mount acts as the mount's one agent. If
Guest is listed on a mount whose agent is the owner, Guest reads what the owner
can read: within LWS's rules for that agent, but the configuration, not LWS,
decides who gets which agent. The next step is an LWS agent of its own for each
WebDAV user. "WebDAV answers success only when LWS said yes" is proved as
lemmas, not yet as one end-to-end theorem.

## The theorems

All in Lean 4, with no `sorry` and no axiom beyond Lean's standard three
(`propext`, `Classical.choice`, `Quot.sound`).

| Theorem | File | What it says |
| --- | --- | --- |
| `load_no_unauthorized_storage` | `L4Factoidal/WebDAV/Theorems.lean` | Every mount of an accepted configuration is `kind: lws`: no storage is opened without authorization. |
| `webdav_within_lws` | `L4Factoidal/WebDAV/Theorems.lean` | Every storage operation that a request causes is a read, on a mount that lists the request's user, and leaves the server only as an LWS client operation on that mount. |
| `handle_no_write` | `L4Factoidal/WebDAV/Theorems.lean` | No request causes a write. |
| `hidden_mount_no_op`, `hidden_mount_trace` | `L4Factoidal/WebDAV/Theorems.lean` | A user who is not in a mount's `users:` causes no storage operation on it. |
| `lws_data_only_through_authorized_step` | `L4Factoidal/LWS/AccessTheorems.lean` | Only the LWS request handler reads or changes an LWS storage's data, and only after `Authorization.decide`; a refused request changes nothing. |
| `insecureNoAuth_is_the_exception` | `L4Factoidal/LWS/AccessTheorems.lean` | The one exception: with `insecureNoAuth` (`lws-serve --insecure-no-auth`), every request proceeds as the configured agent. |
| `agent_ignored_under_authorization` | `L4Factoidal/LWS/AccessTheorems.lean` | With authorization on, the configured agent is not used. |
| `lws_only_lwsStep_serves` | `Wasm/Ops/Lws.lean` | Of the engine's LWS ops, only `lwsStep` serves resource content (the handle tables are private to these ops). |
| `solidRefusesLws_snapshot`, `solidRefusesLws_files` | `Wasm/Ops/Solid.lean` | `solid-serve` refuses a storage written by `lws-serve`, in both storage layouts. |

Not covered: file system access to a storage directory (encryption at rest,
`FACTOIDAL_LWS_KEY`, addresses it); JavaScript in the same process; anything
outside Factoidal.

## One custodian per privileged resource

The two theorems are instances of one principle. Wherever Factoidal's boundary
ends in privileged access to something outside it — a pod's storage, a private
key, a store on disk, an account, network access — exactly **one** component (one
node in the dataflow view) holds that privilege and is responsible for it:

* it is the only holder of the handle or credential;
* every other part of Factoidal asks it, through its interface, and every
  request names a principal, about which the custodian decides;
* the interface can be an internal API call: the transport is not what makes it
  safe, the single decision point is.

This is a reference monitor (complete mediation, tamper-proof, small enough to
verify), and in Factoidal each property can be proved rather than asserted.
For LWS it is already so: the request handler is the custodian of hosted
storage data, its handle tables are private, and the dispatch table is checked.

Consequences:

* **Internal calls instead of the public protocol.** A WebDAV mount of a
  storage hosted in the same process can call the storage's custodian
  directly, with the principal, instead of speaking LWS over HTTP. That is also
  how local mounts can come back safely.
* **Keys stop travelling.** A key's custodian signs on request; the key never
  leaves it. No LWS credential can be plugged into another wrapper.

How to make it enforceable:

| Step | Means |
| --- | --- |
| Inventory | each privileged resource with its one custodian: LWS storages (the LWS handler), agent and signing keys (a key store that signs, never hands out keys), `FACTOIDAL_LWS_KEY` (the sealing layer), stores on disk (the store session), outgoing fetches (one fetch node with the private-address guard), XMPP accounts and TLS keys (their servers) |
| Structure | private handles and opaque types in Lean, so only the custodian's module can touch the resource |
| Gate | the dataflow and entry-point gates map each resource class to exactly one custodian stage; another path fails the build |
| Theorem | one shape per custodian: every effect on the resource is an output of the custodian's step after its decision for the named principal, and no other op reaches it |

## Read-write LWS mounts, carefully

Read only is right for most projections; for LWS, read-write comes back, but
only when:

1. each WebDAV user acts as an LWS agent of its own, so the storage's ACL
   judges the person;
2. every write goes through the custodian (LWS PUT, POST, DELETE, the move
   capability, linkset PATCH), with the theorem extended: every write that a
   WebDAV request causes is an LWS write by the requesting user's agent.

| Behaviour | Responsible handling |
| --- | --- |
| Two editors, one file | conditional writes (`If-Match` on the version read, `If-None-Match: *` on create); a conflict is an error, never a silent overwrite |
| macOS writes a file on close | refuse `LOCK` when the agent may not write, so the open fails first; prove "WebDAV success only on LWS success" end to end |
| WebDAV locks | LWS has no locks: keep them advisory and documented, or make each write conditional on the version seen at lock time |
| MOVE, COPY, rename | LWS's move capability where it fits; else a bounded, conditional copy, deleting the original only after the copy succeeded |
| Dead properties (PROPPATCH) | map them to the resource's linkset through its PATCH interface, or refuse them; no parallel WebDAV-side store |
| `._*` and `.DS_Store` files | a stated policy (refuse, keep in memory, or store); never clutter a storage silently |
| Media types | keep the storage's `Content-Type` on overwrite; guess only for new files |

The full RFC 4918 read-write server is kept in the code (`handleRW`, with its
tests), so writes come back by routing it through the custodian, not by a
rewrite.

## Read-only projections

The same pattern serves other sources as folders and files, for anyone at home
in a file browser. Each source is used only through its standard interface,
with the requesting user's identity, and the theorem template is the same.

| Source | Interface | As files |
| --- | --- | --- |
| SPARQL endpoint | SPARQL Protocol, Graph Store Protocol | `graphs/` (one Turtle file per named graph), `queries/*.rq` shown as `.csv` or `.json` results, `resources/` (one DESCRIBE per IRI) |
| LWS, public data | the LWS client with no login | a pod's public part; the pod's ACL decides |
| Atom, RSS | HTTP GET of the feed | a folder per feed, a file per entry |
| SKOS | SPARQL or a SKOS file | schemes as folders, `skos:narrower` as subfolders, a file per concept named by its preferred label; a concept with two broader concepts appears in both |

Questions to settle first: stable, safe names from labels (with the IRI
recoverable, for example from `.about.ttl` in each folder); caching and limits,
so that listing a folder does not start an expensive query; and which
credential each source sees.

## Status (2026-10-28)

* 0.21.0: read-only WebDAV with named users and a guest, no local mounts, the
  theorems above, and the `solid-serve` refusal.
* Next: a design record and issue for the custodian principle (inventory,
  structure, gate, theorem template); an LWS agent per WebDAV user; then
  read-write LWS mounts; then read-only projections.
