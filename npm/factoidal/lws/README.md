# `@factoidal/core/lws` — a Node host for Linked Web Storage 1.0

The W3C Linked Web Storage Protocol 1.0 core
(<https://w3c.github.io/lws-protocol/lws10-core/>, Linked Web Storage
Working Group editor's draft) served over Node's `http` module.

Tracking issue: <https://github.com/danbri/factoidal/issues/659>.
Design record:
[`docs/designissues/2026-09-06-lws-and-solid-protocols.md`](../../../docs/designissues/2026-09-06-lws-and-solid-protocols.md).
Conformance ledger:
[`docs/lws-solid-conformance.md`](../../../docs/lws-solid-conformance.md).

## What is here and what is not

`server.mjs` is a socket, a body reader and a header writer. Every
protocol decision — status codes, `Link` relations, `Last-Modified`,
containment, the blank-node refusal in PATCH — is made by
`formal/lean4/L4Factoidal/LWS/` and reaches this file only as a
`{status, headers, body}` record. Iron rule 7 of `CLAUDE.md`: no
protocol logic in a host.

The one status code this file writes itself is `500`, and only when the
host or the engine failed rather than answered.

## The wasm contract

| op | arguments | answer |
| --- | --- | --- |
| `lwsOpen` | `[configJson]` | `{ ok, handle, root }` |
| `lwsStep` | `[handle, requestJson]` | `{ ok, response, changed, deliveries?, wake? }`, or `{ ok, resolve: { host } }` |
| `lwsClose` | `[handle]` | `{ ok }` |
| `lwsSnapshot` | `[handle]` | `{ ok, snapshot }` |
| `lwsFetched` | `[handle, documentJson]` | `{ ok, fetch? , installed?, refused? }` |
| `lwsDelivered` | `[handle, reportJson]` | `{ ok, changed, retry? }` |
| `lwsFlush` | `[handle, { now? }]` | `{ ok, changed, deliveries?, wake? }` |

```
request  { method, target, headers: [[name, value]] } + the content as bytes
response { status, headers: [[name, value]], bodyBytes } + the content as bytes
(through callBlobIO; https://github.com/danbri/factoidal/issues/889)
```

`headers` is a list of pairs, not an object: HTTP allows a field name to
repeat and the order of repeated fields carries meaning. `target` is a
path within the storage, so Node's `request.url` is passed through
unchanged and this host composes no IRI.

`configJson` members, all optional: `baseIri` (the absolute IRI the
storage root maps to), `now` (the engine clock in seconds, which advances
by one second per mutation so a write sequence has increasing
`Last-Modified` values with no real clock), `owner`, `agent`, `pageSize`
(the container pagination threshold and page size, default 100, 0 for no
pagination), `rootAcl`, `auth` and `insecureNoAuth` (below),
`notifications` (default true) and `entropy` (random bytes, base64, which
this host makes for every open). A request
may carry `now` and `agent` of its own to override the handle's for one
step; `listen({realClock: true})` is how a server with a real clock feeds
one in, and a test leaves it off to keep the engine's deterministic
clock. The full contract is `docs/lws-solid-conformance.md`, section
"wasm ABI".

A WebAssembly module built before these ops landed answers `unknown op`.
`lwsOpsAvailable(engine)` reports that as `{available: false, reason}`,
and every test in `tests/lws/` skips with the reason printed rather than
passing on an engine that cannot answer.

## Authorization

Authorization follows the draft's "Authorization" section
(https://github.com/danbri/factoidal/issues/886) and is decided by
`formal/lean4/L4Factoidal/LWS/Authorization.lean`. It is ON by default.

```js
const running = await listen({
  port: 3000,
  owner: 'https://id.example/alice',          // root ACL: Read, Write, Control
  auth: { issuers: [{ issuer: 'https://as.example' }] },
  realClock: true
})
```

* Clients send `Authorization: Bearer <access token>` (RFC 6750). The
  token is a JWT (RFC 9068) signed with ES256, RS256 or EdDSA by a trusted
  issuer; `aud` must contain the storage IRI (`baseIri`, or `auth.audience`).
* Without a valid token the answer is 401 with
  `WWW-Authenticate: Bearer resource_metadata="…"`; the RFC 9728 metadata
  document is served at `/.well-known/oauth-protected-resource<path>`.
* The host fetches the issuer's `/.well-known/lws-configuration` and its
  `jwks_uri` when the engine asks (`lwsStep` answers `{ fetch }`), passes
  the bytes to `lwsFetched`, and steps again. `auth.issuers[].jwks` gives
  the keys inline instead.
* `insecureNoAuth: true` serves every request with no authorization. It is
  for development only, and must be asked for.

## Pagination and client links

Both are decided in Lean; this host passes the fields through.

* A container with more than `pageSize` members (default 100) is listed in
  pages (LWS §LWS Media Type, Pagination;
  https://github.com/danbri/factoidal/issues/887). Each page answers 200
  with the `Link` relations `first` and `last`, `next` on every page but the
  last, and `prev` on every page but the first; the page URIs are
  `CONTAINER?page=N`. `totalItems` counts the full membership. The members
  are in increasing path order, each once; the theorem `pageItems_concat` in
  `L4Factoidal/LWS/Operations.lean` states that the pages of an unchanged
  container concatenate to the full listing. Each page has its own `ETag`,
  which starts with the container's clock; the clock changes when the
  membership changes.
* A client sets its own links (`license`, `author`, any extension relation)
  with `Link` and `Prefer: set-linkset` on PUT (replace) or PATCH (add),
  with `Link` on POST, or through the linkset resource `PATH?linkset` with
  JSON Patch or a PUT of `application/linkset+json` (LWS §Metadata, §Update
  Resource; https://github.com/danbri/factoidal/issues/888). The relations
  `linkset`, `type`, `format`, `size`, `modified`, `up`, `items` and
  `lws#storage` are server-managed: a request that sets or changes one gets
  409. A malformed link gets 400. Without `Prefer: set-linkset`, a `Link`
  field on PUT and PATCH is not stored.

## Notifications

LWS notifications and the webhook notification suite
(https://github.com/danbri/factoidal/issues/890) are decided by
`formal/lean4/L4Factoidal/LWS/Notifications.lean`. They are on unless
`notifications: false` is passed.

* The storage description at `/.well-known/lws-storage` names the
  `NotificationService`: endpoint `/.well-known/lws-subscriptions/`, type
  `WebhookSubscription`, and the Ed25519 key that signs deliveries.
* A client POSTs `{"type":"WebhookSubscription","topic":[IRI…],"inbox":URL}`
  (`application/lws+json`, with a token when authorization is on) and gets
  201 with the subscription URL. GET on the endpoint lists the agent's
  subscriptions; GET and DELETE manage one.
* After a write, `lwsStep` names the deliveries: `{ id, url, headers, body }`.
  This host POSTs each one exactly as given, after the response, and reports
  the status to `lwsDelivered`; when the engine answers `retry`, it waits
  `after` seconds and sends the delivery it names. `storage().settled()`
  resolves when no delivery is in flight.
* Rate limit (https://github.com/danbri/factoidal/issues/915): at most
  `deliveryLimit` deliveries (default 10) per subscription in a window of
  `deliveryWindow` seconds (default 60; `deliveryLimit: 0` turns it off).
  The rest wait; an answer then carries `wake: SECONDS`, and this host calls
  `lwsFlush` after that many seconds and sends the one batched delivery it
  names.
* Inbox check (issue 915): when an inbox host is a name, `lwsStep` answers
  `resolve: { host }`; this host resolves it (`dns.lookup`, every address)
  and steps the request again with `resolved: [{ host, addresses }]`.
  `listen()` passes `listen: { address, port, addresses }` to `lwsOpen`. The
  engine refuses a container of this storage under another name of this
  server.
* `controllerInbox: URL` (https://github.com/danbri/factoidal/issues/920):
  each new access request is announced there with a `Create` notification.
* After a move, a request to a previous path answers 301 with `Location`
  (https://github.com/danbri/factoidal/issues/914); `redirectsMax` (default
  256) bounds the table.

## Use

```js
import { listen } from '@factoidal/core/lws'

const running = await listen({ port: 3000, baseIri: 'https://storage.example/',
  insecureNoAuth: true })   // development only; see Authorization
console.log(running.origin)
await running.close()
```

From the command:

```
factoidal lws-serve /var/lib/lws --port 3000 --issuer https://as.example --owner https://id.example/alice
factoidal lws-serve /tmp/dev --port 3000 --insecure-no-auth
```

One of `--issuer`, `--auth-config FILE` or `--insecure-no-auth` is
required.

`--port 0` takes an ephemeral port and the command prints the one it got;
`--base IRI` sets `baseIri`, which defaults to the bound origin. `DIR`
names the storage directory, but the first slice keeps the resource tree
in the engine handle, so nothing is read from it or written to it yet
(design record, section 2).

## Exports

| name | what it is |
| --- | --- |
| `listen(options)` | start a server, resolve when it is listening |
| `createLwsServer(options)` | build the server without listening |
| `openLwsStorage(options)` | open a handle and get `step` / `close` |
| `createLwsServer(...).setBaseIri(iri)` | set `baseIri` before the first request |
| `lwsOpsAvailable(engine)` | probe the loaded module for the ops |
| `LWS_OPS` | the op names |
| `LwsHostError` | a host failure, with `unknownOp` set when the op is absent |

## Tests

```
node tests/lws/server.mjs
node tests/lws/draft-binding.mjs
node tests/lws/binary-bodies.mjs
node tests/lws/authorization.mjs
deno run --allow-read --allow-net --allow-write --allow-env tests/lws/server.mjs
```
