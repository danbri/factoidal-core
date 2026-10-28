# HTTP over XMPP: a server behind NAT reached through an XMPP account

Date: 2026-10-28. Issue: https://github.com/danbri/factoidal/issues/1107.
Status: stage 1 landed 2026-10-28 (the Lean codec, the mapping to
`webdav-serve`, the access decision). Step 1 of the owner's order of
2026-10-28 (the outgoing client stream plus the WebDAV target) landed the same
day; see "Step 1" below. Step 2 (the local proxy, `xmpp-http-proxy`) landed
the same day; see "Step 2" at the end. Steps 3 to 5 are open. The owner's
answer to the 🧭 question at the end, 2026-10-28, verbatim: "4. Y" (start
stage 1).

Owner, 2026-10-27, verbatim, on the WebDAV hub note: "Include a howto for
tailscale, ssh tunnel and xmpp (if it works) as a way to expose pods/servers
from behind NAT." Tailscale and SSH work today (`docs/web/hub/webdav.md`).
XMPP does not: `factoidal xmpp-serve` serves XMPP (RFC 6120/6121), and no part
of Factoidal carries HTTP over it. The expected failure
`tests/hub/hub_webdav_test.mjs` "webdav: reach the server through XMPP"
records the gap.

## The standard: XEP-0332

XEP-0332 "HTTP over XMPP transport" (https://xmpp.org/extensions/xep-0332.html),
version 0.5.1, 2020-03-31. Status **Deferred**; the document says
"Implementation of the protocol described herein is not recommended for
production systems." Read on 2026-10-28.

- A request is `<iq type='set'>` with `<req xmlns='urn:xmpp:http' method=…
  resource=… version='1.1'>`; the response is `<iq type='result'>` with
  `<resp statusCode=… statusMessage=… version='1.1'>`. Methods OPTIONS, GET,
  HEAD, POST, PUT, DELETE, TRACE, PATCH; not CONNECT. Requests may run
  concurrently; responses may arrive in another order.
- Headers: `<headers xmlns='http://jabber.org/protocol/shim'>` (XEP-0131),
  values unchanged.
- Body: one child of `<data>`: `text`, `xml`, `base64`, `chunkedBase64`
  (with `chunk` messages, `nr`, `last`), `sipub` (XEP-0137), `ibb`
  (XEP-0047), `jingle` (XEP-0166). `maxChunkSize` 256 to 65536.
- Size: RFC 6120 servers must accept stanzas of at least 10,000 bytes; many
  servers have limits and bandwidth rules made for chat.
- Access: by roster subscription. Profiles: public, manual, private,
  provisioned (XEP-0324).
- No client-side proxy is defined: the XEP expects browsers and HTTP
  libraries to speak `httpx` themselves. WebDAV clients (Finder, Explorer,
  rclone) do not.

## What would have to be built

1. **Server side, in Lean** (`L4Factoidal/XMPP/`): parse `req` and build
   `resp`, map them to and from the HTTP request and response records that
   `webdav-serve` and `lws-serve` already step (`WebDAV.Server.handle`,
   `LWS.step`). Only `text`, `xml`, `base64` and `chunkedBase64` at first.
   The access decision (which JIDs may send requests, per mount) in Lean.
2. **An XMPP client stream, in Lean and the host**: the NAT side connects OUT
   to an XMPP server (ours or another) with an account (SASL SCRAM, already in
   `L4Factoidal/XMPP/Scram.lean`), so no port opens inbound. `xmpp-serve` is a
   server; the client half of RFC 6120 (stream negotiation, STARTTLS or direct
   TLS, resource binding) does not exist yet.
3. **A local proxy on the reading side**: `factoidal xmpp-http-proxy JID
   --port 8090` listens on 127.0.0.1 and sends each HTTP request as a `req` to
   the remote JID, so Finder or rclone use `http://127.0.0.1:8090/`. Not in
   the XEP; our own surface.
4. **Tests**: both halves against our `xmpp-serve`, then against another XMPP
   server for the client stream; litmus through the proxy is the acceptance
   test. Which other implementations of XEP-0332 exist is not checked yet.

## Risks

- Deferred XEP: until another implementation is found, this is our client
  talking to our server.
- Throughput: chat-oriented server limits; base64 adds about a third; a large
  file needs chunking. Tailscale or SSH stay the recommended routes.
- Security: an XMPP account becomes a way into a storage. The roster check,
  the per-mount allow list and the listener's own login
  (https://github.com/danbri/factoidal/issues/1108) all apply. The review
  notice applies to the new surfaces.

## Estimate and order

Stage 1, about one session: the Lean `req`/`resp` codec with `#guard`s and
the mapping to `webdav-serve`, tested over our own `xmpp-serve` with an
in-process client. Stage 2: the outgoing client stream and the local proxy.
Stage 3: litmus through the proxy, and the hub page section.

🧭 Decision needed: start stage 1, or leave XMPP as "not possible today" with
Tailscale and SSH as the routes behind NAT?

## Stage 1: what landed (2026-10-28)

Modules: `formal/lean4/L4Factoidal/XMPP/HttpOverXmpp.lean` (codec, mapping,
access decision, `step`, codec `#guard`s) and
`formal/lean4/L4Factoidal/XMPP/HttpOverXmppTests.lean` (end-to-end
`#guard`s). Both are imported from `L4Factoidal.lean`.

- Codec: `parseReqIq` / `renderReqIq`, `parseRespIq` / `renderRespIq`,
  `parseChunk` / `renderChunkMessages`, `parseClose` / `renderClose`,
  `splitChunks`, `assembleChunks`. XML goes through `L4Factoidal.XML`
  (`Wire.parseElement`, `Wire.render`); base64 through `XML.Enc.base64` and
  `XML.Enc.base64Decode?` (both loops).
- Mapping: `Req.toDav` / `Req.toDavWith` to `WebDAV.DavRequest` (header names
  in lower case); `respOfDav` from `WebDAV.DavResponse`, with
  `chooseEncoding`.
- Access: `allowed` (bare JID in `Config.allow`).
- `step`: one incoming stanza to the stanzas to send, as a `WebDAV.Prog`.
  It runs `WebDAV.handle`, so every storage the WebDAV server has (local
  directory, LWS mount) is reached the same way.
- Tests: 38 codec `#guard`s and 11 end-to-end `#guard`s. The end-to-end
  ones run XEP-0332 stanza text through `step` against the reference LWS
  server over a model storage (`WebDAV.Tests.lwsRun`): PROPFIND gives a 207
  `resp` with the multistatus as `xml`; PUT and GET as `text` and as
  `base64`; a body above the inline limit comes back in `chunkedBase64`
  chunks of at most `maxChunkSize` bytes that reassemble to the stored
  bytes; a chunked request body is served only after its last chunk, with
  chunks out of order; `close` drops a waiting request; a JID not in the
  allow list gets `forbidden` and the storage does not change; CONNECT gets
  `not-allowed`; other stanzas are not handled.
- No wasm op and no npm surface yet: the codec is Lean only. Stage 2 adds
  the op (`xmppHttpCodec` or a session op beside `xmppSession`) together
  with its `foundation/entrypoints.toml` entry and node test.
- The hub expected failure "webdav: reach the server through XMPP"
  (`tests/hub/hub_webdav_test.mjs`) stays an expected failure.

### Choices (implementer)

The XEP does not decide these; the stage 1 implementer did. Each is also in
the module header.

1. Methods: the XEP's eight plus the WebDAV methods PROPFIND, PROPPATCH,
   MKCOL, COPY, MOVE, LOCK, UNLOCK (RFC 4918). Reason: the target is
   `webdav-serve`, and a WebDAV client cannot work without them. This is an
   extension of the XEP's `Method` enumeration (its XML schema lists eight
   values). CONNECT is refused with `not-allowed` (the XEP excludes it);
   any other method with `feature-not-implemented`.
2. Access: a request is served only when the sender's bare JID is in the
   allow list. No roster logic yet (the XEP's public, manual, private and
   provisioned profiles are not implemented). A refused sender gets
   `forbidden` (type `auth`) before the `req` is read further.
3. Response body encoding: empty body, no `<data>`; body longer than
   `inlineLimit` (default 65,536 bytes), `chunkedBase64`; an XML media type
   whose body parses, `xml` (the element; the XML declaration is dropped);
   a text media type whose body is UTF-8 with only XML characters and no
   carriage return, `text` (an XML reader normalises CR, so the bytes would
   change); otherwise `base64`.
4. `maxChunkSize` counts content bytes before base64. The chunk size is
   `min maxChunkSize chunkSize` (default 65,536). A 64 KiB chunk is about
   87 KiB of base64, above the stanza limit of some servers; stage 2 must
   measure this against the server it uses and lower the default if needed.
5. `sipub`, `ibb` and `jingle` bodies are refused with
   `feature-not-implemented`.
6. A chunked request body waits in the module state until the chunk marked
   `last` and all chunks before it are present; above `maxBodyBytes`
   (16 MiB) or `maxPending` (16) waiting requests, `resource-constraint`.
7. JID comparison: domain part case-insensitive, local part exact; PRECIS is
   not applied (https://github.com/danbri/factoidal/issues/676).
8. Error mapping (RFC 6120 §8.3.3): malformed `req` (missing attribute,
   version not `\d.\d`, `maxChunkSize` outside 256 to 65536, bad
   headers or data), `bad-request`.

### What stage 2 needs

- The outgoing client stream in Lean (RFC 6120 client side: stream open,
  SASL SCRAM with `XMPP/Scram.lean`, resource binding, presence), with the
  host doing only the TLS socket.
- A host loop that feeds each stanza to `HttpOverXmpp.step`, sends the
  output in order, and stops sending a chunk stream when a `close` arrives
  (stage 1 returns all chunks of a response at once).
- The local proxy `factoidal xmpp-http-proxy` and its Lean side: an HTTP
  request to `renderReqIq`, `parseRespIq` plus `assembleChunks` back to an
  HTTP response; request ids and stream ids per proxy session.
- A wasm op for the above, with its `foundation/entrypoints.toml` entry and
  a node test, and the review notice on the new surfaces.
- A measured stanza size limit of the XMPP server used (choice 4).

## The order of the next steps (owner, 2026-10-28)

Owner, 2026-10-28, verbatim: "Ordering: whatever is fastest and safest to
implement" and "Do it", to this order:

1. the outgoing XMPP client stream plus the WebDAV server target;
2. a local HTTP proxy;
3. native `httpx://` transport in our LWS client and WebDAV mounts;
4. a raw LWS target with a fixed base IRI;
5. LWS notifications as XMPP messages.

The owner also asked about SPARQL over XMPP (plan below).

Two client forms, for a reader of a server reached through XMPP:

* **Local proxy** (step 2): `factoidal xmpp-http-proxy JID --port 8090`
  listens on 127.0.0.1 and turns each HTTP request into a `req` stanza to
  JID, so any HTTP client (Finder, Explorer, rclone, curl, a SPARQL client)
  uses `http://127.0.0.1:8090/`. Not in XEP-0332; our own surface.
* **Native `httpx://` transport** (step 3): our LWS client and the WebDAV
  `lws` mounts accept `httpx://JID/path` (the URI scheme of XEP-0332) and
  send the request as a stanza on their own client stream, with no local
  port.

## Step 1: the client stream and the WebDAV target (2026-10-28)

`factoidal webdav-serve CONFIGDIR --xmpp JID --xmpp-password-file FILE
--xmpp-allow JID[,JID]` connects out to an XMPP server and serves the WebDAV
handle over XEP-0332. It opens no port.

* `formal/lean4/L4Factoidal/XMPP/ClientStream.lean`: the client half of
  RFC 6120 as one total state machine (`start`, `feed`, `outgoing`,
  `close`): stream open, SASL SCRAM-SHA-256 with the check of the server
  signature, the stream restart, resource binding, initial presence, stream
  errors, and `service-unavailable` for an IQ get or set that is not HTTP
  (`answerUnserved`). `feed` is a tail-recursive loop over the framed units.
  `#guard`s run this client against `Server.step` (our server) for the whole
  negotiation, a wrong password, an iteration count under the minimum, a
  forged server signature, a server that offers only PLAIN, and a unit split
  over two reads.
* `HttpOverXmpp.step` is now `plan`, then `WebDAV.handle`, then `finish`
  (same behaviour; the 49 stage 1 `#guard`s pass unchanged). The client
  stream calls `plan` and `finish` and carries the request between them
  through the WebDAV handle that already serves HTTP, so a request over XMPP
  and one over HTTP run the same `webdavStep`/`webdavResume` program.
* Wasm ops `xmppClientOpen`, `xmppClientFeed`, `xmppClientAnswer`,
  `xmppClientClose` (`formal/lean4/Wasm/Ops/XmppClient.lean`).
* Host: `npm/factoidal/xmpp/client.mjs` (`connectHttpTarget`): one TCP or
  direct-TLS socket, the SCRAM client nonce from `crypto.randomBytes`, and
  the bytes. No protocol decision.
* Test: `node tests/webdav/xmpp.mjs` starts `factoidal xmpp-serve` with three
  accounts on direct TLS (a self-signed certificate for `example.org`) and
  `webdav-serve --xmpp bob@example.org --xmpp-allow alice@example.org
  --xmpp-tls`; a test client logged in as alice gets PROPFIND 207,
  PUT 201, GET 200, MKCOL 201, a 100,000-byte body back in two
  `chunkedBase64` chunks, `not-allowed` for CONNECT and
  `service-unavailable` for a non-HTTP IQ; carol gets `forbidden` and the
  storage does not change; a wrong password stops the start with exit 1 and
  "SASL failure: not-authorized". The hub test "webdav: reach the server
  through XMPP (XEP-0332)" is now a plain test; a new expected failure
  records that no file browser reaches the server until the local proxy of
  step 2 exists (step 2 made it a plain test).

Choices (implementer), also in the module header of `ClientStream.lean`:

1. TLS: the host does direct TLS (XEP-0368, `--xmpp-tls`), which is what
   `xmpp-serve` serves, or plain TCP to a literal loopback address only.
   STARTTLS is not implemented; a server that requires it and offers no
   SCRAM is refused with a reason.
2. SASL: SCRAM-SHA-256 only (no PLAIN, so the password never goes on the
   wire; SCRAM-SHA-1 would need HMAC-SHA-1, which `Crypto/` does not have).
3. Iteration count between 4,096 and 1,000,000.
4. The server signature must verify, and the server nonce must extend the
   client nonce, or the stream closes.
5. Initial presence after binding.
6. Server address from `--xmpp-host`/`--xmpp-port` (default the JID's
   domain, port 5222 or 5223); no DNS SRV lookup.

Not measured yet: the stanza size limit of a server other than ours (choice
4 of stage 1). Our server accepts the 87 KiB base64 chunks of the test.

### Invariants this step touches

Constraints from the feature-combination audit
(https://github.com/danbri/factoidal/issues/1120), tracked in
https://github.com/danbri/factoidal/issues/1125 (owner mounts over XMPP) and
https://github.com/danbri/factoidal/issues/1128 (login-limit key per JID).
`HttpOverXmpp` runs `WebDAV.handle`, and a local mount acts as the storage
owner, so on this path the JID allow list is the access control.

1. The allow list is not empty and holds bare JIDs only. Decided in Lean
   (`xcStartRefusal`, `Wasm/Ops/XmppClient.lean`; `#guard`s there). Tests:
   "start refused: no --xmpp-allow" and "start refused: an allow-list entry
   with a resource" (`tests/webdav/xmpp.mjs`); carol, not in the list, gets
   `forbidden` and the storage does not change (same file).
2. The allow list trusts the `from` that the server stamps; that is sound
   only on a stream nobody else can read or change. The client does not
   authenticate unless the transport is TLS or plain TCP to a literal
   loopback address (`ClientStream.Config.secureTransport`,
   `ClientStream.isLoopbackHost`); it never sends PLAIN (SCRAM-SHA-256
   only). Tests: the `#guard` "on a transport that is neither TLS nor
   loopback the client sends no `auth`" (`ClientStream.lean`); "start
   refused: plain TCP to a host that is not loopback" (exit 1, before any
   connection); the whole e2e run uses direct TLS.
3. A writable local mount over XMPP needs the operator's opt-in
   `--dangerously-allow-writable-without-login`, and the server prints a
   warning when it is used. Test: "start refused: a writable local mount
   without the opt-in"; the start with the opt-in checks the warning.
4. Login gate on the XMPP path (1125) and the login-limit key per bare JID
   (1128): not met. This branch has no WebDAV login (`--users`), so no rate
   limit applies on this path and none is keyed by an empty client address;
   the JID allow list is the access control. Both are expected failures in
   `tests/webdav/xmpp.mjs` that name their issue and turn the run red when
   they pass.

## SPARQL over XMPP: the plan

`factoidal serve` is not a target yet. Its HTTP handling is in Lean
(`L4Factoidal.HTTP.Wire`, `L4Factoidal.SPARQL.StoreEndpoint`), but the wasm
entry is byte-level (`storeServeRequest` takes the bytes a connection
delivered and answers response bytes) with a durable-append step for updates
(`storeServeCommit`). It has no record-level step that `plan`/`finish` can
call the way they call `webdavStep`. The order:

1. `serve` as a target: a record-level request op in
   `Wasm/Ops/StoreServe.lean` (request record in, response record or append
   request out), then `serve --xmpp JID` with the same client stream.
2. Reflection through the proxy: any SPARQL client reaches the endpoint
   through the local proxy of step 2.
3. `SERVICE <httpx://JID/sparql>` through the native transport of step 3.
4. Forwarding to third-party SPARQL endpoints last: allow-listed per
   endpoint, off by default.

## Step 2: the local proxy (2026-10-28)

`factoidal xmpp-http-proxy --xmpp JID --xmpp-password-file FILE --target
JID/RESOURCE [--port N] [--host 127.0.0.1] [--xmpp-host H] [--xmpp-port P]
[--xmpp-tls] [--xmpp-ca FILE] [--xmpp-resource R] [--timeout SECONDS]`
connects out to an XMPP server as JID (the client stream of step 1), listens
on 127.0.0.1, and sends each HTTP request as a XEP-0332 `req` to the target.
A file browser, rclone, cadaver, litmus or curl then uses
`http://127.0.0.1:PORT/` to reach `webdav-serve --xmpp`.

* `formal/lean4/L4Factoidal/XMPP/HttpRequester.lean`: the requester side as
  one total state machine. `send` (an HTTP request record to the stanzas for
  the target, or a refusal made here), `receive` (a `resp`, a stanza error or
  a `chunk` to an HTTP response record), `tick` (the host's clock; 504 past
  the deadline), `abortAll` (the stream ended; 502). The codec is that of
  stage 1 (`reqNode`, `chunkNode`, `respOfIq?`, `splitChunks`,
  `assembleChunks`); `parseRespIq` now reads through `respOfIq?`.
* Wasm: `xmppClientOpen` takes `proxyTarget` (requester mode), and the new
  ops `xmppClientRequest(handle, nowMs, requestJson)` and
  `xmppClientTick(handle, nowMs)`; `xmppClientFeed` and `xmppClientClose`
  give `responses`. The start rule is `xcProxyRefusal`
  (`Wasm/Ops/XmppClient.lean`).
* Host: `npm/factoidal/xmpp/client.mjs` (`connectHttpRequester`; the socket
  code is now shared with `connectHttpTarget`) and
  `npm/factoidal/xmpp/proxy.mjs` (`startHttpProxy`: the HTTP listener). The
  host reads the request, gives the clock every 500 ms, and writes the
  answer. It decides no status, header or address.
* Test: `node tests/webdav/xmpp-proxy.mjs` (xmpp-serve on direct TLS,
  `webdav-serve --xmpp`, three proxies). Measured 2026-10-28: 16 pass, 0
  fail, 1 xfail, 0 skip (out of 17), with litmus 104 of 104 tests (basic 16,
  copymove 13, props 30, locks 41, http 4), rclone and cadaver through the
  proxy. The hub test "webdav: a file browser reaches the server through XMPP
  (local proxy)" is now a plain test.

Choices (implementer), also in the module header of `HttpRequester.lean`:

1. Request bodies are `base64` up to 65,536 bytes, else `chunkedBase64`
   in chunks of 65,536 bytes; never `text` or `xml`, so the bytes arrive
   unchanged (an XML reader normalises line ends).
2. Only origin-form request targets (`/path`, and `*` for OPTIONS) are sent.
   An absolute-form target gets 400 and CONNECT 405, here and not at the
   target.
3. Stanza errors to statuses: `forbidden` and `not-authorized` 403,
   `not-allowed` 405, `bad-request` 400, `feature-not-implemented` 501,
   `resource-constraint` 503, `remote-server-timeout` 504, other 502.
4. Response headers lose `content-length` and the hop-by-hop headers; the
   host frames the body.
5. The sender of an answer must be the target (full JID, domain part in
   lower case; PRECIS not applied,
   https://github.com/danbri/factoidal/issues/676).
6. Limits: request body 16 MiB (413), response body 64 MiB (502 and a
   `close` for its stream), 16 waiting requests (503), `--timeout` 1 to
   3,600 seconds, default 60 (504).

### Step 2: invariants and their checks

Rows of `docs/designissues/2026-10-28-feature-combination-safety.md` that
this step touches: C1, C3, C4, C6, C13, and C7 (a new listener).

1. **The listener is on loopback only** (C7, I7). `xcProxyRefusal` refuses
   any `listenHost` other than `127.0.0.1`, and the host binds the address
   the engine accepted. Checks: the `#guard`s on `xcProxyRefusal`; "start
   refused: --host other than 127.0.0.1 (exit 1)" in
   `tests/webdav/xmpp-proxy.mjs` and the hub test. Not met: the `Host` and
   `Origin` check against DNS rebinding and cross-site requests from a web
   page in a local browser. Expected failure "a request with a foreign Host
   header is refused (DNS rebinding guard)" names
   https://github.com/danbri/factoidal/issues/1124 (the parallel work for
   that issue had not landed on `origin/main` when this step was written).
2. **The client stream rules of step 1 hold** (C4, I4). The requester mode
   uses the same `ClientStream`: TLS, or plain TCP to a literal loopback
   address; SCRAM-SHA-256 only. Checks: the `ClientStream` `#guard`s; "start
   refused: plain TCP to a host that is not loopback" in the proxy test.
3. **No open proxy** (C5 forwarding, C6). Every stanza the requester makes
   is addressed to `Config.target` and to no other JID: theorems
   `send_to_target`, `receive_to_target`, `tick_to_target`
   (`HttpRequester.lean`), over `Addressed.render`, which writes the `to`
   field as the `to` attribute; the `#guard`s parse each rendered stanza
   and read `to`. The target is a full JID (`xcProxyRefusal`). An answer from
   another JID changes nothing: theorem `receiveNode_other_sender`; test
   "a forged answer from another JID is dropped; 504 after --timeout".
4. **Credentials** (C3, I3). The headers sent are a sublist of the client's
   (`forwardHeaders_sublist`): the proxy adds no header and no credential of
   its own. `Authorization` passes unchanged
   (`forwardHeaders_keeps_authorization`, `reqOf_headers`); it goes to the
   target JID only, by invariant 3. `Proxy-Authorization` and the
   hop-by-hop headers are not forwarded. Test: the proxy test reads the
   `req` that a test client at the target receives.
5. **Limits** (C13, I13). Body, response and pending limits and the
   timeout, choice 6; `#guard`s for 413, 503, 504 and 502; tests for 504 and
   for 100,000-byte bodies both ways. The limits are per proxy process, which
   has one requester (its own JID); the per-sender limits of the serving side
   stay https://github.com/danbri/factoidal/issues/1128.
6. **Access at the target** (C1, I1). Unchanged by this step: the serving
   side's allow list decides; a proxy whose JID is not on it gets 403 for
   every request (test "carol's proxy ... 403, the file does not change"). The
   listener has no login of its own, so every local process acts as the
   proxy's JID; `--help` and the start message say so.

### Remaining stages (no code in this step)

* Native `httpx://` transport in the LWS client and the WebDAV `lws`
  mounts (step 3 of the owner's order): the client sends the request as a
  stanza on its own client stream, with no local port. It must keep C3 path
  7 closed (no token flow over `httpx` by a string rule) and give I6 its
  `peerOf?`.
* Raw LWS over XMPP with a fixed base IRI (step 4), then LWS notifications as
  XMPP messages (step 5).
* SPARQL `serve --xmpp`: the order in "SPARQL over XMPP: the plan" above.
* The `Host`/`Origin` guard on this listener when
  https://github.com/danbri/factoidal/issues/1124 lands (the expected failure
  above turns red then).
