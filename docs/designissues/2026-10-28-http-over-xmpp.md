# HTTP over XMPP: a server behind NAT reached through an XMPP account

Date: 2026-10-28. Issue: https://github.com/danbri/factoidal/issues/1107.
Status: stage 1 landed 2026-10-28 (the Lean codec, the mapping to
`webdav-serve`, the access decision). Stages 2 and 3 are open. The owner's
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
