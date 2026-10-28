# HTTP over XMPP: a server behind NAT reached through an XMPP account

Date: 2026-10-28. Issue: https://github.com/danbri/factoidal/issues/1107.
Status: proposal. No code. The owner decides whether to start
(the 🧭 question at the end).

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
