# 2026-11-02 — XMPP: STARTTLS, then WebSocket, MUC, MIX, GC3

## Owner request (2026-11-02, verbatim)

> "STARTTTLS and also a Strophe.js websocket proxy and also MUC and the two
> other group protocols, ... we will want all of this in lean as part of our
> XMPP server. Can you get us there via xmpp-serve ? Remember it must be lean
> and the more validated theorems connecting us to realworld constraints we
> need the better."

> "aim to get it done enough to be safely in main asap; we can add
> disclaimers etc so long as it is not egregiously stupidly insecure. All our
> server code needs more and more review and verification. We easily lose old
> branches due to scale of the work happening in parallel."

> "get it all in main and testable pls"

The "two other group protocols" are read as MIX (XEP-0369) and GC3, after
the 2026-09-07 priority in `formal/lean4/L4Factoidal/XMPP/README.md`
("implements GC3, with modules for classic MUC and MIX").

## Order

Each step is one pull request from `origin/main`, landed before the next
starts, so no step waits on a long-lived branch.

1. **STARTTLS** (this landing). RFC 6120 section 5 in `Server.lean`; the
   host performs the handshake. Theorems listed in the XMPP design record,
   section "2026-11-02: STARTTLS".
2. **WebSocket (RFC 7395)** for Strophe.js and other browser clients: the
   `<open/>`/`<close/>` framing in Lean beside `Framing.lean`, one message
   per unit, and a `ws` listener in the Node host. No translating proxy is
   needed when the server itself speaks RFC 7395; a proxy to OTHER servers
   is a separate surface (open-relay risk, feature-combination gate).
3. **MUC (XEP-0045)**, a room service on a subdomain: join, occupant JIDs,
   groupchat fan-out, roles and affiliations, with theorems on who receives
   what.
4. **MIX (XEP-0369)**, a channel service over the same room state where it
   fits.
5. **GC3.** The XSF specification is unfinished. The step implements the
   published prototype behaviour and states every point where it chooses a
   wire format, each with an open issue.

## Step 1 result

- Lean: `Config.startTls`, `Session.tls`, `Stage.awaitingStartTls`,
  `Stage.tlsPending`, `Out.startTls`, `stepPreTls`, `Session.tlsEstablished`;
  `Wasm/Ops/XmppSession.lean`: `bufferAfter`, the `tlsPending` stop in
  `drain`, op `xmppSessionTlsUp`.
- Host and CLI: `startTls` option; `xmpp-serve --starttls`; a plaintext
  listener binds to loopback only.
- Tests: the `#guard`s of `Server.lean` (8 new), and
  `npm/factoidal/test/xmpp-starttls.test.mjs` against a locally built wasm.
