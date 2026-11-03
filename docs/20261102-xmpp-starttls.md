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

## Step 2 result (2026-11-03)

XMPP over WebSocket, RFC 7395 over RFC 6455, all decisions in Lean:
`HTTP/WebSocket.lean`, `XMPP/WebSocket.lean`, the `xmppWs*` ops; host
`--ws-port`. No translating proxy: the server speaks RFC 7395 itself, so a
Strophe.js client connects to `ws://` or `wss://` directly. A proxy to
OTHER servers is not built (an open-relay surface; it would need its own
row in the feature-combination record).

## Between steps 2 and 3 (2026-11-03): IQ routing by full JID

Found by the foafos home-pod test (glitchcan-minigam `packages/foafos/pod/test/run.mjs`,
Factoidal as the relay): an IQ to an offline pod was held in the mailbox and never answered.
Fixes https://github.com/danbri/factoidal/issues/1234 and
https://github.com/danbri/factoidal/issues/1139.

- `Out.routeFull full text bounce`: deliver to the one session bound to that full JID now, or
  deliver `bounce` to the sender. Never held.
- `handleIq`: to a full JID, `routeFull` with a `service-unavailable` bounce for get and set
  (RFC 6120 section 10.5.3.2), none for result and error; to the bare JID of another account, the
  server answers `service-unavailable` for it (RFC 6121 section 8.5.2.1.3).
- Theorem `handleIq_no_route`: no IQ produces `Out.route`, the action that may hold a stanza.
- MUC needs the same action: a room delivers to the occupant's full JID, not to every session of
  the account.

## Step 3 design: MUC (XEP-0045), 2026-11-03

Scope for the first landing ("done enough to be safely in main"):

- **Service.** `Config.mucDomain : Option String` (CLI `--muc conference.<domain>`). Off by
  default. Rooms are temporary: created by the first join (an instant room, XEP-0045 section
  10.1.2), destroyed when the last occupant leaves. No persistence, no history.
- **Where the state lives.** A stanza from a bound session whose `to` domain is the MUC domain
  becomes `Out.muc text` (the stanza, with `from` stamped to the sender's full JID by
  `Server.step`, as for every routed stanza). The wasm ops layer keeps one `Muc.Service` per
  server handle beside the rosters and calls the pure function
  `Muc.step : Service → (from : full JID) → Stanza → Service × List Delivery`. A `Delivery` is
  `(to : full JID, stanza)`, performed as `routeFull`. Closing a session runs `Muc.leaveAll` for
  its full JID.
- **Protocol covered.**
  - join: presence to `room@service/nick`; the joiner gets every other occupant's presence, then
    its own with status 110 (and 201 when it created the room), then the subject message
    (section 7.2.15); the others get the new presence;
  - nick conflict: presence error `conflict` (409, section 7.2.9);
  - groupchat message from an occupant: to every occupant, `from` = `room@service/<sender's nick>`;
  - from a non-occupant: error `not-acceptable` (406), delivered to nobody else (section 7.4);
  - private message to `room@service/nick`: to that occupant's full JID (section 7.5);
  - leave (presence unavailable): unavailable to every occupant, status 110 to the leaver;
  - disco#info on the service (identity `conference`/`text`, feature
    `http://jabber.org/protocol/muc`) and on a room; disco#items on the service lists rooms.
- **Roles and affiliations.** The creator is owner and moderator; others are none/participant.
  Real JIDs are never sent to occupants (no `jid` attribute in `muc#user` items): the room is
  non-anonymous to nobody. Kick, ban, configuration forms, passwords and members-only rooms are
  not in this landing; a request for them is answered `feature-not-implemented`.
- **Theorems wanted.**
  1. Fan-out: the recipients of a groupchat message are exactly the occupants' full JIDs.
  2. No spoofing: every delivery has `from` = room JID plus the SENDER's own occupant nick.
  3. A non-occupant's message produces no delivery to any occupant.
  4. Nicks in a room stay distinct after every step.
  5. No delivery carries an occupant's real JID (true by the type: `Delivery` items have no
     real-JID field).
  6. Leaving removes the occupant, and an empty room is gone.

## Step 3 result (2026-11-03)

MUC as designed above: `L4Factoidal/XMPP/Muc.lean` (9 theorems, 9 `#guard`s), the hand-off in
`Server.lean` (`Out.muc`, 3 `#guard`s), the rooms in the ops layer, `xmpp-serve --muc`. Tests:
`npm/factoidal/test/xmpp-muc.test.mjs`. Record row: `xmpp-serve --muc` in
`docs/designissues/2026-10-28-feature-combination-safety.md`.
