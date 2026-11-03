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

## Step 4 design: MIX (XEP-0369 MIX-CORE, XEP-0405 MIX-PAM), 2026-11-03

MIX differs from MUC where it matters for state: a MUC occupant is a SESSION (a full JID; leaving
or disconnecting ends it); a MIX participant is an ACCOUNT (a bare JID; membership survives
disconnects, and messages go to the bare JID, held for an offline account like any message).

Scope for the first landing:

- **Service.** `Config.mixDomain : Option String` (CLI `--mix mix.<domain>`). Off by default.
  Channels in memory; not persistent across a restart (stated).
- **Create.** An IQ set `<create xmlns='urn:xmpp:mix:core:1' channel='name'/>` to the service
  (XEP-0369 section 7.3.2). The creator is recorded as owner. Joining a channel that does not exist
  is `item-not-found`.
- **Join and leave through the user's server (MIX-PAM).** An IQ set to the user's OWN bare JID with
  `<client-join xmlns='urn:xmpp:mix:pam:2' channel='…'><join xmlns='urn:xmpp:mix:core:1'>…`
  joins that bare JID (XEP-0405 section 5.1). The result carries the participant id
  (`<join id='…'>`). `<client-leave>` leaves. A direct `<join/>` to the channel is refused
  (`not-allowed`): MIX-PAM servers are to proxy joins. Joining twice is one participant.
- **Messages.** A groupchat message from a participant to `channel@service` goes to every
  participant's BARE JID (held for offline accounts, `Out.route`), from the channel's bare JID with
  `<mix xmlns='urn:xmpp:mix:core:1'><nick>…</nick></mix>` (XEP-0369 section 7.1.2). The sender gets
  its copy the same way. A non-participant gets `not-acceptable` and nobody else gets anything.
- **JID-hidden.** The `<mix/>` element never carries `<jid>`: participants see nicks only.
- **Discovery.** disco#info on the service (identity `conference`/`mix`, feature
  `urn:xmpp:mix:core:1`, `#create-channel`), disco#items (the channels), disco#info on a channel;
  the server's own disco#info lists `urn:xmpp:mix:pam:2` when MIX is on.
- **Not in this landing.** PubSub nodes (participants, info, config) and their subscriptions,
  presence in channels, MAM, nick registration, private messages, channel destruction,
  administration. The `<subscribe/>` elements of a join are echoed back as given; no node is
  served.
- **Theorems wanted.** Fan-out to exactly the participants' bare JIDs; every delivery from the
  channel with the sender's own nick; a non-participant reaches nobody else; joining twice keeps
  one entry per bare JID (bare JIDs distinct); nicks distinct; leaving removes the participant.

## Step 4 result (2026-11-03)

MIX as designed above: `L4Factoidal/XMPP/Mix.lean` (8 theorems, 8 `#guard`s), the hand-off and
MIX-PAM in `Server.lean` (3 `#guard`s), the channels in the ops layer, `xmpp-serve --mix`. Tests:
`npm/factoidal/test/xmpp-mix.test.mjs`. Record row: `xmpp-serve --mix`. One gap found while
writing the row: messages held for an offline account sit in the host's in-memory queue with no
bound; that was already true of direct messages.

## Step 5 design: GC3 (Groupchat 3.0), 2026-11-03

Source: Matthew Wild, "Groupchat 3.0", slides, 2025-01-30,
https://matthewwild.co.uk/uploads/xmpp-gc3-jan-2025.pdf ("Very early spec, prototype
implementations in progress (Prosody, xmpp-rs)"). A web search on 2026-11-03 found no published
ProtoXEP or registered namespace. What the slides fix:

1. Joins are persistent: membership is not linked to presence; an offline member is still in the
   group. The nick is set at join time and shared by all of a user's clients.
2. Participant JIDs are stable: the resource is a stable participant id (as XEP-0421), unchanged
   when the nick changes, e.g. `mygroup@conference.example.com/ZjM5Y2M3M2MtZGQ5Mi0`.
3. Presence is optional: a member chooses what traffic it receives.
4. "Maybe": one set of affiliations instead of roles; knocking.

What this implementation adds, every point an INVENTED wire choice, listed in one issue with an
xfail each:

- namespace `urn:xmpp:gc3:prototype:0` (deliberately not a plausible final name);
- a separate service domain (`--gc3`), not a mode of the MUC service;
- `<join nick='' presence='true|false'/>` as an IQ set to the group's bare JID; the first join
  creates the group, its creator is `owner`; a second join is no change;
- `<leave/>`, `<nick>new</nick>` (rename, id unchanged), `<remove id=''/>` (owner only),
  `<members/>` (IQ get: id, nick, affiliation; no real JIDs) as IQs to the group;
- messages to every member's bare JID (held for offline members), from `group@service/<id>`, with
  XEP-0421 `<occupant-id/>` and XEP-0172 `<nick/>`;
- membership events (`<event type='joined|left|renamed|removed'/>` in a groupchat message) only to
  members who joined with `presence='true'`;
- participant ids `p1`, `p2`, … per group (opaque, never reused in a group).

Theorems wanted: membership grows only by the joiner's own command (no ghost member: the
attestation design's "membership changes only by authenticated member commands"); a rename keeps
every id; ids and nicks stay distinct; only an owner removes; fan-out to exactly the members'
accounts.

## Step 5 result (2026-11-03)

GC3 prototype as designed above: `L4Factoidal/XMPP/Gc3.lean` (7 theorems, including
`apply_no_ghost`; 8 `#guard`s), `Out.gc3` in `Server.lean`, the groups in the ops layer,
`xmpp-serve --gc3`. Tests: `npm/factoidal/test/xmpp-gc3.test.mjs` (behaviour, plus one xfail per
invented wire choice, https://github.com/danbri/factoidal/issues/1236). With this, the five steps
of the 2026-11-02 request are built; what each leaves out is stated in its module header, the XMPP
README and the feature-combination record.

## Step 6 design: surviving a restart, encrypted at rest, cleaned up (2026-11-03)

Owner, 2026-11-03, verbatim: "you are blabbing about the doubtlessly many shortcomings of *OUR*
early implementations and prototypes, not the core limits of the standards? These limtis are
similar to a break in tcp/ip connectivity between parties: necessary to anticipate and work
around. All sensible modern computers reboot and survive, and it should not be
application-disrupting to do so. If ours don't we'll have to find a fix (and not open
vulnerabilities eg. encrypted at rest matters and if things are written to disk to survive a
boot we'll need a way to ensure that is cleaned up. Maybe Lean theorems?"

Correct: the standards assume a server that survives a reboot. Ours loses, at a restart:

| State | Today | Survives a restart? |
|---|---|---|
| rosters | `DIR/roster/<bare>.tsv`, **plaintext** | yes, but readable by anyone with the disk |
| stanzas held for an offline account | the JS host's `pending` map, in memory, no bound (issue 1235) | **no** |
| MIX channels and participants | ops layer, memory | **no** |
| GC3 groups and members | ops layer, memory | **no** |
| MUC rooms | ops layer, memory | not needed: occupants are sessions; after a restart every session reconnects and XEP-0045 clients rejoin their rooms |

### Design

1. **One state document, decided in Lean.** The ops layer encodes all persistent state of a
   server (rosters, held stanzas, MIX, GC3) as one versioned document (`xmpp-state-1`). After any
   change to persistent state, a feed's answer carries `persist: <sealed bytes>`; the host writes
   them atomically (temporary file, then rename) and does nothing else with them. On start the
   host hands the bytes back (`xmppStateLoad`); Lean opens, validates and installs them, or
   refuses with a reason. The host never parses the state.
2. **Encrypted at rest with verified code.** The document is sealed with ChaCha20-Poly1305 from
   HACL* (`Crypto/ChaChaPoly.lean`, the verified C compiled into the same wasm). The 256-bit key
   comes from `--state-key FILE` (32 random bytes, mode 0600, kept OUTSIDE the state directory, so
   a copied state directory is useless without it); a fresh random 96-bit nonce per write, from the
   host. The associated data binds the format name, the server's domain and a write counter, so a
   document from another server or a swapped file is refused. A wrong key or a damaged file is
   REFUSED at start (exit with a reason); the server never starts empty over an unreadable state,
   because that would silently drop everyone's memberships.
3. **Cleanup by construction.** What is written is a function of the live state only, so:
   - a member who leaves, a channel or group that is removed, a held stanza that is delivered or
     expires, is absent from the next write;
   - held stanzas have a time to live (default 30 days) and a bound per account and in total
     (fixes issue 1235): past the bound a message is answered `resource-constraint`
     (RFC 6120 section 8.3.3.18) and nothing is held;
   - the plaintext roster files are migrated into the sealed document on first start and deleted;
   - old ciphertext left on a disk (an SSD does not overwrite in place) is unreadable without the
     key: replacing the key file is a crypto-shred of every earlier write.
4. **The held queue moves into Lean** (from the JS host), so the hold-or-refuse decision is made
   where the other protocol decisions are.

### Theorems wanted

- `decode (encode s) = some s` for the state document (the round trip), so a restart restores
  exactly what was there; and therefore nothing the live state no longer holds is written.
- `open (seal k n ad p) = some p`, and opening with another key, nonce or associated data gives
  nothing: stated over the AEAD contract (`Crypto/Aead.lean`), with the HACL* functions as the
  `opaque` primitives they are.
- The held queue never exceeds its bounds; no held stanza older than its time to live is kept or
  written; a delivered stanza is removed.
- After `leave` / `remove`, the account is in no part of the persisted state for that channel or
  group (from the round trip and the existing `leaveChannel_gone`, `apply_no_ghost`).

### Tracked as its own issue

https://github.com/danbri/factoidal/issues/1237: the restart requirement, the threat model, and
the open problem of the KEY across an unattended reboot (a key file on the same disk protects a
copied state directory, not a stolen disk). The issue records, as UNVERIFIED and to check against
the Apple Platform Security Guide and the AOSP Resume-on-Reboot documentation, the platform
patterns the owner pasted on 2026-11-03: a one-time reboot token protected against replay (iOS),
a measured-boot device key plus a short-lived remote secret (Android Resume-on-Reboot), and a
one-use cached secret valid seconds before an intended reboot (Android SIM PIN).

### Not in scope, stated

- Rollback: an attacker who can write the state directory can put back an OLDER sealed document
  of the same server. The write counter in the associated data does not stop that without a
  counter kept elsewhere (a TPM, or a second store).
- Memory and swap of the running process, and the key file itself, are the operator's to protect.

### Order

1. The held queue in Lean, bounded, with time to live (fixes 1235).
2. The state document: encode, decode, round-trip theorem.
3. Seal and open with ChaCha20-Poly1305; `--state-key`; load at start, refuse on failure.
4. Rosters into the document; migrate and delete the plaintext files.

### Step 6, part 1 result (2026-11-03)

The held queue is in Lean and bounded (`XMPP/Held.lean`; fixes issue 1235). Owner, 2026-11-03,
on the storage for the rest of step 6: use LWS in-process, through the same authorization path,
with no bypass of auth or ACLs; tracked as https://github.com/danbri/factoidal/issues/1238. The
sealed-file design above is therefore provisional: parts 2 to 4 wait on the audit in issue 1238.

### Step 6, parts 2 to 4 result (2026-11-03)

Built on LWS, as the owner decided: the component principal
(https://github.com/danbri/factoidal-core/pull/323), then the state in an in-process LWS storage,
sealed, with the codec's round-trip theorems; `xmpp-serve --state-key FILE`. Details and the
stated gaps: `formal/lean4/L4Factoidal/XMPP/README.md`, "2026-11-03 (evening)".
