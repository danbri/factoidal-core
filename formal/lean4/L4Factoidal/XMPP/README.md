# L4Factoidal.XMPP — design record

Started 2026-09-07, initially scaffolded as a standalone repo/module
(`factoidal/xmpp/`), then folded into `formal/lean4/L4Factoidal/XMPP/` the
same day on owner correction: "The implementation *is* part of Factoidal
(the Lean aspect of it, so yeah L4Factoidal). You might use our XML,
XPath etc. but it needn't be any more tightly tangled than say our
jsonschemas vs our OWL, or CSVW vs MathML." This file exists because chat
logs are not where decisions belong — see the same rule in
`factoidal/CLAUDE.md`. Update it when a decision here is revisited.

**Location and coupling**: a sibling module under `L4Factoidal/`, same as
`CSVW/`, `MathML/`, `JOSE/`, `XML/`, etc. — built and imported as part of
the single `l4factoidal` Lake package (`formal/lean4/lakefile.lean`), not
its own Lake project. Loosely coupled: reuses `L4Factoidal.XML` for wire
parsing (see below) and will reuse the root `L4Factoidal/Crypto/` HACL*
FFI for hashing/HMAC when SASL needs it, but otherwise stays independent
of unrelated spec areas — the same degree of coupling as CSVW has to OWL.

**License**: inherits the repo's top-level Apache-2.0; no separate LICENSE
file in this directory.

## What this is

A fresh XMPP server implementation, built to make GC3 ("Groupchat 3.0" —
the XSF's early-stage MUC/MIX successor, see
https://matthewwild.co.uk/uploads/xmpp-gc3-jan-2025.pdf) a first-class,
formally-checked citizen instead of a bolt-on. Core protocol logic
(RFC 6120/6121 stream handling, SASL, stanza routing, GC3 itself) is
written in Lean 4.

## Why fresh, not built on an existing server

Considered and rejected: Prosody (MIT, and where the reference GC3
prototype already lives — but the point is an independent,
architecturally unrelated implementation, so the ecosystem gets real
interop signal rather than a second instance of the same assumptions),
MongooseIM / ejabberd (Erlang; ejabberd is GPLv2, excluded on license),
xmpp-rs / Mellium / Jackal (libraries or archived, not complete
maintained servers). Full survey and reasoning: 2026-09-07 chat log, "top
10 actively maintained Apache2/MIT ... XMPP server codebases" thread.

**License policy: Apache-2.0 / MIT only, no GPL/AGPL anywhere in the
dependency graph.** Owner instruction, 2026-09-07.

## Why GC3, not MIX

MIX (XEP-0369) is architecturally interesting (PubSub/MAM-native, no
presence-coupled membership) but the XSF's own 2025 assessment is that it
stalled ("Sisyphus every summit where we discuss MIX again and still go
nowhere" — XMPP Summit 27 report) and requires participant-side PubSub
capability that hindered adoption. GC3 is deliberately MUC-shaped with
incremental fixes (persistent joins, stable participant JIDs via
occupant-id, optional presence) rather than a from-scratch data model,
and is where the XSF's actual current design energy is
(`xmpp:gc3@rooms.modernxmpp.org`, prototypes in Prosody and xmpp-rs).
MIX's JID-hidden-channel work (XEP-0404) is deferred/dead; GC3 does not
currently address anonymity at all. Per owner priority (2026-09-07):
implement GC3 as the primary target, with separate MODULES for classic
MUC and MIX interop — not GC3-only, but GC3-native.

MLS (RFC 9420) is the community's stated direction for group E2EE
("groupchat OMEMO" is explicitly considered the wrong shape — pairwise
Double Ratchet per device-pair, O(n·devices) fan-out, incompatible with
JID-hidden membership since key discovery needs real bare JIDs). MIMI
(IETF, EU DMA-driven interop) is standardizing on MLS + HTTPS for
cross-provider federation; Matrix has proposed Matrix-over-MLS into the
same process. MLS is the target E2EE layer for any future
group-encryption work here (owner priority: "MLS centred").

## XML: reuse `L4Factoidal.XML`, don't reimplement it

Per Iron Rule #7 ("no hand-written reimplementations of what the formal
tree defines") and owner instruction (2026-09-07: "XML for the XML
parts"), all general XML parsing goes through the existing, W3C-XML-1.0-
conformant, F*-ported `L4Factoidal.XML` (`Parser.lean`, `Document.lean` —
4,000+ lines, with its own `Theorems.lean` and W3C-conformance
`ConfProbe.lean`), not a competing parser. `L4Factoidal.XMPP.Wire` is the
thin XMPP-specific glue on top of it:
- complete elements (stanzas, `<stream:features>`) parse via
  `L4Factoidal.XML.parseXML` and its `.root`;
- rendering is new work (`L4Factoidal.XML` is parse-only, built for W3C
  conformance testing, not round-tripping) — not a duplicate of anything;
- the one real, stated gap: `<stream:stream ...>` is never closed until
  the connection ends, so it can never be a complete `Node` the way
  `parseXML` expects. `Wire.parseOpenTag` is a narrow, minimal supplement
  for exactly this case, reusing nothing from `L4Factoidal.XML` only
  because that module doesn't (yet) expose an unclosed-root parsing mode.
  The better long-term fix is probably a small, generic addition to
  `L4Factoidal.XML` itself (useful to any streaming-XML protocol, not
  XMPP-specific) — filed as future work, not silently worked around.

An RDF-ish data structure may be worth reaching for elsewhere (see
"Priorities" below) if a good niche shows up — groups/PEP/PubSub
modeling, not the wire format.

## Architecture: tight core + community extensions (Prosody's model)

Prosody's real lesson isn't its language choice, it's the split: `core/`
+ `net/` + `util/` (~32,000 lines) is the actually-required RFC 6120/6121
machinery; everything XEP-shaped lives in `plugins/mod_*`, and the *bulk*
of Prosody's real-world feature set lives in a separate,
community-maintained `prosody-modules` repo, not the main tree. ejabberd
took the opposite "batteries included" approach and its `mod_*.erl` alone
is 82,000 lines — bigger than its whole core.

This module follows Prosody's split, not ejabberd's:
- **Verified core**: stream negotiation, SASL, stanza routing, JID
  handling, GC3 (+ MUC/MIX modules). Proved, not just tested, where the
  property is a real safety property (join persistence, affiliation
  transitions, occupant-id stability, idempotency — see
  `skills/lean4-proof-patterns` for the proof style to reuse).
- **Extensions**: everything else (most XEPs) should be independently
  addable without touching the verified core, the same way a `mod_*.lua`
  drops into Prosody. Design the core's plugin/hook surface for this from
  the start rather than retrofitting it.

## Runtime: Lean → wasm, hosted on the BEAM

Lean 4's easiest export targets are JS/wasm — `formal/lean4/Wasm/`
already has a working export pipeline for other parts of L4Factoidal,
worth reusing/extending rather than building a second one. But the actual
runtime properties this workload needs — one lightweight process per
connection, preemptive scheduling so one client can't starve others,
supervision trees that isolate and restart a crashed session — are BEAM
(Erlang VM) properties, not Node's. Resolution: wasm is the *artifact*,
BEAM is the *host* — call the Lean-compiled wasm module from
Erlang/Elixir via a NIF wrapping `wasmtime` (prior art: `wasmex`,
https://github.com/tessi/wasmex). This keeps the server "fresh" (new
supervision tree, new connection handling — none of it ejabberd's or
MongooseIM's code) while keeping BEAM's concurrency/fault-isolation
model, at the cost of NIF marshalling discipline (cross the boundary once
per stanza with flat byte buffers, not per-field). Not yet implemented;
core Lean logic comes first and is host-agnostic by construction.

## Cryptography: the root `L4Factoidal/Crypto/` HACL* FFI, not a new one

`formal/lean4/lakefile.lean` already compiles and links vendored,
F*/Low*-verified HACL* C (`third_party/hacl/`) for Ed25519, SHA-2, P-256,
and RSA (`L4Factoidal/Crypto/{Ed25519,SHA2Native,P256Native,RsaNative}.lean`
— the P-256/RSA pair landed 2026-09-06 for JOSE, one day before this
module started). SASL SCRAM-SHA-256 needs HMAC-SHA-256, which doesn't
exist there yet but is buildable in pure Lean on top of the existing
`l4_hacl_sha256`/`l4_hacl_sha256_blocks` externs (HMAC's construction
doesn't need its own native primitive) — add it to `L4Factoidal/Crypto/`
when needed, not as an XMPP-local crypto boundary. No new HACL* binding
work should be XMPP-specific; extend the shared FFI, per the existing
extern-family pattern.

## Testing: reuse the world's test suites, don't invent our own protocol oracle

- **MongooseIM's `big_tests`** (Apache-2.0, Common Test + `escalus`
  client) — black-box, wire-level protocol interop tests against a real
  client library. Worth evaluating for direct reuse against this server,
  since it tests protocol behavior over the wire, not MongooseIM
  internals.
- **RFC 5802 / RFC 7677** — official SCRAM-SHA-1 / SCRAM-SHA-256 test
  vectors, for the SASL layer.
- **RFC 8264 / RFC 8265 (PRECIS)** — official test cases for JID
  localpart/resourcepart enforcement.
- **HACL\*'s own upstream test vectors** (NIST CAVP, RFC vectors) —
  already validated upstream; no need to re-derive, just confirm the
  binding reproduces them.
- **XSF Compliance Suites** (e.g. XEP-0479 and successors) — use as a
  checklist for "what does complete mean this year," not as a test
  format.
- Differential testing against the Prosody and xmpp-rs GC3 prototypes
  once GC3's wire format stabilizes — this implementation's value to the
  standards process is partly *as* an independent check on the other two.

## Why now — 2026 context (owner steer, 2026-09-07)

Design against the world this actually ships into, not the world
MUC/MIX were designed for circa 2002/2016:

- **AI everywhere.** Participants won't all be humans typing on
  keyboards — expect agents/bots as first-class, high-volume clients
  (this is also factoidal's own original motivation for wanting MIX at
  all — see `docs/20260831-xmpp-mix-pilot.md`'s "collaboration surface"
  for coding agents and humans together). Don't design
  auth/rate-limiting/identity around "one human, one client, modest
  message rate" as the only shape.
- **Streams, video, audio, phones.** Real-time media has to be a clean
  extension point from day one — owner priority sharpens this to
  "WebRTC baked in" (not just an extension point) plus WebGPU/WebAudio/
  WebXR assumed client-side. GC3's own presence-optional, persistent-join
  design is already the right call for mobile — validated, not new work.
- **Things going viral / "1:billions ready(ish)".** A room's membership
  shape can jump from a handful of people to a huge, bursty audience with
  no warning. Don't assume every channel is small-group-interactive; the
  core needs to accommodate a broadcast/large-audience shape — different
  fan-out, moderation-at-scale, and rate-limiting needs than a family
  group chat — as a distinct room capability, not a scale failure mode.
- **Distrust of tech megacorps.** Reinforces the license policy and the
  fresh-implementation decision, and argues against defaulting to a
  big-tech OIDC/SSO identity anchor even though it would be the
  lowest-friction option — self-hostability and independent verifiability
  are the point, not a compliance checkbox. (Reconciled with the "modern
  auth — OIDC" priority below: OIDC as one pluggable method, not the only
  one.)
- **Zeroconf/serverless (XEP-0174) and IoT/Thread-ready.** New, distinct
  deployment shapes — a constrained/mesh/no-central-server target is
  materially different from "cloud server handling many phone/browser
  clients," and shouldn't be assumed to fall out of the same architecture
  for free.

## Priorities (owner, 2026-09-07, verbatim)

> SECURE / PRIVATE / ELEGANT / UNDERSTANDABLE / AUDITABLE / MODULAR /
> REGULATED INDUSTRY READY / MOBILE FIRST / POST-slack post-discord
> post-socialweb post-AI / 1:billions ready(ish) / WebRTC baked in /
> WebGPU and webaudio webxr assumed / Minimizes xml / Uses a Knowledge
> Graph RDF abstraction for groups, pep, pubsub, feeds, apis, MCP/AI /
> Modern wrt auth etc - OIDC, email based specs, jose / MLS centred /
> implements GC3, with modules for classic MUC and MIX / MIMI and interop
> is centred including the e2e vs groups/ai tradeoffs / Zeroconf/serverless
> xmpp ready / IoT thread/etc ready / Etc

Read as an ordering/ambition statement, not a spec. "Etc" taken as license
to keep applying this list's spirit to future decisions, not as a literal
further requirement.

**Resolved, 2026-09-07** (owner replies, in order):
1. "XML for the XML parts. An RDF-esque data structure elsewhere if there
   is a niche." → settles the XML-vs-RDF question above: reuse
   `L4Factoidal.XML` for the wire format; RDF/knowledge-graph modeling is
   a genuine sub-theme ("don't bog down in the RDF, it is a sub-theme"),
   reached for opportunistically for groups/PEP/PubSub if a good fit
   shows up, never a blocking dependency.
2. "Loosely coupled to other parts of L4Factoidal but defo part of it." →
   settles the module-location question: `L4Factoidal/XMPP/`, sibling to
   `CSVW/`/`MathML/`/`JOSE/`, not a separate Lake project.
3. "I don't know, find out" (re: what "regulated industry ready"
   concretely requires) → open research item, not urgent, no code depends
   on it yet.

### Still open

1. What does "regulated industry ready" concretely require (retention/
   eDiscovery/audit-log capability), and how is it kept separably opt-in
   from the private-by-default path? Owner: "I don't know, find out" —
   needs research, not a design call yet.
2. The MIMI e2e-vs-groups/AI tradeoff — what mechanism (if any) resolves
   it (see the TEE/Key-Transparency discussion, 2026-09-05/06 chat log) —
   not urgent, no code depends on this yet.

## Status

2026-09-07: module lives at `formal/lean4/L4Factoidal/XMPP/`, imported
from the root `L4Factoidal.lean`, builds as part of the main
`l4factoidal` package (`lake build` from `formal/lean4/`). Real, tested
modules so far:

- `Jid.lean` — RFC 7622 structural + length well-formedness. PRECIS
  enforcement explicitly not yet implemented (flagged in the module
  header, not silently skipped).
- `Wire.lean` — XMPP-specific glue over `L4Factoidal.XML`: `render`/
  `renderList` (serialization — new work, nothing to reuse), `parseElement`
  (delegates to `L4Factoidal.XML.parseXML`), and `parseOpenTag` (the one
  genuinely unsupported case — an unclosed `<stream:stream>` root; see
  "XML" section above for why this isn't a reimplementation of the real
  parser).
- `Core.lean` — `StreamHeader`/`StreamFeatures`/`ConnStage`/`featuresFor`
  (RFC 6120 negotiation, ordering made structural rather than checked)
  and `Stanza` (`message`/`presence`/`iq`), all built on
  `L4Factoidal.XML.Node`/`Attribute` and `Jid`. Round-trip and negative
  cases tested before the move to this location; retesting after the
  move is the immediate next step (see below).
- `Sasl.lean` — SCRAM (RFC 5802/7677) message format only (client-first/
  server-first/client-final/server-final parse+render); hash/HMAC
  computation deliberately not called from here yet (see Crypto section).
- `Gc3.lean` remains a scope-only stub — GC3 itself is still an
  early-stage, unfinished XSF spec. Implementing rooms would be
  inventing a wire format, not implementing one.
- Not yet implemented: STARTTLS (the carrier holds TLS, XEP-0368),
  SCRAM channel binding, server-to-server federation, MUC/MIX interop
  modules, and the BEAM host.

### 2026-09-07, later the same day: a running server

The three gaps listed above as "not yet implemented" — SASL hash/HMAC
computation, resource binding, stanza routing — are implemented, and
`lean_exe l4xmpp-serve` runs.

- `L4Factoidal/Crypto/Hmac.lean` — HMAC-SHA-256 (RFC 2104) and
  PBKDF2-HMAC-SHA-256 (RFC 8018 section 5.2) over the existing
  `Crypto.sha256`, exactly as the "Cryptography" section above proposed
  ("HMAC's construction doesn't need its own native primitive"). RFC 4231
  cases 1, 2, 3, 6, 7 and the RFC 7914 section 11 PBKDF2 vector as
  `#guard`s.
- `L4Factoidal/XMPP/Scram.lean` — the SCRAM-SHA-256 arithmetic. The
  RFC 7677 section 3 published exchange is reproduced: its ClientProof
  verifies and its ServerSignature comes back.
- `L4Factoidal/XMPP/Framing.lean` — where the next top-level unit of a
  stream ends, which is the one thing `L4Factoidal.XML` cannot do for a
  never-closed root. It supplies only the CUT; `Wire.parseElement` (the
  real parser) still parses.
- `L4Factoidal/XMPP/Server.lean` — every remaining protocol decision as
  one total function. RFC 6120 sections 4.2, 4.4, 4.9, 6, 7, 8, 8.4 and
  RFC 6121 sections 2, 3, 4, 8.
- `Harness/XmppServe.lean` — the I/O only.

**The carrier.** `deploy/fly/xmpp/` holds the entire non-Lean part: a
Dockerfile and one socat command that terminates TLS and forks one
process per connection. XEP-0368 direct TLS is what makes that complete
— with no STARTTLS step there is no TLS work left for the application.
No C, no JavaScript, no Erlang serves a connection. The BEAM host
described above is therefore not on the critical path any more; it
remains the interesting option for supervision and scheduling, not the
only way to get a socket.

**Measured.** 41 pass, 0 fail (out of 41) replaying the RFC sequences
through the live binary (`tests/xmpp/server.mjs`); 7 pass, 0 fail (out
of 7) driving it with `@xmpp/client` over a real socket through the
socat carrier (`tools/xmpp-interop.sh`). The interop script exits 2 with
a reason when socat or the client library is absent, never a green skip.

**Two defects the tests found, recorded so they are not repeated.**
(1) `IO.FS.Stream.read n` is `fread`: it blocks until `n` bytes arrive.
Reading 4096 stalled every interactive client — a batch replay through a
closed pipe did not show it, because end of file releases the read.
(2) The host read and unlinked a spooled stanza before asking whether
the session could receive it, and the stanza was destroyed. The gate is
now `Server.Session.canDeliver`, asked BEFORE the mailbox is touched.
Both are written into the module headers beside the code that pays for
them.
- **Retested after the move**: all round-trip/negative-case checks pass
  against the new `L4Factoidal.XML`-backed `Wire`/`Core`.
- **Tested against a live ejabberd instance** (the `foafmixer` pilot
  container, `localhost/foafmixer/ejabberd-mix:26.07-pilot`, running on
  `127.0.0.1:5222`), not just hand-written strings — per owner instruction
  2026-09-07 ("you can and should test against our ejabberd installation").
  Opened a raw TCP connection and captured ejabberd's actual
  `<stream:stream>` + `<stream:features>` response. This caught a real
  bug: `Wire.parseOpenTag` didn't expect the leading `<?xml version='1.0'?>`
  declaration real servers send (every hand-written test string had
  omitted it), so the first real capture failed to parse. Fixed
  (`Wire.skipXmlDecl`); the full, real, byte-for-byte capture now parses
  correctly (from/id/version/xml:lang all extracted) and the real
  `<stream:features>` element round-trips through the reused
  `L4Factoidal.XML` parser. This is exactly why "test against the real
  server" was worth doing over more hand-written strings — it found
  something hand-written tests didn't, on the first try.
- **Proved, not just tested** (owner instruction 2026-09-07: "make the
  most of Lean4 by actually proving interesting/useful things ... near-
  adversarial conditions"):
  - `Jid.parse_some_domain_nonempty` / `_localpart_nonempty` /
    `_resourcepart_nonempty` — for every input string, `parse` never
    returns a JID with an empty-but-present part. Required refactoring
    `Jid.parse` to route through a single `splitParts` helper with one
    guard chain and one constructor call (the original nested
    match-inside-if-inside-match shape produced unmanageable dependent-
    elimination goals) — a case where making code provable also made it
    more readable, not a tradeoff.
  - `Core.featuresFor_startTls_iff_preTls` / `_sasl_iff_postTls` /
    `_bind_iff_authenticated` / `_not_tls_and_bind` — the RFC 6120
    negotiation ordering as actual `iff` theorems, not prose: a future
    refactor that leaks SASL before TLS or bind before authentication
    fails to *compile*, not just fails a test someone has to think to
    write.
  - All seven theorems checked with `#print axioms`: only Lean's standard
    foundational axioms (`propext`, `Classical.choice`, `Quot.sound`,
    only where genuinely needed), no `sorry`, no custom escape hatch.
  - Adversarial `#eval` stress tests (empirical confirmation the
    fuel-bounded, non-`partial` parsers can't be hung or crashed by
    malicious input, on top of the termination guarantee Lean's kernel
    already enforces by accepting the definitions): 100,000 unmatched
    `<` characters, 20,000 attributes on one tag, 20,000 chained `&amp;`
    entities in one attribute value, 5,000 levels of element nesting
    (through the reused `L4Factoidal.XML` parser), and every truncation
    point of the real captured ejabberd stream-open tag — all return
    promptly, none hang, none crash.
- **JS/wasm API landed** (2026-09-07): `Wasm/Ops/Xmpp.lean` exposes
  `xmppJidParse`/`xmppJidRender`/`xmppStreamHeaderParse`/
  `xmppStreamHeaderRender`/`xmppFeaturesFor`/`xmppStanzaParse` on the
  dispatch ABI (`Wasm/Dispatch.lean`), and
  `npm/factoidal/xmpp/index.mjs` wraps them in a functional-programming-
  style JS API (pure functions, `{ok,value}`/`{ok:false,error}` results,
  never throws for an expected outcome) — see
  `npm/factoidal/xmpp/README.md`. 24/24 unit tests pass
  (`npm/factoidal/test/xmpp.test.mjs`), run against the real rebuilt
  wasm, not mocked.
- **Upstream limit found via the JS test suite, repaired 2026-10-10**:
  `parseStanza`/`parseStreamHeader` delegate to the shared
  `L4Factoidal.XML` parser (see "XML" section above). Its scan of a text
  run or a start tag for references, `XML.scanRefs`, used one stack frame
  per reference, so about 2,000 consecutive references in one text node
  overflowed the wasm call stack (bisected 2026-09-07). Issue:
  https://github.com/danbri/factoidal/issues/673. The scan is now a loop,
  `XML.scanRefsLoop`, with a `csimp` theorem that it equals `scanRefs`.
  Measured 2026-10-10 (linux x86_64, Lean 4.33.1, Node 22): 100,000
  sequential references in content or in an attribute value parse under a
  512 KB native stack (`LEAN_STACK_SIZE_KB=512`) and under
  `node --stack-size=512` in wasm; before the repair 10,000 overflowed
  natively and 5,000 in wasm. The adversarial case of
  `npm/factoidal/test/xmpp.test.mjs` now parses a body of 10,000 `&amp;`
  references and checks the payload. The nesting depth of entity
  expansion (an entity whose replacement text references another) still
  costs one frame per level; it is bounded by the number of declared
  entities, because a cycle is rejected (WFC: No Recursion).
- Committed to git in PR #661 (Jid/Wire/Core/Sasl/Gc3 landing) and this
  same-day wasm/JS follow-up.

### 2026-10-22: the server from wasm, behind a Node socket

`Wasm/Ops/XmppSession.lean` puts `Server.step` behind handles the way
`Wasm/Ops/Lws.lean` puts the LWS operations behind one: `xmppOpen` holds
a server (accounts, the roster of each bare JID, who is available),
`xmppSessionOpen` one connection, `xmppSessionFeed` the bytes a socket
read, and the answer is what the harness performs on files and a socket —
`send`, `route`, `presence`, `rostersSaved`, `close`. The host supplies
the stream id and the SCRAM nonce (the module has no random source) and
owns routing: `route` is reported, and the host calls
`xmppSessionDeliver` on the sessions bound to that bare JID, which asks
`Session.canDeliver` before anything else — the gate the harness learned
to ask first (defect 2 above).

`npm/factoidal/xmpp/server.mjs` is the host and `factoidal xmpp-serve`
the command: TCP or XEP-0368 direct TLS, one engine session per
connection, in-memory routing with a per-account hold for unbound
targets, rosters persisted under `DIR/roster/` in the engine's own
encoding, and the harness's `DIR/spool/<bare jid>/` mailbox polled and
delivered, so the two hosts share a state directory and a program that
is not an XMPP client can hand a user a stanza by writing a file. No
protocol decision moved: the harness's `drainBuffer` loop is reproduced
op for op (fresh roster before every `step`, `maxUnits` as
`policy-violation`), and `tests/xmpp/server.mjs`'s RFC sequences are
replayed over real sockets in `npm/factoidal/test/xmpp-serve.test.mjs`,
with the SCRAM exchange computed independently in `node:crypto`.
`tools/xmpp-interop.sh wasm` drives it with `@xmpp/client`.

The BEAM host of the "Runtime" section above is now the third option,
after socat-per-process and Node-per-socket, not the second.

### 2026-10-28: HTTP over XMPP (XEP-0332), stage 1

https://github.com/danbri/factoidal/issues/1107 (a WebDAV server behind NAT
reached through an XMPP account). Plan and choices:
`docs/designissues/2026-10-28-http-over-xmpp.md`.

- `HttpOverXmpp.lean` — the XEP-0332 (v0.5.1, Deferred) `req`/`resp` codec in
  `urn:xmpp:http`, XEP-0131 headers, bodies `text`, `xml`, `base64` and
  `chunkedBase64` (`chunk` messages with `streamId`, `nr`, `last`; `close`);
  the mapping to and from the `WebDAV.DavRequest` / `DavResponse` records of
  `webdav-serve`; the access decision (sender's bare JID in an allow list; no
  roster logic yet); and `step`, one stanza in, stanzas out, as a
  `WebDAV.Prog`. Methods: the XEP's eight plus the RFC 4918 methods
  (implementer choice; the target is `webdav-serve`); CONNECT refused.
- `HttpOverXmppTests.lean` — end-to-end `#guard`s: XEP-0332 stanza text
  through `step` and `WebDAV.handle` against the reference LWS server over a
  model storage (PROPFIND gives 207, chunked bodies both ways, `forbidden`
  for a JID not in the list).
- Lean only: no wasm op, no network surface. Stage 2 adds the outgoing
  client stream, the local proxy and the op.

### 2026-10-28: the client stream, and WebDAV over XMPP (step 1)

https://github.com/danbri/factoidal/issues/1107, step 1 of the order the
owner approved on 2026-10-28 ("Ordering: whatever is fastest and safest to
implement", "Do it"). Record: `docs/designissues/2026-10-28-http-over-xmpp.md`
§ Step 1.

- `ClientStream.lean` — the CLIENT half of RFC 6120 as one total state
  machine: stream open, SASL SCRAM-SHA-256 (RFC 5802/7677 client arithmetic
  over `Crypto/Hmac.lean`; the server signature is checked; the nonce must
  extend ours; iteration count 4,096 to 1,000,000), the stream restart,
  resource binding, initial presence, stream errors, and RFC 6120 §8.4
  `service-unavailable` for an IQ that is not HTTP. No STARTTLS: the host
  does direct TLS (XEP-0368) or plain TCP. `#guard`s run it against
  `Server.step`.
- `HttpOverXmpp.step` = `plan`, `WebDAV.handle`, `finish`, so a host can run
  the WebDAV request through its own handle.
- `Wasm/Ops/XmppClient.lean` — ops `xmppClientOpen`, `xmppClientFeed`,
  `xmppClientAnswer`, `xmppClientClose`; host `npm/factoidal/xmpp/client.mjs`;
  command `factoidal webdav-serve CONFIGDIR --xmpp JID`. Test
  `node tests/webdav/xmpp.mjs`.

### 2026-10-28: the requester side, and the local proxy (step 2)

https://github.com/danbri/factoidal/issues/1107, step 2. Record:
`docs/designissues/2026-10-28-http-over-xmpp.md` § Step 2.

- `HttpRequester.lean` — the XEP-0332 requester as one total state machine:
  `send` (an HTTP request to a `req` iq and `chunk` messages for one target
  JID, or a refusal: 400 absolute-form target, 405 CONNECT, 413 body above
  16 MiB, 503 more than 16 waiting), `receive` (a `resp`, a stanza error, a
  `chunk` from the target only), `tick` (504 past the deadline), `abortAll`
  (502). Theorems: every stanza goes to the target (`send_to_target`,
  `receive_to_target`, `tick_to_target`); a stanza from another JID changes
  nothing (`receiveNode_other_sender`); the forwarded headers are a sublist
  of the client's and keep `Authorization` (`forwardHeaders_sublist`,
  `forwardHeaders_keeps_authorization`).
- `Wasm/Ops/XmppClient.lean` — requester mode of `xmppClientOpen`
  (`proxyTarget`, start rule `xcProxyRefusal`), ops `xmppClientRequest`,
  `xmppClientTick`; host `npm/factoidal/xmpp/proxy.mjs`; command
  `factoidal xmpp-http-proxy`. Test `node tests/webdav/xmpp-proxy.mjs`.

### 2026-11-02: STARTTLS (RFC 6120 section 5)

Owner, 2026-11-02: STARTTLS, a Strophe.js WebSocket endpoint, MUC and the
two other group protocols, all in Lean, "with more validated theorems
connecting us to realworld constraints", landed in `main` in small steps.
This is step 1. Record of the order: `docs/20261102-xmpp-starttls.md`.

- `Config.startTls` (the host holds a certificate and key) and
  `Session.tls` (TLS from the carrier or from a completed STARTTLS). When
  `startTls` is set and the connection is not secure, `step` hands every
  unit to `stepPreTls`: STARTTLS offered as required and no SASL mechanism;
  `<starttls/>` answered with `<proceed/>` and `Out.startTls`; any other
  element is `policy-violation`; in `tlsPending` every unit closes the
  connection with nothing sent. The host does the handshake and reports it
  with `Session.tlsEstablished` (op `xmppSessionTlsUp`).
- Theorems (`Server.lean`, end of file): `steps_requiresStartTls` (any
  sequence of units before the handshake leaves no user, no environment
  change and no action except a write, a close or the upgrade, so no
  password or SCRAM proof is checked in clear), `step_tlsPending`,
  `stepPreTls_startTls`, `tlsEstablished_spec`, `preTlsFeatures_no_sasl`;
  in `Wasm/Ops/XmppSession.lean`, `bufferAfter_startTls` and
  `drain_tlsPending` (bytes that arrive after `<starttls/>` in clear are
  discarded and never read: the plaintext-injection fault, CVE-2011-0411).
  `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` only.
- Host: `npm/factoidal/xmpp/server.mjs` option `startTls`, command
  `factoidal xmpp-serve DIR --cert F --key F --starttls`. The plaintext
  listener now binds to loopback only (invariant I4 of
  `docs/designissues/2026-10-28-feature-combination-safety.md`).
- Test: `node --test npm/factoidal/test/xmpp-starttls.test.mjs` (real
  sockets, a real handshake, an injected `<auth/>` after `<starttls/>`).
- Not changed: the native harness (`Harness/XmppServe.lean`) never sets
  `startTls`; socat holds TLS there. SCRAM channel binding stays out: the
  engine does not see the TLS layer.

### 2026-11-03: XMPP over WebSocket (RFC 7395 over RFC 6455), for Strophe.js

Step 2 of `docs/20261102-xmpp-starttls.md`.

- `HTTP/WebSocket.lean` — RFC 6455 server side: `upgrade` (GET, version
  13, the `Origin` allow list, the required subprotocol, a 16-byte key;
  `Sec-WebSocket-Accept` by SHA-1 of public data, tier 1 of
  `skills/crypto-policy`), `decode` (masking required, RSV bits, opcodes,
  control frames, minimal lengths, a frame limit), `Reader` (fragments,
  ping, close, UTF-8, a message limit), `encode`. Theorems
  `upgrade_accept_checked`, `decode_frame_masked`, `decode_frame_bounded`,
  `feed_done`; `#guard`s with the examples of RFC 6455 sections 1.3 and 5.7.
- `XMPP/WebSocket.lean` — RFC 7395 as a translation at the edge of
  `Server.step`: `unitOfMessage` (`<open/>`, `<close/>`, one element per
  message; a `<stream:stream>` over a WebSocket is refused) and
  `messageOfSend` (by equality with `Server.streamOpenText` and
  `Server.streamCloseText`). Theorems `messageOfSend_open`,
  `messageOfSend_close`, `streamClose_ne_open`. `Server.step` is unchanged.
- `Wasm/Ops/XmppSession.lean` — ops `xmppWsOpen`, and on the blob ABI
  `xmppWsFeed`, `xmppWsDeliver`, `xmppWsClose`; `wsFeedPure` takes a
  connection from its first byte (HTTP handshake, path check, frames,
  units). Theorem `wsFeedPure_handshake_refused`: before an accepted
  handshake no unit reaches `Server.step` and nothing is routed.
- Host and CLI: `xmpp-serve --ws-port N [--ws-path P] [--ws-origin O]...`;
  WebSocket and TCP sessions share one routing table.
- Test: `npm/factoidal/test/xmpp-websocket.test.mjs` (Node's own WebSocket
  client as an independent RFC 6455 implementation; raw sockets for a bad
  Origin, path, subprotocol and an unmasked frame).

## 2026-11-03 (later): IQ routing by full JID

- `Out.routeFull full text bounce` (`Server.lean`): deliver to the one session bound to that full
  JID now, or deliver `bounce` to the sender. Never held.
- `handleIq`: a get or set to a full JID is `routeFull` with a `service-unavailable` bounce
  (RFC 6120 section 10.5.3.2); a result or error has no bounce (section 8.3.1); a get or set to
  the bare JID of another account is answered by the server (RFC 6121 section 8.5.2.1.3).
- Theorem `handleIq_no_route`: no IQ produces `Out.route`, the action that may hold a stanza.
- Hosts: `Wasm/Ops/XmppSession.lean` collects `routeFull`; `npm/factoidal/xmpp/server.mjs`
  delivers to the session whose full JID matches, or the bounce to the sender;
  `Harness/XmppServe.lean` uses its presence files and its per-account mailbox (a stated limit).
- Fixes https://github.com/danbri/factoidal/issues/1234 and
  https://github.com/danbri/factoidal/issues/1139. Tests: 5 `#guard`s in `Server.lean`,
  `npm/factoidal/test/xmpp-iq-routing.test.mjs` (5), and the former xfail in
  `tests/webdav/xmpp.mjs`, now a check.

## 2026-11-03 (later): MUC, XEP-0045 (step 3)

- `L4Factoidal/XMPP/Muc.lean`: `Muc.step : Service → full JID → Stanza → Service × List Delivery`
  over shared, temporary rooms. Join (instant room, status 110 and 201, the subject), nick conflict,
  groupchat, private messages, leave, disco#info and disco#items. A `Delivery` goes to one
  occupant's full JID; `Body` has no field for a real JID.
- `Server.lean`: `Config.mucDomain`; a bound session's stanza to that domain becomes
  `Out.muc fromFull text`, with the sender from the session; disco#items on the server names the
  service.
- `Wasm/Ops/XmppSession.lean`: one `Muc.Service` per server; `.muc` runs `Muc.step` and performs
  each delivery as `routeFull`; `xmppSessionClose` and `xmppWsClose` run `Muc.leaveAll` and return
  the deliveries.
- Host and CLI: `xmpp-serve --muc conference.<domain>` (`mucDomain` in `listen`).
- Theorems: `groupchat_recipients`, `groupchat_from_sender`, `byReal_real`,
  `groupchat_nonoccupant`, `privateMsg_one`, `joinRoom_nodup`, `leaveRoom_gone`, `put_empty`,
  `leaveRoom_nodup`. 9 `#guard`s in `Muc.lean`, 3 in `Server.lean`.
- Not in this step, stated in the module header: nick change, kick, ban, voice, configuration,
  passwords, members-only rooms, history, subject change, persistent rooms. Real JIDs are sent to
  nobody, moderators included.
- MIX (XEP-0369, step 4) and GC3 (step 5) are next.

## 2026-11-03 (later): MIX, XEP-0369 with XEP-0405 MIX-PAM (step 4)

- `L4Factoidal/XMPP/Mix.lean`: `Mix.step` over channels whose participants are ACCOUNTS (bare
  JIDs). Create (IQ `<create/>` to the service), join and leave through the user's own server
  (`<client-join/>`, `<client-leave/>`), channel messages to every participant's bare JID
  (`Delivery.held`: the server may hold them for an offline account), disco. JID-hidden: `<mix/>`
  carries a nick, never a `<jid>`.
- `Server.lean`: `Config.mixDomain`; `Out.mix`; the MIX-PAM interception in `handleLocal`; the
  server's disco#info offers `urn:xmpp:mix:pam:2`, its disco#items names the service.
- Ops layer: a held delivery becomes `route` (may be held), an IQ answer `routeFull`.
- CLI: `xmpp-serve --mix mix.<domain>`.
- Theorems: `message_recipients` (exactly the participants' accounts, every copy held),
  `message_from_sender`, `message_nonparticipant`, `joinChannel_bares_nodup`,
  `joinChannel_nicks_nodup`, `joinChannel_again`, `leaveChannel_gone`. 8 `#guard`s in `Mix.lean`,
  3 in `Server.lean`. `handleIq_no_route` still holds with the MIX-PAM branch.
- Not in this step (module header): PubSub nodes and subscriptions, channel presence, MAM, nick
  registration, private messages, destruction, administration, persistence.

## 2026-11-03 (later): GC3 prototype (step 5)

There is no published GC3 specification. `L4Factoidal/XMPP/Gc3.lean` (formerly a scope stub)
implements what Matthew Wild's slides of 2025-01-30 fix
(https://matthewwild.co.uk/uploads/xmpp-gc3-jan-2025.pdf): persistent joins (membership is the
account's), stable participant JIDs (`group@service/<id>`, unchanged by a rename), optional
presence (membership events only for members that ask), one affiliation scale. Every wire format
is invented and listed in https://github.com/danbri/factoidal/issues/1236, with one xfail each in
`npm/factoidal/test/xmpp-gc3.test.mjs`. XEP-0421 `<occupant-id/>` and XEP-0172 `<nick/>` use their
real namespaces.

- The membership transition relation is `apply : Group → Command → Option Group`; every command
  carries its actor, the authenticated account from the session.
- Theorems: `apply_no_ghost` (no transition adds a member except that member's own join; the
  attestation design's "membership changes only by authenticated member commands"),
  `apply_rename_ids`, `apply_remove_owner`, `apply_join_nicks_nodup`, `message_recipients`,
  `message_nonmember`. 8 `#guard`s; 1 in `Server.lean`.
- `Server.lean`: `Config.gc3Domain`, `Out.gc3`. CLI: `xmpp-serve --gc3 gc3.<domain>`.
- Not covered: knocking, configuration, history, MLS or any encryption, spaces, persistence.

## 2026-11-03 (later): held stanzas in Lean, bounded (issue 1235; step 6, part 1)

- `L4Factoidal/XMPP/Held.lean`: `hold` (refuses past `perAccount` 1,000 or `total` 100,000) and
  `release` (hands back everything held for an account and empties its queue). Theorems:
  `hold_perAccount`, `hold_refused`, `hold_limits`, `release_empties`, `release_returns`. The total
  bound is checked by a `#guard`; its proof needs the one-queue-per-account invariant (to do).
- `Wasm/Ops/XmppSession.lean`: the ops layer keeps the bound full JIDs (`bound`) and the held
  queue (`held`). `Out.route` to an account with a bound session is delivered; otherwise it is held,
  or, past a bound, a message is answered `resource-constraint` (RFC 6120 section 8.3.3.18).
  `bindTransition` hands a newly bound account what was held, oldest first.
- The JS host no longer decides holding; its `pending` map is a fallback for a session that closed
  between the engine's decision and the delivery, bounded at 100.
- Tests: `npm/factoidal/test/xmpp-mix.test.mjs` (the former 1235 xfail, now a check),
  `xmpp-serve.test.mjs` (held, then delivered once on bind).
- Persisting the held queue across a restart: issues 1237 and 1238.
