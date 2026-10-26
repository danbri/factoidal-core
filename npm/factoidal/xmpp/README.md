# `@factoidal/core/xmpp`

A functional-programming-style JavaScript API over `L4Factoidal.XMPP`
(Lean 4, compiled to WebAssembly) — the fresh, GC3-targeting XMPP
implementation described in
[`formal/lean4/L4Factoidal/XMPP/README.md`](../../../formal/lean4/L4Factoidal/XMPP/README.md).

```js
import { parseJid, parseStreamHeader, featuresFor, parseStanza } from '@factoidal/core/xmpp'

const jid = await parseJid('romeo@example.net/orchard')
// { ok: true, value: { localpart: 'romeo', domainpart: 'example.net',
//                       resourcepart: 'orchard', wellFormed: true } }

const bad = await parseJid('@example.com')
// { ok: false, error: 'not a structurally valid JID: @example.com', unknownOp: false }

const features = await featuresFor('postTls', ['SCRAM-SHA-256', 'PLAIN'])
// { ok: true, value: { startTlsRequired: null,
//                       saslMechanisms: ['SCRAM-SHA-256', 'PLAIN'],
//                       canBind: false, canSession: false,
//                       xml: '<stream:features>...</stream:features>' } }
```

## Design: functions in, results out, nothing thrown for an expected outcome

Every function here is pure: plain data in, plain data out, no classes,
nothing to construct or hold onto. A malformed JID, a stanza that isn't
`message`/`presence`/`iq`, an unknown negotiation stage — these are
**ordinary answers**, not exceptional control flow, so every function
returns

```ts
{ ok: true, value: T } | { ok: false, error: string, unknownOp: boolean }
```

rather than throwing. The one thing that still throws is a genuine
host/environment failure — the wasm module not being resolvable or
loadable at all (`loadXmppEngine()`), which is not a protocol-level
outcome and has no sensible data shape to return instead.

## API

| Function | Wraps op | Notes |
|---|---|---|
| `parseJid(jid, options?)` | `xmppJidParse` | RFC 7622 structural + length well-formedness; PRECIS not yet enforced (see below) |
| `renderJid(parts, options?)` | `xmppJidRender` | `{localpart?, domainpart, resourcepart?}` → string |
| `parseStreamHeader(xml, options?)` | `xmppStreamHeaderParse` | tolerates a leading `<?xml ...?>` declaration |
| `renderStreamHeader(header, options?)` | `xmppStreamHeaderRender` | inverse |
| `featuresFor(stage, mechanisms?, options?)` | `xmppFeaturesFor` | `stage` is one of `preTls`/`postTls`/`authenticated`/`bound` |
| `parseStanza(xml, options?)` | `xmppStanzaParse` | `message`/`presence`/`iq` only; payload children come back as one serialized `payloadXml` string, not a tree |

Every function accepts an optional `{ engine }` in its last argument to
reuse an already-loaded engine handle (`await loadXmppEngine()`) instead
of paying the load cost per call — see `loadXmppEngine()`'s doc comment.

`xmppOpsAvailable(options?)` reports whether the resolved wasm module
carries these ops at all, so a caller (or a test) can skip gracefully
against an older committed bundle instead of getting a confusing
"unknown op" error.

## The server: `@factoidal/core/xmpp/server` and `factoidal xmpp-serve`

```sh
mkdir -p state && printf 'juliet:r0m30\nromeo:juli3t\n' > state/accounts
npx factoidal xmpp-serve state --domain localhost            # plaintext on 5222
npx factoidal xmpp-serve state --cert fullchain.pem --key privkey.pem   # XEP-0368 direct TLS on 5223
```

```js
import { listen } from '@factoidal/core/xmpp/server'
const running = await listen({ dir: 'state', domain: 'localhost', port: 0 })
console.log(running.origin)        // xmpp://127.0.0.1:<port>
await running.close()
```

`server.mjs` is a socket, a UTF-8 decoder and a routing table. It runs
one engine session per connection and answers every byte through the
engine's `xmppSessionFeed` operation; `L4Factoidal.XMPP.Server.step`
(Lean, `formal/lean4/L4Factoidal/XMPP/Server.lean`) makes every
protocol decision and the host performs what comes back. It is the same
library the native carrier (`deploy/fly/xmpp/`, one `l4xmpp-serve`
process per connection behind socat) serves; the wasm session ops are
`formal/lean4/Wasm/Ops/XmppSession.lean`.

| op | arguments | answer |
|---|---|---|
| `xmppOpen` | `[configJson]` | `{ ok, handle, domain, accounts }` |
| `xmppSessionOpen` | `[server, optionsJson]` | `{ ok, handle }` — `streamId` and `nonce` are required and come from the host's random source |
| `xmppSessionFeed` | `[session, text]` | `{ ok, send: [...], route: [{to, text}], presence: [...], rostersSaved: [...], close, stage, bare, full, bufferedBytes }` |
| `xmppSessionDeliver` | `[session, text]` | `{ ok, delivered, send }` — `delivered:false` for an unbound session; nothing is lost |
| `xmppSessionClose` | `[session]` | `{ ok, send }` |
| `xmppRosterGet` / `xmppRosterSet` | `[server, bare]` / `[server, bare, encoded]` | the roster in the engine's own on-disk encoding |
| `xmppClose` | `[server]` | `{ ok, sessions }` |

The state directory is laid out as the native carrier's, so the two
hosts can share one: `DIR/accounts` (one `user:password` per line),
`DIR/roster/<bare jid>.tsv` (persisted on every `rostersSaved`, loaded
on start), and `DIR/spool/<bare jid>/<file>` — a stanza written there
by any process is delivered to that account's bound session and
unlinked. That last one is how a program that is not an XMPP client (a
web application, say) hands a user a message: write a file.

Roster snapshots are written in order through temporary-file replacement.
`await running.close()` waits for queued writes and rejects if persistence
failed. This protects against overlapping writes within one host; it does
not coordinate concurrent processes or promise recovery after a power loss.
The spool file is removed when the engine accepts delivery, before any
remote acknowledgement. Stanzas queued for offline accounts in this Node
host are held in memory and disappear on process exit.

`maxBuffered` (default 1 MiB) limits the engine's residual UTF-8 input after
each feed, reported by `bufferedBytes`. A decoder can separately hold up to
three bytes of an incomplete UTF-8 sequence. This is not a bound on complete
stanza size, output queues, offline queues, connection count or idle time.
The host requires this field; an older engine without it closes the affected
connection with an error. Rebuild the host and engine together.

What it speaks: RFC 6120 stream negotiation, stream errors, SASL PLAIN
and SCRAM-SHA-256, resource binding; RFC 6121 roster, presence
subscription and broadcast, message delivery with the server-stamped
`from`; XEP-0030 `disco#info`; XEP-0368 direct TLS with `--cert`/`--key`.
Not: STARTTLS, server-to-server federation, MUC/MIX/GC3 rooms, PRECIS.
Known limitation shared with the native harness: one SCRAM salt per
server (`saltB64` in the config), not one per account.

The shared engine currently reduces routed destinations to bare JIDs and
the Node host delivers to every bound resource. It does not implement full
resource-selection/priority semantics. Binding alone permits delivery; this
is not a complete presence-availability policy. The plaintext test listener
also offers SASL PLAIN and has no transport confidentiality. Supplying only
one of `cert`/`key` is rejected; supplying both selects direct TLS.

Tests: `node --test test/xmpp-serve.test.mjs` drives the host over real
TCP sockets, including an independent SCRAM-SHA-256 computed with
`node:crypto`; `tools/xmpp-interop.sh wasm` drives it with
`@xmpp/client`, a third-party implementation.
`node --test test/xmpp-host.test.mjs` separately checks IO cleanup and
persistence with a mock engine; passing it makes no protocol-conformance claim.

## What this does not cover yet, on purpose

- **Stanza construction from JSON.** `parseStanza` has no inverse: building
  a stanza's XML back from a JSON payload description needs a
  sibling-node XML constructor the Lean side doesn't have yet.
- **GC3 itself.** Still an unfinished, early-stage upstream XSF spec —
  see the design record.
- **SASL/SCRAM computation as a pure function.** The server ops above
  do SCRAM-SHA-256 (via `L4Factoidal.XMPP.Scram` and the HACL* SHA-256
  binding); there is no standalone pure op for it in this module.
- **MUC/MIX interop modules.**

## Upstream limit found via this module's tests (2026-09-07), repaired 2026-10-10

`parseStanza`/`parseStreamHeader` delegate general XML parsing to the
shared `L4Factoidal.XML` module (reused rather than duplicated — see
the design record). Until 2026-10-10 its scan of a text run or a start
tag for references (`XML.scanRefs`) used one stack frame per reference:
a text body with about 2,000 consecutive entity references (for example
`"&amp;".repeat(2000)`) overflowed the wasm call stack
(`Maximum call stack size exceeded`), and the adversarial test was
pinned at 1,000. Issue: https://github.com/danbri/factoidal/issues/673.

The scan is now a loop (`XML.scanRefsLoop`, proved equal to
`XML.scanRefs`). Measured 2026-10-10 with the rebuilt wasm module:
100,000 sequential references in a text node or an attribute value parse
under `node --stack-size=512`; before the repair, 5,000 overflowed there.
`test/xmpp.test.mjs` now parses a body of 10,000 `&amp;` references and
checks the rendered payload. The depth of NESTED entity expansion (an
entity whose replacement text references another entity) still costs one
frame per level, bounded by the number of declared entities. RFC 6120
§11.1 excludes DTD subsets and every entity reference except the five
predefined ones from an XML stream, so conforming XMPP input has no
nested expansion.

## Testing

```bash
cd npm/factoidal
node --test test/xmpp.test.mjs
```

Skips wholesale when the Lean wasm assets aren't resolvable, and skips
per-op when the resolved bundle predates a given op (see
`xmppOpsAvailable`) — the same pattern `test/l4-core.test.js` uses.
