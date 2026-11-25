# Foafnaut: Tor and onion services, what the network design must allow (2026-11-25)

Status: analysis, no code. Owner question, 2026-11-25, verbatim: "what would it take for a
browser such as foafnaut to implement Tor onion network fully and securely?" Owner notes,
same day, verbatim: "connection pooling is being designed concurrently with this
conversation. Also, the substrate (currently Deno on OSX) is up for negotiation, and will vary
with target underlying platforms."

Related: the network record
[2026-11-24-foafnaut-concurrency-and-network.md](2026-11-24-foafnaut-concurrency-and-network.md)
(sections 5 to 7), the pool contract `formal/veil/FoafnautModels/HttpConnections.lean`, and the
fingerprint issue https://github.com/danbri/factoidal/issues/1306 (can Foafnaut look like a
mainstream browser; owner's first estimate: "Infeasible, presumably.").

Section 1 was read from the code at `691df902` on 2026-11-25. Crypto gaps were found by a
search of module names and text (`SHA3`, `SHAKE`, `Keccak`, `AES-CTR`) under
`formal/lean4/L4Factoidal/`. That method cannot see a primitive with another name; check again
before you rely on a "not found".

## 1. What the current design gives

- The engine decides every request (`Net/PageFetch.lean`, `Net/Egress.lean`). The host
  (`labs/demos/foafnaut/native_net.ts`) moves bytes. A Tor route is therefore one decision in
  the engine and one transport in the host.
- The pool and the DNS cache are keyed by a network partition (the top-level site). This maps
  to Tor stream isolation: streams for different partitions use different circuits.
- The desktop host has raw sockets (`socketOpen`).
- Crypto through HACL*: X25519, Ed25519, SHA-1, SHA-2, HKDF, HMAC. AES-GCM on x86-64 only
  (owner decision 2026-10-27, `Crypto/AesGcmNative.lean`).

## 2. What conflicts with Tor

1. DNS. `Egress.lean` requires the engine to know every address before a request; the host
   resolves the name and the engine pins the address (DNS rebinding rule). On the Tor route the
   client must not resolve a name: the exit relay resolves it, and a `.onion` name has no
   address. Egress needs a second mode with no local resolution. In that mode the
   special-purpose address check cannot run locally.
2. TLS. Page TLS is the host's (Deno). Tor relays do not use Web PKI certificates; the Tor link
   handshake authenticates them. This matters only for a Tor client inside the engine (route C).
3. Crypto not found: SHA3-256 and SHAKE-256 (onion v3 addresses, descriptors, key blinding),
   AES-128-CTR (relay cells), Ed25519 key blinding (needs scalar operations that a normal
   Ed25519 interface does not expose). AES is refused on arm64 today.
4. Hub build. It runs inside a host browser, which has no raw TCP. Tor there needs a Snowflake
   (WebRTC) or WebTunnel (HTTPS, WebSocket) bridge.

## 3. Routes

- A. Local Tor SOCKS port (C tor or Arti). The host sends each Tor-route connection to SOCKS5
  with the host name (address type 3), never an address. Each partition gets its own SOCKS
  username and password, so Tor isolates its streams (`IsolateSOCKSAuth`). No new crypto in the
  engine. Smallest change and lowest risk.
- B. Arti embedded through FFI, one isolation token per partition. Adds a Rust dependency.
  HACL* is a precedent for a vendored native library.
- C. A Tor client written in Lean: directory consensus and signature checks, guard state,
  circuits (ntor), relay cells, onion service v3 client (descriptor lookup on the hash ring,
  introduction, rendezvous, client authorisation, proof-of-work). Largest; then external
  review. The Tor Project advises against new independent implementations.

## 4. Requirements on the pool design (in progress, issue 1031)

1. The pool key has a route, not an address: `direct address` or `tor isolationToken`. Put the
   two cases in `HttpConnections.lean` now, so that Tor mode needs no model change later.
2. No connection reuse across origins. HTTP/2 connection coalescing (RFC 9113 section 9.1.1)
   stays off. The model already forbids it; on the Tor route coalescing would join two sites
   on one circuit.
3. When an isolation scope ends (partition closed, "new identity"), close every connection and
   circuit with that key. Tor retires circuits after `MaxCircuitDirtiness` (10 minutes by
   default); a connection that ends with its circuit fails its pending requests, as the model
   already says for a closed connection.
4. Invariant for the `DnsCache` model (network record section 7): a Tor-route request causes
   no local name lookup.

## 5. Requirements on any substrate

For the Tor route a substrate supplies one of:

- a SOCKS5 client that sends the host name, with a username and password per connection;
- an embedded Tor library with isolation tokens;
- raw TCP and a TLS client that gives the engine the peer certificate without Web PKI
  validation (route C only).

In Tor mode the substrate must let the engine turn off: its own name lookups; proxy settings
from the environment and the operating system (`HTTPS_PROXY`, proxy auto-configuration); its
own HTTP cache and cookie jar.

By target: macOS, Linux, Windows desktop: all three. iOS and Android: an embedded library
(examples: Onion Browser with Tor.framework, Tor Browser for Android); the operating systems
limit a separate daemon. Hub: bridges only, or no Tor.

## 6. Limits on every route

- Fingerprint. Foafnaut's layout, fonts, CSS support and JavaScript engine differ from every
  mainstream engine, so a site can tell a Foafnaut user from a Tor Browser user. The anonymity
  set is Foafnaut users on Tor. Tracked in https://github.com/danbri/factoidal/issues/1306.
- FOAF crawl. The order in which a user follows `foaf:knows` and `rdfs:seeAlso` shows whom and
  what the user looks at. Tor hides the network path, not the requests.
- No clearnet fallback. In Tor mode every request uses the Tor route: images, fonts,
  WebSocket, and the address step of Egress.
- Code delivery (Hub). A server that sends the page code on each load can send other code.

## 7. Tests to write before Tor work starts

Each is an expected failure that names an open issue until the feature lands (project rule,
"A stated shortfall"): no DNS query leaves the machine in Tor mode; a `.onion` page loads;
two partitions use two circuits (two SOCKS credentials on route A).

## 8. Measured: Arti components in a Foafnaut page (2026-11-25)

Owner request, 2026-11-25, verbatim: "try building the tor wasm and running it in a simple page
using our wasm implementation. I know this is not a secure path for the real thing, but it will
give a sense for whether this compontent might work easily."

Method. A probe crate on Arti 0.48.0 (`tor-hscrypto`, `tor-netdoc`, `tor-llcrypto`,
`tor-checkable`), built for `wasm32-unknown-unknown` with `wasm-bindgen` 0.2.130
(`--target no-modules`), 450 KB of wasm. A page fetched it over local HTTP, instantiated it with
page `WebAssembly` (BubblePopWASM), and called it from BubblePopJS. Host: the Linux rig
(`tools/foafnaut-linux-rig`, released engine `build-e4445d14752c`, Xvfb, software Vulkan) on a
cloud container. Real time is the host's `leanMs` for the page task that made the call. Reference:
the same module in Node 22. Source, build and run scripts: `labs/demos/foafnaut/tor-probe/`
(`build.sh`, then `run.sh tor-split.html`). A rerun from those scripts gave 62, 803 and 6989 ms for
the three rows below.

Results, Foafnaut against Node:

| Step | Foafnaut | Node | Result |
|---|---|---|---|
| Parse and check an onion v3 address, blind its key for the current time period; parse a 6-relay microdescriptor consensus (Arti test data) | 81 ms (4.9 million instructions) | 3 to 9 ms | same blinded key as Node; a bad checksum is refused |
| x25519 key agreement, 20 pairs | 768 ms, 38 ms a pair | 0.55 to 1.2 ms a pair | keys agree |
| Relay cell crypto, 2000 cells through 3 hops (AES-128-CTR) | 7097 ms, 143 KB/s | 9 to 16 MB/s | round trip correct |

The engine ran about 150 million counted instructions a second.

Findings:

1. The components that need no network run correctly in BubblePopWASM.
2. Circuit set-up cost is acceptable: about 4 to 6 x25519 operations a hop, so of the order of
   100 to 300 ms for a 3-hop circuit in this measurement.
3. Relay cell crypto is the limit: 143 KB/s on the page thread. AES-128-CTR needs a host
   primitive (WebCrypto on the JavaScript hosts, HACL* on native, as
   `skills/crypto-policy` already says for AES) before Tor data rates are usable.
4. `arti-client` 0.48.0 with its `tokio` feature does not compile for wasm: tokio's networking is
   not available on wasm targets. With `default-features = false` and the patch of item 5, it
   compiles for `wasm32-unknown-unknown` (checked 2026-11-25). It still needs an Arti runtime
   (`tor-rtcompat`) for wasm and a transport the host provides; neither is in Arti 0.48.0
   (section 9).
5. `saturating-time` 0.6.0 (used by `tor-netdoc`) does not compile for `wasm32-unknown-unknown`:
   it names `std::time::Instant` where `web-time-compat` gives `web_time::Instant`. The probe used
   a local patch. Not reported upstream: owner rule of 2026-11-25 in `CLAUDE.md`, "Never report
   upstream".
6. Page `Date.now()` and `performance.now()` read the virtual script clock (`Page.lean`, "The
   script clock"; it starts near 0). A Tor client needs wall time (consensus validity, onion
   service time periods). The host must give the Tor component real time as a capability; the
   probe took it as an argument.
7. Decoding 600 KB of base64 in a page script stopped at the BubblePopJS step budget
   (`runBudget`, 5 million steps for one run). Load large modules with `fetch`.
8. Not measured: a full live consensus (about 8000 relays). The test consensus has 6 relays; do
   not extrapolate from it.

## 9. Other work on Tor in wasm (web search, 2026-11-25)

Read from the pages on 2026-11-25; nothing here was run.

- Ethereum Foundation, "Embedding Tor in Browser Wallets, Frontends, and dApps", 2026-03-20,
  https://reads.ethereum.foundation/blog/embedding-arti-in-the-browser/ (npm package tor-js). Arti
  on a fork (voltrevo/arti, branch wasm-arti-client) for `wasm32-unknown-unknown`. A custom
  `WasmRuntime` (timers from gloo_timers, wall clock from `Date.now`, tasks from
  `spawn_local`). Transport: Snowflake only (WebSocket or WebRTC, then KCP, SMUX, rustls, Tor).
  Directory: a bootstrap archive over HTTPS, kept in IndexedDB; first bootstrap about 3 minutes in
  wasm against about 15 s native, then reduced. Onion services: not stated. Their caveats: shared
  JavaScript context with the page, the bootstrap server sees the user's address, wasm
  fingerprinting, experimental rustls crypto provider, no audit yet. New crates `tor-time` and
  `tor-async-compat` were in review upstream.
- webtor-rs, https://github.com/ethereum/webtor-rs: a browser Tor client on Arti crates
  (README: Arti 1.8.0, tor-proto 0.37.0), about 1.2 MB gzipped. Transports: Snowflake (WebSocket
  and WebRTC) and WebTunnel. Onion services not implemented. No fingerprinting protection; no
  audit.
- Echalote, https://www.npmjs.com/package/@hazae41/echalote: a TypeScript Tor client over
  Snowflake and Meek. Its README says it is experimental with security issues; a third-party
  comparison says it does not validate TLS.
- https://github.com/brewsterkahle/onionpress/issues/154 (WASM Tor in browser, closed as a
  duplicate on 2026-10-11): a comment cites Arti merge requests !3816 (arti-client builds for
  wasm32 with no default features), !3763 (a web example) and !3600, and says Arti has no wasm CI.
  Not checked against Arti's GitLab.

For Foafnaut: the runtime of item 4 and a host transport (Snowflake or WebTunnel on the Hub; raw
TCP on desktop) are the missing parts; the tor-js runtime is the nearest existing design. Its
clock reads `Date.now`, which in a Foafnaut page is the virtual clock (section 8, item 6).
