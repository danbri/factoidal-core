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
