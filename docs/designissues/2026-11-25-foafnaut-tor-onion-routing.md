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

## 10. Arti 2.8.0 built for wasm and run in Foafnaut (2026-11-25)

Owner, 2026-11-25, verbatim: "ok looks like you should build from the main source into wasm, and
whatever minimal accomodations we need to make for that. Document everything." Then: "1 make it
as secure and privacy respecting as we can. 2. (B) but do it clean using the latest stable TOR
code and build it for wasm here." Then: "Check for Tor security oopsies too", with
https://app.opencve.io/cve/?product=tor&vendor=torproject. Route (B) is section 3: Arti embedded,
here as wasm.

Code: `labs/demos/foafnaut/tor-wasm/` (README there). Result: Arti starts in a Foafnaut page and
runs its bootstrap until it needs the network; there is no transport, so it stops there.

### 10.1 Source

Arti 2.8.0 (3 November 2026), tag `arti-v2.8.0`, commit
`7c038125baef924a4bf287429c192c5af606f79c`, the latest release on 2026-11-25 (`main` has newer
commits but no newer tag). `build.sh` clones the tag and stops if the commit differs. Its
changelog lists fixes for TROVE-2026-069 and TROVE-2026-070 and for 16 RustSec advisories in
dependencies, so the build includes them.

### 10.2 Changes to Arti (`arti-2.8.0-wasm.patch`, all wasm-only)

1. `saturating-time` (an Arti crate): `use std::time::Instant` where `web_time_compat` gives
   `web_time::Instant` on `wasm32-unknown-unknown`. Two imports changed. Same defect on `main`.
2. `arti-client` `statemgr_from_config`: `unimplemented!()` on wasm (also on `main`). Now
   `TestingStateMgr::new()`, Arti's in-memory state manager, which `client.rs` already imports on
   wasm.
3. `tor-dirmgr`: the directory store is SQLite plus files, with no wasm option (also on `main`).
   New `storage/memory.rs` (254 lines): the same rows in maps, one method per SQL query, named on
   each method. `open_store` uses it on wasm.

For the owner (CLAUDE.md, "I am the upstream route"): items 1 to 3 are defects or gaps in Arti
2.8.0 and `main` for `wasm32-unknown-unknown`. Item 4 of 10.4 (vanguards off when default
features are off) is an Arti packaging trap.

### 10.3 Runtime and configuration (`src/lib.rs`)

- Tasks: `wasm_bindgen_futures::spawn_local`. Timers: `setTimeout` (gloo-timers). Blocking work:
  run at once; `reenter_block_on` panics (there are no threads), and `panic = "abort"` ends the
  module: it fails closed.
- Network: TCP, Unix sockets, UDP and listening all return the error "no transport"; each refusal
  is counted (`refusedConnections`). TLS: a connector that refuses. No other path exists.
- Wall clock: Arti reads `SystemTime` directly in places (`tor-dirmgr/src/bootstrap.rs:830`,
  `tor-dirmgr/src/lib.rs:195`, `arti-client/src/status.rs`), so the runtime cannot correct it.
  A Foafnaut page clock is virtual and reads 0 ms at load (measured). `pages.py` sets
  `Date.now()` to the real time at page generation plus the page's monotonic time since load.
  `bootstrap` refuses to start when the clock reads earlier than 2024.
- Configuration: placeholder state and cache paths (never opened; the defaults need a home
  directory); keystore kind `Ephemeral` (keys in memory only).
- Features: the `arti` program's default security set (`onion-service-client`, `vanguards`,
  `compression`, `bridge-client`) less `pt-client` (it starts processes), plus `memquota`,
  `keymgr`, `ephemeral-keystore`.

### 10.4 Security review

Method: Arti 2.8.0 source and changelog, read locally; the OpenCVE list for C tor (page 1 of 3);
RustSec pages for tor-circmgr. The GitLab changelog page refused the web fetch (HTTP 403); the
clone has the same file.

1. Fixed here: with `default-features = false`, Arti builds without `vanguards` and replaces the
   vanguard configuration with a disabled one (`arti-client/src/config.rs:72-82`). Onion service
   circuits are then open to guard discovery. The build enables `vanguards`.
2. Fixed here: no fallback path. Every connection attempt reaches the refusing provider (Node: 46
   and 56 refusals in 15 s; Foafnaut: 16 to 30). Names are never resolved locally.
3. Checked: page randomness. `crypto.getRandomValues` in a Foafnaut page is HMAC_DRBG-SHA-256
   seeded with 32 bytes from `IO.getRandomBytes` (the operating system) per session, refused
   after 2^48 calls (`WasmVM/Hosts/WebApi.lean:207-225`, `labs/demos/foafnaut/WebScripts.lean:297-304`).
   It is never reseeded, so a read of the generator state gives later outputs.
4. Open: page clock (https://github.com/danbri/factoidal-core/issues/1061, page clock is virtual).
   The shim drifts with the virtual clock; a wrong date breaks consensus and onion service
   time-period checks.
5. Open: state in memory (https://github.com/danbri/factoidal-core/issues/1058, guard churn). Each
   page load picks new guards and fetches the whole directory again.
6. Open: shared script context (https://github.com/danbri/factoidal-core/issues/1059). Another
   script in the page can read Arti's memory, keys included.
7. Open: no transport (https://github.com/danbri/factoidal-core/issues/1060). A future transport
   must keep Arti's own link authentication (CERTS cells), never add Web PKI checks, and never
   fall back to a direct connection. rustls on wasm also needs `rustls-pki-types` with its `web`
   feature (a build of `arti-client` with `rustls` failed on `UnixTime::now`).
8. Note: `memquota` cannot read the memory size on wasm and uses a constant 1 GiB.
9. Note: `hs-pow-full` is off, as in the `arti` program: onion services that require
   proof-of-work under attack may be unreachable.
10. Note: Arti's log lines go to the page console with Arti's safe logging (addresses redacted).
    A host that stores console lines must not store these.
11. Advisories: none found that affects Arti 2.8.0. RUSTSEC-2024-0339 and RUSTSEC-2024-0340
    (tor-circmgr, vanguard path lengths) were fixed in tor-circmgr 0.18.1, long before 0.48.0.
    The C tor CVEs of 2026 on OpenCVE (for example CVE-2026-77587, conflux use-after-free that a
    hostile exit can use to crash a client; CVE-2026-77638, rendezvous point impersonating an
    onion service) are for C tor. Arti's changelog is the record for Arti; the conflux and
    rendezvous code paths are the ones to watch.
12. Fingerprint: https://github.com/danbri/factoidal/issues/1306.

### 10.5 Measurements (2026-11-25, cloud container, Linux rig)

- Build from a clean clone: 2 min 11 s. Module: 5,103,695 bytes of wasm.
- Node 22: client created, bootstrap at 0% "fetching a consensus" until the 15 s limit.
- Foafnaut (released engine `build-e4445d14752c`): the same steps and messages. The page task
  that loads and starts Arti: 11.3 to 11.4 million counted instructions, 1987 to 2226 ms of real
  engine time (three runs).
- Tests: `node --test xfail.test.cjs`: 4 pass, 0 fail (out of 4: three expected failures and the
  refused-connection check). `run.sh`: page clock expected failure holds (raw clock 0 ms).

## 11. What Deno can give the Arti wasm client (2026-11-25)

Owner, 2026-11-25, verbatim: "we don't yet have a transport. What can be done with Deno?"

The desktop host is Deno. A Deno Worker of the host (not the page) can run the Arti module and
give it what a page cannot. Checked in this container on 2026-11-25:

| Need | Deno | Issue it closes |
|---|---|---|
| Transport | `Deno.connect` opens raw TCP (needs `--allow-net`). | https://github.com/danbri/factoidal-core/issues/1060 |
| TLS | `Deno.connectTls` checks certificates against Web PKI and its `handshake()` gives only `alpnProtocol` (checked), not the peer certificate. Tor relays use self-signed link certificates, and Arti needs the peer certificate and RFC 5705 keying material. So TLS runs inside the module (rustls) over the raw TCP stream. | part of 1060 |
| Real clock | `Date.now()` in Deno is the real clock. | https://github.com/danbri/factoidal-core/issues/1061 (for the worker; pages still need it) |
| Randomness | `crypto.getRandomValues` from the operating system. | none needed |
| State | `Deno.writeFile` and `Deno.readFile` in the host's state directory, sealed at rest. | https://github.com/danbri/factoidal-core/issues/1058 |
| Isolation | A Deno Worker is a separate isolate: no page script can read its memory. Pages reach it only through a narrow message interface. | https://github.com/danbri/factoidal-core/issues/1059 |

Other Deno routes, not chosen: `Deno.Command` can start a C tor or Arti program and use its SOCKS
port (route A, section 3), which needs a separate binary; Deno FFI to a native Arti library has
no stable C interface to call.

Rules for the transport: the Worker accepts only IP literals and ports from the consensus (no
name lookup); the engine's Egress decision gets a Tor route mode with no local resolution
(section 2, item 1); no request falls back to a direct connection.

Testing:
- This container cannot reach the Tor network: a TCP connection to the fallback relay
  171.25.193.9:443 opens, but the TLS certificate is issued by "Anthropic, Egress Gateway SDS
  Issuing CA (production)" (checked with `openssl s_client`). Arti must refuse that link, because
  the relay's CERTS cell will not match it. That refusal is a negative test that can run here.
- A local Tor test network can run here: Ubuntu has C tor 0.4.9.11 (`apt-cache policy tor`), and
  chutney builds a private network of authorities, relays and an onion service. Arti then
  bootstraps against that network, end to end, with no public traffic.
- The live network can be tested on the owner's Mac.

## 12. The Deno worker transport (2026-11-25)

Owner, 2026-11-25, verbatim: "Build the Deno Worker transport with TLS for now, but we don't
trust it for real users just yet."

Code: `labs/demos/foafnaut/tor-wasm/` (`src/lib.rs`, `deno/`, `chutney/`). It runs only after the
caller passes `--dangerously-use-unreviewed-tor-transport` (module function
`enable_unreviewed_transport` with that exact string); it prints the experimental code notice.

### 12.1 What it is

- `deno/tor-host.ts` starts `deno/tor-worker.ts` as a Deno Worker with permissions: network,
  read of the module directory; no write, environment, subprocess, FFI, system or import. It
  needs `--unstable-worker-options`.
- The worker gives the module `globalThis.torHost`: `connect` (IP literal and port only; a name
  is refused, so nothing is resolved), `read`, `write` (copies the bytes before any await,
  because they point into module memory), `close`.
- In the module, `HostStream` is Arti's TCP stream over those calls. TLS runs in the module:
  Arti's `RustlsProvider` with the rustls `ring` crypto provider. Arti's own verifier checks the
  link certificate against the relay's CERTS cell; Web PKI is not used.
- `bootstrap(timeout, configToml)` takes an optional Arti configuration (for example a private
  network's `[tor_network]`); `stream_request(host, port, request, max, timeout)` opens one
  stream through the client.
- The worker's clock is Deno's real clock, and it is a separate isolate: for this path the
  page clock (https://github.com/danbri/factoidal-core/issues/1061) and the shared script
  context (https://github.com/danbri/factoidal-core/issues/1059) do not apply. State is still in
  memory (https://github.com/danbri/factoidal-core/issues/1058).

### 12.2 More changes to Arti (in `arti-2.8.0-wasm.patch`)

4. `tor-rtcompat`: `RustlsProvider`, `UnimplementedTls` and the `impls` module are compiled only
   with a native runtime feature (tokio, async-std, smol). The gates now also admit
   `wasm32-unknown-unknown`, where the embedder gives the runtime.
5. `tor-rtcompat/src/impls.rs`: the existing wasm stubs name `socket2`, which is not a
   dependency on that target. The import is gated, and the stub `tcp_pre_connect` returns
   `void::Void` on wasm.

For the owner (upstream route): items 4 and 5 are defects of Arti 2.8.0 on
`wasm32-unknown-unknown`: an embedder there cannot use Arti's TLS provider without them.

The patch now touches 8 files: 295 lines added, 7 removed (254 of them the in-memory store).

### 12.3 Tests and results (this container, 2026-11-25)

- No opt-in: 66 connection attempts refused, 0 dialled.
- Opt-in, public network: this container cannot reach Tor. Port 443: the container's gateway
  completes TLS with its own certificate, and Arti then refuses the link ("Invalid CircID in
  variable cell"). Other ports: connection refused. No circuit was built through the gateway.
- Opt-in, private network (`chutney/run.sh`: chutney with C tor 0.4.9.11, 4 authorities,
  3 relays, 2 exits, one onion service, two local web servers): bootstrap 100%, a request
  through an exit, and a request to the onion service (v3, vanguards on) all PASS. Client time
  about 1 s; the script takes about 130 s, most of it the network starting.
- `node --test xfail.test.cjs`: 6 pass, 0 fail (out of 6).
- Foafnaut page (no host transport): unchanged behaviour; start task 2654 ms (module now
  6.9 MB after wasm-bindgen, with rustls and ring).

### 12.4 Security findings in this step

1. Fixed: Arti's debug lines were printed with debug off (my filter looked for " DEBUG " with a
   space before it; the line starts with the level). Debug lines carry relay addresses in clear
   (`tor_proto` "starting Tor handshake with ..."), outside Arti's safe logging. Test: "no debug
   lines by default", with a control that switches debug on and must see them.
2. Fixed: host errors carried a JavaScript stack with local file paths into Arti's logs. Only the
   message is kept now.
3. Open: the worker's network permission is `net: true`, because Deno cannot limit it to the
   relays of a consensus; the worker itself refuses names. A host that adds other network use to
   this worker breaks the rule.
4. Note: ring's constant-time code is compiled to wasm; a wasm engine (V8 with JIT in Deno) does
   not promise constant-time execution. Timing side channels are not reviewed.
5. Note: one TLS session per relay link, no session resumption (Arti disables it, per tor-spec).

### 12.5 Errors in method, with their cost

- The debug filter of 12.4 item 1 went out in a working build and was found by reading a page
  log. Cost: debug lines with relay addresses would have reached any console store. The test
  now checks it, with a control.
- `chutney/run.sh` first checked free ports with `ss`, which this container does not have: the
  check passed silently. A run then failed after 5 minutes because an earlier network still held
  the ports (C tor relays take up to 30 s to exit after SIGTERM). The check now connects to each
  port. Trap recorded in `skills/foafnaut/SKILL.md`.

## 13. Does our Ethereum code have the same networking problem? (2026-11-25)

Owner, 2026-11-25, verbatim: "Look at our Ethereum code, such as it is. That will also need to do
some networking. Does it have the same problem?"

Where it is: `labs/ethereum-wasm-sparql/` and `zkvm/risc0/evm/` on `main`; the Lean EVM
(`formal/lean4/evm-cleanroom/`) on side branches, newest in
https://github.com/danbri/factoidal-core/pull/1057 (authenticated state witnesses).

What networking it does: only `formal/lean4/evm-cleanroom/scripts/rpc/capture.mjs` (Node, on the
pull request branch) reads public chains through seven allowlisted JSON-RPC methods over HTTPS
(PublicNode, dRPC, Optimism, Polygon). The Lean code reads the saved captures and does no
networking; its `TransactionTransport` module is a resource check on JSON input. The zkVM tools
say: "No external-chain transaction, RPC call to a public chain, or remote proof request is part
of these tools or the recorded tests." The lab on `main` does none.

Answer:
- Transport: no. JSON-RPC over HTTPS uses Web PKI TLS, which `fetch` gives in Node, Deno and
  (where the provider sends CORS headers) a page. Raw TCP and TLS in the module, as for Tor,
  would be needed only for peer-to-peer Ethereum (devp2p: RLPx over TCP with its own ECIES
  handshake, discovery over UDP). None of that exists here.
- Clock: less exposed. The checks use block numbers and hashes. A decision about "latest" or a
  light-client sync period would need real time; in a Foafnaut page it would get the virtual
  clock (https://github.com/danbri/factoidal-core/issues/1061).
- Privacy: yes, a different problem. The RPC provider sees the client's address and every
  account, contract and call it asks about. JSON-RPC through the Tor transport would hide the
  address (many providers refuse Tor exits).
- Trust: the Lean verifier checks accounts and code against the header's state root (EIP-1186
  proofs), but the record says "Providers supply canonical chain selection": headers are not
  checked against the consensus layer (no light client). For Tor, Arti checks the directory
  authorities' signatures on the consensus; the Ethereum path has no equivalent check yet.
- In this container, HTTPS goes through a gateway that terminates TLS, so it can read RPC
  requests made from here.

## 14. Keeping Tor state between runs (2026-11-25)

Owner, 2026-11-25, verbatim: "sure (more than cookies?)" (to persistent state for the Deno
worker), then "could this be LWS pods but local not networked?"

### 14.1 What the state is, and how it compares with cookies

Arti stored two records in the private-network runs: `guards` (the guard sample and the
confirmed guards: relay identities with times) and `circuit_timeouts` (circuit build times).
Keys are not in it (the keystore is ephemeral).

- A cookie is sent to a site on each request. This state is never sent to any site.
- Read from the device, this state shows that the user runs Tor and names the user's guards.
  The guard set changes slowly and is close to unique, so someone who also watches traffic at a
  guard can use it to link that traffic to this device. C tor and Tor Browser keep the same data
  in a state file on disk, in clear text.
- So it is less exposed than a cookie to sites, and more sensitive than a cookie on a device
  that someone else can read.

Rules for this build: keep it sealed at rest; keep it local (never copy it to a remote pod);
keep it apart from page-visible storage; give the user a way to delete it.

### 14.2 Local LWS storage (proposed, not built)

Foafnaut already keeps bookmarks, history and settings in a local LWS storage
(`labs/demos/foafnaut/native_state.ts`: `lws-serve` on 127.0.0.1, authorization on, a did:key
owned by the browser). Tor state can go in a container of a local LWS storage of its own, with
`FACTOIDAL_LWS_KEY` set (sealed with ChaCha20-Poly1305 from HACL*), never synced to a remote pod.
The host process reads and writes it; the Tor worker gets no access to it. A storage written in
clear text is refused for Tor state: the state stays in memory instead, with a warning. Tracking:
https://github.com/danbri/factoidal-core/issues/1058 (its expected failure: the module reports
`state_backend()` "lws-sealed" only when the host says so).

### 14.3 Built now

- Arti patch (6th change): `tor-persist` `TestingStateMgr` gets `snapshot` and `preload`, and on
  wasm one process-wide store (`wasm_shared_state`) that `arti-client` uses.
- Module exports: `state_snapshot`, `state_load`, `set_state_store` (accepts only
  "lws-sealed"), `close`.
- Host: `--restart-check` runs a client, takes the state, starts a second worker with it and
  compares the guards; the state stays in the host process. `--hold MS` waits before the
  snapshot.
- Finding: Arti stores its state every 60 s (`tor-circmgr/src/lib.rs`, `fire_in(60 s)`). It also
  stores when the circuit manager is dropped, but dropping the client did not do that here (no
  "Flushed persistent state" line), so other references stay alive. A host must take a snapshot
  at least every 60 s, so a crash loses at most that much.
- Result: `chutney/run.sh` PASS for bootstrap, exit request, onion service request and "same
  guards after restart" (18 guard identity entries before and after). `node --test
  xfail.test.cjs`: 7 pass, 0 fail (out of 7). The patch now touches 10 files: 323 lines added,
  7 removed.

## 15. Tor state in a sealed local LWS storage (2026-11-25)

Owner, 2026-11-25, verbatim: "2 yes" (to: build the sealed local LWS storage for Tor state).

Code: `labs/demos/foafnaut/tor-wasm/deno/tor-state.ts`; host option `--state-dir DIR`.

- The host starts `factoidal lws-serve DIR/pod` on 127.0.0.1 with authorization on and a did:key
  owner (`DIR/agent.json`, mode 0600), with `FACTOIDAL_LWS_KEY` taken from
  `FOAFNAUT_TOR_STATE_KEY`. The key is not written to disk by this code.
- It uses the storage only when `lws-serve` prints "encryption at rest is ON" (ChaCha20-Poly1305,
  HACL\*). With no key, or a storage that is not sealed, it does not save and says why; the state
  stays in memory.
- The client fetches only that origin. The state is the resource `tor/state.json`. The Tor worker
  has no access to it; the host loads it into the worker before bootstrap and saves the worker's
  snapshot after it.
- The module is told `set_state_store("lws-sealed")` only when that store is in use.

Results (private chutney network, this container):

- `chutney/run.sh`: PASS for bootstrap, exit request, onion service request, "same guards after
  restart, through the sealed store" (18 guard identity entries before and after), and "no guard
  identity in clear text on disk" (a scan of every file of the storage for each guard identity
  string of the snapshot: 0 files).
- No key: "FOAFNAUT_TOR_STATE_KEY is not set ... so Tor state is not saved".
- `node --test xfail.test.cjs`: 7 pass, 0 fail (out of 7).

Limits:

- The at-rest scan looks for the identity strings as they appear in Arti's JSON. It cannot see a
  leak in another encoding; the sealing itself is the storage's (`LWS/DirLock.lean`, HACL\*).
- The key must come from somewhere safe; an operating system key store is not used yet.
- The host saves at the end of a run. A long session must save at least every 60 s (section 14.3).
- The engine bundle for `lws-serve` comes from the `web` set of `danbri/factoidal-builds`
  (`build-e4445d14752c-web`, sha256 checked, source commit in this history). In this container
  `tools/fetch-builds.sh` could not list releases (HTTP 403 from the GitHub API), so it was
  fetched by its tag.
- Pages: no change. https://github.com/danbri/factoidal-core/issues/1058 stays open for the page
  path; its expected failure (`state_backend()` is "lws-sealed") still fails there.

## 16. Stream isolation, new identity, periodic save, memory quota (2026-11-26)

Owner, 2026-11-26, verbatim: "keep improving Tor if there is more to do".

- Stream isolation: `stream_request(partition, ...)` uses one Arti `isolated_client()` per
  partition (for a browser, the top-level site). Streams of the same partition may share a
  circuit; streams of different partitions never do. An empty partition is refused, so no caller
  shares circuits by accident. Host syntax: `--request PARTITION@HOST:PORT`.
- New identity: `new_identity()` forgets every partition's isolation, so later streams use
  circuits that no earlier stream used. Host: `--request NEWID`.
- Periodic save: with `--state-dir`, the host saves the state every 60 s during a run, and at the
  end.
- Memory quota: 256 MiB (`MEMORY_QUOTA_BYTES`) unless the configuration sets `[system.memory]`.
  On wasm Arti cannot read the machine's memory and used a constant 1 GiB (section 10.4 item 8).

Test (`chutney/run.sh`, private network): exit streams siteA, siteA, siteB, new identity, siteA
used circuits `Circ 2.0, 2.0, 2.1, 2.2`: PASS "isolation (same partition shares, other partition
and new identity do not)". The check reads Arti's debug lines ("Got a circuit for ... tunnel_id"),
because Arti keeps a stream's circuit private; debug is on only in this test (section 12.4). All
six checks pass. Arti logged "Memory quota tracking initialised max=256 MiB"; the host made two
periodic saves. `node --test xfail.test.cjs`: 7 pass, 0 fail (out of 7).

Not done: the Foafnaut side that gives each page's top-level site as the partition, and a
"new identity" control in the browser. Both need the page transport
(https://github.com/danbri/factoidal-core/issues/1060).

Fix in the same step: the worker's IPv6 check tested only the characters used, so `a:b` and `:::`
passed it and could have reached Deno's resolver as names. `deno/ip-literal.ts` now accepts IPv4
with no leading zeros and IPv6 only when the WHATWG URL parser accepts it in brackets; no zone id.
`deno/ip-literal.test.ts`: 2 pass, 0 fail (out of 2 groups, 28 cases); the old check fails it.

## 17. Decisions of 2026-11-26: desktop on macOS, Keychain, no Hub

Owner, 2026-11-26, verbatim, to three questions (connect Tor to the browser; the storage key;
the Hub): "YES"; "Storage key - os keychain, yes on macosx. For now we build tor and test it
macosx only."; "Hub: NOT A GOAL. Security and browser-in-a-browser are odd bedfellows."

What follows:

- Tor runs only in a dedicated Deno worker of the native desktop host. `isolated_context()` now
  checks that `globalThis` is a `WorkerGlobalScope` (Deno module workers have no
  `importScripts`, so the earlier check was wrong); `deno/tor.test.ts` asserts it in a real
  worker. https://github.com/danbri/factoidal-core/issues/1059 is closed.
- No Tor in pages or in the Hub, so the page clock gap does not apply:
  https://github.com/danbri/factoidal-core/issues/1061 is closed as not planned. The page
  files (`pages.py`, `run.sh`, `node-ref.cjs`) are removed; the probe in `../tor-probe/` stays
  as the record of the measurement in section 8.
- The state key comes from the macOS Keychain (`security find-generic-password`, created on
  first use). Today `deno/tor-state.ts` `keySource()` says "environment"; its expected failure
  names https://github.com/danbri/factoidal-core/issues/1058.
- Coordinator's reading, not the owner's words: runs on the Linux chutney network stay as
  development checks; the test that counts is on macOS.

Plan for connecting the browser (https://github.com/danbri/factoidal-core/issues/1060):

1. The Tor worker serves SOCKS5 on 127.0.0.1, port 0. The username is the partition (the
   top-level site); the password is a secret made per session, so no other local process can
   use the port. Names are resolved by the exit (`socks5h`), never locally.
2. The wasm module gets a stream API (open, read, write, close) over Arti `DataStream`.
3. The host's network pool uses `Deno.createHttpClient({ proxy: { transport: "socks5",
   url: "socks5h://127.0.0.1:PORT", basicAuth } })`, one client per partition.
4. In Tor mode the Lean egress policy makes no local name lookup, no DNS prefetch and no name
   cache; WebSocket is refused at first (an expected failure with its own issue).
5. A new identity control in the browser calls `new_identity()` and drops the clients.

Coordination: the owner is rethinking how the macOS build uses Deno (worker count and
duplication) in another session, under
https://github.com/danbri/factoidal-core/issues/1031 (threads, tabs, processes, network). What
Tor needs from any structure: one Tor client for the whole browser (one guard set, one state
file), not one per tab; its memory apart from page scripts (a worker or a process); a long-lived
host that keeps circuits across tab changes; and the network pool able to send through a SOCKS5
proxy with a per-partition user name. The Tor worker does not need its own Deno: it can be a
worker inside whatever Deno host stays. Steps 3 to 5 wait for that design; steps 1 and 2 do not
depend on it.

## 18. Stream API, SOCKS5 server, and the NO_PROXY bypass (2026-11-26)

- Module: `stream_open(partition, host, port, timeout)`, `stream_read`, `stream_write` (writes
  and flushes), `stream_close`, `streams_open`. Each stream is split into an Arti `DataReader`
  and `DataWriter`, so one read and one write can wait at the same time; a second operation on
  the same half is refused. Errors give a class ("refused", "timeout", "tor: <Arti error
  kind>"), not Arti's full text.
- `deno/socks5.ts`: RFC 1928 CONNECT only, RFC 1929 username/password required. The user name
  is the partition (top-level site); the password is 32 random bytes per session (hex), compared
  in time that does not depend on where it differs. BIND, UDP ASSOCIATE and the "no
  authentication" method are refused. Domain names go to Tor unchanged (the exit resolves them).
  Listens on 127.0.0.1, port chosen by the system. The worker starts it on op "socks" and gives
  the port and password only to the thread that started the worker.
- Finding: Deno's fetch (2.9.8) applies `NO_PROXY` to a client with an explicit SOCKS5 proxy
  and sends listed hosts directly. The first private network run with SOCKS passed 5 of 5
  fetches while 2 of them (to 127.0.0.1) bypassed Tor: 3 ms each, and the server saw 3 streams.
  Repair: `torHttpClient` clears `NO_PROXY` and `no_proxy` before it makes a client (Deno reads
  them then), and `proxyCheck` fetches loopback (IPv4, IPv6, `localhost`), a 10/8 address and a
  `.invalid` name with the reserved user `foafnaut-proxy-check`; the server records and refuses
  those, and the host refuses to fetch through Tor if any did not arrive. `deno/socks5.test.ts`
  has a control that shows the check sees the bypass when `NO_PROXY` is in force. This is a
  start-up check only: a later change of the environment by other code in the same process is
  not seen.
- Results, private network (chutney, Linux, development check): all 9 checks PASS, including
  the start-up check and 5 Deno fetches at once through SOCKS5 (2 exit, 3 onion), all 5 seen by
  the server, exit fetches 111 and 182 ms, onion fetches 563 to 770 ms. `deno test deno/`: 11
  pass, 0 fail (out of 11; 1 expected failure each for issues 1058 and 1060 among them).
  `node --test module.test.cjs`: 5 pass, 0 fail (out of 5).
- Owner, 2026-11-26, verbatim, on the SOCKS5 secret given only to the browser's main thread:
  "make sure this is splattered with theorems of great impressiveness and robustness". The
  SOCKS5 decisions in `deno/socks5.ts` are also anti-pattern 36 (RFC decisions in TS). Plan:
  move the parse and admit/refuse decisions into Lean (`L4Factoidal/Net/Socks5.lean`), keep only
  byte I/O in TS, and prove: (a) no CONNECT is admitted unless the RFC 1929 exchange gave exactly
  the session secret, for all inputs; (b) the partition key is a function of the user name
  alone and injective; (c) every log, trace or error value is equal for two states that differ
  only in the secret; (d) the comparison reads every byte of both values (structural; not a
  proof of constant CPU time); (e) the listen address is loopback; (f) a Lean model of the
  host messages, in which the secret goes only to the thread that started the worker, with a
  test of the real TS host against it. Then a differential fuzz of the Lean decision against
  the TS code. A property is called proved only when `lake build` builds its file from a root.
- Next for https://github.com/danbri/factoidal-core/issues/1060: in Tor mode, the main-thread
  fetches of `native_html_document.ts` and `run_html.ts` use one `torHttpClient` per top-level
  site; WebSocket refused at first; new identity control; no local name lookup in the Lean
  egress policy.

## 19. Public-network failure on the owner's Mac (2026-11-26): cause open

- Run with `--trace-conns`, Tailscale reported off: 158 TCP dials, 2 opened (both completed the
  TLS and Tor handshakes, about 4.4 KB in each), 113 connect failures (about 70 TimedOut after
  the 75 s macOS connect timeout), worst event-loop lag 38 ms with no stall. `nc` to a directory
  authority on 443 timed out in the same state of the Mac.
- Correction: the message of commit e33848e6b says "The network path drops TCP to Tor relays;
  not the transport". That is not established. An OONI Probe Tor test made by another user on
  the same ISP (Hyperoptic, AS56478) at 16:59 UTC reached all 10 directory authorities
  (https://explorer.ooni.org/measurement/20261126170052.206194_GB_tor_46e6945a9999a913). It
  was not made from the owner's Mac or house network (a first reading said it was, from
  "platform macos"). It shows only that the ISP does not block Tor. A block in the house
  network (a router or firewall with security filtering) or on the laptop (a VPN or Tailscale
  route, a filter extension) is still possible. What the trace does establish: CPU work in the
  module did not block the event loop, and the connections that opened worked.
- Deciding runs: `tailscale status`, `nc`, C tor and `--trace-conns` back to back on the Mac;
  and a phone test on the house Wi-Fi against mobile data. If `nc` and C
  tor connect and our client does not, the fault is in our transport.

Update, same day, phone hotspot (giffgaff 5G), about 17:47 to 17:51 UTC, main after 1d197c7c3:

- `nc` to a directory authority on 443 succeeded; C tor 0.4.9.17 bootstrapped 100%. So the
  earlier failures came from the house network (or the laptop's state on it), which drops TCP
  to Tor relays: `nc` timed out there with Tailscale off and succeeds on the hotspot.
- Ours: bootstrap ok in about 6 s. First public onion service fetch: the Tor Project onion site
  answered "HTTP/1.1 200 OK" (2048 bytes) through partition `b`. Worst event-loop lag 322 ms,
  no stall.
- Open defect: the exit request (example.com:80) timed out after 180 s. Over the run, 5 of 9 new
  connections opened, sent bytes and got no bytes back. The native client has no such failures
  on the same network.
- Trace after this run: per connection, the size and time of the first write (the TLS
  ClientHello: 239 to 247 bytes on the private network), the write count, end of stream from the
  peer, read errors with their text, and summary counts `noReplyThenPeerClosed` and
  `noReplyClosedByArti`. A connection with bytes sent and none received stopped in the TLS
  handshake (no ServerHello), before the Tor link handshake (VERSIONS, CERTS). rustls has TLS
  1.2 and 1.3 enabled (`tls12` feature on).
