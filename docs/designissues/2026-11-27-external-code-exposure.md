# External code each path depends on (2026-11-27)

Owner, 2026-11-27, verbatim: "we don't want to be too tied to any of these, and the exposure to
external code needs to be clear and documented". Earlier the same day: "Seeing some use node, some
use deno, feels off." Plan: https://github.com/danbri/factoidal-core/issues/1176.

This record lists the code that is not ours (not Lean in `formal/lean4`, not our own host
adapters) on each path that moves bytes over a network, does TLS or does cryptography, with the
version measured on 2026-11-27 and what that code decides. Method: read of the host entry
points, `package.json`, `Cargo.lock`, `third_party/*/PROVENANCE.md` and the Deno v2.9.8 sources.
Limit: it is a first version. It covers network, TLS, crypto and the runtimes. It does not yet
cover parsers, media decoders, fonts or build tools; add them as rows when their paths are
audited, and treat any path missing here as not yet audited, not as having no exposure.

## Runtimes

| Runtime | Version measured | Its own TLS and crypto | Where we use it |
| --- | --- | --- | --- |
| Node | 22.23.5 (package floor `>=22.12`) | OpenSSL 3.5.9, V8 12.4 | `npx factoidal`, npm servers (LWS, Solid, WebDAV, authz, XMPP), npm tests, Ethereum RPC capture |
| Deno | 2.9.8 | rustls 0.23.40 with aws-lc-rs, Mozilla roots by default (`DENO_TLS_CA_STORE=system` for the OS store), V8 15.0 | Foafnaut desktop host, Tor worker, single-file executables |
| Browsers | any the user has | their own | npm `browser.js` entry, Hub pages |

Owner decisions: one host runtime (Deno) for what we run; `npx factoidal` keeps running under Node
("keep running - yes pls"); the npm library keeps working in Node and browsers. Code reaches a
runtime only through small adapters (pattern: `npm/factoidal/store-host/node.mjs` and `deno.mjs`,
which move bytes and decide nothing).

## Network and TLS paths

| Path | External code that does the work | What that code decides | What Lean decides |
| --- | --- | --- | --- |
| Foafnaut page loads (`native_html_document.ts`) | Deno `fetch`: hyper, rustls, aws-lc-rs, webpki | TLS versions and suites, certificate trust, HTTP framing, redirects below our policy | Which requests are allowed (`Net/PageFetch.lean`, `Net/Egress.lean`) |
| Foafnaut `wss:` (`native_net.ts`) | `Deno.connect`, `Deno.startTls` | As above for TLS | WebSocket rules (`Net/WebSocket.lean`) |
| Tor (`labs/demos/foafnaut/tor-wasm`) | Arti 2.8.0 and its 500 locked Rust packages (`Cargo.lock`), rustls 0.23 with ring, in our wasm module; Deno gives TCP only | The Tor protocol, path selection, relay crypto, directory checks | SOCKS5 admission (`Net/Socks5.lean`, 29 theorems) |
| npm servers and XMPP | Node `http`, `net`, `tls` (OpenSSL 3.5.9) | TLS and HTTP framing | Protocol state machines (LWS, Solid, WebDAV, XMPP STARTTLS) |
| Ethereum RPC capture (`evm-cleanroom/scripts/rpc`) | Node `https` (OpenSSL) | TLS, HTTP | Nothing in transport; Lean checks the saved replies |

## Cryptography

| Use | Source | Version or pin |
| --- | --- | --- |
| Native hashes, signatures, AEAD, KDF, HPKE (`formal/lean4/ffi/hacl_*.c`) | HACL\* (F\*-verified C, Vale assembly for AES-GCM on x86-64) | commit `f557259007db9933442dde10aa995c1b00bd3446` (`third_party/hacl/PROVENANCE.md`) |
| Wasm hashes and Ed25519 (`third_party/hacl-wasm`) | HACL\* official wasm build | version in `third_party/hacl-wasm/PROVENANCE.md` |
| AES, PBKDF2 on JavaScript hosts (`npm/factoidal/lib/cipher-host.mjs`) | the host's WebCrypto (`globalThis.crypto.subtle`): OpenSSL in Node, aws-lc in Deno, the browser's own | per runtime above |
| Tor relay crypto | ring, curve25519-dalek, aes and others from `Cargo.lock` | locked versions |

## Rules for keeping this true

- A change that adds a runtime call, a crate, an npm dependency or a vendored library adds or
  updates a row here in the same landing.
- A row says what the external code decides. When it decides a protocol or format question that
  Lean could decide, that is a candidate to move into Lean (iron rule 7), with an issue.
- Versions are measured, never copied from memory; each update gives the command or file read.
