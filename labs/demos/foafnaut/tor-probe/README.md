# Tor component probe

Parts of Arti 0.48.0 (the Tor Project's Rust client) that need no network, built to WebAssembly
and run in a Foafnaut page on the built-in engines: BubblePopWASM runs the module, BubblePopJS
runs the page script. It is a measurement, not a Tor client, and not a secure path.

Steps in `src/lib.rs`: onion v3 address parsing (SHA3-256 checksum) and key blinding for the
current time period; microdescriptor consensus parsing (Arti's 6-relay test document); x25519
key agreement; relay cell crypto through 3 hops (AES-128-CTR).

Results, findings and the method: `docs/designissues/2026-11-25-foafnaut-tor-onion-routing.md`,
section 8.

## Run

```sh
rustup target add wasm32-unknown-unknown
cargo install wasm-bindgen-cli --version 0.2.130
bash tools/foafnaut-linux-rig/setup.sh          # from the repository root; Linux, once
labs/demos/foafnaut/tor-probe/build.sh
labs/demos/foafnaut/tor-probe/run.sh tor-probe.html   # each step once, with its result
labs/demos/foafnaut/tor-probe/run.sh tor-split.html   # three loads, real time of each
```

`run.sh` prints the page lines and, for each page task, the host's instruction count and real
engine time (`leanMs`). The `ms` values inside the page lines are virtual: Foafnaut's page clock
moves 1 ms per 100,000 instructions (`Page.lean`, "The script clock"). Use `leanMs`.

The reference is the same module in Node (`.build/torprobe.js` with `wasm_bindgen.initSync`).

## Local patch

`saturating-time-0.6.0-wasm.patch`: `saturating-time` 0.6.0 does not compile for
`wasm32-unknown-unknown` (it names `std::time::Instant` where `web-time-compat` gives
`web_time::Instant`). `build.sh` copies the crate to `.work/` and patches it there. Not reported
upstream (CLAUDE.md, "Never report upstream").

Outputs (`target/`, `.work/`, `.build/`) are not committed.
