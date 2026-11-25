# Arti (Tor) for wasm, run in Foafnaut

Arti 2.8.0, the Tor Project's Rust Tor client (latest stable release, tag `arti-v2.8.0`,
commit `7c038125baef924a4bf287429c192c5af606f79c`), built for `wasm32-unknown-unknown` and run
in a Foafnaut page on the built-in engines (BubblePopWASM runs the module, BubblePopJS the page).

It is not a working Tor client yet: it has no network transport, so it starts, looks for a
consensus, and every connection is refused. It is not a secure path for real use. The full
record (build, every change to Arti, measurements, security review, open risks):
`docs/designissues/2026-11-25-foafnaut-tor-onion-routing.md`, section 10.

## Files

- `build.sh`: clone the tag, check its commit, apply `arti-2.8.0-wasm.patch`, build, generate
  the wasm-bindgen glue and the test page into `.build/`.
- `arti-2.8.0-wasm.patch`: the changes to Arti (three, all wasm-only; see the record).
- `src/lib.rs`: the wasm runtime for Arti and the exported functions.
- `pages.py`: writes `tor-bootstrap.html` (gives the page clock the real time; see the record).
- `run.sh`: runs the page in Foafnaut on the Linux rig and prints Arti's lines and the timing.
- `node-ref.cjs`: the same module in Node, for comparison.
- `xfail.test.cjs`: expected failures, one per open gap, plus a check that every connection
  is refused.

## Run

```sh
rustup target add wasm32-unknown-unknown
cargo install wasm-bindgen-cli --version 0.2.130
bash tools/foafnaut-linux-rig/setup.sh                 # from the repository root, Linux, once
labs/demos/foafnaut/tor-wasm/build.sh
node --test labs/demos/foafnaut/tor-wasm/xfail.test.cjs
labs/demos/foafnaut/tor-wasm/run.sh
```

## Open gaps (each has an expected-failure test)

- https://github.com/danbri/factoidal-core/issues/1060 (no network transport)
- https://github.com/danbri/factoidal-core/issues/1061 (page clock is virtual)
- https://github.com/danbri/factoidal-core/issues/1058 (state only in memory: guard churn)
- https://github.com/danbri/factoidal-core/issues/1059 (shares the page's script context)
