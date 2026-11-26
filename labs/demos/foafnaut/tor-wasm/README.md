# Arti (Tor) for wasm, run in Foafnaut

Arti 2.8.0, the Tor Project's Rust Tor client (latest stable release, tag `arti-v2.8.0`,
commit `7c038125baef924a4bf287429c192c5af606f79c`), built for `wasm32-unknown-unknown` and run
in a dedicated Deno worker of the Foafnaut desktop host. Owner, 2026-11-26: Tor is for the
desktop browser on macOS; not in the Hub and not inside pages (record section 17).

With no host transport it fails closed: every connection is refused. In the Deno worker
(`deno/`) it has a transport: TCP through `Deno.connect`
and TLS inside the module. There it bootstraps on a private Tor network and reaches an exit and
an onion service (`chutney/run.sh`), with one circuit set per partition (top-level site), a
new identity operation, and state kept in a sealed local LWS storage (`deno/tor-state.ts`).

EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS
WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW. The transport is not trusted for real users: it runs
only after the caller passes `--dangerously-use-unreviewed-tor-transport`. The full
record (build, every change to Arti, measurements, security review, open risks):
`docs/designissues/2026-11-25-foafnaut-tor-onion-routing.md`, section 10.

## Files

- `build.sh` (on macOS it needs `brew install llvm`: Apple clang has no wasm32 target, and ring compiles C): clone the tag, check its commit, apply `arti-2.8.0-wasm.patch`, build, generate
  the wasm-bindgen glue and the test page into `.build/`.
- `arti-2.8.0-wasm.patch`: the changes to Arti (all wasm-only; see the record, 10.2 and 12.2).
- `src/lib.rs`: the wasm runtime for Arti and the exported functions.
- `module.test.cjs`: checks of the module in Node: it fails closed with no host transport, the
  opt-in needs the exact string, no debug lines by default, state out and back.
- `deno/tor.test.ts`: the module runs in a dedicated Deno worker; expected failures for
  https://github.com/danbri/factoidal-core/issues/1058 (key from the macOS Keychain) and
  https://github.com/danbri/factoidal-core/issues/1060 (Foafnaut sends pages through Tor).
- `deno/tor-worker.ts`: Deno worker that runs the module and gives it TCP (IP literals only).
- `deno/tor-host.ts`: starts the worker with narrow permissions; bootstrap and stream requests.
- `chutney/network`, `chutney/run.sh`: a private Tor network (C tor) and the end-to-end test.

## Run

```sh
rustup target add wasm32-unknown-unknown
cargo install wasm-bindgen-cli --version 0.2.130
bash tools/foafnaut-linux-rig/setup.sh                 # from the repository root, Linux, once
labs/demos/foafnaut/tor-wasm/build.sh
node --test labs/demos/foafnaut/tor-wasm/module.test.cjs
deno test --unstable-worker-options --allow-read --allow-net labs/demos/foafnaut/tor-wasm/deno/
apt-get install -y tor                                  # private network nodes
python3 -m pip install git+https://gitlab.torproject.org/tpo/core/chutney.git
labs/demos/foafnaut/tor-wasm/chutney/run.sh            # end-to-end, no public traffic
```

## Open gaps (each has an expected-failure test)

- https://github.com/danbri/factoidal-core/issues/1060 (Foafnaut does not yet send page
  requests through Tor; the Deno worker transport is unreviewed)
- https://github.com/danbri/factoidal-core/issues/1058 (the state key comes from the
  environment; it must come from the macOS Keychain)

Closed: https://github.com/danbri/factoidal-core/issues/1059 (the module runs in a dedicated
worker, tested) and https://github.com/danbri/factoidal-core/issues/1061 (page clock: not
planned, Tor does not run in pages).
