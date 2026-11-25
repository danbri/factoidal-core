#!/usr/bin/env bash
# Build the Tor component probe: Arti 0.48.0 crates to wasm32-unknown-unknown, then
# wasm-bindgen glue, then the two test pages. Output in .build/ (not committed).
# Needs: rustup target wasm32-unknown-unknown; wasm-bindgen-cli 0.2.130
#   (cargo install wasm-bindgen-cli --version 0.2.130).
# Record: docs/designissues/2026-11-25-foafnaut-tor-onion-routing.md, section 8.
set -euo pipefail
cd "$(dirname "$0")"
cargo fetch --target wasm32-unknown-unknown >/dev/null 2>&1 || true   # registry sources for the copy below
REG=$(ls -d "${CARGO_HOME:-$HOME/.cargo}"/registry/src/*/ | head -1)
mkdir -p .work .build
# saturating-time 0.6.0 names std::time::Instant on wasm32-unknown-unknown, where its
# web-time-compat layer gives web_time::Instant. Local patch only (CLAUDE.md, never report upstream).
if [[ ! -f .work/saturating-time-0.6.0/.patched ]]; then
  rm -rf .work/saturating-time-0.6.0
  cp -r "$REG/saturating-time-0.6.0" .work/
  patch -s -d .work/saturating-time-0.6.0 -p1 < saturating-time-0.6.0-wasm.patch
  touch .work/saturating-time-0.6.0/.patched
fi
# Arti's own test consensus (6 relays, MIT OR Apache-2.0), read from the crate, not vendored.
cp "$REG/tor-netdoc-0.48.0/testdata/mdconsensus1.txt" .work/
cargo build --release --target wasm32-unknown-unknown
wasm-bindgen --target no-modules --no-typescript --out-dir .build \
  target/wasm32-unknown-unknown/release/torprobe.wasm
python3 pages.py .build
ls -l .build
