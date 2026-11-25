#!/usr/bin/env bash
# Build Arti 2.8.0 (the Tor Project's Rust Tor client, latest stable release) for
# wasm32-unknown-unknown with a minimal runtime (src/lib.rs), then the wasm-bindgen glue and the
# test page. Output in .build/ (not committed).
# Needs: rustup target wasm32-unknown-unknown; wasm-bindgen-cli 0.2.130.
# Record: docs/designissues/2026-11-25-foafnaut-tor-onion-routing.md, section 10.
set -euo pipefail
cd "$(dirname "$0")"
TAG=arti-v2.8.0
COMMIT=7c038125baef924a4bf287429c192c5af606f79c
mkdir -p .work .build
if [[ ! -f .work/arti/.patched ]]; then
  rm -rf .work/arti
  git clone -q --depth 1 --branch "$TAG" https://gitlab.torproject.org/tpo/core/arti.git .work/arti
  got=$(git -C .work/arti rev-parse HEAD)
  [[ "$got" == "$COMMIT" ]] || { echo "build.sh: $TAG is $got, expected $COMMIT" >&2; exit 1; }
  git -C .work/arti apply --whitespace=nowarn "$PWD/arti-2.8.0-wasm.patch"
  touch .work/arti/.patched
fi
cargo build --release --target wasm32-unknown-unknown
# Two glue files: no-modules for the Foafnaut page, web (ES module) for the Deno worker.
wasm-bindgen --target no-modules --no-typescript --out-dir .build \
  target/wasm32-unknown-unknown/release/foafnaut_tor_wasm.wasm
wasm-bindgen --target web --no-typescript --out-dir .build/web \
  target/wasm32-unknown-unknown/release/foafnaut_tor_wasm.wasm
python3 pages.py .build "${TIMEOUT_MS:-15000}"
ls -l .build
