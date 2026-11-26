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
# ring (rustls) compiles C for wasm32. Apple's clang has no wasm32 target, so on macOS use
# Homebrew's LLVM (brew install llvm) unless CC_wasm32_unknown_unknown is already set.
if [[ "$(uname)" == Darwin && -z "${CC_wasm32_unknown_unknown:-}" ]]; then
  llvm=""
  for d in "$(brew --prefix llvm 2>/dev/null || true)" /opt/homebrew/opt/llvm /usr/local/opt/llvm; do
    [[ -n "$d" && -x "$d/bin/clang" ]] && { llvm=$d; break; }
  done
  [[ -n "$llvm" ]] || { echo "build.sh: Apple clang cannot build C for wasm32 (ring). Run: brew install llvm" >&2; exit 1; }
  export CC_wasm32_unknown_unknown="$llvm/bin/clang" AR_wasm32_unknown_unknown="$llvm/bin/llvm-ar"
  echo "build.sh: C for wasm32 with $CC_wasm32_unknown_unknown"
fi
cargo build --release --target wasm32-unknown-unknown
# Two glue files: no-modules for the Foafnaut page, web (ES module) for the Deno worker.
wasm-bindgen --target no-modules --no-typescript --out-dir .build \
  target/wasm32-unknown-unknown/release/foafnaut_tor_wasm.wasm
wasm-bindgen --target web --no-typescript --out-dir .build/web \
  target/wasm32-unknown-unknown/release/foafnaut_tor_wasm.wasm
ls -l .build
