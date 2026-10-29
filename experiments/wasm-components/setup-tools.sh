#!/usr/bin/env bash
# Install the pinned tools of the wasm component experiments into /opt/tc
# (release binaries from GitHub) and jco into /opt/jco (npm). Measured on
# 2026-10-28 in a 4-vCPU Linux x86_64 container: about 3 minutes.
set -euo pipefail
T="${TC_DIR:-/opt/tc}"; mkdir -p "$T/bin"; cd "$T"
gh_dl() { curl -sSfL -o "$2" "https://github.com/$1"; }
[ -d wasi-sdk-30.0-x86_64-linux ] || { gh_dl WebAssembly/wasi-sdk/releases/download/wasi-sdk-30/wasi-sdk-30.0-x86_64-linux.tar.gz wasi-sdk.tgz; tar xzf wasi-sdk.tgz; }
[ -x bin/wasmtime ] || { gh_dl bytecodealliance/wasmtime/releases/download/v37.0.0/wasmtime-v37.0.0-x86_64-linux.tar.xz wt.txz; tar xJf wt.txz; cp wasmtime-v37.0.0-x86_64-linux/wasmtime bin/; }
[ -x bin/wasm-tools ] || { gh_dl bytecodealliance/wasm-tools/releases/download/v1.240.0/wasm-tools-1.240.0-x86_64-linux.tar.gz wt.tgz; tar xzf wt.tgz; cp wasm-tools-1.240.0-x86_64-linux/wasm-tools bin/; }
[ -x bin/wit-bindgen ] || { gh_dl bytecodealliance/wit-bindgen/releases/download/v0.46.0/wit-bindgen-0.46.0-x86_64-linux.tar.gz wb.tgz; tar xzf wb.tgz; cp wit-bindgen-0.46.0-x86_64-linux/wit-bindgen bin/; }
[ -x bin/wac ] || { gh_dl bytecodealliance/wac/releases/download/v0.8.0/wac-cli-x86_64-unknown-linux-musl bin/wac; chmod +x bin/wac; }
mkdir -p "${WORK:-/opt/wc}"
[ -s "${WORK:-/opt/wc}/wasi_snapshot_preview1.reactor.wasm" ] || gh_dl bytecodealliance/wasmtime/releases/download/v37.0.0/wasi_snapshot_preview1.reactor.wasm "${WORK:-/opt/wc}/wasi_snapshot_preview1.reactor.wasm"
rustup target add wasm32-wasip1 wasm32-wasip2
mkdir -p /opt/jco && cd /opt/jco && { [ -f package.json ] || npm init -y >/dev/null; } && npm install @bytecodealliance/jco@1.40.0 @bytecodealliance/preview2-shim
# libuv headers come from a libuv v1.48.0 clone in build.sh step 1.
for b in "$T"/bin/*; do "$b" --version; done
