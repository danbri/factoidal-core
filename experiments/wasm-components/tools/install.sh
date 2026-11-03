#!/usr/bin/env bash
# install.sh — fetch the pinned toolchains for the wasm component experiments
# (https://github.com/danbri/factoidal/issues/1167, milestone 1) into $WC_TOOLS
# (default /opt/wc). Nothing here touches the shipped build.
set -euo pipefail
WC_TOOLS="${WC_TOOLS:-/opt/wc}"
WASI_SDK=34; WASMTIME=49.0.0; WASM_TOOLS=1.239.0; WIT_BINDGEN=0.45.0; WAC=0.8.0
JCO=1.38.0          # npm @bytecodealliance/jco
EMSDK=6.0.8         # the version of the shipped build (skills/lean4-wasm-export)
mkdir -p "$WC_TOOLS/bin"; cd "$WC_TOOLS"
gh=https://github.com
[ -x wasi-sdk/bin/clang ] || { curl -fsSL "$gh/WebAssembly/wasi-sdk/releases/download/wasi-sdk-$WASI_SDK/wasi-sdk-$WASI_SDK.0-x86_64-linux.tar.gz" | tar xz && mv "wasi-sdk-$WASI_SDK.0-x86_64-linux" wasi-sdk; }
[ -x bin/wasmtime ] || { curl -fsSL "$gh/bytecodealliance/wasmtime/releases/download/v$WASMTIME/wasmtime-v$WASMTIME-x86_64-linux.tar.xz" | tar xJ && cp "wasmtime-v$WASMTIME-x86_64-linux/wasmtime" bin/; }
[ -x bin/wasm-tools ] || { curl -fsSL "$gh/bytecodealliance/wasm-tools/releases/download/v$WASM_TOOLS/wasm-tools-$WASM_TOOLS-x86_64-linux.tar.gz" | tar xz && cp "wasm-tools-$WASM_TOOLS-x86_64-linux/wasm-tools" bin/; }
[ -x bin/wit-bindgen ] || { curl -fsSL "$gh/bytecodealliance/wit-bindgen/releases/download/v$WIT_BINDGEN/wit-bindgen-$WIT_BINDGEN-x86_64-linux.tar.gz" | tar xz && cp "wit-bindgen-$WIT_BINDGEN-x86_64-linux/wit-bindgen" bin/; }
[ -x bin/wac ] || { curl -fsSL -o bin/wac "$gh/bytecodealliance/wac/releases/download/v$WAC/wac-cli-x86_64-unknown-linux-musl" && chmod +x bin/wac; }
[ -s wasi_snapshot_preview1.reactor.wasm ] || curl -fsSL -o wasi_snapshot_preview1.reactor.wasm "$gh/bytecodealliance/wasmtime/releases/download/v$WASMTIME/wasi_snapshot_preview1.reactor.wasm"
[ -x node_modules/.bin/jco ] || npm install --silent --prefix "$WC_TOOLS" "@bytecodealliance/jco@$JCO" >/dev/null
[ -d emsdk ] || git clone -q --depth 1 https://github.com/emscripten-core/emsdk emsdk
( cd emsdk && ./emsdk install "$EMSDK" >/dev/null && ./emsdk activate "$EMSDK" >/dev/null )
rustup target add wasm32-wasip1 wasm32-wasip2 >/dev/null
for t in wasi-sdk/bin/clang bin/wasmtime bin/wasm-tools bin/wit-bindgen bin/wac node_modules/.bin/jco; do
  printf '%-28s %s\n' "$t" "$("$WC_TOOLS/$t" --version 2>&1 | head -1)"
done
