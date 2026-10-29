#!/usr/bin/env bash
# Build every variant of the measurements table in RESULTS.md. Each line is
# one build; a failure is logged and the next variant still builds.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LOG="${LOG_DIR:-/opt/wc/logs}"; mkdir -p "$LOG"
v() { local name="$1"; shift
  if env "$@" bash "$HERE/build.sh" > "$LOG/$name.log" 2>&1; then echo "BUILT $name"; else echo "FAILED $name (log $LOG/$name.log)"; fi; }
v p2      TARGET=wasip2 VARIANT=p2
v p2-opt  TARGET=wasip2 VARIANT=p2-opt WASM_OPT=-O3
v p1-opt  TARGET=wasip1 VARIANT=p1-opt WASM_OPT=-O3
v p2-oz   TARGET=wasip2 VARIANT=p2-oz OPT=-Oz WASM_OPT=-Oz
v p2-tail TARGET=wasip2 VARIANT=p2-tail XFLAGS=-mtail-call WASM_OPT=-O3 WASM_OPT_FEATURES=--enable-tail-call
v p2-simd TARGET=wasip2 VARIANT=p2-simd XFLAGS=-msimd128 WASM_OPT=-O3 WASM_OPT_FEATURES=--enable-simd
v p2-eh   TARGET=wasip2 VARIANT=p2-eh XFLAGS=-fwasm-exceptions WASM_OPT=-O3 WASM_OPT_FEATURES=--enable-exception-handling
source /opt/emsdk/emsdk_env.sh >/dev/null 2>&1
if bash "$HERE/baseline-emcc/build.sh" > "$LOG/emcc.log" 2>&1; then echo "BUILT emcc"; else echo "FAILED emcc"; fi
