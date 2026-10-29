#!/usr/bin/env bash
# driver-static/build.sh — strategy 3: wasm-ld links the Rust driver (a
# staticlib), the Lean subset, the Lean runtime and wasi-libc into one
# wasm32-wasip1 command module. Reuses the wasip1 -O3 objects of ../build.sh
# (run `TARGET=wasip1 ../build.sh` first). Output: $WORK/out/static/fx-static.wasm
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WASI_SDK="${WASI_SDK:-/opt/tc/wasi-sdk-30.0-x86_64-linux}"; WORK="${WORK:-/opt/wc}"
KEY="$(printf '%s|%s|%s' wasip1 -O3 "" | sha256sum | cut -c1-12)"; OBJ="$WORK/obj-$KEY"
[ -s "$OBJ/libfx.a" ] || { echo "no wasip1 objects at $OBJ: run TARGET=wasip1 ../build.sh"; exit 1; }
OUT="$WORK/out/static"; mkdir -p "$OUT"
CC="$WASI_SDK/bin/clang --target=wasm32-wasip1 --sysroot=$WASI_SDK/share/wasi-sysroot"
(cd "$HERE" && cargo build --release --target wasm32-wasip1 -q)
$CC -O3 -DNDEBUG -I "$WORK/inc" -I "$WORK/lean4-src/src/include" -I "$HERE/../runtime-wasi/shim" \
    -c "$HERE/../baseline-emcc/fx_emcc.c" -o "$OUT/fx_cabi.o"
$CC -O3 -c "$HERE/main.c" -o "$OUT/main.o"
"$WASI_SDK/bin/clang++" --target=wasm32-wasip1 --sysroot="$WASI_SDK/share/wasi-sysroot" -O3 \
    -Wl,--strip-debug -Wl,-z,stack-size=8388608 \
    "$OUT/main.o" "$OUT/fx_cabi.o" "$HERE/target/wasm32-wasip1/release/libfx_driver_static.a" \
    "$OBJ/libfx.a" "$OBJ/libleaninit.a" "$OBJ/libleanrt.a" \
    -lwasi-emulated-signal -lwasi-emulated-process-clocks -lwasi-emulated-mman -lwasi-emulated-getpid \
    -o "$OUT/fx-static.raw.wasm" 2> "$OUT/link.stderr" || { cat "$OUT/link.stderr"; exit 1; }
wasm-opt -O3 --strip-debug --strip-producers --enable-bulk-memory --enable-nontrapping-float-to-int \
    --enable-sign-ext --enable-mutable-globals "$OUT/fx-static.raw.wasm" -o "$OUT/fx-static.wasm"
echo "  $OUT/fx-static.wasm: $(wc -c < "$OUT/fx-static.wasm") bytes"
