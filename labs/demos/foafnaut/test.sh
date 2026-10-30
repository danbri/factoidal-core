#!/usr/bin/env bash
set -euo pipefail
LAB=$(cd "$(dirname "$0")" && pwd)
. "$LAB/toolchain-versions.env"
[ "$(deno --version | sed -n '1s/^deno \([^ ]*\).*/\1/p')" = "$DENO_VERSION" ] || { echo "Use Deno $DENO_VERSION" >&2; exit 1; }
SKIP=0
BUILD_ARGS=()
while [ $# -gt 0 ]; do
  case "$1" in
    --skip-build) SKIP=1; shift ;;
    --runtime-cache) BUILD_ARGS+=(--runtime-cache "${2:?missing runtime cache}"); shift 2 ;;
    *) echo "usage: $0 [--skip-build] [--runtime-cache DIR]" >&2; exit 2 ;;
  esac
done
if [ "$SKIP" = 0 ]; then bash "$LAB/build-engines.sh" "${BUILD_ARGS[@]}"; fi
mkdir -p "$LAB/.build"
"${CC:-cc}" -std=c11 -O2 -Wall -Wextra -Werror "$LAB/native_coordinates_test.c" \
  -lm -o "$LAB/.build/native-coordinates-test"
"$LAB/.build/native-coordinates-test"
deno check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
  "$LAB/run_ui.ts" "$LAB/run_lean.ts" "$LAB/run_svg.ts" "$LAB/"*_test.ts
deno test --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --allow-read "$LAB/"*_test.ts
