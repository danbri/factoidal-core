#!/usr/bin/env bash
# macOS ARM64 release directory. No binary or runtime cache belongs in git.
set -euo pipefail
LAB=$(cd "$(dirname "$0")" && pwd)
. "$LAB/toolchain-versions.env"
if [ "$(uname -s)" != Darwin ] || [ "$(uname -m)" != arm64 ]; then
  echo 'Native Cocoa packaging currently requires macOS ARM64' >&2; exit 2
fi
[ "$(deno --version | sed -n '1s/^deno \([^ ]*\).*/\1/p')" = "$DENO_VERSION" ] || { echo "Use Deno $DENO_VERSION" >&2; exit 1; }
OUT=${1:-$LAB/.build/dist}
mkdir -p "$OUT" "$LAB/.build/native"
OUT=$(cd "$OUT" && pwd)
bash "$LAB/test.sh" --skip-build
xcrun clang -dynamiclib -fobjc-arc -O2 -Wall -Wextra -Werror -framework Cocoa -framework QuartzCore \
  -Wl,-install_name,@rpath/libnative-window.dylib "$LAB/native_window.m" -o "$OUT/libnative-window.dylib.tmp"
mv "$OUT/libnative-window.dylib.tmp" "$OUT/libnative-window.dylib"
cp "$OUT/libnative-window.dylib" "$LAB/.build/native/libnative-window.dylib"
# The owner requested no repeated FFI prompt for the native window bridge.
# UnsafeWindowSurface requires pathless FFI permission; grant it in this UI build.
# Launchers still cd to OUT for relative read/write permissions and fixtures.
cd "$OUT"
deno compile --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
  --allow-read=. --allow-write=. --allow-run=/usr/bin/open --allow-ffi \
  --include "$LAB/.build/engines/ui-engine.wasm" --include "$LAB/.build/engines/demos-engine.wasm" \
  --include "$LAB/.build/engines/render-plan.wasm" \
  --include "$LAB/.build/engines/foafnaut-engine.wasm" --include "$LAB/foaf/fixtures/demo.ttl" \
  --output "$OUT/native-webgpu-ui-darwin-arm64.tmp" "$LAB/run_ui.ts"
mv "$OUT/native-webgpu-ui-darwin-arm64.tmp" "$OUT/native-webgpu-ui-darwin-arm64"
deno compile --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu \
  --allow-read --allow-write --allow-run=/usr/bin/open \
  --include "$LAB/.build/engines/graphics-generator.wasm" \
  --include "$LAB/.build/engines/render-plan.wasm" \
  --output "$OUT/native-webgpu-lean-darwin-arm64.tmp" "$LAB/run_lean.ts"
mv "$OUT/native-webgpu-lean-darwin-arm64.tmp" "$OUT/native-webgpu-lean-darwin-arm64"
deno compile --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu \
  --allow-read --allow-write --allow-run=/usr/bin/open \
  --include "$LAB/.build/engines/svg-engine.wasm" \
  --include "$LAB/.build/engines/render-plan.wasm" \
  --output "$OUT/native-webgpu-svg-darwin-arm64.tmp" "$LAB/run_svg.ts"
mv "$OUT/native-webgpu-svg-darwin-arm64.tmp" "$OUT/native-webgpu-svg-darwin-arm64"
cp "$LAB/"*.command "$LAB/run-demo.sh" "$LAB/summarize-input.py" "$OUT/"
cp -R "$LAB/svg-fixtures" "$OUT/"
mkdir -p "$OUT/foaf-fixtures"
cp "$LAB/foaf/fixtures/"*.ttl "$OUT/foaf-fixtures/"
for doc in README.md SVG_README.md; do [ ! -f "$LAB/$doc" ] || cp "$LAB/$doc" "$OUT/$doc"; done
cp "$LAB/.build/source-SHA256SUMS" "$LAB/.build/tool-versions.txt" "$OUT/"
chmod +x "$OUT/"*.command "$OUT/run-demo.sh"
shasum -a 256 native-webgpu-ui-darwin-arm64 native-webgpu-lean-darwin-arm64 \
  native-webgpu-svg-darwin-arm64 libnative-window.dylib > "$OUT/SHA256SUMS"
echo "Foafnaut native release directory: $OUT"
