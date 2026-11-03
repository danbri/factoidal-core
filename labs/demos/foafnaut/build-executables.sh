#!/usr/bin/env bash
# macOS ARM64 release directory. No binary or runtime cache belongs in git.
set -euo pipefail
LAB=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$LAB/../../.." && pwd)
PROJECT="$REPO/formal/lean4"
. "$LAB/toolchain-versions.env"
if [ "$(uname -s)" != Darwin ] || [ "$(uname -m)" != arm64 ]; then
  echo 'Native Cocoa packaging currently requires macOS ARM64' >&2; exit 2
fi
[ "$(deno --version | sed -n '1s/^deno \([^ ]*\).*/\1/p')" = "$DENO_VERSION" ] || { echo "Use Deno $DENO_VERSION" >&2; exit 1; }
OUT=${1:-$LAB/.build/dist}
mkdir -p "$OUT" "$LAB/.build/native"
OUT=$(cd "$OUT" && pwd)
# Rebuild the native proof/source closure on a clean checkout. Downloaded WASM
# engines remain untouched; no Emscripten/runtime build occurs in this step.
bash "$LAB/build-engines.sh" --source-only
bash "$LAB/test.sh" --skip-build
# The static browser SVG uses the checked Lean scene/policy backend. An
# extracted native package does not contain Lean sources or a Lean toolchain.
(
  cd "$PROJECT"
  LEAN_PATH="$LAB/.build/olean:$PROJECT/.lake/build/lib/lean" \
    lean -R "$LAB" --run "$LAB/SolvingArtifact.lean" "$OUT/Solving Showcase.svg"
)
xcrun clang -dynamiclib -fobjc-arc -O2 -Wall -Wextra -Werror -framework Cocoa -framework QuartzCore \
  -Wl,-install_name,@rpath/libnative-window.dylib "$LAB/native_window.m" -o "$OUT/libnative-window.dylib.tmp"
mv "$OUT/libnative-window.dylib.tmp" "$OUT/libnative-window.dylib"
cp "$OUT/libnative-window.dylib" "$LAB/.build/native/libnative-window.dylib"
# The owner requested no repeated FFI prompt for the native window bridge.
# UnsafeWindowSurface requires pathless FFI permission; grant it in this UI build.
# Deno compile resolves path-scoped permissions against the *build* directory.
# These binaries are relocated by release packaging, and the explicit --rdf,
# --emit-artifact and --emit-svg options accept paths in that new directory.
# Match the other two renderer CLIs: grant filesystem read/write at compile time;
# the package's relocation smoke then checks actual output paths.
cd "$OUT"
deno compile --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
  --allow-read --allow-write --allow-run=/usr/bin/open --allow-ffi \
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
# The browser uses the same checked scene exporter and policy module. This is
# a static site directory, not another executable or a separate implementation.
mkdir -p "$OUT/web/.build/engines" "$OUT/web/foaf/fixtures"
cp "$LAB/"{policy-demo.html,policy-demo.mjs,policy_engine.mjs,foafnaut_transport.mjs} "$OUT/web/"
cp "$LAB/.build/engines/"{foafnaut-engine,layout-policy-engine}.{mjs,wasm} "$OUT/web/.build/engines/"
cp "$LAB/foaf/fixtures/people.ttl" "$OUT/web/foaf/fixtures/"
for doc in README.md SVG_README.md; do [ ! -f "$LAB/$doc" ] || cp "$LAB/$doc" "$OUT/$doc"; done
cp "$LAB/.build/source-SHA256SUMS" "$LAB/.build/tool-versions.txt" "$LAB/.build/runtime-object-witness.txt" "$OUT/"
(
  cd "$REPO"
  shasum -a 256 labs/demos/foafnaut/{Solving.command,build-executables.sh}
) >> "$OUT/source-SHA256SUMS"
chmod +x "$OUT/"*.command "$OUT/run-demo.sh"
# Exercise an extracted launcher from a relocated directory with spaces and
# no Lean executable on PATH. The stub records the exact browser-open path.
CHECK=$(mktemp -d "${TMPDIR:-/tmp}/foafnaut-package-check.XXXXXXXX")
CHECK=$(cd "$CHECK" && pwd)
trap 'rm -rf "$CHECK"' EXIT
mkdir -p "$CHECK/package with spaces" "$CHECK/bin"
cp "$OUT/Solving.command" "$OUT/Solving Showcase.svg" "$CHECK/package with spaces/"
cat > "$CHECK/bin/open" <<'EOF'
#!/bin/bash
printf '%s\n' "$@" > "$FOAFNAUT_OPEN_LOG"
EOF
chmod +x "$CHECK/bin/open"
(
  export PATH="$CHECK/bin:/usr/bin:/bin"
  export FOAFNAUT_OPEN_LOG="$CHECK/opened"
  if command -v lean >/dev/null; then echo 'Package probe requires PATH without Lean' >&2; exit 1; fi
  /bin/bash "$CHECK/package with spaces/Solving.command"
)
printf '%s\n' "$CHECK/package with spaces/Solving Showcase.svg" > "$CHECK/expected"
cmp "$CHECK/expected" "$CHECK/opened"
echo 'Solving static browser SVG launcher passed relocation with spaces and no Lean'
rm -rf "$CHECK"
trap - EXIT
shasum -a 256 native-webgpu-ui-darwin-arm64 native-webgpu-lean-darwin-arm64 \
  native-webgpu-svg-darwin-arm64 libnative-window.dylib 'Solving Showcase.svg' \
  source-SHA256SUMS tool-versions.txt runtime-object-witness.txt > "$OUT/SHA256SUMS"
echo "Foafnaut native release directory: $OUT"
