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
# Launchers still cd to OUT for relative read/write permissions and fixtures.
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
# The native HTML window. Builds supplies the checked web-render engine; a local
# package with no engine has no window program, and says so.
if [ -f "$LAB/.build/web-render/engines/web-render.wasm" ]; then
  mkdir -p "$LAB/.build/native-html/runtime"
  cp "$LAB/.build/web-render/engines/web-render."{mjs,wasm} "$LAB/.build/native-html/runtime/"
  deno compile --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
    --allow-read --allow-net --allow-ffi --allow-env=HOME \
    --include "$LAB/.build/native-html/runtime/web-render.wasm" \
    --include "$LAB/../../../third_party/fonts/noto-sans/NotoSans-Regular.ttf" \
    --include "$LAB/../../../third_party/fonts/noto-sans/OFL.txt" \
    --include "$LAB/.build/engines/render-plan.wasm" \
    --include "$LAB/native-html/default.html" --include "$LAB/native-html/next.html" --include "$LAB/pages" \
    --include "$LAB/native_html_worker.ts" \
    --output "$OUT/native-webgpu-html-darwin-arm64.tmp" "$LAB/run_html.ts"
  mv "$OUT/native-webgpu-html-darwin-arm64.tmp" "$OUT/native-webgpu-html-darwin-arm64"
  # The native engine library sits beside the window program, which opens it
  # through FFI; with no library the program uses the Wasm engine.
  if [ -f "$LAB/.build/web-render/engines/libweb-render.dylib" ]; then
    cp "$LAB/.build/web-render/engines/libweb-render.dylib" "$OUT/libweb-render.dylib"
  fi
else
  echo 'No web-render engine: this package has no native HTML window' >&2
fi
# A double-click wrapper. macOS starts it in the desktop session, which WebGPU
# needs. It stays beside the package files; it does not copy them.
# The app icon: a FOAF graph drawn by make-icon.py, at the sizes of an .icns.
ICONSET="$LAB/.build/foafnaut.iconset"
rm -rf "$ICONSET"; mkdir -p "$ICONSET"
python3 "$LAB/make-icon.py" "$ICONSET/icon_512x512@2x.png" 1024
for size in 16 32 128 256 512; do
  sips -z "$size" "$size" "$ICONSET/icon_512x512@2x.png" --out "$ICONSET/icon_${size}x${size}.png" >/dev/null
  double=$((size*2))
  [ "$size" = 512 ] || sips -z "$double" "$double" "$ICONSET/icon_512x512@2x.png" --out "$ICONSET/icon_${size}x${size}@2x.png" >/dev/null
done
iconutil -c icns "$ICONSET" -o "$LAB/.build/foafnaut.icns"
rm -rf "$ICONSET"
# A regular app (no LSUIElement): in the Dock and in Command-Tab, with its name and icon.
make_app() {
  local name=$1 id=$2 command=$3 app="$OUT/$1.app"
  rm -rf "$app"
  mkdir -p "$app/Contents/MacOS" "$app/Contents/Resources"
  cp "$LAB/.build/foafnaut.icns" "$app/Contents/Resources/AppIcon.icns"
  cat > "$app/Contents/Info.plist" <<PLIST
<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE plist PUBLIC "-//Apple//DTD PLIST 1.0//EN" "http://www.apple.com/DTDs/PropertyList-1.0.dtd">
<plist version="1.0"><dict>
<key>CFBundleExecutable</key><string>run</string>
<key>CFBundleIdentifier</key><string>org.factoidal.$id.development</string>
<key>CFBundleName</key><string>$name</string>
<key>CFBundleDisplayName</key><string>$name</string>
<key>CFBundleIconFile</key><string>AppIcon</string>
<key>CFBundlePackageType</key><string>APPL</string>
<key>CFBundleShortVersionString</key><string>0.1</string>
<key>CFBundleVersion</key><string>1</string>
<key>LSApplicationCategoryType</key><string>public.app-category.productivity</string>
<key>LSMinimumSystemVersion</key><string>13.0</string>
<key>NSPrincipalClass</key><string>NSApplication</string>
<key>NSHighResolutionCapable</key><true/>
</dict></plist>
PLIST
  cat > "$app/Contents/MacOS/run" <<LAUNCHER
#!/bin/sh
set -eu
LOG="\$HOME/Library/Logs/$name"
mkdir -p "\$LOG"
cd "\$(dirname "\$0")/../../.."
FACTOIDAL_APP_NAME='$name' exec $command "\$@" >>"\$LOG/trace.jsonl" 2>&1
LAUNCHER
  chmod +x "$app/Contents/MacOS/run"
}
make_app 'FOAF Graph' foaf-graph './native-webgpu-ui-darwin-arm64 --demo foafnaut'
if [ -x "$OUT/native-webgpu-html-darwin-arm64" ]; then
  make_app foafnaut foafnaut './native-webgpu-html-darwin-arm64 --follow-links'
fi
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
if [ -x native-webgpu-html-darwin-arm64 ]; then shasum -a 256 native-webgpu-html-darwin-arm64 >> "$OUT/SHA256SUMS"; fi
if [ -f libweb-render.dylib ]; then shasum -a 256 libweb-render.dylib >> "$OUT/SHA256SUMS"; fi
# The compiled browser must start as the app starts it (issue 1268). On 2026-11-08 the binary
# had no env permission, run_html.ts read HOME to find the script guest, and the app stopped
# at start while every test of run_html.ts from source passed. One off-screen graph sweep.
if [ -x "$OUT/native-webgpu-html-darwin-arm64" ]; then
  START_RC=0
  (cd "$OUT" && timeout 180 ./native-webgpu-html-darwin-arm64 --offscreen --no-state --idle-checks-only --graph-sweep >"$OUT/start-check.log" 2>&1) || START_RC=$?
  if [ "$START_RC" != 0 ]; then echo "compiled foafnaut did not start (rc $START_RC):" >&2; grep -v '^{' "$OUT/start-check.log" | head -20 >&2; exit 1; fi
  rm -f "$OUT/start-check.log"
  echo 'Compiled foafnaut started off screen and passed the graph sweep'
fi
echo "Foafnaut native release directory: $OUT"
