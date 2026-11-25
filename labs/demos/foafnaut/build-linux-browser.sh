#!/usr/bin/env bash
# Package the windowed Linux browser from a foafnaut-engines CI artifact in
# .build. A same-revision native worker library can also be supplied there.
set -euo pipefail
LAB=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$LAB/../../.." && pwd)
. "$LAB/toolchain-versions.env"
if [[ $# != 1 || $(uname -s) != Linux ]]; then
  echo "Usage on Linux: bash build-linux-browser.sh NEW_PACKAGE_DIRECTORY" >&2
  exit 2
fi
OUT=$(realpath -m -- "$1")
[[ ! -e "$OUT" ]] || { echo "Package directory already exists: $OUT" >&2; exit 1; }
[[ $(deno --version | awk 'NR==1 {print $2}') == "$DENO_VERSION" ]] || { echo "Use Deno $DENO_VERSION" >&2; exit 1; }
pkg-config --atleast-version=2.0.18 sdl2 || { echo "SDL2 development headers 2.0.18 or newer are required" >&2; exit 1; }
BUILD="$LAB/.build"
RUNTIME="$BUILD/native-html"
ENGINES="$BUILD/web-render/engines"
mkdir -p "$RUNTIME/runtime" "$(dirname "$OUT")"
STAGE=$(mktemp -d "$(dirname "$OUT")/.foafnaut-package.XXXXXXXX")
trap 'rm -rf "$STAGE"' EXIT
(cd "$ROOT" && sha256sum --check --quiet "$BUILD/source-SHA256SUMS")
cp "$ENGINES"/web-render.{mjs,wasm} "$RUNTIME/runtime/"
HOST_SHA=$(git -C "$ROOT" rev-parse HEAD)
export HOST_SHA
python3 - "$ROOT" "$RUNTIME/build-info.json" <<'PY'
import datetime, json, os, pathlib, subprocess, sys
root, output = map(pathlib.Path, sys.argv[1:])
commit = os.environ["HOST_SHA"]
version = json.loads((root / "npm/factoidal/package.json").read_text())["version"]
git = lambda *args: subprocess.check_output(["git", "-C", str(root), *args], text=True).strip()
dirty = bool(git("status", "--porcelain", "--untracked-files=no"))
data = dict(commit=commit[:12], commitFull=commit, version=version, dirty=dirty,
            builtAt=datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
            release=not dirty and "v"+version in git("tag", "--points-at", "HEAD").splitlines())
output.write_text(json.dumps(data, indent=2) + "\n")
PY
# The executable opens the shim by absolute path beside itself. SDL supplies
# the window handles. The Deno runtime owns Vulkan and the swap chain.
read -ra SDL_CFLAGS <<<"$(pkg-config --cflags sdl2)"
read -ra SDL_LIBS <<<"$(pkg-config --libs sdl2)"
"${CC:-cc}" -std=c11 -O2 -Wall -Wextra -Werror -fPIC -shared -Wl,-z,defs \
  "${SDL_CFLAGS[@]}" "$LAB/native_window_linux.c" "${SDL_LIBS[@]}" -lm -o "$STAGE/libnative-window.so"
if [[ -f "$ENGINES/libweb-render.so" ]]; then
  cp "$ENGINES/libweb-render.so" "$STAGE/"
fi
deno compile --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi \
  --allow-read --allow-write --allow-net --allow-ffi --allow-env=HOME,FOAFNAUT_LOG,XDG_DATA_HOME \
  --include "$RUNTIME/build-info.json" --include "$RUNTIME/runtime/web-render.wasm" \
  --include "$BUILD/engines/render-plan.wasm" --include "$ROOT/third_party/fonts" \
  --include "$ROOT/docs/web/hub/foafnaut/font-coverage.mjs" --include "$ROOT/docs/web/hub/foafnaut/fallback-fonts.mjs" \
  --include "$LAB/native-html" --include "$LAB/native_html_worker.ts" --include "$LAB/pages" \
  --output "$STAGE/foafnaut" "$LAB/run_html.ts" --follow-links

# Ask both engines for their own build identity before accepting the package.
# With no native worker these two invocations use the same document Wasm.
for backend in wasm default; do
  flags=()
  [[ $backend != wasm ]] || flags+=(--wasm-engine)
  report=$("$STAGE/foafnaut" --version "${flags[@]}")
  printf '%s\n' "$report"
  line=$(head -1 <<<"$report")
  [[ $line == "foafnaut "*"commit $HOST_SHA,"* && $report != *"does not match"* ]] || {
    echo "$backend document engine differs from the package source $HOST_SHA" >&2; exit 1; }
done
cp "$RUNTIME/build-info.json" "$STAGE/BUILD-INFO.json"
cp "$ROOT/LICENSE" "$ROOT/third_party/notices/GMP-NOTICE.txt" "$STAGE/"
mkdir -p "$STAGE/licences"
cp "$LAB/licences/Deno-LICENSE.txt" "$STAGE/licences/"
(cd "$ROOT/third_party/fonts" && cp --parents -- */OFL.txt "$STAGE/licences/")
cp "$BUILD/source-SHA256SUMS" "$BUILD/tool-versions.txt" "$STAGE/"
cp "$LAB/LINUX.md" "$STAGE/README.md"
(cd "$BUILD" && sha256sum engines/render-plan.{mjs,wasm} web-render/engines/web-render.{mjs,wasm}) > "$STAGE/engine-SHA256SUMS"
(
  cd "$STAGE"
  find . -type f ! -name SHA256SUMS -print0 | LC_ALL=C sort -z | xargs -0 sha256sum > SHA256SUMS
)
mv -T -- "$STAGE" "$OUT"
trap - EXIT
echo "Packaged Linux browser at $OUT"
