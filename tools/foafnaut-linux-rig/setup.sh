#!/usr/bin/env bash
# Prepare a Linux machine with no display and no GPU (a cloud session) to run the Foafnaut
# desktop browser from source and measure it (issue 1031):
# - Xvfb, Mesa software Vulkan (lavapipe) and SDL2 from apt (skip with RIG_NO_APT=1);
# - the newest released engine of main: web-render.{mjs,wasm} and render-plan.{mjs,wasm} of the
#   foafnaut-web set, libweb-render.so of the foafnaut-browser-linux-x86_64 set, both from
#   danbri/factoidal-builds, sha256 checked against the release's build-info.json;
# - libnative-window.so built from this checkout's native_window_linux.c.
# Usage: tools/foafnaut-linux-rig/setup.sh [RIG_DIR]   (default ~/.foafnaut-rig)
# Then:  tools/foafnaut-linux-rig/run.sh [run_html.ts arguments]   (use a sweep so it exits)
# The engine is the released one, not this checkout's Lean: host changes are measured as they
# are; a change to the Lean engine needs an engine build first (skills/foafnaut).
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd); LAB="$ROOT/labs/demos/foafnaut"
RIG=${1:-$HOME/.foafnaut-rig}; mkdir -p "$RIG"
if [[ -z ${RIG_NO_APT:-} ]] && ! command -v Xvfb >/dev/null; then
  apt-get install -y -qq xvfb libvulkan1 mesa-vulkan-drivers libsdl2-dev >/dev/null
fi
BUILDS=https://github.com/danbri/factoidal-builds
fetch_set() {  # fetch_set SET ARCHIVE DIR: newest release of SET, checked, unpacked into DIR
  local set=$1 archive=$2 dir=$3 tag
  tag=$(curl -sfL "https://raw.githubusercontent.com/danbri/factoidal-builds/main/latest/$set.json" | python3 -c 'import json,sys;print(json.load(sys.stdin)["tag"])')
  [[ -f "$dir/.tag" && $(cat "$dir/.tag") == "$tag" ]] && { echo "$set: $tag (cached)"; return; }
  rm -rf "$dir"; mkdir -p "$dir"
  curl -sfL -o "$dir/build-info.json" "$BUILDS/releases/download/$tag/build-info.json"
  curl -sfL -o "$dir/$archive" "$BUILDS/releases/download/$tag/$archive"
  python3 - "$dir/build-info.json" "$dir/$archive" <<'PY'
import hashlib, json, sys
info, path = json.load(open(sys.argv[1])), sys.argv[2]
name = path.rsplit("/", 1)[1]
want = (info.get("artifacts", {}).get(name) or {}).get("sha256")
got = hashlib.sha256(open(path, "rb").read()).hexdigest()
if want and want != got: sys.exit(f"{name}: sha256 {got} is not {want}")
print(f"{name}: sha256 {'checked' if want else 'not listed in build-info.json; per-file sums checked after unpack'}")
PY
  tar -xzf "$dir/$archive" -C "$dir"; echo "$tag" > "$dir/.tag"; echo "$set: $tag"
}
fetch_set foafnaut-web foafnaut-web.tar.gz "$RIG/web"
fetch_set foafnaut-browser-linux-x86_64 foafnaut-browser-linux-x86_64.tar.gz "$RIG/linux"
(cd "$RIG/linux"/foafnaut-linux-x86_64 && sha256sum --check --quiet SHA256SUMS)
RT="$RIG/web/docs/web/hub/html-webgpu/runtime"
mkdir -p "$LAB/.build/native-html/runtime" "$LAB/.build/engines" "$LAB/.build/native"
cp "$RT/web-render.mjs" "$RT/web-render.wasm" "$LAB/.build/native-html/runtime/"
cp "$RT/render-plan.mjs" "$RT/render-plan.wasm" "$LAB/.build/engines/"
read -ra F <<<"$(pkg-config --cflags sdl2)"; read -ra L <<<"$(pkg-config --libs sdl2)"
cc -std=c11 -O2 -Wall -Wextra -Werror -fPIC -shared -Wl,-z,defs "${F[@]}" "$LAB/native_window_linux.c" "${L[@]}" -lm \
  -o "$LAB/.build/native/libnative-window.so"
echo "$RIG/linux/foafnaut-linux-x86_64/libweb-render.so" > "$LAB/.build/native/rig-engine-path"
echo "ready: run tools/foafnaut-linux-rig/run.sh --html FILE --scroll-sweep --perf-summary"
