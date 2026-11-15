#!/bin/sh
# The full mode of spinal_bisect.ts (core issue 450): every variant of the Spinal Tap page on the
# native engine and in the desktop browser (drawing off screen at 1280x800, scale 2), ranked by
# what each feature adds. About 25 to 40 minutes on an M1, more while another agent holds the
# timing lock (/tmp/foafnaut-timing.lock; each run takes it). Not in test.sh.
#
#   sh spinal_bisect_full.sh [APP_DIR] [-- more spinal_bisect.ts options, e.g. --only a,b --watch 25]
# APP_DIR: a release folder with native-webgpu-html-darwin-arm64 and libweb-render.dylib;
# default ~/.foafnaut/current/foafnaut (the installed browser). The engine library is the app's
# unless WEB_RENDER_DYLIB says otherwise. Results: .build/spinal-bisect/full.{json,md}.
set -eu
LAB=$(cd "$(dirname "$0")" && pwd)
APP=${1:-$HOME/.foafnaut/current/foafnaut}
[ "$#" -gt 0 ] && shift
[ "${1:-}" = "--" ] && shift
[ -x "$APP/native-webgpu-html-darwin-arm64" ] || { echo "NOT RUN: no native-webgpu-html-darwin-arm64 in $APP"; exit 0; }
export WEB_RENDER_DYLIB=${WEB_RENDER_DYLIB:-$APP/libweb-render.dylib}
mkdir -p "$LAB/.build/spinal-bisect"
exec deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-ffi -A "$LAB/spinal_bisect.ts" \
  --app "$APP" --engine "$WEB_RENDER_DYLIB" --out "$LAB/.build/spinal-bisect/full.json" --md "$LAB/.build/spinal-bisect/full.md" "$@"
