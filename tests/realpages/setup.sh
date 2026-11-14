#!/bin/bash
# Prepares a work folder (scratch, never committed) for run_all.ts: the macOS engine release of each commit,
# the host sources of the same commit with the measurement steps added (rp_patch.py), and the image tool.
# usage: tests/realpages/setup.sh WORK_DIR SHA12 [SHA12 ...]   (run from the repository root)
# The host needs labs/demos/foafnaut/.build (native window library, wasm engines) of a built checkout:
# set HOSTBUILD=/path/to/labs/demos/foafnaut/.build (it is linked, not copied).
set -euo pipefail
W=$1; shift; H=$(cd "$(dirname "$0")" && pwd); mkdir -p "$W/eng" "$W/host"
[ -x "$W/imgfacts" ] || swiftc -O "$H/imgfacts.swift" -o "$W/imgfacts"
for c in "$@"; do
  if [ ! -f "$W/eng/$c/foafnaut/libweb-render.dylib" ]; then
    mkdir -p "$W/eng/$c"; (cd "$W/eng/$c" && gh release download "build-$c-foafnaut-engine-darwin-arm64" -R danbri/factoidal-builds \
      -p 'foafnaut-engine-darwin-arm64.tar.gz' -p build-info.json && tar xzf foafnaut-engine-darwin-arm64.tar.gz && rm foafnaut-engine-darwin-arm64.tar.gz)
  fi
  if [ ! -d "$W/host/$c" ]; then
    mkdir -p "$W/host/$c"; git archive "$c" labs/demos/foafnaut docs/web/hub/foafnaut third_party/fonts | tar x -C "$W/host/$c"
    find "$W/host/$c" -name '*.lean' -delete
    ln -s "${HOSTBUILD:?set HOSTBUILD}" "$W/host/$c/labs/demos/foafnaut/.build"
    python3 -I "$H/rp_patch.py" "$W/host/$c/labs/demos/foafnaut/run_html.ts"
  fi
done
