#!/usr/bin/env bash
#
# tools/bench/three-engines/qlever-native-build.sh
#
# Build QLever natively (no docker) at the commit pinned in
# tests/qlvr/instance.json. Source and build tree live under QLEVER_NATIVE
# (default /home/user/qlever-native), outside the repository.
# Issue: https://github.com/danbri/factoidal/issues/798. Record:
# docs/designissues/2026-10-12-three-engine-benchmark.md, "QLever native".
#
# Configuration follows the Dockerfile of the pinned commit (Release, Ninja,
# mold, no march=native, -Wno-psabi), without the test binaries and without
# LTO. Targets: qlever-index and qlever-server. Two build jobs (-j2).
# Dependencies: the apt packages listed in the record (Boost 1.83, ICU, zstd,
# OpenSSL, liburing, jemalloc, mold, ninja, uuid). FetchContent downloads the
# other sources from GitHub at configure time.
#
# Usage: qlever-native-build.sh [configure|build]   (default: both)
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
QN="${QLEVER_NATIVE:-/home/user/qlever-native}"
SRC="$QN/src"
BLD="$QN/build"
STEP="${1:-all}"
PIN="$(python3 -I -c 'import json,sys; print(json.load(open(sys.argv[1]))["qlever_commit"])' "$ROOT/tests/qlvr/instance.json")" || exit 1
log() { printf '[qlever-native %s] %s\n' "$(date -u +%H:%M:%S)" "$*" >&2; }

mkdir -p "$QN"
if [ ! -d "$SRC/.git" ]; then
  log "fetch $PIN into $SRC"
  git init -q "$SRC" && git -C "$SRC" remote add origin https://github.com/ad-freiburg/qlever.git
  git -C "$SRC" fetch -q --depth 1 origin "$PIN" || { log "fetch failed"; exit 1; }
  git -C "$SRC" checkout -q FETCH_HEAD || exit 1
fi
HEAD_SHA="$(git -C "$SRC" rev-parse HEAD)"
if [ "$HEAD_SHA" != "$PIN" ]; then
  log "source is $HEAD_SHA, pinned commit is $PIN: stop"; exit 1
fi
log "source at pinned commit $PIN"

if [ "$STEP" = all ] || [ "$STEP" = configure ]; then
  mkdir -p "$BLD"
  log "cmake configure"
  RC=0
  (cd "$BLD" && cmake -DCMAKE_BUILD_TYPE=Release -DLOGLEVEL=INFO -DUSE_PARALLEL=true \
     -D_NO_TIMING_TESTS=ON -DCOMPILER_SUPPORTS_MARCH_NATIVE=FALSE \
     -DCMAKE_EXE_LINKER_FLAGS="-fuse-ld=mold" -DCMAKE_SHARED_LINKER_FLAGS="-fuse-ld=mold" \
     -DCMAKE_CXX_FLAGS="-Wno-psabi" -GNinja "$SRC" > "$QN/configure.log" 2>&1) || RC=$?
  [ "$RC" = 0 ] || { log "configure failed (rc $RC), see $QN/configure.log"; exit "$RC"; }
fi
if [ "$STEP" = all ] || [ "$STEP" = build ]; then
  log "ninja -j2 qlever-index qlever-server"
  RC=0
  (cd "$BLD" && ninja -j2 qlever-index qlever-server > "$QN/build.log" 2>&1) || RC=$?
  [ "$RC" = 0 ] || { log "build failed (rc $RC), see $QN/build.log"; exit "$RC"; }
  log "built: $BLD/qlever-index $BLD/qlever-server"
fi
