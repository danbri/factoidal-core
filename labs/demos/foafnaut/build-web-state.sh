#!/usr/bin/env bash
# Build `web-state`, a small native program that answers the browser-state ops of
# WebState.lean over standard input (WebStateCLI.lean). It needs the built JSON modules of
# formal/lean4 (`lake build L4Factoidal.JSON.Parser L4Factoidal.JSON.Serialize`), or
# LEAN_CORE_BUILD naming another checkout's formal/lean4/.lake/build with the same sources.
# The engine (build-web-render.sh) carries the same ops; this is for tests and for an
# engine built before WebState.
set -euo pipefail
LAB=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$LAB/../../.." && pwd)
PROJECT="$ROOT/formal/lean4"
CORE=${LEAN_CORE_BUILD:-$PROJECT/.lake/build}
BUILD="$LAB/.build/web-state"
mkdir -p "$BUILD/olean" "$BUILD/obj"
cd "$PROJECT"
export LEAN_PATH="$BUILD/olean:$CORE/lib/lean"
for module in WebState WebStateCLI; do
  lean -R "$LAB" -o "$BUILD/olean/$module.olean" -c "$BUILD/$module.c" "$LAB/$module.lean"
done
OBJECTS=()
for module in Encoding/Hex JSON/Value JSON/Serialize JSON/Parser; do
  object="$BUILD/obj/$(echo "$module" | tr / _).o"
  leanc -O2 -c "$CORE/ir/L4Factoidal/$module.c" -o "$object"
  OBJECTS+=("$object")
done
for module in WebState WebStateCLI; do
  leanc -O2 -c "$BUILD/$module.c" -o "$BUILD/obj/$module.o"
  OBJECTS+=("$BUILD/obj/$module.o")
done
leanc -O2 -o "$BUILD/web-state" "${OBJECTS[@]}"
echo "WEB_STATE=$BUILD/web-state"
