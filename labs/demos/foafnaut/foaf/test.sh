#!/usr/bin/env bash
# Fresh small source closure; no lake/full engine or runtime rebuild.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
PROJECT=$(cd "$HERE/../../../../formal/lean4" && pwd)
BUILD="$HERE/.build"
mkdir -p "$BUILD/olean"
LOCK=${FOAFNAUT_BUILD_LOCK:-$BUILD/lean.lock}
if ! mkdir "$LOCK"; then echo "Lean build lock busy: $LOCK" >&2; exit 1; fi
trap 'rmdir "$LOCK"' EXIT
cd "$PROJECT"
TOOLCHAIN=$(lean --print-prefix)
export LEAN_PATH="$BUILD/olean"
for module in RDF/XmlCanon RDF/Core RDF/Graph Encoding/Hex Syntax/Lexing \
  Syntax/NTriples Syntax/IriResolve RDF/IriSyntax NatBounds Syntax/Turtle \
  JSON/Value JSON/Parser JSON/Serialize; do
  mkdir -p "$BUILD/olean/L4Factoidal/$(dirname "$module")"
  "$TOOLCHAIN/bin/lean" -R "$PROJECT" -o "$BUILD/olean/L4Factoidal/$module.olean" "$PROJECT/L4Factoidal/$module.lean"
done
"$TOOLCHAIN/bin/lean" -R "$HERE" -o "$BUILD/olean/FoafGraph.olean" "$HERE/FoafGraph.lean"
"$TOOLCHAIN/bin/lean" -R "$HERE" --run "$HERE/Tests.lean" "$HERE/fixtures/people.ttl"
