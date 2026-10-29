#!/usr/bin/env bash
#
# tests/webannotation/run.sh — the W3C Web Annotation Data Model and Vocabulary
# tests (Recommendations, 2017-02-23) in Lean, over the vendored suite
# third_party/testing/web-annotation (provenance:
# third_party/testing/web-annotation-PROVENANCE.md;
# https://github.com/danbri/factoidal/issues/1165).
#
#   1. annotation-model: every .test file on every conforming document of its
#      kind (the 44 Recommendation examples, the 41 protocol samples). Runs
#      excluded as defective test data (https://github.com/danbri/factoidal/issues/1193)
#      are STALE (a failure) if they pass, and must pass with the corrected
#      tests/webannotation/local/choiceSet.json.
#   2. tests/webannotation/negative: documents that break one MUST each; the
#      named assertion must fail.
#   3. annotation-vocab 01-06: expansion, RDF, three syntax round trips, the
#      JSON-LD round trip, oa.ttl parses, domains and ranges.
#
# Builds l4webannotation in formal/lean4; exits 0 only when every step passes.
set -euo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN="$ROOT/formal/lean4"
SUITE="$ROOT/third_party/testing/web-annotation/annotation-model"
# The Lean runner does not run comparison objects or nested lists; the
# vendored .test files must use neither.
if grep -l '"compareWith"' -r "$SUITE" --include='*.json' --include='*.test' >/dev/null 2>&1; then
  echo "webannotation: a vendored assertion uses compareWith, which l4webannotation does not run" >&2
  exit 2
fi
(cd "$LEAN" && timeout 1800 lake build l4webannotation >/dev/null)
cd "$ROOT"
timeout 600 "$LEAN/.lake/build/bin/l4webannotation" third_party/testing/web-annotation tests/webannotation
