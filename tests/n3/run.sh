#!/usr/bin/env bash
# The Notation3 reader on the W3C N3 Community Group suite and on the Turtle
# suites (https://github.com/danbri/factoidal/issues/1171).
#
#   tests/n3/run.sh            build `l4n3`, run every manifest below
#
# Each line runs `lake exe l4n3` on one manifest. The run fails when a counted
# test fails (rdft:Rejected entries are counted apart and do not fail it) or
# when the N3 and Turtle readers disagree on a Turtle test (`turtle-agreement`).
# Suites: third_party/testing/n3 (pinned, third_party/testing/n3-PROVENANCE.md)
# and third_party/testing/w3c (RDF 1.1 and RDF 1.2 Turtle).
set -uo pipefail

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
LEAN="${ROOT}/formal/lean4"
N3="${ROOT}/third_party/testing/n3/tests"
W3C="${ROOT}/third_party/testing/w3c/rdf"

for f in "${N3}/N3Tests/manifest-parser.ttl" "${W3C}/rdf11/rdf-turtle/manifest.ttl"; do
  if [ ! -f "$f" ]; then
    echo "missing suite file: $f (run: git submodule update --init third_party/testing/n3 third_party/testing/w3c)" >&2
    exit 2
  fi
done

(cd "${LEAN}" && lake build l4n3) || exit 2
BIN="${LEAN}/.lake/build/bin/l4n3"

status=0
run() {
  local rc=0
  timeout 600 "${BIN}" --quiet "$@" || rc=$?
  if [ "$rc" -ne 0 ]; then
    echo "FAILED (exit ${rc}): l4n3 $*"
    status=1
  fi
}

run "${N3}/N3Tests/manifest-parser.ttl"
run "${N3}/N3Tests/manifest-extended.ttl"
run "${N3}/N3Tests/manifest-reasoner.ttl"
run "${N3}/TurtleTests/manifest.ttl"
run "${W3C}/rdf11/rdf-turtle/manifest.ttl"
run --rdf12 "${W3C}/rdf12/rdf-turtle/syntax/manifest.ttl"
run --rdf12 "${W3C}/rdf12/rdf-turtle/eval/manifest.ttl"

exit "${status}"
