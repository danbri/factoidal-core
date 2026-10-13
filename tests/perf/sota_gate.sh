#!/usr/bin/env bash
# tests/perf/sota_gate.sh: the regression gate of the state-of-the-art table
# (key result 2.7 of https://github.com/danbri/factoidal/issues/768;
# https://github.com/danbri/factoidal/issues/811; record
# docs/designissues/2026-10-12-sota-reference.md).
#
# Re-runs every Lean row (engines `lean` and `lean-stream`) of the recorded
# table whose recorded median wall time is at most SOTA_MAX_S seconds
# (default 60), three runs each, and fails when a row
#   - gives a different answer (statement count, solution count, COUNT value,
#     SHA-256 of the canonical N-Quads, consistency verdict), or
#   - takes more than (1 + SOTA_TOLERANCE) x the recorded median CPU time
#     plus 0.05 s, or
#   - holds more than (1 + SOTA_TOLERANCE) x the recorded median peak
#     resident set plus 8 MB.
# SOTA_TOLERANCE defaults to 0.25. A failing row is measured a second time
# before it fails. The reference engines are not run: their rows are
# informative. CPU time is compared because the machine is shared and the
# load average moves wall time more than CPU time
# (skills/perf-benchmarking, "The load average moves wall time").
#
# Needs: formal/lean4/.lake/build/bin/l4factoidal (lake build l4factoidal),
# python3, gene.ttl and the vendored ontologies. Inputs are generated into
# SOTA_FIXTURES (default /tmp/sota-dl-<checkout directory name>/fixtures,
# one directory per checkout: hazard #43 of skills/workflow-gotchas-debugging). Baselines are per host
# (skills/perf-benchmarking, "Baselines are per-host"): after a container
# moves to other hardware, re-measure the Lean rows before reading a failure
# as a regression.
#
# Exit 0: every row passes. Exit 1: a row failed. Exit 2: setup error.
set -uo pipefail
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
REC="${SOTA_RECORD:-$ROOT/docs/designissues/2026-10-12-sota-reference.results.jsonl}"
LEAN="${SOTA_LEAN_BIN:-$ROOT/formal/lean4/.lake/build/bin}/l4factoidal"
if [ ! -x "$LEAN" ]; then
  echo "sota gate: $LEAN missing (cd formal/lean4 && lake build l4factoidal)" >&2
  exit 2
fi
if [ ! -f "$REC" ]; then
  echo "sota gate: recorded table $REC missing" >&2
  exit 2
fi
RC=0
python3 "$ROOT/tools/sota-bench.py" --check "$REC" \
  --tolerance "${SOTA_TOLERANCE:-0.25}" --max-s "${SOTA_MAX_S:-60}" "$@" || RC=$?
exit "$RC"
