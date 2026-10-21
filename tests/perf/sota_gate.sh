#!/usr/bin/env bash
# tests/perf/sota_gate.sh: the regression gate of the state-of-the-art table
# (key result 2.7 of https://github.com/danbri/factoidal/issues/768;
# https://github.com/danbri/factoidal/issues/811; records
# docs/designissues/2026-10-12-sota-reference.md and, since 2026-10-21,
# docs/designissues/2026-10-21-sota-remeasure.md, whose results file is the
# default SOTA_RECORD).
#
# Re-runs every Lean row (engines `lean` and `lean-stream`) of the recorded
# table whose recorded median wall time is at most SOTA_MAX_S seconds
# (default 60), three runs each, and fails when a row
#   - gives a different answer (statement count, solution count, COUNT value,
#     SHA-256 of the canonical N-Quads, consistency verdict), or
#   - takes, in the least of its runs, more than (1 + SOTA_TOLERANCE) x the
#     recorded median CPU time (x the host factor, below) plus 0.05 s, or
#   - holds more than (1 + SOTA_TOLERANCE) x the recorded median peak
#     resident set plus 8 MB, or
#   - takes more than 3 times (SOTA_TIME_BOUND) the minimum wall time of the
#     fastest recorded reference engine of its case, by its own minimum wall
#     time, and carries no expected-failure mark (key result 2.2 of
#     https://github.com/danbri/factoidal/issues/901; marks: XFAIL in
#     tools/sota-bench.py, each naming its open issue). A marked row that
#     measures under 2.2 times (SOTA_TIME_BOUND / SOTA_XPASS_MARGIN) fails as
#     UNEXPECTED PASS.
# Host factor: before the rows, and before the second measurement of a
# failing row, the gate runs Oxigraph on parse-nt 400,000 and scales the
# recorded CPU times and reference wall times by its CPU time over the
# recorded one when that is above 1 (SOTA_CALIBRATE=0 turns it off).
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
REC="${SOTA_RECORD:-$ROOT/docs/designissues/2026-10-21-sota-remeasure.results.jsonl}"
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
