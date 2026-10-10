#!/usr/bin/env bash
#
# tests/stack/canary_control.sh -- the control of the native stack canary can
# fail (issue 749).
#
# tests/stack/run.sh --canary measures a reduced stack with a control before it
# scores anything (see THE CONTROL in run.sh). A control that cannot fail is
# no control, so this script checks both outcomes:
#   1. with LEAN_STACK_SIZE_KB, the variable the Lean runtime reads, the
#      control passes;
#   2. with LEAN_STACK_SIZE, the name this suite set until 2026-10-10, the
#      control fails and says the variable did not reach the process.
#
# Usage:  tests/stack/canary_control.sh [run.sh options, e.g. --fixtures DIR]
# Prints "N pass, M fail (out of 2)". Exit status 0 when both checks hold.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PASS=0; FAIL=0

out="$("$HERE/run.sh" --control-only "$@" 2>&1)"; rc=$?
if [ "$rc" -eq 0 ]; then
  PASS=$((PASS + 1)); echo "ok   right variable: $out"
else
  FAIL=$((FAIL + 1)); echo "FAIL right variable: the control should pass (exit $rc): $out"
fi

out="$(STACK_CANARY_VAR=LEAN_STACK_SIZE "$HERE/run.sh" --control-only "$@" 2>&1)"; rc=$?
if [ "$rc" -eq 1 ] && printf '%s' "$out" | grep -q 'did not reach the process'; then
  PASS=$((PASS + 1)); echo "ok   wrong variable: the control refused to score: $(printf '%s' "$out" | head -c 160)"
else
  FAIL=$((FAIL + 1)); echo "FAIL wrong variable: the control should fail with 'did not reach the process' (exit $rc): $out"
fi

echo "canary control: $PASS pass, $FAIL fail (out of 2)"
[ "$FAIL" -eq 0 ]
