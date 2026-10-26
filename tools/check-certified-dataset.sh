#!/usr/bin/env bash
# Check that the type CertifiedDataset (formal/lean4/L4Factoidal/RDF/CertifiedDataset.lean)
# refuses a dataset that lists one triple two times in one graph.
#
#   1. tests/negative/CertifiedDatasetSingle.lean must elaborate (positive control).
#   2. tests/negative/CertifiedDatasetDuplicate.lean must FAIL, with the goal `False`
#      unsolved: the proof of Dataset.IsSet does not exist for [t, t].
#
# The fixtures are outside every lake build target. Run after `lake build
# L4Factoidal.RDF.CertifiedDataset` (or a full `lake build`).
# Exit 0 when both hold, 1 otherwise. Logs go to .claude-runs/negative/.
set -u
root="$(cd "$(dirname "$0")/.." && pwd)"
lean_dir="$root/formal/lean4"
log_dir="$root/.claude-runs/negative"
mkdir -p "$log_dir"
cd "$lean_dir" || exit 1

pos_rc=0
timeout 600 lake env lean tests/negative/CertifiedDatasetSingle.lean > "$log_dir/single.log" 2>&1 || pos_rc=$?
neg_rc=0
timeout 600 lake env lean tests/negative/CertifiedDatasetDuplicate.lean > "$log_dir/duplicate.log" 2>&1 || neg_rc=$?

fail=0
if [ "$pos_rc" -ne 0 ]; then
  echo "FAIL: positive control did not elaborate (rc=$pos_rc); see $log_dir/single.log"
  cat "$log_dir/single.log"
  fail=1
else
  echo "PASS: a dataset with the triple once is a CertifiedDataset"
fi
if [ "$neg_rc" -eq 0 ]; then
  echo "FAIL: a dataset with a repeated triple elaborated as a CertifiedDataset"
  fail=1
elif grep -q "unsolved goals" "$log_dir/duplicate.log" && grep -q "⊢ False" "$log_dir/duplicate.log"; then
  echo "PASS: a dataset with a repeated triple is refused (unsolved goal False)"
else
  echo "FAIL: duplicate fixture failed for another reason (rc=$neg_rc); see $log_dir/duplicate.log"
  cat "$log_dir/duplicate.log"
  fail=1
fi
exit "$fail"
