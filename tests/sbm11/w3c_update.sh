#!/usr/bin/env bash
#
# tests/sbm11/w3c_update.sh -- the W3C SPARQL 1.1 Update evaluation tests through
# the SBM11 store (https://github.com/danbri/factoidal/issues/849 item 3 and
# https://github.com/danbri/factoidal/issues/850).
#
# For every `mf:UpdateEvaluationTest` of the update manifests under
# third_party/testing/w3c/sparql/sparql11 (add, basic-update, clear, copy,
# delete-data, delete-insert, delete-where, delete, drop, move, update-silent):
#
#   1. the manifests are read from disk (`l4sbm11-w3c list-update`, the manifest
#      reader of the Lean W3C runner);
#   2. REFERENCE: the in-memory Lean update runner (`l4sbm11-w3c run-update`, which
#      calls `Harness.runUpdateEvaluation`, the runner `l4w3c` uses): parse the
#      request with the file URL of the request as BASE, load `ut:data` and
#      `ut:graphData`, `applyUpdateIn`, compare with `mf:result`;
#   3. STORE: `l4sbm11-w3c prepare-update` writes the initial Graph Store (the
#      default graph and every `ut:graphData` with its graph name, loaded as the
#      reference loads it) and the expected Graph Store as N-Quads;
#      `l4sbm11-pack` packs the initial store (the source layer reads the N-Quads);
#      `l4sbm11 update GEN --file REQUEST --base FILE-URL` appends the request as
#      one log batch; `l4sbm11 compact` folds the log into a new generation
#      (`l4sbm11 dump` reads the base of a generation, not the overlay; the
#      compaction reads the overlaid generation by the scans a query uses);
#      `l4sbm11 dump` writes the compacted generation as N-Quads; and
#      `l4sbm11-w3c compare` compares it with the expected store by RDF dataset
#      isomorphism, after the Lean runner's rule that a named graph with no triple
#      is dropped on both sides (the store holds no empty graph).
#
# A request with a LOAD without SILENT is skipped by both (no document is fetched).
#
# Prints, for each suite, "store: N pass, M fail, K expected-fail, S skip (out of
# T); reference: N pass, M fail, S skip (out of T)", then the store-only failures
# (a test that the reference passes and the store fails), the failures of both,
# and the total:
#
#   w3c update: store: N pass, M fail, K expected-fail, S skip (out of T); reference: ...
#
# An expected failure is a row of tests/sbm11/w3c_update_xfail.tsv: suite, entry,
# the URL of an open issue, the reason. The row is checked on every run: a test in
# the table that passes in the store is a FAILURE of the run ("unexpected pass").
#
# Exit status: 0 when the store passes every test the reference passes (except the
# expected failures) and no expected failure passes; 1 otherwise; 2 when a binary
# or a manifest is missing.
#
# Env: L4_BIN_DIR      directory of the binaries (default formal/lean4/.lake/build/bin)
#      FACTOIDAL_TESTING_ROOT  the directory of the W3C fixtures (default
#                      third_party/testing); W3C_SPARQL11_DIR overrides the suite
#      W3C_UPDATE_JOBS tests in parallel (default 4)
#      W3C_UPDATE_KEEP a directory to keep the work directories of the FAILED
#                      tests in
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_BIN_DIR:-$ROOT/formal/lean4/.lake/build/bin}"
TESTING="${FACTOIDAL_TESTING_ROOT:-$ROOT/third_party/testing}"
W3C_DIR="${W3C_SPARQL11_DIR:-$TESTING/w3c/sparql/sparql11}"
XFAIL_TABLE="$HERE/w3c_update_xfail.tsv"
JOBS="${W3C_UPDATE_JOBS:-4}"
SUITES="add basic-update clear copy delete-data delete-insert delete-where delete drop move update-silent"
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack" "$BIN/l4sbm11-w3c" "$W3C_DIR/add/manifest.ttl" "$XFAIL_TABLE"; do
  if [ ! -e "$need" ]; then echo "missing: $need (tools/ensure-test-env.sh; lake build)" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-w3c-update.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
mkdir -p "$TMP/w"

# ---- 1. the tests, from the manifests on disk
manifests=()
for s in $SUITES; do manifests+=("$W3C_DIR/$s/manifest.ttl"); done
rc=0
"$BIN/l4sbm11-w3c" list-update "${manifests[@]}" >"$TMP/rows.raw" 2>"$TMP/rows.err" || rc=$?
if [ "$rc" -ne 0 ]; then echo "list-update failed: $(cat "$TMP/rows.err")" >&2; exit 2; fi
awk -F'\t' '{ printf "%d\t%s\n", NR, $0 }' "$TMP/rows.raw" >"$TMP/rows.tsv"
total_rows="$(wc -l <"$TMP/rows.tsv")"
if [ "$total_rows" -lt 50 ]; then echo "only $total_rows tests listed: the manifests were not read" >&2; exit 2; fi

# ---- 2. one test: reference, then store
# Prints one line: idx, suite, entry, name, reference (pass|fail|skip), detail,
# store (pass|fail|skip), detail.
run_row() {
  local idx suite entry name manifest request
  IFS=$'\t' read -r idx suite entry name manifest request <<<"$1"
  local d="$TMP/w/$idx" ref refd store stored out rc
  mkdir -p "$d"
  # reference
  rc=0
  out="$(timeout 120 "$BIN/l4sbm11-w3c" run-update "$manifest" "$entry" 2>&1)" || rc=$?
  case "$out" in
    pass*) ref=pass; refd=- ;;
    skip*) ref=skip; refd="$(printf '%s' "$out" | head -1 | cut -c1-200)" ;;
    *) ref=fail; refd="$(printf '%s' "$out" | head -1 | cut -c1-200)" ;;
  esac
  # store
  rc=0
  out="$(timeout 120 "$BIN/l4sbm11-w3c" prepare-update "$manifest" "$entry" "$d" 2>&1)" || rc=$?
  case "$out" in
    ok) ;;
    skip*) store=skip; stored="$(printf '%s' "$out" | head -1 | cut -c1-200)" ;;
    *) store=fail; stored="prepare: $(printf '%s' "$out" | head -1 | cut -c1-200)" ;;
  esac
  if [ -z "${store:-}" ]; then
    rc=0
    timeout 120 "$BIN/l4sbm11-pack" "$d/input.nq" "$d/col/gen" --workers 1 >"$d/pack.log" 2>&1 || rc=$?
    if [ "$rc" -ne 0 ]; then store=fail; stored="pack exit $rc: $(tail -1 "$d/pack.log" | cut -c1-200)"; fi
  fi
  if [ -z "${store:-}" ]; then
    rc=0
    timeout 120 "$BIN/l4sbm11" update "$d/col/gen" --file "$request" --base "file://$request" >"$d/update.log" 2>&1 || rc=$?
    if [ "$rc" -ne 0 ]; then store=fail; stored="update exit $rc: $(grep -v '^l4sbm11 update: op ' "$d/update.log" | tail -1 | cut -c1-200)"; fi
  fi
  if [ -z "${store:-}" ]; then
    rc=0
    timeout 120 "$BIN/l4sbm11" compact "$d/col/gen" "$d/col/gen2" >"$d/compact.log" 2>&1 || rc=$?
    if [ "$rc" -ne 0 ]; then store=fail; stored="compact exit $rc: $(tail -1 "$d/compact.log" | cut -c1-200)"; fi
  fi
  if [ -z "${store:-}" ]; then
    rc=0
    timeout 120 "$BIN/l4sbm11" dump "$d/col/gen2" >"$d/dump.nq" 2>"$d/dump.err" || rc=$?
    if [ "$rc" -ne 0 ]; then store=fail; stored="dump exit $rc: $(tail -1 "$d/dump.err" | cut -c1-200)"; fi
  fi
  if [ -z "${store:-}" ]; then
    out="$("$BIN/l4sbm11-w3c" compare "$d/expected.nq" "$d/dump.nq" --expected nq --mode rdf11 2>&1)" || true
    case "$out" in
      pass*) store=pass; stored="$(grep -o 'where path=[a-z]*' "$d/update.log" | sort | uniq -c | tr '\n' ' ' | sed 's/  */ /g; s/ *$//')"; [ -n "$stored" ] || stored=- ;;
      *) store=fail; stored="$(printf '%s' "$out" | head -1 | cut -c1-240)" ;;
    esac
  fi
  if [ -n "${W3C_UPDATE_KEEP:-}" ] && [ "$store" = fail ]; then
    mkdir -p "$W3C_UPDATE_KEEP/$idx"; cp -r "$d/." "$W3C_UPDATE_KEEP/$idx/" 2>/dev/null || true
  fi
  rm -rf "$d/col"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$idx" "$suite" "$entry" "$name" "$ref" "$refd" "$store" "$stored"
}
export -f run_row
export TMP BIN

echo "=== $total_rows update evaluation tests from $(echo "$SUITES" | wc -w) manifests, $JOBS in parallel"
t0=$SECONDS
tr '\n' '\0' <"$TMP/rows.tsv" | xargs -0 -P "$JOBS" -I{} bash -c 'run_row "$1"' _ {} >"$TMP/results.tsv"
echo "=== ran in $((SECONDS - t0)) s"
done_rows="$(wc -l <"$TMP/results.tsv")"
if [ "$done_rows" -ne "$total_rows" ]; then
  echo "FAIL: $done_rows results for $total_rows tests" >&2
  exit 1
fi
[ -n "${W3C_UPDATE_RESULTS:-}" ] && cp "$TMP/results.tsv" "$W3C_UPDATE_RESULTS"

# ---- 3. the report
python3 -I - "$TMP/results.tsv" "$XFAIL_TABLE" "$SUITES" <<'PY'
import sys

results_path, xfail_path, suites_arg = sys.argv[1], sys.argv[2], sys.argv[3]
order = suites_arg.split()
xfail = {}
for ln, line in enumerate(open(xfail_path, encoding="utf-8"), 1):
    line = line.rstrip("\n")
    if not line or line.startswith("#"):
        continue
    f = line.split("\t")
    if len(f) != 4 or not f[2].startswith("https://github.com/danbri/factoidal/issues/"):
        sys.exit(f"{xfail_path}:{ln}: expected suite, entry, issue URL, reason")
    xfail[(f[0], f[1])] = (f[2], f[3])

rows = {}
for line in open(results_path, encoding="utf-8"):
    f = line.rstrip("\n").split("\t")
    idx, suite, entry, name, ref, refd, store, stored = f
    rows.setdefault(suite, []).append((int(idx), entry, name, ref, refd, store, stored))

seen_x = set()
tot = dict(sp=0, sf=0, sx=0, ss=0, rp=0, rf=0, rs=0, n=0)
only_store, both_fail, xpass = [], [], []
for suite in order:
    rs = sorted(rows.get(suite, []))
    sp = sf = sx = ss = rp = rf = rsk = 0
    for idx, entry, name, ref, refd, store, stored in rs:
        key = (suite, entry)
        entry_x = xfail.get(key)
        if ref == "pass": rp += 1
        elif ref == "fail": rf += 1
        else: rsk += 1
        if store == "skip":
            ss += 1
            continue
        if entry_x:
            seen_x.add(key)
            if store == "pass":
                xpass.append((suite, entry, entry_x[0]))
                sf += 1
            else:
                sx += 1
            continue
        if store == "pass":
            sp += 1
        else:
            sf += 1
            if ref == "pass":
                only_store.append((suite, entry, name, stored))
            else:
                both_fail.append((suite, entry, name, stored, refd))
    n = len(rs)
    sx_txt = f", {sx} expected-fail" if sx else ""
    print(f"{suite}: store: {sp} pass, {sf} fail{sx_txt}, {ss} skip (out of {n}); reference: {rp} pass, {rf} fail, {rsk} skip (out of {n})")
    for k, v in (("sp", sp), ("sf", sf), ("sx", sx), ("ss", ss), ("rp", rp), ("rf", rf), ("rs", rsk), ("n", n)):
        tot[k] += v

print()
bad = 0
if only_store:
    bad += len(only_store)
    print(f"store-only failures (the reference passes, the store fails): {len(only_store)}")
    for s, e, n, d in only_store:
        print(f"  FAIL {s} {e} ({n}): {d}")
if both_fail:
    print(f"failures of both (the reference fails too, not a gate failure): {len(both_fail)}")
    for s, e, n, d, rd in both_fail:
        print(f"  both-fail {s} {e} ({n}): store: {d}; reference: {rd}")
if xpass:
    bad += len(xpass)
    print(f"UNEXPECTED PASS (remove the row and close the issue): {len(xpass)}")
    for s, e, i in xpass:
        print(f"  XPASS {s} {e} ({i})")
missing = [k for k in xfail if k not in seen_x]
if missing:
    bad += len(missing)
    print(f"rows of the expected-failure table that match no test: {len(missing)}")
    for s, e in missing:
        print(f"  STALE {s} {e}")
by_issue = {}
for (s, e), (issue, reason) in xfail.items():
    if (s, e) in seen_x:
        by_issue.setdefault(issue, []).append((s, e))
for issue, tests in by_issue.items():
    print(f"expected-fail: {len(tests)} tests, {issue}: " + ", ".join(f"{s}/{e}" for s, e in tests))
print(f"w3c update: store: {tot['sp']} pass, {tot['sf']} fail, {tot['sx']} expected-fail, {tot['ss']} skip (out of {tot['n']}); "
      f"reference: {tot['rp']} pass, {tot['rf']} fail, {tot['rs']} skip (out of {tot['n']})")
sys.exit(1 if bad else 0)
PY
