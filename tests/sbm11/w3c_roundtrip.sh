#!/usr/bin/env bash
#
# tests/sbm11/w3c_roundtrip.sh -- the W3C RDF tests through the SBM11 store
# (https://github.com/danbri/factoidal/issues/837 item 5).
#
# For every positive evaluation test of the W3C RDF suites under
# third_party/testing/w3c/rdf (Turtle, TriG and RDF/XML evaluation tests, and the
# N-Triples and N-Quads canonicalisation tests of RDF 1.2; RDF 1.1 and RDF 1.2
# manifests) and of the JSON-LD 1.1 toRdf manifest (third_party/testing/json-ld):
#
#   1. the manifest is read from disk (`l4sbm11-w3c list-rdf`, `list-jsonld`; the
#      manifest reader of the Lean W3C runner, `Harness.loadManifest`), which gives
#      the action, the result file and the base IRI the manifest states for the test
#      (`mf:assumedTestBase` + the path of the action; for JSON-LD `option.base`,
#      else `baseIri` + `input`);
#   2. STORE: `l4sbm11-pack ACTION GEN --format F --base BASE`, `l4sbm11 verify
#      GEN` (the activation checks), `l4sbm11 dump GEN`, and the dump is compared
#      with the result file by RDF dataset isomorphism (`l4sbm11-w3c compare`, which
#      uses `Dataset.isomorphicOutcome`, the comparison of the Lean W3C runners);
#      language tags compare in lower case (RDF 1.1 Concepts section 3.3; the
#      packer folds them), lexical forms exactly, blank nodes up to a bijection;
#   3. PARSER: the same parse without the store, `Source.parseDocument` on the
#      action with the same base IRI and the RDF version of the manifest, compared
#      with the result file in memory (`l4sbm11-w3c check-parse`).
#
# Nine empty documents (one or more of each syntax) run as well: an empty dataset must
# pack to a valid generation that holds no quad (suite "Empty documents").
#
# With SYNTAX=1 (the default) the positive syntax tests of the N-Triples,
# N-Quads, Turtle and TriG manifests and of JSON-LD run too. They have no result
# file: the expected dataset is the one the parser gives (`l4sbm11-w3c
# compare-source`), so the comparison is store against parser.
#
# Prints, for each suite, "store: N pass, M fail, K expected-fail (out of T);
# parser: N pass, M fail, K expected-fail (out of T)", then the store-only
# failures (a test that the parser passes and the store fails), and the total:
#
#   w3c round trip: N pass, M fail, K expected-fail (out of T)
#
# The numbers of the total are the STORE's, with a failure for every test the
# parser passes and the store fails, and for every expected failure that passes.
# An expected failure is a row of tests/sbm11/w3c_roundtrip_xfail.tsv: suite,
# test name, route (`store` or `both`: the store fails and the parser passes or
# fails too), the URL of an open issue, the reason. The row is checked on every
# run: a test in the table that passes in the store is a FAILURE of the run
# ("unexpected pass"), so the table cannot go stale.
#
# Exit status: 0 when no test failed and no expected failure passed; 1 otherwise;
# 2 when a binary or a manifest is missing.
#
# Env: L4_BIN_DIR    directory of the binaries (default formal/lean4/.lake/build/bin)
#      FACTOIDAL_TESTING_ROOT  the directory of the W3C fixtures (default
#                         third_party/testing of this tree)
#      W3C_ROUNDTRIP_JOBS  tests in parallel (default 4)
#      W3C_ROUNDTRIP_SYNTAX  0 leaves the positive syntax tests out
#      W3C_ROUNDTRIP_KEEP    a directory to keep the dumps and logs of the FAILED
#                            tests in
#      W3C_ROUNDTRIP_RESULTS a file to copy the per-test results to (tab separated:
#                            number, suite, test, kind, store, detail, parser,
#                            detail, notes)
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_BIN_DIR:-$ROOT/formal/lean4/.lake/build/bin}"
TESTING="${FACTOIDAL_TESTING_ROOT:-$ROOT/third_party/testing}"
RDF_DIR="$TESTING/w3c/rdf"
JLD_MANIFEST="$TESTING/json-ld/tests/toRdf-manifest.jsonld"
XFAIL_TABLE="$HERE/w3c_roundtrip_xfail.tsv"
JOBS="${W3C_ROUNDTRIP_JOBS:-4}"
SYNTAX="${W3C_ROUNDTRIP_SYNTAX:-1}"
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack" "$BIN/l4sbm11-w3c" "$RDF_DIR/rdf11/rdf-turtle/manifest.ttl" \
            "$JLD_MANIFEST" "$XFAIL_TABLE"; do
  if [ ! -e "$need" ]; then echo "missing: $need (tools/ensure-test-env.sh; lake build)" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-w3c.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
mkdir -p "$TMP/w"

# ---- 1. the tests, from the manifests on disk
syntax_flag=(); [ "$SYNTAX" != 0 ] && syntax_flag=(--syntax)
manifests=()
while IFS= read -r m; do manifests+=("$m"); done < <(
  find "$RDF_DIR/rdf11" "$RDF_DIR/rdf12" -path '*/rdf-n-quads/*' -name manifest.ttl -o \
       -path '*/rdf-n-triples/*' -name manifest.ttl -o -path '*/rdf-trig/*' -name manifest.ttl -o \
       -path '*/rdf-turtle/*' -name manifest.ttl -o -path '*/rdf-xml/*' -name manifest.ttl | sort)
# the manifest of a suite directory itself (rdf11 suites; the rdf12 ones include their leaves)
for d in rdf-n-quads rdf-n-triples rdf-trig rdf-turtle rdf-xml; do
  [ -f "$RDF_DIR/rdf11/$d/manifest.ttl" ] || continue
  case " ${manifests[*]} " in *" $RDF_DIR/rdf11/$d/manifest.ttl "*) ;; *) manifests+=("$RDF_DIR/rdf11/$d/manifest.ttl") ;; esac
done
rc=0
"$BIN/l4sbm11-w3c" list-rdf "${syntax_flag[@]}" "${manifests[@]}" >"$TMP/rows.rdf" 2>"$TMP/rows.rdf.err" || rc=$?
if [ "$rc" -ne 0 ]; then echo "list-rdf failed: $(cat "$TMP/rows.rdf.err")" >&2; exit 2; fi
"$BIN/l4sbm11-w3c" list-jsonld "${syntax_flag[@]}" "$JLD_MANIFEST" >"$TMP/rows.jld" 2>"$TMP/rows.jld.err" || rc=$?
if [ "$rc" -ne 0 ]; then echo "list-jsonld failed: $(cat "$TMP/rows.jld.err")" >&2; exit 2; fi
# Empty documents: a dataset with no quad packs to a valid generation that holds no quad
# (one document of each syntax; these rows are not from a W3C suite).
mkdir -p "$TMP/empty"
: >"$TMP/empty/expected.nq"
: >"$TMP/empty/empty.nt"; : >"$TMP/empty/empty.nq"; : >"$TMP/empty/empty.ttl"; : >"$TMP/empty/empty.trig"
printf '# a comment and nothing else\n' >"$TMP/empty/comment-only.ttl"
printf '{ }\n' >"$TMP/empty/default-graph-block-with-no-triple.trig"
printf '<?xml version="1.0"?>\n<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"/>\n' >"$TMP/empty/empty-rdf-element.rdf"
printf '[]' >"$TMP/empty/empty-array.jsonld"
printf '{}' >"$TMP/empty/empty-object.jsonld"
for spec in empty.nt:nt empty.nq:nquads empty.ttl:turtle comment-only.ttl:turtle empty.trig:trig \
            default-graph-block-with-no-triple.trig:trig empty-rdf-element.rdf:rdfxml \
            empty-array.jsonld:jsonld empty-object.jsonld:jsonld; do
  f="${spec%%:*}"; fmt="${spec##*:}"
  printf 'Empty documents (not from a W3C suite)\t%s\teval\t%s\t%s\thttp://example.org/%s\trdf12\t%s\tnq\t-\n' \
    "$f" "$TMP/empty/$f" "$TMP/empty/expected.nq" "$f" "$fmt"
done >"$TMP/rows.empty"

cat "$TMP/rows.rdf" "$TMP/rows.jld" "$TMP/rows.empty" | awk -F'\t' '{ printf "%d\t%s\n", NR, $0 }' >"$TMP/rows.tsv"
total_rows="$(wc -l <"$TMP/rows.tsv")"
if [ "$total_rows" -lt 100 ]; then echo "only $total_rows tests listed: the manifests were not read" >&2; exit 2; fi

# ---- 2. one test: pack, verify, dump, compare; parse, compare
# Prints one line: idx, suite, name, kind, store (pass|fail), store detail,
# parser (pass|fail), parser detail, notes.
run_row() {
  local idx suite name kind action result base mode fmt expkind notes
  IFS=$'\t' read -r idx suite name kind action result base mode fmt expkind notes <<<"$1"
  local d="$TMP/w/$idx" store sdetail parser pdetail rc
  mkdir -p "$d"
  # store
  rc=0
  timeout 120 "$BIN/l4sbm11-pack" "$action" "$d/gen" --format "$fmt" --base "$base" --workers 1 \
    >"$d/pack.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then
    store=fail; sdetail="pack exit $rc: $(tail -1 "$d/pack.log" | cut -c1-200)"
  else
    rc=0
    timeout 120 "$BIN/l4sbm11" verify "$d/gen" >"$d/verify.log" 2>&1 || rc=$?
    if [ "$rc" -ne 0 ]; then
      store=fail; sdetail="verify exit $rc: $(grep -m1 FAIL "$d/verify.log" | cut -c1-200)"
    else
      rc=0
      timeout 120 "$BIN/l4sbm11" dump "$d/gen" >"$d/dump.nq" 2>"$d/dump.err" || rc=$?
      if [ "$rc" -ne 0 ]; then
        store=fail; sdetail="dump exit $rc: $(tail -1 "$d/dump.err" | cut -c1-200)"
      else
        if [ "$kind" = eval ]; then
          out="$("$BIN/l4sbm11-w3c" compare "$result" "$d/dump.nq" --expected "$expkind" --mode "$mode" 2>&1)" || true
        else
          out="$("$BIN/l4sbm11-w3c" compare-source "$d/dump.nq" "$action" --format "$fmt" --base "$base" --mode "$mode" 2>&1)" || true
        fi
        case "$out" in
          pass*) store=pass; sdetail="$out" ;;
          *) store=fail; sdetail="$(printf '%s' "$out" | head -1 | cut -c1-240)" ;;
        esac
      fi
    fi
  fi
  # parser
  if [ "$kind" = eval ]; then
    out="$("$BIN/l4sbm11-w3c" check-parse "$action" "$result" --format "$fmt" --base "$base" --expected "$expkind" \
           --mode "$mode" 2>&1)" || true
    case "$out" in
      pass*) parser=pass; pdetail="$out" ;;
      *) parser=fail; pdetail="$(printf '%s' "$out" | head -1 | cut -c1-240)" ;;
    esac
  else
    out="$("$BIN/l4sbm11-w3c" parse-ok "$action" --format "$fmt" --base "$base" --mode "$mode" 2>&1)" || true
    case "$out" in
      pass*) parser=pass; pdetail="parses" ;;
      *) parser=fail; pdetail="$(printf '%s' "$out" | head -1 | cut -c1-240)" ;;
    esac
  fi
  if [ -n "${W3C_ROUNDTRIP_KEEP:-}" ] && { [ "$store" = fail ] || [ "$parser" = fail ]; }; then
    mkdir -p "$W3C_ROUNDTRIP_KEEP/$idx"; cp -r "$d/." "$W3C_ROUNDTRIP_KEEP/$idx/" 2>/dev/null || true
  fi
  rm -rf "$d/gen"
  printf '%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\t%s\n' "$idx" "$suite" "$name" "$kind" "$store" "$sdetail" \
    "$parser" "$pdetail" "$notes"
}
export -f run_row
export TMP BIN

echo "=== $total_rows tests from $(echo "${manifests[@]}" | wc -w) RDF manifests, the JSON-LD toRdf manifest and 9 empty documents, $JOBS in parallel"
t0=$SECONDS
tr '\n' '\0' <"$TMP/rows.tsv" | xargs -0 -P "$JOBS" -I{} bash -c 'run_row "$1"' _ {} >"$TMP/results.tsv"
echo "=== ran in $((SECONDS - t0)) s"
done_rows="$(wc -l <"$TMP/results.tsv")"
if [ "$done_rows" -ne "$total_rows" ]; then
  echo "FAIL: $done_rows results for $total_rows tests" >&2
  exit 1
fi

[ -n "${W3C_ROUNDTRIP_RESULTS:-}" ] && cp "$TMP/results.tsv" "$W3C_ROUNDTRIP_RESULTS"

# ---- 3. the report
python3 -I - "$TMP/results.tsv" "$XFAIL_TABLE" <<'PY'
import sys
from collections import OrderedDict

results_path, xfail_path = sys.argv[1], sys.argv[2]
xfail = {}
for ln, line in enumerate(open(xfail_path, encoding="utf-8"), 1):
    line = line.rstrip("\n")
    if not line or line.startswith("#"):
        continue
    f = line.split("\t")
    if len(f) != 5 or f[2] not in ("store", "both") or not f[3].startswith("https://github.com/danbri/factoidal/issues/"):
        sys.exit(f"{xfail_path}:{ln}: expected suite, name, route (store|both), issue URL, reason")
    xfail[(f[0], f[1])] = (f[2], f[3], f[4])

suites = OrderedDict()
for line in open(results_path, encoding="utf-8"):
    f = line.rstrip("\n").split("\t")
    idx, suite, name, kind, store, sdet, parser, pdet, notes = f
    suites.setdefault(suite, []).append((int(idx), name, kind, store, sdet, parser, pdet, notes))

seen_x = set()
total = {"pass": 0, "fail": 0, "xfail": 0}
only_store, both_fail_unlisted, xpass, stale = [], [], [], []
for suite, rows in suites.items():
    rows.sort()
    sp = sf = sx = pp = pf = px = 0
    for idx, name, kind, store, sdet, parser, pdet, notes in rows:
        key = (suite, name)
        entry = xfail.get(key)
        if entry:
            seen_x.add(key)
            route, issue, reason = entry
            if store == "pass":
                xpass.append((suite, name, issue))
                sf += 1
            else:
                sx += 1
            if route == "store" and parser != "pass":
                stale.append((suite, name, "route store, but the parser fails: " + pdet))
            if parser == "pass":
                pp += 1
            elif route == "both":
                px += 1
            else:
                pf += 1
            continue
        if store == "pass":
            sp += 1
        else:
            sf += 1
            if parser == "pass":
                only_store.append((suite, name, sdet))
            else:
                both_fail_unlisted.append((suite, name, sdet, pdet))
        if parser == "pass":
            pp += 1
        else:
            pf += 1
    n = len(rows)
    total["pass"] += sp; total["fail"] += sf; total["xfail"] += sx
    sx_txt = f", {sx} expected-fail" if sx else ""
    px_txt = f", {px} expected-fail" if px else ""
    print(f"{suite}: store: {sp} pass, {sf} fail{sx_txt} (out of {n}); parser: {pp} pass, {pf} fail{px_txt} (out of {n})")

print()
bad = 0
if only_store:
    bad += len(only_store)
    print(f"store-only failures (the parser passes, the store fails): {len(only_store)}")
    for s, n, d in only_store:
        print(f"  FAIL {s} {n}: {d}")
if both_fail_unlisted:
    bad += len(both_fail_unlisted)
    print(f"failures in both routes with no row in {xfail_path.split('/')[-1]}: {len(both_fail_unlisted)}")
    for s, n, d, pd in both_fail_unlisted:
        print(f"  FAIL {s} {n}: store: {d}; parser: {pd}")
if xpass:
    bad += len(xpass)
    print(f"UNEXPECTED PASS (remove the row and close the issue): {len(xpass)}")
    for s, n, i in xpass:
        print(f"  XPASS {s} {n} ({i})")
missing = [k for k in xfail if k not in seen_x]
if missing:
    bad += len(missing)
    print(f"rows of the expected-failure table that match no test: {len(missing)}")
    for s, n in missing:
        print(f"  STALE {s} {n}")
if stale:
    bad += len(stale)
    for s, n, d in stale:
        print(f"  STALE route {s} {n}: {d}")
by_issue = {}
for (s, n), (route, issue, reason) in xfail.items():
    if (s, n) in seen_x:
        by_issue.setdefault(issue, []).append((s, n))
for issue, tests in by_issue.items():
    print(f"expected-fail: {len(tests)} tests, {issue}")
t = sum(len(r) for r in suites.values())
print(f"w3c round trip: {total['pass']} pass, {total['fail']} fail, {total['xfail']} expected-fail (out of {t})")
sys.exit(1 if total["fail"] or bad else 0)
PY
