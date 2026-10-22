#!/usr/bin/env bash
# Known-defect regression suite — XFAIL semantics.
#
# Every case here reproduces a defect we have FOUND, PROVED and FILED but
# not yet fixed. The point is not to hide them behind a green number: it
# is to make each one a standing, executable claim that can only change
# state deliberately.
#
#   XFAIL  the defect still reproduces      — expected, suite stays green
#   XPASS  the defect did NOT reproduce     — 🔴 SUITE FAILS ON PURPOSE
#   ERROR  the probe itself broke           — 🔴 suite fails
#
# An XPASS is not good news to be silently absorbed. It means either
# somebody fixed the defect (delete the case, close the issue, and say so
# in the same commit) or the probe has drifted and stopped measuring what
# it claims to. Both need a human. A suite that quietly turned green
# would be exactly the "green means we did not do the work" failure mode
# these tests exist to prevent (anti-pattern #3).
#
# Output: human table on stdout, machine-readable JSON to
# docs/test-results/by-suite/known-defects.json.
#
# Binaries. A row may use only the programs that the factoidal-builds workflow
# installs for this suite (job web-gates, step "Known defects", in
# .github/workflows/build.yml of danbri/factoidal-builds), all in one directory:
# `factoidal` and `owl_runner` (F*), `l4factoidal` and `l4w3c` (Lean). A row that
# starts another program (l4sbm11, l4sbm11-pack, l4source-convert, l4diff, ...)
# records ERROR in CI, the step fails, and the web set is not published. A row that
# needs a function which only another program has needs that function in
# `l4factoidal` first. Cost of not having this rule: on 2026-10-14 the row
# JLD-WSTACK (removed 2026-10-18 with the repair of issue 853) started `l4sbm11` and `l4sbm11-pack`; the step failed in three
# scheduled runs of danbri/factoidal-builds (runs 72, 73 and 74, 2026-10-14 18:42
# UTC to 2026-10-15 00:36 UTC) and the web set was not published for any of them.
# Before a change to this file lands, run it in the CI layout: a directory that
# holds only those four programs, with FACTOIDAL_BIN and L4FACTOIDAL_BIN pointing
# into it (skills/test-suites/SKILL.md, Expected failures).
#
# Usage:  tests/known-defects/run.sh [--json-only]

set -uo pipefail   # NOT -e: a failing probe is data, not a crash.

ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
BIN="${FACTOIDAL_BIN:-${ROOT}/bin/linux-x86_64/factoidal}"
# The OWL cases below drive the F* owl_runner (the only F* command line that
# reaches Tableau_Refute.tableau_consistent) and use the Lean CLI as the
# oracle that states the correct answer. Both ship in the same directory as
# `factoidal` (tools/fetch-builds.sh --set native).
OWL_BIN="${OWL_RUNNER_BIN:-$(dirname "$BIN")/owl_runner}"
L4_BIN="${L4FACTOIDAL_BIN:-$(dirname "$BIN")/l4factoidal}"
FIXTURES="${ROOT}/tests/known-defects/fixtures"
JSON_OUT="${ROOT}/docs/test-results/by-suite/known-defects.json"
WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/factoidal-known-defects-XXXXXX")"
trap 'rm -rf "${WORKDIR}"' EXIT

JSON_ONLY=0
[ "${1:-}" = "--json-only" ] && JSON_ONLY=1

XFAIL=0; XPASS=0; ERRORS=0
ROWS=()

# record ID ISSUE TITLE STATE DETAIL
record () {
  local id="$1" issue="$2" title="$3" state="$4" detail="$5"
  case "$state" in
    XFAIL) XFAIL=$((XFAIL+1)) ;;
    XPASS) XPASS=$((XPASS+1)) ;;
    *)     ERRORS=$((ERRORS+1)) ;;
  esac
  ROWS+=("$(printf '{"id":"%s","issue":"%s","title":"%s","state":"%s","detail":"%s"}' \
            "$id" "$issue" "$title" "$state" "${detail//\"/\\\"}")")
  [ "$JSON_ONLY" = "1" ] && return 0
  local mark="  "
  [ "$state" = "XPASS" ] && mark="🔴"
  [ "$state" = "ERROR" ] && mark="🔴"
  printf '%s %-6s  %-7s  %-52s  %s\n' "$mark" "$state" "#$issue" "$title" "$detail"
}

if [ ! -x "$BIN" ]; then
  echo "known-defects: no binary at $BIN" >&2
  exit 2
fi

[ "$JSON_ONLY" = "1" ] || {
  printf '\n=== Known defects — XFAIL suite ===\n'
  printf '   XFAIL = defect still present (expected).  XPASS = defect gone, UPDATE THIS TEST.\n\n'
}

# ---------------------------------------------------------------------
# SR-1 (https://github.com/danbri/factoidal/issues/336, closed 2026-08-04)
# and SR-2 (https://github.com/danbri/factoidal/issues/337, closed
# 2026-08-04) are RETIRED, not removed silently. Both read XPASS on native
# build 5dca271e756e and the issues are closed as completed.
#   SR-1  SELECT DISTINCT returned duplicate rows when two UNION arms
#         built the same solution mapping with bindings in a different order.
#   SR-2  OPTIONAL missed a match the same BGP found, for literals that
#         differ only in language-tag case ("x"@en and "x"@EN).
# ---------------------------------------------------------------------

# ---------------------------------------------------------------------
# SE-1 (#324) -- rdf_term_eq case-folds language tags where the spec says
# TERM IDENTITY. The entailment surface is not reachable from the CLI (the
# `entail` verb materializes a closure, it does not check a conclusion), so
# probe the SAME root cause where it IS reachable: sameTerm. SPARQL 1.1
# s17.4.1.1 defines sameTerm as RDF term identity, and RDF 1.1 Concepts
# s3.3 makes two literals identical only if their language tags are the
# same string -- BCP47 case-insensitivity governs matching, not identity.
# ---------------------------------------------------------------------
cat > "${WORKDIR}/se1.ttl" <<'EOF'
@prefix : <http://ex.org/> .
:a :p "x"@en .
:b :p "x"@EN .
EOF
cat > "${WORKDIR}/se1.rq" <<'EOF'
PREFIX : <http://ex.org/>
SELECT * WHERE { ?a :p ?v1 . ?b :p ?v2 FILTER(?a != ?b && sameTerm(?v1,?v2)) }
EOF
SE1_N=$("$BIN" query --data "${WORKDIR}/se1.ttl" --query "${WORKDIR}/se1.rq" 2>/dev/null \
        | grep -c '"x"@' )
if [ "${SE1_N:-0}" -gt 0 ]; then
  record SE-1 324 "sameTerm case-folds language tags (term identity)" XFAIL \
    "sameTerm(\"x\"@en,\"x\"@EN) is TRUE; identity says they differ"
else
  record SE-1 324 "sameTerm case-folds language tags (term identity)" XPASS \
    "sameTerm now distinguishes tag case -- defect appears FIXED"
fi

# ---------------------------------------------------------------------
# RS-1 (#335) -- FIXED 2026-07-31, case removed.
#
# collect_classes/collect_properties are now split by regime: the RDFS
# harvest reads only what RDF 1.1 Semantics s9 licenses, the wide OWL
# reading moved to owl_reflexivity_axioms behind
# owl_rdfs_closure_with_reflexivity. Verified against the rebuilt binary:
# a graph asserting `:X rdf:type owl:Class` yields NO `:X rdfs:subClassOf
# :X` under --regime RDFS, and still does under --regime OWL-RL where the
# wide harvest is sound.
#
# ⚠️ DO NOT re-add the probe that was here. It fed `:C rdfs:subClassOf :D`
# and asserted that deriving `:C rdfs:subClassOf :C` was unsound. It is
# NOT: s9's condition table puts both endpoints of an rdfs:subClassOf
# triple in IC, and rdfs10 makes every class a subclass of itself, so that
# derivation is licensed. The probe was testing correct behaviour and
# would have XFAILed forever. The real witness needs an OWL typing IRI,
# which is what the F* witness used.
# ---------------------------------------------------------------------

# ---------------------------------------------------------------------
# TTL-PFX (https://github.com/danbri/factoidal/issues/334, closed
# 2026-08-18) is RETIRED, not removed silently. It read XPASS on native
# build 5dca271e756e and the issue is closed as completed. It recorded that
# Turtle silently dropped a statement that used an undeclared prefix and
# exited 0; the document is now rejected.
# ---------------------------------------------------------------------

# ---------------------------------------------------------------------
# JSONLD-MSG — one disjunctive error string covers BOTH a JSON syntax
# error and an unresolvable remote @context, so a user cannot tell a typo
# from an unimplemented feature. Recorded in tests/did-local/README.md.
# Probe: a document with an INLINE context and a syntax error must not
# mention remote contexts.
# ---------------------------------------------------------------------
cat > "${WORKDIR}/badsyntax.jsonld" <<'EOF'
{"@context":{"name":"http://schema.org/name"},"@id":"http://ex.org/1",
 "vm":[{"a":1},{"b":2},
 "name":"Alice"}
EOF
J_OUT=$("$BIN" jsonld --in "${WORKDIR}/badsyntax.jsonld" 2>&1)
if echo "$J_OUT" | grep -q "remote context"; then
  record JSONLD-MSG 275 "syntax error and missing loader share one message" XFAIL \
    "inline-context syntax error still blamed on remote contexts"
elif [ -n "$J_OUT" ]; then
  record JSONLD-MSG 275 "syntax error and missing loader share one message" XPASS \
    "message no longer mentions remote contexts — appears FIXED"
else
  record JSONLD-MSG 275 "syntax error and missing loader share one message" ERROR \
    "malformed JSON-LD produced no error at all"
fi

# ---------------------------------------------------------------------
# NT-ESC (#339) is RETIRED, not removed silently.
#
# It recorded that `RDF.Pretty.term_to_ntriples` escaped nothing, so the
# `dump` verb emitted N-Triples our own parser rejected. Fixed 2026-08-14
# together with issue #443, which found the same function feeding the
# COTTAS store's object column -- so the defect was not display-only: an
# import -> query round trip destroyed every literal containing a quote,
# a newline or a backslash.
#
# The function was deleted rather than patched (a second name for the
# same rendering is what let the two drift), and the standing pin moved
# to tests/local/cli_literal_escape_roundtrip.sh, which covers six
# literal classes on both the `--dump` and the store paths and carries
# an anti-vacuity arm. This file is for defects that still reproduce;
# a fixed one belongs in a regression pin, not here.
# ---------------------------------------------------------------------

# ---------------------------------------------------------------------
# UTF8-STORE (#445) is RETIRED, not removed silently.
#
# It recorded that RDF.Bytes.bytes_of_string used String.list_of_string
# (raw CODEPOINTS) as if it already returned bytes, so every codepoint
# >= 256 was truncated (`codepoint land 0xFF`) on the way to the COTTAS
# store: "café" came back mojibake, CJK/emoji literals came back
# destroyed, and the sharpest case -- 日本語's U+672C truncating to byte
# 0x2C, a literal COMMA -- could change how a token PARSED, not only
# what it said. Fixed 2026-08-15: RDF.Bytes.bytes_of_string/
# bytes_to_string reimplemented on Parser.FastString.Spec's proved
# UTF-8 codec (no second hand-written encoder, per the #443 lesson),
# with a proved round-trip lemma
# (`lemma_bytes_to_string_of_bytes_of_string : s:string -> Lemma
# (bytes_to_string (bytes_of_string s) == s)`, unconditional -- no
# ASCII-only hypothesis). Four length-prefix sites in
# RDF.CottasStore.BaseWriter.fst that used the same wrong codepoint
# count as a byte length were fixed alongside it (one of the four,
# write_dict_entry, plus the DLBA length-block computation in
# string_lengths, were found during the fix, beyond the issue's
# original 3-site list -- both are live in the current `import` write
# path, not just the metadata sites the issue named). Two sibling
# on-disk-format modules that share RDF.Bytes primitives
# (RDF.Store.Columnar.DeltaLog.fst, the durable-UPDATE delta log, and
# RDF.CottasStore.DictWriter.fst, an unused legacy .dict writer) had
# the identical latent defect, surfaced as build failures by the type
# fix rather than found by inspection; both fixed the same way. The
# COTTAS base-file format version was bumped (owner decision,
# 2026-08-15: no migration path) so a store written by the pre-fix
# writer is rejected by the reader rather than silently misread.
#
# The standing pin moved to tests/local/cli_literal_escape_roundtrip.sh,
# which now covers the four non-ASCII cases (café, λόγος, 日本語, an
# emoji outside the BMP) alongside its existing six escape-class
# literals, compared through -o json per the same anti-vacuity
# discipline #443's pin established. This file is for defects that
# still reproduce; a fixed one belongs in a regression pin, not here.
# ---------------------------------------------------------------------

# ---------------------------------------------------------------------
# F* OWL tableau and Turtle serializer defects found by the Lean tree
# (issues 719, 720, 725; opened 2026-10-10 from the Lean repairs).
#
# Each case states the CORRECT answer by running the Lean engine on the same
# input, so a case documents what the answer should be as well as what the
# F* binary does. The case is XFAIL when F* gives the wrong answer and Lean
# the right one. Lean not giving the right answer is an ERROR: the case
# would then be recording a wrong expectation.
#
# OWL verdict path for F*: `owl_runner --regime dl CATALOG.rdf`, which runs
# the premise as an OWL 2 ConsistencyTest through the RL closure and then
# Tableau_Refute.tableau_consistent. It prints one line per test:
#   "  PASS  <id>"                          no clash found (consistent)
#   "  FAIL/unexpected-inconsistency  <id>" the refuter closed every branch
# Any other result (unsupported, parse failure, timeout) is an ERROR.
# Lean verdict path: `l4factoidal owl-consistent FILE --format rdfxml`,
# which prints true, false or unknown on stdout.
# ---------------------------------------------------------------------

# fstar_owl_verdict FILE -> CONSISTENT | INCONSISTENT | OTHER:<what was seen>
# Wraps the RDF/XML ontology FILE as the premise of a one-test catalog.
fstar_owl_verdict () {
  local file="$1" catalog out rc
  catalog="${WORKDIR}/catalog-$(basename "$file")"
  {
    # The premise text must start at the first byte after the opening tag
    # (its XML declaration is only legal there), so the head has no final
    # newline: command substitution strips it.
    printf '%s' "$(cat <<'CATALOG_HEAD'
<?xml version="1.0" encoding="UTF-8"?>
<rdf:RDF xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"
         xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"
         xmlns:owl="http://www.w3.org/2002/07/owl#"
         xmlns:test="http://www.w3.org/2007/OWL/testOntology#">
  <owl:Ontology/>
  <test:TestCase rdf:about="http://owl.semanticweb.org/id/Known-2Ddefect">
    <rdf:type rdf:resource="http://www.w3.org/2007/OWL/testOntology#ConsistencyTest"/>
    <test:identifier rdf:datatype="http://www.w3.org/2001/XMLSchema#string">known-defect</test:identifier>
    <test:normativeSyntax rdf:resource="http://www.w3.org/2007/OWL/testOntology#RDFXML"/>
    <test:status rdf:resource="http://www.w3.org/2007/OWL/testOntology#Approved"/>
    <test:semantics rdf:resource="http://www.w3.org/2007/OWL/testOntology#DIRECT"/>
    <test:species rdf:resource="http://www.w3.org/2007/OWL/testOntology#DL"/>
    <test:rdfXmlPremiseOntology rdf:datatype="http://www.w3.org/2001/XMLSchema#string">
CATALOG_HEAD
)"
    sed -e 's/&/\&amp;/g' -e 's/</\&lt;/g' -e 's/>/\&gt;/g' "$file"
    cat <<'CATALOG_TAIL'
</test:rdfXmlPremiseOntology>
  </test:TestCase>
</rdf:RDF>
CATALOG_TAIL
  } > "$catalog"
  out=$(timeout 120 "$OWL_BIN" --regime dl "$catalog" 2>/dev/null); rc=$?
  if printf '%s\n' "$out" | grep -q '^  PASS  known-defect$'; then
    echo CONSISTENT
  elif printf '%s\n' "$out" | grep -q '^  FAIL/unexpected-inconsistency  known-defect$'; then
    echo INCONSISTENT
  else
    echo "OTHER:exit ${rc}, $(printf '%s\n' "$out" | grep -E '^  (PASS|FAIL|SKIP|UNSUPPORTED)' | sed -n '1p')"
  fi
}

# lean_owl_verdict FILE -> true | false | unknown | OTHER:<exit code>
lean_owl_verdict () {
  local out rc
  out=$(timeout 120 "$L4_BIN" owl-consistent "$1" --format rdfxml 2>/dev/null); rc=$?
  case "$out" in
    true|false|unknown) echo "$out" ;;
    *) echo "OTHER:exit ${rc}" ;;
  esac
}

OWL_PROBE_ERR=""
[ -x "$OWL_BIN" ] || OWL_PROBE_ERR="no owl_runner at ${OWL_BIN} (tools/fetch-builds.sh --set native)"
[ -x "$L4_BIN" ]  || OWL_PROBE_ERR="no l4factoidal at ${L4_BIN} (tools/fetch-builds.sh --set native)"

# Sensitivity control. An OWL case reads XPASS when the F* probe reports
# "consistent", and that is also what a probe reports when it sees nothing at
# all (an empty premise, a runner that stopped consulting the tableau). The
# control is an ontology both engines must call INCONSISTENT; if the F* probe
# does not, every OWL case below is an ERROR, not an XPASS.
if [ -z "$OWL_PROBE_ERR" ]; then
  CTL_F=$(fstar_owl_verdict "${FIXTURES}/owl-control-inconsistent.rdf")
  CTL_L=$(lean_owl_verdict "${FIXTURES}/owl-control-inconsistent.rdf")
  if [ "$CTL_F" != "INCONSISTENT" ] || [ "$CTL_L" != "false" ]; then
    OWL_PROBE_ERR="sensitivity control owl-control-inconsistent.rdf: F* probe ${CTL_F}, Lean ${CTL_L} (both must report inconsistent)"
  fi
fi

# owl_case ID ISSUE TITLE FILE
# FILE is an ontology that is CONSISTENT under the OWL 2 Direct Semantics.
owl_case () {
  local id="$1" issue="$2" title="$3" file="${FIXTURES}/$4" fv lv
  if [ -n "$OWL_PROBE_ERR" ]; then
    record "$id" "$issue" "$title" ERROR "$OWL_PROBE_ERR"
    return 0
  fi
  fv=$(fstar_owl_verdict "$file")
  lv=$(lean_owl_verdict "$file")
  if [ "$lv" != "true" ]; then
    record "$id" "$issue" "$title" ERROR \
      "Lean oracle answered ${lv}, not true; the expectation 'consistent' is unconfirmed"
  elif [ "$fv" = "INCONSISTENT" ]; then
    record "$id" "$issue" "$title" XFAIL \
      "F* reports inconsistent; Lean reports consistent (correct)"
  elif [ "$fv" = "CONSISTENT" ]; then
    record "$id" "$issue" "$title" XPASS \
      "F* now reports consistent, as Lean does -- defect appears FIXED"
  else
    record "$id" "$issue" "$title" ERROR "F* probe: ${fv}"
  fi
}

# 719: the filler of a qualified cardinality restriction is read from
# owl:onClass only, so owl:onDataRange is ignored.
owl_case OWL-719 719 "F* ignores owl:onDataRange in qualified cardinality" \
  owl-719-data-max-qualified.rdf

# 720: the <=-rule branches only over pairs of anonymous witnesses, so it
# offers too few merges and refutes a consistent ontology. Two shapes.
owl_case OWL-720-DATA 720 "F* <=-rule offers no merge with asserted data values" \
  owl-720-data-leq2.rdf
owl_case OWL-720-NAMED 720 "F* <=-rule offers no merge with named individuals" \
  owl-720-named-leq2.rdf

# 725: RDF_Turtle_Serialize.count_runs recurses once per IRI occurrence and is
# not tail recursive, so Turtle output of a large graph overflows the stack.
# Input: the header and 40000 paragraphs of the Wikidata life-science gene.ttl,
# every fifth paragraph from the start (deterministic; no blank nodes, so the
# N-Triples of the input and of a correct re-serialisation are the same set).
# The stack limit of the F* run is pinned at 8192 KB so the result does not depend
# on the caller's shell. Correct answer: Lean serialises the same input to Turtle
# that parses back to the same triples. The Lean run is pinned at 512 KB
# (LEAN_STACK_SIZE_KB=512), 16 times less than the F* run, because the Lean writer
# had the same defect until 2026-10-15 (TurtleSerialize.countRuns, issue 863: 2,711
# triples overflowed 512 KB), and without the pin the oracle ran on the 1 GB default
# thread stack of a Lean program, which compares two different stack sizes.
GENE_SRC="${ROOT}/examples/wikidata/subsets/lifesci-kgx/data/gene.ttl"
TS_ID=TTL-SER-725; TS_ISSUE=725; TS_TITLE="F* Turtle serializer overflows the stack at 40k paragraphs"
if [ ! -r "$GENE_SRC" ]; then
  record "$TS_ID" "$TS_ISSUE" "$TS_TITLE" ERROR "no input file ${GENE_SRC#"$ROOT"/}"
elif [ ! -x "$L4_BIN" ]; then
  record "$TS_ID" "$TS_ISSUE" "$TS_TITLE" ERROR "no l4factoidal at ${L4_BIN} (tools/fetch-builds.sh --set native)"
else
  TS_IN="${WORKDIR}/gene-40000.ttl"
  awk -v want=40000 'BEGIN { RS = ""; ORS = "\n\n" }
       NR == 1 { print; next }
       { if ((NR - 2) % 5 == 0 && picked < want) { picked++; print } }' \
      "$GENE_SRC" > "$TS_IN"
  TS_PARAS=$(awk 'BEGIN { RS = "" } END { print NR - 1 }' "$TS_IN")
  ( ulimit -s 8192 && timeout 300 "$BIN" dump-turtle "$TS_IN" > "${WORKDIR}/ts-fstar.ttl" 2> "${WORKDIR}/ts-fstar.err" )
  TS_RC=$?
  TS_LEAN_RC=0
  env -u LEAN_MAIN_USE_THREAD LEAN_STACK_SIZE_KB=512 timeout 300 "$L4_BIN" parse "$TS_IN" --format turtle --out turtle \
      > "${WORKDIR}/ts-lean.ttl" 2> "${WORKDIR}/ts-lean.err" || TS_LEAN_RC=$?
  TS_SAME=no
  if [ "$TS_LEAN_RC" -eq 0 ]; then
    LC_ALL=C "$BIN" dump "$TS_IN" 2>/dev/null | LC_ALL=C sort -u > "${WORKDIR}/ts-in.nt"
    LC_ALL=C "$BIN" dump "${WORKDIR}/ts-lean.ttl" 2>/dev/null | LC_ALL=C sort -u > "${WORKDIR}/ts-lean.nt"
    if [ -s "${WORKDIR}/ts-in.nt" ] && cmp -s "${WORKDIR}/ts-in.nt" "${WORKDIR}/ts-lean.nt"; then TS_SAME=yes; fi
  fi
  if [ "$TS_PARAS" != "40000" ]; then
    record "$TS_ID" "$TS_ISSUE" "$TS_TITLE" ERROR \
      "input slice has ${TS_PARAS} paragraphs, expected 40000; gene.ttl changed"
  elif [ "$TS_LEAN_RC" -ne 0 ] || [ "$TS_SAME" != "yes" ]; then
    record "$TS_ID" "$TS_ISSUE" "$TS_TITLE" ERROR \
      "Lean oracle failed (exit ${TS_LEAN_RC}, same triples: ${TS_SAME}); the expectation is unconfirmed"
  elif [ "$TS_RC" -ne 0 ] && grep -q 'Stack overflow' "${WORKDIR}/ts-fstar.err"; then
    record "$TS_ID" "$TS_ISSUE" "$TS_TITLE" XFAIL \
      "F* exit ${TS_RC} with Stack overflow in count_runs at 8192 KB; Lean serialises the same input correctly at 512 KB"
  elif [ "$TS_RC" -eq 0 ] && [ -s "${WORKDIR}/ts-fstar.ttl" ]; then
    record "$TS_ID" "$TS_ISSUE" "$TS_TITLE" XPASS \
      "F* now serialises 40000 paragraphs -- defect appears FIXED"
  else
    record "$TS_ID" "$TS_ISSUE" "$TS_TITLE" ERROR \
      "F* exit ${TS_RC} without Stack overflow (or empty output): $(tr "\n" " " < "${WORKDIR}/ts-fstar.err" | cut -c1-120)"
  fi
fi

# ---------------------------------------------------------------------
# F* command-line SPARQL defects found by the Lean vs F* differential
# (issues 736, 738, 739, 740, 747; opened 2026-10-10; record:
# docs/designissues/2026-10-10-lean-vs-fstar-differential.md). Every query
# and expected-result file is a real W3C test file from
# third_party/testing/w3c.
#
# SELECT cases (736, 738) compare three result sets, as canonical rows from
# tests/known-defects/sparql_rows.py: the W3C expected result (.srx), the Lean
# CLI answer (`l4factoidal query`), and the F* answer (`factoidal query -o
# json`). Equal domains are required, so a row that carries an extra binding
# is a different row (SPARQL 1.1 18.1.8).
#   ERROR  the Lean answer is not the expected result (the case would record
#          a wrong expectation), the F* run failed, or the F* answer is
#          neither the expected result nor the wrong row recorded here
#   XPASS  the F* answer is the expected result
#   XFAIL  the F* answer contains the recorded wrong row, and the expected
#          result does not
#
# The cases 739 and 740 also use the Lean CLI as the oracle. Until 2026-10-10
# they used `l4w3c` and the Lean N-Triples parser instead, because the Lean CLI
# had the same two defects (https://github.com/danbri/factoidal/issues/741 and
# https://github.com/danbri/factoidal/issues/742, fixed in the Lean tree on
# 2026-10-10). A Lean CLI built before those fixes makes these two cases ERROR,
# which is the ERROR-on-wrong-Lean rule; run with L4FACTOIDAL_BIN set to a
# newer build (formal/lean4/.lake/build/bin/l4factoidal) until a release built
# from the fix is fetched.
# ---------------------------------------------------------------------
W3C_SPARQL="${ROOT}/third_party/testing/w3c/sparql/sparql11"
W3C_NT="${ROOT}/third_party/testing/w3c/rdf/rdf11/rdf-n-triples"
ROWS_PY="${ROOT}/tests/known-defects/sparql_rows.py"
XSD_INT="http://www.w3.org/2001/XMLSchema#integer"
XSD_BOOL="http://www.w3.org/2001/XMLSchema#boolean"

SPARQL_PROBE_ERR=""
if [ ! -x "$L4_BIN" ]; then
  SPARQL_PROBE_ERR="no l4factoidal at ${L4_BIN} (tools/fetch-builds.sh --set native)"
elif ! command -v python3 > /dev/null 2>&1; then
  SPARQL_PROBE_ERR="no python3 (sparql_rows.py reads the result sets)"
elif [ ! -r "${W3C_SPARQL}/manifest-all.ttl" ] || [ ! -r "${W3C_NT}/manifest.ttl" ]; then
  SPARQL_PROBE_ERR="no W3C test files under third_party/testing/w3c (git submodule update --init --depth 1 third_party/testing/w3c)"
fi

# sparql_select_check TAG DATA QUERY EXPECTED_SRX WRONG_ROW WRONG_WHAT
# Sets SEL_STATE (XFAIL, XPASS or ERROR) and SEL_DETAIL. WRONG_ROW is the exact
# canonical row the F* answer contains while the defect is present.
sparql_select_check () {
  local tag="$1" data="$2" query="$3" expected="$4" wrong_row="$5" wrong_what="$6"
  local d="${WORKDIR}/sel-${tag}" fmt=turtle frc=0 lrc=0
  mkdir -p "$d"
  case "$data" in *.trig) fmt=trig ;; esac
  SEL_STATE=ERROR
  timeout 120 "$BIN" query --data "$data" --query "$query" -o json \
      < /dev/null > "$d/fstar.json" 2> "$d/fstar.err"; frc=$?
  timeout 120 "$L4_BIN" query "$data" --format "$fmt" --query "$query" \
      < /dev/null > "$d/lean.json" 2> "$d/lean.err"; lrc=$?
  if ! python3 -I "$ROWS_PY" < "$expected" > "$d/expected.rows" 2> "$d/expected.err" \
     || [ ! -s "$d/expected.rows" ]; then
    SEL_DETAIL="cannot read the expected result ${expected#"$ROOT"/}"
  elif [ "$lrc" -ne 0 ] \
     || ! python3 -I "$ROWS_PY" < "$d/lean.json" > "$d/lean.rows" 2> "$d/lean.perr"; then
    SEL_DETAIL="Lean oracle failed (exit ${lrc}): $(tr "\n" " " < "$d/lean.err" | cut -c1-100)"
  elif ! cmp -s "$d/lean.rows" "$d/expected.rows"; then
    SEL_DETAIL="Lean oracle answered rows that differ from the W3C expected result; the expectation is unconfirmed"
  elif [ "$frc" -ne 0 ] \
     || ! python3 -I "$ROWS_PY" < "$d/fstar.json" > "$d/fstar.rows" 2> "$d/fstar.perr"; then
    SEL_DETAIL="F* run failed (exit ${frc}): $(tr "\n" " " < "$d/fstar.err" | cut -c1-100)"
  elif cmp -s "$d/fstar.rows" "$d/expected.rows"; then
    SEL_STATE=XPASS
    SEL_DETAIL="F* now gives the W3C expected result"
  elif grep -Fxq -- "$wrong_row" "$d/fstar.rows" && ! grep -Fxq -- "$wrong_row" "$d/expected.rows"; then
    SEL_STATE=XFAIL
    SEL_DETAIL="F* ${wrong_what}"
  else
    SEL_DETAIL="F* answer is neither the expected result nor the recorded wrong row (answer drifted)"
  fi
}

# Aggregation for a case that runs several queries: any ERROR makes the case an
# ERROR (the detail gives each error); all XPASS makes it an XPASS; otherwise it
# is an XFAIL (at least one query still wrong). The XFAIL detail names the
# queries that are still wrong and the ones that are already right.
agg_reset () { AGG_N=0; AGG_XL=""; AGG_PL=""; AGG_EL=""; }
agg_add () {
  local label="$1"
  AGG_N=$((AGG_N+1))
  case "$SEL_STATE" in
    XFAIL) AGG_XL="${AGG_XL}${AGG_XL:+, }${label}" ;;
    XPASS) AGG_PL="${AGG_PL}${AGG_PL:+, }${label}" ;;
    *)     AGG_EL="${AGG_EL}${AGG_EL:+; }${label}: ${SEL_DETAIL}" ;;
  esac
}
agg_record () {
  local id="$1" issue="$2" title="$3" what="$4"
  if [ -n "$AGG_EL" ]; then
    record "$id" "$issue" "$title" ERROR "$AGG_EL"
  elif [ -z "$AGG_XL" ]; then
    record "$id" "$issue" "$title" XPASS "all ${AGG_N} queries now right -- defect appears FIXED"
  else
    record "$id" "$issue" "$title" XFAIL \
      "${what}: still wrong ${AGG_XL}${AGG_PL:+; already right ${AGG_PL}}"
  fi
}

# 736: the F* evaluator gives a value where SPARQL 1.1 section 17 raises an
# error. Two of the twelve tests in the issue. IF: functions/if02, expected
# result one solution with ?error unbound. Cast: cast/cast-int, six strings
# outside the lexical space of xsd:integer ("1.5" among them) must leave
# ?integer unbound; F* binds it (xsd:integer("1.5") gives 1).
S736_TITLE_IF="F* IF() with an error condition returns its third argument"
S736_TITLE_CAST="F* xsd:integer cast accepts strings outside the lexical space"
if [ -n "$SPARQL_PROBE_ERR" ]; then
  record SPARQL-736-IF 736 "$S736_TITLE_IF" ERROR "$SPARQL_PROBE_ERR"
  record SPARQL-736-CAST 736 "$S736_TITLE_CAST" ERROR "$SPARQL_PROBE_ERR"
else
  sparql_select_check 736if "${W3C_SPARQL}/functions/data2.ttl" \
    "${W3C_SPARQL}/functions/if02.rq" "${W3C_SPARQL}/functions/if02.srx" \
    "?error=\"true\"^^<${XSD_BOOL}>" "binds ?error to true for IF(1/0, false, true); expected unbound"
  record SPARQL-736-IF 736 "$S736_TITLE_IF" "$SEL_STATE" "$SEL_DETAIL"
  sparql_select_check 736cast "${W3C_SPARQL}/cast/data.ttl" \
    "${W3C_SPARQL}/cast/cast-int.rq" "${W3C_SPARQL}/cast/cast-int.srx" \
    "?a=<http://example.org/s08> ?integer=\"1\"^^<${XSD_INT}> ?v=\"1.5\"" \
    "binds xsd:integer(\"1.5\") to 1; expected unbound"
  record SPARQL-736-CAST 736 "$S736_TITLE_CAST" "$SEL_STATE" "$SEL_DETAIL"
fi

# 738: the F* command line evaluates SELECT through the store backend, which
# ignores FROM NAMED. The three bindings/graph-from-named tests; the data has
# the named graphs ex:g1 and ex:g2 and every query names only ex:g1. SPARQL 1.1
# 13.2.2 and 18.6: GRAPH ranges over the named graphs of the dataset, so rows
# for ex:g2 are wrong. (The issue also lists UUID, SERVICE SILENT and a
# sub-SELECT inside GRAPH; those items have no case yet.)
S738_TITLE="F* ignores FROM NAMED (store backend)"
if [ -n "$SPARQL_PROBE_ERR" ]; then
  record SPARQL-738-FROM-NAMED 738 "$S738_TITLE" ERROR "$SPARQL_PROBE_ERR"
else
  GFN="${W3C_SPARQL}/bindings"
  agg_reset
  sparql_select_check gfn1 "${GFN}/graph-from-named.trig" "${GFN}/graph-from-named-1.rq" \
    "${GFN}/graph-from-named-1.srx" \
    "?g=<http://example.org/g2> ?x=\"1\"^^<${XSD_INT}>" "gives rows for graph ex:g2"
  agg_add "graph-from-named-1"
  sparql_select_check gfn2 "${GFN}/graph-from-named.trig" "${GFN}/graph-from-named-2.rq" \
    "${GFN}/graph-from-named-2.srx" \
    "?g=<http://example.org/g2> ?x=\"1\"^^<${XSD_INT}>" "gives a row for graph ex:g2"
  agg_add "graph-from-named-2"
  sparql_select_check gfn3 "${GFN}/graph-from-named.trig" "${GFN}/graph-from-named-3.rq" \
    "${GFN}/graph-from-named-3.srx" \
    "?x=\"2\"^^<${XSD_INT}>" "gives the row from GRAPH ex:g2"
  agg_add "graph-from-named-3"
  agg_record SPARQL-738-FROM-NAMED 738 "$S738_TITLE" "F* rows for graphs outside FROM NAMED (W3C bindings tests)"
fi

# 739: the F* command line parses the query with no base IRI, so a relative IRI
# in a query is a parse error. SPARQL 1.1 4.1.1.2 resolves it against the base
# IRI (RFC 3986 5.1.3: the retrieval IRI of the query document). The five W3C
# tests of the issue, one entry per test:
#   DIR | QUERY | qt:data (or -) | qt:graphData files | F* -d FILE | F* -o | EXPECTED
# Oracle: the Lean CLI (`l4factoidal query --query FILE`, which takes the base
# of the query from the file's IRI) on the test's dataset must give the W3C
# expected result; otherwise the case is an ERROR. The CLI reads one dataset,
# so the qt:data and qt:graphData files are written as one N-Quads file, each
# qt:graphData graph named by its file's IRI, as the manifest names it. The
# expected result is compared by kind: an .srx by its rows (sparql_rows.py), a
# Turtle result set (rs:ResultSet) by the rows the Lean CLI reads out of it, a
# graph by its RDFC-1.0 canonical N-Quads. The case is XFAIL while at least one
# F* query still gives "invalid IRI", and the detail names each query.
fileiri () { printf 'file://%s' "$(realpath "$1")"; }
# nq_of FILE [GRAPH]: FILE (Turtle, base = its IRI) as N-Quads lines.
nq_of () {
  timeout 60 "$L4_BIN" parse "$1" --format turtle --base "$(fileiri "$1")" --out nquads < /dev/null |
    if [ -n "${2:-}" ]; then sed -e '/^$/d' -e "s| \.\$| <$2> .|"; else sed '/^$/d'; fi
}
# rs_rows TTL VARS...: the rows of a Turtle rs:ResultSet whose solutions bind
# every variable in VARS, as SPARQL Results JSON, read by the Lean CLI.
rs_rows () {
  local ttl="$1" sel="" pat="" i=0; shift
  for v in "$@"; do
    i=$((i+1)); sel="${sel} ?${v}"
    pat="${pat} ?sol rs:binding ?b${i} . ?b${i} rs:variable \"${v}\" ; rs:value ?${v} ."
  done
  timeout 60 "$L4_BIN" query "$ttl" --format turtle --base "$(fileiri "$ttl")" \
    --query-string "PREFIX rs: <http://www.w3.org/2001/sw/DataAccess/tests/result-set#> SELECT${sel} WHERE { ?set rs:solution ?sol .${pat} }" < /dev/null
}
S739_TITLE="F* parses a query with no base IRI (relative IRI is an error)"
if [ -n "$SPARQL_PROBE_ERR" ]; then
  record SPARQL-739-QUERY-BASE 739 "$S739_TITLE" ERROR "$SPARQL_PROBE_ERR"
else
  agg_reset
  for entry in \
    "bindings|graph.rq|empty.ttl|data01.ttl data02.ttl|data01.ttl|json|graph.ttl" \
    "construct|constructwhere04.rq|-|data.ttl|data.ttl|ntriples|constructwhere04result.ttl" \
    "exists|exists03.rq|exists01.ttl|exists02.ttl|exists01.ttl|json|exists03.srx" \
    "property-path|path-ng-01.rq|-|ng-01.ttl ng-02.ttl ng-03.ttl|ng-01.ttl|json|path-ng-01.srx" \
    "property-path|path-ng-02.rq|-|ng-01.ttl ng-02.ttl ng-03.ttl|ng-01.ttl|json|path-ng-01.srx"
  do
    IFS='|' read -r qdir qfile qdefault qnamed qdata qout qexpected <<< "$entry"
    dir="${W3C_SPARQL}/${qdir}"; d="${WORKDIR}/q739-${qfile%.rq}"; mkdir -p "$d"
    : > "$d/dataset.nq"
    [ "$qdefault" = "-" ] || nq_of "${dir}/${qdefault}" >> "$d/dataset.nq"
    for g in $qnamed; do nq_of "${dir}/${g}" "$(fileiri "${dir}/${g}")" >> "$d/dataset.nq"; done
    timeout 120 "$L4_BIN" query "$d/dataset.nq" --format nquads --query "${dir}/${qfile}" \
        < /dev/null > "$d/lean.out" 2> "$d/lean.err"; lrc=$?
    lean_ok=0
    if [ "$lrc" -eq 0 ]; then
      case "$qexpected" in
        *.srx)
          python3 -I "$ROWS_PY" < "${dir}/${qexpected}" > "$d/want.rows" 2> /dev/null \
            && python3 -I "$ROWS_PY" < "$d/lean.out" > "$d/got.rows" 2> /dev/null \
            && [ -s "$d/want.rows" ] && cmp -s "$d/got.rows" "$d/want.rows" && lean_ok=1 ;;
        graph.ttl)
          rs_rows "${dir}/${qexpected}" g t > "$d/want.json" 2> /dev/null \
            && python3 -I "$ROWS_PY" < "$d/want.json" > "$d/want.rows" 2> /dev/null \
            && python3 -I "$ROWS_PY" < "$d/lean.out" > "$d/got.rows" 2> /dev/null \
            && [ -s "$d/want.rows" ] && cmp -s "$d/got.rows" "$d/want.rows" && lean_ok=1 ;;
        *)
          timeout 60 "$L4_BIN" canonicalize "${dir}/${qexpected}" --format turtle \
              --base "$(fileiri "${dir}/${qexpected}")" < /dev/null > "$d/want.nq" 2> /dev/null \
            && timeout 60 "$L4_BIN" canonicalize "$d/lean.out" --format ntriples \
              < /dev/null > "$d/got.nq" 2> /dev/null \
            && [ -s "$d/want.nq" ] && cmp -s "$d/got.nq" "$d/want.nq" && lean_ok=1 ;;
      esac
    fi
    fout=$(timeout 60 "$BIN" query --data "${dir}/${qdata}" \
             --query "${dir}/${qfile}" -o "$qout" < /dev/null 2>&1); frc=$?
    if [ "$lean_ok" -ne 1 ]; then
      SEL_STATE=ERROR
      SEL_DETAIL="the Lean CLI (exit ${lrc}) did not give the W3C expected result ${qexpected}; the expectation is unconfirmed: $(tr "\n" " " < "$d/lean.err" | cut -c1-80)"
    elif printf '%s\n' "$fout" | grep -q '^SPARQL parse error: invalid IRI'; then
      SEL_STATE=XFAIL
      SEL_DETAIL="F* says invalid IRI; the Lean CLI gives the expected result"
    elif [ "$frc" -eq 0 ] && [ -n "$fout" ] && ! printf '%s\n' "$fout" | grep -qi 'parse error'; then
      SEL_STATE=XPASS
      SEL_DETAIL="F* now parses it"
    else
      SEL_STATE=ERROR
      SEL_DETAIL="F* exit ${frc}, unexpected output: $(printf '%s' "$fout" | tr "\n" " " | cut -c1-80)"
    fi
    agg_add "$qfile"
  done
  agg_record SPARQL-739-QUERY-BASE 739 "$S739_TITLE" "F* says invalid IRI, the Lean CLI gives the W3C result"
fi

# 740: the F* SPARQL parser names a blank node made for collection syntax
# `_:bnode_<n>` with the `_:` inside the identifier, and CONSTRUCT freshens it
# to `tpl_<k>__:bnode_<n>`. The N-Triples writer prints `_:` before it, so the
# label contains a colon. RDF 1.1 N-Triples does not allow that; the W3C test
# rdf-n-triples nt-syntax-bad-bnode-02 is "Colon in bnode label not allowed".
# Query: construct/constructlist.rq (CONSTRUCT { (?s ?o) :prop ?p }).
# The checker is the Lean N-Triples parser (`l4factoidal parse --format
# ntriples`, which passes nt-syntax-bad-bnode-01 and -02 in l4w3c). The oracle
# is the Lean CLI: `l4factoidal query` on the same files must print N-Triples
# that the checker reads, with the RDFC-1.0 canonical form of the W3C expected
# graph constructlistresult.ttl (so the graphs are isomorphic). Three controls;
# failing any makes the case an ERROR:
#   1. the F* output with the colon in each label replaced by an underscore
#      parses, with the same number of triples as the F* output has lines;
#   2. the W3C file nt-syntax-bad-bnode-02.nt is rejected;
#   3. the Lean CLI output is the expected graph (the oracle).
S740_TITLE="F* CONSTRUCT prints blank node labels that are not N-Triples"
if [ -n "$SPARQL_PROBE_ERR" ]; then
  record SPARQL-740-CONSTRUCT-BNODE 740 "$S740_TITLE" ERROR "$SPARQL_PROBE_ERR"
else
  d="${WORKDIR}/construct740"; mkdir -p "$d"
  CL="${W3C_SPARQL}/construct"
  timeout 60 "$BIN" query --data "${CL}/data.ttl" --query "${CL}/constructlist.rq" -o ntriples \
      < /dev/null > "$d/fstar.nt" 2> "$d/fstar.err"; frc=$?
  timeout 60 "$L4_BIN" query "${CL}/data.ttl" --format turtle --query "${CL}/constructlist.rq" \
      < /dev/null > "$d/lean.nt" 2> "$d/lean.err"; lrc=$?
  timeout 60 "$L4_BIN" canonicalize "$d/lean.nt" --format ntriples < /dev/null > "$d/lean.c14n" 2> /dev/null; lcrc=$?
  timeout 60 "$L4_BIN" canonicalize "${CL}/constructlistresult.ttl" --format turtle \
      --base "$(fileiri "${CL}/constructlistresult.ttl")" < /dev/null > "$d/want.c14n" 2> /dev/null; wcrc=$?
  sed 's/__:bnode_/__bnode_/g' "$d/fstar.nt" > "$d/control-ok.nt"
  nlines=$(grep -c . "$d/fstar.nt")
  ok_count=$(timeout 60 "$L4_BIN" parse "$d/control-ok.nt" --format ntriples < /dev/null 2> /dev/null)
  ok_rc=$?
  timeout 60 "$L4_BIN" parse "${W3C_NT}/nt-syntax-bad-bnode-02.nt" --format ntriples \
      < /dev/null > /dev/null 2> /dev/null; bad_rc=$?
  timeout 60 "$L4_BIN" parse "$d/fstar.nt" --format ntriples < /dev/null > /dev/null 2> "$d/lean-parse.err"; out_rc=$?
  if [ "$lrc" -ne 0 ] || [ "$lcrc" -ne 0 ] || [ "$wcrc" -ne 0 ] || [ ! -s "$d/want.c14n" ] \
     || ! cmp -s "$d/lean.c14n" "$d/want.c14n"; then
    record SPARQL-740-CONSTRUCT-BNODE 740 "$S740_TITLE" ERROR \
      "control 3 failed: the Lean CLI output (exit ${lrc}, canonicalize exit ${lcrc}) is not the W3C expected graph constructlistresult.ttl; the expectation is unconfirmed: $(head -n 1 "$d/lean.err")"
  elif [ "$frc" -ne 0 ] || [ "$nlines" -eq 0 ]; then
    record SPARQL-740-CONSTRUCT-BNODE 740 "$S740_TITLE" ERROR \
      "F* run gave exit ${frc} and ${nlines} lines: $(tr "\n" " " < "$d/fstar.err" | cut -c1-100)"
  elif [ "$ok_rc" -ne 0 ] || [ "$ok_count" != "$nlines" ]; then
    record SPARQL-740-CONSTRUCT-BNODE 740 "$S740_TITLE" ERROR \
      "control 1 failed: the Lean parser read ${ok_count:-nothing} triples (exit ${ok_rc}) from the colon-free copy of ${nlines} lines"
  elif [ "$bad_rc" -eq 0 ]; then
    record SPARQL-740-CONSTRUCT-BNODE 740 "$S740_TITLE" ERROR \
      "control 2 failed: the Lean parser accepts nt-syntax-bad-bnode-02.nt"
  elif [ "$out_rc" -eq 0 ]; then
    record SPARQL-740-CONSTRUCT-BNODE 740 "$S740_TITLE" XPASS \
      "F* output now parses as N-Triples (${nlines} lines) -- defect appears FIXED"
  elif grep -q '_:[A-Za-z0-9_]*:' "$d/fstar.nt"; then
    record SPARQL-740-CONSTRUCT-BNODE 740 "$S740_TITLE" XFAIL \
      "F* output has a colon in a blank node label and is rejected: $(head -n 1 "$d/lean-parse.err"); the Lean CLI output is the expected graph"
  else
    record SPARQL-740-CONSTRUCT-BNODE 740 "$S740_TITLE" ERROR \
      "F* output is rejected but has no colon in a label (answer drifted): $(head -n 1 "$d/lean-parse.err")"
  fi
fi

# 747: the F* SPARQL parser gives a [ ] node that is an item of a collection
# the same blank node as the collection cell that holds it, so the cell is its
# own rdf:first (SPARQL 1.1 4.1.4). Query: the W3C file
# sparql10/syntax-sparql1/syntax-forms-01.rq,
#   SELECT * WHERE { ( [ ?x ?y ] ) :p ( [ ?pa ?b ] 57 ) }
# Data: fixtures/sparql-747-collection-bnode.ttl, the 9-triple graph of that
# shape. Expected: one row, EXPECT747 below. Controls; failing any makes the
# case an ERROR:
#   1. both command lines read the data as 9 triples (so the defect is in the
#      query, not the data);
#   2. the Lean CLI answers exactly the expected row (the oracle; the Lean
#      parser had the same defect until 2026-10-10, issue 742).
# XFAIL: F* answers no row. XPASS: F* answers the expected row.
S747_TITLE="F* gives [ ] in a collection the cell's blank node"
EXPECT747="?b=<http://example.org/ns#b1> ?pa=<http://example.org/ns#pa1> ?x=<http://example.org/ns#x1> ?y=<http://example.org/ns#y1>"
if [ -n "$SPARQL_PROBE_ERR" ]; then
  record SPARQL-747-COLLECTION-BNODE 747 "$S747_TITLE" ERROR "$SPARQL_PROBE_ERR"
else
  d="${WORKDIR}/q747"; mkdir -p "$d"
  data747="${ROOT}/tests/known-defects/fixtures/sparql-747-collection-bnode.ttl"
  q747="${ROOT}/third_party/testing/w3c/sparql/sparql10/syntax-sparql1/syntax-forms-01.rq"
  printf '%s\n' "$EXPECT747" > "$d/expected.rows"
  fcount=$(timeout 60 "$BIN" count "$data747" < /dev/null 2> /dev/null | sed -n 's/.*: \([0-9]*\) triples$/\1/p')
  lcount=$(timeout 60 "$L4_BIN" parse "$data747" --format turtle < /dev/null 2> /dev/null | tail -n 1)
  frc=0; lrc=0
  timeout 120 "$BIN" query --data "$data747" --query "$q747" -o json \
      < /dev/null > "$d/fstar.json" 2> "$d/fstar.err" || frc=$?
  timeout 120 "$L4_BIN" query "$data747" --format turtle --query "$q747" \
      < /dev/null > "$d/lean.json" 2> "$d/lean.err" || lrc=$?
  if [ ! -r "$q747" ]; then
    record SPARQL-747-COLLECTION-BNODE 747 "$S747_TITLE" ERROR "no W3C query file ${q747#"$ROOT"/}"
  elif [ "$fcount" != "9" ] || [ "$lcount" != "9" ]; then
    record SPARQL-747-COLLECTION-BNODE 747 "$S747_TITLE" ERROR \
      "data control: F* reads ${fcount:-?} triples, Lean ${lcount:-?}; expected 9 each"
  elif [ "$lrc" -ne 0 ] \
     || ! python3 -I "$ROWS_PY" < "$d/lean.json" > "$d/lean.rows" 2> "$d/lean.perr" \
     || ! cmp -s "$d/lean.rows" "$d/expected.rows"; then
    record SPARQL-747-COLLECTION-BNODE 747 "$S747_TITLE" ERROR \
      "Lean oracle (exit ${lrc}) did not answer exactly the expected row; the expectation is unconfirmed"
  elif [ "$frc" -ne 0 ] \
     || ! python3 -I "$ROWS_PY" < "$d/fstar.json" > "$d/fstar.rows" 2> "$d/fstar.perr"; then
    record SPARQL-747-COLLECTION-BNODE 747 "$S747_TITLE" ERROR \
      "F* run failed (exit ${frc}): $(tr "\n" " " < "$d/fstar.err" | cut -c1-100)"
  elif cmp -s "$d/fstar.rows" "$d/expected.rows"; then
    record SPARQL-747-COLLECTION-BNODE 747 "$S747_TITLE" XPASS \
      "F* now answers the expected row -- defect appears FIXED"
  elif [ ! -s "$d/fstar.rows" ]; then
    record SPARQL-747-COLLECTION-BNODE 747 "$S747_TITLE" XFAIL \
      "F* answers no row for syntax-forms-01.rq on a graph of its shape; the Lean CLI answers the expected row"
  else
    record SPARQL-747-COLLECTION-BNODE 747 "$S747_TITLE" ERROR \
      "F* answers rows that are neither none nor the expected row (answer drifted): $(head -n 1 "$d/fstar.rows" | cut -c1-100)"
  fi
fi

# ---------------------------------------------------------------------
# SPARQL-OPT-FILTER-SCOPE (https://github.com/danbri/factoidal/issues/815)
# -- a FILTER in an OPTIONAL group is evaluated on the group's row only, so a
# variable of the left side reads as unbound. SPARQL 1.1 section 18.2.2.5
# makes `OPTIONAL { P FILTER(F) }` LeftJoin(G, P, F), with F evaluated on the
# merged solution (section 18.5). Data and query:
# fixtures/sparql-815-optional-filter-scope.{ttl,rq}; ex:a has age 72, so its
# name is the OPTIONAL extension; ex:c has age 71, so it has none.
# The Lean engine is FIXED (2026-10-13: the parser makes the group's FILTERs
# the LeftJoin condition, `optionalGroup`; theorems and guards in
# formal/lean4/L4Factoidal/SPARQL/OptionalFilterScope.lean). Its answer is a
# plain assertion: the Lean CLI must answer exactly the rows of section
# 18.2.2.5, or the case is an ERROR. The F* engine (`factoidal query`) still
# has the defect; this case is the F* defect:
#   XFAIL  F* answers the rows without ?n for ex:a (the defect)
#   XPASS  F* answers the rows of section 18.2.2.5: fixed in F*; retire this
#          case and close the issue
#   ERROR  the Lean CLI is wrong (a Lean regression), or any other answer
# ---------------------------------------------------------------------
S815_TITLE="F*: FILTER in OPTIONAL does not see left-side variables"
XSD_I="<http://www.w3.org/2001/XMLSchema#integer>"
EXPECT815="?a=\"71\"^^${XSD_I} ?s=<http://ex.org/c>
?a=\"72\"^^${XSD_I} ?n=\"Alice\" ?s=<http://ex.org/a>"
WRONG815="?a=\"71\"^^${XSD_I} ?s=<http://ex.org/c>
?a=\"72\"^^${XSD_I} ?s=<http://ex.org/a>"
if [ -n "$SPARQL_PROBE_ERR" ]; then
  record SPARQL-OPT-FILTER-SCOPE 815 "$S815_TITLE" ERROR "$SPARQL_PROBE_ERR"
else
  d="${WORKDIR}/q815"; mkdir -p "$d"
  printf '%s\n' "$EXPECT815" > "$d/expected.rows"
  printf '%s\n' "$WRONG815" > "$d/wrong.rows"
  lrc=0; frc=0
  timeout 120 "$L4_BIN" query "${FIXTURES}/sparql-815-optional-filter-scope.ttl" --format turtle \
      --query "${FIXTURES}/sparql-815-optional-filter-scope.rq" \
      < /dev/null > "$d/lean.json" 2> "$d/lean.err" || lrc=$?
  timeout 120 "$BIN" query --data "${FIXTURES}/sparql-815-optional-filter-scope.ttl" \
      --query "${FIXTURES}/sparql-815-optional-filter-scope.rq" -o json \
      < /dev/null > "$d/fstar.json" 2> "$d/fstar.err" || frc=$?
  if [ "$lrc" -ne 0 ] \
     || ! python3 -I "$ROWS_PY" < "$d/lean.json" > "$d/lean.rows" 2> "$d/lean.perr"; then
    record SPARQL-OPT-FILTER-SCOPE 815 "$S815_TITLE" ERROR \
      "Lean run failed (exit ${lrc}): $(tr "\n" " " < "$d/lean.err" | cut -c1-100)"
  elif ! cmp -s "$d/lean.rows" "$d/expected.rows"; then
    record SPARQL-OPT-FILTER-SCOPE 815 "$S815_TITLE" ERROR \
      "the Lean CLI does not answer the rows of section 18.2.2.5 (Lean regression): $(head -n 1 "$d/lean.rows" | cut -c1-100)"
  elif [ "$frc" -ne 0 ] \
     || ! python3 -I "$ROWS_PY" < "$d/fstar.json" > "$d/fstar.rows" 2> "$d/fstar.perr"; then
    record SPARQL-OPT-FILTER-SCOPE 815 "$S815_TITLE" ERROR \
      "F* run failed (exit ${frc}): $(tr "\n" " " < "$d/fstar.err" | cut -c1-100)"
  elif cmp -s "$d/fstar.rows" "$d/expected.rows"; then
    record SPARQL-OPT-FILTER-SCOPE 815 "$S815_TITLE" XPASS \
      "F* now binds ?n for ex:a -- defect appears FIXED in F*"
  elif cmp -s "$d/fstar.rows" "$d/wrong.rows"; then
    record SPARQL-OPT-FILTER-SCOPE 815 "$S815_TITLE" XFAIL \
      "F*: OPTIONAL { ?s ex:name ?n FILTER(?a = 72) } binds ?n for no row; section 18.2.2.5 binds it for ex:a (the Lean CLI does)"
  else
    record SPARQL-OPT-FILTER-SCOPE 815 "$S815_TITLE" ERROR \
      "F* answers neither the expected nor the recorded rows: $(head -n 1 "$d/fstar.rows" | cut -c1-100)"
  fi
fi

# ---------------------------------------------------------------------
# RDFXML-LANG-SCOPE (https://github.com/danbri/factoidal/issues/329, the open F*
# issue; the Lean repair was https://github.com/danbri/factoidal/issues/841) -- the F*
# RDF/XML parser applies the xml:lang of a property element to the property
# elements that follow it in the same node element. XML 1.0 section 2.12 limits
# the language to the element that specifies it and its content, so
#   <ex:p xml:lang="fr">a</ex:p><ex:q>b</ex:q>
# makes "a"@fr and a plain "b". Parser.RDFXML.fst returns the state of the
# property element (restore_scope st2 ...), where the node element's scope is
# the one to return. Fixture: fixtures/rdfxml-841-lang-scope.rdf (the same file
# as tests/sbm11/syntax/lang_scope.rdf). The Lean parser is FIXED (2026-10-14:
# Syntax/RdfXml.lean closePropertyScope; theorems propertyElt_scope and
# propertyEltList_scope). Its answer is a plain assertion: the Lean CLI must
# print exactly the two expected N-Quads lines, or the case is an ERROR (run
# with L4FACTOIDAL_BIN set to formal/lean4/.lake/build/bin/l4factoidal until a
# release built from the fix is fetched). F* is NOT repaired (no F* toolchain
# in the session that fixed Lean); this case records its behaviour:
#   XFAIL  F* reads <q> "b" as "b"@fr (the defect)
#   XPASS  F* prints the two expected lines: fixed in F*; retire this case and
#          close issue 329
#   ERROR  the Lean CLI is wrong, F* does not read <p> "a"@fr (the probe
#          measured nothing), or F* prints anything else
# ---------------------------------------------------------------------
R841_TITLE="F* RDF/XML applies the xml:lang of a property element to the next ones"
R841_FIXTURE="${FIXTURES}/rdfxml-841-lang-scope.rdf"
R841_P='<http://example.org/s> <http://example.org/p> "a"@fr .'
R841_Q_PLAIN='<http://example.org/s> <http://example.org/q> "b" .'
R841_Q_FR='<http://example.org/s> <http://example.org/q> "b"@fr .'
if [ ! -x "$L4_BIN" ]; then
  record RDFXML-LANG-SCOPE 329 "$R841_TITLE" ERROR "no l4factoidal at ${L4_BIN} (tools/fetch-builds.sh --set native)"
else
  d="${WORKDIR}/rdfxml841"; mkdir -p "$d"
  printf '%s\n%s\n' "$R841_P" "$R841_Q_PLAIN" | LC_ALL=C sort > "$d/expected.nq"
  lrc=0; frc=0
  timeout 60 "$L4_BIN" parse "$R841_FIXTURE" --format rdfxml --out nquads \
      < /dev/null > "$d/lean.raw" 2> "$d/lean.err" || lrc=$?
  timeout 60 "$BIN" dump-nq "$R841_FIXTURE" \
      < /dev/null > "$d/fstar.raw" 2> "$d/fstar.err" || frc=$?
  sed '/^$/d' "$d/lean.raw" | LC_ALL=C sort > "$d/lean.nq"
  sed '/^$/d' "$d/fstar.raw" | LC_ALL=C sort > "$d/fstar.nq"
  if [ "$lrc" -ne 0 ] || ! cmp -s "$d/lean.nq" "$d/expected.nq"; then
    record RDFXML-LANG-SCOPE 329 "$R841_TITLE" ERROR \
      "the Lean CLI (exit ${lrc}) does not print the two expected N-Quads lines (Lean regression, or a build from before the fix): $(head -n 2 "$d/lean.nq" | tr "\n" " " | cut -c1-120)"
  elif [ "$frc" -ne 0 ]; then
    record RDFXML-LANG-SCOPE 329 "$R841_TITLE" ERROR \
      "F* run failed (exit ${frc}): $(tr "\n" " " < "$d/fstar.err" | cut -c1-100)"
  elif ! grep -Fxq -- "$R841_P" "$d/fstar.nq"; then
    record RDFXML-LANG-SCOPE 329 "$R841_TITLE" ERROR \
      "F* does not read <p> \"a\"@fr (the probe measured nothing): $(head -n 2 "$d/fstar.nq" | tr "\n" " " | cut -c1-120)"
  elif cmp -s "$d/fstar.nq" "$d/expected.nq"; then
    record RDFXML-LANG-SCOPE 329 "$R841_TITLE" XPASS \
      "F* now prints the two expected lines -- defect appears FIXED in F*"
  elif grep -Fxq -- "$R841_Q_FR" "$d/fstar.nq" && [ "$(grep -c . "$d/fstar.nq")" -eq 2 ]; then
    record RDFXML-LANG-SCOPE 329 "$R841_TITLE" XFAIL \
      "F* reads <q> \"b\" as \"b\"@fr (XML 1.0 section 2.12: plain); the Lean CLI prints the plain literal"
  else
    record RDFXML-LANG-SCOPE 329 "$R841_TITLE" ERROR \
      "F* prints neither the expected lines nor the recorded wrong line: $(head -n 3 "$d/fstar.nq" | tr "\n" " " | cut -c1-120)"
  fi
fi

# ---------------------------------------------------------------------
# JSONLD-BNODE-COLLIDE (https://github.com/danbri/factoidal/issues/840) -- the F*
# JSON-LD to RDF conversion names the blank nodes it generates _jld_anon<N>
# (Parser.JSONLD.fst, jld_fresh_bnode) and passes the blank node identifiers that the
# document writes through unchanged, so a document that writes _:_jld_anon0 and
# also holds a node object with no @id gets ONE node where it has two. The
# fixture (fixtures/jsonld-840-bnode-collide.jsonld, the same file as
# tests/sbm11/syntax/bnode_collide.jsonld) holds five nodes: three with a written
# label (_:_jld_anon0, _:_jld_anon1, _:genid1) and two with none. The Lean
# parser is FIXED (2026-10-14: JSONLD/ToRdf.lean generatedPrefix chooses the
# prefix of the generated labels from the document; theorem generated_ne_written
# in JSONLD/Theorems.lean). Its answer is a plain assertion: the Lean CLI must
# print five quads with five distinct blank node subjects, or the case is an
# ERROR (run with L4FACTOIDAL_BIN set to formal/lean4/.lake/build/bin/l4factoidal
# until a release built from the fix is fetched). F* is NOT repaired (no F*
# toolchain in the session that fixed Lean); this case records its behaviour:
#   XFAIL  F* prints three distinct blank node subjects for the five nodes
#   XPASS  F* prints five: fixed in F*; retire this case and close the issue
#   ERROR  the Lean CLI is wrong, or F* prints any other number of subjects
# ---------------------------------------------------------------------
J840_TITLE="F* JSON-LD gives a generated blank node the label of a written one"
J840_FIXTURE="${FIXTURES}/jsonld-840-bnode-collide.jsonld"
# j840_subjects FILE: the number of distinct blank node subjects among the lines.
j840_subjects () { grep -o '^_:[^ ]*' "$1" | LC_ALL=C sort -u | grep -c .; }
if [ ! -x "$L4_BIN" ]; then
  record JSONLD-BNODE-COLLIDE 840 "$J840_TITLE" ERROR "no l4factoidal at ${L4_BIN} (tools/fetch-builds.sh --set native)"
else
  d="${WORKDIR}/jsonld840"; mkdir -p "$d"
  lrc=0; frc=0
  timeout 60 "$L4_BIN" parse "$J840_FIXTURE" --format jsonld --out nquads \
      < /dev/null > "$d/lean.raw" 2> "$d/lean.err" || lrc=$?
  timeout 60 "$BIN" dump-nq "$J840_FIXTURE" \
      < /dev/null > "$d/fstar.raw" 2> "$d/fstar.err" || frc=$?
  sed '/^$/d' "$d/lean.raw" > "$d/lean.nq"
  sed '/^$/d' "$d/fstar.raw" > "$d/fstar.nq"
  lean_quads="$(grep -c . "$d/lean.nq")"
  lean_subjects="$(j840_subjects "$d/lean.nq")"
  fstar_quads="$(grep -c . "$d/fstar.nq")"
  fstar_subjects="$(j840_subjects "$d/fstar.nq")"
  if [ "$lrc" -ne 0 ] || [ "$lean_quads" != 5 ] || [ "$lean_subjects" != 5 ]; then
    record JSONLD-BNODE-COLLIDE 840 "$J840_TITLE" ERROR \
      "the Lean CLI (exit ${lrc}) prints ${lean_quads} quads with ${lean_subjects} distinct blank node subjects, expected 5 and 5 (Lean regression, or a build from before the fix)"
  elif [ "$frc" -ne 0 ]; then
    record JSONLD-BNODE-COLLIDE 840 "$J840_TITLE" ERROR \
      "F* run failed (exit ${frc}): $(tr "\n" " " < "$d/fstar.err" | cut -c1-100)"
  elif [ "$fstar_quads" != 5 ]; then
    record JSONLD-BNODE-COLLIDE 840 "$J840_TITLE" ERROR \
      "F* prints ${fstar_quads} quads, expected 5 (the probe measured nothing): $(head -n 2 "$d/fstar.nq" | tr "\n" " " | cut -c1-120)"
  elif [ "$fstar_subjects" = 5 ]; then
    record JSONLD-BNODE-COLLIDE 840 "$J840_TITLE" XPASS \
      "F* now prints five distinct blank node subjects -- defect appears FIXED in F*"
  elif [ "$fstar_subjects" = 3 ]; then
    record JSONLD-BNODE-COLLIDE 840 "$J840_TITLE" XFAIL \
      "F* prints 3 distinct blank node subjects for 5 nodes: _:_jld_anon0 and _:_jld_anon1 each carry a written node and a generated one (the Lean CLI prints 5)"
  else
    record JSONLD-BNODE-COLLIDE 840 "$J840_TITLE" ERROR \
      "F* prints ${fstar_subjects} distinct blank node subjects, neither the expected 5 nor the recorded 3"
  fi
fi

# ---------------------------------------------------------------------
# NX-1 (https://github.com/danbri/factoidal/issues/777) -- the Lean native
# crypto externs (HACL*, `@[extern]` + `opaque`) have no stated equivalence
# to the pure Lean functions. `sha256Hacl` is opaque, so no Lean theorem can
# relate it to `Crypto.sha256`; agreement is only measured (l4vc-probe,
# l4native-crypto-smoke). This probe reads the SOURCE, because the gap is
# the absence of a statement: XFAIL while no declaration named
# `sha256Hacl_eq_sha256` exists under formal/lean4. When one lands (an axiom
# citing the HACL* theorem, or a theorem), this reads XPASS: update issue 777
# and retire the case in the same commit.
# ---------------------------------------------------------------------
LEAN_SRC="${ROOT}/formal/lean4"
if [ ! -f "${LEAN_SRC}/L4Factoidal/Crypto/SHA2Native.lean" ]; then
  record NX-1 777 "native SHA-256 extern has no equivalence statement" ERROR \
    "formal/lean4/L4Factoidal/Crypto/SHA2Native.lean not found"
elif ! grep -q 'opaque sha256Hacl' "${LEAN_SRC}/L4Factoidal/Crypto/SHA2Native.lean"; then
  record NX-1 777 "native SHA-256 extern has no equivalence statement" ERROR \
    "probe drifted: sha256Hacl is no longer declared opaque in SHA2Native.lean"
elif grep -rqE '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(theorem|axiom|lemma)[[:space:]]+([A-Za-z0-9_.]*\.)?sha256Hacl_eq_sha256\b' \
      "${LEAN_SRC}" --include='*.lean'; then
  record NX-1 777 "native SHA-256 extern has no equivalence statement" XPASS \
    "a declaration named sha256Hacl_eq_sha256 now exists"
else
  record NX-1 777 "native SHA-256 extern has no equivalence statement" XFAIL \
    "no sha256Hacl_eq_sha256 theorem or axiom in formal/lean4 (agreement is measured only)"
fi

# ---------------------------------------------------------------------
# SF-1 to SF-4 (https://github.com/danbri/factoidal/issues/826) -- the
# strict chunked parse (formal/lean4/L4Factoidal/Syntax/StrictFeed.lean,
# https://github.com/danbri/factoidal/issues/813) has three equalities with
# the reference parsers, and one about the UTF-8 decoding under them, that
# are measured (tools/strict-parse-differential.sh,
# 21,012 agree, 0 differ (out of 21,012) on 2026-10-13) but not proved.
# Like NX-1, these probes read the SOURCE: XFAIL while no theorem of the
# name exists under formal/lean4. When one lands, the row reads XPASS:
# retire it, update issue 826 and docs/designissues/2026-09-03-rdf-parsing-
# strategy.md section 3b.3 in the same commit.
#   SF-1  walkAll_init_eq_parseTurtleWalk  (the chunked Turtle walk's
#         `walkAll` from the initial state is `parseTurtleWalk`)
#   SF-2  LineFeed.run_triple_eq_batch     (N-Triples chunk boundary; the probe
#         matches the leaf name run_triple_eq_batch in any namespace)
#   SF-3  LineFeed.run_quad12_eq_batch     (N-Quads chunk boundary, RDF 1.2;
#         leaf name run_quad12_eq_batch)
#   SF-4  Utf8Stream.feedChunks_eq_fromUTF8 (byte chunks decode to the text
#         String.fromUTF8? gives for their concatenation; leaf name)
# ---------------------------------------------------------------------
SF_SRC="${LEAN_SRC}/L4Factoidal/Syntax/StrictFeed.lean"
sf_probe () { # ID TITLE THEOREM DRIFT-PATTERN DRIFT-WHAT
  local id="$1" title="$2" thm="$3" drift="$4" what="$5"
  if [ ! -f "$SF_SRC" ]; then
    record "$id" 826 "$title" ERROR "${SF_SRC#"$ROOT"/} not found"
  elif ! grep -qE "$drift" "$SF_SRC"; then
    record "$id" 826 "$title" ERROR "probe drifted: ${what} is no longer defined in ${SF_SRC#"$ROOT"/}"
  elif grep -rqE "^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(private[[:space:]]+)?(theorem|lemma)[[:space:]]+([A-Za-z0-9_.]*\.)?${thm//./\\.}\b" \
        "${LEAN_SRC}" --include='*.lean'; then
    record "$id" 826 "$title" XPASS "a theorem named ${thm} now exists"
  else
    record "$id" 826 "$title" XFAIL \
      "no ${thm} theorem in formal/lean4 (agreement is measured by tools/strict-parse-differential.sh only)"
  fi
}
sf_probe SF-1 "chunked Turtle walk: walkAll = parseTurtleWalk unproved" \
  walkAll_init_eq_parseTurtleWalk '^def walkAll ' 'walkAll'
sf_probe SF-2 "N-Triples chunk boundary of LineFeed unproved" \
  run_triple_eq_batch '^def LineFeed\.run ' 'LineFeed.run'
sf_probe SF-3 "N-Quads RDF 1.2 chunk boundary of LineFeed unproved" \
  run_quad12_eq_batch '^theorem LineFeed\.run_quad11_eq_batch ' 'LineFeed.run_quad11_eq_batch'
SF_SRC="${LEAN_SRC}/L4Factoidal/Syntax/Utf8Stream.lean"
sf_probe SF-4 "Utf8Stream chunk decoding = whole-file decoding unproved" \
  feedChunks_eq_fromUTF8 '^def Utf8Stream\.feed ' 'Utf8Stream.feed'

# ---------------------------------------------------------------------
# SK-1 and SK-2 (https://github.com/danbri/factoidal/issues/852) -- the stream
# writers of the serialiser layer (formal/lean4/L4Factoidal/RDF/Sink.lean,
# `Writer.push`) have no theorem that relates them to the batch writers; the
# check is tests/sbm11/export_roundtrip.sh (51 pass, 0 fail, 1 expected-fail,
# out of 52 on 2026-10-14). Like SF-1 to SF-4, these probes read the SOURCE:
# XFAIL while no theorem of the name exists under formal/lean4. When one lands,
# the row reads XPASS: retire it, update issue 852 and docs/designissues/
# 2026-09-03-rdf-parsing-strategy.md section 3g in the same commit.
#   SK-1  writer_nquads_eq_toNQuads  (N-Triples and N-Quads: the text of the
#         stream writer is the text of the batch writer; leaf name)
#   SK-2  writer_turtle_readback     (Turtle and TriG: the text of the stream
#         writer reads back as the dataset it was given; leaf name)
# ---------------------------------------------------------------------
SK_SRC="${LEAN_SRC}/L4Factoidal/RDF/Sink.lean"
sk_probe () { # ID TITLE THEOREM
  local id="$1" title="$2" thm="$3"
  if [ ! -f "$SK_SRC" ]; then
    record "$id" 852 "$title" ERROR "${SK_SRC#"$ROOT"/} not found"
  elif ! grep -qE '^def Writer\.push ' "$SK_SRC"; then
    record "$id" 852 "$title" ERROR "probe drifted: Writer.push is no longer defined in ${SK_SRC#"$ROOT"/}"
  elif grep -rqE "^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(private[[:space:]]+)?(theorem|lemma)[[:space:]]+([A-Za-z0-9_.]*\.)?${thm//./\\.}\b" \
        "${LEAN_SRC}" --include='*.lean'; then
    record "$id" 852 "$title" XPASS "a theorem named ${thm} now exists"
  else
    record "$id" 852 "$title" XFAIL \
      "no ${thm} theorem in formal/lean4 (agreement is measured by tests/sbm11/export_roundtrip.sh only)"
  fi
}
sk_probe SK-1 "stream writer = batch writer for N-Triples and N-Quads unproved" writer_nquads_eq_toNQuads
sk_probe SK-2 "stream writer text reads back for Turtle and TriG unproved" writer_turtle_readback

# ---------------------------------------------------------------------
# RX-1 (https://github.com/danbri/factoidal/issues/936) -- the RDF/XML chunk
# fold of the source layer (formal/lean4/L4Factoidal/Syntax/RdfXmlChunkFold.lean,
# https://github.com/danbri/factoidal/issues/838) reads each child of rdf:RDF
# from its own character array. Its fall-back phases are proved equal to the
# whole-document reader (readAll_eq_whole_of_notStreamed); the children phase
# is measured only (l4rdfxml-chunk-diff: 2432 agree, 0 differ (out of 2432) on
# 2026-10-22). Like SF-1 to SF-4, this probe reads the SOURCE: XFAIL while no
# theorem named rdfxml_chunk_readAll_eq_whole exists under formal/lean4. When
# one lands, the row reads XPASS: retire it, close issue 936 and update
# docs/designissues/2026-09-03-rdf-parsing-strategy.md section 3k in the same
# commit.
# ---------------------------------------------------------------------
RX_SRC="${LEAN_SRC}/L4Factoidal/Syntax/RdfXmlChunkFold.lean"
if [ ! -f "$RX_SRC" ]; then
  record RX-1 936 "RDF/XML chunk fold = whole-document reader unproved" ERROR "${RX_SRC#"$ROOT"/} not found"
elif ! grep -qE '^def Body\.flush ' "$RX_SRC"; then
  record RX-1 936 "RDF/XML chunk fold = whole-document reader unproved" ERROR \
    "probe drifted: Body.flush is no longer defined in ${RX_SRC#"$ROOT"/}"
elif grep -rqE "^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(private[[:space:]]+)?(theorem|lemma)[[:space:]]+([A-Za-z0-9_.]*\.)?rdfxml_chunk_readAll_eq_whole\b" \
      "${LEAN_SRC}" --include='*.lean'; then
  record RX-1 936 "RDF/XML chunk fold = whole-document reader unproved" XPASS \
    "a theorem named rdfxml_chunk_readAll_eq_whole now exists"
else
  record RX-1 936 "RDF/XML chunk fold = whole-document reader unproved" XFAIL \
    "no rdfxml_chunk_readAll_eq_whole theorem in formal/lean4 (agreement is measured by l4rdfxml-chunk-diff only)"
fi

# ---------------------------------------------------------------------
# SR-1 (https://github.com/danbri/factoidal/issues/944) -- the Turtle and TriG
# split read (several readers, one for each byte range between the dot
# boundaries that formal/lean4/L4Factoidal/Syntax/TurtleSplitScan.lean finds;
# `Source.Reader.resume`; https://github.com/danbri/factoidal/issues/842) has
# no theorem that its quads equal the single reader's, blank-node labels
# included. It is measured only
# (tools/split-read-differential.sh: 17,962 agree, 0 differ (out of 17,962)
# over the W3C Turtle and TriG files and the tests/sbm11/syntax fixtures on
# 2026-10-22). Like SF-1 to SF-4, this
# probe reads the SOURCE: XFAIL while no theorem named splitRead_eq_single
# exists under formal/lean4. When one lands, the row reads XPASS: retire it,
# close issue 944 and update docs/designissues/2026-09-03-rdf-parsing-
# strategy.md section 3l in the same commit.
# ---------------------------------------------------------------------
SR_SRC="${LEAN_SRC}/L4Factoidal/Syntax/TurtleSplitScan.lean"
SR_TITLE="Turtle/TriG split read = single reader unproved"
if [ ! -f "$SR_SRC" ]; then
  record SR-1 944 "$SR_TITLE" ERROR "${SR_SRC#"$ROOT"/} not found"
elif ! grep -qE '^def Cold\.handle ' "$SR_SRC"; then
  record SR-1 944 "$SR_TITLE" ERROR "probe drifted: Cold.handle is no longer defined in ${SR_SRC#"$ROOT"/}"
elif grep -rqE "^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(private[[:space:]]+)?(theorem|lemma)[[:space:]]+([A-Za-z0-9_.]*\.)?splitRead_eq_single\b" \
      "${LEAN_SRC}" --include='*.lean'; then
  record SR-1 944 "$SR_TITLE" XPASS "a theorem named splitRead_eq_single now exists"
else
  record SR-1 944 "$SR_TITLE" XFAIL \
    "no splitRead_eq_single theorem in formal/lean4 (agreement is measured by tools/split-read-differential.sh only)"
fi

# ---------------------------------------------------------------------
# Summary + JSON
# ---------------------------------------------------------------------
TOTAL=$((XFAIL + XPASS + ERRORS))
mkdir -p "$(dirname "$JSON_OUT")"
{
  printf '{\n  "suite": "known-defects",\n'
  printf '  "description": "Defects found, proved and filed but not yet fixed. XFAIL = still reproduces (expected). XPASS = gone, update the test.",\n'
  printf '  "xfail": %d,\n  "xpass": %d,\n  "errors": %d,\n  "total": %d,\n' \
    "$XFAIL" "$XPASS" "$ERRORS" "$TOTAL"
  printf '  "cases": [\n'
  for i in "${!ROWS[@]}"; do
    printf '    %s' "${ROWS[$i]}"
    [ "$i" -lt $((${#ROWS[@]} - 1)) ] && printf ','
    printf '\n'
  done
  printf '  ]\n}\n'
} > "$JSON_OUT"

[ "$JSON_ONLY" = "1" ] || {
  printf '\nknown-defects: %d still present (XFAIL, expected), %d unexpectedly gone (XPASS), %d probe errors (out of %d)\n' \
    "$XFAIL" "$XPASS" "$ERRORS" "$TOTAL"
  printf 'wrote %s\n' "${JSON_OUT#"$ROOT"/}"
  if [ "$XPASS" -gt 0 ]; then
    printf '\n🔴 %d defect(s) no longer reproduce. That is not automatically good news:\n' "$XPASS"
    printf '   either somebody fixed it (delete the case + close the issue in the same\n'
    printf '   commit) or the probe drifted and has stopped measuring what it claims.\n'
  fi
}

# XPASS and ERROR both fail the suite. XFAIL alone is green.
[ "$XPASS" -eq 0 ] && [ "$ERRORS" -eq 0 ]
