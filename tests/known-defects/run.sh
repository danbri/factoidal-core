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
# F* OWL tableau defects found by the Lean tree
# (issues 719, 720; opened 2026-10-10 from the Lean repairs).
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
# control is an INCONSISTENT ontology; if the F* probe does not call it
# inconsistent, every OWL case below is an ERROR, not an XPASS.
# Lean must answer false (inconsistent) or unknown, never true. Since
# factoidal-core 87fd052e (2026-10-22) `owl-consistent` gives a verdict only
# with a checked certificate and answers unknown outside the admitted
# fragment (atomic classes and owl:someValuesFrom), which does not admit data
# cardinality restrictions
# (https://github.com/danbri/factoidal/issues/960). Until 2026-10-22 the
# control required Lean false, and the web gates of factoidal-builds failed
# from core 0a7fab49 (2026-10-22 22:25 UTC) to this change.
if [ -z "$OWL_PROBE_ERR" ]; then
  CTL_F=$(fstar_owl_verdict "${FIXTURES}/owl-control-inconsistent.rdf")
  CTL_L=$(lean_owl_verdict "${FIXTURES}/owl-control-inconsistent.rdf")
  if [ "$CTL_F" != "INCONSISTENT" ] || { [ "$CTL_L" != "false" ] && [ "$CTL_L" != "unknown" ]; }; then
    OWL_PROBE_ERR="sensitivity control owl-control-inconsistent.rdf: F* probe ${CTL_F}, Lean ${CTL_L} (F* must report inconsistent; Lean false or unknown)"
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
  # Lean true confirms the fixture. Lean unknown is no verdict: the public
  # operation answers true only with a checked model, and its reader admits
  # atomic classes and owl:someValuesFrom only, not the data cardinality
  # restrictions of these fixtures (issue 960); the fixture stays as confirmed
  # by the Lean tableau before 87fd052e. Lean false contradicts the fixture: ERROR.
  local oracle
  case "$lv" in
    true)    oracle="Lean reports consistent (correct)" ;;
    unknown) oracle="Lean gives no verdict (https://github.com/danbri/factoidal/issues/960)" ;;
    *)
      record "$id" "$issue" "$title" ERROR \
        "Lean oracle answered ${lv}; the expectation 'consistent' is contradicted or unconfirmed"
      return 0 ;;
  esac
  if [ "$fv" = "INCONSISTENT" ]; then
    record "$id" "$issue" "$title" XFAIL \
      "F* reports inconsistent; ${oracle}"
  elif [ "$fv" = "CONSISTENT" ]; then
    record "$id" "$issue" "$title" XPASS \
      "F* now reports consistent -- defect appears FIXED; ${oracle}"
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

# ---------------------------------------------------------------------
# F* command-line SPARQL defect found by the Lean vs F* differential
# (issue 747; opened 2026-10-10; record:
# docs/designissues/2026-10-10-lean-vs-fstar-differential.md). The query is a
# real W3C test file from third_party/testing/w3c. The case compares canonical
# rows from tests/known-defects/sparql_rows.py: the Lean CLI answer
# (`l4factoidal query`, the oracle) and the F* answer (`factoidal query -o
# json`). Equal domains are required, so a row that carries an extra binding
# is a different row (SPARQL 1.1 18.1.8).
# ---------------------------------------------------------------------
W3C_SPARQL10_SYNTAX="${ROOT}/third_party/testing/w3c/sparql/sparql10/syntax-sparql1"
ROWS_PY="${ROOT}/tests/known-defects/sparql_rows.py"

SPARQL_PROBE_ERR=""
if [ ! -x "$L4_BIN" ]; then
  SPARQL_PROBE_ERR="no l4factoidal at ${L4_BIN} (tools/fetch-builds.sh --set native)"
elif ! command -v python3 > /dev/null 2>&1; then
  SPARQL_PROBE_ERR="no python3 (sparql_rows.py reads the result sets)"
elif [ ! -r "${W3C_SPARQL10_SYNTAX}/syntax-forms-01.rq" ]; then
  SPARQL_PROBE_ERR="no W3C test files under third_party/testing/w3c (git submodule update --init --depth 1 third_party/testing/w3c)"
fi

# 747: the F* SPARQL parser gave a [ ] node that is an item of a collection
# the same blank node as the collection cell that holds it, so the cell was its
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
# The original defect (F* answers no row) is fixed: merge f074febcd (F* ports
# of Lean fixes, 2026-11-05) gives the expected row. The F* answer still has
# extra bindings: SELECT * projects the internal variables `?_bnode__:bnode_<n>`
# that the parser makes for the [ ] nodes, which 18.1.8 and 18.2.1 do not allow
# (a SELECT * row binds the variables in scope of the query pattern only).
#   XFAIL: the F* row is the expected row plus bindings of `?_bnode__:` variables.
#   XPASS: the F* row is exactly the expected row.
S747_TITLE="F* SELECT * projects internal variables for [ ] in a collection"
EXPECT747="?b=<http://example.org/ns#b1> ?pa=<http://example.org/ns#pa1> ?x=<http://example.org/ns#x1> ?y=<http://example.org/ns#y1>"
if [ -n "$SPARQL_PROBE_ERR" ]; then
  record SPARQL-747-COLLECTION-BNODE 747 "$S747_TITLE" ERROR "$SPARQL_PROBE_ERR"
else
  d="${WORKDIR}/q747"; mkdir -p "$d"
  data747="${ROOT}/tests/known-defects/fixtures/sparql-747-collection-bnode.ttl"
  q747="${W3C_SPARQL10_SYNTAX}/syntax-forms-01.rq"
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
  else
    # Remove the bindings of internal variables; the rest must be exactly the
    # expected row, and at least one binding must have been removed.
    sed -E 's/(^| )\?_bnode__:[^ =]+=[^ ]*//g; s/^ //' "$d/fstar.rows" > "$d/fstar.stripped"
    leaked=$(grep -o '?_bnode__:[^ =]*=' "$d/fstar.rows" | sort -u | wc -l | tr -d ' ')
    if [ "$leaked" -gt 0 ] && cmp -s "$d/fstar.stripped" "$d/expected.rows"; then
      record SPARQL-747-COLLECTION-BNODE 747 "$S747_TITLE" XFAIL \
        "F* answers the expected row plus ${leaked} internal variables (?_bnode__:...); the Lean CLI answers the expected row only"
    else
      record SPARQL-747-COLLECTION-BNODE 747 "$S747_TITLE" ERROR \
        "F* answer is neither the expected row nor the expected row plus ?_bnode__: bindings (answer drifted): $(head -n 1 "$d/fstar.rows" | cut -c1-100)"
    fi
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
# N3-1 (https://github.com/danbri/factoidal/issues/1172) -- no theorem says
# that the N3 reader on Turtle text gives the Turtle reader's graph. The
# agreement is measured only (`turtle-agreement` lines of tests/n3/run.sh).
# This probe reads the SOURCE: XFAIL while neither `parseN3_turtle11` (RDF 1.1
# Turtle) nor `parseN3_turtle12` (RDF 1.2 Turtle) is declared under
# formal/lean4/L4Factoidal/N3. When both exist this reads XPASS: retire the
# case and close issue 1172 in the same commit. One of the two is not enough.
# ---------------------------------------------------------------------
if [ ! -f "${LEAN_SRC}/L4Factoidal/N3/Parser.lean" ]; then
  record N3-1 1172 "N3 reader = Turtle reader on Turtle text has no theorem" ERROR \
    "formal/lean4/L4Factoidal/N3/Parser.lean not found"
elif grep -rqE '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?theorem[[:space:]]+([A-Za-z0-9_.]*\.)?parseN3_turtle11\b' \
       "${LEAN_SRC}/L4Factoidal/N3" --include='*.lean' \
     && grep -rqE '^[[:space:]]*(@\[[^]]*\][[:space:]]*)?theorem[[:space:]]+([A-Za-z0-9_.]*\.)?parseN3_turtle12\b' \
       "${LEAN_SRC}/L4Factoidal/N3" --include='*.lean'; then
  record N3-1 1172 "N3 reader = Turtle reader on Turtle text has no theorem" XPASS \
    "theorems parseN3_turtle11 and parseN3_turtle12 now exist"
else
  record N3-1 1172 "N3 reader = Turtle reader on Turtle text has no theorem" XFAIL \
    "no parseN3_turtle11 / parseN3_turtle12 theorem under formal/lean4/L4Factoidal/N3 (agreement measured only)"
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
# JS-1 (https://github.com/danbri/factoidal/issues/946) -- the JSON-LD item
# reader of the source layer (formal/lean4/L4Factoidal/Syntax/JsonLdChunkFold.lean,
# https://github.com/danbri/factoidal/issues/839) reads one top-level node
# object at a time. Its fall-back is proved equal to the whole-document reader
# (Source.jsonld_readAll_of_notStreamed); the item reading is measured only
# (l4jsonld-chunk-diff: 68,812 agree, 0 differ (out of 68,812) on 2026-10-22).
# XFAIL while no theorem named jsonld_chunk_readAll_eq_whole exists under
# formal/lean4. When one lands, the row reads XPASS: retire it, close issue 946
# and update docs/designissues/2026-09-03-rdf-parsing-strategy.md section 3n in
# the same commit.
# ---------------------------------------------------------------------
JS_SRC="${LEAN_SRC}/L4Factoidal/Syntax/JsonLdChunkFold.lean"
JS_TITLE="JSON-LD item reader = whole-document reader unproved"
if [ ! -f "$JS_SRC" ]; then
  record JS-1 946 "$JS_TITLE" ERROR "${JS_SRC#"$ROOT"/} not found"
elif ! grep -qE '^def State\.endItem ' "$JS_SRC"; then
  record JS-1 946 "$JS_TITLE" ERROR "probe drifted: State.endItem is no longer defined in ${JS_SRC#"$ROOT"/}"
elif grep -rqE "^[[:space:]]*(@\[[^]]*\][[:space:]]*)?(private[[:space:]]+)?(theorem|lemma)[[:space:]]+([A-Za-z0-9_.]*\.)?jsonld_chunk_readAll_eq_whole\b" \
      "${LEAN_SRC}" --include='*.lean'; then
  record JS-1 946 "$JS_TITLE" XPASS "a theorem named jsonld_chunk_readAll_eq_whole now exists"
else
  record JS-1 946 "$JS_TITLE" XFAIL \
    "no jsonld_chunk_readAll_eq_whole theorem in formal/lean4 (agreement is measured by l4jsonld-chunk-diff only)"
fi

# ---------------------------------------------------------------------
# JS-2 (https://github.com/danbri/factoidal/issues/947) -- the whole-document
# JSON-LD reader does not expand a top-level array when no base is given, so a
# node object's own @context is ignored (ToRdf.hasInlineContext is false for an
# array). JSON-LD 1.1 Expansion Algorithm expands each array item and processes
# an item's @context. Expected quad: <http://example.org/a> foaf:name "Alice".
# XFAIL while the parse gives no quad; XPASS when it gives the quad (retire the
# row, close issue 947, update section 3n of the parsing-strategy record).
# ---------------------------------------------------------------------
JS2_TITLE="JSON-LD top-level array ignores a node object's @context"
if [ ! -x "$L4_BIN" ]; then
  record JS-2 947 "$JS2_TITLE" ERROR "no l4factoidal at ${L4_BIN} (tools/fetch-builds.sh --set native)"
else
  printf '%s\n' '[{"@context":{"name":"http://xmlns.com/foaf/0.1/name"},"@id":"http://example.org/a","name":"Alice"}]' > "${WORKDIR}/js2.jsonld"
  printf '%s\n' '{"@context":{"name":"http://xmlns.com/foaf/0.1/name"},"@id":"http://example.org/a","name":"Alice"}' > "${WORKDIR}/js2-obj.jsonld"
  JS2_WANT='<http://example.org/a> <http://xmlns.com/foaf/0.1/name> "Alice" .'
  JS2_OBJ=$(timeout 60 "$L4_BIN" parse "${WORKDIR}/js2-obj.jsonld" --format jsonld --out nquads 2>/dev/null)
  JS2_ARR=$(timeout 60 "$L4_BIN" parse "${WORKDIR}/js2.jsonld" --format jsonld --out nquads 2>/dev/null)
  if [ "$JS2_OBJ" != "$JS2_WANT" ]; then
    record JS-2 947 "$JS2_TITLE" ERROR "oracle (same node as a top-level object) did not give the expected quad"
  elif [ "$JS2_ARR" = "$JS2_WANT" ]; then
    record JS-2 947 "$JS2_TITLE" XPASS "the array form now gives the expected quad"
  else
    record JS-2 947 "$JS2_TITLE" XFAIL "array form gives ${#JS2_ARR} bytes of N-Quads, expected the foaf:name quad"
  fi
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
# strategy.md section 3m in the same commit.
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
