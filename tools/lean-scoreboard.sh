#!/bin/bash
# tools/lean-scoreboard.sh -- run every Lean conformance runner against the
# real W3C (and other) test manifests and print ONE labelled table:
#
#   spec area | runner | pass | fail | skip/other | total | command
#
# The same rows are written as JSON (default .claude-runs/lean-scoreboard.json).
#
# Usage:
#   tools/lean-scoreboard.sh [--only RUNNER[,RUNNER...]] [--resume]
#                            [--json PATH] [--logdir PATH] [--timeout SECONDS]
#                            [--list]
#                            [--verbose] [-h|--help]
#
#   --only     Run a subset. A name is a runner (l4w3c, l4owl-probe, ...) or a
#              job id (l4w3c-sparql11, l4owl-probe-dl-inconsistency, ...).
#   --resume   Reuse a runner log under .claude-runs/lean-scoreboard/ when its
#              .meta file shows the run finished. A log with no .meta file (the
#              process died mid-run) is run again. Use this after a container
#              restart.
#   --json     Where to write the JSON rows.
#   --logdir   Where to keep the runner logs (default .claude-runs/lean-scoreboard).
#   --timeout  Wall-clock cap per runner, in seconds (default 1200).
#   --list     Print the job ids and commands, then exit.
#   --verbose  Also copy each runner's output to stderr while it runs.
#
# Rules this script follows:
#   * Every runner runs from the repository root, by the path of its built
#     binary (formal/lean4/.lake/build/bin/NAME). It never runs `lake`.
#   * Every runner is capped by timeout(1). A timeout is a row "TIMEOUT after
#     N s", never a pass count.
#   * The full output of every runner is saved with tee in
#     .claude-runs/lean-scoreboard/<runner>[-<variant>].log.
#   * Counts come from the runner's own summary line. If the line cannot be
#     parsed, the row says UNPARSED, keeps the raw line, and has parse=false.
#   * A runner that prints "manifest not found" or "directory not present",
#     or that discovers 0 tests, has MEASURED NOTHING. Its row is ERROR. The
#     script never turns such a run into a score (anti-pattern 3, 25, 30).
#   * Runners run one after another. The machine has 4 CPUs shared with other
#     work.
#
# Exit code: 0 when every row has a number and no row fails; 1 when at least
# one row fails; 3 when at least one row is ERROR, TIMEOUT or UNPARSED; 2 for
# a usage error. (3 takes precedence over 1.)
#
# Not in the table, on purpose: l4wasm-cli, l4factoidal (CLI tools, not
# conformance runners), l4xmpp-serve (a server), and the l4block-* tools (the
# persisted-store tools; their smoke tests are tools/blockengine-*-smoke.sh).
#
# Columns. "skip/other" is every count that is neither pass nor fail: skips,
# unsupported cases, undecided cases, local overrides, cases the runner could
# not read, cases it does not attempt. A row whose "other" has a meaning that
# the runner's own words do not give gets a numbered note under the table. When
# the runner prints no total, the script adds the counts and says so in the
# note. A "census" row (xmlconf-probe, the CSV reader probe) counts files and has
# no expected verdicts, so it shows "-" for pass and fail. A "none" row names a
# specification area for which the Lean tree has no runner.
#
# Written without bash 4 features (no associative arrays, no mapfile) so that
# it can run on macOS bash 3.2; it was tested only with bash 5.2.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT" || exit 2

BIN="formal/lean4/.lake/build/bin"
LOGDIR=".claude-runs/lean-scoreboard"
JSON_OUT=".claude-runs/lean-scoreboard.json"
RUNNER_TIMEOUT=1200
RESUME=0
ONLY=""
LIST_ONLY=0
VERBOSE=0

usage() { sed -n '2,/^set -uo/p' "$0" | sed -e '$d' -e 's/^# \{0,1\}//'; }

while [ $# -gt 0 ]; do
  case "$1" in
    --only)    ONLY="${2:-}"; shift 2 || { echo "lean-scoreboard: --only needs a value" >&2; exit 2; } ;;
    --resume)  RESUME=1; shift ;;
    --json)    JSON_OUT="${2:-}"; shift 2 || { echo "lean-scoreboard: --json needs a path" >&2; exit 2; } ;;
    --logdir)  LOGDIR="${2:-}"; shift 2 || { echo "lean-scoreboard: --logdir needs a path" >&2; exit 2; } ;;
    --timeout) RUNNER_TIMEOUT="${2:-}"; shift 2 || { echo "lean-scoreboard: --timeout needs a number" >&2; exit 2; } ;;
    --list)    LIST_ONLY=1; shift ;;
    --verbose) VERBOSE=1; shift ;;
    -h|--help) usage; exit 0 ;;
    *) echo "lean-scoreboard: unknown argument: $1" >&2; usage >&2; exit 2 ;;
  esac
done
case "$RUNNER_TIMEOUT" in ''|*[!0-9]*) echo "lean-scoreboard: --timeout must be a whole number of seconds" >&2; exit 2 ;; esac
[ -n "$JSON_OUT" ] && [ -n "$LOGDIR" ] || { echo "lean-scoreboard: --json and --logdir need a path" >&2; exit 2; }

TIMEOUT_BIN="$(command -v timeout || command -v gtimeout || true)"
if [ -z "$TIMEOUT_BIN" ] && [ "$LIST_ONLY" -eq 0 ]; then
  echo "lean-scoreboard: timeout(1) is required (GNU coreutils; on macOS: brew install coreutils)" >&2
  exit 2
fi

# The F* binary that l4diff compares against. Same platform directories the
# rest of the repository uses.
case "$(uname -s)" in
  Darwin) PLATFORM_DIR="darwin-$(uname -m)" ;;
  *)      PLATFORM_DIR="linux-$(uname -m)" ;;
esac

# --------------------------------------------------------------------------
# Paths of the suites (relative to the repository root).
# --------------------------------------------------------------------------
W3C="third_party/testing/w3c"
SHACL10="third_party/testing/shacl/data-shapes-test-suite/tests"
SHACL12="third_party/testing/shacl/shacl12-test-suite/tests"
OWLDIR="third_party/testing/owl"

# --------------------------------------------------------------------------
# Job table. One job is one run of one runner binary.
#
#   defjob ID RUNNER PARSER FAILKEY AREA LABEL ARGS [STDIN-SNIPPET]
#
# ID         log name; <runner> or <runner>-<variant>
# PARSER     function that turns the saved log into rows
# FAILKEY    selects how failing test ids are read from the log
# AREA/LABEL default row text; used for the single ERROR/TIMEOUT row of a job
# ARGS       argument string, already shell-quoted
# STDIN      shell snippet whose output feeds the runner's standard input
# --------------------------------------------------------------------------
JOB_N=0
defjob() {
  local n=$JOB_N
  JOB_ID[$n]="$1"; JOB_RUNNER[$n]="$2"; JOB_PARSER[$n]="$3"; JOB_FAILKEY[$n]="$4"
  JOB_AREA[$n]="$5"; JOB_LABEL[$n]="$6"; JOB_ARGS[$n]="$7"; JOB_STDIN[$n]="${8:-}"
  JOB_N=$((n + 1))
}

# --- SPARQL ---------------------------------------------------------------
defjob l4w3c-sparql11 l4w3c parse_sparql11 w3c \
  "SPARQL 1.1 (query+update+protocol, manifest-all)" "" \
  "--quiet $W3C/sparql/sparql11/manifest-all.ttl"
defjob l4sparql-probe l4sparql-probe parse_sparql_probe none \
  "SPARQL 1.1 query syntax (parser only, no evaluation)" "" \
  "$W3C/sparql/sparql11"
defjob l4w3c-sparql12 l4w3c parse_w3c_total w3c \
  "SPARQL 1.2" "" \
  "--quiet $W3C/sparql/sparql12/manifest.ttl"
# --- RDF 1.1 syntaxes and semantics ----------------------------------------
defjob l4w3c-rdf11 l4w3c parse_rdf11 w3c \
  "RDF 1.1 syntaxes + rdf-mt" "" \
  "--quiet $W3C/rdf/rdf11/manifest.ttl"
defjob l4turtle-probe l4turtle-probe parse_turtle_probe turtle_probe \
  "RDF 1.1 Turtle/TriG (file-name probe)" "" \
  "$W3C/rdf/rdf11"
defjob l4rdfxml-probe l4rdfxml-probe parse_rdfxml_probe none \
  "RDF 1.1 RDF/XML (probe)" "" \
  "$W3C/rdf/rdf11/rdf-xml"
# --- RDF 1.2 ---------------------------------------------------------------
defjob l4w3c-rdf12 l4w3c parse_rdf12 w3c \
  "RDF 1.2 syntaxes" "" \
  "--quiet $W3C/rdf/rdf12/manifest.ttl"
defjob l4rdf-semantics l4rdf-semantics parse_rdf_semantics w3c \
  "RDF 1.2 rdf-semantics (entailment)" "" \
  "$W3C/rdf/rdf12/rdf-semantics/manifest.ttl"
# --- RDFC-1.0 ----------------------------------------------------------------
defjob l4w3c-rdfc l4w3c parse_w3c_total w3c \
  "RDFC-1.0" "manifest-driven" \
  "--quiet third_party/testing/rdf-canon/tests/manifest.ttl"
defjob l4rdfc-probe l4rdfc-probe parse_rdfc_probe none \
  "RDFC-1.0" "probe" \
  "third_party/testing/rdf-canon/tests/rdfc10"
# --- OWL 2 -------------------------------------------------------------------
defjob l4owl-probe-rl l4owl-probe parse_owl owl \
  "OWL 2, RL closure regime" "" \
  "--dir $OWLDIR"
defjob l4owl-probe-rl-extra l4owl-probe parse_owl owl \
  "OWL 2, RL closure regime" "" \
  "--dir $OWLDIR type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf"
defjob l4owl-probe-dl-inconsistency l4owl-probe parse_owl owl \
  "OWL 2, DL regime (RL closure + tableau refuter)" "" \
  "--dir $OWLDIR --dl --refute-ms 3000 type-inconsistency.rdf"
defjob l4owl-probe-dl-positive-entailment l4owl-probe parse_owl owl \
  "OWL 2, DL regime (RL closure + tableau refuter)" "" \
  "--dir $OWLDIR --dl --refute-ms 3000 type-positive-entailment.rdf"
defjob l4owl-probe-dl-consistency l4owl-probe parse_owl owl \
  "OWL 2, DL regime (RL closure + tableau refuter)" "" \
  "--dir $OWLDIR --dl --refute-ms 3000 type-consistency.rdf"
defjob l4owl-probe-dl-syntax l4owl-probe parse_owl owl \
  "OWL 2, DL regime (RL closure + tableau refuter)" "" \
  "--dir $OWLDIR --dl --refute-ms 3000 syntax-dl.rdf"
# --- SHACL -------------------------------------------------------------------
defjob l4shacl-core10 l4shacl parse_shacl shacl \
  "SHACL Core (1.0 suite)" "" \
  "$SHACL10/core/manifest.ttl"
defjob l4shacl-sparql10 l4shacl parse_shacl shacl \
  "SHACL-SPARQL (1.0 suite)" "" \
  "$SHACL10/sparql/manifest.ttl"
defjob l4shacl-core12 l4shacl parse_shacl shacl \
  "SHACL 1.2 core" "" \
  "$SHACL12/core/manifest.ttl"
defjob l4shacl-sparql12 l4shacl parse_shacl shacl \
  "SHACL 1.2 sparql" "" \
  "$SHACL12/sparql/manifest.ttl"
defjob l4shacl-nodeexpr l4shacl-nodeexpr parse_shacl_nodeexpr w3c \
  "SHACL 1.2 node expressions" "" ""
defjob l4shacl-rules l4shacl-rules parse_shacl_rules w3c \
  "SHACL 1.2 rules" "" ""
# --- ShEx --------------------------------------------------------------------
defjob l4shex l4shex parse_shex shex \
  "ShEx (ShExJ validation suite)" "" \
  "--verbose"
defjob l4shexc l4shexc parse_shexc shexc \
  "ShEx (ShExC parser vs ShExJ twins)" "" ""
# --- RIF ---------------------------------------------------------------------
defjob l4rif l4rif parse_rif rif \
  "RIF Core" "" ""
# --- CSVW --------------------------------------------------------------------
defjob l4csvw-rdf l4csvw-rdf parse_csvw_rdf csvw \
  "CSVW csv2rdf" "" ""
defjob l4csvw-json l4csvw-json parse_csvw_json csvw \
  "CSVW csv2json" "" ""
defjob l4csvw-validate l4csvw-validate parse_csvw_validate csvw \
  "CSVW validation" "" ""
defjob l4csvw-probe l4csvw-probe parse_csvw_probe none \
  "CSVW CSV reader" "census" ""
# --- XML stack ---------------------------------------------------------------
defjob l4xmlconf l4xmlconf parse_xmlconf xmlconf \
  "XML 1.0 conformance (xmlconf)" "" ""
defjob xmlconf-probe xmlconf-probe parse_xmlconf_probe none \
  "XML 1.0 conformance (xmlconf)" "census" "" \
  "find third_party/testing/xml/xmlconf -type f -name '*.xml' | LC_ALL=C sort"
defjob l4xpath l4xpath parse_xpath xpath \
  "XPath 1.0 (repo unit battery tests/unit/xpath_cases.json)" "" ""
defjob l4xslt l4xslt parse_xslt xslt \
  "XSLT 1.0" "" ""
defjob l4schematron l4schematron parse_schematron schematron \
  "Schematron" "" ""
defjob l4mathml l4mathml parse_mathml mathml \
  "MathML (Content)" "" ""
defjob l4jsonschema l4jsonschema parse_jsonschema jsonschema \
  "JSON Schema draft-07" "" ""
defjob l4xsd-datatypes l4xsd-datatypes parse_xsd xsd \
  "XSD datatypes (W3C XSD test suite, instance tests)" "" \
  "--verbose"
# --- JSON-LD -----------------------------------------------------------------
defjob l4jsonld-probe l4jsonld-probe parse_jsonld_probe jsonld \
  "JSON-LD toRdf" "" ""
defjob l4jsonld-api l4jsonld-api parse_jsonld_api jsonld \
  "JSON-LD" "" ""
defjob l4jsonld-frame l4jsonld-frame parse_jsonld_frame jsonld_frame \
  "JSON-LD framing" "" ""
# --- RML ---------------------------------------------------------------------
defjob l4rml l4rml parse_rml rml \
  "RML Core" "" ""
# --- VC / DID / JOSE / crypto --------------------------------------------------
defjob l4vc-probe l4vc-probe parse_block_rows bracket \
  "VC / DID / Data Integrity" "" ""
defjob l4jose-probe l4jose-probe parse_block_rows bracket \
  "JOSE / DPoP / Solid-OIDC" "" ""
defjob l4crypto-probe l4crypto-probe parse_block_rows bracket \
  "Crypto primitives (RFC vectors, Wycheproof)" "" ""
# --- GeoSPARQL, GRDDL, HDT -------------------------------------------------------
defjob l4geo l4geo parse_geo geo \
  "GeoSPARQL (v0 unit pin; not the OGC suite)" "" ""
defjob l4grddl l4grddl parse_grddl grddl \
  "GRDDL" "" ""
defjob l4hdt l4hdt parse_hdt hdt \
  "HDT container" "" ""
# --- LWS / Solid -------------------------------------------------------------------
defjob l4lws-probe l4lws-probe parse_registry lws \
  "LWS 1.0 core" "" ""
defjob l4solid-probe l4solid-probe parse_registry lws \
  "Solid Protocol + WAC" "" ""
# --- Parity and invariant batteries (not W3C suites) --------------------------------
defjob l4toan l4toan parse_toan toan \
  "Think-of-a-Number parity battery (Math + MathML)" "" ""
defjob l4prop l4prop parse_prop prop \
  "Property-based invariants (generated cases)" "" ""
defjob l4rdfs-semi l4rdfs-semi parse_rdfs_semi none \
  "RDFS closure, semi-naive vs naive (equivalence)" "" ""
defjob l4diff l4diff parse_diff diff \
  "Differential vs F* engine (SPARQL 1.1 manifest-all)" "" \
  "--fstar bin/$PLATFORM_DIR/factoidal $W3C/sparql/sparql11/manifest-all.ttl"

# Areas with no Lean runner. Each claim was checked against
# formal/lean4/Harness/*.lean and lakefile.lean when this script was written.
NONE_ROWS="XForms (Bind, recalculate)|Lean library L4Factoidal/XForms/Bind.lean has build-time #guard checks only; no Harness runner
ShEx negative syntax (100 ShExC reject fixtures)|l4shexc compares ShExC with ShExJ twins only; the reject fixtures are not read
RML-IO, RML-FNML, RML-CC, RML-star test cases|l4rml reads rml-core test-cases only
EECC interop (vc-verifier-rules, webuild-attestations)|no Lean module or runner
QUDT|no Lean module or runner"

# --------------------------------------------------------------------------
# Row storage. Fields are separated by the ASCII unit separator, because bash
# read collapses empty fields when the separator is a tab.
# --------------------------------------------------------------------------
US=$'\037'
ROWS=()
ROW_N=0

# Text that must not contain the field separator or line breaks.
clean() { printf '%s' "$1" | tr '\r\n\t\037' '    '; }

CUR_ID=""; CUR_RUNNER=""; CUR_AREA=""; CUR_LABEL=""; CUR_CMD=""; CUR_LOG=""
CUR_SECS=0; CUR_RC=0; CUR_IDX=0

# add_row STATUS AREA LABEL PASS FAIL OTHER TOTAL PARSE NOTE RAW DETAIL
add_row() {
  local status="$1" area="$2" label="$3" p="$4" f="$5" o="$6" t="$7" parse="$8" note="$9" raw="${10}" detail="${11:-}"
  ROWS[$ROW_N]="$(clean "$area")${US}$(clean "$CUR_RUNNER")${US}$(clean "$label")${US}${status}${US}${p}${US}${f}${US}${o}${US}${t}${US}${parse}${US}$(clean "$note")${US}$(clean "$CUR_CMD")${US}$(clean "$CUR_LOG")${US}${CUR_SECS}${US}${CUR_RC}${US}$(clean "$raw")${US}$(clean "$detail")${US}$(clean "$CUR_ID")"
  ROW_N=$((ROW_N + 1))
  JOB_ROWS=$((JOB_ROWS + 1))
  if [ "$status" = ok ] && [ "${f:-0}" -gt 0 ] 2>/dev/null; then JOB_FAILS=$((JOB_FAILS + f)); fi
  return 0
}

# append_note IDX TEXT -- add TEXT to the note field (field 10) of stored row IDX.
append_note() {
  local idx="$1" text="$2" a r l st p f o t pa nt c lg se rc rw d id
  IFS="$US" read -r a r l st p f o t pa nt c lg se rc rw d id <<EOF2
${ROWS[$idx]}
EOF2
  nt="${nt:+$nt; }$text"
  ROWS[$idx]="${a}${US}${r}${US}${l}${US}${st}${US}${p}${US}${f}${US}${o}${US}${t}${US}${pa}${US}${nt}${US}${c}${US}${lg}${US}${se}${US}${rc}${US}${rw}${US}${d}${US}${id}"
}

# emit_status STATUS AREA LABEL REASON [RAW]   -- a row with no numbers
emit_status() {
  local status="$1" area="$2" label="$3" reason="$4" raw="${5:-}" parse="false"
  [ "$status" = error ] || [ "$status" = timeout ] && parse="n/a"
  add_row "$status" "$area" "$label" "" "" "" "" "$parse" "$reason" "$raw" ""
}

# emit_ok AREA LABEL P F O T NOTE RAW [DETAIL]
emit_ok() {
  local area="$1" label="$2" p="$3" f="$4" o="$5" t="$6" note="$7" raw="$8" detail="${9:-}"
  if [ "$t" -eq 0 ]; then
    emit_status error "$area" "$label" "discovered 0 tests (out of 0); nothing was measured" "$raw"
    return 0
  fi
  if [ $((p + f + o)) -ne "$t" ]; then
    note="! pass+fail+other is $((p + f + o)) but the runner says out of $t${note:+; $note}"
  fi
  add_row ok "$area" "$label" "$p" "$f" "$o" "$t" true "$note" "$raw" "$detail"
}

# --------------------------------------------------------------------------
# Log reading helpers. All read $CUR_LOG.
# --------------------------------------------------------------------------

# pick_line ERE [first|last] -- one matching line, or nothing.
pick_line() {
  if [ "${2:-last}" = first ]; then
    grep -E -m1 -- "$1" "$CUR_LOG"
  else
    grep -E -- "$1" "$CUR_LOG" | sed -n '$p'
  fi
}

# scoreline_nums LINE -- print "PASS FAIL OTHER TOTAL" for a line of the form
#   LABEL: N pass, M fail[, K word]... (out of T[ word])
# Any count that is not "pass" or "fail" counts as OTHER. Returns 1 when the
# line does not have that form.
scoreline_nums() {
  local line="$1" head counts piece n word p=0 f=0 o=0 t re
  re='\(out of ([0-9]+)'
  [[ "$line" =~ $re ]] || return 1
  t="${BASH_REMATCH[1]}"
  head="${line%%\(out of*}"
  counts="${head##*: }"
  re='^([0-9]+) +(.+)$'
  local oldifs="$IFS"
  IFS=','
  for piece in $counts; do
    piece="${piece#"${piece%%[! ]*}"}"
    piece="${piece%"${piece##*[! ]}"}"
    if ! [[ "$piece" =~ $re ]]; then IFS="$oldifs"; return 1; fi
    n="${BASH_REMATCH[1]}"; word="${BASH_REMATCH[2]}"
    case "$word" in
      pass) p=$((p + n)) ;;
      fail) f=$((f + n)) ;;
      *)    o=$((o + n)) ;;
    esac
  done
  IFS="$oldifs"
  printf '%s %s %s %s\n' "$p" "$f" "$o" "$t"
}

# nofd_nums LINE -- for "LABEL: N of D": PASS=N, FAIL=D-N.
nofd_nums() {
  local line="$1" re='([0-9]+) of ([0-9]+)' n d
  [[ "${line##*: }" =~ $re ]] || return 1
  n="${BASH_REMATCH[1]}"; d="${BASH_REMATCH[2]}"
  [ "$n" -le "$d" ] || return 1
  printf '%s %s 0 %s\n' "$n" $((d - n)) "$d"
}

# line_int ERE -- first integer after the label colon of the last matching line.
line_int() {
  local l v
  l="$(pick_line "$1" last)"
  [ -n "$l" ] || return 1
  v="$(printf '%s\n' "$l" | sed -nE 's/^[^:]*:[[:space:]]*([0-9]+).*$/\1/p')"
  [ -n "$v" ] || return 1
  printf '%s\n' "$v"
}

# row_sl AREA LABEL ERE [first|last] [NOTE] -- one row from a score line.
row_sl() {
  local area="$1" label="$2" re="$3" which="${4:-last}" note="${5:-}" line nums
  line="$(pick_line "$re" "$which")"
  if [ -z "$line" ]; then
    emit_status unparsed "$area" "$label" "no line matching /$re/ in the log"
    return 1
  fi
  if ! nums="$(scoreline_nums "$line")"; then
    emit_status unparsed "$area" "$label" "summary line does not follow 'N pass, M fail (out of T)'" "$line"
    return 1
  fi
  set -- $nums
  emit_ok "$area" "$label" "$1" "$2" "$3" "$4" "$note" "$line"
}

# row_nofd AREA LABEL ERE [first|last] [NOTE] -- one row from "LABEL: N of D".
row_nofd() {
  local area="$1" label="$2" re="$3" which="${4:-last}" note="${5:-}" line nums
  line="$(pick_line "$re" "$which")"
  if [ -z "$line" ]; then
    emit_status unparsed "$area" "$label" "no line matching /$re/ in the log"
    return 1
  fi
  if ! nums="$(nofd_nums "$line")"; then
    emit_status unparsed "$area" "$label" "summary line does not follow 'N of D'" "$line"
    return 1
  fi
  set -- $nums
  emit_ok "$area" "$label" "$1" "$2" "$3" "$4" "${note:+$note; }fail = D minus N (the runner prints 'N of D')" "$line"
}

# rows_for_labels AREA_PREFIX ERE_BUILDER ... is avoided; each parser below
# lists its rows explicitly.

# block_rows AREA ERE -- one row for every distinct label among the lines
# matching ERE (last occurrence wins), in order of first appearance. TOTAL
# lines are skipped: catalogs overlap, so a total double-counts units.
block_rows() {
  local area="$1" re="$2" line head counts label labels="" seen found=0 l2
  while IFS= read -r line; do
    [ -n "$line" ] || continue
    head="${line%%\(out of*}"; counts="${head##*: }"; label="${head%": $counts"}"
    case "$label" in TOTAL*|*" TOTAL"*) continue ;; esac
    case "$labels" in *"${US}${label}${US}"*) ;; *) labels="${labels}${US}${label}${US}" ;; esac
  done < <(grep -E -- "$re" "$CUR_LOG")
  # Walk the labels in order of first appearance.
  local rest="$labels" lab
  while [ -n "$rest" ]; do
    rest="${rest#"$US"}"; lab="${rest%%"$US"*}"; rest="${rest#"$lab"}"; rest="${rest#"$US"}"
    [ -n "$lab" ] || continue
    found=1
    l2="$(grep -E -- "$re" "$CUR_LOG" | while IFS= read -r line; do
            head="${line%%\(out of*}"; counts="${head##*: }"
            if [ "${head%": $counts"}" = "$lab" ]; then printf '%s\n' "$line"; fi
          done | sed -n '$p')"
    [ -n "$l2" ] || continue
    local nums
    if nums="$(scoreline_nums "$l2")"; then
      set -- $nums
      emit_ok "$area" "$lab" "$1" "$2" "$3" "$4" "" "$l2"
    else
      emit_status unparsed "$area" "$lab" "summary line does not follow 'N pass, M fail (out of T)'" "$l2"
    fi
  done
  if [ "$found" -eq 0 ]; then
    emit_status unparsed "$area" "" "no line matching /$re/ in the log"
  fi
}

# --------------------------------------------------------------------------
# Parsers. Each reads $CUR_LOG and calls emit_*. A parser that emits nothing
# is turned into an UNPARSED row by the caller.
# --------------------------------------------------------------------------
parse_w3c_total() {
  row_sl "$CUR_AREA" "$CUR_LABEL" '^TOTAL: [0-9]+ pass' last
}

parse_sparql11() {
  local detail
  detail="$(grep -E '^[A-Za-z0-9_/-]+: [0-9]+ pass, [0-9]+ fail.*\(out of [0-9]+\)$' "$CUR_LOG" | grep -v '^TOTAL:' | paste -s -d ';' - | sed 's/;/; /g')"
  local line nums
  line="$(pick_line '^TOTAL: [0-9]+ pass' last)"
  if [ -z "$line" ]; then emit_status unparsed "$CUR_AREA" "" "no TOTAL line in the log"; return; fi
  if ! nums="$(scoreline_nums "$line")"; then emit_status unparsed "$CUR_AREA" "" "TOTAL line does not follow the score-line grammar" "$line"; return; fi
  set -- $nums
  emit_ok "$CUR_AREA" "" "$1" "$2" "$3" "$4" "per-suite counts are in the JSON detail field" "$line" "$detail"
}

parse_sparql_probe() {
  row_sl "$CUR_AREA" "" '^TOTAL \(manifest-listed query files\): [0-9]+ pass' last \
    "* 12 query files in no manifest are not scored; 55 update files are out of scope for this probe"
}

parse_rdf11() {
  row_sl "RDF 1.1 syntax: N-Triples" "" '^rdf-n-triples: [0-9]+ pass' last
  row_sl "RDF 1.1 syntax: N-Quads" "" '^rdf-n-quads: [0-9]+ pass' last
  row_sl "RDF 1.1 syntax: Turtle" "" '^rdf-turtle: [0-9]+ pass' last
  row_sl "RDF 1.1 syntax: TriG" "" '^rdf-trig: [0-9]+ pass' last
  row_sl "RDF 1.1 syntax: RDF/XML" "" '^rdf-xml: [0-9]+ pass' last
  row_sl "RDF 1.1 rdf-mt (semantics/entailment)" "" '^rdf-mt: [0-9]+ pass' last
}

parse_turtle_probe() {
  local sec key line nums area
  for sec in turtle trig; do
    for key in parse-positive reject-negative eval-iso; do
      line="$(awk -v sec="$sec" -v key="$key" '
        /^=== rdf-turtle/ { s = "turtle" }
        /^=== rdf-trig/   { s = "trig" }
        s == sec && index($0, key ": ") == 1 { l = $0 }
        END { if (l != "") print l }' "$CUR_LOG")"
      if [ "$sec" = turtle ]; then area="RDF 1.1 Turtle (file-name probe)"; else area="RDF 1.1 TriG (file-name probe)"; fi
      if [ -z "$line" ]; then emit_status unparsed "$area" "$key" "no '$key: N of D' line in the $sec section"; continue; fi
      if ! nums="$(nofd_nums "$line")"; then emit_status unparsed "$area" "$key" "line does not follow 'N of D'" "$line"; continue; fi
      set -- $nums
      emit_ok "$area" "$key" "$1" "$2" "$3" "$4" "fail = D minus N (the probe prints 'N of D'); the probe walks files by name, the manifest-driven row is l4w3c" "$line"
    done
  done
}

parse_rdfxml_probe() {
  local k
  for k in parse-positive reject-negative eval-isomorphic; do
    row_sl "RDF 1.1 RDF/XML (probe)" "$k" "^$k: [0-9]+ pass" last
  done
}

parse_rdf12() {
  row_sl "RDF 1.2 syntax: N-Triples" "syntax" '^rdf-n-triples/syntax: [0-9]+ pass' last
  row_sl "RDF 1.2 syntax: N-Triples" "c14n" '^rdf-n-triples/c14n: [0-9]+ pass' last
  row_sl "RDF 1.2 syntax: N-Quads" "syntax" '^rdf-n-quads/syntax: [0-9]+ pass' last
  row_sl "RDF 1.2 syntax: N-Quads" "c14n" '^rdf-n-quads/c14n: [0-9]+ pass' last
  row_sl "RDF 1.2 syntax: Turtle" "syntax" '^rdf-turtle/syntax: [0-9]+ pass' last
  row_sl "RDF 1.2 syntax: Turtle" "eval" '^rdf-turtle/eval: [0-9]+ pass' last
  row_sl "RDF 1.2 syntax: TriG" "syntax" '^rdf-trig/syntax: [0-9]+ pass' last
  row_sl "RDF 1.2 syntax: TriG" "eval" '^rdf-trig/eval: [0-9]+ pass' last
  row_sl "RDF 1.2 syntax: RDF/XML" "eval" '^rdf-xml/eval: [0-9]+ pass' last
}

parse_rdf_semantics() {
  row_sl "$CUR_AREA" "" '^rdf-semantics: [0-9]+ pass' last
}

parse_rdfc_probe() {
  row_nofd "RDFC-1.0" "probe: SHA-256 eval tests" '^rdfc10 eval: [0-9]+ of [0-9]+' last
  row_nofd "RDFC-1.0" "probe: SHA-384 eval tests" '^sha384 eval: [0-9]+ of [0-9]+' last
  row_nofd "RDFC-1.0" "probe: map tests" '^rdfc10 map eval: [0-9]+ of [0-9]+' last
  row_nofd "RDFC-1.0" "probe: negative eval (excessive-calls abort)" '^negative eval \(excessive-calls abort\): [0-9]+ of [0-9]+' last
}

parse_owl() {
  # Catalog rows overlap (type-consistency.rdf contains the positive-entailment
  # units too), so no TOTAL row is emitted.
  block_rows "$CUR_AREA" '^(profile|type|syntax|semantics)-[A-Za-z-]+\.rdf( [A-Za-z]+Test)?: [0-9]+ pass, [0-9]+ fail.*\(out of [0-9]+\)$'
}

parse_shacl() {
  row_sl "$CUR_AREA" "" '^shacl-(core|sparql) TOTAL: [0-9]+ pass' last
}
parse_shacl_nodeexpr() { row_sl "$CUR_AREA" "" '^shacl 1\.2 node-expr TOTAL: [0-9]+ pass' last; }
parse_shacl_rules()    { row_sl "$CUR_AREA" "" '^shacl 1\.2 rules TOTAL: [0-9]+ pass' last; }

parse_shex() {
  local line nums tot nr
  line="$(pick_line '^shex validation: [0-9]+ pass' last)"
  if [ -z "$line" ]; then emit_status unparsed "$CUR_AREA" "" "no 'shex validation:' line in the log"; return; fi
  if ! nums="$(scoreline_nums "$line")"; then emit_status unparsed "$CUR_AREA" "" "summary line does not follow the score-line grammar" "$line"; return; fi
  nr="$(line_int '^NOT READ: [0-9]+ entries')" || { emit_status unparsed "$CUR_AREA" "" "no 'NOT READ: N entries' line" "$line"; return; }
  tot="$(pick_line '^NOT READ: [0-9]+ entries' last | sed -nE 's/.*\(out of ([0-9]+)\).*/\1/p')"
  [ -n "$tot" ] || { emit_status unparsed "$CUR_AREA" "" "no '(out of T)' on the NOT READ line" "$line"; return; }
  set -- $nums
  emit_ok "$CUR_AREA" "" "$1" "$2" "$nr" "$tot" "other = entries the reader could not read (not a verdict)" "$line"
}

parse_shexc() {
  local line m x tot dec nr
  line="$(pick_line '^ShExC DIFFERENTIAL: [0-9]+ match' last)"
  if [ -z "$line" ]; then emit_status unparsed "$CUR_AREA" "" "no 'ShExC DIFFERENTIAL:' line in the log"; return; fi
  m="$(printf '%s\n' "$line" | sed -nE 's/^ShExC DIFFERENTIAL: ([0-9]+) match, ([0-9]+) mismatch.*$/\1/p')"
  x="$(printf '%s\n' "$line" | sed -nE 's/^ShExC DIFFERENTIAL: ([0-9]+) match, ([0-9]+) mismatch.*$/\2/p')"
  dec="$(line_int '^DECLINED: [0-9]+ schemas')" || dec=""
  nr="$(line_int '^NO REFERENCE: [0-9]+ schemas')" || nr=""
  tot="$(grep -E '^[[:space:]]+\(out of [0-9]+ \.shex files\)' "$CUR_LOG" | sed -nE 's/^[[:space:]]+\(out of ([0-9]+) \.shex files\).*$/\1/p' | sed -n '$p')"
  if [ -z "$m" ] || [ -z "$x" ] || [ -z "$dec" ] || [ -z "$nr" ] || [ -z "$tot" ]; then
    emit_status unparsed "$CUR_AREA" "" "a count is missing (match, mismatch, DECLINED, NO REFERENCE, .shex total)" "$line"; return
  fi
  emit_ok "$CUR_AREA" "" "$m" "$x" $((dec + nr)) "$tot" "pass = ShExC parse equals the ShExJ twin; other = declined by the parser ($dec) + no ShExJ twin ($nr)" "$line"
}

parse_rif() {
  local line nums u nr lo
  line="$(pick_line '^rif-core DECIDED: [0-9]+ pass' last)"
  if [ -z "$line" ]; then emit_status unparsed "$CUR_AREA" "" "no 'rif-core DECIDED:' line in the log"; return; fi
  if ! nums="$(scoreline_nums "$line")"; then emit_status unparsed "$CUR_AREA" "" "summary line does not follow the score-line grammar" "$line"; return; fi
  u="$(line_int '^UNDECIDED: [0-9]+ cases')" || u=""
  nr="$(line_int '^NOT READ: [0-9]+ cases')" || nr=""
  lo="$(line_int '^LOCAL OVERRIDE: [0-9]+ cases')" || lo=""
  if [ -z "$u" ] || [ -z "$nr" ] || [ -z "$lo" ]; then
    emit_status unparsed "$CUR_AREA" "" "a count is missing (UNDECIDED, NOT READ, LOCAL OVERRIDE)" "$line"; return
  fi
  set -- $nums
  emit_ok "$CUR_AREA" "" "$1" "$2" $((u + nr + lo)) $(($1 + $2 + u + nr + lo)) \
    "total derived: decided $(($1 + $2)) + undecided $u + not read $nr + local override $lo; the runner prints no total" "$line"
}

parse_csvw_rdf()      { row_sl "$CUR_AREA" "" '^csv2rdf TOTAL: [0-9]+ pass' last; }
parse_csvw_json()     { row_sl "$CUR_AREA" "" '^csv2json TOTAL: [0-9]+ pass' last; }
parse_csvw_validate() { row_sl "$CUR_AREA" "" '^csvw-validation: [0-9]+ pass' last; }

parse_csvw_probe() {
  local line u r f t
  line="$(pick_line '^csvw READER probe: ' last)"
  if [ -z "$line" ]; then emit_status unparsed "$CUR_AREA" "$CUR_LABEL" "no 'csvw READER probe:' line in the log"; return; fi
  u="$(printf '%s\n' "$line" | sed -nE 's/^csvw READER probe: ([0-9]+) read with uniform width, ([0-9]+) read ragged.*, ([0-9]+) failed to read \(out of ([0-9]+) \.csv files\).*$/\1/p')"
  r="$(printf '%s\n' "$line" | sed -nE 's/^csvw READER probe: ([0-9]+) read with uniform width, ([0-9]+) read ragged.*, ([0-9]+) failed to read \(out of ([0-9]+) \.csv files\).*$/\2/p')"
  f="$(printf '%s\n' "$line" | sed -nE 's/^csvw READER probe: ([0-9]+) read with uniform width, ([0-9]+) read ragged.*, ([0-9]+) failed to read \(out of ([0-9]+) \.csv files\).*$/\3/p')"
  t="$(printf '%s\n' "$line" | sed -nE 's/^csvw READER probe: ([0-9]+) read with uniform width, ([0-9]+) read ragged.*, ([0-9]+) failed to read \(out of ([0-9]+) \.csv files\).*$/\4/p')"
  if [ -z "$u" ] || [ -z "$r" ] || [ -z "$f" ] || [ -z "$t" ]; then
    emit_status unparsed "$CUR_AREA" "$CUR_LABEL" "summary line does not have the expected shape" "$line"; return
  fi
  if [ "$t" -eq 0 ]; then emit_status error "$CUR_AREA" "$CUR_LABEL" "read 0 files; nothing was measured" "$line"; return; fi
  add_row census "$CUR_AREA" "$CUR_LABEL" "" "" "$t" "$t" true \
    "* NOT a conformance score: $((u + r)) CSV files read ($u uniform width, $r ragged), $f failed to read; the probe does not compare with the expected output" "$line" ""
}

parse_xmlconf() {
  local line nums oop n sum=0 total
  line="$(pick_line '^xml conformance SCORED: [0-9]+ pass' last)"
  if [ -z "$line" ]; then emit_status unparsed "$CUR_AREA" "" "no 'xml conformance SCORED:' line in the log"; return; fi
  if ! nums="$(scoreline_nums "$line")"; then emit_status unparsed "$CUR_AREA" "" "summary line does not follow the score-line grammar" "$line"; return; fi
  oop="$(grep -E -A6 '^OUT OF PROFILE, reported not scored:' "$CUR_LOG" | grep -oE '[0-9]+ (optional-behaviour|XML 1\.1|not UTF-8|for editions 1-4 only|Namespaces-in-XML cases|referenced files not on disk)')"
  if [ -z "$oop" ]; then emit_status unparsed "$CUR_AREA" "" "no OUT OF PROFILE counts in the log" "$line"; return; fi
  while IFS= read -r n; do sum=$((sum + ${n%% *})); done <<EOF
$oop
EOF
  set -- $nums
  total=$(($1 + $2 + sum))
  emit_ok "$CUR_AREA" "" "$1" "$2" "$sum" "$total" \
    "total derived: scored $(($1 + $2)) (the runner's 'out of $4 in profile') + $sum out-of-profile cases the runner reports but does not score" "$line"
}

parse_xmlconf_probe() {
  local line a r t
  # The probe writes its summary to stderr while stdout is buffered, so the
  # summary can start in the middle of a verdict line.
  line="$(pick_line 'summary: [0-9]+ accepted as well-formed' last | sed -E 's/^.*(summary: )/\1/')"
  if [ -z "$line" ]; then emit_status unparsed "$CUR_AREA" "$CUR_LABEL" "no 'summary:' line in the log"; return; fi
  a="$(printf '%s\n' "$line" | sed -nE 's/^summary: ([0-9]+) accepted as well-formed, ([0-9]+) rejected as malformed \(out of ([0-9]+) files\).*$/\1/p')"
  r="$(printf '%s\n' "$line" | sed -nE 's/^summary: ([0-9]+) accepted as well-formed, ([0-9]+) rejected as malformed \(out of ([0-9]+) files\).*$/\2/p')"
  t="$(printf '%s\n' "$line" | sed -nE 's/^summary: ([0-9]+) accepted as well-formed, ([0-9]+) rejected as malformed \(out of ([0-9]+) files\).*$/\3/p')"
  if [ -z "$a" ] || [ -z "$r" ] || [ -z "$t" ]; then emit_status unparsed "$CUR_AREA" "$CUR_LABEL" "summary line does not have the expected shape" "$line"; return; fi
  if [ "$t" -eq 0 ]; then emit_status error "$CUR_AREA" "$CUR_LABEL" "read 0 files; nothing was measured" "$line"; return; fi
  # A census has no expected verdicts, so there is no pass or fail count.
  add_row census "$CUR_AREA" "$CUR_LABEL" "" "" "$t" "$t" true \
    "* NOT a conformance score: $a files accepted as well-formed, $r rejected (no expected verdict is read; l4xmlconf is the scored row)" "$line" ""
}

parse_xpath() {
  row_sl "$CUR_AREA" "" '^xpath 1\.0 unit battery: [0-9]+ pass' last \
    "* repository unit battery, not a W3C suite"
}

parse_xslt() {
  local line nums ref nu er tot
  line="$(pick_line '^xslt EXACT-or-WHITESPACE: [0-9]+ pass' last)"
  if [ -z "$line" ]; then emit_status unparsed "$CUR_AREA" "" "no 'xslt EXACT-or-WHITESPACE:' line in the log"; return; fi
  if ! nums="$(scoreline_nums "$line")"; then emit_status unparsed "$CUR_AREA" "" "summary line does not follow the score-line grammar" "$line"; return; fi
  ref="$(line_int '^REFUSED: [0-9]+ cases')" || ref=""
  nu="$(line_int '^NOT UTF-8 or missing: [0-9]+ cases')" || nu=0
  er="$(line_int '^ERRORS: [0-9]+ cases')" || er=0
  tot="$(grep -E '^[[:space:]]+\(out of [0-9]+ cases in the manifest\)' "$CUR_LOG" | sed -nE 's/^[[:space:]]+\(out of ([0-9]+) cases in the manifest\).*$/\1/p' | sed -n '$p')"
  if [ -z "$ref" ] || [ -z "$tot" ]; then emit_status unparsed "$CUR_AREA" "" "REFUSED count or manifest total is missing" "$line"; return; fi
  set -- $nums
  emit_ok "$CUR_AREA" "" "$1" "$2" $((ref + nu + er)) "$tot" \
    "pass includes whitespace-only differences; other = refused ($ref) + not UTF-8 ($nu) + unreadable ($er)" "$line"
}

parse_schematron() {
  local line nums u er tot
  line="$(pick_line '^schematron DECIDED: [0-9]+ pass' last)"
  if [ -z "$line" ]; then emit_status unparsed "$CUR_AREA" "" "no 'schematron DECIDED:' line in the log"; return; fi
  if ! nums="$(scoreline_nums "$line")"; then emit_status unparsed "$CUR_AREA" "" "summary line does not follow the score-line grammar" "$line"; return; fi
  u="$(line_int '^UNDECIDED: [0-9]+ cases')" || u=""
  er="$(line_int '^ERRORS: [0-9]+ cases')" || er=0
  tot="$(grep -E '^[[:space:]]+\(out of [0-9]+ cases in the manifest\)' "$CUR_LOG" | sed -nE 's/^[[:space:]]+\(out of ([0-9]+) cases in the manifest\).*$/\1/p' | sed -n '$p')"
  if [ -z "$u" ] || [ -z "$tot" ]; then emit_status unparsed "$CUR_AREA" "" "UNDECIDED count or manifest total is missing" "$line"; return; fi
  set -- $nums
  emit_ok "$CUR_AREA" "" "$1" "$2" $((u + er)) "$tot" "other = undecided ($u, expression outside the XPath subset) + unreadable ($er)" "$line"
}

parse_mathml() {
  row_sl "$CUR_AREA" "" '^content-mathml evaluation: [0-9]+ pass' last "other = markup the reader did not parse"
}

parse_jsonschema() {
  local line nums u tot
  line="$(pick_line '^json-schema draft-07 DECIDED: [0-9]+ pass' last)"
  if [ -z "$line" ]; then emit_status unparsed "$CUR_AREA" "" "no 'json-schema draft-07 DECIDED:' line in the log"; return; fi
  if ! nums="$(scoreline_nums "$line")"; then emit_status unparsed "$CUR_AREA" "" "summary line does not follow the score-line grammar" "$line"; return; fi
  u="$(line_int '^UNDETERMINED: [0-9]+ tests')" || u=""
  tot="$(grep -E '^[[:space:]]+\(out of [0-9]+ run;' "$CUR_LOG" | sed -nE 's/^[[:space:]]+\(out of ([0-9]+) run;.*$/\1/p' | sed -n '$p')"
  if [ -z "$u" ] || [ -z "$tot" ]; then emit_status unparsed "$CUR_AREA" "" "UNDETERMINED count or '(out of N run' is missing" "$line"; return; fi
  set -- $nums
  emit_ok "$CUR_AREA" "" "$1" "$2" "$u" "$tot" "other = undetermined (keyword outside the ported slice)" "$line"
}

parse_xsd() {
  local line nums notscored
  line="$(pick_line '^XSD datatype instance tests: [0-9]+ pass' last)"
  if [ -z "$line" ]; then emit_status unparsed "$CUR_AREA" "" "no 'XSD datatype instance tests:' line in the log"; return; fi
  if ! nums="$(scoreline_nums "$line")"; then emit_status unparsed "$CUR_AREA" "" "summary line does not follow the score-line grammar" "$line"; return; fi
  notscored="$(pick_line '^not scored: ' last)"
  set -- $nums
  emit_ok "$CUR_AREA" "" "$1" "$2" "$3" "$4" "* total = scored instance tests only; $notscored" "$line"
}

parse_jsonld_probe() {
  row_sl "$CUR_AREA" "" '^toRdf: [0-9]+ pass' first
}

parse_jsonld_api() {
  local k
  for k in expand compact flatten fromRdf html; do
    row_sl "JSON-LD $k" "" "^$k: [0-9]+ pass" last "other = local-override + unsupported"
  done
}

parse_jsonld_frame() {
  row_sl "$CUR_AREA" "" '^jsonld-frame: [0-9]+ pass' last "other = unsupported"
}

parse_rml() {
  local line nums nr neg
  line="$(pick_line '^[^ ]*rml-core/test-cases: [0-9]+ pass' last)"
  if [ -z "$line" ]; then emit_status unparsed "$CUR_AREA" "" "no 'rml-core/test-cases:' line in the log"; return; fi
  if ! nums="$(scoreline_nums "$line")"; then emit_status unparsed "$CUR_AREA" "" "summary line does not follow the score-line grammar" "$line"; return; fi
  nr="$(line_int '^NOT READ: [0-9]+ cases')" || nr=""
  neg="$(line_int '^NEGATIVE \(the mapping must be rejected\): [0-9]+ cases')" || neg=""
  if [ -z "$nr" ] || [ -z "$neg" ]; then emit_status unparsed "$CUR_AREA" "" "NOT READ or NEGATIVE count is missing" "$line"; return; fi
  set -- $nums
  emit_ok "$CUR_AREA" "" "$1" "$2" $(($3 + nr + neg)) $(($1 + $2 + $3 + nr + neg)) \
    "total derived; other = comparison gave up ($3) + not read ($nr) + negative cases the runner does not attempt ($neg)" "$line"
}

# One row per "label: N pass, M fail ... (out of T)" line at the start of a
# line (the closing block of the probe); skips the TOTAL line.
parse_block_rows() {
  block_rows "$CUR_AREA" '^[a-z0-9][A-Za-z0-9:_ -]*: [0-9]+ pass, [0-9]+ fail.*\(out of [0-9]+\)$'
}

parse_geo()  { row_sl "$CUR_AREA" "" '^geosparql-v0: [0-9]+ pass' last "* unit pin twin of the F* test, not the OGC GeoSPARQL suite"; }
parse_hdt()  { row_sl "$CUR_AREA" "" '^HDT container: [0-9]+ pass' last "one unit per vendored .hdt file; the log lists each file's stage 2 and stage 3 sub-check counts"; }
parse_toan() { row_sl "$CUR_AREA" "" '^TOAN \(Lean\): [0-9]+ pass' last "* parity battery, not a W3C suite"; }

parse_grddl() {
  local line nums nt un rf tot
  line="$(pick_line '^grddl DECIDED: [0-9]+ pass' last)"
  if [ -z "$line" ]; then emit_status unparsed "$CUR_AREA" "" "no 'grddl DECIDED:' line in the log"; return; fi
  if ! nums="$(scoreline_nums "$line")"; then emit_status unparsed "$CUR_AREA" "" "summary line does not follow the score-line grammar" "$line"; return; fi
  nt="$(line_int '^NO TRANSFORMATION FOUND: [0-9]+ cases')" || nt=""
  un="$(line_int '^UNAVAILABLE: [0-9]+ cases')" || un=0
  rf="$(line_int '^REFUSED: [0-9]+ cases')" || rf=0
  tot="$(grep -E '^[[:space:]]+\(out of [0-9]+ tests in the manifest\)' "$CUR_LOG" | sed -nE 's/^[[:space:]]+\(out of ([0-9]+) tests in the manifest\).*$/\1/p' | sed -n '$p')"
  if [ -z "$nt" ] || [ -z "$tot" ]; then emit_status unparsed "$CUR_AREA" "" "NO TRANSFORMATION count or manifest total is missing" "$line"; return; fi
  set -- $nums
  emit_ok "$CUR_AREA" "" "$1" "$2" $((nt + un + rf)) "$tot" \
    "other = no transformation found ($nt) + document not in the vendored docroot ($un) + refused ($rf)" "$line"
}

# LWS and Solid: two kinds of line. The executed checks, and the registry of
# specification requirement rows.
parse_registry() {
  local area="$CUR_AREA" line nums
  row_sl "$area" "guarded checks (executed)" '^guarded checks: [0-9]+ pass' last
  line="$(pick_line '^registry: [0-9]+ proved' last)"
  if [ -z "$line" ]; then emit_status unparsed "$area" "requirement rows" "no 'registry:' line in the log"; return; fi
  local pr gu ho op tot re
  re='^registry: ([0-9]+) proved, ([0-9]+) guarded, ([0-9]+) host-verified, ([0-9]+) open \(out of ([0-9]+)\)'
  if ! [[ "$line" =~ $re ]]; then emit_status unparsed "$area" "requirement rows" "registry line does not have the expected shape" "$line"; return; fi
  pr="${BASH_REMATCH[1]}"; gu="${BASH_REMATCH[2]}"; ho="${BASH_REMATCH[3]}"; op="${BASH_REMATCH[4]}"; tot="${BASH_REMATCH[5]}"
  emit_ok "$area" "requirement rows" $((pr + gu + ho)) 0 "$op" "$tot" \
    "pass = rows backed by a proof ($pr), a guarded check ($gu) or a host test ($ho); other = $op open rows with no check" "$line"
}

parse_prop() {
  local p=0 f=0 t=0 n=0 line nums raw
  while IFS= read -r line; do
    if nums="$(scoreline_nums "$line")"; then
      set -- $nums
      p=$((p + $1)); f=$((f + $2)); t=$((t + $4)); n=$((n + 1))
    fi
  done < <(grep -E '^PROP [a-z_0-9]+: [0-9]+ pass, [0-9]+ fail.*\(out of [0-9]+\)$' "$CUR_LOG")
  raw="$(pick_line '^PROP TOTAL: ' last)"
  if [ "$n" -eq 0 ]; then emit_status unparsed "$CUR_AREA" "" "no 'PROP name: N pass' lines in the log"; return; fi
  emit_ok "$CUR_AREA" "" "$p" "$f" 0 "$t" "* sum over $n properties, 500 generated cases each; generated, not a W3C suite" "$raw"
}

parse_rdfs_semi() {
  local line re a d t
  line="$(pick_line '^delta vs naive closure: ' last)"
  re='^delta vs naive closure: ([0-9]+) agree, ([0-9]+) differ \(out of ([0-9]+)\)'
  if [ -z "$line" ] || ! [[ "$line" =~ $re ]]; then emit_status unparsed "$CUR_AREA" "" "no 'delta vs naive closure:' line of the expected shape" "$line"; return; fi
  a="${BASH_REMATCH[1]}"; d="${BASH_REMATCH[2]}"; t="${BASH_REMATCH[3]}"
  emit_ok "$CUR_AREA" "" "$a" "$d" 0 "$t" "* pass = semi-naive closure equals the naive closure; an equivalence check, not a W3C suite" "$line"
}

parse_diff() {
  local line re a d ti fe le sk t
  line="$(pick_line '^DIFF TOTAL: ' last)"
  re='^DIFF TOTAL: ([0-9]+) agree, ([0-9]+) disagree, ([0-9]+) tie-order, ([0-9]+) fstar-error, ([0-9]+) lean-error, ([0-9]+) skipped \(out of ([0-9]+)\)'
  if [ -z "$line" ] || ! [[ "$line" =~ $re ]]; then emit_status unparsed "$CUR_AREA" "" "no 'DIFF TOTAL:' line of the expected shape" "$line"; return; fi
  a="${BASH_REMATCH[1]}"; d="${BASH_REMATCH[2]}"; ti="${BASH_REMATCH[3]}"; fe="${BASH_REMATCH[4]}"; le="${BASH_REMATCH[5]}"; sk="${BASH_REMATCH[6]}"; t="${BASH_REMATCH[7]}"
  emit_ok "$CUR_AREA" "" "$a" "$d" $((ti + fe + le + sk)) "$t" \
    "* pass = agree with the F* engine; other = tie-order $ti + fstar-error $fe + lean-error $le + skipped $sk" "$line"
}

# --------------------------------------------------------------------------
# Failing test ids of a saved log, by FAILKEY, one per line. This reads saved
# logs only; the caller shows the first 10. A runner's own output is never
# truncated.
# --------------------------------------------------------------------------
fail_ids_all() {
  local key="$1" log="$2"
  case "$key" in
    w3c|grddl|rif|mathml|xpath|geo)
      grep -E '^FAIL ' "$log" | sed -E 's/^FAIL ([^:]+):.*$/\1/' ;;
    shacl)
      grep -E '^FAIL ' "$log" | sed -E 's/^FAIL (.*) \([^()]*\): .*$/\1/' ;;
    owl)
      grep -E '^FAIL ' "$log" | sed -E 's/^FAIL (.*\]): .*$/\1/' ;;
    csvw)
      grep -E '^(FAIL|NEG-FAIL|OVER-STRICT) ' "$log" | sed -E 's/^(FAIL|NEG-FAIL|OVER-STRICT) ([^ ]+).*$/\1 \2/' ;;
    xslt|schematron)
      grep -E '^FAIL ' "$log" | sed -E 's/^FAIL //' ;;
    turtle_probe)
      grep -E '^  FAIL ' "$log" | sed -E 's/^  FAIL ([^:]+):.*$/\1/' ;;
    jsonld_frame)
      grep -E '^    #[A-Za-z0-9]+ ' "$log" | sed -E 's/^    (#[A-Za-z0-9]+) .*$/\1/' ;;
    jsonld)
      grep -E '^  #[A-Za-z0-9]+ \[' "$log" | sed -E 's/^  (#[A-Za-z0-9]+) .*$/\1/' ;;
    shex)
      grep -E '^FAIL ' "$log" | sed -E 's/^FAIL (.*) \(.*$/\1/' ;;
    shexc)
      grep -E '^MISMATCH ' "$log" | sed -E 's/^MISMATCH ([^:]+):.*$/\1/' ;;
    xsd)
      grep -E '^  FAIL ' "$log" | sed -E 's/^  FAIL ([^ ]+) .*$/\1/' ;;
    xmlconf)
      grep -E '^FAIL ' "$log" | sed -E 's/^FAIL ([^ ]+) .*$/\1/' ;;
    jsonschema)
      grep -E 'decided-and-wrong in ' "$log" ;;
    bracket)
      grep -E '^[[:space:]]*\[FAIL\]' "$log" | sed -E 's/^[[:space:]]*\[FAIL\][[:space:]]*//' ;;
    prop)
      grep -E '^FAIL ' "$log" ;;
    hdt)
      grep -E '^FAIL ' "$log" | sed -E 's/^FAIL ([^:]+):.*$/\1/' ;;
    lws)
      grep -E '^FAIL ' "$log" | sed -E 's/^FAIL ([^ ]+).*$/\1/' ;;
    toan)
      grep -E '^[[:space:]]+FAIL ' "$log" | sed -E 's/^[[:space:]]+FAIL[[:space:]]+//' ;;
    diff)
      grep -E '^(DISAGREE|FSTAR-ERROR|LEAN-ERROR) ' "$log" | sed -E 's/^([A-Z-]+) ([^:]+):.*$/\1 \2/' ;;
    *)
      grep -E '^[[:space:]]*(FAIL|MISMATCH)[: ]' "$log" ;;
  esac
}

# --------------------------------------------------------------------------
# Running a job.
# --------------------------------------------------------------------------
meta_get() { sed -n "s/^$2=//p" "$1" | sed -n '1p'; }

# Patterns that mean a runner measured nothing.
NOTHING_RE='manifest not found|manifest did NOT parse|manifest did not parse|manifest parsed but named no entries|corpus (directory )?not found|directory not present|directory not found|cases file not found|suite root not found|run tools/ensure-test-env\.sh|catalog not read|no numbers reported|cannot read .*suite\.xml|F\* binary not found|no \.hdt files found|^[[:space:]]*MISSING '
PANIC_RE='INTERNAL PANIC|^PANIC at|[Ss]tack overflow'

run_job() {
  local i="$1" cmd full t0 t1 rc timed_out=0 id log meta
  id="${JOB_ID[$i]}"; log="$LOGDIR/$id.log"; meta="$LOGDIR/$id.meta"
  cmd="$BIN/${JOB_RUNNER[$i]}"
  [ -n "${JOB_ARGS[$i]}" ] && cmd="$cmd ${JOB_ARGS[$i]}"
  full="$cmd"
  [ -n "${JOB_STDIN[$i]}" ] && full="${JOB_STDIN[$i]} | $cmd"

  if [ "$RESUME" -eq 1 ] && [ -f "$meta" ] && [ -s "$log" ]; then
    echo "[$SEL_POS/$SEL_N] $id: reusing finished log ($(meta_get "$meta" secs) s, rc $(meta_get "$meta" rc))" >&2
    return 0
  fi
  if [ ! -x "$BIN/${JOB_RUNNER[$i]}" ]; then
    rm -f "$meta"
    printf 'lean-scoreboard: runner binary not built: %s\n' "$BIN/${JOB_RUNNER[$i]}" > "$log"
    printf 'rc=127\nsecs=0\ntimeout_s=%s\ntimed_out=0\ncmd=%s\n' "$RUNNER_TIMEOUT" "$full" > "$meta"
    echo "[$SEL_POS/$SEL_N] $id: runner binary missing" >&2
    return 0
  fi

  rm -f "$meta"
  echo "[$SEL_POS/$SEL_N] $id: running (cap ${RUNNER_TIMEOUT} s) ..." >&2
  t0=$(date +%s)
  if [ -n "${JOB_STDIN[$i]}" ]; then
    ( eval "${JOB_STDIN[$i]}" ) | eval "$TIMEOUT_BIN -k 10 $RUNNER_TIMEOUT $cmd" 2>&1 | if [ "$VERBOSE" -eq 1 ]; then tee "$log" >&2; else tee "$log" > /dev/null; fi
    rc="${PIPESTATUS[1]}"
  else
    eval "$TIMEOUT_BIN -k 10 $RUNNER_TIMEOUT $cmd" < /dev/null 2>&1 | if [ "$VERBOSE" -eq 1 ]; then tee "$log" >&2; else tee "$log" > /dev/null; fi
    rc="${PIPESTATUS[0]}"
  fi
  t1=$(date +%s)
  if [ "$rc" -eq 124 ] || { [ "$rc" -eq 137 ] && [ $((t1 - t0)) -ge "$RUNNER_TIMEOUT" ]; }; then timed_out=1; fi
  printf 'rc=%s\nsecs=%s\ntimeout_s=%s\ntimed_out=%s\ncmd=%s\n' "$rc" $((t1 - t0)) "$RUNNER_TIMEOUT" "$timed_out" "$full" > "$meta.tmp" && mv "$meta.tmp" "$meta"
  echo "[$SEL_POS/$SEL_N] $id: done rc=$rc in $((t1 - t0)) s" >&2
}

# process_job INDEX -- read the saved log and meta, append rows.
process_job() {
  local i="$1" meta log rc secs timed_out reason line first_row
  CUR_IDX="$i"; CUR_ID="${JOB_ID[$i]}"; CUR_RUNNER="${JOB_RUNNER[$i]}"
  CUR_AREA="${JOB_AREA[$i]}"; CUR_LABEL="${JOB_LABEL[$i]}"
  log="$LOGDIR/$CUR_ID.log"; meta="$LOGDIR/$CUR_ID.meta"
  CUR_LOG="$log"
  JOB_ROWS=0; JOB_FAILS=0
  rc="$(meta_get "$meta" rc)"; secs="$(meta_get "$meta" secs)"; timed_out="$(meta_get "$meta" timed_out)"
  CUR_CMD="$(meta_get "$meta" cmd)"; CUR_RC="${rc:-?}"; CUR_SECS="${secs:-0}"

  if [ "$timed_out" = 1 ]; then
    emit_status timeout "$CUR_AREA" "$CUR_LABEL" "TIMEOUT after $(meta_get "$meta" timeout_s) s"
  elif [ "$rc" = 127 ]; then
    emit_status error "$CUR_AREA" "$CUR_LABEL" "runner binary not built: $BIN/$CUR_RUNNER"
  elif [ ! -s "$log" ]; then
    emit_status error "$CUR_AREA" "$CUR_LABEL" "the runner printed nothing (exit code $rc)"
  elif line="$(grep -E -m1 -- "$NOTHING_RE" "$log")" && [ -n "$line" ]; then
    emit_status error "$CUR_AREA" "$CUR_LABEL" "measured nothing: $(printf '%s' "$line" | cut -c1-200)" "$line"
  elif line="$(grep -E -m1 'HARNESS-DIAG[A-Za-z-]* .*(no_manifest|zero_tests)=[1-9]' "$log")" && [ -n "$line" ]; then
    emit_status error "$CUR_AREA" "$CUR_LABEL" "the runner's own HARNESS-DIAG line reports a manifest that was not read or had 0 tests" "$line"
  elif line="$(grep -E -m1 -- "$PANIC_RE" "$log")" && [ -n "$line" ]; then
    emit_status error "$CUR_AREA" "$CUR_LABEL" "the log contains a Lean panic: $(printf '%s' "$line" | cut -c1-200)" "$line"
  elif [ "$rc" != 0 ] && [ "$rc" != 1 ]; then
    emit_status error "$CUR_AREA" "$CUR_LABEL" "exit code $rc (0 and 1 are the runners' pass/fail codes)" "$(grep -E '.' "$log" | sed -n '$p')"
  else
    first_row="$ROW_N"
    "${JOB_PARSER[$i]}"
    if [ "$JOB_ROWS" -gt 0 ] && [ "$rc" = 1 ] && [ "$JOB_FAILS" -eq 0 ]; then
      append_note "$first_row" "! exit code 1, but no row of this run shows a failure; the log has failures in a suite this run does not report (see the log)"
    fi
    if [ "$JOB_ROWS" -eq 0 ]; then
      line="$(grep -E '(pass|fail|out of)' "$log" | sed -n '$p')"
      [ -n "$line" ] || line="$(grep -E '.' "$log" | sed -n '$p')"
      emit_status unparsed "$CUR_AREA" "$CUR_LABEL" "the parser produced no row" "$(printf '%s' "$line" | cut -c1-300)"
    fi
  fi
  JOB_FAILN[$i]="$JOB_FAILS"
}

# --------------------------------------------------------------------------
# Output.
# --------------------------------------------------------------------------
jstr() {
  local s
  s="$(printf '%s' "$1" | tr -d '\000-\037\177' | sed -e 's/\\/\\\\/g' -e 's/"/\\"/g')"
  if command -v iconv >/dev/null 2>&1; then s="$(printf '%s' "$s" | iconv -f UTF-8 -t UTF-8 -c 2>/dev/null)"; fi
  printf '"%s"' "$s"
}
jnum() { if [ -n "$1" ]; then printf '%s' "$1"; else printf 'null'; fi; }

write_json() {
  local out="$1" i first=1 row
  local area runner label status p f o t parse note cmd log secs rc raw detail id
  mkdir -p "$(dirname "$out")"
  {
    printf '{\n'
    printf '  "generated_utc": %s,\n' "$(jstr "$(date -u +%Y-%m-%dT%H:%M:%SZ)")"
    printf '  "git_head": %s,\n' "$(jstr "$(git rev-parse --short HEAD 2>/dev/null)")"
    printf '  "host": %s,\n' "$(jstr "$(uname -sm)")"
    printf '  "runner_timeout_s": %s,\n' "$RUNNER_TIMEOUT"
    printf '  "only": %s,\n' "$(jstr "$ONLY")"
    printf '  "rows": [\n'
    i=0
    while [ "$i" -lt "$ROW_N" ]; do
      row="${ROWS[$i]}"
      IFS="$US" read -r area runner label status p f o t parse note cmd log secs rc raw detail id <<EOF
$row
EOF
      [ "$first" -eq 1 ] || printf ',\n'
      first=0
      printf '    {"spec_area": %s, "label": %s, "runner": %s, "job": %s, "status": %s, "pass": %s, "fail": %s, "other": %s, "total": %s, "parse": ' \
        "$(jstr "$area")" "$(jstr "$label")" "$(jstr "$runner")" "$(jstr "$id")" "$(jstr "$status")" "$(jnum "$p")" "$(jnum "$f")" "$(jnum "$o")" "$(jnum "$t")"
      case "$parse" in true) printf 'true' ;; false) printf 'false' ;; *) printf 'null' ;; esac
      printf ', "note": %s, "command": %s, "log": %s, "seconds": %s, "exit_code": %s, "raw_summary_line": %s, "detail": %s}' \
        "$(jstr "$note")" "$(jstr "$cmd")" "$(jstr "$log")" "$(jnum "$secs")" "$(jstr "$rc")" "$(jstr "$raw")" "$(jstr "$detail")"
      i=$((i + 1))
    done
    printf '\n  ]\n}\n'
  } > "$out.tmp" && mv "$out.tmp" "$out"
}

print_table() {
  local i row k=0 notes="" cellarea show
  local area runner label status p f o t parse note cmd log secs rc raw detail id
  local data=""
  i=0
  while [ "$i" -lt "$ROW_N" ]; do
    row="${ROWS[$i]}"
    IFS="$US" read -r area runner label status p f o t parse note cmd log secs rc raw detail id <<EOF
$row
EOF
    cellarea="$area"
    [ -n "$label" ] && cellarea="$area: $label"
    # A note is printed under the table when the row has no number, when it
    # starts with "* " or "! ", or when the row has an "other" count it
    # explains. Every note is in the JSON.
    show=0
    case "$status" in ok) ;; *) [ -n "$note" ] && show=1 ;; esac
    case "$note" in "* "*|"! "*) show=1 ;; esac
    if [ "$status" = ok ] && [ -n "$note" ] && [ "${o:-0}" -gt 0 ] 2>/dev/null; then show=1; fi
    if [ "$show" -eq 1 ]; then
      k=$((k + 1))
      cellarea="$cellarea [n$k]"
      note="${note#"* "}"
      notes="${notes}[n$k] ${area}${label:+: $label}: ${note}
"
    fi
    case "$status" in
      ok)      : ;;
      census)  p="-"; f="-" ;;
      error)   p="ERROR"; f="-"; o="-"; t="-" ;;
      timeout) p="TIMEOUT"; f="-"; o="-"; t="-" ;;
      unparsed) p="UNPARSED"; f="-"; o="-"; t="-" ;;
      none)    p="none"; f="-"; o="-"; t="-" ;;
    esac
    data="${data}${cellarea}${US}${runner}${US}${p}${US}${f}${US}${o}${US}${t}${US}${cmd}
"
    i=$((i + 1))
  done
  printf '%s' "$data" | awk -F"$US" '
    BEGIN { split("spec area|runner|pass|fail|skip/other|total|command", H, "|"); n = 7 }
    { for (c = 1; c <= n; c++) { cell[NR, c] = $c; if (length($c) > w[c]) w[c] = length($c) } rows = NR }
    END {
      for (c = 1; c <= n; c++) if (length(H[c]) > w[c]) w[c] = length(H[c])
      line = ""
      for (c = 1; c <= n; c++) { line = line sprintf((c >= 3 && c <= 6) ? "%" w[c] "s" : "%-" w[c] "s", H[c]); if (c < n) line = line " | " }
      sub(/ +$/, "", line)
      print line
      line = ""
      for (c = 1; c <= n; c++) { s = ""; m = (c < n) ? w[c] : length(H[c]); for (j = 0; j < m; j++) s = s "-"; line = line s; if (c < n) line = line "-+-" }
      print line
      for (r = 1; r <= rows; r++) {
        line = ""
        for (c = 1; c <= n; c++) { line = line sprintf((c >= 3 && c <= 6) ? "%" w[c] "s" : "%-" w[c] "s", cell[r, c]); if (c < n) line = line " | " }
        sub(/ +$/, "", line)
        print line
      }
    }'
  if [ -n "$notes" ]; then
    echo
    echo "Notes:"
    printf '%s' "$notes"
  fi
}

# --------------------------------------------------------------------------
# Main.
# --------------------------------------------------------------------------
if [ "$LIST_ONLY" -eq 1 ]; then
  i=0
  while [ "$i" -lt "$JOB_N" ]; do
    cmd="$BIN/${JOB_RUNNER[$i]}${JOB_ARGS[$i]:+ ${JOB_ARGS[$i]}}"
    [ -n "${JOB_STDIN[$i]}" ] && cmd="${JOB_STDIN[$i]} | $cmd"
    printf '%-40s %s\n' "${JOB_ID[$i]}" "$cmd"
    i=$((i + 1))
  done
  exit 0
fi

if [ ! -d "third_party/testing/w3c/sparql" ] || [ ! -d "third_party/testing/owl" ]; then
  echo "lean-scoreboard: test fixtures are missing under third_party/testing; run tools/ensure-test-env.sh first." >&2
  echo "lean-scoreboard: with the fixtures absent every runner discovers 0 tests and the table would be empty of facts." >&2
  exit 3
fi

mkdir -p "$LOGDIR" || exit 2

# Select jobs.
SELECTED=()
if [ -n "$ONLY" ]; then
  oldifs="$IFS"; IFS=','
  for tok in $ONLY; do
    found=0
    i=0
    while [ "$i" -lt "$JOB_N" ]; do
      if [ "${JOB_RUNNER[$i]}" = "$tok" ] || [ "${JOB_ID[$i]}" = "$tok" ]; then
        found=1
        SELECTED[${#SELECTED[@]}]="$i"
      fi
      i=$((i + 1))
    done
    if [ "$found" -eq 0 ]; then
      IFS="$oldifs"
      echo "lean-scoreboard: --only: no runner or job named '$tok'. Names:" >&2
      i=0; while [ "$i" -lt "$JOB_N" ]; do echo "  ${JOB_RUNNER[$i]}  (job ${JOB_ID[$i]})" >&2; i=$((i + 1)); done
      exit 2
    fi
  done
  IFS="$oldifs"
  # Keep table order and drop duplicates.
  SORTED=()
  i=0
  while [ "$i" -lt "$JOB_N" ]; do
    for s in "${SELECTED[@]}"; do
      if [ "$s" = "$i" ]; then SORTED[${#SORTED[@]}]="$i"; break; fi
    done
    i=$((i + 1))
  done
  SELECTED=("${SORTED[@]}")
else
  i=0
  while [ "$i" -lt "$JOB_N" ]; do SELECTED[${#SELECTED[@]}]="$i"; i=$((i + 1)); done
fi

T_START=$(date +%s)
JOB_ROWS=0; JOB_FAILS=0
SEL_N=${#SELECTED[@]}; SEL_POS=0
for i in "${SELECTED[@]}"; do
  SEL_POS=$((SEL_POS + 1))
  run_job "$i"
  process_job "$i"
done

# Areas with no Lean runner (only in a full run).
if [ -z "$ONLY" ]; then
  CUR_RUNNER="none"; CUR_CMD=""; CUR_LOG=""; CUR_SECS=0; CUR_RC=""; CUR_ID="none"
  while IFS='|' read -r narea nreason; do
    [ -n "$narea" ] || continue
    add_row none "$narea" "" "" "" "" "" "n/a" "no Lean runner: $nreason" "" ""
  done <<EOF
$NONE_ROWS
EOF
fi

T_END=$(date +%s)
write_json "$JSON_OUT"

echo
echo "Lean scoreboard, $(date -u +%Y-%m-%dT%H:%M:%SZ), git $(git rev-parse --short HEAD 2>/dev/null), ${#SELECTED[@]} runs, $((T_END - T_START)) s this invocation (runs reused with --resume are not timed again)"
echo
print_table

# Row counts by status, and the failing ids.
n_ok=0; n_err=0; n_fail=0; i=0
while [ "$i" -lt "$ROW_N" ]; do
  IFS="$US" read -r area runner label status p f o t parse note cmd log secs rc raw detail id <<EOF
${ROWS[$i]}
EOF
  case "$status" in
    ok)      n_ok=$((n_ok + 1)); [ "${f:-0}" -gt 0 ] && n_fail=$((n_fail + 1)) ;;
    census|none) : ;;
    *)       n_err=$((n_err + 1)) ;;
  esac
  i=$((i + 1))
done
echo
echo "Rows with numbers: $n_ok (of which $n_fail have failures). Rows that are ERROR, TIMEOUT or UNPARSED: $n_err. JSON: $JSON_OUT. Logs: $LOGDIR/"

printed_header=0
for i in "${SELECTED[@]}"; do
  if [ "${JOB_FAILN[$i]:-0}" -gt 0 ]; then
    if [ "$printed_header" -eq 0 ]; then
      echo
      echo "First 10 failing test ids, from the saved logs:"
      printed_header=1
    fi
    ids_all="$(fail_ids_all "${JOB_FAILKEY[$i]}" "$LOGDIR/${JOB_ID[$i]}.log")"
    n_ids="$(printf '%s\n' "$ids_all" | grep -c .)"
    if [ "$n_ids" -eq 0 ]; then
      echo "  ${JOB_ID[$i]}: a row fails, and the log lists no failing id (run the command with the runner's verbose flag)"
    else
      echo "  ${JOB_ID[$i]}: $n_ids failing ids listed in the log"
      printf '%s\n' "$ids_all" | awk 'NR <= 10' | sed 's/^/    /'
    fi
  fi
done

if [ "$n_err" -gt 0 ]; then exit 3; fi
if [ "$n_fail" -gt 0 ]; then exit 1; fi
exit 0
