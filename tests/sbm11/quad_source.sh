#!/usr/bin/env bash
#
# tests/sbm11/quad_source.sh -- the SBM11 packer takes RDF quads from any
# producer, not from a file path (https://github.com/danbri/factoidal/issues/866).
# Owner, 2026-10-15, verbatim: "isn't packing (into shardborough?) done against
# abstract rdf graph or dataset API not a text file format???"
#
# The entry is `Sbm11Pack.packQuads` (Harness/Sbm11PackLib.lean). It takes one way to
# open a producer (`QuadSource`, L4Factoidal/RDF/QuadSource.lean) for each phase-1
# worker. The file reader is one producer; this script runs the others.
#
#   (1) selftest   `l4sbm11-quad-source selftest`: in process, no document text. The
#                  batches of the Dataset and array producers are the quads of the
#                  dataset in order, within the batch bounds, equal to the pure model
#                  of the theorems; a step that throws makes every later call throw;
#                  the generation of a dataset is byte-identical for 1, 2 and 5
#                  producers, batches of 1, 3 and 4,096 quads, term maps of 7, 40 and
#                  262,144 terms, the quads in order and in reverse, and the default graph
#                  and the named graphs as two datasets.
#   (2) dataset    A Dataset value in memory, packed (`pack-dataset`), dumped
#                  (`l4sbm11 dump`) and compared with the dataset by RDF dataset
#                  isomorphism (`l4sbm11-w3c compare`) and by the RDFC-1.0 canonical
#                  N-Quads of both (`l4factoidal canonicalize`). Seven datasets: empty,
#                  default graph, named graphs, a mixed one (blank nodes as subject,
#                  object and graph name, a repeated triple, a triple in two graphs, a
#                  named graph with no triple), one that stresses the dictionary
#                  (Unicode, escapes, a 100,000-character literal, integers and other
#                  datatypes), one with RDF 1.2 terms (a directional literal, nested
#                  triple terms), and 52,800 generated quads. RDFC-1.0 is defined on
#                  RDF 1.1 datasets, so the RDF 1.2 dataset is compared by isomorphism
#                  only. The generation passes the activation checks
#                  (`l4sbm11 verify`). The named graphs of the generation
#                  (`l4sbm11 graphs`, the graph list GNL1) are the named graphs of
#                  the dataset, the graph with no triple and the graph named by a
#                  blank node included (`names CASE`; issues 855 and 856): the same
#                  IRIs and the same number of blank nodes.
#   (3) file       The command line: the file route and the Dataset route
#                  (`--via-dataset`: the whole document is read into a Dataset, then
#                  packed from the Dataset producer) give byte-identical generations,
#                  the manifest included, for every syntax fixture of
#                  tests/sbm11/syntax, the gate fixtures and a 1 MB generated dataset.
#                  D5 (d5.trig, d5.jsonld): six named graphs, three of them with no
#                  triple, three named by a blank node; the TriG reader declares each
#                  graph block and the JSON-LD reader each named graph, and
#                  `l4sbm11 graphs` of the pack lists all six.
#   (4) hdt        The triples of an HDT file packed with no text in between
#                  (`l4sbm11-pack FILE.hdt`): the vendored hdt-cpp 1.3.3 fixtures
#                  (third_party/testing/hdt). The dump of the generation equals the
#                  HDT store's own dump (`hdt-dump`: `HDT.searchTriples`), and the
#                  N-Triples file the fixture was made from (RDF dataset
#                  isomorphism, RDFC-1.0 canonical N-Quads). The manifest records the
#                  length and the SHA-256 of the HDT file (the digest of
#                  third_party/testing/hdt/README.md). The output does not depend on
#                  --workers. A damaged file is refused. An id outside the dictionary and a
#                  subject after the last are errors, never a term in a quad
#                  (`hdt-errors`).
#   (5) layering   the producer interface imports no syntax module and names none.
#
# Prints "quad source: N pass, M fail, K expected-fail (out of T)". Exit 0 when no case
# failed; 2 when a binary or a fixture is missing.
#
# Env: L4_BIN_DIR   directory of l4sbm11, l4sbm11-pack, l4sbm11-w3c, l4sbm11-quad-source
#                   and l4factoidal (default formal/lean4/.lake/build/bin)
#      FACTOIDAL_TESTING_ROOT  the directory of the fixtures (default
#                   third_party/testing of this tree)
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_BIN_DIR:-$ROOT/formal/lean4/.lake/build/bin}"
TESTING="${FACTOIDAL_TESTING_ROOT:-$ROOT/third_party/testing}"
FX="$HERE/syntax"
HDT="$TESTING/hdt"
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack" "$BIN/l4sbm11-w3c" "$BIN/l4sbm11-quad-source" \
            "$BIN/l4factoidal" "$FX/d1.nt" "$HDT/rml-core-ontology.hdt" "$HDT/rdf-mt-test002.hdt" \
            "$TESTING/rml-modules/rml-core/ontology/documentation/ontology.nt" \
            "$TESTING/w3c/rdf/rdf11/rdf-mt/datatypes/test002.nt"; do
  if [ ! -e "$need" ]; then echo "missing: $need (lake build; tools/ensure-test-env.sh)" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-quadsource.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
PASS=0; FAIL=0; XFAIL=0
record() { # record <name> <ok:0|1> <detail>
  if [ "$2" = 0 ]; then PASS=$((PASS + 1)); printf 'ok     %-44s %s\n' "$1" "$3"
  else FAIL=$((FAIL + 1)); printf 'FAIL   %-44s %s\n' "$1" "$3"; fi
}
# same_names WANT GOT: the same IRIs (one `<...>` on each line) and the same number of
# blank nodes (`_:` lines; a label is a name for one document); prints a summary
same_names() {
  local wi gi wb gb
  wi="$(grep '^<' "$1" | sort)"; gi="$(grep '^<' "$2" | sort)"
  wb="$(grep -c '^_:' "$1")"; gb="$(grep -c '^_:' "$2")"
  if [ "$wi" = "$gi" ] && [ "$wb" = "$gb" ]; then
    echo "$(grep -c . "$2") named graphs: $(printf '%s' "$gi" | grep -c .) IRIs, $gb blank nodes"; return 0
  fi
  echo "want IRIs [$(printf '%s' "$wi" | tr '\n' ' ')] and $wb blank nodes; the generation lists [$(printf '%s' "$gi" | tr '\n' ' ')] and $gb blank nodes"
  return 1
}

echo "=== (1) producers and the entry, in process"
rc=0
timeout 900 "$BIN/l4sbm11-quad-source" selftest "$TMP/selftest" >"$TMP/selftest.log" 2>&1 || rc=$?
sum="$(grep '^quad source selftest:' "$TMP/selftest.log")"
if [ -n "$sum" ]; then
  sp="$(printf '%s' "$sum" | sed -n 's/.*: \([0-9]*\) pass, \([0-9]*\) fail.*/\1/p')"
  sf="$(printf '%s' "$sum" | sed -n 's/.*: \([0-9]*\) pass, \([0-9]*\) fail.*/\2/p')"
  PASS=$((PASS + sp)); FAIL=$((FAIL + sf))
  grep -v '^quad source selftest:' "$TMP/selftest.log" | sed 's/^/     /'
  echo "     $sum"
  if [ "$rc" -ne 0 ] && [ "$sf" -eq 0 ]; then record selftest-exit 1 "exit $rc with no failed case"; fi
else record selftest 1 "exit $rc: $(tail -1 "$TMP/selftest.log")"; fi

echo "=== (2) a Dataset value in memory: pack, dump, compare with the dataset"
canon() { "$BIN/l4factoidal" canonicalize "$1" --format nquads 2>"$2.err"; }
while IFS=$'\t' read -r name nquads version; do
  [ -z "$name" ] && continue
  d="$TMP/ds-$name"; mkdir -p "$d"
  rc=0
  timeout 600 "$BIN/l4sbm11-quad-source" pack-dataset "$name" "$d/gen" --expected "$d/expected.nq" >"$d/pack.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then record "dataset $name pack" 1 "exit $rc: $(tail -1 "$d/pack.log")"; continue; fi
  rc=0; "$BIN/l4sbm11" verify "$d/gen" >"$d/verify.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then record "dataset $name verify" 1 "exit $rc: $(grep -m1 FAIL "$d/verify.log")"; continue; fi
  # the named graphs, empty ones included: the graph list of the generation
  "$BIN/l4sbm11-quad-source" names "$name" >"$d/names.want" 2>"$d/names.err"
  rc=0; "$BIN/l4sbm11" graphs "$d/gen" >"$d/names.got" 2>"$d/graphs.err" || rc=$?
  if [ "$rc" -ne 0 ]; then record "dataset $name named graphs" 1 "exit $rc: $(tail -1 "$d/graphs.err")"
  else out="$(same_names "$d/names.want" "$d/names.got")"; record "dataset $name named graphs" "$?" "$out"; fi
  rc=0; timeout 600 "$BIN/l4sbm11" dump "$d/gen" >"$d/dump.nq" 2>"$d/dump.err" || rc=$?
  if [ "$rc" -ne 0 ]; then record "dataset $name dump" 1 "exit $rc: $(tail -1 "$d/dump.err")"; continue; fi
  out="$("$BIN/l4sbm11-w3c" compare "$d/expected.nq" "$d/dump.nq" --expected nq --mode rdf12 2>&1)"; rc=$?
  case "$out" in
    pass*) record "dataset $name = dump (isomorphic)" 0 "$nquads quads; $out" ;;
    *) record "dataset $name = dump (isomorphic)" 1 "$(printf '%s' "$out" | head -1 | cut -c1-200)" ;;
  esac
  if [ "$version" = rdf12 ]; then
    echo "     (RDFC-1.0 is defined on RDF 1.1 datasets: $name has a triple term or a directional literal, so only the isomorphism applies)"
  elif canon "$d/expected.nq" "$d/expected" >"$d/expected.c14n" && canon "$d/dump.nq" "$d/dump" >"$d/dump.c14n" \
     && cmp -s "$d/expected.c14n" "$d/dump.c14n"; then
    record "dataset $name = dump (RDFC-1.0)" 0 "$(grep -c . "$d/dump.c14n") canonical quads, equal"
  else record "dataset $name = dump (RDFC-1.0)" 1 "canonical N-Quads differ or the command failed: $(head -1 "$d/expected.err" "$d/dump.err" 2>/dev/null | tr '\n' ' ')"; fi
  # the dump is not vacuous: its quad count is the dataset's, apart from the quads that
  # are the same quad (a repeated triple, a triple in two graphs is two quads)
  nd="$(grep -c . "$d/dump.nq")"
  if [ "$nd" -gt 0 ] || [ "$nquads" = 0 ]; then record "dataset $name has quads in the dump" 0 "$nd lines"
  else record "dataset $name has quads in the dump" 1 "the dump is empty"; fi
done < <("$BIN/l4sbm11-quad-source" cases)

# The entry does not depend on the division of the quads among producers or on the
# size of the batches: the same files from separate processes.
for name in mixed terms big; do
  d="$TMP/ds-$name"
  rc=0; timeout 600 "$BIN/l4sbm11-quad-source" pack-dataset "$name" "$d/gen-split" --producers 3 --batch 5 --run-terms 50 >"$d/split.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then record "dataset $name 3 producers" 1 "exit $rc: $(tail -1 "$d/split.log")"; continue; fi
  if diff -rq "$d/gen" "$d/gen-split" >"$d/split.diff" 2>&1; then record "dataset $name 3 producers = 1 producer" 0 "every file byte-identical ($(ls "$d/gen" | wc -l) files)"
  else record "dataset $name 3 producers = 1 producer" 1 "$(head -1 "$d/split.diff")"; fi
done

echo "=== (3) the command line: the file route and the Dataset route"
same_gen() { # same_gen A B: every file of A and B, the manifest too, byte-identical
  diff -rq "$1" "$2" >"$TMP/same.diff" 2>&1 && echo "$(ls "$1" | wc -l) files byte-identical" || { head -1 "$TMP/same.diff"; return 1; }
}
mkdir -p "$TMP/multi"
python3 -I "$FX/gen_multi.py" "$TMP/multi" 1500 >/dev/null 2>&1
check_via() { # check_via LABEL FILE [ARGS...]
  local label="$1" f="$2"; shift 2
  local a="$TMP/via-a-$label" b="$TMP/via-b-$label" rc1=0 rc2=0
  rm -rf "$a" "$b"
  timeout 600 "$BIN/l4sbm11-pack" "$f" "$a" "$@" >"$a.log" 2>&1 || rc1=$?
  timeout 600 "$BIN/l4sbm11-pack" "$f" "$b" "$@" --via-dataset >"$b.log" 2>&1 || rc2=$?
  if [ "$rc1" -ne 0 ] || [ "$rc2" -ne 0 ]; then
    record "via-dataset $label" 1 "exit file route $rc1, Dataset route $rc2: $(tail -1 "$b.log" | cut -c1-160)"; return
  fi
  if ! grep -q 'producer=dataset' "$b.log"; then record "via-dataset $label" 1 "the log does not name the Dataset producer"; return; fi
  local out; out="$(same_gen "$a" "$b")"; local r=$?
  record "via-dataset $label" "$r" "$out"
  rm -rf "$a" "$b"
}
for f in "$FX"/d1.* "$FX"/d2.* "$FX"/d3.* "$FX"/d4.* "$FX"/d5.* "$FX"/bnode_collide.* "$FX"/lang_scope.* "$FX"/scope_paths.*; do
  check_via "$(basename "$f")" "$f"
done
# D5: the named graphs with no triple and the graphs named by a blank node reach the graph list
printf '<http://example.org/g0>\n<http://example.org/g1>\n<http://example.org/g2>\n_:x1\n_:x2\n_:x3\n' >"$TMP/d5.want"
for f in "$FX"/d5.trig "$FX"/d5.jsonld; do
  g="$TMP/d5-$(basename "$f")"; rm -rf "$g"
  rc=0; timeout 600 "$BIN/l4sbm11-pack" "$f" "$g" >"$g.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then record "named graphs $(basename "$f")" 1 "pack exit $rc: $(tail -1 "$g.log")"; continue; fi
  rc=0; "$BIN/l4sbm11" verify "$g" >"$g.verify" 2>&1 || rc=$?
  "$BIN/l4sbm11" graphs "$g" >"$g.names" 2>"$g.err" || rc=$((rc + 10))
  if [ "$rc" -ne 0 ]; then record "named graphs $(basename "$f")" 1 "verify or graphs exit $rc: $(grep -m1 FAIL "$g.verify") $(tail -1 "$g.err")"; continue; fi
  out="$(same_names "$TMP/d5.want" "$g.names")"; r=$?
  grep -q 'named-graphs=6 ' "$g.log" || { r=1; out="$out; the pack line says $(grep -o 'named-graphs=[0-9]*' "$g.log")"; }
  record "named graphs $(basename "$f")" "$r" "$out (2 IRIs and 2 blank nodes with no triple)"
  rm -rf "$g"
done
check_via gate.nq "$HERE/gate/gate.nq"
check_via gate12.nq "$HERE/gate12/gate12.nq"
for f in "$TMP"/multi/multi.*; do check_via "multi.${f##*.}" "$f"; done

echo "=== (4) an HDT file packed with no text in between"
tmp_hdt="$TMP/hdt"; mkdir -p "$tmp_hdt"
hdt_case() { # hdt_case NAME FILE.hdt GROUND-TRUTH KIND MODE DIGEST
  local name="$1" f="$2" truth="$3" kind="$4" mode="$5" digest="$6" rc out
  local d="$tmp_hdt/$name"; mkdir -p "$d"
  rc=0; timeout 600 "$BIN/l4sbm11-pack" "$f" "$d/gen" >"$d/pack.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then record "hdt $name pack" 1 "exit $rc: $(tail -1 "$d/pack.log")"; return; fi
  grep -q 'format=hdt' "$d/pack.log" || { record "hdt $name format" 1 "the log does not say format=hdt"; return; }
  rc=0; "$BIN/l4sbm11" verify "$d/gen" >"$d/verify.log" 2>&1 || rc=$?
  if [ "$rc" -ne 0 ]; then record "hdt $name verify" 1 "exit $rc: $(grep -m1 FAIL "$d/verify.log")"; return; fi
  "$BIN/l4sbm11" dump "$d/gen" >"$d/dump.nq" 2>"$d/dump.err" || { record "hdt $name dump" 1 "$(tail -1 "$d/dump.err")"; return; }
  "$BIN/l4sbm11-quad-source" hdt-dump "$f" >"$d/own.nq" 2>"$d/own.err" || { record "hdt $name own dump" 1 "$(tail -1 "$d/own.err")"; return; }
  out="$("$BIN/l4sbm11-w3c" compare "$d/own.nq" "$d/dump.nq" --expected nq --mode rdf12 2>&1)"
  case "$out" in
    pass*) record "hdt $name = the HDT store's own dump" 0 "$(grep -c . "$d/dump.nq") quads; $out" ;;
    *) record "hdt $name = the HDT store's own dump" 1 "$(printf '%s' "$out" | head -1 | cut -c1-200)" ;;
  esac
  if canon "$d/own.nq" "$d/own" >"$d/own.c14n" && canon "$d/dump.nq" "$d/dump" >"$d/dump.c14n" && cmp -s "$d/own.c14n" "$d/dump.c14n"; then
    record "hdt $name = the HDT store's own dump (RDFC-1.0)" 0 "$(grep -c . "$d/dump.c14n") canonical quads, equal"
  else record "hdt $name = the HDT store's own dump (RDFC-1.0)" 1 "canonical N-Quads differ"; fi
  out="$("$BIN/l4sbm11-w3c" compare "$truth" "$d/dump.nq" --expected "$kind" --mode "$mode" 2>&1)"
  case "$out" in
    pass*) record "hdt $name = the file it was made from" 0 "$out" ;;
    *) record "hdt $name = the file it was made from" 1 "$(printf '%s' "$out" | head -1 | cut -c1-200)" ;;
  esac
  local got; got="$("$BIN/l4sbm11" stats "$d/gen" 2>/dev/null | sed -n 's/^source-bytes: \([0-9]*\) source-sha256: \(.*\)$/\1 \2/p')"
  local want; want="$(stat -c %s "$f") $digest"
  if [ "$got" = "$want" ]; then record "hdt $name manifest source" 0 "the length and SHA-256 of the HDT file"
  else record "hdt $name manifest source" 1 "manifest '$got', file '$want'"; fi
}
hdt_case rml-core "$HDT/rml-core-ontology.hdt" "$TESTING/rml-modules/rml-core/ontology/documentation/ontology.nt" nt rdf11 \
  4c392b40040134ae5ba316e802572ea07e0871fbdac89880961d6df468537b6c
hdt_case test002 "$HDT/rdf-mt-test002.hdt" "$TESTING/w3c/rdf/rdf11/rdf-mt/datatypes/test002.nt" nt rdf11 \
  c5442e54470b81cf6ae44d39f32e723110b9c3af622956229060f63fd2522868
# the output does not depend on --workers (an HDT file is one producer), and --format hdt
# names the store when the extension does not
cp "$HDT/rml-core-ontology.hdt" "$tmp_hdt/store.bin"
rc=0; timeout 600 "$BIN/l4sbm11-pack" "$HDT/rml-core-ontology.hdt" "$tmp_hdt/w4" --workers 4 >"$tmp_hdt/w4.log" 2>&1 || rc=$?
rc2=0; timeout 600 "$BIN/l4sbm11-pack" "$tmp_hdt/store.bin" "$tmp_hdt/fmt" --format hdt >"$tmp_hdt/fmt.log" 2>&1 || rc2=$?
if [ "$rc" = 0 ] && [ "$rc2" = 0 ]; then
  out="$(same_gen "$tmp_hdt/rml-core/gen" "$tmp_hdt/w4")"; record "hdt --workers 4 = default" "$?" "$out"
  out="$(same_gen "$tmp_hdt/rml-core/gen" "$tmp_hdt/fmt")"; record "hdt --format hdt on store.bin = default" "$?" "$out"
else record "hdt options" 1 "exit $rc, $rc2: $(tail -1 "$tmp_hdt/w4.log" "$tmp_hdt/fmt.log" | tr '\n' ' ')"; fi
# the error paths of the producer, on stores that opened: an id that is 0 or outside the
# dictionary, and a subject after the last, are errors and never a term in a quad
for f in rml-core-ontology rdf-mt-test002; do
  rc=0; out="$("$BIN/l4sbm11-quad-source" hdt-errors "$HDT/$f.hdt" 2>&1)" || rc=$?
  sum="$(printf '%s\n' "$out" | grep '^hdt errors:')"
  if [ -n "$sum" ]; then
    sp="$(printf '%s' "$sum" | sed -n 's/.*: \([0-9]*\) pass, \([0-9]*\) fail.*/\1/p')"
    sf="$(printf '%s' "$sum" | sed -n 's/.*: \([0-9]*\) pass, \([0-9]*\) fail.*/\2/p')"
    PASS=$((PASS + sp)); FAIL=$((FAIL + sf))
    printf '%s\n' "$out" | grep -v '^hdt errors:' | sed 's/^/     /'
    echo "     $f: $sum"
    if [ "$rc" -ne 0 ] && [ "$sf" -eq 0 ]; then record "hdt $f errors-exit" 1 "exit $rc with no failed case"; fi
  else record "hdt $f errors" 1 "exit $rc: $(printf '%s\n' "$out" | tail -1)"; fi
done
# a damaged file is refused, and so is a file that is not HDT
head -c 100 "$HDT/rml-core-ontology.hdt" >"$tmp_hdt/cut.hdt"
rc=0; "$BIN/l4sbm11-pack" "$tmp_hdt/cut.hdt" "$tmp_hdt/cut" >"$tmp_hdt/cut.log" 2>&1 || rc=$?
if [ "$rc" = 1 ] && grep -q 'not a readable HDT file' "$tmp_hdt/cut.log"; then record "hdt truncated file" 0 "refused: $(tail -1 "$tmp_hdt/cut.log" | cut -c1-100)"
else record "hdt truncated file" 1 "exit $rc: $(tail -1 "$tmp_hdt/cut.log")"; fi
rc=0; "$BIN/l4sbm11-pack" "$FX/d1.nt" "$tmp_hdt/nt-as-hdt" --format hdt >"$tmp_hdt/nt.log" 2>&1 || rc=$?
if [ "$rc" = 1 ] && grep -q 'not a readable HDT file' "$tmp_hdt/nt.log"; then record "hdt a text file" 0 "refused"
else record "hdt a text file" 1 "exit $rc: $(tail -1 "$tmp_hdt/nt.log")"; fi

echo "=== (5) layering: the producer interface names no syntax"
rc=0
out="$(python3 -I "$HERE/storage_layering.py" 2>&1)" || rc=$?
if [ "$rc" -eq 0 ]; then record layering 0 "$(printf '%s' "$out" | tail -1)"
else record layering 1 "exit $rc: $(printf '%s' "$out" | head -3 | tr '\n' ' ')"; fi

echo
echo "quad source: $PASS pass, $FAIL fail, $XFAIL expected-fail (out of $((PASS + FAIL + XFAIL)))"
[ "$FAIL" -eq 0 ]
