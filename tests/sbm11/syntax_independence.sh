#!/usr/bin/env bash
#
# tests/sbm11/syntax_independence.sh -- SBM11 stores an RDF dataset, not a
# syntax (owner, 2026-10-14; https://github.com/danbri/factoidal/issues/837).
#
# Hand-written fixtures in tests/sbm11/syntax/ write the same dataset in
# several syntaxes. Each is packed with `l4sbm11-pack` (the format from the
# file extension) and the generations are compared:
#
#   D1  IRIs, xsd:string, language-tagged and typed literals (integer, a
#       non-canonical integer, date, a custom datatype), no blank nodes,
#       default graph only. Written as .nt .nq .ttl .trig .rdf .jsonld. Every
#       file of the six generations except the manifest is byte-identical; the
#       manifests differ only in the source length and the source digest.
#   D2  D1 and two named graphs. Written as .nq .trig .jsonld. The same check.
#   D4  RDF 1.2: triple terms (one nested in another) and a directional
#       language string. Written as .nt .nq .ttl .trig. The same check as D1.
#   D3  blank nodes: labelled, anonymous, a property list, a collection.
#       Written in all six syntaxes. A blank node label is a name for the
#       document, so the generations are not compared byte for byte: the
#       RDFC-1.0 canonical N-Quads (`l4factoidal canonicalize`) of
#       `l4sbm11 dump` are.
#   multi  one generated dataset of about 1 MB (gen_multi.py) in .nt .ttl
#       (default graph) and .nq .trig (named graphs), so that the 64 KiB
#       chunks of the readers cut tokens and UTF-8 sequences. The same
#       byte-identity check.
#   blank nodes of one document stay distinct: explicit labels that a
#       generated label could equal, and anonymous nodes, in one document
#       (bnode_collide.*): five distinct blank nodes in each of the four syntaxes
#       that mint labels. The JSON-LD reader chooses the prefix of the labels it
#       generates from the document (until 2026-10-14 it merged the explicit
#       `_:_jld_anon0` with the generated `_jld_anon0`, and read three nodes,
#       https://github.com/danbri/factoidal/issues/840).
#   xml:lang of one property element does not reach the next
#       (lang_scope.rdf against lang_scope.nt): the RDF/XML reader gives the
#       quads of the N-Triples twin (XML 1.0 section 2.12; until 2026-10-14 it
#       gave "b"@fr for the plain "b", https://github.com/danbri/factoidal/issues/841).
#       scope_paths.rdf against scope_paths.nt: the same rule for every kind of
#       property element, for xml:base and for nested node elements.
#   format selection: an unknown extension is refused with a message that asks
#       for --format (no default syntax); --format decides; N-Triples refuses a
#       graph name and N-Quads reads it.
#   every generation passes `l4sbm11 verify` (the activation checks).
#   the other readers of the source layer: `l4sbm11-dict-pack` (packer phases 1
#       and 2) writes the two dictionary files of the pack for every fixture in
#       every syntax; `l4factoidal parse --format F --out nquads` gives the same
#       N-Quads for D1 and D2 in every syntax that writes them (D3: equal RDFC-1.0
#       canonical N-Quads). Neither command has a format table of its own.
#
# Prints "N pass, M fail, K expected-fail (out of T)". Exit 0 when no case
# failed and no expected failure passed; 2 when a binary is missing.
#
# Env: L4_BIN_DIR   directory of l4sbm11, l4sbm11-pack, l4sbm11-dict-pack and l4factoidal
#                   (default formal/lean4/.lake/build/bin)
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_BIN_DIR:-$ROOT/formal/lean4/.lake/build/bin}"
FX="$HERE/syntax"
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack" "$BIN/l4sbm11-dict-pack" "$BIN/l4factoidal" "$FX/d1.nt"; do
  if [ ! -e "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-syntax.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
PASS=0; FAIL=0; XFAIL=0
record() { # record <name> <ok:0|1> <detail>
  if [ "$2" = 0 ]; then PASS=$((PASS + 1)); printf 'ok     %-34s %s\n' "$1" "$3"
  else FAIL=$((FAIL + 1)); printf 'FAIL   %-34s %s\n' "$1" "$3"; fi
}
xfail() { # xfail <name> <issue-url> <expected-failure-holds:0|1> <detail>
  if [ "$3" = 0 ]; then XFAIL=$((XFAIL + 1)); printf 'XFAIL  %-34s (%s) %s\n' "$1" "$2" "$4"
  else FAIL=$((FAIL + 1)); printf 'XPASS  %-34s (%s) %s -- flip this case to a real assertion and close the issue\n' "$1" "$2" "$4"; fi
}

# pack NAME SOURCE [ARGS...]: pack SOURCE to $TMP/NAME; the log is $TMP/NAME.log
pack() {
  local name="$1" src="$2"; shift 2
  rm -rf "$TMP/$name"
  timeout 600 "$BIN/l4sbm11-pack" "$src" "$TMP/$name" "$@" >"$TMP/$name.log" 2>&1
}

# same_data A B: every file of A except the manifest is in B, byte for byte,
# and B has no other file. Prints the number of files compared.
same_data() {
  local a="$TMP/$1" b="$TMP/$2" f n=0
  [ "$(ls "$a" | grep -v '^manifest.sbm11$' | sort)" = "$(ls "$b" | grep -v '^manifest.sbm11$' | sort)" ] || { echo "file lists differ"; return 1; }
  for f in $(ls "$a" | grep -v '^manifest.sbm11$'); do
    cmp -s "$a/$f" "$b/$f" || { echo "$f differs"; return 1; }
    n=$((n + 1))
  done
  echo "$n files byte-identical"
}

# manifests_differ_in_source_only A B: the manifest bytes are equal outside the
# 40 bytes that follow the layout string (the source length, 8 bytes, and the
# source SHA-256, 32 bytes), and the digests are different.
manifests_differ_in_source_only() {
  local layout
  layout="$("$BIN/l4sbm11" stats "$TMP/$1" 2>/dev/null | sed -n 's/^layout: //p')"
  python3 -I - "$TMP/$1/manifest.sbm11" "$TMP/$2/manifest.sbm11" "$layout" <<'PY'
import sys
a, b = (open(p, "rb").read() for p in sys.argv[1:3])
layout = sys.argv[3].encode()
if len(a) != len(b): sys.exit("manifest lengths differ: %d, %d" % (len(a), len(b)))
at = a.index(layout) + len(layout)
if b.index(layout) + len(layout) != at: sys.exit("layout strings are at different places")
if a[:at] != b[:at] or a[at + 40:] != b[at + 40:]:
    sys.exit("manifests differ outside the source length and digest")
if a[at + 8:at + 40] == b[at + 8:at + 40]: sys.exit("the source digests are equal")
print("differ only in the source length (%d, %d) and digest" % (
    int.from_bytes(a[at:at + 8], "little"), int.from_bytes(b[at:at + 8], "little")))
PY
}

# check_pair REF OTHER LABEL: the data files are equal and the manifests differ
# only in the source fields.
check_pair() {
  local ref="$1" other="$2" label="$3" out
  if ! out="$(same_data "$ref" "$other")"; then record "$label data" 1 "$out"; return; fi
  record "$label data" 0 "$out"
  if out="$(manifests_differ_in_source_only "$ref" "$other" 2>&1)"; then record "$label manifest" 0 "$out"
  else record "$label manifest" 1 "$out"; fi
}

verify_gen() { # verify_gen NAME
  local rc=0
  "$BIN/l4sbm11" verify "$TMP/$1" >"$TMP/$1.verify" 2>&1 || rc=$?
  if [ "$rc" = 0 ]; then record "verify $1" 0 "activation checks pass"
  else record "verify $1" 1 "exit $rc: $(tail -1 "$TMP/$1.verify")"; fi
}

echo "=== D1: no blank nodes, default graph, six syntaxes"
for ext in nt nq ttl trig rdf jsonld; do
  rc=0; pack "d1-$ext" "$FX/d1.$ext" || rc=$?
  if [ "$rc" != 0 ]; then record "d1 pack .$ext" 1 "exit $rc: $(tail -1 "$TMP/d1-$ext.log")"; fi
done
for ext in nq ttl trig rdf jsonld; do
  [ -d "$TMP/d1-$ext" ] && check_pair d1-nt "d1-$ext" "d1 .nt = .$ext"
done
for ext in nt nq ttl trig rdf jsonld; do [ -d "$TMP/d1-$ext" ] && verify_gen "d1-$ext"; done

echo "=== D2: D1 and named graphs, three syntaxes"
for ext in nq trig jsonld; do
  rc=0; pack "d2-$ext" "$FX/d2.$ext" || rc=$?
  if [ "$rc" != 0 ]; then record "d2 pack .$ext" 1 "exit $rc: $(tail -1 "$TMP/d2-$ext.log")"; fi
done
for ext in trig jsonld; do
  [ -d "$TMP/d2-$ext" ] && check_pair d2-nq "d2-$ext" "d2 .nq = .$ext"
done
for ext in nq trig jsonld; do [ -d "$TMP/d2-$ext" ] && verify_gen "d2-$ext"; done
# D2 is D1 plus four quads: the graph column is stored, not dropped.
q1="$(sed -n 's/^quads: \([0-9]*\) .*/\1/p' <("$BIN/l4sbm11" stats "$TMP/d1-nt" 2>/dev/null))"
q2="$(sed -n 's/^quads: \([0-9]*\) .*/\1/p' <("$BIN/l4sbm11" stats "$TMP/d2-nq" 2>/dev/null))"
if [ -n "$q1" ] && [ "$q2" = "$((q1 + 4))" ]; then record "d2 graph quads" 0 "D1 has $q1 quads, D2 has $q2"
else record "d2 graph quads" 1 "D1 $q1, D2 $q2, expected D1 + 4"; fi

echo "=== D4: RDF 1.2 triple terms (nested) and a directional language string, four syntaxes"
for ext in nt nq ttl trig; do
  rc=0; pack "d4-$ext" "$FX/d4.$ext" || rc=$?
  if [ "$rc" != 0 ]; then record "d4 pack .$ext" 1 "exit $rc: $(tail -1 "$TMP/d4-$ext.log")"; fi
done
for ext in nq ttl trig; do
  [ -d "$TMP/d4-$ext" ] && check_pair d4-nt "d4-$ext" "d4 .nt = .$ext"
done
for ext in nt nq ttl trig; do [ -d "$TMP/d4-$ext" ] && verify_gen "d4-$ext"; done
# The dump holds the triple terms: two outer ones and one nested in a third.
if [ -d "$TMP/d4-nt" ]; then
  tt="$("$BIN/l4sbm11" dump "$TMP/d4-nt" 2>/dev/null | grep -c '<<(')"
  if [ "$tt" = 3 ]; then record "d4 triple terms" 0 "3 quads have a triple term as object"
  else record "d4 triple terms" 1 "$tt quads have a triple term, expected 3"; fi
fi

echo "=== D3: blank nodes, six syntaxes, RDFC-1.0 canonical N-Quads of the dump"
for ext in nt nq ttl trig rdf jsonld; do
  rc=0; pack "d3-$ext" "$FX/d3.$ext" || rc=$?
  if [ "$rc" != 0 ]; then record "d3 pack .$ext" 1 "exit $rc: $(tail -1 "$TMP/d3-$ext.log")"; continue; fi
  "$BIN/l4sbm11" dump "$TMP/d3-$ext" >"$TMP/d3-$ext.dump.nq" 2>/dev/null
  crc=0
  "$BIN/l4factoidal" canonicalize "$TMP/d3-$ext.dump.nq" --format nquads >"$TMP/d3-$ext.c14n" 2>"$TMP/d3-$ext.c14n.err" || crc=$?
  if [ "$crc" != 0 ]; then record "d3 canonicalize .$ext" 1 "exit $crc: $(head -1 "$TMP/d3-$ext.c14n.err")"; fi
done
for ext in nq ttl trig rdf jsonld; do
  if [ -s "$TMP/d3-nt.c14n" ] && cmp -s "$TMP/d3-nt.c14n" "$TMP/d3-$ext.c14n"; then
    record "d3 .nt = .$ext" 0 "$(wc -l <"$TMP/d3-$ext.c14n") canonical quads, equal"
  else record "d3 .nt = .$ext" 1 "canonical N-Quads differ or are missing"; fi
done
for ext in nt nq ttl trig rdf jsonld; do [ -d "$TMP/d3-$ext" ] && verify_gen "d3-$ext"; done

echo "=== multi-chunk dataset (about 1 MB): chunk boundaries inside tokens and code points"
mkdir -p "$TMP/multi"
if python3 -I "$FX/gen_multi.py" "$TMP/multi" 1500; then
  for ext in nt ttl nq trig; do
    rc=0; pack "multi-$ext" "$TMP/multi/multi.$ext" || rc=$?
    if [ "$rc" != 0 ]; then record "multi pack .$ext" 1 "exit $rc: $(tail -1 "$TMP/multi-$ext.log")"; fi
  done
  [ -d "$TMP/multi-ttl" ] && check_pair multi-nt multi-ttl "multi .nt = .ttl"
  [ -d "$TMP/multi-trig" ] && check_pair multi-nq multi-trig "multi .nq = .trig"
  for ext in nt ttl nq trig; do [ -d "$TMP/multi-$ext" ] && verify_gen "multi-$ext"; done
else record "multi generate" 1 "gen_multi.py failed"; fi

echo "=== blank nodes of one document stay distinct"
distinct_subjects() { # NAME: distinct blank node subjects in the dump
  "$BIN/l4sbm11" dump "$TMP/$1" 2>/dev/null | grep -o '^_:[^ ]*' | sort -u | wc -l
}
for ext in ttl trig rdf jsonld; do
  rc=0; pack "bc-$ext" "$FX/bnode_collide.$ext" || rc=$?
  if [ "$rc" != 0 ]; then record "bnode-collide $ext" 1 "exit $rc: $(tail -1 "$TMP/bc-$ext.log")"; continue; fi
  n="$(distinct_subjects "bc-$ext")"
  if [ "$n" = 5 ]; then record "bnode-collide $ext" 0 "5 distinct blank nodes"
  else record "bnode-collide $ext" 1 "$n distinct blank nodes, expected 5"; fi
done

echo "=== xml:lang of one property element does not reach the next"
# RDF/XML and its N-Triples twin (tests/sbm11/syntax/lang_scope.*) give the same
# quads (XML 1.0 section 2.12: the language applies to the element that specifies
# it and its content; https://github.com/danbri/factoidal/issues/841).
# scope_paths.* has no blank node and one property element of each kind
# (literal content, datatype, empty, rdf:resource, a nested node element) that
# sets xml:lang or xml:base, each followed by a property element that must not see it.
for pair in lang_scope scope_paths; do
  "$BIN/l4sbm11" canon "$FX/$pair.nt" 2>/dev/null | sort >"$TMP/$pair.nt.canon"
  "$BIN/l4sbm11" canon "$FX/$pair.rdf" 2>/dev/null | sort >"$TMP/$pair.rdf.canon"
  name="${pair//_/-}"
  if [ ! -s "$TMP/$pair.nt.canon" ]; then record "$name rdfxml" 1 "the N-Triples twin did not read"
  elif [ ! -s "$TMP/$pair.rdf.canon" ]; then record "$name rdfxml" 1 "the RDF/XML file did not read"
  elif cmp -s "$TMP/$pair.nt.canon" "$TMP/$pair.rdf.canon"; then
    record "$name rdfxml" 0 "$(wc -l <"$TMP/$pair.rdf.canon") quads, equal to the N-Triples twin ($(grep -c '@' "$TMP/$pair.rdf.canon") with a language tag)"
  else
    record "$name rdfxml" 1 "RDF/XML reads $(grep -c '@fr' "$TMP/$pair.rdf.canon") French literals where the twin has $(grep -c '@fr' "$TMP/$pair.nt.canon"): $(diff "$TMP/$pair.nt.canon" "$TMP/$pair.rdf.canon" | grep '^[<>]' | head -1 | cut -c1-100)"
  fi
done

echo "=== format selection"
cp "$FX/d1.ttl" "$TMP/noext"
cp "$FX/d1.ttl" "$TMP/odd.dat"
for src in noext odd.dat; do
  rc=0; pack "fs-$src" "$TMP/$src" || rc=$?
  if [ "$rc" != 0 ] && grep -q -- '--format' "$TMP/fs-$src.log"; then record "no default syntax ($src)" 0 "refused, asks for --format"
  else record "no default syntax ($src)" 1 "exit $rc: $(tail -1 "$TMP/fs-$src.log")"; fi
done
rc=0; pack fs-flag "$TMP/odd.dat" --format turtle || rc=$?
if [ "$rc" = 0 ]; then
  out="$(same_data d1-ttl fs-flag)"; r=$?
  record "--format turtle on odd.dat" "$r" "$out"
else record "--format turtle on odd.dat" 1 "exit $rc: $(tail -1 "$TMP/fs-flag.log")"; fi
rc=0; pack fs-bad "$TMP/odd.dat" --format nonsense || rc=$?
if [ "$rc" != 0 ] && grep -q "unknown format 'nonsense'" "$TMP/fs-bad.log"; then record "--format nonsense" 0 "refused by name"
else record "--format nonsense" 1 "exit $rc: $(tail -1 "$TMP/fs-bad.log")"; fi
printf '<http://e/s> <http://e/p> <http://e/o> <http://e/g> .\n' >"$TMP/quad.nt"
cp "$TMP/quad.nt" "$TMP/quad.nq"
rc=0; pack fs-nt-graph "$TMP/quad.nt" || rc=$?
if [ "$rc" != 0 ] && grep -q "parse error at" "$TMP/fs-nt-graph.log"; then record "N-Triples refuses a graph name" 0 "$(tail -1 "$TMP/fs-nt-graph.log" | sed 's/^[^ ]* [^ ]* //' | cut -c1-100)"
else record "N-Triples refuses a graph name" 1 "exit $rc: $(tail -1 "$TMP/fs-nt-graph.log")"; fi
rc=0; pack fs-nq-graph "$TMP/quad.nq" || rc=$?
if [ "$rc" = 0 ]; then record "N-Quads reads a graph name" 0 "1 quad packed"
else record "N-Quads reads a graph name" 1 "exit $rc: $(tail -1 "$TMP/fs-nq-graph.log")"; fi
rc=0; "$BIN/l4sbm11" canon "$TMP/noext" >"$TMP/canon.out" 2>"$TMP/canon.err" || rc=$?
if [ "$rc" != 0 ] && grep -q -- '--format' "$TMP/canon.err"; then record "canon: no default syntax" 0 "refused, asks for --format"
else record "canon: no default syntax" 1 "exit $rc: $(tail -1 "$TMP/canon.err")"; fi

echo "=== l4sbm11-dict-pack reads every syntax: its dictionary files are the pack's"
for spec in d1:nt d1:nq d1:ttl d1:trig d1:rdf d1:jsonld d2:nq d2:trig d2:jsonld \
            d4:nt d4:nq d4:ttl d4:trig d3:nt d3:nq d3:ttl d3:trig d3:rdf d3:jsonld; do
  name="${spec%%:*}"; ext="${spec##*:}"; dp="dp-$name-$ext"
  rm -rf "$TMP/$dp"; rc=0
  timeout 300 "$BIN/l4sbm11-dict-pack" "$FX/$name.$ext" "$TMP/$dp" >"$TMP/$dp.log" 2>&1 || rc=$?
  if [ "$rc" != 0 ]; then record "dict-pack $name .$ext" 1 "exit $rc: $(tail -1 "$TMP/$dp.log" | cut -c1-120)"; continue; fi
  if [ -d "$TMP/$name-$ext" ] && cmp -s "$TMP/$dp/dict.gdv1" "$TMP/$name-$ext/dict.gdv1" \
      && cmp -s "$TMP/$dp/dict.gdx1" "$TMP/$name-$ext/dict.gdx1"; then
    record "dict-pack $name .$ext" 0 "dict.gdv1 and dict.gdx1 equal those of l4sbm11-pack"
  else record "dict-pack $name .$ext" 1 "the dictionary files differ from those of l4sbm11-pack"; fi
done

echo "=== l4factoidal parse reads every syntax: the same N-Quads for one dataset"
parse_tag() { case "$1" in nt) echo ntriples;; nq) echo nquads;; ttl) echo turtle;; trig) echo trig;; rdf) echo rdfxml;; jsonld) echo jsonld;; esac; }
parse_sorted() { # parse_sorted FIXTURE EXT OUT: N-Quads of the fixture, sorted
  "$BIN/l4factoidal" parse "$FX/$1.$2" --format "$(parse_tag "$2")" --out nquads 2>"$TMP/parse.err" | sort >"$3"
  [ "${PIPESTATUS[0]}" = 0 ] && [ -s "$3" ]
}
for ext in nt nq ttl trig rdf jsonld; do
  parse_sorted d1 "$ext" "$TMP/parse-d1-$ext.nq" || record "parse d1 .$ext" 1 "$(head -1 "$TMP/parse.err" | cut -c1-120)"
done
for ext in nq ttl trig rdf jsonld; do
  if [ -s "$TMP/parse-d1-nt.nq" ] && cmp -s "$TMP/parse-d1-nt.nq" "$TMP/parse-d1-$ext.nq"; then
    record "parse d1 .nt = .$ext" 0 "$(wc -l <"$TMP/parse-d1-$ext.nq") quads, equal"
  else record "parse d1 .nt = .$ext" 1 "the N-Quads differ or are missing"; fi
done
for ext in nq trig jsonld; do
  parse_sorted d2 "$ext" "$TMP/parse-d2-$ext.nq" || record "parse d2 .$ext" 1 "$(head -1 "$TMP/parse.err" | cut -c1-120)"
done
for ext in trig jsonld; do
  if [ -s "$TMP/parse-d2-nq.nq" ] && cmp -s "$TMP/parse-d2-nq.nq" "$TMP/parse-d2-$ext.nq"; then
    record "parse d2 .nq = .$ext" 0 "$(wc -l <"$TMP/parse-d2-$ext.nq") quads, equal"
  else record "parse d2 .nq = .$ext" 1 "the N-Quads differ or are missing"; fi
done
for ext in nt nq ttl trig rdf jsonld; do
  if parse_sorted d3 "$ext" "$TMP/parse-d3-$ext.nq" \
      && "$BIN/l4factoidal" canonicalize "$TMP/parse-d3-$ext.nq" --format nquads >"$TMP/parse-d3-$ext.c14n" 2>/dev/null; then :
  else record "parse d3 .$ext" 1 "parse or canonicalize failed: $(head -1 "$TMP/parse.err" | cut -c1-120)"; fi
done
for ext in nq ttl trig rdf jsonld; do
  if [ -s "$TMP/parse-d3-nt.c14n" ] && cmp -s "$TMP/parse-d3-nt.c14n" "$TMP/parse-d3-$ext.c14n"; then
    record "parse d3 .nt = .$ext" 0 "$(wc -l <"$TMP/parse-d3-$ext.c14n") canonical quads, equal"
  else record "parse d3 .nt = .$ext" 1 "canonical N-Quads differ or are missing"; fi
done

echo
echo "syntax independence: $PASS pass, $FAIL fail, $XFAIL expected-fail (out of $((PASS + FAIL + XFAIL)))"
[ "$FAIL" -eq 0 ]
