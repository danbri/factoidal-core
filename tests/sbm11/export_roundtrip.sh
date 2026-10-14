#!/usr/bin/env bash
#
# tests/sbm11/export_roundtrip.sh -- `l4sbm11 export` writes the dataset a
# generation stores in any of the six RDF syntaxes through the serialiser layer
# (L4Factoidal/RDF/Sink.lean; https://github.com/danbri/factoidal/issues/837 item 6).
#
# The check is a round trip through the store: a fixture of tests/sbm11/syntax/
# is packed, the generation is exported in a syntax, the export is packed, and
# the data files of the two generations are byte-identical (the manifests differ
# in the source length and digest). The fixtures:
#
#   D1  no blank nodes, default graph only: all six syntaxes. The exported RDF/XML
#       has a plain literal after a language-tagged one in the same node element;
#       the Lean RDF/XML reader reads it plain (XML 1.0 section 2.12). Until
#       2026-10-14 it read "Alice" as "Alice"@en, because it applied the `xml:lang`
#       of a property element to the property elements after it
#       (https://github.com/danbri/factoidal/issues/841).
#   D2  D1 and four quads in two named graphs: N-Quads, TriG and JSON-LD. N-Triples,
#       Turtle and RDF/XML have no graph name, and the export is refused before it
#       writes a byte; `--graph default`, `--graph all` and `--graph IRI` choose.
#   D4  RDF 1.2 (triple terms, nested; a directional language string): N-Triples,
#       N-Quads, Turtle and TriG. RDF/XML and JSON-LD have no form for a triple
#       term, and the export says so.
#   D3  blank nodes: all six syntaxes, compared by the RDFC-1.0 canonical N-Quads
#       of `l4sbm11 dump` (a reader may name a blank node differently).
#   multi  a generated dataset of about 1 MB (tests/sbm11/syntax/gen_multi.py,
#       N-Triples and N-Quads), so that the output crosses many 64 KiB writes and
#       the SPO order interleaves the graphs (TriG starts a new block each time the
#       graph changes): N-Quads, TriG, N-Triples, Turtle and RDF/XML (the default
#       graph only). In the RDF/XML of the 12,000 triples the `note` of every
#       subject follows its language-tagged labels (the order of the keys), which
#       is the shape of https://github.com/danbri/factoidal/issues/841.
#
# And: `export --format nquads` is `dump` byte for byte; `--out` writes the file
# and a refused export leaves none; `--prefix` shortens the IRIs and the export
# reads back the same; an empty generation exports in every syntax to a document
# that packs to an empty generation; the usage errors exit 2.
#
# Prints "N pass, M fail, K expected-fail (out of T)". Exit 0 when no case failed
# and no expected failure passed; 2 when a binary is missing.
#
# Env: L4_BIN_DIR   directory of l4sbm11, l4sbm11-pack and l4factoidal
#                   (default formal/lean4/.lake/build/bin)
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_BIN_DIR:-$ROOT/formal/lean4/.lake/build/bin}"
FX="$HERE/syntax"
for need in "$BIN/l4sbm11" "$BIN/l4sbm11-pack" "$BIN/l4factoidal" "$FX/d1.nt"; do
  if [ ! -e "$need" ]; then echo "missing: $need" >&2; exit 2; fi
done
TMP="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-export.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
PASS=0; FAIL=0; XFAIL=0
record() { # record <name> <ok:0|1> <detail>
  if [ "$2" = 0 ]; then PASS=$((PASS + 1)); printf 'ok     %-40s %s\n' "$1" "$3"
  else FAIL=$((FAIL + 1)); printf 'FAIL   %-40s %s\n' "$1" "$3"; fi
}
xfail() { # xfail <name> <issue-url> <expected-failure-holds:0|1> <detail>
  if [ "$3" = 0 ]; then XFAIL=$((XFAIL + 1)); printf 'XFAIL  %-40s (%s) %s\n' "$1" "$2" "$4"
  else FAIL=$((FAIL + 1)); printf 'XPASS  %-40s (%s) %s -- flip this case to a real assertion and close the issue\n' "$1" "$2" "$4"; fi
}

# pack NAME SOURCE [ARGS...]: pack SOURCE to $TMP/NAME
pack() {
  local name="$1" src="$2"; shift 2
  rm -rf "$TMP/$name"
  timeout 600 "$BIN/l4sbm11-pack" "$src" "$TMP/$name" "$@" >"$TMP/$name.log" 2>&1
}

# same_data A B: every file of A except the manifest is in B, byte for byte, and
# B has no other file. Prints the number of files compared.
same_data() {
  local a="$TMP/$1" b="$TMP/$2" f n=0
  [ "$(ls "$a" | grep -v '^manifest.sbm11$' | sort)" = "$(ls "$b" | grep -v '^manifest.sbm11$' | sort)" ] || { echo "file lists differ"; return 1; }
  for f in $(ls "$a" | grep -v '^manifest.sbm11$'); do
    cmp -s "$a/$f" "$b/$f" || { echo "$f differs"; return 1; }
    n=$((n + 1))
  done
  echo "$n files byte-identical"
}

EXT_OF=(nquads:nq ntriples:nt turtle:ttl trig:trig rdfxml:rdf jsonld:jsonld)
ext_of() { local f; for f in "${EXT_OF[@]}"; do [ "${f%%:*}" = "$1" ] && { echo "${f##*:}"; return; }; done; }

# roundtrip REF NAME FORMAT: export generation REF in FORMAT to $TMP/NAME.EXT, pack
# it as NAME; exit 0 when the data files equal REF's. Prints why not.
roundtrip() {
  local ref="$1" name="$2" fmt="$3" ext rc=0 out
  ext="$(ext_of "$fmt")"
  timeout 600 "$BIN/l4sbm11" export "$TMP/$ref" --format "$fmt" --out "$TMP/$name.$ext" >"$TMP/$name.export.out" 2>"$TMP/$name.export.err" || rc=$?
  if [ "$rc" -ne 0 ]; then echo "export exit $rc: $(head -1 "$TMP/$name.export.err" | cut -c1-160)"; return 1; fi
  if ! pack "$name" "$TMP/$name.$ext"; then echo "pack of the export failed: $(tail -1 "$TMP/$name.log" | cut -c1-160)"; return 1; fi
  same_data "$ref" "$name"
}

echo "=== D1, D2, D4: export in each syntax that can write the dataset, pack, byte-identical data files"
pack d1 "$FX/d1.nt" || record "pack d1" 1 "$(tail -1 "$TMP/d1.log")"
pack d2 "$FX/d2.nq" || record "pack d2" 1 "$(tail -1 "$TMP/d2.log")"
pack d4 "$FX/d4.nt" || record "pack d4" 1 "$(tail -1 "$TMP/d4.log")"
for fmt in nquads ntriples turtle trig rdfxml jsonld; do
  out="$(roundtrip d1 "d1-$fmt" "$fmt")"; record "d1 export $fmt" $? "$out"
done
for fmt in nquads trig jsonld; do
  out="$(roundtrip d2 "d2-$fmt" "$fmt")"; record "d2 export $fmt" $? "$out"
done
for fmt in nquads ntriples turtle trig; do
  out="$(roundtrip d4 "d4-$fmt" "$fmt")"; record "d4 export $fmt" $? "$out"
done

echo "=== syntaxes with no graph name refuse a generation with named graphs, before any output"
for fmt in ntriples turtle rdfxml; do
  rc=0
  "$BIN/l4sbm11" export "$TMP/d2" --format "$fmt" >"$TMP/refuse.out" 2>"$TMP/refuse.err" || rc=$?
  if [ "$rc" = 1 ] && [ ! -s "$TMP/refuse.out" ] && grep -q 'named graphs (the first graph is <http://example.org/g1>)' "$TMP/refuse.err" \
      && grep -q -- '--graph' "$TMP/refuse.err"; then
    record "d2 export $fmt refused" 0 "exit 1, no output, names the graph and the choices"
  else record "d2 export $fmt refused" 1 "exit $rc, $(wc -c <"$TMP/refuse.out") bytes on stdout: $(head -1 "$TMP/refuse.err" | cut -c1-160)"; fi
done
rc=0
"$BIN/l4sbm11" export "$TMP/d2" --format ntriples --out "$TMP/refused.nt" >/dev/null 2>&1 || rc=$?
if [ "$rc" = 1 ] && [ ! -e "$TMP/refused.nt" ] && [ -z "$(ls "$TMP" | grep 'refused.nt.tmp')" ]; then
  record "refused export leaves no file" 0 "no FILE and no temporary file"
else record "refused export leaves no file" 1 "exit $rc; $(ls "$TMP" | grep refused | tr '\n' ' ')"; fi

echo "=== --graph chooses the quads of a syntax with no graph name"
# D2 is D1 plus four quads in two named graphs: the default graph is D1.
rc=0
"$BIN/l4sbm11" export "$TMP/d2" --format ntriples --graph default --out "$TMP/d2-default.nt" >/dev/null 2>"$TMP/g.err" || rc=$?
if [ "$rc" = 0 ] && pack d2-default "$TMP/d2-default.nt"; then out="$(same_data d1 d2-default)"; record "--graph default = D1" $? "$out"
else record "--graph default = D1" 1 "exit $rc: $(head -1 "$TMP/g.err")"; fi
# the union: the quads of d2.nq without their graph names, one triple once
grep -v '^#' "$FX/d2.nq" | sed -E 's/ <http:\/\/example\.org\/g[12]> \.$/ ./' | sort -u >"$TMP/d2-union.nt"
rc=0
"$BIN/l4sbm11" export "$TMP/d2" --format ntriples --graph all --out "$TMP/d2-all.nt" >/dev/null 2>"$TMP/g.err" || rc=$?
if [ "$rc" = 0 ] && pack d2-all "$TMP/d2-all.nt" && pack d2-union "$TMP/d2-union.nt"; then
  out="$(same_data d2-union d2-all)"; record "--graph all = the union" $? "$out"
else record "--graph all = the union" 1 "exit $rc: $(head -1 "$TMP/g.err")"; fi
# one graph
grep '<http://example.org/g2> \.$' "$FX/d2.nq" | sed -E 's/ <http:\/\/example\.org\/g2> \.$/ ./' >"$TMP/d2-g2.nt"
rc=0
"$BIN/l4sbm11" export "$TMP/d2" --format turtle --graph http://example.org/g2 --out "$TMP/d2-g2.ttl" >/dev/null 2>"$TMP/g.err" || rc=$?
if [ "$rc" = 0 ] && pack d2-g2 "$TMP/d2-g2.ttl" && pack d2-g2-ref "$TMP/d2-g2.nt"; then
  out="$(same_data d2-g2-ref d2-g2)"; record "--graph IRI = that graph (Turtle)" $? "$out"
else record "--graph IRI = that graph (Turtle)" 1 "exit $rc: $(head -1 "$TMP/g.err")"; fi
rc=0
"$BIN/l4sbm11" export "$TMP/d2" --format ntriples --graph http://example.org/nowhere >/dev/null 2>"$TMP/g.err" || rc=$?
if [ "$rc" = 1 ] && grep -q 'is not in the store' "$TMP/g.err"; then record "--graph IRI not in the store" 0 "refused by name"
else record "--graph IRI not in the store" 1 "exit $rc: $(head -1 "$TMP/g.err")"; fi
rc=0
"$BIN/l4sbm11" export "$TMP/d2" --format nquads --graph all >/dev/null 2>"$TMP/g.err" || rc=$?
if [ "$rc" = 2 ]; then record "--graph with N-Quads is a usage error" 0 "exit 2"
else record "--graph with N-Quads is a usage error" 1 "exit $rc"; fi

echo "=== syntaxes with no form for a term say so"
for fmt in rdfxml jsonld; do
  rc=0
  "$BIN/l4sbm11" export "$TMP/d4" --format "$fmt" --out "$TMP/d4-refused.$fmt" >/dev/null 2>"$TMP/refuse.err" || rc=$?
  if [ "$rc" = 1 ] && grep -qi 'triple term' "$TMP/refuse.err" && [ ! -e "$TMP/d4-refused.$fmt" ]; then
    record "d4 export $fmt refused" 0 "$(head -1 "$TMP/refuse.err" | cut -c1-100)"
  else record "d4 export $fmt refused" 1 "exit $rc: $(head -1 "$TMP/refuse.err" | cut -c1-160)"; fi
done

echo "=== D3: blank nodes, six syntaxes, RDFC-1.0 canonical N-Quads of the dump"
pack d3 "$FX/d3.nt" || record "pack d3" 1 "$(tail -1 "$TMP/d3.log")"
canon_of() { # canon_of GEN OUT: RDFC-1.0 canonical N-Quads of the dump of GEN
  "$BIN/l4sbm11" dump "$TMP/$1" >"$TMP/$1.dump.nq" 2>/dev/null &&
    "$BIN/l4factoidal" canonicalize "$TMP/$1.dump.nq" --format nquads >"$2" 2>/dev/null
}
canon_of d3 "$TMP/d3.c14n"
for fmt in nquads ntriples turtle trig rdfxml jsonld; do
  ext="$(ext_of "$fmt")"; rc=0
  "$BIN/l4sbm11" export "$TMP/d3" --format "$fmt" --out "$TMP/d3-$fmt.$ext" >/dev/null 2>"$TMP/d3.err" || rc=$?
  if [ "$rc" -ne 0 ]; then record "d3 export $fmt" 1 "export exit $rc: $(head -1 "$TMP/d3.err" | cut -c1-160)"; continue; fi
  if pack "d3-$fmt" "$TMP/d3-$fmt.$ext" && canon_of "d3-$fmt" "$TMP/d3-$fmt.c14n" && [ -s "$TMP/d3.c14n" ] && cmp -s "$TMP/d3.c14n" "$TMP/d3-$fmt.c14n"; then
    record "d3 export $fmt" 0 "$(wc -l <"$TMP/d3-$fmt.c14n") canonical quads, equal"
  else record "d3 export $fmt" 1 "pack failed or the canonical N-Quads differ"; fi
done

echo "=== N-Quads export is dump, byte for byte"
for g in d1 d2 d3 d4; do
  "$BIN/l4sbm11" dump "$TMP/$g" >"$TMP/$g.dump" 2>/dev/null
  "$BIN/l4sbm11" export "$TMP/$g" --format nquads >"$TMP/$g.exp" 2>/dev/null
  if [ -s "$TMP/$g.dump" ] && cmp -s "$TMP/$g.dump" "$TMP/$g.exp"; then record "$g export nquads = dump" 0 "$(wc -c <"$TMP/$g.dump") bytes"
  else record "$g export nquads = dump" 1 "the outputs differ"; fi
done

echo "=== --out writes the file; standard output is the same text"
"$BIN/l4sbm11" export "$TMP/d1" --format turtle >"$TMP/d1.stdout.ttl" 2>/dev/null
if [ -s "$TMP/d1.stdout.ttl" ] && cmp -s "$TMP/d1.stdout.ttl" "$TMP/d1-turtle.ttl"; then record "--out = standard output" 0 "$(wc -c <"$TMP/d1.stdout.ttl") bytes"
else record "--out = standard output" 1 "the file and the standard output differ"; fi
if [ -z "$(ls "$TMP" | grep '\.tmp-')" ]; then record "no temporary file is left" 0 "none"
else record "no temporary file is left" 1 "$(ls "$TMP" | grep '\.tmp-' | tr '\n' ' ')"; fi

echo "=== --prefix"
rc=0
"$BIN/l4sbm11" export "$TMP/d1" --format turtle --prefix ex=http://example.org/ --prefix xsd=http://www.w3.org/2001/XMLSchema# \
  --out "$TMP/d1-prefixed.ttl" >/dev/null 2>"$TMP/p.err" || rc=$?
if [ "$rc" = 0 ] && grep -q '^@prefix ex: <http://example.org/> \.$' "$TMP/d1-prefixed.ttl" && grep -q '^ex:s1 ex:age 42 ;$' "$TMP/d1-prefixed.ttl" \
    && [ "$(wc -c <"$TMP/d1-prefixed.ttl")" -lt "$(wc -c <"$TMP/d1-turtle.ttl")" ] && pack d1-prefixed "$TMP/d1-prefixed.ttl"; then
  out="$(same_data d1 d1-prefixed)"; record "--prefix shortens and reads back" $? "$out"
else record "--prefix shortens and reads back" 1 "exit $rc: $(head -1 "$TMP/p.err")"; fi
rc=0
"$BIN/l4sbm11" export "$TMP/d2" --format trig --prefix ex=http://example.org/ --out "$TMP/d2-prefixed.trig" >/dev/null 2>"$TMP/p.err" || rc=$?
if [ "$rc" = 0 ] && grep -q '^GRAPH ex:g1 {$' "$TMP/d2-prefixed.trig" && pack d2-prefixed "$TMP/d2-prefixed.trig"; then
  out="$(same_data d2 d2-prefixed)"; record "--prefix in TriG, graph names too" $? "$out"
else record "--prefix in TriG, graph names too" 1 "exit $rc: $(head -1 "$TMP/p.err")"; fi

echo "=== usage errors"
rc=0; "$BIN/l4sbm11" export "$TMP/d1" >/dev/null 2>&1 || rc=$?
if [ "$rc" = 2 ]; then record "no --format" 0 "exit 2"; else record "no --format" 1 "exit $rc"; fi
rc=0; "$BIN/l4sbm11" export "$TMP/d1" --format nonsense >/dev/null 2>"$TMP/u.err" || rc=$?
if [ "$rc" = 2 ] && grep -q "unknown format 'nonsense'" "$TMP/u.err"; then record "--format nonsense" 0 "refused by name"
else record "--format nonsense" 1 "exit $rc: $(head -1 "$TMP/u.err")"; fi
rc=0; "$BIN/l4sbm11" export "$TMP/nowhere" --format nquads >/dev/null 2>&1 || rc=$?
if [ "$rc" = 1 ]; then record "no such generation" 0 "exit 1"; else record "no such generation" 1 "exit $rc"; fi

echo "=== an empty generation exports in every syntax to a document that packs to an empty generation"
: >"$TMP/empty.nt"
pack empty "$TMP/empty.nt" || record "pack empty" 1 "$(tail -1 "$TMP/empty.log")"
for fmt in nquads ntriples turtle trig rdfxml jsonld; do
  ext="$(ext_of "$fmt")"; rc=0
  "$BIN/l4sbm11" export "$TMP/empty" --format "$fmt" --out "$TMP/empty-$fmt.$ext" >/dev/null 2>"$TMP/e.err" || rc=$?
  if [ "$rc" -ne 0 ]; then record "empty export $fmt" 1 "exit $rc: $(head -1 "$TMP/e.err")"; continue; fi
  if pack "empty-$fmt" "$TMP/empty-$fmt.$ext" && out="$(same_data empty "empty-$fmt")" && "$BIN/l4sbm11" verify "$TMP/empty-$fmt" >/dev/null 2>&1; then
    record "empty export $fmt" 0 "$(wc -c <"$TMP/empty-$fmt.$ext") bytes; $out"
  else record "empty export $fmt" 1 "the export does not pack to an empty generation: $(tail -1 "$TMP/empty-$fmt.log" | cut -c1-120)"; fi
done

echo "=== a generated dataset of about 1 MB: many 64 KiB writes, graphs interleaved in SPO order"
mkdir -p "$TMP/multi"
if python3 -I "$FX/gen_multi.py" "$TMP/multi" 1500; then
  pack multi-nt "$TMP/multi/multi.nt" || record "pack multi.nt" 1 "$(tail -1 "$TMP/multi-nt.log")"
  pack multi-nq "$TMP/multi/multi.nq" || record "pack multi.nq" 1 "$(tail -1 "$TMP/multi-nq.log")"
  for fmt in nquads trig; do
    out="$(roundtrip multi-nq "multi-nq-$fmt" "$fmt")"; record "multi (named graphs) export $fmt" $? "$out"
  done
  for fmt in ntriples turtle rdfxml; do
    out="$(roundtrip multi-nt "multi-nt-$fmt" "$fmt")"; record "multi (default graph) export $fmt" $? "$out"
  done
  blocks="$(grep -c '^GRAPH \|^{$' "$TMP/multi-nq-trig.trig")"
  graphs=5
  if [ "$blocks" -gt "$graphs" ]; then record "TriG blocks follow the graph changes" 0 "$blocks blocks for $graphs graphs (the SPO order interleaves them)"
  else record "TriG blocks follow the graph changes" 1 "$blocks blocks for $graphs graphs"; fi
else record "multi generate" 1 "gen_multi.py failed"; fi

echo
echo "export round trip: $PASS pass, $FAIL fail, $XFAIL expected-fail (out of $((PASS + FAIL + XFAIL)))"
[ "$FAIL" -eq 0 ]
