#!/usr/bin/env bash
# tools/strict-parse-differential.sh OLD NEW [DIR...]
#
# Differential check of the strict `l4factoidal parse` between two binaries
# (https://github.com/danbri/factoidal/issues/813): every .nt, .nq and .ttl
# file under DIR (default: the W3C RDF 1.1 and 1.2 suites, RDF/XML excluded)
# is parsed by OLD and NEW, as `parse FILE --format F --out nquads` and as
# `parse FILE --format F` (the count), each with and without `--base`, in the
# RDF 1.1 mode and (files of the RDF 1.2 suites) in the RDF 1.2 mode.
#
# NEW runs once per chunk size in STRICT_DIFF_CHUNKS (default "0 7 1"; 0 is
# the built-in 65,536 bytes, the others set L4_STRICT_CHUNK_BYTES, so with 1
# and 7 every line and statement boundary of the small W3C files falls across
# a chunk boundary). OLD runs once.
#
# A case agrees when the exit status and the standard error are the same and,
# when OLD exits 0, the standard output is the same byte for byte. When OLD
# exits non-zero, NEW's standard output may hold the lines it wrote before
# the error (the streamed parse writes each chunk before it reads the next)
# and is not compared.
#
# Then (unless STRICT_DIFF_GENERATED=0) generated files of several chunks
# each, to put errors and directives past the first chunks: an N-Quads file
# of 150,000 lines over 50 graphs (IRI and blank-node labels) with repeated
# quads, language tags in two cases and comment and CR LF lines, and the same
# with a malformed line at line 120,000; 20,000 paragraphs of gene.ttl with a
# malformed statement in the middle, with a `PREFIX` directive whose IRI is
# on the next line in the middle (the scanner walk refuses it after lines are
# written; `parseTurtle` accepts it) and at the start; 100,000 N-Triples
# lines with an unterminated string in the middle; and lines longer than a chunk
# (https://github.com/danbri/factoidal/issues/869): a literal of 150,000 characters
# between short lines, one of 100,000 two-byte characters (200,000 bytes, so a chunk
# boundary falls between bytes of a line), an error on the line after a long line
# (its offset counts the long line), an unterminated string inside a long line, a long
# last line with no line break, in N-Triples and in N-Quads; escapes, labels that end in a
# dot and RDF 1.2 triple terms and language tags in long lines (issue 949).
#
# N-Triples and N-Quads files are also read with `--lenient --out nquads` (unless
# STRICT_DIFF_LENIENT=0), with the chunk sizes set by L4_LENIENT_CHUNK_BYTES; the standard
# output is compared also when the exit status is 1 (diagnostics).
#
# Prints one DIFF line per disagreement and a summary; exit 0 when every case
# agrees, 1 otherwise, 2 on a setup error.
set -uo pipefail
OLD="${1:?usage: strict-parse-differential.sh OLD NEW [DIR...]}"
NEW="${2:?usage: strict-parse-differential.sh OLD NEW [DIR...]}"
shift 2
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
if [ "$#" -eq 0 ]; then
  set -- "$ROOT/third_party/testing/w3c/rdf/rdf11" "$ROOT/third_party/testing/w3c/rdf/rdf12"
fi
for b in "$OLD" "$NEW"; do
  [ -x "$b" ] || { echo "not executable: $b" >&2; exit 2; }
done
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT
cases=0; agree=0; differ=0; ok_cases=0; err_cases=0
run_case() { # file format out(nquads|count) base [lenient]
  local f="$1" fmt="$2" out="$3" base="$4" len="${5:-}"
  local args=(parse "$f" --format "$fmt")
  [ "$out" = nquads ] && args+=(--out nquads)
  [ -n "$base" ] && args+=(--base "$base")
  [ -n "$len" ] && args+=(--lenient)
  local var=L4_STRICT_CHUNK_BYTES
  [ -n "$len" ] && var=L4_LENIENT_CHUNK_BYTES
  local orc=0 nrc chunk
  timeout 60 "$OLD" "${args[@]}" > "$TMP/o.out" 2> "$TMP/o.err" || orc=$?
  for chunk in ${STRICT_DIFF_CHUNKS:-0 7 1}; do
    nrc=0
    if [ "$chunk" = 0 ]; then
      timeout 60 "$NEW" "${args[@]}" > "$TMP/n.out" 2> "$TMP/n.err" || nrc=$?
    else
      env "$var=$chunk" timeout 60 "$NEW" "${args[@]}" > "$TMP/n.out" 2> "$TMP/n.err" || nrc=$?
    fi
    cases=$((cases + 1))
    local why=""
    [ "$orc" = "$nrc" ] || why="exit $orc vs $nrc"
    cmp -s "$TMP/o.err" "$TMP/n.err" || why="$why stderr"
    # The lenient walk writes every statement it keeps, also when it exits 1.
    if [ "$orc" = 0 ] || [ -n "$len" ]; then
      ok_cases=$((ok_cases + 1))
      cmp -s "$TMP/o.out" "$TMP/n.out" || why="$why stdout"
    else
      err_cases=$((err_cases + 1))
    fi
    if [ -z "$why" ]; then agree=$((agree + 1)); else
      differ=$((differ + 1)); echo "DIFF ($why, chunk $chunk): ${args[*]}"
    fi
  done
}
while IFS= read -r f; do
  case "$f" in
    */rdf-xml/*) continue ;;
    *.nt) fmts="ntriples" ;;
    *.nq) fmts="nquads" ;;
    *.ttl) fmts="turtle" ;;
    *) continue ;;
  esac
  case "$f" in
    */rdf12/*) case "$fmts" in
        ntriples) fmts="ntriples ntriples12" ;;
        nquads) fmts="nquads nquads12" ;;
        turtle) fmts="turtle turtle12" ;;
      esac ;;
  esac
  for fmt in $fmts; do
    for out in nquads count; do
      run_case "$f" "$fmt" "$out" ""
      run_case "$f" "$fmt" "$out" "http://example.org/base/dir/doc"
    done
    # The lenient walk of N-Triples and N-Quads (issue 949), unless STRICT_DIFF_LENIENT=0.
    case "$fmt" in
      ntriples*|nquads*) [ "${STRICT_DIFF_LENIENT:-1}" != 0 ] && run_case "$f" "$fmt" nquads "" lenient ;;
    esac
  done
done < <(find -L "$@" -type f \( -name '*.nt' -o -name '*.nq' -o -name '*.ttl' \) | sort)
if [ "${STRICT_DIFF_GENERATED:-1}" != 0 ]; then
  GEN="$TMP/gen"
  mkdir -p "$GEN"
  python3 - "$ROOT" "$GEN" <<'PY'
import random, sys
from pathlib import Path
root, gen = Path(sys.argv[1]), Path(sys.argv[2])
sys.path.insert(0, str(root / "tools"))
import bench_lean_vs_fstar as bl
random.seed(7)
lines = []
for i in range(150000):
    g = i % 50
    o = random.choice([f"<http://e/o{i % 700}>",
                       f'"v{i % 500}"@{random.choice(["en", "EN", "fr"])}',
                       f"_:b{i % 300}",
                       f'"{i % 90}"^^<http://www.w3.org/2001/XMLSchema#integer>'])
    gl = "" if g == 0 else (f" <http://e/g{g}>" if g % 7 else f" _:gb{g}")
    lines.append(f"<http://e/s{i % 9000}> <http://e/p{i % 13}> {o}{gl} .\n")
    if i % 10 == 0:
        lines.append(lines[-1])
    if i % 1000 == 0:
        lines.append("# comment line\n\r\n")
(gen / "big.nq").write_text("".join(lines))
(gen / "bad.nq").write_text("".join(lines[:120000] + ["<http://e/a> <http://e/p> .\n"] + lines[120000:]))
t = Path(bl.gene_slice(20000)).read_text()
k = t.index("\n\n", len(t) // 2)
(gen / "bad.ttl").write_text(t[:k] + "\n\nwd:Q1 wdt:P2 .\n" + t[k:])
d = "PREFIX zz:\n  <http://zz.example/>\nzz:a zz:b zz:c .\n"
(gen / "prefix-mid.ttl").write_text(t[:k] + "\n\n" + d + t[k:])
(gen / "prefix-start.ttl").write_text(d + t)
n = Path(bl.gen_nt(100000)).read_text()
m = n.index("\n", len(n) // 2) + 1
(gen / "bad.nt").write_text(n[:m] + '<http://e/a> <http://e/p> "unterminated .\n' + n[m:])
# Lines longer than a chunk (issue 869).
big = '"' + "a" * 150000 + '"'
wide = '"' + "\u00e9" * 100000 + '"'
short = '<http://e/s> <http://e/p> <http://e/o> .\n'
bad = '<http://e/s> <http://e/p> .\n'
(gen / "long.nt").write_text(short + f"<http://e/a> <http://e/p> {big} .\n" + short + f"<http://e/a> <http://e/p> {wide} .\n" + short)
(gen / "long-bad.nt").write_text(short + f"<http://e/a> <http://e/p> {big} .\n" + bad + short)
(gen / "long-open.nt").write_text(short + '<http://e/a> <http://e/p> "' + "a" * 150000 + " .\n" + short)
(gen / "long-last.nt").write_text(short + f"<http://e/a> <http://e/p> {wide} .")
(gen / "long-crlf.nt").write_text(short.replace("\n", "\r\n") + f"<http://e/a> <http://e/p> {big} .\r\n" + short.replace("\n", "\r\n"))
(gen / "long.nq").write_text(short + f"<http://e/a> <http://e/p> {big} <http://e/g> .\n" + short + f"<http://e/a> <http://e/p> {wide} _:g .\n")
(gen / "long-bad.nq").write_text(f"<http://e/a> <http://e/p> {wide} <http://e/g> .\n" + bad + short)
# Escapes, a label that ends in a dot, and the RDF 1.2 line grammar in lines longer than a
# chunk (issue 949). Files named *12.* are also read in the RDF 1.2 mode.
esc = '"' + "a" * 150000 + '\\u0041\\U0001F600\\t"'
(gen / "long-esc.nt").write_text(short + f"<http://e/a> <http://e/p> {esc} .\n" + short + '<http://e/a> <http://e/p> "' + "b" * 150000 + '\\u12" .\n')
(gen / "long-dot.nt").write_text(short + "<http://e/a> <http://e/p> _:" + "c" * 150000 + ".\n_:" + "d" * 150000 + ". <http://e/p> _:x.y.\n" + short)
tt = "<<( <http://e/a> <http://e/b> " * 30 + '"' + "e" * 150000 + '"@en--rtl' + " )>>" * 30
(gen / "long12.nt").write_text(short + f"<http://e/a> <http://e/p> {tt} .\n" + f'<http://e/a> <http://e/p> {big} @en .\n' + f'<http://e/a> <http://e/p> {big}  ^^  <http://e/t> .\n' + f"<http://e/a> <http://e/p> {tt} )>> .\n" + short)
(gen / "long12.nq").write_text(short + f"<http://e/a> <http://e/p> {tt} <http://e/g> .\n" + f'<http://e/a> <http://e/p> {big}@en--ltr _:g .\n' + f"<http://e/a> <http://e/p> << <http://e/a> >> .\n" + short)
PY
  for f in "$GEN"/*.nq; do for out in nquads count; do run_case "$f" nquads "$out" ""; done; done
  for f in "$GEN"/*.ttl; do for out in nquads count; do run_case "$f" turtle "$out" ""; done; done
  for f in "$GEN"/*.nt; do for out in nquads count; do run_case "$f" ntriples "$out" ""; done; done
  for f in "$GEN"/*12.nt; do for out in nquads count; do run_case "$f" ntriples12 "$out" ""; done; done
  for f in "$GEN"/*12.nq; do for out in nquads count; do run_case "$f" nquads12 "$out" ""; done; done
  if [ "${STRICT_DIFF_LENIENT:-1}" != 0 ]; then
    for f in "$GEN"/long*.nt; do run_case "$f" ntriples nquads "" lenient; done
    for f in "$GEN"/long*.nq; do run_case "$f" nquads nquads "" lenient; done
    for f in "$GEN"/*12.nt; do run_case "$f" ntriples12 nquads "" lenient; done
    for f in "$GEN"/*12.nq; do run_case "$f" nquads12 nquads "" lenient; done
  fi
fi
echo "strict-parse-differential: $agree agree, $differ differ (out of $cases cases; old exit 0 in $ok_cases, non-zero in $err_cases)"
[ "$differ" -eq 0 ]
