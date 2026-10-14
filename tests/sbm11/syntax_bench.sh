#!/usr/bin/env bash
#
# tests/sbm11/syntax_bench.sh -- pack time and peak memory of `l4sbm11-pack` for
# each source syntax (https://github.com/danbri/factoidal/issues/837).
#
# One generated dataset (tests/sbm11/syntax/gen_multi.py) is written in each
# syntax and packed with `l4sbm11-pack`. The N-Triples and N-Quads text comes
# from the generator. Turtle, TriG, RDF/XML and JSON-LD come from the Lean
# serialisers (`l4source-convert`), and the generator's own Turtle and TriG are
# packed as well. For each pack the script prints the wall time, the peak
# resident set size (tests/trig-pack/peak_rss.py, a small wrapper process: the
# harness `wait4` reads the size of the parent), the rates, and whether the
# generation has the same data files as the reference pack (N-Triples for the
# default-graph syntaxes, N-Quads for the named-graph syntaxes).
#
# Two datasets:
#   big    --subjects N        (default 110,000: about 100 MB of N-Quads text)
#          N-Triples, N-Quads, Turtle, TriG.
#   small  --small-subjects M  (default 11,000: about 10 MB of N-Quads text)
#          all six syntaxes. The Lean RDF/XML and JSON-LD writers take time
#          quadratic in the dataset (22 s and 44 s for the 8.3 MB of N-Triples
#          text of the small set, 2026-10-14;
#          https://github.com/danbri/factoidal/issues/845 and
#          https://github.com/danbri/factoidal/issues/712), so those two
#          syntaxes stay small.
#
# Not measured here: a comparison with another store. `oxigraph load` is timed
# for the N-Quads file only when `oxigraph` is on PATH (this command is not
# tested; `oxigraph` was not on PATH on 2026-10-14, so the record has no
# comparison row).
#
# Usage:  tests/sbm11/syntax_bench.sh [--subjects N] [--small-subjects M]
#                                     [--workers K] [--dir DIR] [--keep]
#                                     [--only big|small]
# Env:    L4_BIN_DIR   directory of l4sbm11-pack and l4source-convert
#                      (default formal/lean4/.lake/build/bin)
# Exit:   0 when every pack succeeded and every generation equals its
#         reference, 1 otherwise, 2 when a binary is missing.
# The times are wall times: run it with no other build or test running.
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${L4_BIN_DIR:-$ROOT/formal/lean4/.lake/build/bin}"
SUBJECTS=110000
SMALL=11000
WORKERS=4
KEEP=0
DIR=""
ONLY=""
while [ $# -gt 0 ]; do
  case "$1" in
    --subjects) SUBJECTS="$2"; shift 2 ;;
    --small-subjects) SMALL="$2"; shift 2 ;;
    --workers) WORKERS="$2"; shift 2 ;;
    --dir) DIR="$2"; shift 2 ;;
    --keep) KEEP=1; shift ;;
    --only) ONLY="$2"; shift 2 ;;
    -h|--help) sed -n '2,/^set -uo/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'; exit 0 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
for need in "$BIN/l4sbm11-pack" "$BIN/l4source-convert" \
            "$HERE/syntax/gen_multi.py" "$ROOT/tests/trig-pack/peak_rss.py"; do
  [ -e "$need" ] || { echo "missing: $need" >&2; exit 2; }
done
if [ -z "$DIR" ]; then DIR="$(mktemp -d "${TMPDIR:-/tmp}/sbm11-bench.XXXXXX")"; else mkdir -p "$DIR"; fi
cleanup() { if [ "$KEEP" = 0 ]; then rm -rf "$DIR"; else echo "kept: $DIR"; fi; }
trap cleanup EXIT
RESULTS="$DIR/results.tsv"
: > "$RESULTS"
FAILS=0

now_ms() { echo $(( $(date +%s%N) / 1000000 )); }
secs() { awk -v a="$1" -v b="$2" 'BEGIN { printf "%.1f", (b - a) / 1000 }'; }

echo "load average at start: $(cut -d' ' -f1-3 /proc/loadavg); $(nproc) CPUs; workers requested: $WORKERS"

# convert SET FROM TO SRC OUT: write SRC (read as FROM) in syntax TO with the
# Lean serialiser.
convert() {
  local set="$1" from="$2" to="$3" src="$4" out="$5" t0 t1
  t0=$(now_ms)
  if ! "$BIN/l4source-convert" "$src" "$out" --from "$from" --to "$to" >"$out.log" 2>&1; then
    echo "convert failed: $src -> $out: $(tail -1 "$out.log")" >&2
    FAILS=$((FAILS + 1)); rm -f "$out"; return 1
  fi
  t1=$(now_ms)
  printf 'write  %-5s %-11s %12d bytes  %7s s\n' "$set" "$(basename "$out")" "$(stat -c %s "$out")" "$(secs "$t0" "$t1")"
}

# gen_digest GEN: one digest of every file of a generation except the manifest
# (the manifest holds the length and the digest of the source text).
gen_digest() { (cd "$1" && find . -type f ! -name manifest.sbm11 | sort | xargs sha256sum | sha256sum | cut -d' ' -f1); }

# measure SET LABEL FILE CLASS: pack FILE and append one line to RESULTS. CLASS
# is "default" or "named"; the first pack of a class in a set is its reference.
measure() {
  local set="$1" label="$2" file="$3" class="$4" gen="$DIR/gen-$1-$2" rc=0
  local same dg line first phase refd="$DIR/ref-$1-$4"
  [ -e "$file" ] || { echo "no file for $label" >&2; FAILS=$((FAILS + 1)); return; }
  rm -rf "$gen"
  timeout 3600 python3 -I "$ROOT/tests/trig-pack/peak_rss.py" "$BIN/l4sbm11-pack" "$file" "$gen" \
    --workers "$WORKERS" >"$gen.out" 2>"$gen.err" || rc=$?
  if [ "$rc" != 0 ]; then
    echo "pack failed: $label: exit $rc: $(tail -1 "$gen.err")" >&2
    FAILS=$((FAILS + 1)); rm -rf "$gen" "$gen.out" "$gen.err"; return
  fi
  line="$(grep -E '^peak-rss-bytes=' "$gen.out" | tail -1)"
  first="$(grep -E '^sbm11-pack: source=' "$gen.err" | head -1)"
  phase="$(grep -E 'phase1-ms=' "$gen.err" | tail -1)"
  dg="$(gen_digest "$gen")"
  if [ ! -e "$refd" ]; then echo "$dg" > "$refd"; same=reference
  elif [ "$(cat "$refd")" = "$dg" ]; then same=same
  else same=DIFFERENT; FAILS=$((FAILS + 1)); fi
  python3 -I - "$set" "$label" "$file" "$same" "$line" "$first" "$phase" >> "$RESULTS" <<'PY'
import os, re, sys
set_, label, file, same, line, first, phase = sys.argv[1:8]
def field(text, key, cast=float):
    m = re.search(r'(?:^|\s)' + re.escape(key) + r'=([0-9.]+)', text)
    return cast(m.group(1)) if m else float('nan')
print("\t".join(str(x) for x in (
    set_, label, os.path.getsize(file), field(first, 'quads', int), field(first, 'workers', int),
    field(line, 'wall-seconds'), field(line, 'peak-rss-bytes'), field(phase, 'phase1-ms'),
    field(phase, 'total-ms'), same)))
PY
  rm -rf "$gen" "$gen.out" "$gen.err"
}

if [ "$ONLY" != small ]; then
  echo "=== big: $SUBJECTS subjects"
  B="$DIR/big"; mkdir -p "$B"
  python3 "$HERE/syntax/gen_multi.py" "$B" "$SUBJECTS"
  convert big nquads turtle "$B/multi.nt" "$B/lean.ttl"
  convert big nquads trig "$B/multi.nq" "$B/lean.trig"
  measure big ntriples "$B/multi.nt" default
  measure big turtle-generator "$B/multi.ttl" default
  measure big turtle-lean "$B/lean.ttl" default
  measure big nquads "$B/multi.nq" named
  measure big trig-generator "$B/multi.trig" named
  measure big trig-lean "$B/lean.trig" named
  if command -v oxigraph >/dev/null 2>&1; then
    t0=$(now_ms)
    oxigraph load --location "$DIR/oxigraph-store" --file "$B/multi.nq" >"$DIR/oxigraph.log" 2>&1
    echo "oxigraph load of multi.nq: exit $?, $(secs "$t0" "$(now_ms)") s"
  else
    echo "oxigraph: not on PATH; no comparison row"
  fi
  rm -rf "$B"
fi
if [ "$ONLY" != big ]; then
  echo "=== small: $SMALL subjects"
  S="$DIR/small"; mkdir -p "$S"
  python3 "$HERE/syntax/gen_multi.py" "$S" "$SMALL"
  convert small nquads turtle "$S/multi.nt" "$S/lean.ttl"
  convert small nquads trig "$S/multi.nq" "$S/lean.trig"
  convert small nquads rdfxml "$S/multi.nt" "$S/lean.rdf"
  convert small nquads jsonld "$S/multi.nt" "$S/lean.jsonld"
  measure small ntriples "$S/multi.nt" default
  measure small turtle-generator "$S/multi.ttl" default
  measure small turtle-lean "$S/lean.ttl" default
  measure small rdfxml-lean "$S/lean.rdf" default
  measure small jsonld-lean "$S/lean.jsonld" default
  measure small nquads "$S/multi.nq" named
  measure small trig-generator "$S/multi.trig" named
  measure small trig-lean "$S/lean.trig" named
  rm -rf "$S"
fi

python3 -I - "$RESULTS" <<'PY'
import sys
rows = [l.rstrip("\n").split("\t") for l in open(sys.argv[1]) if l.strip()]
if not rows:
    print("no results"); sys.exit(0)
hdr = ("set", "syntax (writer)", "source MB", "kquads", "workers", "wall s", "MB/s", "kquads/s",
       "peak RSS MB", "RSS B/src B", "phase1 s", "phase1 MB/s", "generation")
out = [hdr]
by = {}
for set_, label, size, quads, workers, wall, rss, p1, total, same in rows:
    size, quads, workers, wall, rss, p1 = int(size), int(quads), int(float(workers)), float(wall), float(rss), float(p1)
    by[(set_, label)] = (size, quads, workers, wall, rss, p1)
    out.append((set_, label, f"{size / 1e6:.1f}", f"{quads / 1e3:.0f}", str(workers), f"{wall:.1f}",
                f"{size / 1e6 / wall:.1f}", f"{quads / 1e3 / wall:.0f}", f"{rss / 1e6:.0f}",
                f"{rss / size:.2f}", f"{p1 / 1e3:.2f}", f"{size / 1e6 / (p1 / 1e3):.1f}", same))
w = [max(len(r[i]) for r in out) for i in range(len(hdr))]
for r in out:
    print("  ".join(c.ljust(w[i]) if i < 2 or i == len(hdr) - 1 else c.rjust(w[i]) for i, c in enumerate(r)))
print()
print("phase 1 time per source byte, against N-Quads of the same set (the parallel-split")
print("issue applies to a syntax read by one worker when this is above 2.0):")
for set_ in ("big", "small"):
    ref = by.get((set_, "nquads"))
    if not ref:
        continue
    for (s, label), v in by.items():
        if s == set_ and label != "nquads":
            print(f"  {set_:5s} {label:17s} {(v[5] / v[0]) / (ref[5] / ref[0]):6.1f}x per byte, "
                  f"{(v[5] / v[1]) / (ref[5] / ref[1]):5.1f}x per quad")
PY
echo
if [ "$FAILS" != 0 ]; then echo "syntax bench: $FAILS failure(s)"; exit 1; fi
echo "syntax bench: every pack succeeded and every generation equals its reference"
