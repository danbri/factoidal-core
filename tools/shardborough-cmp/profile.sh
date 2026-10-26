#!/usr/bin/env bash
# Sample one oracle query on one layout with perf (cpu-clock, DWARF call
# graphs) and print the inclusive share of the functions that mark each
# phase: block fetch and verification, decode, in-memory dataset and index
# build, evaluation, output.
#
# Usage: tools/shardborough-cmp/profile.sh LAYOUT QUERY-NAME [WORK-DIR]
#   LAYOUT ibk3 | ibk5; QUERY-NAME e.g. q07-join-three
# Env: PERF (default: the first /usr/lib/linux-tools/*/perf), FREQ (199),
#      REPORT_ONLY=1 (reuse an existing .data file).
# Output: WORK/perf/LAYOUT-QUERY.data and .children.txt (perf report
# --children), and the phase table on stdout.
# Design record: docs/designissues/2026-10-11-shardborough-vs-qlever.md
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
B="$ROOT/formal/lean4/.lake/build/bin"
LAYOUT="$1"; NAME="$2"; WORK="${3:-/home/user/qlvr-work/shardborough-cmp}"
PERF="${PERF:-$(ls /usr/lib/linux-tools/*/perf 2>/dev/null | head -n 1)}"
FREQ="${FREQ:-199}"
[ -x "$PERF" ] || { echo "profile.sh: no perf (apt-get install linux-tools-<version>-generic)"; exit 2; }
case "$LAYOUT" in
  ibk3) TOOL="$B/l4block-id-v3-query" ;;
  ibk5) TOOL="$B/l4block-quad-query" ;;
  *) echo "profile.sh: unknown layout $LAYOUT"; exit 2 ;;
esac
OUT="$WORK/perf"; mkdir -p "$OUT"
DATA="$OUT/$LAYOUT-$NAME.data"
QTEXT="$(cat "$ROOT/tests/qlvr/queries/$NAME.rq")"
REC_RC=0
if [ "${REPORT_ONLY:-0}" = 1 ] && [ -s "$DATA" ]; then :; else
"$PERF" record -q -F "$FREQ" --call-graph dwarf,16384 -o "$DATA" -- \
  "$TOOL" "$WORK/col-$LAYOUT" --json --query "$QTEXT" > /dev/null 2> "$OUT/$LAYOUT-$NAME.err" || REC_RC=$?
fi
[ "$REC_RC" -eq 0 ] || { echo "profile.sh: perf record rc=$REC_RC"; cat "$OUT/$LAYOUT-$NAME.err"; exit 1; }
"$PERF" report -i "$DATA" --children --no-demangle -g none --sort symbol --stdio 2>/dev/null \
  > "$OUT/$LAYOUT-$NAME.children.txt"
python3 - "$OUT/$LAYOUT-$NAME.children.txt" <<'PY'
import re, sys
rows = []
for line in open(sys.argv[1], errors="replace"):
    m = re.match(r"\s*([\d.]+)%\s+([\d.]+)%\s+\[\.\]\s+(\S+)", line)
    if m:
        rows.append((float(m.group(1)), float(m.group(2)), m.group(3)))
# Phase markers: substrings of Lean-compiled C symbol names. The share of a
# phase is the largest inclusive share among its markers (markers of one
# phase nest), so the phases may overlap where one calls another; the table
# says which marker gave each number. Shares are of all samples. A DWARF
# unwind of 16 KiB can stop short of main on deep stacks, so the query
# function's own share understates; the phase markers are leaf-near.
phases = [
  ("read and materialise the selected blocks (all of the next three nest here)", ["IndexedBlockV3Materialize_materializeEntries", "QuadQuery_readEntriesV5", "QuadQuery_readEntriesV4"]),
  ("  fetch and verify (pread, SHA-256, Merkle)", ["PosixRangeIO_readVerifiedRangeCached", "QuadQuery_artifactAdmitted"]),
  ("  decode the dictionary (PTD pages, term codec)", ["PTD_decodePagesGo", "PTD_decodePageArray", "PTD_decode_x3f"]),
  ("  of which List.length inside the term parser", ["l_List_lengthTR"]),
  ("build the in-memory dataset and hash index", ["StoreDataset_indexedGraphBackend", "StoreDataset_indexedDatasetBackend", "QuadDataset_datasetOfQuads"]),
  ("evaluate", ["StoreDataset_evalSelectBackendOnGraph", "StoreDataset_evalSelectBackendDataset", "StoreDataset_runSelectQueryBackendDataset", "SPARQL_Query_evalSelect"]),
  ("write SPARQL JSON", ["QueryResult_toSrjFast"]),
]
print("phase\tinclusive %\tmarker symbol")
for label, keys in phases:
    best = (0.0, "-")
    for ch, self_, sym in rows:
        if any(k in sym for k in keys) and ch > best[0]:
            best = (ch, sym)
    print(f"{label}\t{best[0]:.1f}\t{best[1][:110]}")
print("top self-time symbols:")
for ch, self_, sym in sorted(rows, key=lambda r: -r[1])[:12]:
    print(f"  self {self_:5.1f}%  children {ch:5.1f}%  {sym[:110]}")
PY
