#!/usr/bin/env bash
# The same 21 oracle queries through `l4qlvr query --explain` on QLever's own
# index: compressed column bytes read, blocks read, total time and peak RSS
# of the Lean reader on QLever's layout. This is the "same Lean, QLever's
# layout" column of the design record
# docs/designissues/2026-10-11-shardborough-vs-qlever.md.
#
# Usage: tools/shardborough-cmp/qlvr_bytes.sh [INDEXDIR] [OUT-TSV]
# Needs: formal/lean4/.lake/build/bin/l4qlvr (lake build l4qlvr) and the side
# index (l4qlvr side-index INDEXDIR); see skills/qlvr/SKILL.md.
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
B="$ROOT/formal/lean4/.lake/build/bin"
IDX="${1:-/home/user/qlvr-work/instance}"
OUT="${2:-/home/user/qlvr-work/shardborough-cmp/measure/qlvr-explain.tsv}"
printf 'query\tframe_bytes\tblocks_read\ttotal_ms\tpeak_rss_kb\n' > "$OUT"
for q in "$ROOT"/tests/qlvr/queries/q*.rq; do
  name="$(basename "$q" .rq)"
  RC=0
  "$B/l4qlvr" query "$IDX" --file "$q" --explain > /dev/null 2> "$OUT.$name.err" || RC=$?
  python3 - "$name" "$OUT.$name.err" "$RC" >> "$OUT" <<'PY'
import re, sys
name, err, rc = sys.argv[1:4]
t = open(err, errors="replace").read()
fb = sum(int(x) for x in re.findall(r"frames \d+, (\d+) bytes", t))
bl = sum(int(x) for x in re.findall(r"blocks (\d+) of \d+", t))
tot = re.search(r"total (\d+) ms", t)
rss = re.search(r"VmHWM\): (\d+) kB", t)
print("\t".join([name, str(fb), str(bl), tot.group(1) if tot else "-",
                 rss.group(1) if rss else "-"]) + ("" if rc == "0" else f"\trc={rc}"))
PY
done
cat "$OUT"
