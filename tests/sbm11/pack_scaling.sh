#!/usr/bin/env bash
# SBM11 stage 3 pack scaling (https://github.com/danbri/factoidal/issues/789).
#
# Packs SOURCE (n) and a doubled source (2n: SOURCE followed by a copy whose
# IRIs carry a suffix, datatype IRIs unchanged, as tests/sbm11/dict_scaling.sh
# builds it) with l4sbm11-pack and checks the stage 3 targets: pack under
# 120 s for SOURCE, peak RSS under 300 MB, and peak RSS of 2n within 10 % of n.
#
# Usage: tests/sbm11/pack_scaling.sh
# Env:   SBM11_SOURCE (default /home/user/qlvr-work/instance/olympics.nt)
#        SBM11_WORK   (default /home/user/qlvr-work/sbm11/pack-scaling; removed at the end)
# Exit:  0 all assertions hold, 1 an assertion fails, 2 setup error.
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SRC="${SBM11_SOURCE:-/home/user/qlvr-work/instance/olympics.nt}"
WORK="${SBM11_WORK:-/home/user/qlvr-work/sbm11/pack-scaling}"
BIN="$HERE/../../formal/lean4/.lake/build/bin/l4sbm11-pack"
[ -x "$BIN" ] || { echo "missing $BIN (lake build l4sbm11-pack)"; exit 2; }
[ -f "$SRC" ] || { echo "missing $SRC"; exit 2; }
mkdir -p "$WORK" || exit 2
FAIL=0
check() { if [ "$2" = 1 ]; then echo "ok   $1"; else echo "FAIL $1"; FAIL=1; fi; }

run_one() { # run_one NAME SOURCE -> sets RSS_KB, MS, BYTES
  rm -rf "$WORK/$1"
  local log
  log="$("$BIN" "$2" "$WORK/$1" 2>&1)" || { echo "pack $1 failed: $log"; exit 1; }
  RSS_KB="$(printf '%s' "$log" | grep -o 'peak-rss=[0-9]*' | cut -d= -f2)"
  MS="$(printf '%s' "$log" | grep -o 'total-ms=[0-9]*' | cut -d= -f2)"
  BYTES="$(printf '%s' "$log" | grep -o 'total-on-disk=[0-9]*' | cut -d= -f2)"
  echo "$1: total-ms=$MS peak-rss=$RSS_KB kB on-disk=$BYTES"
  rm -rf "$WORK/$1"
}

run_one n "$SRC"; RSS_N="$RSS_KB"; MS_N="$MS"
python3 - "$SRC" "$WORK/doubled.nt" <<'PY'
import re, sys
src, dst = sys.argv[1], sys.argv[2]
iri = re.compile(r'(?<!\^\^)<([^>]*)>')
with open(dst, "w", encoding="utf-8") as out:
    with open(src, encoding="utf-8") as fh:
        for line in fh:
            out.write(line)
    with open(src, encoding="utf-8") as fh:
        for line in fh:
            out.write(iri.sub(lambda m: "<" + m.group(1) + "-copy2>", line))
PY
run_one 2n "$WORK/doubled.nt"; RSS_2N="$RSS_KB"; MS_2N="$MS"
rm -f "$WORK/doubled.nt"
check "pack of n under 120 s ($MS_N ms)" "$(( MS_N < 120000 ? 1 : 0 ))"
check "peak RSS of n under 300 MB ($RSS_N kB)" "$(( RSS_N < 307200 ? 1 : 0 ))"
check "peak RSS of 2n ($RSS_2N kB) within 10 % of n ($RSS_N kB); time 2n $MS_2N ms" \
  "$(( RSS_2N * 100 <= 110 * RSS_N && RSS_2N * 100 >= 90 * RSS_N ? 1 : 0 ))"
rmdir "$WORK" 2>/dev/null
exit "$FAIL"
