#!/usr/bin/env bash
# SBM11 stage 3 check (https://github.com/danbri/factoidal/issues/789).
#
#   tests/sbm11/stage3_check.sh SOURCE.nt WORKDIR [PACK-OPTIONS...]
#
# Packs SOURCE into WORKDIR/gen-1 with l4sbm11-pack, activates it
# (WORKDIR/CURRENT), then checks:
#   1. `l4sbm11 dump` of SPO equals `l4sbm11 canon SOURCE` as a set of N-Quads
#      lines (both sorted with LC_ALL=C sort -u; counts of lines only in one
#      side are printed and must be 0);
#   2. the four permutations hold the same quads: `dump-ids` of each, sorted,
#      byte-identical;
#   3. tampered copies (a PRM1 first row, last row or row count, a PRB1 frame
#      byte), each resealed so that the manifest digests match, are refused
#      by `l4sbm11 verify` for the block reason, not the digest;
#   4. scan and count of the q03 predicate (dbp:year) and count of every row.
# Exit 0 only when every check passes. Pack and check output goes to
# WORKDIR/*.log; a summary goes to stdout.
set -u
SRC="$1"; WORK="$2"; shift 2
HERE="$(cd "$(dirname "$0")" && pwd)"
BIN="$HERE/../../formal/lean4/.lake/build/bin"
PACK="$BIN/l4sbm11-pack"; CLI="$BIN/l4sbm11"
for b in "$PACK" "$CLI"; do
  [ -x "$b" ] || { echo "missing $b (lake build l4sbm11-pack l4sbm11)"; exit 2; }
done
mkdir -p "$WORK"
rm -rf "$WORK/gen-1" "$WORK/CURRENT" "$WORK/tamper"
fail=0
note() { echo "$*"; }
bad() { echo "FAIL: $*"; fail=1; }

# wall time of a command in ms (the tools print their own VmHWM)
wall() { local t0 t1; t0=$(date +%s%N); "$@"; local rc=$?; t1=$(date +%s%N); WALL_MS=$(( (t1 - t0) / 1000000 )); return $rc; }

wall "$PACK" "$SRC" "$WORK/gen-1" "$@" > "$WORK/pack.log" 2> "$WORK/pack.err"
rc=$?
[ "$rc" -eq 0 ] || { bad "pack exit $rc"; cat "$WORK/pack.log" "$WORK/pack.err"; exit 1; }
grep '^sbm11-pack' "$WORK/pack.log"
note "pack: wall-ms=$WALL_MS"

wall "$CLI" activate "$WORK" gen-1 > "$WORK/activate.log" 2> "$WORK/activate.err"
rc=$?
grep -h 'sbm11-activate\|sbm11-verify' "$WORK/activate.log" "$WORK/activate.err"
note "activate: wall-ms=$WALL_MS"
[ "$rc" -eq 0 ] || bad "activate exit $rc"
[ "$(cat "$WORK/CURRENT" 2>/dev/null)" = "gen-1" ] || bad "CURRENT does not name gen-1"

# 1. dump of SPO against the source as sets
"$CLI" dump "$WORK" spo 2> "$WORK/dump.err" | LC_ALL=C sort -u > "$WORK/dump.sorted"
"$CLI" canon "$SRC" | LC_ALL=C sort -u > "$WORK/source.sorted"
only_dump=$(LC_ALL=C comm -23 "$WORK/dump.sorted" "$WORK/source.sorted" | wc -l)
only_src=$(LC_ALL=C comm -13 "$WORK/dump.sorted" "$WORK/source.sorted" | wc -l)
both=$(LC_ALL=C comm -12 "$WORK/dump.sorted" "$WORK/source.sorted" | wc -l)
note "dump-vs-source: equal=$both only-in-dump=$only_dump only-in-source=$only_src"
[ "$only_dump" -eq 0 ] && [ "$only_src" -eq 0 ] || bad "dump differs from the source"
note "dump: $(grep 'sbm11:' "$WORK/dump.err")"

# 2. the four permutations hold the same quads
for p in pso pos spo osp; do
  "$CLI" dump-ids "$WORK" "$p" 2>/dev/null | LC_ALL=C sort > "$WORK/ids-$p.sorted"
done
for p in pos spo osp; do
  if cmp -s "$WORK/ids-pso.sorted" "$WORK/ids-$p.sorted"; then :; else bad "$p holds other quads than pso"; fi
done
note "permutations: $(wc -l < "$WORK/ids-pso.sorted") rows each, same quad set: $([ $fail -eq 0 ] && echo yes || echo no)"

# 3. tampered copies are refused. Each is resealed (`l4sbm11 reseal`: new
#    digests and Merkle roots in the manifest), so the refusal must come from
#    the PRM1 or block checks and not from the digest check.
tamper() { # tamper NAME FILE PYTHON-STATEMENT-ON-b EXPECT
  local name="$1" file="$2" expr="$3" expect="$4" dir="$WORK/tamper/$1"
  rm -rf "$dir"; mkdir -p "$WORK/tamper"; cp -r "$WORK/gen-1" "$dir"
  python3 -c "import sys
p=sys.argv[1]; b=bytearray(open(p,'rb').read()); $expr; open(p,'wb').write(bytes(b))" "$dir/$file"
  "$CLI" reseal "$dir" > /dev/null || { bad "reseal $name"; return; }
  if "$CLI" verify "$dir" > "$WORK/tamper-$name.log" 2>&1; then bad "tamper $name was admitted"
  elif grep -q "$expect" "$WORK/tamper-$name.log"; then note "tamper $name: refused ($(grep -m1 'FAIL\|l4sbm11:' "$WORK/tamper-$name.log"))"
  else bad "tamper $name refused for another reason: $(grep -m1 'FAIL\|l4sbm11' "$WORK/tamper-$name.log")"; fi
}
# the first row of the first PSO block, c2 byte 0 (the PRM1 header is 22 bytes)
tamper prm-first pso.prm1 'b[22+16]^=1' 'first row differs from PRM1'
# the last row of the first SPO block, c2 byte 0 (first row 32 bytes, then c0, c1)
tamper prm-last spo.prm1 'b[22+32+16]^=1' 'last row differs from PRM1\|does not decode as PRM1'
# the row count of the first OSP block, one less
tamper prm-rows osp.prm1 'b[22+64]-=1' 'does not decode as PRM1'
# one frame byte in the middle of SPO
tamper prb-byte spo.prb1 'b[len(b)//2]^=0x10' 'block'
rm -rf "$WORK/tamper"

# 4. scan and count
YEAR='<http://dbpedia.org/property/year>'
"$CLI" scan "$WORK" pso "$YEAR" > "$WORK/scan-year.nq" 2> "$WORK/scan-year.err"
note "scan pso dbp:year: rows=$(wc -l < "$WORK/scan-year.nq") $(grep 'sbm11: scan' "$WORK/scan-year.err" | sed 's/sbm11: //')"
note "  $(grep 'sbm11: scan read' "$WORK/scan-year.err" | sed 's/sbm11: //')"
"$CLI" count "$WORK" pso "$YEAR" > "$WORK/count-year.out" 2> "$WORK/count-year.err"
note "count pso dbp:year: $(cat "$WORK/count-year.out") $(grep 'sbm11: count perm' "$WORK/count-year.err" | sed 's/sbm11: //')"
"$CLI" count "$WORK" pso > "$WORK/count-all.out" 2> "$WORK/count-all.err"
note "count all: $(cat "$WORK/count-all.out") $(grep 'sbm11: count perm' "$WORK/count-all.err" | sed 's/sbm11: //')"
note "  $(grep 'sbm11: count read' "$WORK/count-all.err" | sed 's/sbm11: //')"
[ "$(cat "$WORK/count-all.out")" = "$(wc -l < "$WORK/ids-pso.sorted")" ] || bad "count of all rows differs from the dump"
[ "$(cat "$WORK/count-year.out")" = "$(wc -l < "$WORK/scan-year.nq")" ] || bad "count of dbp:year differs from the scan"

if [ "$fail" -eq 0 ]; then echo "stage3-check: PASS"; else echo "stage3-check: FAIL"; fi
exit "$fail"
