#!/usr/bin/env bash
# Pack the QLever comparison instance (olympics.nt) into the two Shardborough
# layouts and activate each. Records wall time and peak RSS per step.
#
# Usage: tools/shardborough-cmp/pack.sh [WORK-DIR]
#   WORK-DIR default: /home/user/qlvr-work/shardborough-cmp
# Needs: formal/lean4/.lake/build/bin/l4block-shard-pack and -activate
#        (cd formal/lean4 && lake build l4block-shard-pack l4block-shard-activate).
# Design record: docs/designissues/2026-10-11-shardborough-vs-qlever.md
set -u
ROOT="$(cd "$(dirname "$0")/../.." && pwd)"
B="$ROOT/formal/lean4/.lake/build/bin"
WORK="${1:-/home/user/qlvr-work/shardborough-cmp}"
INPUT="${QLVR_INPUT:-/home/user/qlvr-work/instance/olympics.nt}"
RU="$ROOT/tools/shardborough-cmp/rusage.py"
mkdir -p "$WORK/measure"

for layout in ibk3 ibk5; do
  COL="$WORK/col-$layout"
  if [ -e "$COL/CURRENT" ]; then
    echo "pack.sh: $COL already activated; remove it to repack"; continue
  fi
  rm -rf "$COL"; mkdir -p "$COL"
  PACK_RC=0
  python3 "$RU" "$WORK/measure/pack-$layout.json" -- \
    "$B/l4block-shard-pack" "$INPUT" "$COL/gen-1" "$layout" \
    > "$WORK/measure/pack-$layout.out" 2>&1 || PACK_RC=$?
  cat "$WORK/measure/pack-$layout.out"
  if [ "$PACK_RC" -ne 0 ]; then echo "pack.sh: pack $layout failed rc=$PACK_RC"; exit 1; fi
  ACT_RC=0
  python3 "$RU" "$WORK/measure/activate-$layout.json" -- \
    "$B/l4block-shard-activate" "$COL" gen-1 \
    > "$WORK/measure/activate-$layout.out" 2>&1 || ACT_RC=$?
  cat "$WORK/measure/activate-$layout.out"
  if [ "$ACT_RC" -ne 0 ]; then echo "pack.sh: activate $layout failed rc=$ACT_RC"; exit 1; fi
done

# Bytes on disk per file type (suffix after the first dot of the name).
for layout in ibk3 ibk5; do
  echo "== bytes per file type: $layout"
  python3 - "$WORK/col-$layout/gen-1" <<'PY'
import os, sys, collections, re
d = sys.argv[1]
acc = collections.Counter(); cnt = collections.Counter()
for n in os.listdir(d):
    p = os.path.join(d, n)
    if not os.path.isfile(p):
        continue
    if n.startswith("blob-"):
        k = "blob" + (".merkle" if n.endswith(".merkle") else "")
    else:
        k = re.sub(r"^predicate-\d+", "predicate-N", n)
    acc[k] += os.path.getsize(p); cnt[k] += 1
tot = sum(acc.values())
for k in sorted(acc, key=lambda k: -acc[k]):
    print(f"{k}\t{cnt[k]}\t{acc[k]}")
print(f"TOTAL\t{sum(cnt.values())}\t{tot}")
PY
done
