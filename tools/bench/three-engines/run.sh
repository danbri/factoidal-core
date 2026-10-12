#!/usr/bin/env bash
#
# tools/bench/three-engines/run.sh — SBM11, Virtuoso 7.2 (and QLever where a
# docker daemon runs) on olympics and a DBpedia 2016-10 slice.
# Issue: https://github.com/danbri/factoidal/issues/798. Record:
# docs/designissues/2026-10-12-three-engine-benchmark.md.
#
# Rebuilds every number from scratch: data, SBM11 generations, Virtuoso
# databases, answer checks, timings. Writes $BENCH_DATA/results/results.json
# (machine-readable) and prints the markdown tables of the record.
#
# Needs: the Lean toolchain (l4sbm11 is built here), virtuoso-opensource 7.2
# (apt-get install virtuoso-opensource), python3, curl, about 8 GB of free
# disk under BENCH_DATA and about 3.5 GB of /dev/shm (the DBpedia N-Triples
# file is staged in tmpfs while the engines load it, to keep the disk peak
# under the budget of the issue).
#
# Environment: BENCH_DATA (default /home/user/bench-data), QLVR_WORK
# (default /home/user/qlvr-work: olympics.nt and the QLever oracle, from
# tools/qlvr/build-instance.sh), ROUNDS (7), COLD_ROUNDS (3), REPEAT (5),
# DATASETS ("olympics dbpedia"), STEPS ("data pack load answers timing
# qbuild qindex qanswers qtiming report"), MIN_FREE_GB (3), QLEVER_NATIVE
# (default /home/user/qlever-native: QLever source and build, no docker).
#
# QLever runs natively (steps qbuild, qindex, qanswers, qtiming; see
# qlever-native-build.sh and the record, section "QLever native"). The docker
# path (tools/qlvr/build-instance.sh, the image of the pinned commit) needs a
# docker daemon, which this machine does not run; it stays documented there
# and is not used here. The QLever index needs the N-Triples file: for
# olympics it is $QLVR_WORK/instance/olympics.nt; for dbpedia it is the staged
# $SHM/dbpedia.nt, which the load step deletes unless KEEP_NT=1.
set -euo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
export BENCH_DATA="${BENCH_DATA:-/home/user/bench-data}"
QLVR_WORK="${QLVR_WORK:-/home/user/qlvr-work}"
SHM="${SHM:-/dev/shm/bench-data}"
ROUNDS="${ROUNDS:-7}"; COLD_ROUNDS="${COLD_ROUNDS:-3}"; REPEAT="${REPEAT:-5}"
DATASETS="${DATASETS:-olympics dbpedia}"
STEPS="${STEPS:-data pack load answers timing qbuild qindex qanswers qtiming report}"
QLEVER_NATIVE="${QLEVER_NATIVE:-/home/user/qlever-native}"
QLEVER_BIN="$QLEVER_NATIVE/build"
RES="$BENCH_DATA/results"
mkdir -p "$BENCH_DATA/dl" "$BENCH_DATA/sbm11" "$BENCH_DATA/virtuoso" "$BENCH_DATA/qlever" "$RES" "$SHM"
export PATH="$HOME/.elan/bin:$PATH"
BIN="$ROOT/formal/lean4/.lake/build/bin"
log() { printf '[run %s] %s\n' "$(date -u +%H:%M:%S)" "$*" >&2; }
has_step() { case " $STEPS " in *" $1 "*) return 0 ;; esac; return 1; }
check_disk() {
  local free_kb; free_kb=$(df -Pk "$BENCH_DATA" | awk 'NR==2 {print $4}')
  if [ "$free_kb" -lt $(( ${MIN_FREE_GB:-3} * 1024 * 1024 )) ]; then
    log "free disk ${free_kb} kB under ${MIN_FREE_GB:-3} GB: stop"; exit 3
  fi
  log "free disk $(( free_kb / 1024 )) MB, load $(cut -d' ' -f1 /proc/loadavg)"
}

# Pinned inputs.
DBP_BASE=https://downloads.dbpedia.org/2016-10/core-i18n/en
DBP_OBJ=mappingbased_objects_en.ttl.bz2
DBP_OBJ_SHA=a5811aa5a6bea87e7e75db3f3ef7a9ce55e588dc61f72fec5c920b718f9c5953
DBP_LIT=mappingbased_literals_en.ttl.bz2
DBP_LIT_SHA=0d0d6b55b240758075bb74b6c0f5144e2319f3dbf17a452f780fd43356f5d518
DBP_NT_SHA=94025f74d5c4643ce05984524e5583c59a057b8110544ec9a7c55fbd21de85e1
OLY_NT="$QLVR_WORK/instance/olympics.nt"
OLY_NT_SHA=44e15095a3a9beefe09c512882a08d9b7aa82bba5e48fa22bfbfb361dde01ce0

nt_of() { case $1 in olympics) echo "$OLY_NT" ;; dbpedia) echo "$SHM/dbpedia.nt" ;; esac; }
graph_of() { echo "http://factoidal.org/bench/$1"; }
sha_ok() { [ "$(sha256sum "$1" | cut -d' ' -f1)" = "$2" ] || { log "sha256 mismatch: $1"; exit 1; }; }

# 0. machine -----------------------------------------------------------------
python3 -I - "$RES/machine.json" <<'PY'
import json, os, platform, subprocess, sys
cpu = [l.split(":", 1)[1].strip() for l in open("/proc/cpuinfo") if l.startswith("model name")]
mem = [l for l in open("/proc/meminfo") if l.startswith("MemTotal")][0].split()[1]
rota = {}
for d in os.listdir("/sys/block"):
    try:
        rota[d] = open("/sys/block/%s/queue/rotational" % d).read().strip()
    except OSError:
        pass
r = subprocess.run(["/usr/bin/virtuoso-t", "-?"], capture_output=True, text=True)
virt = [l.strip() for l in (r.stdout + r.stderr).splitlines() if l.startswith("Version")]
json.dump({"cpu": cpu[0] if cpu else None, "vcpus": os.cpu_count(), "mem_kb": int(mem),
           "kernel": platform.release(), "block_rotational": rota,
           "virtuoso": virt[0] if virt else None},
          open(sys.argv[1], "w"), indent=1)
PY

# 1. data --------------------------------------------------------------------
if has_step data; then
  check_disk
  for f in "$DBP_OBJ:$DBP_OBJ_SHA" "$DBP_LIT:$DBP_LIT_SHA"; do
    name=${f%%:*}; sha=${f##*:}
    [ -f "$BENCH_DATA/dl/$name" ] || curl -sSfL -o "$BENCH_DATA/dl/$name" "$DBP_BASE/$name"
    sha_ok "$BENCH_DATA/dl/$name" "$sha"
  done
  if [ ! -f "$SHM/dbpedia.nt" ]; then
    python3 -I "$HERE/slice.py" "$BENCH_DATA/dl/$DBP_OBJ" "$BENCH_DATA/dl/$DBP_LIT" \
      "$SHM/dbpedia.nt" "$RES/slice-stats.json"
  fi
  sha_ok "$SHM/dbpedia.nt" "$DBP_NT_SHA"
  [ -f "$OLY_NT" ] || { log "missing $OLY_NT: run tools/qlvr/build-instance.sh"; exit 1; }
  sha_ok "$OLY_NT" "$OLY_NT_SHA"
fi

# 2. SBM11 pack ----------------------------------------------------------------
if has_step pack; then
  (cd "$ROOT/formal/lean4" && lake build l4sbm11 l4sbm11-pack >&2)
  for ds in $DATASETS; do
    check_disk
    rm -rf "$BENCH_DATA/sbm11/$ds"
    log "pack $ds"
    echo "loadavg_before $(cut -d' ' -f1 /proc/loadavg)" >"$RES/pack-$ds.log"
    "$HERE/guarded.sh" "$RES/pack-$ds.json" -- "$BIN/l4sbm11-pack" "$(nt_of "$ds")" \
      "$BENCH_DATA/sbm11/$ds" >>"$RES/pack-$ds.log" 2>&1
    echo "loadavg_after $(cut -d' ' -f1 /proc/loadavg)" >>"$RES/pack-$ds.log"
    du -sb "$BENCH_DATA/sbm11/$ds" | cut -f1 >"$RES/sbm11-size-$ds.txt"
  done
fi

# 3. Virtuoso load -------------------------------------------------------------
if has_step load; then
  for ds in $DATASETS; do
    check_disk
    log "virtuoso load $ds"
    python3 -I "$HERE/bench.py" virtuoso-load --nt "$(nt_of "$ds")" --graph "$(graph_of "$ds")" \
      --dbdir "$BENCH_DATA/virtuoso/$ds" --out "$RES/virtuoso-load-$ds.json"
  done
  # The staged N-Triples file holds about 3 GB of RAM; free it before timing.
  [ -n "${KEEP_NT:-}" ] || rm -f "$SHM/dbpedia.nt"
fi

# 4. answers -------------------------------------------------------------------
if has_step answers; then
  for ds in $DATASETS; do
    oracle=(); [ "$ds" = olympics ] && [ -d "$QLVR_WORK/oracle" ] && oracle=(--oracle "$QLVR_WORK/oracle")
    log "answers $ds"
    python3 -I "$HERE/bench.py" answers --dataset "$ds" --queries "$HERE/queries/$ds" \
      --gen "$BENCH_DATA/sbm11/$ds" --dbdir "$BENCH_DATA/virtuoso/$ds" --graph "$(graph_of "$ds")" \
      --outdir "$BENCH_DATA/answers/$ds" "${oracle[@]}" --out "$RES/answers-$ds.json"
  done
fi

# 5. timing --------------------------------------------------------------------
if has_step timing; then
  for ds in $DATASETS; do
    log "timing $ds"
    python3 -I "$HERE/bench.py" timing --dataset "$ds" --queries "$HERE/queries/$ds" \
      --gen "$BENCH_DATA/sbm11/$ds" --dbdir "$BENCH_DATA/virtuoso/$ds" --graph "$(graph_of "$ds")" \
      --answers "$RES/answers-$ds.json" --rounds "$ROUNDS" --cold-rounds "$COLD_ROUNDS" \
      --repeat "$REPEAT" --out "$RES/timing-$ds.json"
  done
fi

# 6. QLever native -------------------------------------------------------------
if has_step qbuild; then
  "$HERE/qlever-native-build.sh" all
fi
if has_step qindex; then
  for ds in $DATASETS; do
    check_disk
    nt="$(nt_of "$ds")"
    [ -f "$nt" ] || { log "QLever $ds: missing input $nt (see the header of run.sh)"; exit 1; }
    base="$BENCH_DATA/qlever/$ds"
    rm -rf "$base"; mkdir -p "$base"
    settings="$(python3 -I "$HERE/bench.py" qlever-settings --base "$base/$ds")"
    log "qlever index $ds"
    echo "loadavg_before $(cut -d' ' -f1 /proc/loadavg)" >"$RES/qlever-index-$ds.log"
    (cd "$base" && "$HERE/guarded.sh" "$RES/qlever-index-$ds.json" -- "$QLEVER_BIN/qlever-index" \
      -i "$base/$ds" -f "$nt" -F nt -p -j 4 -m 4G -s "$settings") >>"$RES/qlever-index-$ds.log" 2>&1
    echo "loadavg_after $(cut -d' ' -f1 /proc/loadavg)" >>"$RES/qlever-index-$ds.log"
    find "$base" -maxdepth 1 -type f -name "$ds.*" ! -name '*.log' ! -name '*.settings.json' \
      -printf '%s\n' | awk '{s+=$1} END {print s+0}' >"$RES/qlever-size-$ds.txt"
  done
fi
if has_step qanswers; then
  for ds in $DATASETS; do
    oracle=(); [ "$ds" = olympics ] && [ -d "$QLVR_WORK/oracle" ] && oracle=(--oracle "$QLVR_WORK/oracle")
    log "qlever answers $ds"
    python3 -I "$HERE/bench.py" qlever-answers --dataset "$ds" --queries "$HERE/queries/$ds" \
      --index "$BENCH_DATA/qlever/$ds/$ds" --answers-dir "$BENCH_DATA/answers/$ds" \
      --outdir "$BENCH_DATA/answers/$ds" "${oracle[@]}" --out "$RES/qlever-answers-$ds.json"
  done
fi
if has_step qtiming; then
  for ds in $DATASETS; do
    log "qlever timing $ds"
    python3 -I "$HERE/bench.py" qlever-timing --dataset "$ds" --queries "$HERE/queries/$ds" \
      --index "$BENCH_DATA/qlever/$ds/$ds" --answers "$RES/qlever-answers-$ds.json" \
      --rounds "$ROUNDS" --cold-rounds "$COLD_ROUNDS" --out "$RES/qlever-timing-$ds.json"
  done
fi

# 7. report --------------------------------------------------------------------
if has_step report; then
  python3 -I "$HERE/report.py" "$RES" $DATASETS
  python3 -I "$HERE/bench.py" qlever-report --results "$RES" $DATASETS > "$RES/qlever-report.md"
fi
