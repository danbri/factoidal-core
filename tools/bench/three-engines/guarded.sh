#!/usr/bin/env bash
#
# tools/bench/three-engines/guarded.sh OUT-JSON -- CMD ARGS...
#
# Run CMD under tools/shardborough-cmp/rusage.py (wall time and peak RSS of
# the child into OUT-JSON). While it runs, check the free space of the
# filesystem of BENCH_DATA every 5 s; when it falls under MIN_FREE_GB
# (default 3), kill the command and exit 3. The machine's disk is shared
# with other work (issue 798 constraint).
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
OUT="${1:?usage: guarded.sh OUT-JSON -- CMD ARGS...}"; shift
[ "${1:-}" = "--" ] && shift
MIN_FREE_GB="${MIN_FREE_GB:-3}"
DATA="${BENCH_DATA:-/home/user/bench-data}"
python3 -I "$ROOT/tools/shardborough-cmp/rusage.py" "$OUT" -- "$@" &
pid=$!
while kill -0 "$pid" 2>/dev/null; do
  free_kb=$(df -Pk "$DATA" | awk 'NR==2 {print $4}')
  if [ "$free_kb" -lt $(( MIN_FREE_GB * 1024 * 1024 )) ]; then
    echo "guarded: free disk ${free_kb} kB < ${MIN_FREE_GB} GB; stopping $*" >&2
    pkill -TERM -P "$pid"
    kill -TERM "$pid" 2>/dev/null
    wait "$pid"
    exit 3
  fi
  sleep 5
done
rc=0; wait "$pid" || rc=$?
exit "$rc"
