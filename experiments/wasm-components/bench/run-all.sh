#!/usr/bin/env bash
# run-all.sh — measure every built variant on the same inputs and print one
# JSON line per (variant, host, document). Inputs: bench/gen-data.py output.
#   sizes:     raw and gzip -9 bytes of the shipped artifact(s)
#   node:      bench/node-bench.mjs (jco for components, the emcc glue for emcc)
#   wasmtime:  the variant composed with driver-rs (wac plug), precompiled
#              with `wasmtime compile`; wall time of a run on a one-triple
#              document (process start, instantiation, Lean initialisation)
#              and the driver's medians on the benchmark documents.
#   node-composed: the same composed component under `jco run` (Node).
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
W="${WORK:-/opt/wc}"; T="${TOOLS:-/opt/tc/bin}"; JCO="${JCO_DIR:-/opt/jco}"
N="${N:-7}"; DATA="$HERE/bench/data"; DOCS="${DOCS:-people-2000 people-10000}"
printf '<urn:s> <urn:p> <urn:o> .\n' > "$DATA/one.nt"
size() { printf '"bytes":%s,"gzipBytes":%s' "$(wc -c < "$1")" "$(gzip -9c "$1" | wc -c)"; }
ms_since() { echo $(( ($(date +%s%N) - $1) / 1000000 )); }
for v in ${VARIANTS:-emcc p2 p2-opt p1-opt p2-oz p2-tail p2-simd p2-eh p2-ehx static}; do
  O="$W/out/$v"
  # p2-eh carries legacy exception instructions (Node only; wasmtime 37 has
  # no legacy-exceptions option); p2-ehx the exnref form (wasmtime only;
  # Node 22 needs --experimental-wasm-exnref for it).
  WT=""; NODE_OK=1; WT_OK=1
  case "$v" in p2-eh) WT_OK=0;; p2-ehx) WT="-W exceptions=y"; NODE_OK=0;; esac
  if [ "$v" = emcc ]; then
    [ -s "$O/fxsubset.wasm" ] || { echo "{\"variant\":\"$v\",\"missing\":true}"; continue; }
    echo "{\"variant\":\"$v\",\"artifact\":\"wasm\",$(size "$O/fxsubset.wasm")}"
    echo "{\"variant\":\"$v\",\"artifact\":\"glue\",$(size "$O/fxsubset.mjs")}"
    for d in $DOCS; do for r in 1 2 3; do
      echo "{\"variant\":\"$v\",\"host\":\"node\",\"doc\":\"$d\",\"run\":$r,\"r\":$(node "$HERE/bench/node-bench.mjs" emcc "$O" "$DATA/$d.ttl" turtle "$DATA/q1.rq" "$N")}"
    done; done
    continue
  fi
  if [ "$v" = static ]; then
    [ -s "$O/fx-static.wasm" ] || { echo "{\"variant\":\"$v\",\"missing\":true}"; continue; }
    echo "{\"variant\":\"$v\",\"artifact\":\"wasm\",$(size "$O/fx-static.wasm")}"
    "$T/wasmtime" compile "$O/fx-static.wasm" -o "$O/run.cwasm"
    RUN="$O/run.cwasm"
  else
    [ -s "$O/subset.wasm" ] || { echo "{\"variant\":\"$v\",\"missing\":true}"; continue; }
    echo "{\"variant\":\"$v\",\"artifact\":\"component\",$(size "$O/subset.wasm")}"
    rm -rf "$O/jco"; (cd "$JCO" && npx jco transpile "$O/subset.wasm" -o "$O/jco" --name subset >/dev/null 2>&1)
    echo "{\"variant\":\"$v\",\"artifact\":\"jco-core\",$(size "$O/jco/subset.core.wasm")}"
    echo "{\"variant\":\"$v\",\"artifact\":\"jco-glue\",$(size "$O/jco/subset.js")}"
    [ "$NODE_OK" = 1 ] && for d in $DOCS; do for r in 1 2 3; do
      echo "{\"variant\":\"$v\",\"host\":\"node\",\"doc\":\"$d\",\"run\":$r,\"r\":$(node "$HERE/bench/node-bench.mjs" jco "$O/jco" "$DATA/$d.ttl" turtle "$DATA/q1.rq" "$N")}"
    done; done
    "$T/wac" plug "$HERE/driver-rs/target/wasm32-wasip2/release/fx-driver.wasm" --plug "$O/subset.wasm" -o "$O/composed.wasm"
    [ "$WT_OK" = 1 ] || continue
    t=$(date +%s%N); "$T/wasmtime" compile $WT "$O/composed.wasm" -o "$O/run.cwasm"
    echo "{\"variant\":\"$v\",\"host\":\"wasmtime\",\"compileMs\":$(ms_since $t)}"
    [ "$NODE_OK" = 1 ] && for d in $DOCS; do for r in 1 2 3; do
      echo "{\"variant\":\"$v\",\"host\":\"node-composed\",\"doc\":\"$d\",\"run\":$r,\"r\":$("$JCO/node_modules/.bin/jco" run "$O/composed.wasm" "$DATA/$d.ttl" turtle "$DATA/q1.rq" "$N")}"
    done; done
    RUN="$O/run.cwasm"
  fi
  for r in 1 2 3; do
    t=$(date +%s%N); "$T/wasmtime" run $WT --allow-precompiled --dir "$DATA::/data" "$RUN" /data/one.nt ntriples /data/q1.rq 1 > /dev/null
    echo "{\"variant\":\"$v\",\"host\":\"wasmtime\",\"doc\":\"one\",\"run\":$r,\"wallMs\":$(ms_since $t)}"
  done
  for d in $DOCS; do for r in 1 2 3; do
    echo "{\"variant\":\"$v\",\"host\":\"wasmtime\",\"doc\":\"$d\",\"run\":$r,\"r\":$("$T/wasmtime" run $WT --allow-precompiled --dir "$DATA::/data" "$RUN" "/data/$d.ttl" turtle /data/q1.rq "$N")}"
  done; done
done
