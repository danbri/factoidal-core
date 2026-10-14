#!/usr/bin/env bash
#
# tests/stack/run.sh — the deep-input stress suite.
#
# Every case here is an ordinary document that is only LARGE in one
# dimension a caller controls: how many entity references, how long a
# literal, how many collection items, how many quads, how many UNION
# arms, how deep a group, how many manifest entries. A function that
# recurses over that dimension without a tail-call loop consumes one
# C stack frame per step and the process dies; a function that loops,
# or that carries a worklist, does not.
#
# Two routes, because they have different stacks:
#   wasm    the shipped module (docs/web/hub/assets/l4/), run in Node.
#           This is the SMALLEST stack we ship, and the one a browser
#           tab runs.  IT IS A BUILD PRODUCT: a Lean fix does not reach
#           it until the wasm module is rebuilt (missing module: the wasm
#           routes record one failure and score nothing).
#   native  formal/lean4/.lake/build/bin/l4wasm-cli, the same dispatch
#           ABI compiled for the host. A Lean executable runs main on a
#           thread the Lean runtime creates, with a 1 GB stack by default
#           (src/runtime/thread.cpp:27, LEAN_DEFAULT_THREAD_STACK_SIZE).
#
# CANARY MODE (--canary [KB], default 512) runs the native route with a
# reduced stack, so a function that consumes a frame per input element
# fails HERE, with a case name, instead of only in a browser tab.
#
# THE KNOB. The Lean runtime reads the environment variable
# LEAN_STACK_SIZE_KB and gives the thread that runs main that many
# kilobytes. Source, Lean 4.33.1 (the toolchain of formal/lean4),
# src/runtime/thread.cpp:
#     171:  const char * stack_size_env = std::getenv("LEAN_STACK_SIZE_KB");
#     174:  sz = sz / 4 * 4 * 1024; // as in `Shell`
#     193:  set_thread_stack_size_from_env();   (in lean_run_main)
# The value is a number of kilobytes, rounded down to a multiple of 4.
# `ulimit -s` and a variable named LEAN_STACK_SIZE (bytes) do nothing:
# main does not run on the process's main thread, so the rlimit does not
# reach it, and the runtime never reads the second name. Until 2026-10-10
# this script set those two and so measured nothing (issue 749; measured on
# linux-x86_64: turtle-collection, 100,000 items, returned 200,001 quads
# under `ulimit -s 512` with LEAN_STACK_SIZE=524288 and aborted under
# LEAN_STACK_SIZE_KB=512, before the collection reader of issue 678 became a
# loop). The toolchain installed by elan ships no runtime sources, only the
# string; the sources are the leanprover/lean4 tag
# v4.33.1. LEAN_MAIN_USE_THREAD=0 would run main on the process's main
# thread, where the knob does not apply; the canary unsets it.
#
# THE CONTROL. The mode does not trust the knob; it measures it first, with
# tests/stack/StackControl.lean, a program that holds one function that is
# non-tail on purpose (foldNonTail: one native frame per list element) and
# imports nothing from L4Factoidal, so no library repair can change it.
# run.sh compiles it with `lean -c` and `leanc` (about 2 s, through
# `lake env` in formal/lean4). Three runs must behave:
#     canary budget, 100 elements      runs        (the budget is not so
#                                                   small that nothing starts)
#     canary budget, N elements        OVERFLOWS   (exit 134, "Stack overflow")
#     default budget, N elements       runs        (prints the sum)
# with N = max(200000, 400 * KB). If any run differs, or the control cannot
# be compiled, the native canary refuses to score: it records one failing
# case named `control` that says which run differed, scores none of the
# canary cases, and the mode cannot report a pass (anti-pattern #28: an
# audit that cannot fail is evidence about the audit before it is evidence
# about the code). macOS is untested with LEAN_STACK_SIZE_KB: the runtime
# sets the stack through pthread attributes, so it is expected to apply
# there, and the control decides.
#
# Measured 2026-10-10, linux x86_64, Lean 4.33.1, control program: largest
# n that ran under LEAN_STACK_SIZE_KB = 256: 12,142; 512: 20,334; 1024:
# 36,718; 2048: 69,486; 4096: 135,022 (about 32 bytes per element). With no
# variable (1 GB) 20,000,000 elements ran in 3.6 s.
#
# The wasm equivalent needs a diagnostic module, not a flag at run time.
# Rebuild with
#     -sSTACK_SIZE=262144 -sSTACK_OVERFLOW_CHECK=2
# in formal/lean4/Wasm/build-wasm.sh: the small stack makes an
# input-proportional recursion fail early, and OVERFLOW_CHECK=2 writes a
# canary word past the stack end so the abort NAMES the function instead
# of reporting "Maximum call stack size exceeded" from an arbitrary
# frame. That module is a diagnostic, never the shipped one.
#
# Usage:  tests/stack/run.sh [--route wasm|native|both] [--fixtures DIR]
#                            [--canary [KB]] [--control-only]
#
# --control-only compiles and runs the canary control and nothing else.
# tests/stack/canary_control.sh uses it to show that the control can FAIL:
# with a wrong variable name (STACK_CANARY_VAR=LEAN_STACK_SIZE, the name this
# suite used until 2026-10-10) the control must refuse to score.
#
# Scores are printed as "N pass, M fail (out of T)" per route.
set -uo pipefail

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN_DIR="$ROOT/formal/lean4"
CLI="$LEAN_DIR/.lake/build/bin/l4wasm-cli"

ROUTE=both
CANARY=0
CONTROL_ONLY=0
CANARY_KB=512
FIXTURES="${STACK_FIXTURES:-${TMPDIR:-/tmp}/factoidal-stack-fixtures}"
TIMEOUT="${STACK_TIMEOUT:-120}"
# sbm11-delta request size (quads deleted; the insert has twice as many).
# gen_cases.py reads the same variable.
N_DELTA="${STACK_SBM11_DELTA:-4000}"
export STACK_SBM11_DELTA="$N_DELTA"
# sbm11-update-where solutions (gen_cases.py reads the same variable).
N_WHERE="${STACK_SBM11_WHERE:-12000}"
export STACK_SBM11_WHERE="$N_WHERE"
while [ $# -gt 0 ]; do
  case "$1" in
    --route) ROUTE="$2"; shift 2 ;;
    --fixtures) FIXTURES="$2"; shift 2 ;;
    --timeout) TIMEOUT="$2"; shift 2 ;;
    --control-only) CONTROL_ONLY=1; CANARY=1; shift ;;
    --canary)
      CANARY=1
      case "${2:-}" in ''|-*) shift 1 ;; *) CANARY_KB="$2"; shift 2 ;; esac ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done

mkdir -p "$FIXTURES"
if [ "$CONTROL_ONLY" != 1 ]; then
  echo "=== generating fixtures in $FIXTURES"
  python3 "$HERE/gen_cases.py" "$FIXTURES" || exit 2
fi

# A portable timeout: macOS ships no coreutils `timeout`.
# The watchdog's own stdout MUST go to /dev/null. Command substitution
# waits for every writer to close the pipe, so a watchdog that inherits
# stdout holds `$(...)` open for the whole timeout and every case then
# "passes" after exactly the cap. That bug made the first run of this
# suite report seven passes at 30,000 ms each.
run_capped() {
  local secs="$1"; shift
  "$@" &
  local pid=$!
  ( sleep "$secs"; kill -9 "$pid" ) >/dev/null 2>&1 &
  local killer=$!
  wait "$pid"; local rc=$?
  kill -9 "$killer" >/dev/null 2>&1
  wait "$killer" 2>/dev/null
  return "$rc"
}

PASS=0; FAIL=0; TOTAL=0
declare -a RESULTS=()

record() { # record <route> <case> <ok:0|1> <detail>
  TOTAL=$((TOTAL + 1))
  if [ "$3" = 0 ]; then
    PASS=$((PASS + 1)); printf 'ok   %-8s %-22s %s\n' "$1" "$2" "$4"
  else
    FAIL=$((FAIL + 1)); printf 'FAIL %-8s %-22s %s\n' "$1" "$2" "$4"
  fi
}

# ---------------------------------------------------------------- native
native_case() { # native_case <case> <op> <argsfile>
  local name="$1" op="$2" argsfile="$3"
  local out rc t0 t1
  t0=$(python3 -c 'import time;print(int(time.time()*1000))')
  out="$(run_capped "$TIMEOUT" "$CLI" call "$op" "$FIXTURES/$argsfile" 2>&1)"; rc=$?
  t1=$(python3 -c 'import time;print(int(time.time()*1000))')
  local ms=$((t1 - t0))
  if [ "$rc" -ne 0 ]; then
    record native "$name" 1 "exit $rc after ${ms}ms: $(printf '%s' "$out" | head -c 160)"
  elif printf '%s' "$out" | grep -q '"ok":false'; then
    record native "$name" 1 "engine error after ${ms}ms: $(printf '%s' "$out" | head -c 160)"
  else
    record native "$name" 0 "${ms}ms"
  fi
}

# ---------------------------------------------------------- canary control
#
# See THE CONTROL in the header. CANARY_PREFIX runs a command with the canary
# budget; it unsets LEAN_MAIN_USE_THREAD so that main runs on the runtime's
# own thread, the one the knob sizes.
CONTROL_SRC="$HERE/StackControl.lean"
CONTROL_BIN=""
CONTROL_WHY=""
CONTROL_OK=0

# An external command, not a function: run_capped kills the PID it starts, and
# a backgrounded shell function would leave its child process running.
# STACK_CANARY_VAR exists so that tests/stack/canary_control.sh can set the
# wrong name and see the control refuse to score.
CANARY_VAR="${STACK_CANARY_VAR:-LEAN_STACK_SIZE_KB}"
CANARY_PREFIX=(env -u LEAN_MAIN_USE_THREAD "$CANARY_VAR=$CANARY_KB")

control_build() { # sets CONTROL_BIN, or CONTROL_WHY when it cannot compile
  local c="$FIXTURES/stack-control.c" bin="$FIXTURES/stack-control"
  if [ -x "$bin" ] && [ "$bin" -nt "$CONTROL_SRC" ]; then CONTROL_BIN="$bin"; return 0; fi
  if ! command -v lake >/dev/null 2>&1; then
    CONTROL_WHY="lake is not on PATH, so the control program cannot be compiled (export PATH=\"\$HOME/.elan/bin:\$PATH\")"
    return 1
  fi
  local log
  # lake runs in formal/lean4 only (CLAUDE.md, Lean Lake working directory).
  log="$( cd "$LEAN_DIR" && lake env sh -c \
      'cd "$1" && lean --root=. -c "$2" StackControl.lean && leanc -O1 -o "$3" "$2"' \
      sh "$HERE" "$c" "$bin" 2>&1 )" || {
    CONTROL_WHY="the control program did not compile: $(printf '%s' "$log" | head -c 300)"
    return 1
  }
  CONTROL_BIN="$bin"
}

# control_run <budget:canary|default> <n>; sets CONTROL_RC and CONTROL_OUT.
control_run() {
  if [ "$1" = canary ]; then
    CONTROL_OUT="$(run_capped "$TIMEOUT" "${CANARY_PREFIX[@]}" "$CONTROL_BIN" "$2" 2>&1)"; CONTROL_RC=$?
  else
    CONTROL_OUT="$(run_capped "$TIMEOUT" env -u LEAN_MAIN_USE_THREAD -u LEAN_STACK_SIZE_KB -u "$CANARY_VAR" "$CONTROL_BIN" "$2" 2>&1)"; CONTROL_RC=$?
  fi
}

# Runs the three control runs. Sets CONTROL_OK=1 when all behave, otherwise
# CONTROL_WHY names the first run that did not.
canary_control() {
  local n=$((CANARY_KB * 400))
  [ "$n" -lt 200000 ] && n=200000
  CONTROL_OK=0
  control_build || return 1

  control_run canary 100
  if [ "$CONTROL_RC" -ne 0 ] || [ "$(printf '%s' "$CONTROL_OUT" | tail -1)" != 4950 ]; then
    CONTROL_WHY="the control with 100 elements did not run under ${CANARY_VAR}=${CANARY_KB} (exit $CONTROL_RC): $(printf '%s' "$CONTROL_OUT" | head -c 160)"
    return 1
  fi

  control_run canary "$n"
  if [ "$CONTROL_RC" -eq 0 ]; then
    CONTROL_WHY="${CANARY_VAR}=${CANARY_KB} did not reach the process: the non-tail control with $n elements RAN (it must overflow). Check that this Lean runtime reads ${CANARY_VAR} (it read LEAN_STACK_SIZE_KB in 4.33.1), and that the budget is below about $((n * 32 / 1024)) KB"
    return 1
  fi
  if ! printf '%s' "$CONTROL_OUT" | grep -q 'Stack overflow'; then
    CONTROL_WHY="the control with $n elements failed under ${CANARY_VAR}=${CANARY_KB}, but not with a stack overflow (exit $CONTROL_RC): $(printf '%s' "$CONTROL_OUT" | head -c 160)"
    return 1
  fi

  control_run default "$n"
  local want=$((n * (n - 1) / 2))
  if [ "$CONTROL_RC" -ne 0 ] || [ "$(printf '%s' "$CONTROL_OUT" | tail -1)" != "$want" ]; then
    CONTROL_WHY="the control with $n elements did not run at the default stack budget (exit $CONTROL_RC): $(printf '%s' "$CONTROL_OUT" | head -c 160)"
    return 1
  fi
  CONTROL_OK=1
  CONTROL_DETAIL="n=$n: 100 elements ran and $n elements overflowed under ${CANARY_KB}KB; $n elements ran at the default budget"
}

# --control-only: run the control and nothing else (used by canary_control.sh).
if [ "$CONTROL_ONLY" = 1 ]; then
  if canary_control; then
    echo "ok   canary control: $CONTROL_DETAIL"; exit 0
  fi
  echo "FAIL canary control: native canary NOT SCORED: $CONTROL_WHY"; exit 1
fi

# Cases that overflow a reduced or a browser-sized stack today, each with the
# open issue that tracks it. A listed case passes the suite while it overflows
# and turns the suite red if it stops overflowing, so the fix flips this table
# and closes the issue. A listed case that fails in any other way is a
# failure. The table applies to the three routes that have a small stack: the
# native canary, the wasm canary and the wasm route. The native route runs on
# the 1 GB default stack and has no entries. (`turtle-collection` was listed
# for https://github.com/danbri/factoidal/issues/678 until 2026-10-10, when
# the Turtle collection reader became a loop; it runs in all three routes.
# `xml-entities` was listed for https://github.com/danbri/factoidal/issues/673
# until the same day, when the XML reference scan became a loop.
# `turtle-predicates` was listed for
# https://github.com/danbri/factoidal/issues/754 until the same day, when the
# Turtle predicate-object list reader became a loop.)
xfail_issue() { # xfail_issue <case>; prints the issue URL or nothing
  case "$1" in
    # $2 is the route (canary, wcanary or wasm), for a case that overflows
    # in some of the small-stack routes only. (`xml-text-chain` was listed
    # for https://github.com/danbri/factoidal/issues/755 in all three
    # routes, and `xml-markup-chain` in wcanary, until 2026-10-12, when
    # nested entity expansion became a worklist.)
    # regex-replace-groups (5,000 repetitions) overflows at 512 KB, natively
    # and in Node, and runs on the default Node stack (measured 2026-10-13).
    regex-replace-groups)
      case "${2:-}" in canary|wcanary) echo "https://github.com/danbri/factoidal/issues/816" ;; esac ;;
    rdfc-bnode-chain) echo "https://github.com/danbri/factoidal/issues/817" ;;
    # (`sparql-collection` was listed in wcanary for
    # https://github.com/danbri/factoidal/issues/818 until 2026-10-13, when
    # ggpLabeledBnodes, the INSERT DATA blank node label check and the last
    # frame per member of the join chain, became a loop over a work list;
    # native now runs it at 64 KB.)
  esac
}

# score_case <route> <case> <kind> <detail>, with kind ran | overflow | error.
score_case() {
  local route="$1" name="$2" kind="$3" detail="$4" issue
  issue="$(xfail_issue "$name" "$route")"
  if [ -z "$issue" ]; then
    if [ "$kind" = ran ]; then record "$route" "$name" 0 "$detail"
    else record "$route" "$name" 1 "$detail"; fi
  elif [ "$kind" = overflow ]; then
    record "$route" "$name" 0 "xfail: still overflows, tracked ($issue)"
  elif [ "$kind" = ran ]; then
    record "$route" "$name" 1 "UNEXPECTED PASS: flip this xfail and close $issue"
  else
    record "$route" "$name" 1 "xfail case failed without a stack overflow: $detail"
  fi
}

canary_case() { # canary_case <case> <op> <argsfile>
  local name="$1" op="$2" argsfile="$3" out rc
  out="$( run_capped "$TIMEOUT" "${CANARY_PREFIX[@]}" "$CLI" call "$op" "$FIXTURES/$argsfile" 2>&1 )"
  rc=$?
  if printf '%s' "$out" | grep -q 'Stack overflow'; then
    score_case canary "$name" overflow "STACK OVERFLOW under ${CANARY_KB}KB (exit $rc)"
  elif [ "$rc" -ne 0 ]; then
    score_case canary "$name" error "exit $rc under ${CANARY_KB}KB: $(printf '%s' "$out" | head -c 140)"
  elif printf '%s' "$out" | grep -q '"ok":false'; then
    score_case canary "$name" error "engine error under ${CANARY_KB}KB: $(printf '%s' "$out" | head -c 140)"
  else
    score_case canary "$name" ran "ok under ${CANARY_KB}KB"
  fi
}

# ------------------------------------------------------------------ wasm
# The wasm module is a build product (docs/web/hub/assets/l4/l4factoidal.wasm
# and .mjs; gitignored since the 2026-10-09 split; installed by
# tools/fetch-builds.sh --set web or built by formal/lean4/Wasm/build-wasm.sh).
# When it is missing, no wasm case
# can run, and a case that did not run must not read as a case that passed:
# the wasm routes record one failure and score nothing.
WASM_DIR="$ROOT/docs/web/hub/assets/l4"
WASM_OK=1
for f in l4factoidal.js l4factoidal.mjs l4factoidal.wasm; do
  [ -f "$WASM_DIR/$f" ] || WASM_OK=0
done

# wasm_run <case> [stack-size-KB]: runs one case in Node, alone in its process.
# Sets WASM_KIND to ran (the module answered ok:true), overflow (a call-stack
# overflow) or error (no answer, or ok:false for any other reason), and
# WASM_DETAIL. The kind comes from the case's JSON line, never from the
# absence of an error message.
wasm_run() {
  local name="$1" kb="${2:-}" out rc line
  if [ -n "$kb" ]; then
    out="$(run_capped "$TIMEOUT" node --stack-size="$kb" "$HERE/wasm_case.mjs" "$name" "$FIXTURES" 2>&1)"; rc=$?
  else
    out="$(run_capped "$TIMEOUT" node "$HERE/wasm_case.mjs" "$name" "$FIXTURES" 2>&1)"; rc=$?
  fi
  line="$(printf '%s' "$out" | grep '^{' | tail -1)"
  if printf '%s' "$line" | grep -q '"ok":true'; then
    WASM_KIND=ran
    WASM_DETAIL="$(printf '%s' "$line" | python3 -c 'import json,sys;print(str(json.load(sys.stdin).get("ms"))+"ms")' 2>/dev/null)"
  elif printf '%s' "$line" | grep -qi 'call stack size exceeded\|stack overflow'; then
    WASM_KIND=overflow; WASM_DETAIL="call stack overflow"
  else
    WASM_KIND=error
    WASM_DETAIL="node exit $rc: ${line:-$(printf '%s' "$out" | head -c 160)}"
    WASM_DETAIL="$(printf '%s' "$WASM_DETAIL" | head -c 200)"
  fi
}

wasm_case() { # wasm_case <case>: the default Node stack
  wasm_run "$1"
  score_case wasm "$1" "$WASM_KIND" "$WASM_DETAIL"
}

wasm_missing() { # wasm_missing <route>
  record "$1" "wasm module" 1 "NOT SCORED: $WASM_DIR lacks l4factoidal.{js,mjs,wasm}; install it with tools/fetch-builds.sh --set web or build it with formal/lean4/Wasm/build-wasm.sh"
}

CASES=(
  "xml-entities        parseToDatasetJson   args-xml.json"
  "xml-entities-attr   parseToDatasetJson   args-xml-attr.json"
  "xml-entities-dtd    parseToDatasetJson   args-xml-dtd.json"
  "xml-text-chain      parseToDatasetJson   args-xml-text-chain.json"
  "xml-markup-chain    parseToDatasetJson   args-xml-markup-chain.json"
  "turtle-literal      parseToDatasetJson   args-turtle-literal.json"
  "turtle-collection   parseToDatasetJson   args-turtle-collection.json"
  "turtle-predicates   parseToDatasetJson   args-turtle-predicates.json"
  "nquads-one-subject  parseToDatasetJson   args-nquads.json"
  "nquads-long-literal parseToDatasetJson   args-nquads-long-literal.json"
  "sparql-union        queryDataset         args-sparql-union.json"
  "sparql-nested       queryDataset         args-sparql-nested.json"
  "sparql-order-limit  queryDataset         args-sparql-order-limit.json"
  "manifest            storeManifestInspect manifest-args.json"
  "rdfxml-collection   parseToDatasetJson   args-rdfxml-collection.json"
  "sparql-collection   updateDataset        args-sparql-collection.json"
  "sparql-replace-long queryDataset         args-sparql-replace-long.json"
  "regex-replace-groups queryDataset        args-regex-replace-groups.json"
  "rdfc-bnode-chain    canonicalizeToNQuads args-rdfc-bnode-chain.json"
  "delta-log-decode    deltaLogDecode       args-delta-log-decode.json"
  "delta-log-merge     deltaLogMerge        args-delta-log-merge.json"
)

if [ "$ROUTE" = native ] || [ "$ROUTE" = both ]; then
  if [ ! -x "$CLI" ]; then
    echo "=== native: building l4wasm-cli"
    ( cd "$LEAN_DIR" && lake build l4wasm-cli >/dev/null ) || { echo "lake build failed"; exit 2; }
  fi
  echo
  echo "=== native route ($CLI)"
  for row in "${CASES[@]}"; do
    # shellcheck disable=SC2086
    set -- $row
    native_case "$1" "$2" "$3"
  done
fi

# The delta-log fixture is written by gen_cases.py, not by the engine, so a
# run that only "did not overflow" could pass on a log the engine reads as
# torn at its first record. This case checks the decode itself: all 100,000
# batches, one entry each, nothing torn (issue 728).
deltalog_count_case() { # deltalog_count_case <route> <prefix...>
  local route="$1"; shift
  local out rc want='"batches":100000,"entries":100000,"torn":false,"tornBytes":0'
  out="$(run_capped "$TIMEOUT" "$@" "$CLI" call deltaLogDecode "$FIXTURES/args-delta-log-decode.json" 2>&1)"; rc=$?
  if printf '%s' "$out" | grep -q 'Stack overflow'; then
    score_case "$route" delta-log-count overflow "STACK OVERFLOW (exit $rc)"
  elif [ "$rc" -ne 0 ] || ! printf '%s' "$out" | grep -qF "$want"; then
    score_case "$route" delta-log-count error "exit $rc: $(printf '%s' "$out" | head -c 160)"
  else
    score_case "$route" delta-log-count ran "100,000 batches, not torn"
  fi
}
if [ "$ROUTE" = native ] || [ "$ROUTE" = both ]; then
  deltalog_count_case native env
fi

NATIVE_CANARY="not run"
if [ "$CANARY" = 1 ]; then
  echo
  echo "=== canary route (native under ${CANARY_VAR}=${CANARY_KB})"
  if [ ! -x "$CLI" ]; then
    record canary control 1 "native canary NOT SCORED: $CLI does not exist"
    NATIVE_CANARY="NOT SCORED (no l4wasm-cli)"
  elif canary_control; then
    record canary control 0 "$CONTROL_DETAIL"
    NATIVE_CANARY="scored"
    for row in "${CASES[@]}"; do
      set -- $row
      canary_case "$1" "$2" "$3"
    done
    deltalog_count_case canary "${CANARY_PREFIX[@]}"
  else
    record canary control 1 "native canary NOT SCORED: $CONTROL_WHY"
    NATIVE_CANARY="NOT SCORED (control failed)"
    echo "    The wasm/JS canary below does not depend on the native knob and still runs."
  fi
  # The tab overflow is a V8 CALL-STACK overflow, and `node --stack-size` DOES
  # bound that on every platform (measured 2026-09-08: the manifest case throws
  # under a small size before the fix, and passes after). This is the canary
  # for a browser tab; the wasm shadow-stack flag `-sSTACK_SIZE` bounds a
  # DIFFERENT stack and is not needed here. Runs the built module, so a Lean
  # fix reaches it only after Wasm/build-wasm.sh.
  echo
  echo "=== canary route (wasm cases in Node under --stack-size=${CANARY_KB})"
  if [ "$WASM_OK" = 1 ]; then
    for row in "${CASES[@]}"; do
      set -- $row
      wasm_run "$1" "$CANARY_KB"
      score_case wcanary "$1" "$WASM_KIND" "$WASM_DETAIL"
    done
  else
    wasm_missing wcanary
  fi
fi

if [ "$ROUTE" = wasm ] || [ "$ROUTE" = both ]; then
  echo
  echo "=== wasm route (docs/web/hub/assets/l4/l4factoidal.wasm, Node $(node --version))"
  echo "    NOTE: this is the BUILT module. A Lean fix reaches it only"
  echo "    after formal/lean4/Wasm/build-wasm.sh is rerun."
  if [ "$WASM_OK" = 1 ]; then
    for row in "${CASES[@]}"; do
      set -- $row
      wasm_case "$1"
    done
  else
    wasm_missing wasm
  fi
fi

# ------------------------------------------- zstd (Factoidal/qlvr, issue 778)
# The pure-Lean zstd decoder (L4Factoidal.Codec.Zstd) has no op on the
# dispatch ABI; it runs through its own harness, l4qlvr-zstd-check, on one
# frame of 9,600,000 bytes of output (gen_cases.py, zstd-ids.zst). Native
# route at the default stack; canary route under the canary budget once the
# control has passed. https://github.com/danbri/factoidal/issues/778
ZSTD_BIN="$LEAN_DIR/.lake/build/bin/l4qlvr-zstd-check"
zstd_case() { # zstd_case <route> <prefix...>
  local route="$1"; shift
  local f="$FIXTURES/zstd-ids.zst" out rc
  if [ ! -f "$f" ] || [ ! -f "$f.sha256" ]; then
    record "$route" zstd-8mib 1 "fixture missing: gen_cases.py needs the Python zstandard package"
    return
  fi
  if [ ! -x "$ZSTD_BIN" ]; then
    record "$route" zstd-8mib 1 "$ZSTD_BIN does not exist (lake build l4qlvr-zstd-check)"
    return
  fi
  out="$(run_capped "$TIMEOUT" "$@" "$ZSTD_BIN" frame "$f" "$(cat "$f.sha256")" 2>&1)"; rc=$?
  if printf '%s' "$out" | grep -q 'Stack overflow'; then
    score_case "$route" zstd-8mib overflow "STACK OVERFLOW (exit $rc)"
  elif [ "$rc" -ne 0 ]; then
    score_case "$route" zstd-8mib error "exit $rc: $(printf '%s' "$out" | tail -1 | head -c 160)"
  else
    score_case "$route" zstd-8mib ran "$(printf '%s' "$out" | sed -n 2p)"
  fi
}
if [ "$ROUTE" = native ] || [ "$ROUTE" = both ]; then
  echo
  echo "=== zstd frame, native default stack"
  zstd_case native env
fi
if [ "$CANARY" = 1 ]; then
  echo
  echo "=== zstd frame, native under ${CANARY_VAR}=${CANARY_KB}"
  if [ "$CONTROL_OK" = 1 ]; then
    zstd_case canary "${CANARY_PREFIX[@]}"
  else
    record canary zstd-8mib 1 "NOT SCORED: the canary control did not pass"
  fi
fi

# ------------------------- QLever index dump (Factoidal/qlvr, issue 778)
# `l4qlvr dump` decodes every SPO block of the QLever instance (1,781,625
# triples, 39 blocks of up to 31,250 rows; every row loop, the FSST word
# loop, the literal escape loop and the zstd decoder) and prints N-Triples.
# The instance is outside the repository (QLVR_WORK, default
# /home/user/qlvr-work; tools/qlvr/build-instance.sh builds it). Without it
# the case is reported as NOT RUN and not scored.
# `qlvr-join` runs the largest join of the oracle queries,
# tests/qlvr/queries/q07-join-three.rq, through `l4qlvr query`: four scans
# (one of 269,625 rows over 9 PSO blocks), two merge joins and a hash join,
# ORDER BY over 313 rows (the merge sort) and the SPARQL JSON renderer.
QLVR_BIN="$LEAN_DIR/.lake/build/bin/l4qlvr"
QLVR_INST="${QLVR_WORK:-/home/user/qlvr-work}/instance"
qlvr_case() { # qlvr_case <route> <prefix...>
  local route="$1"; shift
  local out="$FIXTURES/qlvr-dump.nt" err="$FIXTURES/qlvr-dump.err" rc lines
  if [ ! -x "$QLVR_BIN" ]; then
    record "$route" qlvr-dump 1 "$QLVR_BIN does not exist (lake build l4qlvr)"
    return
  fi
  run_capped "$TIMEOUT" "$@" "$QLVR_BIN" dump "$QLVR_INST" >"$out" 2>"$err"; rc=$?
  lines="$(wc -l <"$out")"
  rm -f "$out"
  if grep -q 'Stack overflow' "$err"; then
    score_case "$route" qlvr-dump overflow "STACK OVERFLOW (exit $rc)"
  elif [ "$rc" -ne 0 ] || [ "$lines" -ne 1781625 ]; then
    score_case "$route" qlvr-dump error "exit $rc, $lines lines: $(tail -1 "$err" | head -c 160)"
  else
    score_case "$route" qlvr-dump ran "$(tail -1 "$err")"
  fi
}
QLVR_JOIN_RQ="$ROOT/tests/qlvr/queries/q07-join-three.rq"
qlvr_join_case() { # qlvr_join_case <route> <prefix...>
  local route="$1"; shift
  local out="$FIXTURES/qlvr-join.json" err="$FIXTURES/qlvr-join.err" rc rows
  if [ ! -x "$QLVR_BIN" ]; then
    record "$route" qlvr-join 1 "$QLVR_BIN does not exist (lake build l4qlvr)"
    return
  fi
  run_capped "$TIMEOUT" "$@" "$QLVR_BIN" query "$QLVR_INST" --file "$QLVR_JOIN_RQ" >"$out" 2>"$err"; rc=$?
  rows="$(grep -o '"a":' "$out" | wc -l)"
  rm -f "$out"
  if grep -q 'Stack overflow' "$err"; then
    score_case "$route" qlvr-join overflow "STACK OVERFLOW (exit $rc)"
  elif [ "$rc" -ne 0 ] || [ "$rows" -ne 313 ]; then
    score_case "$route" qlvr-join error "exit $rc, $rows rows: $(tail -1 "$err" | head -c 160)"
  else
    score_case "$route" qlvr-join ran "$(tail -1 "$err")"
  fi
}
if [ ! -f "$QLVR_INST/olympics.index.spo" ]; then
  echo
  echo "=== qlvr-dump NOT RUN (not scored): no QLever instance at $QLVR_INST"
else
  if [ "$ROUTE" = native ] || [ "$ROUTE" = both ]; then
    echo
    echo "=== QLever index dump, native default stack"
    qlvr_case native env
    echo
    echo "=== QLever four-pattern join (l4qlvr query q07), native default stack"
    qlvr_join_case native env
  fi
  if [ "$CANARY" = 1 ]; then
    echo
    echo "=== QLever index dump, native under ${CANARY_VAR}=${CANARY_KB}"
    if [ "$CONTROL_OK" = 1 ]; then
      qlvr_case canary "${CANARY_PREFIX[@]}"
      echo
      echo "=== QLever four-pattern join (l4qlvr query q07), native under ${CANARY_VAR}=${CANARY_KB}"
      qlvr_join_case canary "${CANARY_PREFIX[@]}"
    else
      record canary qlvr-dump 1 "NOT SCORED: the canary control did not pass"
      record canary qlvr-join 1 "NOT SCORED: the canary control did not pass"
    fi
  fi
fi

# ------------------------- SBM11 global dictionary (issue 788)
# `l4sbm11-dict-pack` packs gen_cases.py's sbm11-dict.nt (150,000 subjects,
# a 300,000-byte literal) with runs of 20,000 terms: the streaming parse, the
# external sort (sorted runs, k-way merge), the front-coded page encoder and
# decoder over the 300,000-byte key; then `--check` decodes every page and
# looks up every key and every source term.
# https://github.com/danbri/factoidal/issues/788
SBM11_BIN="$LEAN_DIR/.lake/build/bin/l4sbm11-dict-pack"
sbm11_case() { # sbm11_case <route> <prefix...>
  local route="$1"; shift
  local src="$FIXTURES/sbm11-dict.nt" out="$FIXTURES/sbm11-dict-out" rc log
  if [ ! -x "$SBM11_BIN" ]; then
    record "$route" sbm11-dict 1 "$SBM11_BIN does not exist (lake build l4sbm11-dict-pack)"
    return
  fi
  rm -rf "$out"
  log="$(run_capped "$TIMEOUT" "$@" "$SBM11_BIN" "$src" "$out" --run-terms 20000 2>&1)"; rc=$?
  if [ "$rc" -eq 0 ]; then
    log="$log
$(run_capped "$TIMEOUT" "$@" "$SBM11_BIN" --check "$src" "$out" 2>&1)"; rc=$?
  fi
  rm -rf "$out"
  if printf '%s' "$log" | grep -q 'Stack overflow'; then
    score_case "$route" sbm11-dict overflow "STACK OVERFLOW (exit $rc)"
  elif [ "$rc" -ne 0 ] || ! printf '%s' "$log" | grep -q 'failures=0'; then
    score_case "$route" sbm11-dict error "exit $rc: $(printf '%s' "$log" | tail -1 | head -c 160)"
  else
    score_case "$route" sbm11-dict ran "$(printf '%s' "$log" | grep -o 'terms=[0-9]* pages=[0-9]*' | head -1); $(printf '%s' "$log" | grep -o 'runs=[0-9]*' | head -1); check failures=0"
  fi
}
if [ "$ROUTE" = native ] || [ "$ROUTE" = both ]; then
  echo
  echo "=== SBM11 dictionary pack and check, native default stack"
  sbm11_case native env
fi
if [ "$CANARY" = 1 ]; then
  echo
  echo "=== SBM11 dictionary pack and check, native under ${CANARY_VAR}=${CANARY_KB}"
  if [ "$CONTROL_OK" = 1 ]; then
    sbm11_case canary "${CANARY_PREFIX[@]}"
  else
    record canary sbm11-dict 1 "NOT SCORED: the canary control did not pass"
  fi
fi

# ------------------------- SBM11 triple terms (issue 792 item 1)
# `l4sbm11-dict-pack --nest-check 300000`: an RDF 1.2 triple term nested
# 300,000 deep in the object position (a 5,100,011-byte class-7 key) through
# `normalizeTerm` (the innermost language tag folded), the class-7 key encoder
# `termKeyBytes?`, the decoder `decodeKey?` and the encoder again; the second
# key must be the bytes of the first. The nesting is above the wasm module's
# 8 MB stack at 32 bytes a frame (262,144), and far above this canary's.
# https://github.com/danbri/factoidal/issues/792
sbm11_tt_case() { # sbm11_tt_case <route> <prefix...>
  local route="$1"; shift
  local rc log
  if [ ! -x "$SBM11_BIN" ]; then
    record "$route" sbm11-triple-term 1 "$SBM11_BIN does not exist (lake build l4sbm11-dict-pack)"
    return
  fi
  log="$(run_capped "$TIMEOUT" "$@" "$SBM11_BIN" --nest-check 300000 2>&1)"; rc=$?
  if printf '%s' "$log" | grep -q 'Stack overflow'; then
    score_case "$route" sbm11-triple-term overflow "STACK OVERFLOW (exit $rc)"
  elif [ "$rc" -ne 0 ] || ! printf '%s' "$log" | grep -q 'depth=300000 .*failures=0'; then
    score_case "$route" sbm11-triple-term error "exit $rc: $(printf '%s' "$log" | tail -1 | head -c 160)"
  else
    score_case "$route" sbm11-triple-term ran "$(printf '%s' "$log" | grep -o 'depth=[0-9]* key-bytes=[0-9]*' | head -1); round trip failures=0"
  fi
}
if [ "$ROUTE" = native ] || [ "$ROUTE" = both ]; then
  echo
  echo "=== SBM11 triple term nested 300,000 deep, key encode and decode, native default stack"
  sbm11_tt_case native env
fi
if [ "$CANARY" = 1 ]; then
  echo
  echo "=== SBM11 triple term nested 300,000 deep, key encode and decode, native under ${CANARY_VAR}=${CANARY_KB}"
  if [ "$CONTROL_OK" = 1 ]; then
    sbm11_tt_case canary "${CANARY_PREFIX[@]}"
  else
    record canary sbm11-triple-term 1 "NOT SCORED: the canary control did not pass"
  fi
fi

# ------------------------- DLOG version 2: a deep triple term in an entry (issue 792 item 1)
# `l4block-delta-log --nest-check 300000`: one DLB1 batch whose entry holds an
# RDF 1.2 triple term nested 300,000 deep in the object position, the
# innermost object a directional literal, through the DLOG version 2 term
# codec: the append plan of a new log (`appendPlan?`, the encoder a loop over
# the object chain), `parseLogChecked` (the decoder a loop with a stack of the
# subjects and predicates) and the append plan of the decoded batch, whose
# bytes must be the first ones. The nesting is above the wasm module's 8 MB
# stack at 32 bytes a frame (262,144), and far above this canary's.
# https://github.com/danbri/factoidal/issues/792
DLOG_BIN="$LEAN_DIR/.lake/build/bin/l4block-delta-log"
dlog_tt_case() { # dlog_tt_case <route> <prefix...>
  local route="$1"; shift
  local rc log
  if [ ! -x "$DLOG_BIN" ]; then
    record "$route" delta-log-triple-term 1 "$DLOG_BIN does not exist (lake build l4block-delta-log)"
    return
  fi
  log="$(run_capped "$TIMEOUT" "$@" "$DLOG_BIN" --nest-check 300000 2>&1)"; rc=$?
  if printf '%s' "$log" | grep -q 'Stack overflow'; then
    score_case "$route" delta-log-triple-term overflow "STACK OVERFLOW (exit $rc)"
  elif [ "$rc" -ne 0 ] || ! printf '%s' "$log" | grep -q 'depth=300000 .*failures=0'; then
    score_case "$route" delta-log-triple-term error "exit $rc: $(printf '%s' "$log" | tail -1 | head -c 160)"
  else
    score_case "$route" delta-log-triple-term ran "$(printf '%s' "$log" | grep -o 'depth=[0-9]* log-bytes=[0-9]* version=[0-9]*' | head -1); round trip failures=0"
  fi
}
if [ "$ROUTE" = native ] || [ "$ROUTE" = both ]; then
  echo
  echo "=== DLOG version 2, a triple term nested 300,000 deep in an entry, native default stack"
  dlog_tt_case native env
fi
if [ "$CANARY" = 1 ]; then
  echo
  echo "=== DLOG version 2, a triple term nested 300,000 deep in an entry, native under ${CANARY_VAR}=${CANARY_KB}"
  if [ "$CONTROL_OK" = 1 ]; then
    dlog_tt_case canary "${CANARY_PREFIX[@]}"
  else
    record canary delta-log-triple-term 1 "NOT SCORED: the canary control did not pass"
  fi
fi

# ------------------------- SBM11 permutations (issue 789)
# `l4sbm11-pack` packs the same sbm11-dict.nt (600,001 triples) with runs of
# 20,000 terms, row runs of 20,000 rows (the external sort of phase 3 writes
# and merges 30 or more runs per permutation) and blocks of 65,536 rows (the
# largest block encode, and the frame decode the packer runs on every frame);
# then `l4sbm11 verify` decodes every block of the four permutations, checks
# PRM1, re-encodes every frame and compares the quad digests, and
# `l4sbm11 dump-ids` reads every SPO block.
# https://github.com/danbri/factoidal/issues/789
SBM11P_BIN="$LEAN_DIR/.lake/build/bin/l4sbm11-pack"
SBM11C_BIN="$LEAN_DIR/.lake/build/bin/l4sbm11"
sbm11_perm_case() { # sbm11_perm_case <route> <prefix...>
  local route="$1"; shift
  local src="$FIXTURES/sbm11-dict.nt" out="$FIXTURES/sbm11-perm-out" rc log rows
  if [ ! -x "$SBM11P_BIN" ] || [ ! -x "$SBM11C_BIN" ]; then
    record "$route" sbm11-perm 1 "l4sbm11-pack or l4sbm11 does not exist (lake build l4sbm11-pack l4sbm11)"
    return
  fi
  rm -rf "$out"
  log="$(run_capped "$TIMEOUT" "$@" "$SBM11P_BIN" "$src" "$out" --run-terms 20000 --sort-rows 20000 --block-rows 65536 2>&1)"; rc=$?
  if [ "$rc" -eq 0 ]; then
    log="$log
$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" verify "$out" 2>&1)"; rc=$?
  fi
  if [ "$rc" -eq 0 ]; then
    rows="$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" dump-ids "$out" spo 2>>"$FIXTURES/sbm11-perm.err" | wc -l)"
    rc=$?
    log="$log
dump-ids rows=$rows"
    if [ "$(cat "$FIXTURES/sbm11-perm.err" 2>/dev/null | grep -c 'Stack overflow')" -gt 0 ]; then
      log="$log
Stack overflow in dump-ids"
    fi
    rm -f "$FIXTURES/sbm11-perm.err"
  fi
  rm -rf "$out"
  if printf '%s' "$log" | grep -q 'Stack overflow'; then
    score_case "$route" sbm11-perm overflow "STACK OVERFLOW (exit $rc)"
  elif [ "$rc" -ne 0 ] || ! printf '%s' "$log" | grep -q 'admitted failures=0' || ! printf '%s' "$log" | grep -q 'dump-ids rows=600001'; then
    score_case "$route" sbm11-perm error "exit $rc: $(printf '%s' "$log" | grep -m1 'FAIL\|l4sbm11' | head -c 160)"
  else
    score_case "$route" sbm11-perm ran "$(printf '%s' "$log" | grep -o 'quads=[0-9]*' | head -1); $(printf '%s' "$log" | grep -o 'spo blocks=[0-9]*' | head -1); verify admitted; dump-ids rows=600001"
  fi
}
if [ "$ROUTE" = native ] || [ "$ROUTE" = both ]; then
  echo
  echo "=== SBM11 permutation pack, verify and dump, native default stack"
  sbm11_perm_case native env
fi
if [ "$CANARY" = 1 ]; then
  echo
  echo "=== SBM11 permutation pack, verify and dump, native under ${CANARY_VAR}=${CANARY_KB}"
  if [ "$CONTROL_OK" = 1 ]; then
    sbm11_perm_case canary "${CANARY_PREFIX[@]}"
  else
    record canary sbm11-perm 1 "NOT SCORED: the canary control did not pass"
  fi
fi

# ------------------------- SBM11 export (issue 837 item 6)
# `l4sbm11 export` writes the sbm11-dict.nt generation (600,001 quads, 150,000
# subjects, a 300,000-byte literal) as N-Quads, Turtle and TriG. The writers of
# the serialiser layer (L4Factoidal/RDF/Sink.lean) are loops over the quads of
# the SPO permutation: no frame for each quad, subject, predicate or object, and
# the 300,000-byte literal goes through the string escape of each writer. The
# N-Quads export has 600,001 lines. The Turtle and the TriG export pack again to
# the data files of the first generation (every file but the manifest).
# https://github.com/danbri/factoidal/issues/837
sbm11_export_case() { # sbm11_export_case <route> <prefix...>
  local route="$1"; shift
  local src="$FIXTURES/sbm11-dict.nt" out="$FIXTURES/sbm11-export-out" rc=0 log fmt lines f same=1
  if [ ! -x "$SBM11P_BIN" ] || [ ! -x "$SBM11C_BIN" ]; then
    record "$route" sbm11-export 1 "l4sbm11-pack or l4sbm11 does not exist (lake build l4sbm11-pack l4sbm11)"
    return
  fi
  rm -rf "$out" "$out-nquads" "$out-turtle" "$out-trig" "$out-turtle.gen" "$out-trig.gen"
  log="$(run_capped "$TIMEOUT" "$@" "$SBM11P_BIN" "$src" "$out" --run-terms 20000 --sort-rows 20000 --block-rows 65536 2>&1)"; rc=$?
  for fmt in nquads turtle trig; do
    [ "$rc" -eq 0 ] || break
    log="$log
$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" export "$out" --format "$fmt" --out "$out-$fmt" 2>&1)"; rc=$?
  done
  lines=0
  if [ "$rc" -eq 0 ]; then
    lines="$(wc -l <"$out-nquads")"
    for fmt in turtle trig; do
      [ "$rc" -eq 0 ] || break
      log="$log
$(run_capped "$TIMEOUT" "$@" "$SBM11P_BIN" "$out-$fmt" "$out-$fmt.gen" --format "$fmt" --run-terms 20000 --sort-rows 20000 --block-rows 65536 2>&1)"; rc=$?
      if [ "$rc" -eq 0 ]; then
        for f in $(ls "$out" | grep -v '^manifest.sbm11$'); do
          cmp -s "$out/$f" "$out-$fmt.gen/$f" || same=0
        done
      fi
    done
  fi
  rm -rf "$out" "$out-nquads" "$out-turtle" "$out-trig" "$out-turtle.gen" "$out-trig.gen"
  if printf '%s' "$log" | grep -q 'Stack overflow'; then
    score_case "$route" sbm11-export overflow "STACK OVERFLOW (exit $rc)"
  elif [ "$rc" -ne 0 ] || [ "$lines" != 600001 ] || [ "$same" != 1 ]; then
    score_case "$route" sbm11-export error "exit $rc; N-Quads lines $lines (expected 600001); packed again equal: $same; $(printf '%s' "$log" | grep -m1 'l4sbm11' | head -c 120)"
  else
    score_case "$route" sbm11-export ran "N-Quads, Turtle and TriG export of 600,001 quads; N-Quads lines=600001; Turtle and TriG pack again to the same data files"
  fi
}
if [ "$ROUTE" = native ] || [ "$ROUTE" = both ]; then
  echo
  echo "=== SBM11 export in N-Quads, Turtle and TriG, native default stack"
  sbm11_export_case native env
fi
if [ "$CANARY" = 1 ]; then
  echo
  echo "=== SBM11 export in N-Quads, Turtle and TriG, native under ${CANARY_VAR}=${CANARY_KB}"
  if [ "$CONTROL_OK" = 1 ]; then
    sbm11_export_case canary "${CANARY_PREFIX[@]}"
  else
    record canary sbm11-export 1 "NOT SCORED: the canary control did not pass"
  fi
fi

# ------------------------------- SBM11 id query path (issue 790)
# `l4sbm11 query` on the sbm11-dict.nt generation (600,001 quads, blocks of
# 65,536 rows): a merge join of 150,000 rows with each side and a COUNT over
# it, ORDER BY DESC with LIMIT over 150,000 rows (top-k), GROUP BY over
# 150,000 rows (1,000 groups), STRSTARTS on 150,000 labels (61,111 match,
# by rank ranges of the dictionary) counted and streamed out, and the
# 300,000-byte literal written as SPARQL JSON (the key printer's escape
# loop). The block decode, the joins, the sort and the printer each run over
# input-proportional data. https://github.com/danbri/factoidal/issues/790
# OPTIONAL (issue 775): a left outer join of the 150,000 labels with the
# 150,000 p:n rows, filtered in the group to 1,000 (COUNT(*) 150,000,
# COUNT(?n) 1,000) and to 2 (ORDER BY DESC(?n) with unbound last, LIMIT 3):
# the merge pairs, `OptJoin.outerPairs` and `gatherOpt` over 150,000 rows;
# every query of the case must run on the id path.
# Issue 823: SUM and MAX over the 150,000 joined rows (the rows decoded by
# `IdQuery.decodeRowsM`, then the reference `selectPost`), a REGEX (a residual
# FILTER) counted over the 150,000 labels, an ASK whose REGEX no joined row
# passes, and ORDER BY an expression (`selectPost` over 150,000 rows).
sbm11_query_case() { # sbm11_query_case <route> <prefix...>
  local route="$1"; shift
  local src="$FIXTURES/sbm11-dict.nt" out="$FIXTURES/sbm11-query-out" rc log r q
  local P='PREFIX p: <http://example.org/p/> '
  if [ ! -x "$SBM11P_BIN" ] || [ ! -x "$SBM11C_BIN" ]; then
    record "$route" sbm11-query 1 "l4sbm11-pack or l4sbm11 does not exist (lake build l4sbm11-pack l4sbm11)"
    return
  fi
  if [ ! -f "$out/manifest.sbm11" ]; then
    rm -rf "$out"
    if ! "$SBM11P_BIN" "$src" "$out" --block-rows 65536 >/dev/null 2>&1; then
      record "$route" sbm11-query 1 "l4sbm11-pack failed"
      return
    fi
  fi
  log=""
  rc=0
  for q in \
    "SELECT (COUNT(*) AS ?c) WHERE { ?s p:label ?l . ?s p:n ?n }" \
    "SELECT ?s ?n WHERE { ?s p:n ?n . ?s p:m ?m } ORDER BY DESC(?n) ?s LIMIT 3" \
    "SELECT ?m (COUNT(*) AS ?c) WHERE { ?s p:m ?m } GROUP BY ?m ORDER BY DESC(?c) ?m LIMIT 2" \
    "SELECT (COUNT(*) AS ?c) WHERE { ?s p:label ?l FILTER(STRSTARTS(?l, \"label 1\")) }" \
    "SELECT ?l WHERE { ?s p:label ?l FILTER(STRSTARTS(?l, \"label 1\")) }" \
    "SELECT ?o WHERE { <http://example.org/sbm11/big> p:text ?o }" \
    "SELECT (COUNT(*) AS ?c) (COUNT(?n) AS ?k) WHERE { ?s p:label ?l OPTIONAL { ?s p:n ?n FILTER(?n < 1000) } }" \
    "SELECT ?n WHERE { ?s p:label ?l OPTIONAL { ?s p:n ?n FILTER(?n >= 149998) } } ORDER BY DESC(?n) LIMIT 3"; do
    r="$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" query "$out" "$P$q" 2>&1)"; rc=$?
    log="$log
$(printf '%s' "$r" | head -c 300) ... $(printf '%s' "$r" | grep -o 'sbm11-query: path=[a-z]*; rows [0-9]*') rc=$rc"
    [ "$rc" -ne 0 ] && break
  done
  # issue 809: joins with candidates (--sip always): the find and gather
  # loops of Storage/Sbm11/Sip.lean over blocks of 65,536 rows, every row a
  # candidate (150,000 candidates), and a left outer join with candidates
  local sip=""
  if [ "$rc" -eq 0 ]; then
    for q in \
      "SELECT (COUNT(*) AS ?c) WHERE { ?s p:label ?l . ?s p:n ?n }" \
      "SELECT (COUNT(*) AS ?c) (COUNT(?n) AS ?k) WHERE { ?s p:label ?l OPTIONAL { ?s p:n ?n FILTER(?n < 1000) } }"; do
      r="$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" query "$out" "$P$q" --sip always --explain 2>&1)"; rc=$?
      sip="$sip
$(printf '%s' "$r" | grep -o '"value":"[0-9]*"' | tr '\n' ' ') $(printf '%s' "$r" | grep -o 'sideways ?s: [0-9]* candidates' | head -1) $(printf '%s' "$r" | grep -o 'Stack overflow' | head -1) rc=$rc"
      [ "$rc" -ne 0 ] && break
    done
  fi
  # issue 823: the reference post-processing and residual FILTERs on ids
  local post=""
  if [ "$rc" -eq 0 ]; then
    for q in \
      "SELECT (SUM(?n) AS ?t) (MAX(?n) AS ?mx) WHERE { ?s p:label ?l . ?s p:n ?n }" \
      "SELECT (COUNT(*) AS ?c) WHERE { ?s p:label ?l FILTER(REGEX(?l, \"^label 1\")) }" \
      "ASK { ?s p:label ?l . ?s p:n ?n FILTER(REGEX(?l, \"^nomatch\")) }" \
      "SELECT (STRLEN(?l) AS ?k) WHERE { ?s p:label ?l } ORDER BY DESC(?k) LIMIT 1"; do
      r="$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" query "$out" "$P$q" 2>&1)"; rc=$?
      post="$post
$(printf '%s' "$r" | grep -o '"value":"[0-9]*"\|"boolean":[a-z]*' | tr '\n' ' ') $(printf '%s' "$r" | grep -o 'path=[a-z]*' | head -1) $(printf '%s' "$r" | grep -o 'Stack overflow' | head -1) rc=$rc"
      [ "$rc" -ne 0 ] && break
    done
  fi
  log="$log$sip$post"
  if printf '%s' "$log" | grep -q 'Stack overflow'; then
    score_case "$route" sbm11-query overflow "STACK OVERFLOW (exit $rc)"
  elif [ "$rc" -ne 0 ] || ! printf '%s' "$log" | grep -q '"value":"150000"' || ! printf '%s' "$log" | grep -q '"value":"61111"' \
      || ! printf '%s' "$log" | grep -q 'path=ids; rows 61111' \
      || ! printf '%s' "$log" | grep -q '"value":"1000"' || ! printf '%s' "$log" | grep -q '"value":"149998"' \
      || printf '%s' "$log" | grep -q 'path=reference' \
      || [ "$(printf '%s' "$sip" | grep -c '"value":"150000" .*sideways ?s: 150000 candidates')" -ne 2 ] \
      || ! printf '%s' "$sip" | grep -q '"value":"1000"' \
      || ! printf '%s' "$post" | grep -qE '"value":"11249925000" "value":"149999" +path=ids' \
      || ! printf '%s' "$post" | grep -qE '"value":"61111" +path=ids' \
      || ! printf '%s' "$post" | grep -qE '"boolean":false +path=ids' \
      || ! printf '%s' "$post" | grep -qE '"value":"12" +path=ids'; then
    score_case "$route" sbm11-query error "exit $rc: $(printf '%s' "$log" | grep -m1 'l4sbm11\|rc=[1-9]' | head -c 160)"
  else
    score_case "$route" sbm11-query ran "merge join of 150000 rows; STRSTARTS 61111 rows streamed; 300000-byte literal written; OPTIONAL left outer join of 150000 rows (COUNT, ORDER BY); both joins again with 150000 candidates (issue 809); SUM and MAX over 150000 decoded rows, REGEX counted over 150000 labels, ASK false, ORDER BY an expression (issue 823)"
  fi
}
if [ "$ROUTE" = native ] || [ "$ROUTE" = both ]; then
  echo
  echo "=== SBM11 id query path, native default stack"
  sbm11_query_case native env
fi
if [ "$CANARY" = 1 ]; then
  echo
  echo "=== SBM11 id query path, native under ${CANARY_VAR}=${CANARY_KB}"
  if [ "$CONTROL_OK" = 1 ]; then
    sbm11_query_case canary "${CANARY_PREFIX[@]}"
  else
    record canary sbm11-query 1 "NOT SCORED: the canary control did not pass"
  fi
fi
rm -rf "$FIXTURES/sbm11-query-out"

# ------------------------------- SBM11 delta overlay (issue 791)
# The sbm11-dict.nt generation (600,001 quads, blocks of 65,536 rows), then
# gen_cases.py's two updates: DELETE DATA of N_DELTA (4,000) p:n quads and
# INSERT DATA of 4,000 new p:n values for the same subjects (inside the base
# blocks) and 4,000 quads of new subjects with new labels (overlay ids, after
# every base id), 8,000 quads in one request (1,000 and 2,000 until the
# SPARQL tokenizer became linear, https://github.com/danbri/factoidal/issues/802).
# Replayed at every open (12,000 entries), merged into the PSO scans
# block by block (`Overlay.mergeRows` over whole 65,536-row blocks), counted,
# sorted, filtered; then `l4sbm11 compact` (two scans of the overlaid SPO
# permutation, the term run, the packer's phases 2 and 3) and a count on the
# compacted generation. https://github.com/danbri/factoidal/issues/791
sbm11_delta_case() { # sbm11_delta_case <route> <prefix...>
  local route="$1"; shift
  local src="$FIXTURES/sbm11-dict.nt" col="$FIXTURES/sbm11-delta-col" rc log r q
  local P='PREFIX p: <http://example.org/p/> '
  if [ ! -x "$SBM11P_BIN" ] || [ ! -x "$SBM11C_BIN" ]; then
    record "$route" sbm11-delta 1 "l4sbm11-pack or l4sbm11 does not exist (lake build l4sbm11-pack l4sbm11)"
    return
  fi
  rm -rf "$col"
  if ! "$SBM11P_BIN" "$src" "$col/gen" --block-rows 65536 >/dev/null 2>&1 \
      || ! "$SBM11C_BIN" activate "$col" gen >/dev/null 2>&1; then
    record "$route" sbm11-delta 1 "l4sbm11-pack or activate failed"
    return
  fi
  log=""
  rc=0
  for u in "$FIXTURES/sbm11-delta-del-$N_DELTA.ru" "$FIXTURES/sbm11-delta-ins-$N_DELTA.ru"; do
    r="$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" update "$col" --file "$u" 2>&1)"; rc=$?
    log="$log
$(printf '%s' "$r" | head -c 300) rc=$rc"
    [ "$rc" -ne 0 ] && break
  done
  if [ "$rc" -eq 0 ]; then
    for q in \
      "SELECT (COUNT(*) AS ?c) WHERE { ?s p:n ?n }" \
      "SELECT ?s ?n WHERE { ?s p:n ?n } ORDER BY DESC(?n) LIMIT 1" \
      "SELECT (COUNT(*) AS ?c) WHERE { ?s p:label ?l }" \
      "SELECT ?s WHERE { ?s p:label ?l FILTER(STRSTARTS(?l, \"new 99\")) }"; do
      r="$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" query "$col" "$P$q" 2>&1)"; rc=$?
      log="$log
$(printf '%s' "$r" | head -c 300) ... $(printf '%s' "$r" | grep -o 'sbm11-query: path=[a-z]*; rows [0-9]*') rc=$rc"
      [ "$rc" -ne 0 ] && break
    done
  fi
  if [ "$rc" -eq 0 ]; then
    r="$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" compact "$col" "$col/gen2" 2>&1)"; rc=$?
    log="$log
$(printf '%s' "$r" | grep -o 'quads=[0-9]* terms=[0-9]*' | head -1) rc=$rc"
  fi
  if [ "$rc" -eq 0 ]; then
    r="$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" query "$col/gen2" "${P}SELECT (COUNT(*) AS ?c) WHERE { ?s p:label ?l }" 2>&1)"; rc=$?
    log="$log
compacted: $(printf '%s' "$r" | head -c 300) rc=$rc"
  fi
  if printf '%s' "$log" | grep -q 'Stack overflow'; then
    score_case "$route" sbm11-delta overflow "STACK OVERFLOW (exit $rc)"
  elif [ "$rc" -ne 0 ] || ! printf '%s' "$log" | grep -q '"value":"150000"' \
      || ! printf '%s' "$log" | grep -q "\"value\":\"$((1000000 + N_DELTA - 1))\"" \
      || [ "$(printf '%s' "$log" | grep -c "\"value\":\"$((150000 + N_DELTA))\"")" -ne 2 ] \
      || ! printf '%s' "$log" | grep -q 'path=ids; rows 11'; then
    score_case "$route" sbm11-delta error "exit $rc: $(printf '%s' "$log" | grep -m1 'l4sbm11\|rc=[1-9]' | head -c 160)"
  else
    score_case "$route" sbm11-delta ran "$((3 * N_DELTA)) entries replayed ($N_DELTA and $((2 * N_DELTA)) quads per request); 65536-row blocks merged; counts 150000 and $((150000 + N_DELTA)); compacted count $((150000 + N_DELTA))"
  fi
  rm -rf "$col"
}
if [ "$ROUTE" = native ] || [ "$ROUTE" = both ]; then
  echo
  echo "=== SBM11 delta overlay, native default stack"
  sbm11_delta_case native env
fi
if [ "$CANARY" = 1 ]; then
  echo
  echo "=== SBM11 delta overlay, native under ${CANARY_VAR}=${CANARY_KB}"
  if [ "$CONTROL_OK" = 1 ]; then
    sbm11_delta_case canary "${CANARY_PREFIX[@]}"
  else
    record canary sbm11-delta 1 "NOT SCORED: the canary control did not pass"
  fi
fi

# The update with a WHERE clause and a template blank node (issues 849 and 850) on
# the same 600,001-quad generation: one DELETE/INSERT whose WHERE clause (a numeric
# FILTER) has N_WHERE (12,000) solutions removes N_WHERE p:m quads and adds 3 *
# N_WHERE quads (a p:m2 quad, and a p:ref and a p:of quad around a fresh blank node
# for each solution), in one batch of 48,000 entries. The lists of that length
# (solutions, instantiated quads, entries), the 12,000 label draws and the decoder of
# a batch of that many entries must not take a stack frame for each element (until
# 2026-10-14 the decoder of a version 1 batch did, and every open of the log overflowed
# a 512 KB stack). The first query replays the log: COUNT(DISTINCT ?r) is N_WHERE only
# when the supply drew N_WHERE labels. Then `l4sbm11 compact` folds the log, and
# three queries count on the new generation. Until 2026-10-14 each replay cost one
# dictionary lookup for each term of each entry (https://github.com/danbri/factoidal/issues/858)
# and the case replayed the log twice only; the replay now looks the distinct terms up in
# dictionary order. The reader and the writer of the log hold it as a `ByteArray`
# (`Storage/DeltaLogBytes.lean`, https://github.com/danbri/factoidal/issues/851 and
# https://github.com/danbri/factoidal/issues/857), and each loop over its bytes is a tail call.
sbm11_update_where_case() { # sbm11_update_where_case <route> <prefix...>
  local route="$1"; shift
  local src="$FIXTURES/sbm11-dict.nt" col="$FIXTURES/sbm11-where-col" rc log r q
  local P='PREFIX p: <http://example.org/p/> '
  if [ ! -x "$SBM11P_BIN" ] || [ ! -x "$SBM11C_BIN" ]; then
    record "$route" sbm11-update-where 1 "l4sbm11-pack or l4sbm11 does not exist (lake build l4sbm11-pack l4sbm11)"
    return
  fi
  rm -rf "$col"
  if ! "$SBM11P_BIN" "$src" "$col/gen" --block-rows 65536 >/dev/null 2>&1 \
      || ! "$SBM11C_BIN" activate "$col" gen >/dev/null 2>&1; then
    record "$route" sbm11-update-where 1 "l4sbm11-pack or activate failed"
    return
  fi
  log=""
  r="$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" update "$col" --file "$FIXTURES/sbm11-update-where-$N_WHERE.ru" 2>&1)"; rc=$?
  log="$log
$(printf '%s' "$r" | head -c 300) rc=$rc"
  if [ "$rc" -eq 0 ]; then
    r="$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" query "$col" "${P}SELECT (COUNT(DISTINCT ?r) AS ?c) WHERE { ?s p:ref ?r }" 2>&1)"; rc=$?
    log="$log
overlay: $(printf '%s' "$r" | head -c 300) ... $(printf '%s' "$r" | grep -o 'sbm11-query: path=[a-z]*; rows [0-9]*') rc=$rc"
  fi
  if [ "$rc" -eq 0 ]; then
    r="$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" compact "$col" "$col/gen2" 2>&1)"; rc=$?
    log="$log
$(printf '%s' "$r" | grep -o 'quads=[0-9]* terms=[0-9]*' | head -1) rc=$rc"
  fi
  if [ "$rc" -eq 0 ]; then
    for q in \
      "SELECT (COUNT(*) AS ?c) WHERE { ?s p:m2 ?m }" \
      "SELECT (COUNT(DISTINCT ?r) AS ?c) WHERE { ?s p:ref ?r }" \
      "SELECT (COUNT(*) AS ?c) WHERE { ?s p:m ?m }"; do
      r="$(run_capped "$TIMEOUT" "$@" "$SBM11C_BIN" query "$col/gen2" "$P$q" 2>&1)"; rc=$?
      log="$log
compacted: $(printf '%s' "$r" | head -c 300) rc=$rc"
      [ "$rc" -ne 0 ] && break
    done
  fi
  if printf '%s' "$log" | grep -q 'Stack overflow'; then
    score_case "$route" sbm11-update-where overflow "STACK OVERFLOW (exit $rc)"
  elif [ "$rc" -ne 0 ] \
      || [ "$(printf '%s' "$log" | grep -c "\"value\":\"$N_WHERE\"")" -ne 3 ] \
      || ! printf '%s' "$log" | grep -q "\"value\":\"$((150000 - N_WHERE))\"" \
      || ! printf '%s' "$log" | grep -q 'where path=ids solutions=' ; then
    score_case "$route" sbm11-update-where error "exit $rc: $(printf '%s' "$log" | grep -m1 'l4sbm11\|rc=[1-9]' | head -c 160)"
  else
    score_case "$route" sbm11-update-where ran "$N_WHERE solutions on the id path, $((4 * N_WHERE)) entries in one batch replayed and compacted, $N_WHERE fresh blank nodes (distinct on the overlay and after compaction); counts $N_WHERE and $((150000 - N_WHERE)) on the new generation"
  fi
  rm -rf "$col"
}
if [ "$ROUTE" = native ] || [ "$ROUTE" = both ]; then
  echo
  echo "=== SBM11 update with a WHERE clause, native default stack"
  sbm11_update_where_case native env
fi
if [ "$CANARY" = 1 ]; then
  echo
  echo "=== SBM11 update with a WHERE clause, native under ${CANARY_VAR}=${CANARY_KB}"
  if [ "$CONTROL_OK" = 1 ]; then
    sbm11_update_where_case canary "${CANARY_PREFIX[@]}"
  else
    record canary sbm11-update-where 1 "NOT SCORED: the canary control did not pass"
  fi
fi

# ------------------------------- surfaces the shipped ABI does not reach
echo
echo "=== not reachable from a shipped surface (reported, not scored)"
echo "    jsonld-nested   5000-deep JSON-LD: the wasm/CLI parse op answers"
echo "                    \"JSON-LD is not in the Lean engine's v1 surface\""
echo "                    (Wasm/Ops/Parse.lean). Fixture is generated at"
echo "                    \$FIXTURES/jsonld-nested.jsonld for the l4jsonld-probe."
echo "    shacl-shapes    5000-shape SHACL graph: no SHACL op on the dispatch"
echo "                    ABI. Fixture at \$FIXTURES/shacl-shapes.ttl for l4shacl."

echo
[ "$CANARY" = 1 ] && echo "native canary: $NATIVE_CANARY (${CANARY_VAR}=${CANARY_KB})"
echo "stack stress: $PASS pass, $FAIL fail (out of $TOTAL)"
[ "$FAIL" -eq 0 ]
