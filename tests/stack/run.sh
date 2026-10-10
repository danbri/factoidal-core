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
    # No case is listed today.
  esac
}

# score_case <route> <case> <kind> <detail>, with kind ran | overflow | error.
score_case() {
  local route="$1" name="$2" kind="$3" detail="$4" issue
  issue="$(xfail_issue "$name")"
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
  "turtle-literal      parseToDatasetJson   args-turtle-literal.json"
  "turtle-collection   parseToDatasetJson   args-turtle-collection.json"
  "turtle-predicates   parseToDatasetJson   args-turtle-predicates.json"
  "nquads-one-subject  parseToDatasetJson   args-nquads.json"
  "sparql-union        queryDataset         args-sparql-union.json"
  "sparql-nested       queryDataset         args-sparql-nested.json"
  "manifest            storeManifestInspect manifest-args.json"
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
