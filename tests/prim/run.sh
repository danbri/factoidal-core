#!/usr/bin/env bash
#
# tests/prim/run.sh — differential test of L4Factoidal.Prim.Bytes on every
# target this container can build (https://github.com/danbri/factoidal/issues/797).
#
# `Prim.Bytes.stU64LE` is an `@[extern c inline]` primitive: the code that runs
# is a C expression, trusted, with the Lean reference `stU64LERef`. The test
# executable `l4prim-test` (Harness/PrimBytesTest.lean) compares the two on
# random and edge-case inputs (positions size-8, size-7, 0, past the end, the
# USize wrap-around; shared and exclusive arrays) and checks read after write.
#
#   (a) native  formal/lean4/.lake/build/bin/l4prim-test (clang, USize 64 bits).
#   (b) wasm32  the same generated C compiled by emcc (tools/lean-wasm-exe.sh,
#               USize 32 bits), run by node. Not scored, with the reason
#               printed, when emcc or the wasm runtime objects of
#               formal/lean4/Wasm/build-wasm.sh are absent; PRIM_REQUIRE_WASM=1
#               makes that an exit 2.
#
# Needs: `lake build l4prim-test` in formal/lean4. Prints "N pass, M fail
# (out of T)" per target; exits 0 only when every target run passes, 1 on a
# failure, 2 when an input is missing.
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="$ROOT/formal/lean4/.lake/build/bin/l4prim-test"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/prim-test.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT

[ -x "$BIN" ] || { echo "prim: $BIN missing (cd formal/lean4 && lake build l4prim-test)"; exit 2; }

fails=0
score() {   # $1 target, $2 output file, $3 exit code
  local line; line="$(grep '^prim-bytes: [0-9]* pass' "$2" | tail -1)"
  grep '^FAIL\|numBits' "$2"
  if [ "$3" -eq 0 ] && [ -n "$line" ] && echo "$line" | grep -q ' 0 fail '; then
    echo "prim $1: ${line#prim-bytes: }"
  else
    echo "prim $1: FAILED (exit $3) ${line#prim-bytes: }"; fails=$((fails + 1))
  fi
}

rc=0; "$BIN" > "$TMP/native.txt" 2>&1 || rc=$?
score native "$TMP/native.txt" "$rc"

wrc=0
L4_WASM_EXE_OBJ="${L4_WASM_EXE_OBJ:-$TMP/obj}" \
  "$ROOT/tools/lean-wasm-exe.sh" Harness.PrimBytesTest "$TMP/l4prim-test.js" > "$TMP/build.txt" 2>&1 || wrc=$?
if [ "$wrc" -eq 0 ]; then
  rc=0; node "$TMP/l4prim-test.js" > "$TMP/wasm.txt" 2>&1 || rc=$?
  score wasm32 "$TMP/wasm.txt" "$rc"
elif [ "$wrc" -eq 2 ]; then
  echo "prim wasm32: not run: $(tail -1 "$TMP/build.txt")"
  [ "${PRIM_REQUIRE_WASM:-0}" = "1" ] && exit 2
else
  cat "$TMP/build.txt"; echo "prim wasm32: FAILED to build"; fails=$((fails + 1))
fi

[ "$fails" -eq 0 ] || exit 1
exit 0
