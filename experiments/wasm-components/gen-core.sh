#!/usr/bin/env bash
# Regenerate the C of Lean's core library (Init, Std.Data, Std.Classes, Std.Do
# and the 26 Std.Time modules that Std.Time.DateTime.Timestamp needs) with the
# native lean, as step 3 of formal/lean4/Wasm/build-wasm.sh does. Skips files
# that exist. Inputs: TC (toolchain prefix), CORE_C (output dir), P (jobs).
set -euo pipefail
LEAN_SRC="$TC/src/lean"
export LEAN_PATH="$TC/lib/lean"
gen_one() {
  local f="$1" out
  out="$CORE_C/$(echo "${f#$LEAN_SRC/}" | sed 's|/|_|g; s|\.lean$|.c|')"
  [ -s "$out" ] && return 0
  "$TC/bin/lean" -R "$LEAN_SRC" -c "$out" "$f" >/dev/null 2>&1 || { echo "GEN-FAIL $f" >&2; rm -f "$out"; }
}
export -f gen_one; export CORE_C LEAN_SRC TC
STD_TIME="Internal/Bounded Internal/UnitVal Internal Time/Unit/Nanosecond Time/Unit/Second
  Time/Unit/Minute Time/Unit/Hour Time/Unit/Millisecond Time/Unit/Basic Time/Basic
  Time/HourMarker Time/PlainTime Time Date/Unit/Day Date/Unit/Month Date/Unit/Year
  Date/Unit/Weekday Date/Unit/Week Date/Unit/Basic Date/ValidDate Date/Basic
  Date/PlainDate Date Duration DateTime/WallTime DateTime/Timestamp"
{ echo "$LEAN_SRC/Init.lean"; find "$LEAN_SRC/Init" -name '*.lean'
  for d in Data Classes Do; do [ -d "$LEAN_SRC/Std/$d" ] && find "$LEAN_SRC/Std/$d" -name '*.lean'; done
  for m in $STD_TIME; do echo "$LEAN_SRC/Std/Time/$m.lean"; done; true; } \
  | xargs -P "${P:-4}" -I{} bash -c 'gen_one "$@"' _ {}
echo "  core C files: $(ls "$CORE_C"/*.c | wc -l)"
