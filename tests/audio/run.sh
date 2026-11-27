#!/usr/bin/env bash
#
# tests/audio/run.sh — the audio sink of the web engine (issue
# https://github.com/danbri/factoidal-core/issues/1169, stage D1; plan
# docs/designissues/2026-11-26-foafnaut-audio-plan.md section 13.5).
#
#   1. ring_stress   the C ring and the null consumer under ThreadSanitizer (gcc): a writer thread
#                    and a reader thread, 20 million frames, random chunk sizes, every frame checked.
#   2. ring replay   a trace of 100,000 random single-threaded operations of the C ring (capacity 7)
#                    replayed through formal/lean4/L4Factoidal/WebAudio/Ring.lean.
#   3. audio-sink-test  `lake exe audio-sink-test`: refusals, all-or-nothing writes, pause, one second of
#                    a 440 Hz sine through `wav:PATH` and `null`, bit for bit against the file.
#
#   4. automation-fill-diff  `lake exe automation-fill-diff`: 20,000 random AudioParam event lists, `Automation.fill`
#                    (binary64) against `Automation.fillSpec` (exact rationals), bit for bit.
#   5. audio-realtime-test  `lake exe audio-realtime-test`: a real-time AudioContext's ops through the engine's IO
#                    functions and its rendering task to `wav:PATH`, bit for bit against an OfflineAudioContext
#                    render of the same ops; no under-run; the autoplay rule (plan 13.7) through `null`.
#   6. page_tone.sh  a page's AudioContext on BubblePopJS in the native engine to a WAV file, against the
#                    page's own OfflineAudioContext render. Skipped (not failed) when web-render-native is
#                    not built; it needs labs/demos/foafnaut/build-web-render.sh --native.
#
# Needs gcc (with libtsan), the Lean toolchain (elan). Exit 0 only when every part passes.
set -uo pipefail
export LC_ALL=C
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
LEAN4="$ROOT/formal/lean4"
FFI="$LEAN4/ffi"
export PATH="$HOME/.elan/bin:$PATH"
TMP="$(mktemp -d "${TMPDIR:-/tmp}/audio-test.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
fails=0
part() { # $1 name, $2 exit code
  if [ "$2" -eq 0 ]; then echo "audio $1: pass"; else echo "audio $1: FAIL (exit $2)"; fails=$((fails+1)); fi
}

# 1. ThreadSanitizer stress
rc=0
gcc -std=c11 -Wall -Wextra -Werror -fsanitize=thread -O1 -g -pthread -DL4_AUDIO_NO_LEAN -I "$FFI" \
  "$HERE/ring_stress.c" "$FFI/audio_sink.c" -lm -o "$TMP/ring_stress" || rc=$?
if [ $rc -eq 0 ]; then
  TSAN_OPTIONS="halt_on_error=1 exitcode=66" "$TMP/ring_stress" 2>&1 | tee "$TMP/stress.log" || true
  rc=${PIPESTATUS[0]}
  grep -q 'ThreadSanitizer' "$TMP/stress.log" && rc=66
fi
part "ring stress (ThreadSanitizer)" $rc

# 2. Trace replay
rc=0
gcc -std=c11 -Wall -Wextra -Werror -O1 -I "$FFI" "$HERE/ring_trace.c" -o "$TMP/ring_trace" || rc=$?
if [ $rc -eq 0 ]; then "$TMP/ring_trace" 100000 12345 > "$TMP/trace.txt" || rc=$?; fi
if [ $rc -eq 0 ]; then
  echo "trace: $(wc -l < "$TMP/trace.txt") operations"
  (cd "$LEAN4" && lake build L4Factoidal.WebAudio.Ring >/dev/null && lake env lean --run "$HERE/RingReplay.lean" "$TMP/trace.txt") || rc=$?
fi
part "ring trace replay" $rc

# 3. Sink against a WAV file
rc=0
(cd "$LEAN4" && lake build audio-sink-test >/dev/null && AUDIO_TEST_DIR="$TMP" .lake/build/bin/audio-sink-test) || rc=$?
part "audio-sink-test" $rc

# 4. Automation.fill against fillSpec
rc=0
(cd "$LEAN4" && lake build automation-fill-diff >/dev/null && .lake/build/bin/automation-fill-diff) || rc=$?
part "automation-fill-diff" $rc

# 5. A real-time context through its rendering task
rc=0
(cd "$LEAN4" && lake build audio-realtime-test >/dev/null && AUDIO_TEST_DIR="$TMP" .lake/build/bin/audio-realtime-test) || rc=$?
part "audio-realtime-test" $rc

# 6. A page through the native engine
rc=0
"$HERE/page_tone.sh" || rc=$?
if [ $rc -eq 2 ]; then echo "audio page_tone: skipped (no web-render-native)"; else part "page_tone" $rc; fi

if [ $fails -eq 0 ]; then echo "audio: all pass"; exit 0; fi
echo "audio: $fails part(s) failed"
exit 1
