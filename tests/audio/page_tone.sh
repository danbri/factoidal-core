#!/usr/bin/env bash
#
# tests/audio/page_tone.sh — a page's AudioContext plays through the native engine to a WAV file
# (issue https://github.com/danbri/factoidal-core/issues/1169, step D3; plan
# docs/designissues/2026-11-26-foafnaut-audio-plan.md, section 13.6).
#
# The page tone-page.html runs on BubblePopJS in the native engine (web-render-native
# --script-seq). A key press (WebDriver key actions: user activation) starts a real-time
# AudioContext with a 440 Hz sine oscillator from 0 s to 1 s; at `ended` the page closes it. The
# engine's audio sink is `wav:FILE` (FOAFNAUT_AUDIO_SINK). Checks: the first 48,000 frames of the
# file hash to the page's own OfflineAudioContext render of the same graph (FNV-1a over the binary32
# bits, frame by frame); the frames after them are 0; no under-run; the page saw `ended`, then
# `closed`. The page sees the states of the Web Audio API constructor: `suspended` at once, then
# `statechange` to `running`. Prints the trace measures (render time, first sound).
#
# Needs .build/web-render/web-render-native (labs/demos/foafnaut/build-web-render.sh --native).
set -uo pipefail
HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(cd "$HERE/../.." && pwd)"
BIN="${WEB_RENDER_NATIVE:-$ROOT/labs/demos/foafnaut/.build/web-render/web-render-native}"
[ -x "$BIN" ] || { echo "page_tone: no $BIN (build-web-render.sh --native)"; exit 2; }
TMP="$(mktemp -d "${TMPDIR:-/tmp}/page-tone.XXXXXX")"
trap 'rm -rf "$TMP"' EXIT
rc=0
FOAFNAUT_AUDIO_SINK="wav:$TMP/out.wav" FOAFNAUT_AUDIO_RATE=48000 timeout 120 \
  "$BIN" "$HERE/tone-page.html" 800 600 --script-seq "$HERE/tone-requests.json" "$TMP/answers.jsonl" \
  2> "$TMP/stderr.log" || rc=$?
grep '"type":"native-audio' "$TMP/stderr.log" || true
[ $rc -eq 0 ] || { echo "page_tone: engine exit $rc"; tail -20 "$TMP/stderr.log"; exit 1; }
python3 -I - "$TMP/answers.jsonl" "$TMP/out.wav" "$TMP/stderr.log" <<'PY'
import json, struct, sys
answers, wav, err = sys.argv[1:4]
logs = []
for line in open(answers):
    line = line.strip()
    if not line: continue
    a = json.loads(line)
    if 'error' in a and isinstance(a['error'], str): print('answer error:', a['error'])
    logs += a.get('logs', [])
    for e in a.get('errors', []): print('page error:', e)
print('page logs:', logs)
fails = []
offline = [l for l in logs if l.startswith('offline-hash ')]
if not offline: fails.append('no offline-hash log')
for need in ('created suspended', 'statechange running', 'ended at', 'statechange closed', 'closed closed'):
    if not any(l.startswith(need) for l in logs): fails.append(f'no log "{need}"')
import os
data = open(wav, "rb").read() if os.path.exists(wav) else b""
if len(data) < 58: fails.append(f'wav has {len(data)} bytes')
else:
    rate, ch = struct.unpack_from('<I', data, 24)[0], struct.unpack_from('<H', data, 22)[0]
    words = struct.unpack_from(f'<{(len(data) - 58) // 4}I', data, 58)
    frames = len(words) // ch
    print(f'wav: {frames} frames, {ch} channels, {rate} Hz')
    if ch != 2 or rate != 48000 or frames < 48000: fails.append('wav shape')
    else:
        h = 2166136261
        for w in words[:96000]: h = ((h ^ w) * 16777619) & 0xffffffff
        if offline and int(offline[0].split()[1]) != h: fails.append(f'hash {h} != page offline {offline[0]}')
        loud = sum(1 for w in words[96000:] if w != 0)
        if loud: fails.append(f'{loud} values after the stop are not 0')
        first = next((i for i, w in enumerate(words) if w != 0), None)
        if first is not None and first // 2 != 1: print(f'first non-zero frame {first // 2}')
under = None
for line in open(err):
    if '"native-audio-end"' in line:
        try: under = json.loads(line).get('underruns')
        except ValueError: pass
if under is None: fails.append('no native-audio-end line')
elif under != 0: fails.append(f'{under} under-runs')
for f in fails: print('FAIL', f)
print('page_tone:', 'pass' if not fails else f'{len(fails)} fail')
sys.exit(1 if fails else 0)
PY
