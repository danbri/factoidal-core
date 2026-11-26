#!/bin/bash
# Fetch the media decoder modules that Lean's WasmVM runs (Opus, Vorbis, VP8, MP3) from
# danbri/factoidal-builds, third_party/media-decoders/wasm, into DIR, and check each one's size
# and SHA-256 against the pins of formal/lean4/L4Factoidal/Media/Modules.lean. The builds commit
# is read from the same file, so this script and Lean can not disagree.
# Record: docs/designissues/2026-11-26-foafnaut-audio-plan.md; issue
# https://github.com/danbri/factoidal-core/issues/1169.
#
# Usage: tools/fetch-media-decoders.sh [DIR]     (default ~/.cache/factoidal/media-decoders)
# Then:  cd formal/lean4 && lake exe media-bench check DIR
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/.." && pwd)
PINS=$ROOT/formal/lean4/L4Factoidal/Media/Modules.lean
DIR=${1:-$HOME/.cache/factoidal/media-decoders}
mkdir -p "$DIR"
sha() { if command -v sha256sum >/dev/null; then sha256sum "$1"; else shasum -a 256 "$1"; fi | cut -d' ' -f1; }
# One line per pin: commit file bytes sha256
python3 - "$PINS" > "$DIR/.pins" <<'EOF'
import re, sys
s = open(sys.argv[1]).read()
commit = re.search(r'"danbri/factoidal-builds ([0-9a-f]{40}) ', s).group(1)
for m in re.finditer(r'file := "([^"]+)", bytes := (\d+), abi := \d+,\s*sha256 := "([0-9a-f]{64})"', s):
    print(commit, m.group(1), m.group(2), m.group(3))
EOF
[ -s "$DIR/.pins" ] || { echo "no pins read from $PINS" >&2; exit 1; }
bad=0
while read -r commit file bytes want; do
  url="https://raw.githubusercontent.com/danbri/factoidal-builds/$commit/third_party/media-decoders/wasm/$file"
  if [ ! -f "$DIR/$file" ] || [ "$(sha "$DIR/$file")" != "$want" ]; then
    curl -sSfL --retry 3 -o "$DIR/$file.part" "$url" && mv "$DIR/$file.part" "$DIR/$file"
  fi
  got=$(sha "$DIR/$file"); size=$(wc -c < "$DIR/$file" | tr -d ' ')
  if [ "$got" = "$want" ] && [ "$size" = "$bytes" ]; then echo "ok   $file ($size bytes)"
  else echo "FAIL $file: $size bytes, SHA-256 $got; pinned $bytes, $want" >&2; bad=1; fi
done < "$DIR/.pins"
rm -f "$DIR/.pins"
[ "$bad" = 0 ] && echo "modules in $DIR"
exit "$bad"
