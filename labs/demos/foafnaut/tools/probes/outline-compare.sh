#!/usr/bin/env bash
# Compare every glyph of TrueType fonts: Lean SfntOutline against FreeType.
# usage: outline-compare.sh FONT.ttf ...   Needs pkg-config freetype2.
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"; lean="$here/../../../../../formal/lean4"
work="$(mktemp -d)"; trap 'rm -rf "$work"' EXIT
clang -O2 "$here/outline-freetype.c" $(pkg-config --cflags --libs freetype2) -o "$work/ft"
cd "$lean"
status=0
for font in "$@"; do
  "$work/ft" "$font" 0 1000000 > "$work/ft.txt"
  lake env lean --run "$here/OutlineDump.lean" "$font" 0 "$(wc -l < "$work/ft.txt")" > "$work/lean.txt"
  different="$(diff "$work/ft.txt" "$work/lean.txt" | grep -c '^<' || true)"
  echo "$(basename "$font"): $(wc -l < "$work/ft.txt") glyphs, $different different"
  [ "$different" = 0 ] || status=1
done
exit $status
