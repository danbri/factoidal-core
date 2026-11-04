#!/usr/bin/env bash
set -euo pipefail
lab="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$lab/.build"
# Font libraries are host data adapters; they do not implement Lean layout.
read -r -a font_flags <<< "$(pkg-config --cflags --libs harfbuzz freetype2)"
if [[ "$(uname -s)" != Darwin ]]; then
  read -r -a crypto_flags <<< "$(pkg-config --cflags --libs openssl)"
  font_flags+=("${crypto_flags[@]}")
fi
clang -std=c11 -O2 -Wall -Wextra -Werror "$lab/tools/font-shape.c" \
  "${font_flags[@]}" -o "$lab/.build/font-shape"
printf '%s\n' "$lab/.build/font-shape"
