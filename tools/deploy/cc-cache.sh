#!/usr/bin/env bash
# cc-cache.sh: compile one C file to a content-addressed object and link it to its name.
#   cc-cache.sh <cache-dir> <out.o> <src.c> <compiler> [flags...]
# Used by tools/deploy/build-units.py so that a re-run compiles only changed files.
set -euo pipefail
cache=$1; out=$2; src=$3; shift 3
key=$( { cat "$src"; printf '%s\n' "$*"; } | shasum -a 256 | cut -c1-40)
obj="$cache/${key:0:2}/$key.o"
if [ ! -s "$obj" ]; then
  mkdir -p "$cache/${key:0:2}"
  "$@" -c "$src" -o "$obj.$$" 2>/dev/null
  mv "$obj.$$" "$obj"
fi
ln -f "$obj" "$out"
