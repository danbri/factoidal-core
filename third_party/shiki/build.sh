#!/usr/bin/env bash
# Reproduce the selected dependency bundle; normal Pages builds do not run this.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
cp "$HERE/package.json" "$HERE/package-lock.json" "$HERE/entry.mjs" "$TMP/"
npm ci --prefix "$TMP" --cache "$TMP/cache" --ignore-scripts --no-audit --no-fund
node "$TMP/node_modules/esbuild/bin/esbuild" "$TMP/entry.mjs" --bundle --format=esm --platform=browser --target=es2022 --minify --outfile="$HERE/highlight.mjs"
