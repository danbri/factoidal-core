#!/usr/bin/env bash
# tools/bundle-sizes.sh
#
# Measures raw and gzip -9 byte sizes for the shipped npm bundles
# (issue https://github.com/danbri/factoidal/issues/684) and writes
# docs/test-results/bundle-sizes.json:
#
#   { "measuredAt": ISO date, "gitSha": ..., "bundles": [ { "path",
#     "rawBytes", "gzipBytes" }, ... ] }
#
# The wasm asset files carry a content hash in their filename
# (js_of_ocaml/wasm_of_ocaml output, e.g.
# code-5a7fc68f2ab1323718b8.wasm) and are found by globbing their
# assets directory rather than hardcoding the hash. A missing file, or
# an assets directory with zero or more than one *.wasm file, is a
# packaging problem this script reports and exits 1 on -- it does not
# silently measure a subset.
#
# Usage:
#   tools/bundle-sizes.sh
#
# Since @factoidal/core 0.9.0 the package ships one engine, the Lean 4
# wasm (npm/factoidal/l4-assets/, issue 713). Those files, and the
# JavaScript browser.js loads, are REQUIRED rows: a missing one is a
# packaging problem and the script exits 1. The F* bundles are not in
# the package any more; they are measured BY PATH under
# docs/fstar-extracted/ (installed by `tools/fetch-builds.sh --set web`)
# as OPTIONAL comparison rows, each prefixed `OPT:`, and a missing one is
# reported and skipped. This script builds nothing (run
# formal/lean4/Wasm/build-wasm.sh or tools/fetch-builds.sh first).

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO_ROOT"

OUT_JSON="docs/test-results/bundle-sizes.json"

# Repo-root-relative paths. GLOB: entries resolve to exactly one file.
PATHS=(
  "npm/factoidal/l4-assets/l4factoidal.wasm"
  "npm/factoidal/l4-assets/l4factoidal.mjs"
  "npm/factoidal/l4-assets/l4factoidal.js"
  "npm/factoidal/browser.js"
  "npm/factoidal/lib/api.mjs"
  "npm/factoidal/lib/lean-entry.mjs"
  "npm/factoidal/rdfjs.mjs"
  "OPT:docs/fstar-extracted/factoidal-npm-entry.js"
  "OPT:docs/fstar-extracted/factoidal.js"
  "OPT:docs/fstar-extracted/factoidal-npm-entry.wasm.js"
  "OPT:GLOB:docs/fstar-extracted/factoidal-npm-entry.wasm.assets/*.wasm"
  "OPT:docs/fstar-extracted/factoidal-npm-entry-lite.js"
  "OPT:docs/fstar-extracted/factoidal-npm-entry-lite.wasm.js"
  "OPT:GLOB:docs/fstar-extracted/factoidal-npm-entry-lite.wasm.assets/*.wasm"
)

resolve_glob() {
  # $1: repo-relative glob pattern. Prints the single repo-relative
  # match on stdout, or errors (exit 1) on zero or multiple matches.
  local pattern="$1"
  local matches=()
  local f
  for f in $REPO_ROOT/$pattern; do
    [ -e "$f" ] && matches+=("$f")
  done
  if [ "${#matches[@]}" -eq 0 ]; then
    echo "bundle-sizes: no file matches $pattern" >&2
    return 1
  fi
  if [ "${#matches[@]}" -gt 1 ]; then
    echo "bundle-sizes: $pattern matched ${#matches[@]} files, expected exactly one: ${matches[*]}" >&2
    return 1
  fi
  # realpath --relative-to keeps the JSON's paths repo-root-relative
  # regardless of which assets-dir layout produced the match.
  realpath --relative-to="$REPO_ROOT" "${matches[0]}"
}

ROWS_TSV="$(mktemp)"
trap 'rm -f "$ROWS_TSV"' EXIT

printf '%-70s %12s %12s\n' 'path' 'rawBytes' 'gzipBytes'

RESOLVE_RC=0
for entry in "${PATHS[@]}"; do
  optional=0
  if [ "${entry#OPT:}" != "$entry" ]; then
    optional=1
    entry="${entry#OPT:}"
  fi
  if [ "${entry#GLOB:}" != "$entry" ]; then
    if ! path="$(resolve_glob "${entry#GLOB:}" 2>/dev/null)"; then
      if [ "$optional" -eq 1 ]; then
        echo "bundle-sizes: optional F* comparison file ${entry#GLOB:} absent (tools/fetch-builds.sh --set web); skipped" >&2
      else
        resolve_glob "${entry#GLOB:}" >/dev/null
        RESOLVE_RC=1
      fi
      continue
    fi
  else
    path="$entry"
  fi

  if [ ! -f "$REPO_ROOT/$path" ]; then
    if [ "$optional" -eq 1 ]; then
      echo "bundle-sizes: optional F* comparison file $path absent (tools/fetch-builds.sh --set web); skipped" >&2
    else
      echo "bundle-sizes: missing $path -- run formal/lean4/Wasm/build-wasm.sh or tools/fetch-builds.sh --set web first" >&2
      RESOLVE_RC=1
    fi
    continue
  fi

  raw_bytes="$(wc -c < "$REPO_ROOT/$path")"
  RAW_RC=$?
  if [ "$RAW_RC" -ne 0 ]; then
    echo "bundle-sizes: wc -c failed on $path (exit $RAW_RC)" >&2
    RESOLVE_RC=1
    continue
  fi
  raw_bytes="$(printf '%s' "$raw_bytes" | tr -d '[:space:]')"

  gzip_bytes="$(gzip -9 -c "$REPO_ROOT/$path" | wc -c)"
  GZIP_RC=$?
  if [ "$GZIP_RC" -ne 0 ]; then
    echo "bundle-sizes: gzip -9 failed on $path (exit $GZIP_RC)" >&2
    RESOLVE_RC=1
    continue
  fi
  gzip_bytes="$(printf '%s' "$gzip_bytes" | tr -d '[:space:]')"

  printf '%-70s %12s %12s\n' "$path" "$raw_bytes" "$gzip_bytes"
  printf '%s\t%s\t%s\n' "$path" "$raw_bytes" "$gzip_bytes" >>"$ROWS_TSV"
done

if [ "$RESOLVE_RC" -ne 0 ]; then
  echo "bundle-sizes: one or more files could not be measured (see above); $OUT_JSON NOT written." >&2
  exit 1
fi

MEASURED_AT="$(date -u +%Y-%m-%dT%H:%M:%SZ)"
GIT_SHA="$(git rev-parse HEAD)"
GIT_RC=$?
if [ "$GIT_RC" -ne 0 ]; then
  echo "bundle-sizes: git rev-parse HEAD failed (exit $GIT_RC)" >&2
  exit 1
fi

mkdir -p "$(dirname "$OUT_JSON")"

python3 -c '
import json, sys

measured_at, git_sha, tsv_path, out_path = sys.argv[1:5]

bundles = []
with open(tsv_path, "r", encoding="utf-8") as f:
    for line in f:
        line = line.rstrip("\n")
        if not line:
            continue
        path, raw_bytes, gzip_bytes = line.split("\t")
        bundles.append({
            "path": path,
            "rawBytes": int(raw_bytes),
            "gzipBytes": int(gzip_bytes),
        })

doc = {"measuredAt": measured_at, "gitSha": git_sha, "bundles": bundles}
with open(out_path, "w", encoding="utf-8") as f:
    json.dump(doc, f, indent=2)
    f.write("\n")
' "$MEASURED_AT" "$GIT_SHA" "$ROWS_TSV" "$OUT_JSON"
PY_RC=$?
if [ "$PY_RC" -ne 0 ]; then
  echo "bundle-sizes: writing $OUT_JSON failed (exit $PY_RC)" >&2
  exit 1
fi

echo "bundle-sizes: wrote $OUT_JSON"
