#!/usr/bin/env bash
# tools/check-exe.sh — check one executable that tools/build-exe.sh made, on
# the platform it is for.
#
# Usage: tools/check-exe.sh EXE [--quick]
#
# Checks: `--help`, `version` (prints the engine's wasm digest),
# `sample-store` then a COUNT query (15 triples), `serve` answers an ASK
# over HTTP, and (not with --quick) the desktop WebDAV harness
# `tests/webdav-desktop/selftest.mjs --cli EXE`, which needs Node 22.
# Score line: "N pass, M fail (out of T)". Exit 0 when nothing failed.
set -uo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
EXE="${1:?usage: tools/check-exe.sh EXE [--quick]}"
QUICK="${2:-}"
case "$EXE" in /*|[A-Za-z]:*) ;; *) EXE="$PWD/$EXE" ;; esac
WORK="$(mktemp -d)"
trap 'kill "${SPID:-}" 2>/dev/null; rm -rf "$WORK"' EXIT
PASS=0; FAIL=0
ok () { PASS=$((PASS+1)); echo "  ok    $1"; }
bad () { FAIL=$((FAIL+1)); echo "  FAIL  $1"; }

"$EXE" --help >"$WORK/help.txt" 2>&1 && grep -q 'usage: factoidal' "$WORK/help.txt" && ok "--help" || bad "--help: $(head -c 300 "$WORK/help.txt")"
"$EXE" version >"$WORK/version.txt" 2>&1 && grep -q 'wasm sha256' "$WORK/version.txt" && ok "version: $(grep -m1 'installed wasm' "$WORK/version.txt")" || bad "version: $(head -c 300 "$WORK/version.txt")"
STORE="$("$EXE" sample-store "$WORK/store" 2>"$WORK/ss.err" | tail -1)"
if [ -n "$STORE" ] && [ -d "$STORE" ]; then ok "sample-store"; else bad "sample-store: $(head -c 300 "$WORK/ss.err")"; fi
"$EXE" query "$WORK/store" 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }' >"$WORK/q.txt" 2>&1
grep -q '"15"' "$WORK/q.txt" && ok "query: COUNT = 15" || bad "query: $(head -c 300 "$WORK/q.txt")"
PORT=$(( 20000 + RANDOM % 20000 ))
"$EXE" serve "$WORK/store" --port "$PORT" >"$WORK/serve.txt" 2>&1 &
SPID=$!
ANSWER=""
for _ in $(seq 1 60); do
  ANSWER="$(curl -s "http://127.0.0.1:$PORT/sparql?query=ASK%7B%3Fs%20%3Fp%20%3Fo%7D" -H 'Accept: application/sparql-results+json' 2>/dev/null)" && [ -n "$ANSWER" ] && break
  sleep 0.5
done
case "$ANSWER" in *'"boolean":true'*) ok "serve: ASK over HTTP" ;; *) bad "serve: '$ANSWER' $(head -c 300 "$WORK/serve.txt")" ;; esac
kill "$SPID" 2>/dev/null; wait "$SPID" 2>/dev/null; SPID=""

if [ "$QUICK" != "--quick" ]; then
  if node "$REPO_ROOT/tests/webdav-desktop/selftest.mjs" --cli "$EXE" >"$WORK/dav.txt" 2>&1; then ok "webdav: $(tail -1 "$WORK/dav.txt")"; else bad "webdav: $(tail -5 "$WORK/dav.txt")"; fi
fi

echo "check-exe: $PASS pass, $FAIL fail (out of $((PASS + FAIL)))"
[ "$FAIL" -eq 0 ]
