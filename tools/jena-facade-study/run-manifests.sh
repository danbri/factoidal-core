#!/usr/bin/env bash
# Stage 0b of docs/designissues/2026-10-25-jena-style-facade-feasibility.md:
# run Apache Jena's own W3C-form manifests (jena-arq/testing/ARQ and
# jena-arq/testing/SPARQL-CDTs) with l4w3c, the runner of the hub
# scoreboard (tools/lean-scoreboard.sh). Reads the Jena tree only; it does
# not run Jena or Maven.
#
# Usage (from the repository root, after the Lean build):
#   bash tools/jena-facade-study/run-manifests.sh <jena root> [out dir]
#
# ARQ/ValueTesting gives its expected results as .n3 files (Turtle text).
# l4w3c reads .srx/.srj/.tsv/.csv/.ttl/.rdf results only, so the script also
# runs a copy of that directory with the .n3 files renamed to .ttl.
set -euo pipefail
JENA=${1:?usage: run-manifests.sh <jena root> [out dir]}
OUT=${2:-$(mktemp -d)}
L4W3C=formal/lean4/.lake/build/bin/l4w3c
T="$JENA/jena-arq/testing"
mkdir -p "$OUT"
run() { "$L4W3C" "$2" > "$OUT/$1.txt" 2>&1 || true; printf '%-22s %s\n' "$1" "$(grep '^TOTAL:' "$OUT/$1.txt")"; }
run arq "$T/ARQ/manifest-arq.ttl"
run arq-scripting "$T/ARQ/Scripting/manifest.ttl"
run sparql-cdts "$T/SPARQL-CDTs/manifest-all.ttl"
VT="$OUT/ValueTesting-ttl"
rm -rf "$VT"; mkdir -p "$VT"; cp "$T/ARQ/ValueTesting/"* "$VT/"
for f in "$VT"/*.n3; do mv "$f" "${f%.n3}.ttl"; done
sed -i.bak 's/\.n3>/.ttl>/g' "$VT"/manifest.ttl "$VT"/*.rq && rm -f "$VT"/*.bak
run arq-valuetesting-ttl "$VT/manifest.ttl"
echo "logs: $OUT"
