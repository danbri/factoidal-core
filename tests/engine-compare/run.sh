#!/usr/bin/env bash
# Private comparison build: the Lean engine of @factoidal/core against the
# F* engine's npm-entry bundle (issue 713 stage 3; owner, 2026-10-10:
# "Private builds might compare this with F* (or indeed different wasms from
# different toolchains)").
#
#   tests/engine-compare/run.sh PATH/TO/factoidal-npm-entry.js
#
# The bundle is a factoidal-builds artifact (`tools/fetch-builds.sh --set
# web` installs it under docs/fstar-extracted/), never part of the npm
# package. The Lean side is npm/factoidal as it stands, with its wasm in
# npm/factoidal/l4-assets/ (or $FACTOIDAL_L4_ASSETS).
#
# Exit status: the node --test status; 2 when the bundle is absent.
set -u

ENTRY="${1:-}"
if [ -z "$ENTRY" ] || [ ! -f "$ENTRY" ]; then
  echo "engine-compare: no F* npm-entry bundle at '${ENTRY}'." >&2
  echo "usage: $0 PATH/TO/factoidal-npm-entry.js" >&2
  echo "(tools/fetch-builds.sh --set web installs docs/fstar-extracted/factoidal-npm-entry.js)" >&2
  exit 2
fi

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ENTRY_ABS="$(cd "$(dirname "$ENTRY")" && pwd)/$(basename "$ENTRY")"

RC=0
FACTOIDAL_FSTAR_ENTRY="$ENTRY_ABS" node --test "$HERE"/*.test.mjs || RC=$?
exit "$RC"
