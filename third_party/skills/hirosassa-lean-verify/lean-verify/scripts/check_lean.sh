#!/usr/bin/env bash
# Check whether a Lean environment is available. Uses a timeout so it doesn't hang on a download/lock wait.
set -u

for cmd in elan lean lake; do
  if command -v "$cmd" >/dev/null 2>&1; then
    echo "found: $cmd -> $(command -v "$cmd")"
  else
    echo "missing: $cmd"
  fi
done

if ! command -v elan >/dev/null 2>&1; then
  echo "elan is missing. Install it following references/setup.md (after confirming with the user)."
  exit 1
fi

# The first run may be slow while downloading the toolchain, or wait on another process's lock.
# Judging by process name picks up false positives (ourselves, unrelated shells), so decide by whether the command succeeds.
if command -v timeout >/dev/null 2>&1; then
  timeout 60 lean --version || { echo "lean --version did not finish within 60s. The toolchain may still be downloading. Wait for it to finish and rerun."; exit 2; }
else
  lean --version
fi

# Plausible is a lake dependency, not part of core. Report whether this project can use it.
# Lines starting with "plausible:" are machine-readable: available / not installed / unavailable (single-file mode).
root="$PWD"
while [ ! -f "$root/lakefile.toml" ] && [ ! -f "$root/lakefile.lean" ]; do
  [ "$root" = "/" ] && { root=""; break; }
  root="$(dirname "$root")"
done

if [ -z "$root" ]; then
  echo "Single-file mode: no lakefile found, so plausible cannot be used."
  echo "plausible: unavailable (single-file mode)"
elif [ -d "$root/.lake/packages/plausible" ]; then
  echo "lake project: $root"
  echo "plausible: available"
else
  echo "lake project: $root"
  if grep -qs plausible "$root/lakefile.toml" "$root/lakefile.lean"; then
    echo "plausible is declared in the lakefile but not resolved yet (needs 'lake update', ask the user first)."
  else
    echo "plausible is not in the lakefile. Adding it needs the user's permission (see references/setup.md §4)."
  fi
  echo "plausible: not installed"
fi
