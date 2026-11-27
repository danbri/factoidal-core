#!/bin/bash
# Linux CI for the limb fields and the fast precompile paths: every part in ci.d, in name order.
# A part builds its targets with `lake -f lakefile-fieldperf.toml build …` and runs its checks.
set -euo pipefail
cd "$(dirname "$0")/../.."
for part in scripts/fieldperf/ci.d/*.sh; do
  echo "=== $part"
  bash "$part"
done
