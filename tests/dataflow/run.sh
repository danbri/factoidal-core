#!/usr/bin/env bash
# Dataflow inventory drift test (https://github.com/danbri/factoidal/issues/975, phase A3).
# Regenerates the inventory from the Lean registry and fails when
# docs/dataflow-inventory.md differs from it.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
python3 "$here/tools/dataflow-inventory.py" --check
