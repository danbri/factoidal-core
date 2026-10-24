#!/usr/bin/env bash
# Dataflow inventory tests (https://github.com/danbri/factoidal/issues/975).
#
# 1. Negative test: the report program run on `negativeRegistry`
#    (formal/lean4/L4Factoidal/Dataflow/RegistryTests.lean), where every entry
#    has a status that disagrees with its fields, must stop with exit 1 and
#    print an error line for every entry.
# 2. Drift test: regenerate the inventory from the Lean registry and fail
#    when docs/dataflow-inventory.md differs from it.
# 3. The FOUNDATION gate (tools/foundation-gate.py, foundation/README.md).
# 4. The entry-point gate (tools/entrypoint-gate.py, foundation/README.md).
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)"
lean="$here/formal/lean4"

(cd "$lean" && timeout 600 lake build L4Factoidal.Dataflow.RegistryTests >/dev/null)
rc=0
out="$(cd "$lean" && DATAFLOW_REGISTRY=negative timeout 600 lake env lean ../../tools/dataflow-inventory.lean 2>&1)" || rc=$?
if [ "$rc" -ne 1 ]; then
  printf "%s\n" "$out"
  echo "dataflow negative test: expected exit 1 from the report on negativeRegistry, got $rc" >&2
  exit 1
fi
if printf "%s\n" "$out" | grep -q "BEGIN-INVENTORY"; then
  printf "%s\n" "$out"
  echo "dataflow negative test: the report printed an inventory for negativeRegistry" >&2
  exit 1
fi
for i in 1 2 3 4 5 6 7 8 9; do
  if ! printf "%s\n" "$out" | grep -q "^negative $i:"; then
    printf "%s\n" "$out"
    echo "dataflow negative test: no error line for negative entry $i" >&2
    exit 1
  fi
done
echo "dataflow negative test: the report stopped on all 9 negative entries"

python3 "$here/tools/dataflow-inventory.py" --check

# 3. The FOUNDATION gate (issue 975, item 1): its fixture tests, then the gate
#    on this tree (foundation/manifest.toml, foundation/allow-imports.txt).
python3 -I "$here/tests/foundation/test_foundation_gate.py"
python3 -I "$here/tools/foundation-gate.py" --root "$here"

# 4. The entry-point gate (issue 975, item 3): its fixture tests, then the
#    gate on this tree (foundation/entrypoints.toml,
#    foundation/unbound-entrypoints.txt, docs/dataflow-inventory.md as
#    checked current in step 2).
python3 -I "$here/tests/foundation/test_entrypoint_gate.py"
python3 -I "$here/tools/entrypoint-gate.py" --root "$here"
