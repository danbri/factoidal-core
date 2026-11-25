#!/usr/bin/env bash
# Run this checkout's run_html.ts under Xvfb with software Vulkan and the released native engine
# (after setup.sh). Arguments go to run_html.ts. Use a sweep so the run exits.
set -euo pipefail
ROOT=$(cd "$(dirname "$0")/../.." && pwd); LAB="$ROOT/labs/demos/foafnaut"
ENGINE=$(cat "$LAB/.build/native/rig-engine-path")
export VK_ICD_FILENAMES=${VK_ICD_FILENAMES:-/usr/share/vulkan/icd.d/lvp_icd.json}
cd "$LAB"
exec xvfb-run -a -s "-screen 0 1280x900x24" deno run --no-check --no-config --no-npm --node-modules-dir=none \
  --unstable-webgpu --unstable-ffi -A run_html.ts --native-engine "$ENGINE" --no-splash "$@"
