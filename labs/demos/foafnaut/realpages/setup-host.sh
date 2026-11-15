#!/usr/bin/env bash
# Make a checkout of the Foafnaut lab able to run run_html.ts on a released engine library,
# with no Lean and no engine build: the host needs the Wasm modules it imports (the
# foafnaut-web release of factoidal-builds: web-render and render-plan; a native run loads
# web-render and never calls it) and, on macOS, the window library (native_window.m, built
# here with clang when no release copy is given).
#   setup-host.sh LAB_DIR WEB_DIR [NATIVE_WINDOW_DYLIB]
# LAB_DIR: labs/demos/foafnaut of the checkout. WEB_DIR: the extracted foafnaut-web set (the
# directory that holds docs/web/hub/html-webgpu/runtime).
set -euo pipefail
LAB=$1; WEB=$2; WINDOW=${3:-}
RT=$WEB/docs/web/hub/html-webgpu/runtime
mkdir -p "$LAB/.build/native-html/runtime" "$LAB/.build/engines" "$LAB/.build/native"
cp "$RT/web-render.mjs" "$RT/web-render.wasm" "$LAB/.build/native-html/runtime/"
cp "$RT/render-plan.mjs" "$RT/render-plan.wasm" "$LAB/.build/engines/"
if [ "$(uname -s)" = Darwin ]; then
  if [ -n "$WINDOW" ] && [ -f "$WINDOW" ]; then cp "$WINDOW" "$LAB/.build/native/libnative-window.dylib"
  else
    xcrun clang -dynamiclib -fobjc-arc -O2 -Wall -Wextra -Werror -framework Cocoa -framework QuartzCore \
      -Wl,-install_name,@rpath/libnative-window.dylib "$LAB/native_window.m" -o "$LAB/.build/native/libnative-window.dylib"
  fi
fi
echo "host ready: $LAB"
