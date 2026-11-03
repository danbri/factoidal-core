#!/usr/bin/env bash
# Optional real WindowServer probe. A headless skip is 77, never a pass.
set -euo pipefail
LAB=$(cd "$(dirname "$0")" && pwd)
NATIVE=${1:-$LAB/.build/native}
mkdir -p "$LAB/.build"
xcrun clang -fobjc-arc -O2 -Wall -Wextra -Werror -framework Cocoa \
  -L "$NATIVE" -lnative-window -Wl,-rpath,"$NATIVE" \
  "$LAB/native_input_probe.m" -o "$LAB/.build/native-input-probe"
"$LAB/.build/native-input-probe"
