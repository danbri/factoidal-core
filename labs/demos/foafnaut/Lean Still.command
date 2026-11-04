#!/bin/zsh
set -eu
DEMO_DIR="${0:A:h}"
cd "$DEMO_DIR"
exec "$DEMO_DIR/native-webgpu-lean-darwin-arm64" "$DEMO_DIR/render-lean.ppm" "$@"
