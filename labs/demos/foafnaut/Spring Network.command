#!/bin/zsh
set -eu
DEMO_DIR="${0:A:h}"
cd "$DEMO_DIR"
exec "$DEMO_DIR/run-demo.sh" springs "$@"
