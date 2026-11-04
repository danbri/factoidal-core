#!/bin/zsh
set -eu
DEMO_DIR="${0:A:h}"
exec "$DEMO_DIR/run-demo.sh" foafnaut "$@"
