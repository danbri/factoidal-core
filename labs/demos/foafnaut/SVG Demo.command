#!/bin/zsh
set -eu
DEMO_DIR="${0:A:h}"
cd "$DEMO_DIR"
LOG_FILE="$DEMO_DIR/native-svg.log"
if (( $# == 0 )); then
  set -- "$DEMO_DIR/svg-fixtures/gallery.svg" "$DEMO_DIR/render-svg.ppm"
fi
{
  print -- "[$(date -u '+%Y-%m-%dT%H:%M:%SZ')] Native SVG demo: $*"
  shasum -a 256 "$DEMO_DIR/native-webgpu-svg-darwin-arm64"
  print -- "Run log: $LOG_FILE"
} 2>&1 | tee -a "$LOG_FILE"
exec /usr/bin/script -qae "$LOG_FILE" "$DEMO_DIR/native-webgpu-svg-darwin-arm64" "$@"
