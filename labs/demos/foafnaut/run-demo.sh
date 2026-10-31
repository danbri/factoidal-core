#!/bin/zsh
set -eu
set -o pipefail
DEMO_DIR="${0:A:h}"
if [[ ! -x "$DEMO_DIR/native-webgpu-ui-darwin-arm64" && -x "$DEMO_DIR/.build/dist/native-webgpu-ui-darwin-arm64" ]]; then
  DEMO_DIR="$DEMO_DIR/.build/dist"
fi
if [[ ! -x "$DEMO_DIR/native-webgpu-ui-darwin-arm64" ]]; then
  print -u2 "Build the native demos first with: $DEMO_DIR/build-executables.sh"
  exit 1
fi
cd "$DEMO_DIR"
DEMO_NAME="${1:-springs}"
case "$DEMO_NAME" in
  vectors|springs|layout|foafnaut) ;;
  *) print -u2 'Choose vectors, springs, layout or foafnaut.'; exit 1 ;;
esac
if (( $# > 0 )); then shift; fi
LOG_FILE="$DEMO_DIR/native-$DEMO_NAME.log"
{
  print -- "[$(date -u '+%Y-%m-%dT%H:%M:%SZ')] Native demo: $DEMO_NAME; arguments: $*"
  shasum -a 256 "$DEMO_DIR/native-webgpu-ui-darwin-arm64" "$DEMO_DIR/libnative-window.dylib"
  print -- "Run log: $LOG_FILE"
} 2>&1 | tee -a "$LOG_FILE"
# Deno needs a terminal to ask for the native-surface FFI permission. Give the
# child a PTY while recording output; a plain pipe to tee prevents that prompt.
exec /usr/bin/script -qae "$LOG_FILE" "$DEMO_DIR/native-webgpu-ui-darwin-arm64" --demo "$DEMO_NAME" "$@"
