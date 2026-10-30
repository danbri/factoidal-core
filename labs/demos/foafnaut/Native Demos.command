#!/bin/zsh
set -eu
DEMO_DIR="${0:A:h}"
cd "$DEMO_DIR"
print 'Lean WASM + native WebGPU'
print '1  Spring network — drag nodes, Space pauses, R resets'
print '2  Responsive layout — resize the window and select cards'
print '3  Vector playground — drag the circle and pink curve handle'
print ''
read 'DEMO_CHOICE?Choose [1]: '
case "${DEMO_CHOICE:-1}" in
  1) DEMO_NAME=springs ;;
  2) DEMO_NAME=layout ;;
  3) DEMO_NAME=vectors ;;
  *) print 'Choose 1, 2, or 3.'; exit 1 ;;
esac
exec "$DEMO_DIR/run-demo.sh" "$DEMO_NAME" "$@"
