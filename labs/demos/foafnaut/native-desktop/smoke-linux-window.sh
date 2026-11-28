#!/usr/bin/env bash
# Verify the displayed frame on an isolated X11 screen, including native mouse delivery.
set -euo pipefail

if [[ $# != 3 ]]; then
  echo "Usage: $0 RUST_HOST LIBWEB_RENDER LIBNATIVE_WINDOW" >&2
  exit 2
fi

if [[ ${FOAFNAUT_WINDOW_SMOKE_DISPLAY:-} != private ]]; then
  exec xvfb-run -a -s '-screen 0 800x600x24' \
    env FOAFNAUT_WINDOW_SMOKE_DISPLAY=private SDL_VIDEODRIVER=x11 "$0" "$@"
fi

log=$(mktemp)
"$1" "$2" --window "$3" >"$log" 2>&1 &
host=$!
cleanup() {
  local result=$?
  if kill -0 "$host" 2>/dev/null; then
    kill "$host"
  fi
  wait "$host" 2>/dev/null || true
  if (( result != 0 )); then
    cat "$log" >&2
  fi
  rm -f "$log"
}
trap cleanup EXIT

require_host() {
  if ! kill -0 "$host" 2>/dev/null; then
    echo 'Foafnaut exited before the expected frame' >&2
    exit 1
  fi
}

window=''
deadline=$((SECONDS + 30))
while (( SECONDS < deadline )); do
  require_host
  window=$(xdotool search --onlyvisible --name '^Foafnaut$' 2>/dev/null | head -n 1) || true
  [[ -z "$window" ]] || break
  sleep 0.1
done
if [[ -z "$window" ]]; then
  echo 'Foafnaut did not show a window' >&2
  exit 1
fi

wait_for_pixel() {
  local wanted_r=$1 wanted_g=$2 wanted_b=$3 pixel=''
  local r g b deadline=$((SECONDS + 20))
  while (( SECONDS < deadline )); do
    require_host
    # Read from the X server after presentation. The point is inside the swatch.
    pixel=$(import -window "$window" -crop 1x1+30+120 -depth 8 rgb:- 2>/dev/null | od -An -tu1) || pixel=''
    read -r r g b <<<"$pixel"
    if [[ "$r" =~ ^[0-9]+$ && "$g" =~ ^[0-9]+$ && "$b" =~ ^[0-9]+$ ]] &&
       (( (r - wanted_r)**2 + (g - wanted_g)**2 + (b - wanted_b)**2 <= 12 )); then
      return
    fi
    sleep 0.1
  done
  printf 'Expected RGB %d %d %d at the swatch. Last pixel was %s\n' \
    "$wanted_r" "$wanted_g" "$wanted_b" "$pixel" >&2
  exit 1
}

wait_for_pixel 176 48 48
xdotool mousemove --window "$window" 30 30 click 1
wait_for_pixel 32 80 160
echo 'PASS: the native pointer click changed the displayed Foafnaut swatch from red to blue'
