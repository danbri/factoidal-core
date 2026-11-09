#!/bin/bash
# Runs a Foafnaut program through the developer proxy. Development only.
# usage: foafnaut-through-proxy.sh (--record NAME|--replay NAME|--passthrough)
#          [--default-service S] [--allow-existing] -- PROGRAM [ARG...]
# --allow-existing passes --append to a recording that exists already.
set -u
here="$(cd "$(dirname "$0")" && pwd)"
proxy_args=()
while [ $# -gt 0 ]; do
  case "$1" in
    --record|--replay) proxy_args+=("$1" "$2"); shift 2 ;;
    --passthrough) proxy_args+=("$1"); shift ;;
    --default-service) proxy_args+=("$1" "$2"); shift 2 ;;
    --allow-existing) proxy_args+=(--append); shift ;;
    --) shift; break ;;
    *) echo "foafnaut-through-proxy: unknown argument $1" >&2; exit 2 ;;
  esac
done
if [ $# -eq 0 ]; then
  echo "usage: foafnaut-through-proxy.sh (--record NAME|--replay NAME|--passthrough) [--default-service S] [--allow-existing] -- PROGRAM [ARG...]" >&2
  exit 2
fi
if [ -n "${FOAFNAUT_DEVPROXY_EXTRA_ARGS:-}" ]; then
  # shellcheck disable=SC2206
  proxy_args+=($FOAFNAUT_DEVPROXY_EXTRA_ARGS)
fi

ca="$(node "$here/devproxy.mjs" --print-ca)" || exit 2
log="$(mktemp -t foafnaut-devproxy)"
fifo="$(mktemp -u -t foafnaut-devproxy-fifo)"
mkfifo "$fifo"
node "$here/devproxy.mjs" --port 0 "${proxy_args[@]}" >"$fifo" 2>"$log" &
proxy_pid=$!
cleanup() { kill "$proxy_pid" 2>/dev/null; wait "$proxy_pid" 2>/dev/null; rm -f "$fifo"; }
trap cleanup EXIT
line=""
read -r -t 20 line <"$fifo"
case "$line" in
  "LISTENING 127.0.0.1:"*) port="${line##*:}" ;;
  *) echo "foafnaut-through-proxy: the proxy did not start:" >&2; cat "$log" >&2; exit 2 ;;
esac
echo "foafnaut-through-proxy: proxy on 127.0.0.1:$port, log $log" >&2

# The proxy variables and DENO_CERT are read by the Deno runtime itself, so a
# compiled program with no --allow-env for them still obeys them.
env -u NO_PROXY -u no_proxy \
  HTTP_PROXY="http://127.0.0.1:$port" HTTPS_PROXY="http://127.0.0.1:$port" \
  http_proxy="http://127.0.0.1:$port" https_proxy="http://127.0.0.1:$port" \
  DENO_CERT="$ca" "$@"
rc=$?
kill "$proxy_pid" 2>/dev/null
wait "$proxy_pid" 2>/dev/null
grep -E 'devproxy: (MISS|upstream|refused|service)' "$log" | sed -e 's/^/foafnaut-through-proxy: /' >&2
exit "$rc"
