#!/bin/sh
set -eu
if [ "$(id -u)" = 0 ]; then
  mkdir -p /data/lws /data/xmpp /data/caddy /config
  chown node:node /data /data/lws /data/xmpp /data/caddy /config
  exec gosu node /opt/replica/entrypoint.sh
fi
: "${PUBLIC_ORIGIN:?Set PUBLIC_ORIGIN to the external HTTPS origin}"
: "${WRITER_SUBJECT:?Set WRITER_SUBJECT to the laptop identity IRI}"
: "${SITE_ADDRESS:?Set SITE_ADDRESS to the TLS hostname, or http://:8080 behind Fly TLS}"
node /opt/replica/server.mjs &
lws_pid=$!
caddy run --config /opt/replica/Caddyfile --adapter caddyfile &
caddy_pid=$!
xmpp_pid=""
if [ "${XMPP_ENABLED:-false}" = true ]; then
  node /opt/replica/xmpp-alpha.mjs &
  xmpp_pid=$!
fi
cleanup() {
  if [ -n "$xmpp_pid" ]; then
    kill "$xmpp_pid" 2>/dev/null || true
    wait "$xmpp_pid" 2>/dev/null || true
  fi
  kill "$lws_pid" "$caddy_pid" 2>/dev/null || true
  wait "$lws_pid" "$caddy_pid" 2>/dev/null || true
}
trap cleanup EXIT
trap 'exit 0' INT TERM
while kill -0 "$lws_pid" 2>/dev/null && kill -0 "$caddy_pid" 2>/dev/null; do
  if [ -n "$xmpp_pid" ] && ! kill -0 "$xmpp_pid" 2>/dev/null; then
    wait "$xmpp_pid" 2>/dev/null || true
    echo 'XMPP alpha exited; LWS and HTTPS continue. Inspect logs before restarting.' >&2
    xmpp_pid=""
  fi
  sleep 1
done
exit 1
