#!/bin/sh
# Starts Caddy, waits for the certificate, then runs the XMPP server and the pod. It restarts the XMPP server when the certificate is renewed, and the pod
# if it stops, alone.
set -eu
if [ "$(id -u)" = 0 ]; then
  mkdir -p /data/xmpp /data/caddy /data/config /data/pod-https
  chown -R node:node /data
  exec gosu node /opt/xmpp/entrypoint.sh
fi
: "${XMPP_DOMAIN:?}" "${XMPP_ACCOUNTS_B64:?}" "${XMPP_STATE_KEY:?}"
: "${POD_TOKEN:?the https pod has no other lock, so it must not start without its token}"
# A lock from before a reboot names a process id that may now belong to something
# else, and the storage then refuses to open. Nothing of ours is running yet.
rm -f /data/pod-https/lws.lock
umask 077
secrets=$(mktemp -d)
echo "$XMPP_ACCOUNTS_B64" | base64 -d > "$secrets/accounts"
printf '%s\n' "$XMPP_STATE_KEY" > "$secrets/state-key"
unset XMPP_ACCOUNTS_B64 XMPP_STATE_KEY

caddy run --config /opt/xmpp/Caddyfile --adapter caddyfile &
caddy_pid=$!
unset POD_TOKEN

find_cert() { find /data/caddy/certificates -name "$XMPP_DOMAIN.crt" 2>/dev/null | head -1; }
n=0
while [ -z "$(find_cert)" ]; do
  n=$((n + 1))
  if [ "$n" -gt 300 ]; then echo 'no certificate after 300 seconds' >&2; exit 1; fi
  kill -0 "$caddy_pid"
  sleep 1
done
crt=$(find_cert)
key="${crt%.crt}.key"

xmpp_pid=""
pod_pid=""
start_xmpp() {
  # shellcheck disable=SC2086
  node /opt/xmpp/node_modules/@factoidal/core/bin/factoidal.mjs xmpp-serve /data/xmpp \
    --domain "$XMPP_DOMAIN" --muc "rooms.$XMPP_DOMAIN" --host 0.0.0.0 \
    --accounts "$secrets/accounts" --state-key "$secrets/state-key" \
    --cert "$crt" --key "$key" --starttls --port 5222 --tls-port 5223 \
    --max-connections 200 --login-timeout 30 \
    --ws-port 5281 --ws-origin https://danbri.github.io --ws-origin http://localhost:8080 \
    ${XMPP_EXTRA_ARGS:-} &
  xmpp_pid=$!
}
# One store, two carriages. HTTP is on loopback, reached only through Caddy, which
# holds the token. Over XMPP only foafos may ask, and only for what the route names.
start_pod() {
  POD_PASSWORD=$(sed -n 's/^pod://p' "$secrets/accounts") node /opt/xmpp/pod.mjs --base "https://$XMPP_DOMAIN:8443/" \
    --dir /data/pod-https --http 3000 --cors-origin http://localhost:8080 --cors-origin https://danbri.github.io \
    --xmpp "xmpps://$XMPP_DOMAIN:5223" --domain "$XMPP_DOMAIN" --jid pod --allow "foafos@$XMPP_DOMAIN" \
    --route 'GET,HEAD,PUT,POST,PATCH,DELETE /' --insecure-no-auth &
  pod_pid=$!
}
stop_all() { kill "$xmpp_pid" "$caddy_pid" "$pod_pid" 2>/dev/null || true; wait 2>/dev/null || true; }
trap stop_all EXIT
trap 'exit 0' INT TERM

start_xmpp
start_pod
stamp=$(cksum "$crt")
while kill -0 "$caddy_pid" 2>/dev/null; do
  if ! kill -0 "$xmpp_pid" 2>/dev/null; then echo 'xmpp-serve stopped' >&2; exit 1; fi
  # The pod must never take XMPP down with it, so it restarts alone. The lock is its own.
  if ! kill -0 "$pod_pid" 2>/dev/null; then echo 'pod stopped: restarting it' >&2; rm -f /data/pod-https/lws.lock; start_pod; fi
  if [ "$(cksum "$crt")" != "$stamp" ]; then
    echo 'certificate renewed: restarting xmpp-serve' >&2
    kill "$xmpp_pid"; wait "$xmpp_pid" 2>/dev/null || true
    stamp=$(cksum "$crt")
    start_xmpp
  fi
  sleep 30
done
exit 1
