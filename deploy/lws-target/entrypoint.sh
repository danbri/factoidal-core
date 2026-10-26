#!/bin/sh
# Starts Factoidal's LWS server and its authorization server behind one port
# (README.md in this directory). Settings, from the environment:
#
#   LWS_PUBLIC_URL     the public base URL without a trailing slash, e.g.
#                      https://host.example/targets/factoidal. The storage root
#                      is LWS_PUBLIC_URL/ and the issuer is LWS_PUBLIC_URL.
#   LWS_OWNER          the agent (WebID or CID URL) with full control of the storage.
#   LWS_PAGE_SIZE      members per page of a container listing (default 4, so that
#                      small containers span pages).
#   LWS_ALLOW_PRIVATE_FETCH=1
#                      the authorization server may fetch identity documents over
#                      http and from private addresses (a test network only).
#   LWS_INSECURE_NO_AUTH=1
#                      no authorization at all (development only).
#   LWS_STORAGE        snapshot or files (default files).
#   FACTOIDAL_LWS_KEY  if set, the storage and the signing keys are sealed at rest.
set -eu
: "${LWS_PUBLIC_URL:?LWS_PUBLIC_URL must be the public base URL, e.g. https://host.example/targets/factoidal}"
PUBLIC=${LWS_PUBLIC_URL%/}
PAGE=${LWS_PAGE_SIZE:-4}
STORAGE=${LWS_STORAGE:-files}
mkdir -p /data/storage /data/as

if [ "${LWS_INSECURE_NO_AUTH:-0}" = 1 ]; then
  factoidal lws-serve /data/storage --insecure-no-auth --host 127.0.0.1 --port 8081 \
    --base "$PUBLIC/" --page-size "$PAGE" --storage "$STORAGE" &
  LWS_PID=$!
  AS_PID=
else
  : "${LWS_OWNER:?LWS_OWNER must name the agent that owns the storage}"
  set -- --issuer "$PUBLIC" --host 127.0.0.1 --port 8082 --resource "$PUBLIC/.well-known/lws-storage"
  [ "${LWS_ALLOW_PRIVATE_FETCH:-0}" = 1 ] && set -- "$@" --allow-http --allow-private-fetch
  factoidal authz-serve /data/as "$@" &
  AS_PID=$!
  # The storage trusts the issuer with its JWK Set given inline, so it never has to
  # reach its own public URL. authz-serve writes its key file at its first start.
  i=0
  until [ -s /data/as/authz-keys.json ]; do
    i=$((i + 1)); [ "$i" -le 100 ] || { echo "authz-serve wrote no key file" >&2; exit 1; }
    sleep 0.1
  done
  factoidal authz-keys /data/as > /data/jwks.json
  node -e '
    const fs = require("fs");
    const [issuer, file] = process.argv.slice(1);
    fs.writeFileSync(file, JSON.stringify({ issuers: [{ issuer, jwks: JSON.parse(fs.readFileSync("/data/jwks.json", "utf8")) }] }));
  ' "$PUBLIC" /data/auth-config.json
  factoidal lws-serve /data/storage --auth-config /data/auth-config.json --owner "$LWS_OWNER" \
    --host 127.0.0.1 --port 8081 --base "$PUBLIC/" --page-size "$PAGE" --storage "$STORAGE" &
  LWS_PID=$!
fi

AS_PREFIX=$(node -e 'console.log(new URL(process.argv[1]).pathname.replace(/\/+$/, ""))' "$PUBLIC") \
  node /opt/lws-target/front.mjs &
FRONT_PID=$!
trap 'kill $FRONT_PID $LWS_PID $AS_PID 2>/dev/null; exit 0' INT TERM
# Stop the container when any of the three stops.
while kill -0 "$FRONT_PID" 2>/dev/null && kill -0 "$LWS_PID" 2>/dev/null \
      && { [ -z "$AS_PID" ] || kill -0 "$AS_PID" 2>/dev/null; }; do
  sleep 1
done
echo "a process stopped; stopping the container" >&2
kill $FRONT_PID $LWS_PID $AS_PID 2>/dev/null || true
exit 1
