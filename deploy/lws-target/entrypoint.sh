#!/bin/sh
# Starts Factoidal's LWS server with its authorization server on port 8080:
# one process, `factoidal lws-serve --authz` (README.md in this directory).
# The engine decides which requests are the authorization server's
# (formal/lean4/L4Factoidal/Authz/Mount.lean). Settings, from the environment:
#
#   LWS_PUBLIC_URL     the public base URL without a trailing slash, e.g.
#                      https://host.example/targets/factoidal. The storage root
#                      is LWS_PUBLIC_URL/ and the issuer is LWS_PUBLIC_URL. A proxy
#                      in front may remove the URL's path from each request.
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
set -- /data/storage --host 0.0.0.0 --port 8080 --base "${LWS_PUBLIC_URL%/}/" \
  --page-size "${LWS_PAGE_SIZE:-4}" --storage "${LWS_STORAGE:-files}"
if [ "${LWS_INSECURE_NO_AUTH:-0}" = 1 ]; then
  set -- "$@" --insecure-no-auth
else
  : "${LWS_OWNER:?LWS_OWNER must name the agent that owns the storage}"
  set -- "$@" --authz /data/as --owner "$LWS_OWNER"
  [ "${LWS_ALLOW_PRIVATE_FETCH:-0}" = 1 ] && set -- "$@" --allow-http --allow-private-fetch
fi
mkdir -p /data/storage
exec factoidal lws-serve "$@"
