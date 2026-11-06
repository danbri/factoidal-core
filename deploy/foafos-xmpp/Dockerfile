# foafos-xmpp: the one Fly box for Foafos: a public test XMPP server and its pods.
# Build context is this directory.
FROM caddy:2.10.2 AS acme
FROM node:22-bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends gosu ca-certificates \
    && rm -rf /var/lib/apt/lists/*
ARG FACTOIDAL_VERSION
WORKDIR /opt/xmpp
RUN if [ -z "${FACTOIDAL_VERSION}" ]; then echo 'Set FACTOIDAL_VERSION to an exact npm version' >&2; exit 2; fi; \
    npm install --omit=dev --ignore-scripts --save-exact "@factoidal/core@${FACTOIDAL_VERSION}" @xmpp/client@0.14.0 \
    && npm cache clean --force
# The XMPP host is plain JavaScript. These two files come from a pinned commit,
# for code newer than the npm version. Empty FACTOIDAL_HOST_COMMIT is not valid:
# remove these lines when the npm version carries `--tls-port`.
ARG FACTOIDAL_HOST_COMMIT
ADD --chmod=644 https://raw.githubusercontent.com/danbri/factoidal-core/${FACTOIDAL_HOST_COMMIT}/npm/factoidal/xmpp/server.mjs node_modules/@factoidal/core/xmpp/server.mjs
ADD --chmod=755 https://raw.githubusercontent.com/danbri/factoidal-core/${FACTOIDAL_HOST_COMMIT}/npm/factoidal/bin/factoidal.mjs node_modules/@factoidal/core/bin/factoidal.mjs
# The pod lives with Foafos, in danbri/glitchcan-minigam, pinned like the host above.
ARG FOAFOS_POD_COMMIT
ADD --chmod=644 https://raw.githubusercontent.com/danbri/glitchcan-minigam/${FOAFOS_POD_COMMIT}/packages/foafos/pod/pod.mjs pod.mjs
COPY --from=acme /usr/bin/caddy /usr/bin/caddy
COPY Caddyfile entrypoint.sh ./
RUN chmod 755 entrypoint.sh
ENV XDG_DATA_HOME=/data XDG_CONFIG_HOME=/data/config
EXPOSE 5222 5223 5281 8080 8090
ENTRYPOINT ["/opt/xmpp/entrypoint.sh"]
