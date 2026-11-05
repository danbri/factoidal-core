# Build context is THIS DIRECTORY, never the repository or laptop home.
FROM caddy:2.10.2 AS proxy
FROM node:22-bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends gosu ca-certificates \
    && rm -rf /var/lib/apt/lists/*
# Resolve the npm latest tag before invoking Docker and pass its exact version
# here. A version change invalidates this install layer instead of reusing a
# cached `latest` resolution. Exact versions also support audit rebuilds.
ARG FACTOIDAL_VERSION
WORKDIR /opt/replica
RUN if [ -z "${FACTOIDAL_VERSION}" ]; then echo 'Set FACTOIDAL_VERSION to an exact npm version' >&2; exit 2; fi; \
    npm install --omit=dev --ignore-scripts --save-exact "@factoidal/core@${FACTOIDAL_VERSION}" \
    && npm cache clean --force
COPY --from=proxy /usr/bin/caddy /usr/bin/caddy
COPY server.mjs config.mjs xmpp-alpha.mjs webdav-readonly.mjs Caddyfile entrypoint.sh ./
COPY public/ /srv/site/
RUN mkdir -p /data/lws /data/xmpp /data/caddy /config /srv/site \
    && chown -R node:node /data /config /srv/site \
    && chmod 755 entrypoint.sh
# Initialize fresh Fly volume ownership, then entrypoint drops to node.
USER root
ENV XDG_DATA_HOME=/data XDG_CONFIG_HOME=/config
EXPOSE 8080 8443
ENTRYPOINT ["/opt/replica/entrypoint.sh"]
