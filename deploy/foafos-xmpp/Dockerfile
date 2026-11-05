# foafos-xmpp: a public test XMPP server. Build context is this directory.
FROM caddy:2.10.2 AS acme
FROM node:22-bookworm-slim
RUN apt-get update && apt-get install -y --no-install-recommends gosu ca-certificates \
    && rm -rf /var/lib/apt/lists/*
ARG FACTOIDAL_VERSION
WORKDIR /opt/xmpp
RUN if [ -z "${FACTOIDAL_VERSION}" ]; then echo 'Set FACTOIDAL_VERSION to an exact npm version' >&2; exit 2; fi; \
    npm install --omit=dev --ignore-scripts --save-exact "@factoidal/core@${FACTOIDAL_VERSION}" \
    && npm cache clean --force
COPY --from=acme /usr/bin/caddy /usr/bin/caddy
COPY Caddyfile entrypoint.sh ./
RUN chmod 755 entrypoint.sh
ENV XDG_DATA_HOME=/data XDG_CONFIG_HOME=/data/config
EXPOSE 5222 5223 5281 8080
ENTRYPOINT ["/opt/xmpp/entrypoint.sh"]
