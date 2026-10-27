# syntax=docker/dockerfile:1
# One image of the published npm package @factoidal/core. The image runs the
# `factoidal` command line; the first argument picks the command, so one image
# serves every command (serve, lws-serve, solid-serve, authz-serve,
# xmpp-serve, query, ...). It holds no per-server logic. Notes: README.md.
#
# The source is the package at FACTOIDAL_VERSION, checked against
# FACTOIDAL_INTEGRITY (the registry's dist.integrity, sha512).
#   docker build --build-arg FACTOIDAL_VERSION=0.16.0 \
#     --build-arg FACTOIDAL_INTEGRITY="$(npm view @factoidal/core@0.16.0 dist.integrity)" .
# To build from an unpacked package directory instead (no registry access):
#   docker build --build-context source=../../npm/factoidal -t factoidal .
ARG FACTOIDAL_VERSION=0.16.0
ARG FACTOIDAL_INTEGRITY=sha512-5hYuxtlZ75LwPO0eqHSEHqnriBCtrn2k9fbZYPUjSlDY2mE+hqji+5YupArRk111iBlkxz5TvXabd08smUFhcQ==

# ---- source: the package, unpacked ----
FROM node:24.21.0-trixie-slim AS fetch
ARG FACTOIDAL_VERSION
ARG FACTOIDAL_INTEGRITY
WORKDIR /fetch
RUN npm pack --silent "@factoidal/core@${FACTOIDAL_VERSION}" > name.txt \
 && node -e ' \
      const fs = require("fs"), crypto = require("crypto"); \
      const [alg, want] = process.argv[1].split("-"); \
      const got = crypto.createHash(alg).update(fs.readFileSync(fs.readFileSync("name.txt", "utf8").trim())).digest("base64"); \
      if (got !== want) { console.error("integrity mismatch: " + alg + "-" + got); process.exit(1) }' \
      "$FACTOIDAL_INTEGRITY" \
 && mkdir /src && tar -xzf "$(cat name.txt)" -C /src --strip-components=1
FROM scratch AS source
COPY --from=fetch /src/ /

# ---- runtime ----
FROM node:24.21.0-trixie-slim
COPY --from=source / /opt/factoidal/
RUN ln -s /opt/factoidal/bin/factoidal.mjs /usr/local/bin/factoidal \
 && mkdir -p /data && chown node:node /data
USER node
WORKDIR /data
VOLUME /data
ENTRYPOINT ["factoidal"]
CMD ["--help"]
