# syntax=docker/dockerfile:1
# Factoidal's LWS server (factoidal lws-serve) with its authorization server
# (factoidal authz-serve), as one container that keeps the target contract of
# Touchstone (https://github.com/ebremer/touchstone, targetservers/README.md,
# "The contract"): plain HTTP on port 8080, public base URL from LWS_PUBLIC_URL,
# the issuer at LWS_PUBLIC_URL, the storage given to LWS_OWNER, state in /data,
# a user other than root. Operating notes: README.md in this directory.
#
# The source is the published package @factoidal/core at FACTOIDAL_VERSION,
# checked against FACTOIDAL_INTEGRITY (the registry's dist.integrity). Every
# protocol decision in it is made by Lean 4 code compiled to one wasm module.
# To build a local checkout instead (npm/factoidal after a wasm build):
#   docker build --build-context source=../../npm/factoidal -t factoidal-lws .
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
COPY front.mjs entrypoint.sh /opt/lws-target/
RUN ln -s /opt/factoidal/bin/factoidal.mjs /usr/local/bin/factoidal \
 && chmod 0755 /opt/lws-target/entrypoint.sh \
 && mkdir /data && chown node:node /data
USER node
VOLUME /data
EXPOSE 8080
ENTRYPOINT ["/opt/lws-target/entrypoint.sh"]
