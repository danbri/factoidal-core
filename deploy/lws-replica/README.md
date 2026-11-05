# HTTPS website and LWS push receiver

Optional [private XMPP alpha test service](XMPP.md) can run on the same Machine.
It is disabled by default and adds no public XMPP port.

Source configuration for the deployed `danbri-foafpod` Fly alpha. This is a
single-writer resource push receiver, NOT yet journaled replication, atomic
multi-resource snapshots, automatic synchronization or failover. XMPP is a
private alpha service; it has no public Fly service port.

Last live status check (2026-11-01): one started `lhr` Machine, 1024 MB, 1 GB
encrypted `lws_data` volume, passing `/lws/` health check, image digest
`sha256:99fe6a97773f031f303bc5eac6c4ce11ea0d49fa0136d1f6c89819a5864e409c`.
The current running image was built with `@factoidal/core` 0.28.0 according to
the deployment build log; the installed package has not been inspected inside
the live Machine. The current source recipe resolves npm `latest` per build.

* `/` serves the approved repository-root export in `public/`. It is static;
  HTML/JS execute in browsers, but server code does not execute. Directories
  without index files are browsable. LWS routes below take precedence.
* `/lws/` is the canonical pod base, publicly readable, HTTP GET/HEAD/OPTIONS
  only. Anonymous mutation is also refused by the Lean LWS authorization layer.
* `/dav/` is an unauthenticated, public read-only WebDAV view of that LWS
  endpoint. It exposes no LWS backing files. Its local integration test covers
  PROPFIND, GET and refusal of write methods; live `/dav/` behavior has not yet
  been checked against Fly.
* `/_replicate/relative-path` maps to that same LWS resource. Only PUT/DELETE
  are admitted by the proxy. Lean verifies the JWT and WAC; the laptop subject
  has Write, not Control, so it cannot edit ACLs with this credential.
* No LWS port is published: it binds loopback inside the container. Webhooks,
  grants, moves, type search and linkset writes are disabled for this receiver.
* The server has one pinned laptop PUBLIC Ed25519 key. Its private key stays
  on the laptop. Bearer tokens expire in five minutes. A stolen token remains
  usable until expiry; this is not proof of a physical laptop or DPoP.

All replicated content is public. Do not send private resources. This profile
does not replicate arbitrary source ACLs. Reuse only a new empty state volume;
rootAcl initializes a new store and is not an ACL migration mechanism. Rotate
the public key by changing configuration and restarting. Back up the volume.

## Prepare and run with Docker Compose

From this directory, create `public/` containing the repository files you
intend to publish at the website apex. Export a reviewed PUBLIC git commit,
not a live checkout containing secrets or `.git`. Do not include symlinks,
credentials, .env files, deployment configuration or private keys. This export
is intentionally explicit: the Dockerfile never copies the whole checkout.
Review the export before building. The image and static endpoint both contain
these files, and dotfiles are blocked by the proxy as an additional measure.

```sh
node laptop.mjs init "$HOME/.config/factoidal-replica"
cp "$HOME/.config/factoidal-replica/writer.jwks.json" ./writer.jwks.json
export DOMAIN=pod.example.org
export WRITER_SUBJECT=urn:example:dan-laptop
export FACTOIDAL_VERSION="$(npm view @factoidal/core dist-tags.latest)"
printf 'Building with @factoidal/core %s\n' "$FACTOIDAL_VERSION"
docker compose build
docker compose up -d
```

Use the real DNS name pointing to the host. Ports 80 and 443 must reach the
container for [Caddy automatic HTTPS](https://caddyserver.com/docs/automatic-https).
State and certificates are persistent named volumes. The process runs as uid
1000 with a read-only root filesystem under Compose. No secrets are build args
or image layers. The only copied operator key file is public and mounted at
runtime. Before every build, resolve npm's current `latest` tag to an exact
version as shown above. That exact version keys Docker's cached install layer,
so a newer published release is installed on the next build. Each resulting
image is reproducible against that resolved package version; the running
service changes only after redeploy. For an audit rebuild or rollback, set
`FACTOIDAL_VERSION=x.y.z` to the chosen exact version. Image tags are
version-pinned, not digest-pinned; use reviewed digest pins for a reproducible
release.

Create a resource from the laptop (parent containers must exist):

```sh
ORIGIN=https://pod.example.org
TOKEN=$(node laptop.mjs token "$HOME/.config/factoidal-replica" "$ORIGIN" "$WRITER_SUBJECT")
# Feed the bearer header through stdin so it is not in curl's argument list.
printf 'Authorization: Bearer %s\n' "$TOKEN" | curl --fail-with-body \
  --header @- --header 'Content-Type: application/json' \
  --header 'If-None-Match: *' --upload-file pipeline.json \
  "$ORIGIN/_replicate/pipeline.json"
unset TOKEN
curl --fail "$ORIGIN/lws/pipeline.json"
```

For replacement or deletion obtain the current ETag from the read endpoint
and supply `If-Match` with that exact value. Do not retry a 412 by overwriting.
The receiver currently relies on the publishing client to supply these
preconditions; it does not enforce a revision chain. Never put tokens in URLs.

## Fly.io

Use `fly.toml.example` as a starting point for a separate app. Fly terminates
public HTTPS and redirects HTTP; Caddy listens privately on port 8080. Keep
PUBLIC_ORIGIN set to the external HTTPS origin. Do not expose 3000 or configure
a public direct HTTP TCP service. The existing skosdex app is untouched.

Resolve the package before each deploy so the exact version changes the Docker
install cache key:

```sh
FACTOIDAL_VERSION="$(npm view @factoidal/core dist-tags.latest)"
printf 'Deploying with @factoidal/core %s\n' "$FACTOIDAL_VERSION"
flyctl deploy --remote-only --ha=false \
  --build-arg "FACTOIDAL_VERSION=$FACTOIDAL_VERSION" -a "$POD_APP"
```

For a deliberate audit rebuild or rollback, set `FACTOIDAL_VERSION` to an
exact version instead. The deployed app uses a persistent `lws_data` volume.
The Fly entrypoint initializes its directory ownership as root, then drops to
uid/gid 1000 before starting either service. Compose starts directly as uid
1000 using initialized named volumes.
Set `WRITER_JWKS_JSON` at runtime to the
contents of the public JWKS (Fly secrets can carry configuration too). No
private laptop key is uploaded. `public/` is baked into the image on Fly;
Docker Compose instead mounts it read-only. Rebuild to publish a new website.
The current Fly Machine uses 1024 MB after the 512 MB configuration was
OOM-killed. One Machine and one writer process per volume; do not scale this
snapshot store horizontally.

## Identity federation is separate

Recognizing Dan through Google OIDC and GitHub OAuth must not grant replication
rights. Map validated `(issuer, sub)` for Google, and a verified stable numeric
GitHub account ID for GitHub, to an owner-controlled local identity. Do not infer
links from names, emails or arbitrary RDF `sameAs`. Google ID tokens are for
the login client, not directly LWS access tokens: validate login, then issue a
pod-audience LWS access token with the permitted role. GitHub Actions OIDC is
workload identity, not interactive user login. Provider login adapters and this
identity-link configuration are NOT included in this container yet. Public
reads require no login; the laptop writer identity remains separate.

## Validation

`node --test deploy/lws-replica/security.test.mjs` from the repo root tests the
actual Lean authorization engine with signed tokens: public read, laptop write,
wrong identity/audience, expired token, ACL mutation refusal and create conflict.
Local validation used installed core 0.27.0; the deployed 0.28.0 image still
needs the same authorization and WebDAV checks. Caddy configuration is
validated independently. With `CADDY_BIN` pointing to Caddy 2.10.2,
`node --test deploy/lws-replica/proxy.test.mjs` checks real proxy routing,
method refusals, bearer forwarding, apex content and dotfile exclusion against
a mock upstream; cryptographic checks are in the separate real-engine test.
The local proxy, authorization and WebDAV tests are separate evidence; passing
local tests do not verify live Fly routing. The deployed Machine has an
operator public JWKS and the matching laptop private key remains local. Never
include private keys or pod secrets in this repository or static site export.
