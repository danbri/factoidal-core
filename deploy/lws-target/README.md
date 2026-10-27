# Factoidal LWS server as a Docker target

One container with `factoidal lws-serve --authz`: the W3C Linked Web Storage
1.0 server and its OAuth 2.0 authorization server in one process on one port,
made so that another party can test it with Docker alone. It keeps the
target contract of Touchstone, the LWS conformance harness of
https://github.com/ebremer/touchstone (`targetservers/README.md`, "The
contract"). Owner, 2026-10-26: "Idea is we write dockerfiles for our lws server
and they or someone hammer it in a docker based server".

Every protocol decision is made by the Lean 4 code of `@factoidal/core` (one
wasm module), including which requests are the authorization server's
(`formal/lean4/L4Factoidal/Authz/Mount.lean`). The shell script only turns
the settings into command-line options.

| file | what it does |
| --- | --- |
| `Dockerfile` | fetches `@factoidal/core` at `FACTOIDAL_VERSION`, checks it against `FACTOIDAL_INTEGRITY` (the registry's `dist.integrity`), runs as user `node`, state in `/data` |
| `entrypoint.sh` | `factoidal lws-serve /data/storage --authz /data/as --base LWS_PUBLIC_URL/ --port 8080 ...` |
| `touchstone.env` | how Touchstone's `run-all.sh` tests this target |
| `compose.service.yaml` | the service entry for Touchstone's `targetservers/compose.yaml` |

`lws-serve --authz` is in 0.18.0 and later; the Dockerfile pins 0.18.0.

## Settings

| variable | meaning |
| --- | --- |
| `LWS_PUBLIC_URL` | public base URL, no trailing slash, e.g. `https://host.example/targets/factoidal`. Storage root `LWS_PUBLIC_URL/`; issuer `LWS_PUBLIC_URL` |
| `LWS_OWNER` | the agent with full control of a new storage (required unless `LWS_INSECURE_NO_AUTH=1`) |
| `LWS_PAGE_SIZE` | container page size (default 4) |
| `LWS_STORAGE` | `files` (default) or `snapshot` |
| `LWS_ALLOW_PRIVATE_FETCH=1` | the authorization server may fetch identity documents over http and from private addresses (test networks only) |
| `LWS_INSECURE_NO_AUTH=1` | no authorization (development only) |
| `FACTOIDAL_LWS_KEY` | seal the storage and the signing keys at rest |

The issuer is `LWS_PUBLIC_URL`. Its metadata is at
`/.well-known/lws-configuration` + the issuer's path (RFC 8414 §3.1); the
token endpoint and the JWK Set are at `LWS_PUBLIC_URL/.well-known/lws-token`
and `LWS_PUBLIC_URL/.well-known/lws-jwks`. A proxy in front may remove the
path of `LWS_PUBLIC_URL` from each request (Touchstone's router, `strip`
mode): the server reads both forms of every path.

## Build and run

```
docker build -t factoidal-lws deploy/lws-target
docker run -p 8080:8080 -v factoidal-lws:/data \
  -e LWS_PUBLIC_URL=http://localhost:8080 -e LWS_OWNER=https://id.example/alice \
  factoidal-lws
```

A local checkout instead of the published package (after a wasm build):
`docker build --build-context source=npm/factoidal -t factoidal-lws deploy/lws-target`.

The private signing key, for a harness that mints test tokens
(`HarnessIssuedTokens`): `docker exec <container> factoidal authz-keys /data/as --private`.
Never publish that output.

## In Touchstone's targetservers

Copy this directory to `targetservers/factoidal/`, add `compose.service.yaml`
to `compose.yaml` (and the two lines it names to `compose.local.yaml`), add
`factoidal` to the router's target list if the router has one, then
`targetservers/run-all.sh factoidal`.

## Checked, 2026-10-27 (image built from a local checkout with `lws-serve --authz`)

Container with `LWS_PUBLIC_URL=http://localhost:18090/targets/factoidal`,
probed with curl at the paths a prefix-stripping proxy sends:

- `/.well-known/lws-configuration`: RFC 8414 metadata, issuer
  `.../targets/factoidal`, `token_endpoint` `.../targets/factoidal/.well-known/lws-token`,
  `jwks_uri` `.../targets/factoidal/.well-known/lws-jwks`; `/.well-known/lws-jwks` 200.
- `/.well-known/oauth-protected-resource/x`: `resource` `.../targets/factoidal/x`.
- the whole form `/.well-known/lws-configuration/targets/factoidal`: 200.
- anonymous `GET /`: 401 with `resource_metadata`.
- `factoidal authz-keys /data/as --private` prints the private JWK Set.

The whole token flow (401, both metadata documents, token exchange with a
did:key credential, PUT and GET as the owner, `/token` and `/jwks` as storage
resources), at an origin and behind a proxy that removes `/targets/f`:
`node tests/authz/mounted.mjs`, 6 pass, 0 fail (out of 6). Touchstone scores of
the same server outside Docker (`tools/lws-touchstone.sh`) are in
`docs/designissues/2026-10-21-lws-touchstone-run.md`.

## Known limits

- The 3 SAML tests are inapplicable: this target configures no SAML identity
  provider (`--saml-idp`), so it does not declare `SamlTrust`
  (https://github.com/danbri/factoidal/issues/926).
