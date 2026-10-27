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

`lws-serve --authz` is in the releases after 0.16.0. Until one is published,
build from a local checkout (below).

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

## Checked, 2026-10-26 (image of `@factoidal/core` 0.16.0)

By hand with curl on one container, base `http://localhost:18080/targets/factoidal`,
paths as the router sends them in its `strip` mode:

- `/.well-known/lws-configuration`: the RFC 8414 metadata, issuer, token
  endpoint and `jwks_uri` under the public base; `/jwks` 200.
- `/.well-known/lws-storage`: 200 `application/lws+cid`.
- anonymous `GET /`: 401 with `resource_metadata`; that metadata at the
  router's path `/.well-known/oauth-protected-resource/` names the resource
  `.../targets/factoidal/`.
- a token signed with the key that `authz-keys --private` prints, `sub` the
  owner: `PUT` 201, `GET` 200; the same for another agent: 403.
- after `docker restart`: same key, same content.
- `LWS_INSECURE_NO_AUTH=1`: anonymous `POST` of a container 201.

These are hand checks. Touchstone scores of the same server outside Docker
(`tools/lws-touchstone.sh`) are in
`docs/designissues/2026-10-21-lws-touchstone-run.md`.

## Known limits

- The 3 SAML tests are inapplicable: the authorization server has no XML
  Signature verifier (https://github.com/danbri/factoidal/issues/926), so the
  target does not declare `SamlTrust`.
