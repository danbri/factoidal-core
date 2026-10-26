# Factoidal LWS server as a Docker target

One container with `factoidal lws-serve` (the W3C Linked Web Storage 1.0
server) and `factoidal authz-serve` (its OAuth 2.0 authorization server),
made so that another party can test it with Docker alone. It keeps the
target contract of Touchstone, the LWS conformance harness of
https://github.com/ebremer/touchstone (`targetservers/README.md`, "The
contract"). Owner, 2026-10-26: "Idea is we write dockerfiles for our lws server
and they or someone hammer it in a docker based server".

Every protocol decision is made by the Lean 4 code in the published package
`@factoidal/core` (one wasm module). The files here only start the two
servers and route by path.

| file | what it does |
| --- | --- |
| `Dockerfile` | fetches `@factoidal/core` at `FACTOIDAL_VERSION`, checks it against `FACTOIDAL_INTEGRITY` (the registry's `dist.integrity`), runs as user `node`, state in `/data` |
| `entrypoint.sh` | starts `authz-serve` (port 8082) and `lws-serve` (port 8081) on loopback, and `front.mjs` on 8080 |
| `front.mjs` | sends the authorization server paths to `authz-serve` and every other path to `lws-serve`, unchanged |
| `touchstone.env` | how Touchstone's `run-all.sh` tests this target |
| `compose.service.yaml` | the service entry for Touchstone's `targetservers/compose.yaml` |

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

The storage trusts the issuer with the issuer's JWK Set given inline
(`lws-serve --auth-config`), so the container never fetches its own public URL.

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

- The 3 SAML tests are inapplicable: `authz-serve` has no XML Signature
  verifier (https://github.com/danbri/factoidal/issues/926), so the target
  does not declare `SamlTrust`.
- A storage resource cannot be named `/token` or `/jwks` at the storage root:
  those paths go to the authorization server.
