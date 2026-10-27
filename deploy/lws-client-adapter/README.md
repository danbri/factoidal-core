# Factoidal LWS client adapter for the lws-client driver

`adapter.mjs` lets the driver of
[ebremer/lws-client](https://github.com/ebremer/lws-client) (`driver/PROTOCOL.md`,
`lws-driver/1`) control the Factoidal LWS client. Touchstone's client matrix
uses that driver. The client is the Lean state machine in
`formal/lean4/L4Factoidal/LWS/Client/`, reached through the npm host
`@factoidal/core/lws/client` (`npm/factoidal/lws/client.mjs`).
Tracking: https://github.com/danbri/factoidal/issues/917 (LWS client).
Design record: `docs/designissues/2026-10-22-lws-client.md`.

## Run

```
node deploy/lws-client-adapter/adapter.mjs
```

The adapter reads JSON lines on standard input and writes JSON lines on
standard output. It needs Node 22.12 or later (the package `engines` value).
It prints `hello` first, with `library` set to
`factoidal-lws-client/<package version>` and `language` set to `factoidal`.

By default it imports `../../npm/factoidal/lws/client.mjs`. Set
`FACTOIDAL_CLIENT_MODULE` to another path (or `file:` URL) of `lws/client.mjs`
to use a package that sits elsewhere. The package version comes from the
`package.json` one directory above that file.

Check it with the checker of the lws-client clone (Node 22 or later):

```
node driver/adapters/check.mjs -- node /path/to/factoidal-core/deploy/lws-client-adapter/adapter.mjs
```

Result on 2026-10-27, mock server of the clone, wasm sha256 `7a87bf45`:

```
factoidal: 31 passed, 3 failed, 3 skipped
```

The three failures and three skips are all from operations or options listed
under "Unsupported" below; the next section says which.

## What the adapter decides

Nothing about the wire (iron rule 7 of `CLAUDE.md`). Every request, header,
media type, retry, paging step and authorization step is the Lean client's.
The adapter does these things only:

1. It translates a protocol request into one client operation and returns the
   result in the protocol's shape.
2. REPORTING. The protocol's `Metadata`, `Storage` and `Item` shapes are keyed
   by Link relations (`type`, `up`, `linkset`, `lws#storage`, `first`, `next`,
   `prev`, `last`) and by members of the storage description. The client
   returns the status, the header pairs and the body. The adapter reads them
   to fill those shapes (RFC 8288 Link field parsing, resolution of relative
   references). Nothing it reads goes into a request. Open item: a Lean
   function that returns these shapes would remove this code from the host.
3. KEY SETUP. `configure` with `didKey` makes a P-256 key pair with
   `node:crypto` and computes its `did:key` (multicodec 0x1200, base58btc).
   The engine signs with the key. The same code exists in
   `tests/authz/fixtures.mjs`. Open item: a Lean function for the `did:key` of
   a P-256 key (`L4Factoidal/VC/DidKey.lean` has the Ed25519 one).
4. ERROR NAMES. `error.kind` is the protocol's name for an HTTP status
   (404 is `NotFoundError`). The engine's failure codes map to
   `AuthenticationError`, `ProtocolError`, `TransportError`,
   `InvalidArguments` or `InternalError`.
5. The `fetch` given to the client adds only what `configure` asked for: the
   `userAgent`, extra `headers`, and a `timeoutSeconds` abort.
6. A few calls give the client a URL it can use. Index and search take a URL
   inside the storage (a service endpoint does not answer with the storage
   link), so the adapter hands the client the last URL it saw in that origin.
   A linkset is reached through its resource, so the adapter remembers which
   resource each linkset URL came from.
7. Two media types are named: `application/linkset+json` for
   `update_linkset` (the client picks PUT from it), and the OpenID ID Token
   type `urn:ietf:params:oauth:token-type:id_token` for `configure` `openid`.

## Operations

36 operations in `PROTOCOL.md` section 4. 34 are in `hello.operations`.

Supported (34): `configure`, `discover_storage`, `get_storage_description`,
`head`, `read`, `read_container`, `list_container`, `create`,
`create_container`, `update`, `patch`, `delete`, `linkset_url`,
`read_linkset`, `update_linkset`, `patch_linkset`, `move`, `subscribe`,
`list_subscriptions`, `get_subscription`, `unsubscribe`,
`verify_notification`, `request_access`, `get_access_request`,
`list_access_requests`, `cancel_access_request`, `grant_access`,
`get_access_grant`, `list_access_grants`, `revoke_access_grant`,
`read_type_index`, `list_types`, `search_all`, `shutdown`.

Unsupported operations (2, answer `Unsupported`, not in `hello.operations`):

| operation | reason |
|---|---|
| `search_types` | The client follows every result page and returns the whole result. The protocol returns one page, with the page `id`. |
| `accepted_query_formats` | The client has no operation that reads the accepted query formats. |

Unsupported options (the operation stays in the list and answers
`Unsupported` when the option is given):

| operation and option | reason |
|---|---|
| `read` `rangeStart`, `rangeEnd`, `ifNoneMatch`, `prefer` | The client's `read` takes only `accept`. The checker fails on these two checks (`ifNoneMatch`, range). |
| `verify_notification` `trustedStorages` | The client's receiver has no trusted-storage list. The checker passes it in its one verify check, so that check fails. The driver leaves it out unless a test sets it. |
| `subscribe` `expires` | The client's subscribe has no expiry option. |
| `update` `ifNoneMatch` other than `*` | The client has `If-None-Match: *` only. |
| `configure` `allowInsecureHttp: false` | The client does not refuse `http`. |
| `configure` `bearer` without `realm` | The client sends a token only to URLs under a storage root. |
| `configure` `selfSigned` or `didKey` with a key other than P-256 (`EdDSA`) | The engine signs ES256 only. |
| `request_access`, `grant_access` with other than one policy | The client writes one policy per document. |
| `update_linkset`, `patch_linkset` for a linkset the adapter has not seen | See item 6. Do `head`, `read`, `linkset_url` or `read_linkset` of the resource first. |

Authentication types: `none`, `bearer` (with `realm`), `openid`, `selfSigned`
(P-256), `didKey` (ES256). `openid` carries an ID Token the caller already has
(`idToken`); the adapter gives it to the client as the RFC 8693 subject token.
The client has no OpenID sign-in of its own (authorization code flow with
PKCE), so a caller cannot ask it to obtain an ID Token:
https://github.com/danbri/factoidal/issues/1043 (LWS client OpenID sign-in).

Results the client cannot give are omitted, not invented: `read_type_index`
has no `totalItems` or page links (the client reads every page);
`contentRange` is not returned (no range option).

## Adding it to the lws-client driver and the Touchstone image

Files in `ebremer/lws-client` (do not edit that repository from here):

1. `driver/adapters/factoidal/adapter.mjs`: a copy of `adapter.mjs`.
2. `driver/server/src/main/resources/application.yaml`: under
   `lws.driver.languages`, a `factoidal` entry with
   `command: [node, adapters/factoidal/adapter.mjs]`.
3. `driver/README.md` and `driver/adapters/check.mjs` list the languages by
   hand; add `factoidal` where the others are named (the checker needs no
   change to run it).

Files in `ebremer/touchstone`:

4. `targetservers/clients/Dockerfile`: a Node stage that installs the package,
   and two `COPY` lines in the runtime stage. The image already has
   `/usr/local/bin/node` (Node 24). For example:

   ```
   FROM node:24.21.0-trixie-slim AS factoidal
   WORKDIR /opt/factoidal
   RUN npm install --no-audit --no-fund --omit=dev @factoidal/core@0.16.0
   ```

   and in the runtime stage:

   ```
   COPY --from=factoidal /opt/factoidal /opt/factoidal
   COPY --from=source /driver/adapters/factoidal/adapter.mjs driver/adapters/factoidal/
   ENV FACTOIDAL_CLIENT_MODULE=/opt/factoidal/node_modules/@factoidal/core/lws/client.mjs
   ```

   The package carries its engine at `l4-assets/l4factoidal.wasm`; the
   adapter and the client need nothing else. If the build uses
   `--build-context source=/path/to/lws-client`, step 1 and 2 are in that
   checkout. Use a package version whose wasm has the client operations
   (`lwsClientStart`, `lwsClientStep`); the adapter fails at its first
   operation with `unknown op` otherwise.
5. `targetservers/clients/application.yaml`: the same `factoidal` entry, with
   `command: [node, adapters/factoidal/adapter.mjs]` (the working directory is
   `/opt/lws-client/driver`).
6. `targetservers/interop-all.sh`: add `factoidal` to the `--languages` list in
   its comment and to any list of language names it checks.

Not verified: that the published `@factoidal/core@0.16.0` wasm carries the LWS
client operations (the adapter was checked against the wasm built in this
repository, sha256 `7a87bf45`); that the Docker build works (no image was
built); how the driver treats a language name it does not know.
