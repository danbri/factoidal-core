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

Result on 2026-10-27, mock server of the clone, branch of
https://github.com/danbri/factoidal/issues/1065 (wasm sha256 56f6d898):

```
factoidal: 37 passed, 0 failed, 0 skipped
```

Before that issue (commit ec300a9): `factoidal: 31 passed, 3 failed, 3 skipped`.
Every failure and skip came from a feature the Lean client did not have.

## What the adapter decides

Nothing about the wire and nothing about the reading of a response (iron
rule 7 of `CLAUDE.md`). It translates JSON: a protocol request becomes one
operation of the Lean client, and the `report` member of the client's answer
is the protocol's result. `tools/host-purity-lint.sh` (group 4) fails when
the file names an HTTP status, a protocol header, a key or identifier
construction, a linkset media type, an ID token type URI or a `.well-known`
path. The adapter does these things only:

1. It renames members and checks the JSON type of an argument.
2. It applies the driver's own conventions: `limit` and `truncated` on a lazy
   sequence, and the three forms of a request body (`text`, `base64`, `json`).
3. It passes `configure` to the client's session: `bearer` (`token`, `realm`),
   `openid` (`idToken`), `selfSigned` (the private JWK), `didKey` (a key the
   client makes: `createDidKey` over the wasm op `lwsClientNewKey`, from 64
   random bytes of the host's random source). It always sets the session
   member `legacyChallenge`: the driver protocol has no option for the 401
   challenge `Bearer as_uri="…", realm="…"` of the drafts before 2026-10-19,
   and the driver's Java and JS clients always follow it (css and sparq-lws
   send only that form: https://github.com/danbri/factoidal/issues/1115).
   The library's default stays off.
4. It gives the client's `fetch` only what `configure` asked for: the
   `userAgent`, extra `headers`, a `timeoutSeconds` abort.
5. It gives an access request or grant to the client as its members: one
   `policies` member per policy of the document (actions, assignee, targets,
   constraint), and the inbox; the client writes the document.
6. It gives `subscribe` its `serviceUrl` as the operation's `endpoint`, so the
   client POSTs the subscription to it with no discovery (lwsd's notification
   endpoint sends no storage link).
7. It gives a write's `ifNoneMatch` to the client whole, as
   `ifNoneMatchTags`; the client reads the entity-tag list (RFC 9110
   §13.1.2) and sends it alone or with the `If-Match` of `ifMatch`.
8. It maps `configure` `allowInsecureHttp: false` to the session option
   `requireHttps`: the client sends no request to a URL that is not https, in
   any phase, and the operation fails with `TransportError` (code
   `insecureTransport`) before the request is sent. This is stricter than
   step 8 (Transport security) of the token exchange in the lws-client
   `design/client-api.md`, which asks only the authorization server and its token endpoint to
   be https and excepts loopback hosts. When the argument is absent or
   `true`, the option is off.

Four readings that the adapter made in JavaScript until commit ec300a9 are in
Lean now (`formal/lean4/L4Factoidal/LWS/Client/`):

| was in the adapter | now in Lean |
|---|---|
| the Metadata, Item, Page, Storage and Subscription shapes from the `Link` field (RFC 8288), the header fields and the storage description; the name of an error | `Report.lean` (`metadataJson`, `itemJson`, `pageJson`, `storageJson`, `subscriptionJson`, `bodyJson`, `errorReport`); each `done` document has a `report` member, each `fail` document a `report` with the error |
| a new P-256 key and its `did:key` (and now Ed25519) | `Keys.lean` (`newAgent`), wasm op `lwsClientNewKey`; theorems `multikeyJwk?_p256`, `multikeyJwk?_ed25519` (`KeysTheorems.lean`) |
| the media type `application/linkset+json` for `update_linkset`, and the ID token type URI | operation kind `putLinkset` (the client sends a PUT in the linkset media type), session member `idToken` |
| the map from a linkset URL to its resource, and from a service to a URL inside its storage | operation members `linksetUrl`, `endpoint`, `storage`: the client takes the linkset, the service endpoint or the storage description directly |

## Operations

All 36 operations of `PROTOCOL.md` section 4 are in `hello.operations`. The
protocol operations that need an OpenID sign-in are none: `configure` `openid`
takes an ID Token the caller already has (`idToken`); the client has no
sign-in of its own (authorization code flow with PKCE), so a caller cannot
ask it to obtain an ID Token:
https://github.com/danbri/factoidal/issues/1043 (LWS client OpenID sign-in).

No option answers `Unsupported`. The last three
(https://github.com/danbri/factoidal/issues/1116) work now: `update` and
`patch` with `ifNoneMatch` entity tags, alone or with `ifMatch`
(`patch` takes them as one more case of the same precondition code, although
`PROTOCOL.md` lists no `ifNoneMatch` for it); `configure`
`allowInsecureHttp: false`; `request_access` and `grant_access` with any
number of policies. A document with no policy is `InvalidArguments`.

A session key that is neither a P-256 nor an Ed25519 private JWK of 32 bytes
ends the first operation with `InvalidArguments`. Results the client cannot
give are omitted, not invented.

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
