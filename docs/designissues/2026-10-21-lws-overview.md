# Linked Web Storage in Factoidal: what it is, what it does, what is missing (2026-10-21)

One-page overview, written at the owner's request ("in one page explain what
LWS is and what we can do with this tool we made, what is missing, what
strengths it has"). Detail: `skills/lws-solid/SKILL.md`,
`docs/lws-solid-conformance.md`, `docs/designissues/2026-10-21-lws-touchstone-run.md`.

## What LWS is

Linked Web Storage (LWS) is a protocol that the W3C Linked Web Storage Working
Group writes (https://w3c.github.io/lws-protocol/; Working Draft of 19 October
2026). It continues the Solid Protocol. A person or an organisation keeps data
in a storage that they choose; applications read and write it over HTTP with
the permission of the owner. The drafts define:

- containers (folders) and data resources (any bytes: RDF, JSON, images);
- create, read, update and delete, with conditional requests, byte ranges,
  JSON Patch and paged container listings;
- metadata per resource as an RFC 9264 linkset;
- discovery through a storage description;
- authorization by bearer tokens from an authorization server that the storage
  trusts (OpenID Connect, SAML, self-signed controlled identifiers);
- notifications (webhooks), access requests and grants, moving resources, and
  a type index with type search.

## What our tool does

`npx factoidal lws-serve DIR` starts an LWS storage server from the npm package
`@factoidal/core`. It supports:

- containers and data resources stored byte for byte; JSON Patch; ranges;
  `If-Match`, `If-None-Match`, `If-Modified-Since`, `If-Unmodified-Since`;
  pagination (`--page-size`); linksets with client-managed links; container
  listings as JSON, Turtle and JSON-LD; the storage description;
- authorization on by default: bearer token signature, issuer, audience and
  time checks, then Web Access Control (`--issuer`, `--owner`;
  `--insecure-no-auth` for development);
- webhook notifications with RFC 9421 signatures, retry, and a read check at
  delivery time;
- the Type Index and Type Search services (`lws10-index`): types from
  `Link rel="type"`, the native class and Turtle content, a QUERY filter in
  conjunctive normal form over types and indexed relations, answers filtered
  by the requester's read access (https://github.com/danbri/factoidal/issues/912);
- persistence in `DIR/lws-state.json`;
- encryption at rest of that file, off by default: with `FACTOIDAL_LWS_KEY`
  set to a 32-byte key, the file is sealed with ChaCha20-Poly1305 (HACL*)
  under a new random nonce for every write and authenticated at start; a
  wrong key or a changed file stops the start
  (https://github.com/danbri/factoidal/issues/921). It protects the file on
  disk only: not the memory of a running server, not the key in its
  environment, not what the server answers to clients.

The same engine serves the Solid Protocol (`solid-serve`) and has a Solid
client. The same package also parses, queries (SPARQL), validates (SHACL,
ShEx) and reasons over RDF.

## Strengths

- Every protocol decision (status codes, headers, authorization, notification
  content) is made in Lean 4. The JavaScript host only handles sockets, files
  and timers, and a lint checks this.
- Some properties are proved, for example: pages of a container list each
  member once; a byte range selects the exact bytes; a new name is always
  free; dates written by the server parse back to the same instant; a
  notification goes only to a subscriber that can read the resource. Most
  other rules are checked by `#guard` examples at build time.
- An external check: Touchstone, the conformance harness of another
  implementer (221 tests), gives 0 failed on the issue-911 branch, with
  authorization 146 passed, 75 inapplicable. Confirmation on `main` is in
  progress.
- Cost is linear in body size: a PUT of 100,000 triples takes 85 ms, a GET
  40 ms (https://github.com/danbri/factoidal/issues/903).
- The sealed snapshot has theorems over any AEAD with RFC 8439 correctness
  (open inverts seal; a changed format, cipher or key id, or a wrong key, is
  refused; a plaintext comes back only through the AEAD's authentication);
  every one-character change of a sealed file is refused at run time with the
  real cipher (`L4Factoidal/LWS/SnapshotSeal.lean`, `l4crypto-probe`,
  `tests/lws/encryption.mjs`). Cost, measured 2026-10-21 (wasm in Node, a storage of about 1,050 small
  resources, 100 PUTs, two runs): a PUT that writes the snapshot takes 133 to
  143 ms sealed against 49 to 54 ms clear; the file is 1.33 times larger
  (658,069 against 493,434 bytes); a restart takes 378 to 437 ms against 183
  to 190 ms. `node tests/lws/scaling.mjs` with the variable set: 12 pass, 0
  fail (out of 12); reopen at 2,000 resources 439 ms sealed against 241 ms
  clear, ratio 4m/m 5.56 against 4.81 (bound 6.0).
- One WebAssembly module in Node; the same package for every function.

## What is missing

- Access requests and grants, 17 tests, and 10 more tests that need them:
  https://github.com/danbri/factoidal/issues/913.
- Moving resources, 11 tests: https://github.com/danbri/factoidal/issues/914
  (in progress).
- Notification hardening (rate limits, inbox checks, loops through another
  host name): https://github.com/danbri/factoidal/issues/915. Only the webhook
  channel exists; no streaming channel.
- Storage: the whole state is held in memory and written to one snapshot file,
  so a storage is limited by memory. A storage on Shardborough is not started.
- No authorization server of our own; the storage trusts an external one.
- Not on the public results page (https://ebremer.com/lws/conformance); owner
  decision 2026-10-21: "Not yet". No users outside the project.
- The drafts change often and contradict themselves in two places
  (`docs/designissues/2026-10-21-lws-draft-inconsistencies.md`).
