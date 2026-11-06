# Compositor pod discovery and conditional storage

The compositor storage adapter reads a caller-supplied FOAF/Turtle bootstrap
through the public LWS client. It passes that exact text and its document base
URI to the public Lean RDF parser, then queries the resulting graph with Lean
SPARQL. It discovers only explicit `pim:storage` objects and subjects explicitly
typed `pim:Storage`. It does not follow acquaintances, `seeAlso`, storage-description
links, or infer a pod from a profile's origin. Each root retains its bootstrap,
subject and predicate. This is declaration provenance, not ownership,
authorization, or a storage conformance verdict.

`docs/web/hub/data-compositor/pod-storage.mjs` exports:

- `discoverPods({core,client,bootstrapUrl})`: roots with declaration provenance,
  and rejected noncanonical/unsafe root declarations.
- `rememberPods(discovery,storage)` and `loadKnownPods(storage)`: allowlisted pod
  metadata only, merging discoveries across bootstraps. No client, bearer token,
  authentication session, or arbitrary extra property is persisted.
- `revalidateKnownPod({core,client,pod})`: re-read the bootstrap and require the
  same declaration in its current graph.
- `rootedPath(root,filename)`: one safe editor filename under the selected root.
- `createPodStorage({core,client,root})`: list/load/save operations. Passing a
  provenance object revalidates the bootstrap before **every save**, including
  after worker restarts. Passing a string means an explicitly selected manual
  root and does not claim bootstrap provenance.

A load returns exact UTF-8 text and the server ETag, or null when no ETag was
provided. Updating requires the ETag from the loaded document. Creating requires
explicit `create:true`, mapped to the LWS client's `ifNoneMatchStar` precondition.
Updates use `ifMatch` with the supplied tag. Both set `retry412:0`. A conflict is
returned as the existing LWS client error; no fallback overwrite is attempted.
A missing ETag prevents updating, rather than fetching a newer one and silently
replacing a concurrent edit. The adapter does not change the JSON pipeline
schema; the UI owns its validation.

Targets are confined to the selected canonical HTTP(S) root. Credentials in
URLs, query/fragment components, repaired traversal, encoded dot/separator/percent
paths, sibling roots and cross-origin targets are refused before client calls.
Listings containing actionable out-of-root members are refused. These are
editor-target restrictions, not changes to the LWS protocol or token scope.

The existing LWS client remains responsible for HTTP request construction,
authentication, redirects, paging, conditional writes and response interpretation.
Its default Node/Deno engine loader is now imported lazily: a browser can import
the same client module and inject the already loaded public core engine without
loading a file-backed Node store host or another WebAssembly instance. Hosting
must expose that patched module and its existing errors module. Credentials
remain in the explicitly supplied client's transient session.

## Validation

`tests/hub/compositor_pod_storage_test.mjs` includes real published-engine RDF
parsing/SPARQL discovery, safe metadata persistence, provenance revalidation,
exact text/ETag transport, target confinement, error propagation and browser-only
module-import controls. A VM browser context allows only the client and errors
modules and has no Node loader or Buffer; its request/response transport passes.

An additional test connects the actual published engine's LWS client and server
state machines through a byte/HTTP-field transport. Creation, exact load and tag,
listing, matching-tag update, refused create collision and refused stale-tag
update all pass. This tests engine behavior rather than a stub's interpretation
of option names. The socket roundtrip test starts an isolated temporary LWS
storage on loopback and additionally exercises FOAF bootstrap discovery through
that server; it must run on a host that permits loopback binding. The child
sandbox refused binding with EPERM. The parent then ran the full nine-test
suite on the host with Node 22: all nine passed, including real loopback TCP
(about 696 ms total). The tenth, additional actual-engine in-process test also
passed separately in the child. There are no test skips or user-pod network writes.

No Lean build, large cache copy, release dispatch, or deployment was performed
for this adapter. Public pod/CORS/authentication interoperability still depends
on the target server and browser policy; an in-process test does not establish
those properties.

## 2026-11-01 browser HTTP boundary check

The real loopback test now configures the exact hub origin
`https://danbri.github.io`. It checks PUT preflight with Authorization,
Content-Type and conditional-write headers, ETag exposure, absence of cookie
credentials permission, and no allowed-origin response for an unlisted site.
All client requests in the roundtrip carry the allowed Origin. Ten storage
tests pass. Node does not enforce browser CORS or private-network policy, so
this remains HTTP-boundary evidence, not a real-browser or actual-user-pod test.

## Response budget

The compositor storage worker injects `boundedFetch` into the shared LWS client.
Each delivered response is limited to 2 MiB, including bootstrap/profile and
listing responses; oversized streams are cancelled. This counts actual stream
bytes, not Content-Length. Three transport regression groups cover exact-limit
Unicode bytes, status/ETag preservation, chunked overrun with a false header,
cancellation, empty responses and read failures. They pass and are included
in the package compositor wrapper (36 expected tests). Browser-internal network
buffering and a single already-delivered oversized chunk are outside this bound.
This adds no authorization or LWS protocol decisions to the host. It is an
application budget; large pod listings may need narrower folders/paging.
