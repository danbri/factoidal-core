# LWS drafts: two inconsistencies found by the Touchstone work (2026-10-21)

Draft text for the owner to file on https://github.com/w3c/lws-protocol/issues.
Owner decision, 2026-10-21: "Draft text for you". Not posted by an agent.
Source: w3c/lws-protocol at commit 9a08ff65a6670cc5d308ed5e531032f23af30fcc
(2026-10-19). Found while making `factoidal lws-serve` pass Touchstone
(https://github.com/danbri/factoidal/issues/911,
https://github.com/danbri/factoidal/issues/912).

## Issue 1: schema.org namespace, `http` or `https`

The core draft and the vocabulary give different IRIs for the same terms.

- `lws10-core/container-representation.md` line 77 declares
  `@prefix schema: <http://schema.org/> .`, and its examples (lines 106 and
  111) use `<http://schema.org/size>`. The vocabulary snapshot
  `lws10-vocab/SNAPSHOTS/DNOTE-lws10-vocab-20260714/Overview.html` also uses
  `http://schema.org/`.
- `lws10-vocab/vocabulary.yml` line 10 gives the prefix value
  `https://schema.org/`.
- The JSON-LD context URL `https://www.w3.org/ns/lws/v1` answers 404
  (checked 2026-10-21), so a client cannot read the mapping that the JSON
  form uses.

An RDF client that reads a Turtle or JSON-LD container representation gets
different triples depending on which document the server followed. Touchstone
test `container-lws-profile-turtle` expects `http://schema.org/size`.

Proposed resolution: choose one namespace, make the examples, the vocabulary
and the context agree, and publish the context at its URL.

## Issue 2: is resource `type` server-managed or client-settable?

- `lws10-core/Operations/metadata.md` line 29, Metadata Types table: "System
  Managed | Maintained by the server; Read-Only. Includes `linkset`, `type`,
  `format`, `size`, `modified`."
- `lws10-index/index.html` (the type index and search draft): "servers SHOULD
  derive resource types from HTTP Link headers provided by the client during
  resource creation or modification, combined with the server's intrinsic
  knowledge of the resource's state (such as native LWS classes ...)".
- Touchstone test `type-search-reflects-update` expects a `PUT` with `Prefer:
  set-linkset` and a `Link: <...>; rel="type"` header to succeed.

These cannot both hold for the same link relation. Our reading, used in
`L4Factoidal/LWS/Linkset.lean`: the LWS class link (`lws:Container`,
`lws:DataResource`) is server-managed and a change to it gets 409; other
`rel="type"` links are types declared by the client and are stored and indexed.

Proposed resolution: state this split in §Metadata (server-managed LWS class;
client-declared additional types), or state that `type` is fully
server-managed and change the index draft to match.
