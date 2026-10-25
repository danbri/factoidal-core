# The dataset view of an LWS storage (first version)

Issue: https://github.com/danbri/factoidal/issues/1011. Owner, 2026-10-25,
verbatim: "LWS dataset-view - implement something for practical experience".

LWS 1.0 Core (https://w3c.github.io/lws-protocol/lws10-core/) defines
resources, containers, metadata resources and their representations. It does
not define an RDF dataset made from a storage. The definition below is
Factoidal's. It is not an LWS Working Group decision.

## Definition

A snapshot is what one client read from one storage: the containment pairs
of the container listings, and for each RDF resource read, its IRI, its
`ETag`, its `Last-Modified` and the RDF graph of its representation.

The view of a snapshot (`formal/lean4/L4Factoidal/LWS/DatasetView.lean`,
`view`) is the RDF dataset (RDF 1.1 Concepts §4) with:

- a default graph with one triple `<container> ldp:contains <member>` for
  each containment pair (LDP 1.0 §5.2.1.4; the Solid Protocol, which this
  repository's LWS server uses as its binding, uses it too);
- one named graph for each RDF resource (data or metadata), whose name is
  the resource IRI. If one IRI was read twice, the first read is used.

The blank nodes of two reads are distinct (RDF 1.1 Concepts §3.4); each read
is parsed in its own blank-node scope.

Proved: the graph names are distinct (`view_names_nodup`); the names are
the IRIs read (`view_mem_names`); a change of one resource's representation
(`Snapshot.replace`) keeps the default graph and the names and changes the
graph of that IRI only (`view_replace`, `view_replace_lookup`).

Decision made here, Claude-inferred (not an owner decision): containment is
the default graph, not a named graph. Reason: a named graph for containment
needs a name that no resource IRI can have, and LWS gives none; the default
graph has no name. A consequence: `GRAPH ?g { ... }` ranges over resources
only.

## The source and its assumption

`formal/lean4/L4Factoidal/Dataflow/LwsSource.lean`: `lwsSource st s` is a
`Sourced` whose den is `view (st.at s)`, the view of the storage `st` at the
snapshot instant over the resources of `s`. The record that the evaluator
runs is built from the reads. They agree under one named assumption,
`lwsReadsAtSnapshot` (`ReadsAtSnapshot`): each GET returned the
representation its ETag identifies at the snapshot instant, and the
listings were the containment at that instant. `lwsSource_query_sound` is
`Sourced.query_sound` for this source. Ratchet line:
`foundation/assumptions.txt`, `name:lwsReadsAtSnapshot`.

## Where the decisions are

| Decision | Where |
|---|---|
| which listing members are containers, which are read, which are left out (media type with no RDF reader) | `LWS/DatasetViewRead.lean`, `planListing` |
| ETag, Last-Modified, media type, parse, blank-node scope of each read | `readOfDone` |
| the view, the evidence | `view`, `viewOfDocsJson`; wasm ops `lwsViewPlan`, `lwsDatasetView` |
| the HTTP requests | the LWS client (`LWS/Client/Machine.lean`) |
| the loop | `npm/factoidal/lws/dataset.mjs` (in `tools/host-purity-lint.sh`, group 1) |

## Limits of this version

- Full crawl on every open: one `list` per container, one GET per RDF
  resource. No search index (`lws10-searchindex`), no caching, no
  conditional requests.
- Metadata resources are not crawled (a listing does not enumerate them).
  The definition admits them.
- The crawl is a sequence of GETs. A write during the crawl can give a
  dataset that the storage never held at one instant; the assumption above
  is then false. A check is to send HEAD for each resource after the crawl
  and compare the ETags. Not done.
- The evidence lists every resource read, not only the resources that
  contributed to an answer.
- A TriG or N-Quads resource gives its default graph only.
- Tested against this repository's server only (KR5 needs a second server).

## Questions for the LWS Working Group

1. Should LWS define an RDF dataset view of a storage, or of a container?
2. If yes: is containment part of the view, and with which predicate (LWS
   has its own listing format, `items`)? In the default graph or in a named
   graph with a defined name?
3. Are metadata resources graphs of the view, and how is a metadata
   resource linked to the resource it describes?
4. Can a server give a consistent snapshot (one ETag for the whole storage
   or container, or a snapshot token), so a client need not assume one?
