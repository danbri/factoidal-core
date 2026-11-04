# The dataset view of an LWS storage

Issue: https://github.com/danbri/factoidal/issues/1011. Owner, 2026-10-25,
verbatim: "LWS dataset-view - implement something for practical experience".

LWS 1.0 Core (https://w3c.github.io/lws-protocol/lws10-core/) defines
resources, containers, metadata resources and their representations. It does
not define an RDF dataset made from a storage. The definitions below are
Factoidal's. They are not LWS Working Group decisions.

The current definition is version 2 (section "Version 2 (2026-11-03)"). The
section "Version 1 (2026-10-25, replaced)" stays as the record of the first
definition.

## Version 2 (2026-11-03)

Owner directive, 2026-11-03, verbatim: "Do linksets and then in a table of
contents named graph express other links from docs to their metadata based on
the extraction paradigm".

Owner answers, 2026-11-03, verbatim:

- relation IRIs: "LWS vocab where defined" (the IANA base for the rest);
- the name of the table-of-contents graph: "Storage description IRI";
- containment: "Into the TOC graph".

### Definition

A snapshot (`formal/lean4/L4Factoidal/LWS/DatasetView.lean`, `Snapshot`) is
what one client read from one storage:

- `storage`: the storage description IRI. It is the target of the link with
  relation `https://www.w3.org/ns/lws#storage` in the linkset of the first
  container listed (the storage root). Without it there is no view: the op
  `lwsDatasetView` fails with an error that says the view needs the storage
  description IRI as the name of its table-of-contents graph.
- `members`: the containment pairs of the container listings.
- `entries`: for each listing member, its IRI and kind (from the listing
  `type`: `Container` or `StorageRoot` is a container, all else is a data
  resource), and for a data resource the listing's `format`, `size` and
  `modified` when the listing gives them.
- `reads`: for each RDF document read, its IRI, `ETag`, `Last-Modified` and
  the RDF graph of its representation.
- `linksets`: for each linkset read, the resource IRI, the linkset IRI (the
  `url` of the client's `readLinkset` `done` document), its `ETag`, and its
  links. The links come from the `application/linkset+json` document
  (RFC 9264 §4.2): each link context object has `anchor` (when it has none,
  the resource IRI), and members whose name is a relation type and whose
  value is an array of target objects with `href`. A relative `anchor` or
  `href` is resolved against the linkset IRI. The view keeps (context,
  relation, target) only. Target attributes (`title`, `type`, `hreflang`)
  are not part of the view. This is a part of the definition, not a gap.

The view (`view`) is the RDF dataset (RDF 1.1 Concepts §4) with:

- an empty default graph;
- the table-of-contents graph, first in the named graphs, named by
  `storage`. It holds:
  - `<container> lws:items <member>` for each containment pair;
  - `<member> rdf:type lws:Container` or `lws:DataResource`;
  - for a data resource with listing values, `<member> dcterms:format
    "fmt"`, `<member> schema:size "n"^^xsd:long` and `<member>
    dcterms:modified "t"^^xsd:dateTime`, with the predicates, namespaces
    and datatypes of the Turtle form of a listing
    (`L4Factoidal/LWS/Binding.lean`, `containerTurtle`);
  - `<resource> <http://www.iana.org/assignments/relation/linkset>
    <linkset>` for each linkset read;
- one named graph for each RDF document read, named by its IRI;
- one named graph for each linkset read, named by the linkset IRI, with one
  triple `<context> <relIri rel> <target>` for each link.

The names are distinct by construction (`Snapshot.names`): the
table-of-contents name first, then the document IRIs, then the linkset IRIs,
in order. An item whose IRI is already a name is left out (the first wins).
`lwsDatasetView` lists each such item in `skipped`, with the reason that its
IRI is already the name of another graph.

A non-RDF resource (for example a PNG) has no document graph. It is in the
table-of-contents graph (from its listing) and it has a linkset graph when
its linkset was read.

### Relation IRIs (`relIri`)

| Relation type in the linkset | IRI in the view | Source |
|---|---|---|
| an absolute IRI (an extension relation type, RFC 8288 §2.1.2), for example `https://www.w3.org/ns/lws#storage` | the IRI as it is | RFC 8288 §2.1.2 |
| `items` | `https://www.w3.org/ns/lws#items` | the LWS vocabulary |
| `type` | `http://www.w3.org/1999/02/22-rdf-syntax-ns#type` | the `application/lws+json` context maps `type` to `@type` |
| any other registered name, lower-cased (RFC 8288 §2.1.1), for example `up`, `describedby`, `linkset` | `http://www.iana.org/assignments/relation/` + the name | RFC 8288 Appendix A.2 |
| a name that is neither (no colon, not `reg-rel-type` of RFC 8288 §3.3) | none: the link is left out, with a reason in `skipped` | |

RFC 8288 §2.1.1 says that to convert a registered relation type to a URI
for comparison with extension relation types is "NOT RECOMMENDED". The view
is a serialisation of the links in RDF, and `relIri` states the mapping it
uses (its doc comment cites both sections).

### Choices that are Claude-inferred (not owner decisions)

- `lws:items` replaces `ldp:contains`. This follows from "LWS vocab where
  defined": the LWS vocabulary defines `items`.
- The table-of-contents graph also holds the listing members (`rdf:type`,
  `dcterms:format`, `schema:size`, `dcterms:modified`), the RDF that the
  Turtle form of a listing gives.
- A linkset graph is named by the linkset IRI.
- The IANA base `http://www.iana.org/assignments/relation/` for the
  registered names that the LWS vocabulary does not define.
- `type` maps to `rdf:type`.
- First-wins naming, with each left-out item in `skipped`.
- The storage link is the first link with relation `lws#storage` whose
  context is the storage root, in the first linkset read of the root.
- `size` gives a triple only when the listing value is a JSON number of
  decimal digits.
- A relation type that is neither an absolute IRI nor a registered name,
  and a target object with no `href`, are left out with a reason.
- The plan of a listing (`lwsViewPlan`) names the linksets to read: the
  listed container, then every member that is not a container. A container
  gets its linkset when it is listed. When the host gives no container IRI,
  the plan uses the `id` of the listing document, when it has one.
- The storage root has no `rdf:type` triple in the table-of-contents graph,
  because it is not a listing member. Its type is in its linkset graph (the
  `type` link).
- The table-of-contents link `<resource> iana:linkset <linkset>` stays when
  the linkset graph is left out because of a name clash.
- The N-Quads of `lwsDatasetView` are those of the certified view
  (`Dataset.certify`), so each graph is a set.
- The assumption `lwsReadsAtSnapshot` now covers the linkset reads, the
  listing members and the storage description IRI too (`StorageAt` has
  `storage`, `entries` and `linksetOf`).

### Proved

In `DatasetView.lean`:

- `view_names_nodup`: the graph names are distinct.
- `view_names`, `view_mem_names` (with `mem_names`): the names are the
  storage description IRI, the document IRIs and the linkset IRIs, each
  once, in that order.
- `view_toc_first`: the first named graph is named `s.storage` and its graph
  is the table-of-contents graph `s.toc`. `view_lookup_toc` states it for
  `lookupNamed`.
- `view_replace`, `view_replace_lookup`: a change of one document's
  representation (`Snapshot.replace`) keeps the default graph and the names,
  and changes the graph named by that IRI only, when that graph is the
  document's graph. The table-of-contents graph (`replace_toc`) and the
  linkset graphs do not change.
- `view_lookup`, `view_lookup_linkset`: the graph named by a document IRI is
  the graph of its first read; the graph named by a linkset IRI that is no
  other name is the graph of its first linkset read.

In `DatasetViewRead.lean`: `snapshotOfDocs_reads` (each read of the
snapshot is the read of a document), `snapshotOfDocs_linksets` (the same for
linkset reads), `snapshotOfDocs_storage` (the name of the table-of-contents
graph is the target of the storage link in the snapshot's linkset reads),
`snapshotOfDocs_storage_missing` (without it, the error).

`#print axioms` of each: `propext`, `Classical.choice`, `Quot.sound` or
fewer.

### Tests

- `formal/lean4/L4Factoidal/LWS/DatasetViewTests.lean` (`#guard`s, through
  the shipped evaluator over `lwsSource`): a storage root with one container,
  two Turtle resources, one PNG and one resource that answers 404, with
  linkset documents in the shape of `Binding.lean` `linksetJson`.
- `formal/lean4/Wasm/Ops/LwsDataset.lean` (`#guard`s of the op envelopes)
  and `formal/lean4/Wasm/native-smoke.sh` (the op envelopes through the
  native CLI).
- `npm/factoidal/test/lws-dataset-1011.test.mjs`: this package's LWS server,
  crawled through the client. It is skipped when the loaded wasm does not
  carry version 2 of `lwsViewPlan`.

## Version 1 (2026-10-25, replaced)

The rest of this section is the first definition, kept as the record.

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
only. Version 2 replaces this decision: the owner's answer "Into the TOC
graph" puts the containment in the table-of-contents graph, whose name is the
storage description IRI.

## The source and its assumption

`formal/lean4/L4Factoidal/Dataflow/LwsSource.lean`: `lwsSource st s` is a
`Sourced` whose den is `view (st.at s)`, the view of the storage `st` at the
snapshot instant over the resources of `s`. The record that the evaluator
runs is built from the reads. They agree under one named assumption,
`lwsReadsAtSnapshot` (`ReadsAtSnapshot`): each GET returned the
representation (or, for a linkset read, the linkset) its ETag identifies at
the snapshot instant, and the listings (containment and listing members) and
the storage description IRI were those of the storage at that instant.
`lwsSource_query_sound` is
`Sourced.query_sound` for this source. Ratchet line:
`foundation/assumptions.txt`, `name:lwsReadsAtSnapshot`.

## Where the decisions are

| Decision | Where |
|---|---|
| which listing members are containers, which are read, which are left out (media type with no RDF reader), whose linksets are read | `LWS/DatasetViewRead.lean`, `planListing` |
| the listing members of the table-of-contents graph (kind, format, size, modified) | `entriesOfListing` |
| ETag, Last-Modified, media type, parse, blank-node scope of each read | `readOfDone` |
| the links of each linkset read (anchor, relation, href, resolution against the linkset IRI) | `linksetOfDone`; relation IRIs `LWS/DatasetView.lean`, `relIri` |
| the storage description IRI | `storageOf?` |
| the view, the names, the evidence, the items left out | `view`, `Snapshot.names`, `viewOfDocsJson`, `nameClashes`; wasm ops `lwsViewPlan`, `lwsDatasetView` |
| the HTTP requests | the LWS client (`LWS/Client/Machine.lean`) |
| the loop | `npm/factoidal/lws/dataset.mjs` (in `tools/host-purity-lint.sh`, group 1) |

## Limits of this version

- Full crawl on every open: one `list` per container, one GET per RDF
  resource, and one HEAD and one GET per resource for its linkset. No
  search index (`lws10-searchindex`), no caching, no conditional requests.
- Metadata resources other than linksets are not crawled (a listing does
  not enumerate them).
- The crawl is a sequence of GETs. A write during the crawl can give a
  dataset that the storage never held at one instant; the assumption above
  is then false. A check is to send HEAD for each resource after the crawl
  and compare the ETags. Not done.
- The evidence lists every document and linkset read, not only the reads
  that contributed to an answer.
- A TriG or N-Quads resource gives its default graph only.
- Tested against this repository's server only (KR5 needs a second server).

## Questions for the LWS Working Group

1. Should LWS define an RDF dataset view of a storage, or of a container?
2. If yes: is containment part of the view, and with which predicate (LWS
   has its own listing format, `items`)? In the default graph or in a named
   graph with a defined name?
3. Are metadata resources graphs of the view, and how is a metadata
   resource linked to the resource it describes? Version 2 answers this for
   linksets: each linkset is a graph named by its linkset IRI, and the
   table-of-contents graph links each resource to it with the IANA
   `linkset` relation. Is a linkset the right unit, and is there an LWS
   term for that link? Does the WG prefer the IANA relation IRIs, or an LWS
   term for each relation the LWS draft uses (`up`, `type`, `linkset`)?
4. Can a server give a consistent snapshot (one ETag for the whole storage
   or container, or a snapshot token), so a client need not assume one?
