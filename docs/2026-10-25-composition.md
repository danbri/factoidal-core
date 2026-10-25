# Composition: sources, `query_sound`, and the guarantee of a path

Issue: https://github.com/danbri/factoidal/issues/975 (owner-approved plan, 2026-10-25, step 1 and step 2).

## The query theorem

`Dataflow.query_sound` (`formal/lean4/L4Factoidal/Dataflow/Compose.lean`):
for any `LawfulDataset` `S`, any set dataset `ds` with `ds.den = S.den`, and
any parsed query, the evaluator run on `queryInput env S ds q` satisfies
`EvalContract`. The input has `S`'s backend and a set dataset with den
`S.den`.

Premises: the evaluator's named assumption (`ev.AssumptionHolds`) and the
record's named assumptions (`Assumed S.assumed_contracts`). `ds` names the
value that the reference evaluator reads. The theorem does not depend on
where `S` came from.

`pipeline_sound` (`Dataflow/EndToEnd.lean`) has the same statement as
before. Its proof is now `readerSource_spec` + `query_sound`.

## Sources

A source gives a `Sourced`: a `LawfulDataset` and a set dataset with the
same den. Each source theorem states the den and the named assumptions.

| Source | Lean | den | Named assumptions | Status |
|---|---|---|---|---|
| (a) reader | `readerSource`, `readerSource_spec` | `raw.den` of the parse | none | ✅ proved |
| (b) API dataset handle after `add` / `delete` | `handleSource`, `handleSource_spec`, `Sourced.handle_den` | each operation's effect on the den, in order (`DatasetDen.insertQuads`, `deleteQuads`) | none | ✅ proved |
| (c) SPARQL 1.1 Update | `updateSource`, `updateSource_spec` | den of the `applyUpdateIn` result; `OpsDen` from the input den (each operation's section 3 effect) | none | ✅ proved |
| (d) reasoner output | `reasonerSource`, `reasonerSource_spec`, `Sourced.reason` | default graph = `r.run g`, no named graph, `r.regime.Entails g (r.run g)` | none | ✅ proved |
| (e) union of records, shards | `Sourced.union`, `Sourced.unionAll`, `unionBackend_exact` | `DatasetDen.union` of the dens | the members' | ✅ proved |
| (f) any `LawfulStore` as the default graph (HDT, COTTAS, RML, overlays) | `Sourced.ofStore`, `Sourced.ofStore_spec` | `defaultDen st.graph` | the store's (`backendReadOpsExact`, `cottasReadOpsExact`, `rmlPushdownInvisible`, `rmlVirtualIsMaterialised`) | ✅ proved under the store's assumptions |
| (g) an LWS storage snapshot (https://github.com/danbri/factoidal/issues/1011) | `lwsSource`, `lwsSource_spec`, `lwsSource_query_sound` (`Dataflow/LwsSource.lean`) | `view (st.at s)`: the dataset view (`LWS/DatasetView.lean`) of the storage at the snapshot instant, over the resources read | `lwsReadsAtSnapshot` | ✅ proved under the assumption |

Limits:

* (c): the quad lists of operations with a WHERE clause come from the
  engine's `evalWhere`. `OpsDen` takes them as inputs; `evalWhere` is not
  proved against SPARQL 1.1 Query section 18 (`SPARQL/UpdateDenotation.lean`,
  "The boundary").
* (f): a disk store has one graph. A COTTAS or HDT store with named graphs
  needs a `LawfulDataset` constructor that is built from per-graph stores.
  The missing lemma is `DatasetBackendExact` for that record.
* The answer is not proved to depend only on the den. The reference value
  is `alignNamed S.backend ds`. This value has the backend's graph order.

## The guarantee of a composed path

A path is a chain of sources that ends in a query. Its guarantee is computed
from the parts. It is not written for each path.

1. The den is the composition of the source theorems. Example: an update of
   a union of two read documents has den = `OpsDen` applied to
   `raw1.den ∪ raw2.den`.
2. The named assumptions are the union of the `Sourced.assumptions` of each
   step (`Sourced.union_spec`, `Sourced.unionAll_spec`), plus
   `ev.AssumptionHolds`.
3. `Sourced.query_sound` gives `EvalContract` over that den, under those
   assumptions.

A step that is not a source in this table has no den theorem. A path that
contains such a step has no guarantee from this composition.

## Tests

`Dataflow/SourcesTests.lean`, 41 `#guard`s. For each source (b) to (f), the
backend path answers, and its answer equals `referenceAnswer` over the
record's reference dataset (SELECT rows up to order). One guard pins the
known SELECT `*` header gap on an empty result: the backend header is `[]`
and the reference header is `[s, p, o]` (`Dataflow/Evaluator.lean`, "Not
claimed").
