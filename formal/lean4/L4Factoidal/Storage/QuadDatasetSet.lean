/-
L4Factoidal.Storage.QuadDatasetSet — the dataset a quad sequence denotes is a
set of quads.

`Storage.QuadDataset.datasetOfQuads` is the decode of a generation's quad rows
into a `Dataset`: the IBK4 and IBK5 readers, the WASM store operations and the
SBM11 reference path (`Harness/Sbm11Query.lean`, `selectedDataset`) all build
their dataset with it. A generation can hold one quad in more than one row
(the packer publishes blocks before it has seen the whole graph), so the set
is made here.

`datasetOfQuads_isSet`: for every list of rows, the result is a set
(`Dataset.IsSet`, RDF 1.1 Concepts §3 and §4): no two triples of one graph are
`Triple.eqb`-equal, and no graph name occurs two times. No hypothesis on the
rows.

The proof is the invariant `BucketsOk` of the accumulator, kept by every row
(`addQuadRow_ok`): each graph is a `FastGraph` whose index is exact
(`FastGraph.Inv`) and whose list is a set (instance of `Graph.KeyNodup.add`
through `FastGraph.add_toGraph`), and the name list has no repeat and holds
only names the map has.

Tracking: https://github.com/danbri/factoidal/issues/973.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.QuadDataset
import L4Factoidal.RDF.DatasetSet

namespace L4Factoidal.Storage.QuadDataset

open L4Factoidal.RDF

/-- A graph under construction whose index is exact and whose list is a set. -/
def GraphOk (g : FastGraph) : Prop := g.Inv ∧ g.toGraph.KeyNodup

theorem graphOk_empty : GraphOk {} := ⟨FastGraph.inv_empty, Graph.keyNodup_nil⟩

theorem GraphOk.add {g : FastGraph} (t : Triple) (h : GraphOk g) : GraphOk (g.add t) := by
  refine ⟨FastGraph.add_inv h.1, ?_⟩
  rw [FastGraph.add_toGraph t h.1]
  exact h.2.add t

/-- The invariant of the accumulator. -/
structure BucketsOk (b : GraphBuckets) : Prop where
  default : GraphOk b.defaultGraph
  named : ∀ n, GraphOk (b.named.getD n {})
  order : b.orderRev.Nodup
  known : ∀ n ∈ b.orderRev, b.named.contains n = true

theorem bucketsOk_empty : BucketsOk {} where
  default := graphOk_empty
  named := fun n => by simp only [Std.HashMap.getD_empty]; exact graphOk_empty
  order := List.nodup_nil
  known := fun _ h => by cases h

theorem addQuadRow_ok {b : GraphBuckets} (q : IndexedBlockWireV4.QuadRow) (h : BucketsOk b) :
    BucketsOk (addQuadRow b q) := by
  unfold addQuadRow
  split
  · exact { h with default := h.default.add _ }
  · next name _ =>
    split
    · refine { h with named := ?_, known := ?_ }
      · intro n
        rw [Std.HashMap.getD_modify]
        split
        · next he =>
          have hk : name = n := beq_iff_eq.mp he
          subst hk
          have hn := h.named name
          rw [Std.HashMap.getD_eq_getD_getElem?] at hn
          cases hv : b.named[name]? with
          | none => exact graphOk_empty
          | some v =>
            rw [hv] at hn
            exact hn.add _
        · exact h.named n
      · intro n hn
        rw [Std.HashMap.contains_modify]
        exact h.known n hn
    · next hc =>
      refine { default := h.default, named := ?_, order := ?_, known := ?_ }
      · intro n
        show GraphOk ((b.named.insert name (FastGraph.add _ {})).getD n {})
        rw [Std.HashMap.getD_insert]
        split
        · exact graphOk_empty.add _
        · exact h.named n
      · refine List.nodup_cons.mpr ⟨?_, h.order⟩
        intro hm
        exact hc (h.known name hm)
      · intro n hn
        show (b.named.insert name (FastGraph.add _ {})).contains n = true
        rw [Std.HashMap.contains_insert]
        rcases List.mem_cons.mp hn with e | hn
        · subst e; simp
        · simp [h.known n hn]

theorem foldl_addQuadRow_ok :
    ∀ (qs : List IndexedBlockWireV4.QuadRow) {b : GraphBuckets}, BucketsOk b →
      BucketsOk (qs.foldl addQuadRow b)
  | [], _, h => h
  | q :: qs, _, h => foldl_addQuadRow_ok qs (addQuadRow_ok q h)

/-- The decode of a quad sequence is a set of quads, for every sequence. -/
theorem datasetOfQuads_isSet (quads : List IndexedBlockWireV4.QuadRow) :
    (datasetOfQuads quads).IsSet := by
  have h := foldl_addQuadRow_ok quads bucketsOk_empty
  unfold datasetOfQuads
  refine ⟨h.default.2, ?_, ?_⟩
  · simp only [Dataset.names, List.map_map]
    have : ((fun ng : NamedGraph => ng.name) ∘ fun name =>
        ({ name, graph := ((quads.foldl addQuadRow {}).named.getD name {}).toGraph } :
          NamedGraph)) = id := rfl
    rw [this, List.map_id]
    exact List.pairwise_reverse.mpr (h.order.imp fun hne e => hne e.symm)
  · intro ng hng
    obtain ⟨n, _, rfl⟩ := List.mem_map.mp hng
    exact (h.named n).2

-- Observable cardinality: a quad in two rows is one quad; one triple in two
-- graphs is two quads; a name in two rows is one named graph.
private def tq : Triple := ⟨.iri ⟨"urn:s", by decide⟩, ⟨"urn:p", by decide⟩, .literal (Literal.string "x")⟩
private def tqEN : Triple := ⟨.iri ⟨"urn:s", by decide⟩, ⟨"urn:p", by decide⟩, .literal (Literal.langString "x" "EN")⟩
private def tqEn : Triple := ⟨.iri ⟨"urn:s", by decide⟩, ⟨"urn:p", by decide⟩, .literal (Literal.langString "x" "en")⟩
private def gq : Subject := .iri ⟨"urn:g", by decide⟩
#guard (datasetOfQuads [(none, tq), (none, tq), (some gq, tq), (some gq, tq)]).default.length == 1
#guard (datasetOfQuads [(none, tq), (none, tq), (some gq, tq), (some gq, tq)]).named.map
  (·.graph.length) == [1]
#guard (datasetOfQuads [(none, tqEN), (none, tqEn)]).default.length == 1

#print axioms datasetOfQuads_isSet

end L4Factoidal.Storage.QuadDataset
