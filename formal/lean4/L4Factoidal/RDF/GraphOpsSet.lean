/-
L4Factoidal.RDF.GraphOpsSet — the graph operations keep a set a set.

RDF 1.1 Concepts §3: an RDF graph is a set of triples. The condition is
`Graph.KeyNodup` (`RDF/DatasetSet.lean`). Each theorem below is about one
producer of a graph that a public operation (a wasm op, a command-line verb,
the SBM11 query path) gives to a serialiser, a count or a store. It says
"input is a set → output is a set", or "output is a set" when the producer
builds its result with `Graph.add` from the empty graph.

Every proof is an instance of one lemma, `Graph.KeyNodup.graphAddAll`
(`RDF/GraphSet.lean`): the left fold of `Graph.add` keeps a set a set.
`Graph.union`, the CONSTRUCT collection step, the FROM merge and the closure
round `RDFS.addAll` are that fold. A producer that only drops triples
(`Graph.cbd`, a filter of the active graph) keeps the set because a sublist of
a set is a set (`Graph.KeyNodup.filter`).

| Producer | Theorem |
|---|---|
| `Graph.add`, `Graph.remove`, `Graph.union` | `Graph.KeyNodup.add`, `.remove`, `.union` (DatasetSet, CertifiedDataset) |
| CONSTRUCT, `SPARQL.evalConstruct` | `evalConstruct_keyNodup` (no hypothesis) |
| FROM merge, `SPARQL.fromMerge` | `fromMerge_keyNodup` (no hypothesis) |
| active graph, `SPARQL.applyDataset` | `applyDataset_keyNodup` |
| CBD, `Graph.cbd` | `Graph.cbd_keyNodup` |
| DESCRIBE, `SPARQL.evalDescribe` | `evalDescribe_keyNodup` |
| ρdf closure, `RDFS.closure`, `RDFS.closureFix` | `RDFS.closure_keyNodup`, `RDFS.closureFix_keyNodup` |
| RDFS closure, `RDFS.fullClosure`; RDF closure `RDFS.rdfClosure` | `RDFS.fullClosure_keyNodup`, `RDFS.rdfClosure_keyNodup` |
| RDFS-Plus closure, `RDFS.rdfsPlusClosureFix` | `RDFS.rdfsPlusClosureFix_keyNodup` |

The OWL 2 RL closure (`OWL.RL.closureFix`) is not in this table: its add step
`OWL.RL.addOne` compares triples structurally, so `"x"@en` and `"x"@EN` in one
position are two list entries. The ops that serialise it end with
`Graph.toSet` (`Wasm/Ops/Reason.lean`, `owlRlClosureSet`). Update application
is `applyUpdateIn_isSet` (`RDF/CertifiedDataset.lean`); the parse layer is
`Dataset.toSet_isSet` and `parseNQuadsFast_isSet` (`RDF/DatasetSet.lean`).

Tracking: https://github.com/danbri/factoidal/issues/973.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.GraphSet
import L4Factoidal.RDF.ConciseBoundedDescription
import L4Factoidal.RDFS.FullClosure
import L4Factoidal.RDFS.RDFSPlus
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.RDF

/-- A sublist of a set is a set. -/
theorem Graph.KeyNodup.filter {g : Graph} (f : Triple → Bool) (h : g.KeyNodup) :
    Graph.KeyNodup (g.filter f) := by
  unfold Graph.KeyNodup at *
  exact List.Nodup.sublist (List.Sublist.map _ List.filter_sublist) h

/-- The concise bounded description of a set is a set (it is a filter of the
graph, `Graph.cbd`). -/
theorem Graph.cbd_keyNodup {g : Graph} (roots : List Subject) (h : g.KeyNodup) :
    (g.cbd roots).KeyNodup := by
  unfold Graph.cbd
  exact h.filter _

/-- A left fold of `Graph.union` from a set is a set. -/
theorem foldl_union_keyNodup :
    ∀ (gs : List Graph) {acc : Graph}, acc.KeyNodup → (gs.foldl Graph.union acc).KeyNodup
  | [], _, h => h
  | g :: gs, acc, h => by
      refine foldl_union_keyNodup gs ?_
      rw [Graph.union_eq_graphAddAll]
      exact Graph.KeyNodup.graphAddAll g h

end L4Factoidal.RDF

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-- SPARQL 1.1 Query §16.2: the CONSTRUCT result is a set, for every
dataset and query (the template instances are collected with `Graph.add`
from the empty graph). -/
theorem evalConstruct_keyNodup (env : EvalEnv) (ds : Dataset) (q : Query) :
    (evalConstruct env ds q).KeyNodup := by
  unfold evalConstruct
  split
  simp only
  split
  · rw [foldl_add_eq_graphAddAll]
    exact Graph.KeyNodup.graphAddAll _ Graph.keyNodup_nil
  · exact Graph.keyNodup_nil

/-- §13.2.1: the RDF merge of the FROM graphs is a set, for every list of
graphs. -/
theorem fromMerge_keyNodup (gs : List Graph) : (fromMerge gs).KeyNodup := by
  unfold fromMerge
  exact foldl_union_keyNodup _ Graph.keyNodup_nil

/-- The active graph after the dataset clauses: a set when the active graph
given is one. -/
theorem applyDataset_keyNodup (dcs : List DatasetClause) (ds : Dataset) {active : Graph}
    (h : active.KeyNodup) : (applyDataset dcs ds active).2.KeyNodup := by
  unfold applyDataset
  split
  · exact h
  · exact fromMerge_keyNodup _

/-- SPARQL 1.1 Query §16.4: the DESCRIBE result over a dataset whose default
graph is a set is a set. -/
theorem evalDescribe_keyNodup (env : EvalEnv) {ds : Dataset} (q : Query)
    (h : ds.default.KeyNodup) : (evalDescribe env ds q).KeyNodup := by
  unfold evalDescribe
  have ha := applyDataset_keyNodup q.dataset ds h
  revert ha
  generalize applyDataset q.dataset ds ds.default = p
  obtain ⟨ds', active⟩ := p
  intro ha
  simp only
  split
  · exact Graph.cbd_keyNodup _ ha
  · exact Graph.keyNodup_nil

theorem evalDescribe_keyNodup_of_isSet (env : EvalEnv) {ds : Dataset} (q : Query)
    (h : ds.IsSet) : (evalDescribe env ds q).KeyNodup :=
  evalDescribe_keyNodup env q h.default

end L4Factoidal.SPARQL

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

theorem addAll_keyNodup (ts : List Triple) {g : Graph} (h : g.KeyNodup) :
    (addAll g ts).KeyNodup := by
  rw [addAll_eq_graphAddAll]
  exact Graph.KeyNodup.graphAddAll ts h

/-- One ρdf round keeps a set a set. -/
theorem step_keyNodup {g : Graph} (h : g.KeyNodup) : (step g).KeyNodup :=
  addAll_keyNodup _ h

/-- The ρdf closure of a set is a set, for every fuel. -/
theorem closure_keyNodup : ∀ (n : Nat) {g : Graph}, g.KeyNodup → (closure g n).KeyNodup
  | 0, _, h => h
  | n + 1, g, h => by
      simp only [closure]
      split
      · exact h
      · exact closure_keyNodup n (step_keyNodup h)

theorem closureFix_keyNodup {g : Graph} (h : g.KeyNodup) : (closureFix g).KeyNodup :=
  closure_keyNodup _ h

theorem fullStep_keyNodup {g : Graph} (h : g.KeyNodup) : (fullStep g).KeyNodup :=
  addAll_keyNodup _ h

theorem fullClosureLoop_keyNodup :
    ∀ (n : Nat) {g : Graph}, g.KeyNodup → (fullClosureLoop g n).KeyNodup
  | 0, _, h => h
  | n + 1, g, h => by
      simp only [fullClosureLoop]
      split
      · exact h
      · exact fullClosureLoop_keyNodup n (fullStep_keyNodup h)

/-- RDF 1.1 Semantics §9.2.1: the RDFS closure (axioms seeded, then the rule
rounds) of a set is a set. -/
theorem fullClosure_keyNodup (D cmps : List WfIri) {g : Graph} (h : g.KeyNodup) :
    (fullClosure D cmps g).KeyNodup := by
  unfold fullClosure
  exact fullClosureLoop_keyNodup _ (addAll_keyNodup _ h)

/-- RDF 1.1 Semantics §8.1: the RDF closure of a set is a set. -/
theorem rdfClosure_keyNodup (cmps : List WfIri) {g : Graph} (h : g.KeyNodup) :
    (rdfClosure cmps g).KeyNodup := by
  unfold rdfClosure
  exact addAll_keyNodup _ (addAll_keyNodup _ h)

theorem rdfsPlusStep_keyNodup {g : Graph} (h : g.KeyNodup) : (rdfsPlusStep g).KeyNodup :=
  addAll_keyNodup _ (step_keyNodup h)

theorem rdfsPlusClosure_keyNodup :
    ∀ (n : Nat) {g : Graph}, g.KeyNodup → (rdfsPlusClosure g n).KeyNodup
  | 0, _, h => h
  | n + 1, g, h => by
      simp only [rdfsPlusClosure]
      split
      · exact h
      · exact rdfsPlusClosure_keyNodup n (rdfsPlusStep_keyNodup h)

/-- The RDFS-Plus closure of a set is a set. -/
theorem rdfsPlusClosureFix_keyNodup {g : Graph} (h : g.KeyNodup) :
    (rdfsPlusClosureFix g).KeyNodup :=
  rdfsPlusClosure_keyNodup _ h

end L4Factoidal.RDFS

namespace L4Factoidal.RDF

#print axioms SPARQL.evalConstruct_keyNodup
#print axioms SPARQL.evalDescribe_keyNodup
#print axioms SPARQL.fromMerge_keyNodup
#print axioms RDFS.closureFix_keyNodup
#print axioms RDFS.fullClosure_keyNodup
#print axioms RDFS.rdfClosure_keyNodup
#print axioms RDFS.rdfsPlusClosureFix_keyNodup

end L4Factoidal.RDF
