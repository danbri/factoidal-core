/-
L4Factoidal.SPARQL.FromMergeStage — the FROM default graph as a dataflow
stage (https://github.com/danbri/factoidal/issues/979, registry of
https://github.com/danbri/factoidal/issues/975).

`fromMergeStage`: the graphs that the FROM clauses name (in clause order,
each IRI once) to the default graph of the query, `SPARQL.fromMerge`. The
contract: the output is `fromMerge` of the input and it denotes an RDF merge
of the input graphs (`FromMerge.fromMerge_isMergeOf`; SPARQL 1.1 Query section
13.2.1, RDF 1.1 Semantics section 5.2).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.FromMerge
import L4Factoidal.Dataflow.Stage

namespace L4Factoidal.SPARQL.FromMerge

open L4Factoidal.RDF

/-- The contract of `fromMergeStage`. -/
def FromMergeContract (gs : List Graph) (out : Graph) : Prop :=
  out = fromMerge gs ∧ IsMergeOf (gs.map graphDen) (graphDen out)

/-- The FROM graphs to the default graph of the query. -/
def fromMergeStage : L4Factoidal.Dataflow.Stage String (List Graph) Graph :=
  L4Factoidal.Dataflow.Stage.ofFun fromMerge FromMergeContract
    (fun gs => ⟨rfl, fromMerge_isMergeOf gs⟩)

#print axioms fromMergeStage

end L4Factoidal.SPARQL.FromMerge
