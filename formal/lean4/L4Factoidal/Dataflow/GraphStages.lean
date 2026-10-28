/-
L4Factoidal.Dataflow.GraphStages — stages with more than one input port, for
graph pipelines (`Dataflow/Graph.lean`,
https://github.com/danbri/factoidal/issues/1130).

`datasetMerge a c`: the RDF merge of two datasets (RDF 1.1 Semantics section
5.2, extended to datasets as `DatasetDen.IsMerge`): each input gets its own
blank-node scope (`scopeDocument 1`, `scopeDocument 2`), then the default
graphs and the named-graph lists are appended (`Dataset.combine`). Theorem
`datasetMerge_isMerge`: the result denotes a merge of the two inputs, so a
blank node of one input is never the blank node of the other, whatever labels
the documents used.

`datasetMergeStage`: the stage with two ports, `left` and `right`, as a
`PortComponent` over any wire system whose `dataset` carrier is
`RDF.Dataset` (`MergeWires`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Graph
import L4Factoidal.RDF.DocumentScope

set_option linter.unusedSectionVars false

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF

/-- The RDF merge of two datasets (module comment). -/
def datasetMerge (a c : Dataset) : Dataset :=
  (a.scopeDocument 1).combine (c.scopeDocument 2)

/-- **`datasetMerge` denotes a merge** of its two inputs. -/
theorem datasetMerge_isMerge (a c : Dataset) :
    DatasetDen.IsMerge a.den c.den (datasetMerge a c).den :=
  scopeDocument_combine_isMerge (by decide) a c

/-- A wire system with a wire whose carrier is `RDF.Dataset`. -/
structure MergeWires {W : Type} (S : WireSystem W) where
  dataset : W
  carrier_eq : S.Carrier dataset = Dataset

section

variable {W N : Type} [DecidableEq W] [DecidableEq N]
variable {S : WireSystem W} {A : N → Prop}

/-- The merge stage: ports `left` and `right`, both on the dataset wire;
output on the dataset wire; contract: the output denotes a merge of the two
inputs. No named assumption. -/
def datasetMergeStage (M : MergeWires S) (contractName : Option N) : PortComponent S A where
  sig := { name := "datasetMerge", ins := [("left", M.dataset), ("right", M.dataset)],
           outW := M.dataset, contract := contractName, assumptions := [] }
  run := fun
    | .cons a (.cons c .nil) =>
      .ok (cast M.carrier_eq.symm (datasetMerge (cast M.carrier_eq a) (cast M.carrier_eq c)))
  contract := fun
    | .cons a (.cons c .nil), y =>
      DatasetDen.IsMerge (cast M.carrier_eq a).den (cast M.carrier_eq c).den (cast M.carrier_eq y).den
  sound _ := fun
    | .cons a (.cons c .nil), y, h => by
      simp only [Except.ok.injEq] at h
      subst h
      simpa using datasetMerge_isMerge (cast M.carrier_eq a) (cast M.carrier_eq c)

end

#print axioms datasetMerge_isMerge

end L4Factoidal.Dataflow
