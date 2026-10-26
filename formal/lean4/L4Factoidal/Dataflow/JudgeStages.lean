/-
L4Factoidal.Dataflow.JudgeStages — the reasoner, validator and checker
interface types as dataflow stages (https://github.com/danbri/factoidal/issues/975,
item 2).

`SoundReasoner.toStage`: the contract of the stage is the regime's entailment.
The shipped reasoners are the stages of the closures that the older stage
definitions give (`rdfsReasoner_run`, `owlRlReasoner_run`: the same closure
function).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Reasoner
import L4Factoidal.Dataflow.Stage

namespace L4Factoidal.Dataflow

open L4Factoidal.RDF

/-- The reasoner as a dataflow stage; its contract is the regime. -/
def SoundReasoner.toStage (r : SoundReasoner) : Stage String Graph Graph :=
  Stage.ofFun r.run r.regime.Entails r.sound

theorem rdfsReasoner_run (D : List WfIri) (g : Graph) :
    (rdfsReasoner D).run g = RDFS.fullClosure D (cmpSlice g) g := by
  simp only [rdfsReasoner]

theorem owlRlReasoner_run (g : Graph) :
    owlRlReasoner.run g = Graph.toSet (OWL.RL.closureFix g) := by
  simp only [owlRlReasoner]

theorem rhoDfReasoner_run (g : Graph) : rhoDfReasoner.run g = RDFS.closureFix g := by
  simp only [rhoDfReasoner]

#print axioms SoundReasoner.toStage

end L4Factoidal.Dataflow
