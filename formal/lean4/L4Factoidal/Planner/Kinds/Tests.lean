/-
Capability-aware planner, KR 2.3: build-time checks of the source-kind
description readers (https://github.com/danbri/factoidal/issues/801) and
the axiom audit of the theorems in `Kinds/Common.lean`. The full test set
(with the SBM11 generation, the mock services and the expected-failure
cases) is `lake exe l4planner-test` (`Harness/PlannerKinds.lean`).
-/
import L4Factoidal.Planner.Kinds.Sbm11
import L4Factoidal.Planner.Kinds.Memory
import L4Factoidal.Planner.Kinds.Sparql
import L4Factoidal.Planner.Kinds.FacadeX
import L4Factoidal.Planner.Kinds.Rest
import L4Factoidal.Planner.Kinds.Mcp

namespace L4Factoidal.Planner.Kinds.Tests

open L4Factoidal.RDF L4Factoidal.Planner L4Factoidal.Planner.Kinds

def kn : WfIri := ⟨"http://example.org/knows", rfl⟩
def a : Subject := .iri ⟨"http://example.org/a", rfl⟩
def b : Term := .iri ⟨"http://example.org/b", rfl⟩

-- The permutations PSO, POS, SPO, OSP give all eight input sets.
#guard (Sbm11.permShapes ["pso", "pos", "spo", "osp"]).length == 8
#guard ((Sbm11.permShapes ["pso", "pos", "spo", "osp"]).map (·.inputs)).all
  (fun s => Memory.subsets3.contains s)
-- One permutation gives its four prefixes only.
#guard (Sbm11.permShapes ["spo"]).map (·.inputs) == [[], [0], [0, 1], [0, 1, 2]]

-- In-memory: 8 triple-form shapes and 4 per predicate.
#guard (match Memory.describe [{ s := a, p := kn, o := b }] with
  | .ok ds => ds.length == 12
  | .error _ => false)

-- Façade-X: the CSV triples (root type, 2 members, 4 cells).
#guard (match FacadeX.readOptions "x-sparql-anything:location=file:///p.csv,csv.headers=true" with
  | .ok o => (match FacadeX.triplesOf o "a,b\n1,2\n3,4\n" with
    | .ok g => g.length == 7
    | .error _ => false)
  | .error _ => false)
-- A relative location without `root` is refused.
#guard (FacadeX.readOptions "x-sparql-anything:location=p.csv").toBool == false

-- A subject template reads its slot back.
#guard (match JsonTerms.SubjectTemplate.read? "http://example.org/{id}" "id" with
  | some t => t.slotValue? ⟨"http://example.org/bob", rfl⟩ == some "bob" &&
      t.slotValue? ⟨"http://example.org/a/b", rfl⟩ == none &&
      t.slotValue? ⟨"http://other.org/bob", rfl⟩ == none
  | none => false)

-- JSON numbers: integer, decimal, double.
#guard (JsonTerms.numberTerm? "12").isSome && (JsonTerms.numberTerm? "1.5").isSome &&
  (JsonTerms.numberTerm? "1e3").isSome

/-! ## Axiom audit -/

#print axioms lookupImpl_sound
#print axioms lookupImpl_complete
#print axioms graphSource_triples
#print axioms graphSource_sound
#print axioms graphSource_complete

end L4Factoidal.Planner.Kinds.Tests
