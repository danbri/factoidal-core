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
import L4Factoidal.Planner.Kinds.WebMcp
import L4Factoidal.Planner.Kinds.Llm
import L4Factoidal.Planner.Exactness

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

-- LLM confidence in thousandths (KR 4.4).
#guard Llm.thousandths? "0.8" == some 800 && Llm.thousandths? "0.85" == some 850 &&
  Llm.thousandths? "1" == some 1000 && Llm.thousandths? "1.0" == some 1000 &&
  Llm.thousandths? "0" == some 0 && Llm.thousandths? "1.5" == none &&
  Llm.thousandths? "0.8125" == none && Llm.thousandths? "8e-1" == none

-- WebMCP: a tool that is not read-only is refused (KR 4.4).
#guard (WebMcp.describe "{\"origin\": \"https://a.example\", \"tool\": {\"name\": \"t\", \"description\": \"d\",
  \"inputSchema\": {\"required\": [\"id\"]}}, \"org.factoidal/rdf\": {\"subject\": \"id\",
  \"subjectTemplate\": \"http://example.org/{id}\", \"predicates\": {\"v\": \"http://example.org/v\"}}}").toBool == false

/-! ## Axiom audit -/

#print axioms lookupImpl_sound
#print axioms lookupImpl_complete
#print axioms graphSource_triples
#print axioms graphSource_sound
#print axioms graphSource_complete
-- KR 4.4: exactness of answers (`Planner/Exactness.lean`)
#print axioms execUsed_rows
#print axioms execUsed_approx
#print axioms runUsed_exact_iff
#print axioms run_exact_only_if
#print axioms rewriting_used
#print axioms rewriting_run_approx

end L4Factoidal.Planner.Kinds.Tests
