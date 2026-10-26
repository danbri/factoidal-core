/-
Capability-aware planner, KR 2.2: build-time checks of the structural
planner (https://github.com/danbri/factoidal/issues/801), over the mock
catalog of `Planner/Tests.lean`. The full test set, with its
expected-failure bucket, is the executable `l4planner-test`
(`Harness/PlannerTest.lean`); `#guard` cannot express an expected
failure.
-/
import L4Factoidal.Planner.Search
import L4Factoidal.Planner.FromQuery
import L4Factoidal.Planner.Tests

namespace L4Factoidal.Planner.SearchTests

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner L4Factoidal.Planner.Tests

def names (cat : Catalog) (r : Ranked) : List String :=
  r.rewriting.steps.map (fun a => (cat[a.src]?.map (·.cap.name)).getD "?")

-- The dependent join: scan `knows`, then look up the name of each ?y.
#guard ((search cat reqNames 2).head?.map (names cat)) == some ["knows-sparql", "people-rest"]
#guard (search cat reqNames 2).all (fun r => r.rewriting.check cat reqNames)
#guard (search cat reqNames 2).all (fun r => sameAnswers reqNames (r.rewriting.toPlan reqNames))
-- With one access the lookup input is never bound.
#guard (plan cat reqNames 1).isAnswerable == false
-- The approximate source: the plan is marked.
#guard ((search cat reqAge 2).head?.map (·.approx)) == some true
-- `age` needs its subject, and no access binds ?x: not answerable.
#guard (plan cat { bgp := [{ s := .var "x", p := .iri pAge, o := .var "y" }],
                   projection := ["x"] } 3).isAnswerable == false
-- A requirement with no source for its predicate.
#guard (plan cat { bgp := [{ s := .var "x", p := .iri ⟨"http://example.org/other", rfl⟩,
                             o := .var "y" }], projection := ["x"] } 3).isAnswerable == false

/-! ## Axiom audit -/

#print axioms search_check
#print axioms search_isRewriting
#print axioms search_sound
#print axioms search_complete
#print axioms search_mem_of_minimal
#print axioms plan_notAnswerable_sound
#print axioms args_mem_pool_of_exactCover
#print axioms mem_dfs_of_minimal

end L4Factoidal.Planner.SearchTests
