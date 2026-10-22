/-
Capability-aware planner, KR 2.4: build-time checks of the execution
state machine (https://github.com/danbri/factoidal/issues/801), over the
mock catalog of `Planner/Tests.lean`. The full test set, with its
expected-failure bucket, is the executable `l4planner-test`
(`Harness/PlannerTest.lean`); `#guard` cannot express an expected
failure.
-/
import L4Factoidal.Planner.Exec
import L4Factoidal.Planner.Tests
import L4Factoidal.Planner.ExecM

namespace L4Factoidal.Planner.ExecTests

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner L4Factoidal.Planner.Tests
open L4Factoidal.Planner.Exec

def outRows (req : Requirement) (st : State) : List (List (Option Term)) :=
  canon req.projection (st.output.map Row.binding)

def refRows (c : Catalog) (req : Requirement) : List (List (Option Term)) :=
  canon req.projection (req.answers (declaredGraph c))

/-- `people` with a call quota of 1. -/
def peopleQ1 : Source := { people with cap := { people.cap with cost := { people.cap.cost with callQuota := some 1 } } }

def catQ1 : Catalog := [peopleQ1, knows, age]

-- The run of the family ends `done`, and its output is the reference
-- evaluator's answers over the declared graph.
#guard (match run cat reqNames 2 {} noFaults with
  | some st => st.status == .done && sameMultiset (outRows reqNames st) (refRows cat reqNames)
  | none => false)
-- It makes one call of `knows` and one call of `people` per `knows` row (2).
#guard (match run cat reqNames 2 {} noFaults with
  | some st => st.calls 1 == 1 && st.calls 0 == 2
  | none => false)

-- With a call quota of 1 on `people`, the plan needs 2 calls; the family
-- has no other plan, so the run stops after one call, with no output.
#guard (match run catQ1 reqNames 2 {} noFaults with
  | some st => st.status == .stopped && st.calls 0 == 1 && st.output.isEmpty
  | none => false)

-- A failed first call of `people` is retried, and the run gives the
-- reference answers (3 calls of `people`: 2 rows and 1 retry).
#guard (match run cat reqNames 2 {} (fun i n => i == 0 && n == 1) with
  | some st => st.status == .done && st.calls 0 == 3 &&
      sameMultiset (outRows reqNames st) (refRows cat reqNames)
  | none => false)

-- With no retry allowed and no alternative, the same failure stops the run.
#guard (match run cat reqNames 2 { maxRetries := 0 } (fun i n => i == 0 && n == 1) with
  | some st => st.status == .stopped && st.retries == 0
  | none => false)

-- The approximate source: every output row is marked.
#guard (match run cat reqAge 2 {} noFaults with
  | some st => st.status == .done && !st.output.isEmpty && st.output.all (·.approx)
  | none => false)

/-! ## KR 4.1: the plan run through a monad (`Planner/ExecM.lean`)

Calls in `StateM Nat` count themselves, so the run is seen to make each
call when the plan reaches it; the rows are those of `Plan.run`. -/

def countingCalls (c : Catalog) : Calls (StateM Nat) :=
  fun i inp => do
    modify (· + 1)
    pure (match c[i]? with | some s => s.sem.impl inp | none => [])

def rwGoodPlan : Plan := rwGood.toPlan reqNames

-- One call of `knows`, then one call of `people` per `knows` row (2).
#guard ((rwGoodPlan.runM cat (countingCalls cat)).run 0).2 == 3
#guard canon reqNames.projection (((rwGoodPlan.runM cat (countingCalls cat)).run 0).1.map Row.binding) ==
  canon reqNames.projection ((rwGoodPlan.run cat).map Row.binding)
-- In `Id`, `pureCalls` gives `Plan.run` (`runM_eq_run`, `pureCalls_denote`).
#guard canon reqNames.projection ((rwGoodPlan.runM (m := Id) cat (pureCalls cat)).map Row.binding) ==
  canon reqNames.projection ((rwGoodPlan.run cat).map Row.binding)

/-! ## Axiom audit -/

#print axioms flatMapRowsM_pure
#print axioms execM_eq_exec
#print axioms runM_eq_run
#print axioms runM_sound
#print axioms pureCalls_denote

#print axioms init_inv
#print axioms next_inv
#print axioms reachable_inv
#print axioms reachable_sound
#print axioms reachable_quota
#print axioms reachable_output
#print axioms reachable_unmarked_of_allExact
#print axioms next_measure_lt
#print axioms next_wf
#print axioms stepExec_next
#print axioms runFrom_reachable
#print axioms runFrom_final
#print axioms run_spec

end L4Factoidal.Planner.ExecTests
