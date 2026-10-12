/-
Capability-aware planner, KR 2.1: executable examples.

https://github.com/danbri/factoidal/issues/801. Three mock sources:

* `people` — a REST-like lookup: arity 2 (person, name), the subject
  (position 0) is a required input. Exact.
* `knows` — a SPARQL-endpoint-like free scan: arity 2 (person, person),
  no required input. Exact.
* `age` — an LLM-like source: arity 2 (person, age), subject required,
  approximate. Its implementation returns a value that is not in its
  declared extension, so its rows must be marked.

The tests check: the well-formedness predicate and the rewriting check
accept a plan with bound inputs and reject one with an unbound input;
the executed answers of an exact rewriting equal (as a multiset of
projected rows) the reference evaluator's answers over the materialised
declared graph; rows that depend on the approximate source are marked.
-/
import L4Factoidal.Planner.Soundness

namespace L4Factoidal.Planner.Tests

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner

def iri (s : String) (h : isIri s = true) : Term := .iri ⟨s, h⟩
def lit (s : String) : Term := .literal (Literal.string s)

def alice : Term := iri "http://example.org/alice" rfl
def bob   : Term := iri "http://example.org/bob" rfl
def carol : Term := iri "http://example.org/carol" rfl
def pName  : WfIri := ⟨"http://example.org/name", rfl⟩
def pKnows : WfIri := ⟨"http://example.org/knows", rfl⟩
def pAge   : WfIri := ⟨"http://example.org/age", rfl⟩

/-- The implementation of a lookup over a finite extension: every
extension tuple that matches the input. -/
def lookupImpl (ext : List Tuple) : InputBinding → List Tuple :=
  fun inp => ext.filter (tupleMatchesInput inp)

def costRest : CostModel := { perCall := 50, perRow := 1, callQuota := some 1000 }
def costScan : CostModel := { perCall := 200, perRow := 1 }
def costLlm  : CostModel := { perCall := 2000, perRow := 0, callQuota := some 10 }

def people : Source where
  cap := { name := "people-rest", arity := 2, inputs := [0], location := "https://api.example.org",
           cost := costRest, exactness := .exact }
  mapping := { templates := [{ s := .arg 0, p := .const (.iri pName), o := .arg 1 }] }
  sem := { ext := [[alice, lit "Alice"], [bob, lit "Bob"], [carol, lit "Carol"]],
           impl := lookupImpl [[alice, lit "Alice"], [bob, lit "Bob"], [carol, lit "Carol"]] }

def knows : Source where
  cap := { name := "knows-sparql", arity := 2, inputs := [], location := "https://sparql.example.org",
           cost := costScan, exactness := .exact }
  mapping := { templates := [{ s := .arg 0, p := .const (.iri pKnows), o := .arg 1 }] }
  sem := { ext := [[alice, bob], [bob, carol]],
           impl := lookupImpl [[alice, bob], [bob, carol]] }

/-- Declared extension: carol is 41. The implementation answers 99. -/
def age : Source where
  cap := { name := "age-llm", arity := 2, inputs := [0], location := "llm",
           cost := costLlm, exactness := .approximate }
  mapping := { templates := [{ s := .arg 0, p := .const (.iri pAge), o := .arg 1 }] }
  sem := { ext := [[carol, lit "41"]],
           impl := lookupImpl [[carol, lit "99"]] }

def cat : Catalog := [people, knows, age]

/-! ## Requirement: names of the people somebody knows, without Carol -/

def notCarol : RowFilter := RowFilter.onVar "n" (fun o => o != some (lit "Carol"))

def reqNames : Requirement where
  bgp := [ { s := .var "x", p := .iri pKnows, o := .var "y" },
           { s := .var "y", p := .iri pName,  o := .var "n" } ]
  filters := [notCarol]
  projection := ["x", "n"]

/-- Scan `knows`, then look up the name of each `?y` (input bound). -/
def rwGood : Rewriting :=
  { steps := [ { src := 1, args := [.var "x", .var "y"] },
               { src := 0, args := [.var "y", .var "n"] } ] }

/-- The lookup first: its required input `?y` is not bound yet. -/
def rwBad : Rewriting :=
  { steps := [ { src := 0, args := [.var "y", .var "n"] },
               { src := 1, args := [.var "x", .var "y"] } ] }

/-- Projected rows, as lists of values in projection order. -/
def canon (vs : List VarName) (rows : List Binding) : List (List (Option Term)) :=
  rows.map (fun mu => vs.map (fun v => mu.lookup v))

def planRows (p : Plan) : List Binding := (p.run cat).map Row.binding

/-- Same multiset: equal lengths, and each row of `a` occurs as often in
`b` as in `a`. -/
def sameMultiset (a b : List (List (Option Term))) : Bool :=
  a.length == b.length && a.all (fun x => a.count x == b.count x)

def sameAnswers (req : Requirement) (p : Plan) : Bool :=
  sameMultiset (canon req.projection (planRows p))
    (canon req.projection (req.answers (declaredGraph cat)))

-- Well-formedness and the rewriting check.
#guard decide ((chainPlan rwGood.steps).WellFormed cat)
#guard !decide ((chainPlan rwBad.steps).WellFormed cat)
#guard rwGood.check cat reqNames
#guard !rwBad.check cat reqNames
-- A plan that covers only the first triple pattern is not a rewriting.
#guard !(Rewriting.check cat reqNames { steps := [{ src := 1, args := [.var "x", .var "y"] }] })
-- The well-formed plan never finds an input unbound; the bad one does.
#guard !(rwGood.toPlan reqNames).inputFailure cat { binding := [], approx := false }
#guard (rwBad.toPlan reqNames).inputFailure cat { binding := [], approx := false }

-- Executed answers equal the reference evaluator's answers over the
-- materialised declared graph: alice knows bob ("Bob"); bob knows carol
-- ("Carol") is removed by the filter.
#guard canon reqNames.projection (planRows (rwGood.toPlan reqNames)) == [[some alice, some (lit "Bob")]]
#guard sameAnswers reqNames (rwGood.toPlan reqNames)
#guard (canon reqNames.projection (reqNames.answers (declaredGraph cat))).length == 1
#guard ((rwGood.toPlan reqNames).run cat).all (fun x => !x.approx)
-- The bad plan returns nothing (its first access has no input).
#guard (rwBad.toPlan reqNames).run cat |>.isEmpty

/-! ## Requirement without filter: every knows edge with the name -/

def reqAll : Requirement :=
  { reqNames with filters := [], projection := ["x", "y", "n"] }

#guard rwGood.check cat reqAll
#guard sameAnswers reqAll (rwGood.toPlan reqAll)
#guard ((rwGood.toPlan reqAll).run cat).length == 2

/-! ## Approximate source: rows are marked -/

def reqAge : Requirement where
  bgp := [ { s := .var "x", p := .iri pKnows, o := .var "y" },
           { s := .var "y", p := .iri pAge,   o := .var "a" } ]
  projection := ["x", "a"]

def rwAge : Rewriting :=
  { steps := [ { src := 1, args := [.var "x", .var "y"] },
               { src := 2, args := [.var "y", .var "a"] } ] }

#guard rwAge.check cat reqAge
-- The reference evaluator over the declared graph: bob knows carol, 41.
#guard canon reqAge.projection (reqAge.answers (declaredGraph cat)) == [[some bob, some (lit "41")]]
-- The plan returns the approximate value 99, and marks the row.
#guard canon reqAge.projection (planRows (rwAge.toPlan reqAge)) == [[some bob, some (lit "99")]]
#guard ((rwAge.toPlan reqAge).run cat).all (fun x => x.approx)
-- No unmarked row, so the soundness theorem has nothing to cover here.
#guard ((rwAge.toPlan reqAge).run cat).filter (fun x => !x.approx) |>.isEmpty

/-! ## Union of two rewritings -/

#guard (((Plan.union (rwGood.toPlan reqNames) (rwGood.toPlan reqNames)).run cat).length == 2)

/-! ## Axiom audit -/

#print axioms rewriting_sound
#print axioms rewriting_sound_allExact
#print axioms run_unmarked_of_allExact
#print axioms union_sound
#print axioms wellFormed_no_inputFailure

end L4Factoidal.Planner.Tests
