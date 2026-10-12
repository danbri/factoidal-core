/-
Harness/PlannerTest — the test set of the structural planner
(`L4Factoidal.Planner.Search`), OKR batch 2, KR 2.2:
https://github.com/danbri/factoidal/issues/801.

Each case is a requirement over mock capabilities with binding patterns,
the bound `k` on the number of accesses, and the expected verdict (a plan
family, or "not answerable"). For each plan the search returns, the case
checks:

* the rewriting passes `Rewriting.check` and its plan never finds a
  required input unbound (`Plan.inputFailure`);
* an exact plan: `Plan.exec` against the mock sources gives the reference
  evaluator's answers over the materialised declared graph (multiset
  equality of the projected rows); with mode `subset`, a sub-multiset
  that is strictly smaller (a sound plan that is not complete);
* a plan that uses an approximate source: every row carries the marker.

Expected failures (CLAUDE.md, "A stated shortfall is a failing test plus
an open issue"; `skills/test-suites/SKILL.md` § Expected failures, form
"Lean probes"). Each `xfail` case states the behaviour that is missing
today and names https://github.com/danbri/factoidal/issues/801. It is
counted in the `expected-fail` bucket while it fails. When it passes, the
run prints `XPASS` and exits 1: flip it to a plain case and update the
issue.

Prints "planner: N pass, M fail, K expected-fail (out of T)"; the exit
code is 0 only when M = 0 and there is no XPASS.
-/
import L4Factoidal.Planner.Search
import L4Factoidal.Planner.FromQuery
import L4Factoidal.SPARQL.Parser

namespace PlannerTest

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner

def issue801 : String := "https://github.com/danbri/factoidal/issues/801"

/-! ## Terms -/

def fallbackIri : WfIri := ⟨"http://example.org/invalid", rfl⟩

def mkWf (s : String) : WfIri := if h : isIri s = true then ⟨s, h⟩ else fallbackIri

def ex (n : String) : Term := .iri (mkWf ("http://example.org/" ++ n))
def exP (n : String) : WfIri := mkWf ("http://example.org/" ++ n)
def lit (s : String) : Term := .literal (Literal.string s)

def alice : Term := ex "alice"
def bob   : Term := ex "bob"
def carol : Term := ex "carol"
def dave  : Term := ex "dave"
def sales : Term := ex "sales"
def eng   : Term := ex "eng"
def s1    : Term := ex "sensor1"
def member : Term := ex "Member"

def pName    : WfIri := exP "name"
def pKnows   : WfIri := exP "knows"
def pAge     : WfIri := exP "age"
def pEmail   : WfIri := exP "email"
def pWorksIn : WfIri := exP "worksIn"
def pReading : WfIri := exP "reading"
def rdfType  : WfIri := mkWf "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

/-! ## Mock sources -/

def lookupImpl (ext : List Tuple) : InputBinding → List Tuple :=
  fun inp => ext.filter (tupleMatchesInput inp)

def tmpl (p : WfIri) (o : Nat := 1) : TripleTemplate :=
  { s := .arg 0, p := .const (.iri p), o := .arg o }

def mkSrc (name : String) (arity : Nat) (inputs : List Nat) (cost : CostModel)
    (templates : List TripleTemplate) (ext : List Tuple)
    (exactness : Exactness := .exact) (impl : Option (InputBinding → List Tuple) := none) :
    Source where
  cap := { name := name, arity := arity, inputs := inputs, location := "mock:" ++ name,
           cost := cost, exactness := exactness }
  mapping := { templates := templates }
  sem := { ext := ext, impl := impl.getD (lookupImpl ext) }

def namesExt : List Tuple :=
  [[alice, lit "Alice"], [bob, lit "Bob"], [carol, lit "Carol"], [dave, lit "Dave"]]

/-- REST lookup: the subject (position 0) is a required input. -/
def people : Source :=
  mkSrc "people-rest" 2 [0] { perCall := 50, perRow := 1, callQuota := some 1000 } [tmpl pName] namesExt

/-- The same relation as a free scan, at a higher cost. -/
def namesScan : Source :=
  mkSrc "names-scan" 2 [] { perCall := 500, perRow := 1 } [tmpl pName] namesExt

/-- The same relation by name: the object (position 1) is a required input. -/
def byName : Source :=
  mkSrc "name-index-rest" 2 [1] { perCall := 30, perRow := 1 } [tmpl pName] namesExt

/-- SPARQL-endpoint-like free scan. -/
def knows : Source :=
  mkSrc "knows-sparql" 2 [] { perCall := 200, perRow := 1 } [tmpl pKnows]
    [[alice, bob], [bob, carol], [carol, dave]]

def memberTmpl : TripleTemplate :=
  { s := .arg 0, p := .const (.iri rdfType), o := .const member }

/-- A unary relation: every listed person is a `Member`. -/
def members : Source :=
  mkSrc "members-scan" 1 [] { perCall := 100, perRow := 1 } [memberTmpl]
    [[alice], [bob], [carol], [dave]]

/-- The same relation, listing only two people. -/
def membersPartial : Source :=
  mkSrc "members-partial-scan" 1 [] { perCall := 100, perRow := 1 } [memberTmpl] [[alice], [bob]]

/-- An SQL-like table (person, name, department): one tuple gives a
`name` triple and a `worksIn` triple. -/
def employee : Source :=
  mkSrc "employee-sql" 3 [] { perCall := 300, perRow := 1 } [tmpl pName 1, tmpl pWorksIn 2]
    [[alice, lit "Alice", sales], [bob, lit "Bob", eng]]

def agesExt : List Tuple := [[carol, lit "41"], [dave, lit "30"]]

/-- LLM-like source: approximate; for Carol it answers 99, not 41. -/
def ageLlm : Source :=
  mkSrc "age-llm" 2 [0] { perCall := 2000, perRow := 0, callQuota := some 10 } [tmpl pAge] agesExt
    (exactness := .approximate) (impl := some (lookupImpl [[carol, lit "99"], [dave, lit "30"]]))

/-- An exact age source, more expensive than the LLM. -/
def ageDb : Source :=
  mkSrc "age-db" 2 [0] { perCall := 5000, perRow := 1 } [tmpl pAge] agesExt

def email : Source :=
  mkSrc "email-rest" 2 [0] { perCall := 40, perRow := 1 } [tmpl pEmail]
    [[bob, .iri (mkWf "mailto:bob@example.org")], [carol, .iri (mkWf "mailto:carol@example.org")]]

/-- A sensor read: the sensor (subject) is a required input. -/
def sensor : Source :=
  mkSrc "sensor-rest" 2 [0] { perCall := 10, perRow := 1 } [tmpl pReading] [[s1, lit "20"]]

/-- A triple scan: the predicate is a tuple position. -/
def triples : Source :=
  mkSrc "triples-sparql" 3 [] { perCall := 1000, perRow := 1 }
    [{ s := .arg 0, p := .arg 1, o := .arg 2 }]
    [[alice, .iri pKnows, bob], [bob, .iri pName, lit "Bob"]]

/-- A triple scan that requires a key (position 3) that no triple pattern
mentions. -/
def keyed : Source :=
  mkSrc "keyed-scan" 4 [3] { perCall := 10, perRow := 1 }
    [{ s := .arg 0, p := .arg 1, o := .arg 2 }]
    [[alice, .iri pKnows, bob, lit "k1"]]

/-- The REST lookup whose implementation returns only the first two
tuples of its extension: sound, not complete for its inputs. -/
def peopleLossy : Source :=
  mkSrc "people-rest-lossy" 2 [0] { perCall := 50, perRow := 1 } [tmpl pName] namesExt
    (impl := some (lookupImpl (namesExt.take 2)))

/-- The REST lookup with a call quota of 1. -/
def peopleQuota : Source :=
  mkSrc "people-rest-quota1" 2 [0] { perCall := 50, perRow := 1, callQuota := some 1 }
    [tmpl pName] namesExt

/-! ## Requirements -/

def tp (s : PatternSubject) (p : WfIri) (o : PatternTerm) : TriplePattern :=
  { s := s, p := .iri p, o := o }

def v (n : String) : PatternTerm := .var n
def sv (n : String) : PatternSubject := .var n
def si (t : Term) : PatternSubject := match t with | .iri i => .iri i | _ => .var "bad"
def oi (t : Term) : PatternTerm := match t with | .iri i => .iri i | _ => .var "bad"
def ol (s : String) : PatternTerm := .literal (Literal.string s)

def reqChain : Requirement :=
  { bgp := [tp (sv "x") pKnows (v "y"), tp (sv "y") pName (v "n")], projection := ["x", "n"] }

def notCarol : RowFilter := RowFilter.onVar "n" (fun o => o != some (lit "Carol"))

def reqAge : Requirement :=
  { bgp := [tp (sv "x") pKnows (v "y"), tp (sv "y") pAge (v "a")], projection := ["x", "a"] }

def reqXName : Requirement :=
  { bgp := [tp (sv "x") pName (v "n")], projection := ["x", "n"] }

def reqAllTriples : Requirement :=
  { bgp := [{ s := sv "s", p := v "p", o := v "o" }], projection := ["s", "p", "o"] }

def sparqlChain : String :=
  "SELECT ?x ?n WHERE { ?x <http://example.org/knows> ?y . ?y <http://example.org/name> ?n }"

def sparqlGraph : String :=
  "SELECT ?x WHERE { GRAPH <http://example.org/g> { ?x <http://example.org/knows> ?y } }"

def sparqlFilter : String :=
  "SELECT ?x ?n WHERE { ?x <http://example.org/knows> ?y . ?y <http://example.org/name> ?n FILTER(?n != \"Carol\") }"

def reqOfSparql (text : String) : Option Requirement :=
  match parseSparql text with
  | .ok q    => Requirement.ofQuery? q
  | .error _ => none

/-! ## Answers -/

def canon (vs : List VarName) (rows : List Binding) : List (List (Option Term)) :=
  rows.map (fun mu => vs.map (fun x => mu.lookup x))

/-- The declared graph as an RDF graph (a set of triples). -/
def materialise (cat : Catalog) : Graph := (declaredGraph cat).eraseDups

def refRows (cat : Catalog) (req : Requirement) : List (List (Option Term)) :=
  canon req.projection (req.answers (materialise cat))

def runRows (cat : Catalog) (req : Requirement) (rw : Rewriting) : List Row :=
  (rw.toPlan req).run cat

def planRows (cat : Catalog) (req : Requirement) (rw : Rewriting) : List (List (Option Term)) :=
  canon req.projection ((runRows cat req rw).map Row.binding)

def sameMultiset (a b : List (List (Option Term))) : Bool :=
  a.length == b.length && a.all (fun x => a.count x == b.count x)

def strictSubMultiset (a b : List (List (Option Term))) : Bool :=
  a.length < b.length && a.all (fun x => a.count x ≤ b.count x)

def srcNames (cat : Catalog) (rw : Rewriting) : List String :=
  rw.steps.map (fun a => (cat[a.src]?.map (·.cap.name)).getD "?")

/-- Calls the executor makes to each access of a chain: one per row of the
prefix before it. -/
def stepCalls (cat : Catalog) (rw : Rewriting) : List (Access × Nat) :=
  (List.range rw.steps.length).filterMap (fun i =>
    rw.steps[i]?.map (fun a => (a, ((chainPlan (rw.steps.take i)).run cat).length)))

def withinQuota (cat : Catalog) (rw : Rewriting) : Bool :=
  (stepCalls cat rw).all (fun (a, calls) =>
    match cat[a.src]? with
    | some s => match s.cap.cost.callQuota with
      | some q => calls ≤ q
      | none   => true
    | none => true)

/-! ## Cases -/

inductive Mode where
  | equal
  | subset

structure Case where
  id : String
  cat : Catalog
  req : Option Requirement
  k : Nat
  answerable : Bool
  first : Option (List String) := none
  firstApprox : Option Bool := none
  minPlans : Nat := 0
  mode : Mode := .equal

/-- The checks of one plan; the list of failures. -/
def checkPlan (c : Case) (req : Requirement) (r : Ranked) : List String :=
  let rw := r.rewriting
  let tag := s!"plan {srcNames c.cat rw}"
  let rows := runRows c.cat req rw
  let f1 := if rw.check c.cat req then [] else [s!"{tag}: check fails"]
  let f2 := if (rw.toPlan req).inputFailure c.cat { binding := [], approx := false } then
      [s!"{tag}: an input is unbound at run time"] else []
  let f3 :=
    if r.approx then
      if rows.all (·.approx) then [] else [s!"{tag}: approximate plan has an unmarked row"]
    else
      if rows.any (·.approx) then [s!"{tag}: exact plan has a marked row"] else
      let got := planRows c.cat req rw
      let want := refRows c.cat req
      match c.mode with
      | .equal =>
        if sameMultiset got want then []
        else [s!"{tag}: answers differ from the reference ({got.length} rows, want {want.length})"]
      | .subset =>
        if strictSubMultiset got want then []
        else [s!"{tag}: answers are not a strict sub-multiset of the reference"]
  f1 ++ f2 ++ f3

def runCase (c : Case) : List String :=
  match c.req with
  | none => ["the requirement could not be built"]
  | some req =>
    let fam := search c.cat req c.k
    let fv := if (!fam.isEmpty) == c.answerable then []
      else [s!"verdict: answerable = {!fam.isEmpty}, want {c.answerable}"]
    let ff := match c.first, fam.head? with
      | some want, some r =>
        if srcNames c.cat r.rewriting == want then []
        else [s!"first plan {srcNames c.cat r.rewriting}, want {want}"]
      | some want, none => [s!"no plan, want first {want}"]
      | none, _ => []
    let fa := match c.firstApprox, fam.head? with
      | some want, some r => if r.approx == want then [] else [s!"first plan approx = {r.approx}"]
      | _, _ => []
    let fn := if fam.length ≥ c.minPlans then [] else [s!"{fam.length} plans, want at least {c.minPlans}"]
    fv ++ ff ++ fa ++ fn ++ fam.flatMap (checkPlan c req)

def cases : List Case := [
  { id := "subject-lookup", cat := [people], k := 2, answerable := true,
    req := some { bgp := [tp (si alice) pName (v "n")], projection := ["n"] },
    first := some ["people-rest"] },
  { id := "object-lookup", cat := [byName], k := 2, answerable := true,
    req := some { bgp := [tp (sv "x") pName (ol "Bob")], projection := ["x"] },
    first := some ["name-index-rest"] },
  { id := "object-input-never-bound", cat := [byName], k := 3, answerable := false,
    req := some reqXName },
  { id := "two-sources-cheaper-first", cat := [namesScan, people], k := 2, answerable := true,
    req := some { bgp := [tp (si alice) pName (v "n")], projection := ["n"] },
    first := some ["people-rest"], minPlans := 2 },
  { id := "dependent-join", cat := [knows, people], k := 2, answerable := true,
    req := some reqChain, first := some ["knows-sparql", "people-rest"] },
  { id := "dependent-join-bound-too-small", cat := [knows, people], k := 1, answerable := false,
    req := some reqChain },
  { id := "dependent-join-three", cat := [knows, people], k := 3, answerable := true,
    req := some { bgp := [tp (sv "x") pKnows (v "y"), tp (sv "y") pKnows (v "z"),
                          tp (sv "z") pName (v "n")], projection := ["x", "n"] },
    first := some ["knows-sparql", "knows-sparql", "people-rest"] },
  { id := "input-never-bound", cat := [sensor, knows], k := 3, answerable := false,
    req := some { bgp := [tp (sv "s") pReading (v "r")], projection := ["s", "r"] } },
  { id := "no-source-for-predicate", cat := [people, knows], k := 3, answerable := false,
    req := some { bgp := [tp (sv "x") pWorksIn (v "d")], projection := ["x", "d"] } },
  -- A scan of another relation could bind ?x for the lookup, but nothing
  -- states that it lists every person: no plan is admitted.
  { id := "binder-without-constraint-not-admitted", cat := [people, membersPartial], k := 2,
    answerable := false, req := some reqXName },
  { id := "source-not-complete-for-inputs", cat := [knows, peopleLossy], k := 2, answerable := true,
    req := some reqChain, first := some ["knows-sparql", "people-rest-lossy"], mode := .subset },
  { id := "indirect-through-mapping", cat := [people, employee], k := 2, answerable := true,
    req := some { bgp := [tp (sv "e") pName (v "n"), tp (sv "e") pWorksIn (v "d")],
                  projection := ["e", "n", "d"] },
    first := some ["employee-sql"] },
  { id := "approximate-marked", cat := [knows, ageLlm], k := 2, answerable := true,
    req := some reqAge, first := some ["knows-sparql", "age-llm"], firstApprox := some true },
  { id := "exact-before-approximate", cat := [knows, ageLlm, ageDb], k := 2, answerable := true,
    req := some reqAge, first := some ["knows-sparql", "age-db"], firstApprox := some false,
    minPlans := 2 },
  { id := "filter", cat := [knows, people], k := 2, answerable := true,
    req := some { reqChain with filters := [notCarol] } },
  { id := "constant-in-output", cat := [knows], k := 1, answerable := true,
    req := some { bgp := [tp (si alice) pKnows (v "y")], projection := ["y"] },
    first := some ["knows-sparql"] },
  { id := "triple-scan-variable-predicate", cat := [triples], k := 1, answerable := true,
    req := some reqAllTriples, first := some ["triples-sparql"] },
  { id := "mapping-constant", cat := [members], k := 1, answerable := true,
    req := some { bgp := [{ s := sv "x", p := .iri rdfType, o := oi member }], projection := ["x"] } },
  { id := "empty-bgp", cat := [people], k := 0, answerable := true,
    req := some { bgp := [], projection := [] }, first := some [] },
  { id := "dependent-join-email", cat := [knows, email], k := 2, answerable := true,
    req := some { bgp := [tp (sv "x") pKnows (v "y"), tp (sv "y") pEmail (v "m")],
                  projection := ["x", "m"] },
    first := some ["knows-sparql", "email-rest"] },
  { id := "all-constants", cat := [knows], k := 1, answerable := true,
    req := some { bgp := [tp (si alice) pKnows (oi bob)], projection := [] } },
  { id := "from-sparql", cat := [knows, people], k := 2, answerable := true,
    req := reqOfSparql sparqlChain, first := some ["knows-sparql", "people-rest"] },
  { id := "three-sources-ranked", cat := [knows, people, namesScan], k := 2, answerable := true,
    req := some reqChain, first := some ["knows-sparql", "people-rest"], minPlans := 2 }
]

/-- The hand-written rewriting of `?s ?p ?o` over `keyed`, with the key
`"k1"` (a constant that the requirement does not mention), passes the
check and gives the reference answers. Control for `xfail` case
`search-outside-constant`. -/
def keyedRw : Rewriting :=
  { steps := [{ src := 0, args := [.var "s", .var "p", .var "o", .const (lit "k1")] }] }

def controlCases : List (String × List String) := [
  ("outside-constant-control",
    (if keyedRw.check [keyed] reqAllTriples then [] else ["check fails"]) ++
    (if sameMultiset (planRows [keyed] reqAllTriples keyedRw) (refRows [keyed] reqAllTriples)
     then [] else ["answers differ"])),
  ("from-sparql-filter-rejected-today",
    -- `ofQuery?` returns none for FILTER and GRAPH (see the xfail cases).
    (if (reqOfSparql sparqlFilter).isNone && (reqOfSparql sparqlGraph).isNone then []
     else ["ofQuery? accepted FILTER or GRAPH; flip the xfail cases"]))
]

/-! ## Expected failures (issue 801)

Each test returns `true` when the missing behaviour is present. -/

structure XCase where
  id : String
  issue : String
  what : String
  test : Unit → Bool

def xcases : List XCase := [
  { id := "search-outside-constant", issue := issue801,
    what := "an access with a required input that no requirement pattern names (a key constant)",
    test := fun _ => !(search [keyed] reqAllTriples 1).isEmpty },
  { id := "quota-in-admission", issue := issue801,
    what := "cost model used for admission: no plan in the family exceeds a call quota",
    test := fun _ => (search [knows, peopleQuota] reqChain 2).all
      (fun r => withinQuota [knows, peopleQuota] r.rewriting) },
  { id := "runtime-quota-adaptation", issue := issue801,
    what := "execution state machine: the run stays within each call quota and gives the reference answers",
    test := fun _ =>
      match (search [knows, peopleQuota, namesScan] reqChain 2).head? with
      | some r => withinQuota [knows, peopleQuota, namesScan] r.rewriting &&
          sameMultiset (planRows [knows, peopleQuota, namesScan] reqChain r.rewriting)
            (refRows [knows, peopleQuota, namesScan] reqChain)
      | none => false },
  { id := "named-graph-requirement", issue := issue801,
    what := "named graphs: a requirement with GRAPH <g> { ... }",
    test := fun _ => (reqOfSparql sparqlGraph).isSome },
  { id := "rowfilter-from-expr", issue := issue801,
    what := "RowFilter from a SPARQL FILTER expression",
    test := fun _ => (reqOfSparql sparqlFilter).isSome },
  { id := "indirect-binder-inclusion-dependency", issue := issue801,
    what := "an indirect plan through a binder access justified by an inclusion dependency (members lists every person)",
    test := fun _ =>
      match (search [people, members] reqXName 2).head? with
      | some r => sameMultiset (planRows [people, members] reqXName r.rewriting)
          (refRows [people, members] reqXName)
      | none => false },
  { id := "wide-relation-unnamed-output", issue := issue801,
    what := "an access with an output position that the requirement does not use (no fresh variable in Rewriting.check)",
    test := fun _ =>
      match (search [employee] reqXName 1).head? with
      | some r => sameMultiset (planRows [employee] reqXName r.rewriting) (refRows [employee] reqXName)
      | none => false }
]

def main : IO UInt32 := do
  let mut pass := 0
  let mut fail := 0
  let mut xfail := 0
  let mut xpass := 0
  for c in cases do
    let errs := runCase c
    if errs.isEmpty then
      pass := pass + 1
      IO.println s!"PASS {c.id}"
    else
      fail := fail + 1
      IO.println s!"FAIL {c.id}: {errs}"
  for (id, errs) in controlCases do
    if errs.isEmpty then
      pass := pass + 1
      IO.println s!"PASS {id}"
    else
      fail := fail + 1
      IO.println s!"FAIL {id}: {errs}"
  for x in xcases do
    if x.test () then
      xpass := xpass + 1
      IO.println s!"XPASS {x.id}: {x.what} now holds; flip to an assertion and update {x.issue}"
    else
      xfail := xfail + 1
      IO.println s!"xfail {x.id}: {x.what} ({x.issue})"
  let failAll := fail + xpass
  IO.println s!"planner: {pass} pass, {failAll} fail, {xfail} expected-fail (out of {pass + failAll + xfail})"
  return (if failAll == 0 then 0 else 1)

end PlannerTest

def main : IO UInt32 := PlannerTest.main
