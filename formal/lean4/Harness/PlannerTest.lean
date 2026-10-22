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

The source-kind cases of KR 2.3 (SBM11, in-memory, SPARQL endpoint,
Façade-X file, REST, MCP) are in `Harness/PlannerKinds.lean`; `main` runs
them after the cases here and adds their counts. The shared case
machinery is `Harness/PlannerCheck.lean`.

Prints "planner: N pass, M fail, K expected-fail (out of T)"; the exit
code is 0 only when M = 0 and there is no XPASS.
-/
import L4Factoidal.Planner.Search
import L4Factoidal.Planner.FromQuery
import L4Factoidal.Planner.Exec
import L4Factoidal.SPARQL.Parser
import Harness.PlannerCheck
import Harness.PlannerKinds

namespace PlannerTest

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner PlannerCheck

/-! ## Terms -/

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

/-- An RDF 1.2 triple-term pattern in the object position
(https://github.com/danbri/factoidal/issues/792 item 1). -/
def sparqlTripleTerm : String :=
  "SELECT ?x ?y WHERE { ?x <http://example.org/says> <<( <http://example.org/a> <http://example.org/knows> ?y )>> }"

/-- `reqOfSparql` with the SPARQL 1.2 grammar. -/
def reqOfSparql12 (text : String) : Option Requirement :=
  match parseSparql text none .v12 with
  | .ok q    => Requirement.ofQuery? q
  | .error _ => none

/-- The query parses (SPARQL 1.2 grammar) and its WHERE clause is one triple
    pattern whose object is a triple term, so `ofQuery?` refusing it is the
    refusal of the triple term and not of a parse error. -/
def tripleTermQueryParses : Bool :=
  match parseSparql sparqlTripleTerm none .v12 with
  | .ok q =>
    match q.pattern with
    | .bgp [tp] => match tp.o with | .tripleTerm _ _ _ => true | _ => false
    | _ => false
  | .error _ => false

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
     else ["ofQuery? accepted FILTER or GRAPH; flip the xfail cases"])),
  ("triple-term-query-parses",
    -- the control of xfail case `triple-term-requirement`
    (if tripleTermQueryParses then [] else ["the triple-term query does not parse to one triple-term pattern"]))
]

/-! ## Expected failures (issue 801)

Each test returns `true` when the missing behaviour is present. -/

def xcases : List XCase := [
  { id := "search-outside-constant", issue := issue801,
    what := "an access with a required input that no requirement pattern names (a key constant)",
    test := fun _ => !(search [keyed] reqAllTriples 1).isEmpty },
  { id := "named-graph-requirement", issue := issue801,
    what := "named graphs: a requirement with GRAPH <g> { ... }",
    test := fun _ => (reqOfSparql sparqlGraph).isSome },
  { id := "rowfilter-from-expr", issue := issue801,
    what := "RowFilter from a SPARQL FILTER expression",
    test := fun _ => (reqOfSparql sparqlFilter).isSome },
  { id := "triple-term-requirement", issue := issue801,
    what := "an RDF 1.2 triple-term pattern in a requirement (no access shape returns one; ofQuery? refuses it)",
    test := fun _ => (reqOfSparql12 sparqlTripleTerm).isSome },
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

/-! ## KR 2.4: the execution state machine (`Planner/Exec.lean`)

Each case runs the driver `Exec.run` over the plan family of `search`
and checks the run's status, its output against the reference
evaluator's answers over the materialised declared graph (multiset
equality), the call counts against the call quotas, and the markers.
`runtime-quota-adaptation` was an expected failure of KR 2.2; this work
makes it pass, so it is an assertion now. -/

section ExecCases
open L4Factoidal.Planner.Exec

def outRows (req : Requirement) (st : State) : List (List (Option Term)) :=
  canon req.projection (st.output.map Row.binding)

/-- Every call count is within its source's call quota. -/
def callsWithinQuota (cat : Catalog) (st : State) : Bool :=
  (List.range cat.length).all (fun i =>
    match cat[i]? with
    | some s => match s.cap.cost.callQuota with
      | some q => st.calls i ≤ q
      | none   => true
    | none => true)

def callList (cat : Catalog) (st : State) : List Nat := (List.range cat.length).map st.calls

def statusName : Status → String
  | .running => "running"
  | .done    => "done"
  | .stopped => "stopped"

/-- The fault schedule that fails every call of source `i`. -/
def failAll (i : Nat) : Faults := fun j _ => j == i

/-- The fault schedule that fails call `n` of source `i` only. -/
def failOnce (i n : Nat) : Faults := fun j m => j == i && m == n

/-- Common checks: the run exists, ends with `want`, and stays within the
call quotas; when `want` is `done` and `exact`, the output is the
reference answers and no row is marked. -/
def execChecks (cat : Catalog) (req : Requirement) (k : Nat) (cfg : Config) (faults : Faults)
    (want : Status) (exact : Bool := true) : Option State × List String :=
  match run cat req k cfg faults with
  | none => (none, ["no plan family"])
  | some st =>
    let f1 := if st.status == want then [] else
      [s!"status {statusName st.status}, want {statusName want}"]
    let f2 := if callsWithinQuota cat st then [] else [s!"a call quota is exceeded: {callList cat st}"]
    let f3 := if want == .done && exact then
        (if sameMultiset (outRows req st) (refRows cat req) then []
         else [s!"output differs from the reference ({st.output.length} rows)"]) ++
        (if st.output.any (·.approx) then ["an exact run has a marked row"] else [])
      else []
    (some st, f1 ++ f2 ++ f3)

/-- A source with the statistic `rowsPerCall := some n`. -/
def withStat (s : Source) (n : Nat) : Source :=
  { s with cap := { s.cap with cost := { s.cap.cost with rowsPerCall := some n } } }

/-- `knows` with a statistic that is too low: it declares 1 tuple per
call and answers 3. A plan that the estimate admits can meet a quota at
run time. -/
def knowsLow : Source := withStat knows 1

/-- `knows` with its true statistic (3 tuples). -/
def knowsTrue : Source := withStat knows 3

/-- A scan with a row quota of 1 that declares 1 tuple per call and
answers 3. -/
def knowsRowQ1 : Source :=
  mkSrc "knows-sparql-rowquota1" 2 [] { perCall := 200, perRow := 1, rowQuota := some 1, rowsPerCall := some 1 }
    [tmpl pKnows] [[alice, bob], [bob, carol], [carol, dave]]

/-- Another `knows` scan, more expensive, with no quota. -/
def knowsB : Source :=
  mkSrc "knows-sparql-b" 2 [] { perCall := 300, perRow := 1, rowsPerCall := some 1 }
    [tmpl pKnows] [[alice, bob], [bob, carol], [carol, dave]]

/-- Two people know `carol`: the lookup of `carol` is a cache hit the
second time. -/
def knowsDup : Source :=
  mkSrc "knows-dup" 2 [] { perCall := 200, perRow := 1 } [tmpl pKnows]
    [[alice, carol], [bob, carol]]

/-! Measured rows: 20 people known by `alice`. The scan declares 1 tuple
per call and answers 20. -/

def pers (i : Nat) : Term := ex ("p" ++ toString i)

def bigKnowsExt : List Tuple := (List.range 20).map (fun i => [alice, pers i])
def bigNamesExt : List Tuple := (List.range 20).map (fun i => [pers i, lit ("P" ++ toString i)])

def knowsBig : Source :=
  mkSrc "knows-big" 2 [] { perCall := 200, perRow := 1, rowsPerCall := some 1 } [tmpl pKnows] bigKnowsExt
def lookupBigQ : Source :=
  mkSrc "names-lookup-quota2" 2 [0] { perCall := 50, perRow := 1, callQuota := some 2 } [tmpl pName] bigNamesExt
def lookupBig : Source :=
  mkSrc "names-lookup" 2 [0] { perCall := 60, perRow := 1 } [tmpl pName] bigNamesExt
def scanBig : Source :=
  mkSrc "names-scan-big" 2 [] { perCall := 500, perRow := 1, rowsPerCall := some 20 } [tmpl pName] bigNamesExt

/-- Static order: the quota lookup, the other lookup, the scan. -/
def catRows : Catalog := [knowsBig, lookupBigQ, lookupBig, scanBig]

/-! Measured latency: three lookups of the same relation; the quota
lookup and lookup B are at location `host-b`, lookup C at `host-c`. -/

def mkLookupAt (name loc : String) (cost : CostModel) : Source :=
  let s := mkSrc name 2 [0] cost [tmpl pName] namesExt
  { s with cap := { s.cap with location := loc } }

def catLat : Catalog :=
  [knowsLow,
   mkLookupAt "names-q" "host-b" { perCall := 10, perRow := 1, callQuota := some 1 },
   mkLookupAt "names-b" "host-b" { perCall := 20, perRow := 1 },
   mkLookupAt "names-c" "host-c" { perCall := 60, perRow := 1 }]

/-- Every call at `host-b` (sources 1 and 2) takes 1000 units. -/
def slowHostB : Latency := fun i _ => if i == 1 || i == 2 then 1000 else 0

def usesSrc (st : State) (i : Nat) : Bool := st.plan.steps.any (·.src == i)

def execCases : List (String × List String) :=
  let catQ := [knowsLow, peopleQuota]
  let catA := [knowsLow, peopleQuota, namesScan]
  let catF := [knows, people, namesScan]
  [
  -- Admission (KR 4.2): with no statistic the estimate is 100 calls of the
  -- lookup, over its quota of 1; `search` keeps the plan (structural
  -- family), `searchAdmitted` drops it; with a quota of 1000 it is
  -- admitted.
  ("quota-in-admission",
    (if (search [knows, peopleQuota] reqChain 2).isEmpty then ["no structural plan"] else []) ++
    (if (searchAdmitted [knows, peopleQuota] reqChain 2).all
          (fun r => withinQuota [knows, peopleQuota] r.rewriting) &&
        (searchAdmitted [knows, peopleQuota] reqChain 2).isEmpty
     then [] else ["a plan over the call quota is admitted"]) ++
    (if (searchAdmitted [knows, people] reqChain 2).isEmpty then ["the plan within quota is not admitted"] else []) ++
    (if (run [knows, peopleQuota] reqChain 2 {} noFaults).isNone then [] else ["a run without an admitted plan"])),
  -- The static first plan needs 3 calls of a source with a call quota of 1,
  -- and the family has no other plan: the run stops within the quota.
  ("exec-quota-stops",
    (match (search catQ reqChain 2).head? with
     | some r => if withinQuota catQ r.rewriting then ["the static plan does not exceed the quota"] else []
     | none => ["no plan"]) ++
    (let (st?, errs) := execChecks catQ reqChain 2 {} noFaults .stopped
     errs ++ match st? with
       | some st => (if st.output.isEmpty then [] else ["a stopped run has output"]) ++
           (if st.calls 1 == 1 then [] else [s!"calls {callList catQ st}, want 1 call of the quota source"])
       | none => [])),
  -- The same quota with another plan in the family: the run switches and
  -- gives the reference answers.
  ("runtime-quota-adaptation",
    let (st?, errs) := execChecks catA reqChain 2 {} noFaults .done
    errs ++ match st? with
      | some st => if st.switches ≥ 1 then [] else ["no switch"]
      | none => []),
  -- Every call of the lookup fails; after one retry the run switches to
  -- another plan of the family and gives the reference answers.
  ("exec-failure-adaptation",
    let (st?, errs) := execChecks catF reqChain 2 {} (failAll 1) .done
    errs ++ match st? with
      | some st => (if st.switches == 1 then [] else [s!"{st.switches} switches, want 1"]) ++
          (if st.calls 1 == 2 then [] else [s!"calls {callList catF st}, want 2 calls of the lookup"])
      | none => []),
  -- The first call of the lookup fails and the retry succeeds: no switch,
  -- one extra call.
  ("exec-retry-succeeds",
    let (st?, errs) := execChecks [knows, people] reqChain 2 {} (failOnce 1 1) .done
    errs ++ match st? with
      | some st => (if st.switches == 0 then [] else ["a switch"]) ++
          (if st.calls 1 == 4 then [] else [s!"calls {callList [knows, people] st}, want 4 calls of the lookup"])
      | none => []),
  -- No retry allowed and no other plan: the failure stops the run.
  ("exec-retry-bound-stops",
    let (st?, errs) := execChecks [knows, people] reqChain 2 { maxRetries := 0 } (failOnce 1 1) .stopped
    errs ++ match st? with
      | some st => if st.output.isEmpty && st.retries == 0 then [] else ["output or retries"]
      | none => []),
  -- An approximate source: every output row is marked.
  ("exec-approximate-marked",
    let (st?, errs) := execChecks [knowsTrue, ageLlm] reqAge 2 {} noFaults .done (exact := false)
    errs ++ match st? with
      | some st => if !st.output.isEmpty && st.output.all (·.approx) then [] else ["a row is not marked"]
      | none => []),
  -- Exact before approximate: the run uses the exact source and gives the
  -- reference answers, unmarked.
  ("exec-exact-before-approximate",
    (execChecks [knowsTrue, ageLlm, ageDb] reqAge 2 {} noFaults .done).2),
  -- Not answerable: no plan family, no run.
  ("exec-not-answerable",
    if (run [byName] reqXName 3 {} noFaults).isNone then [] else ["a run without a plan family"]),
  -- KR 4.2. Row quota at run time: the scan answers 3 tuples, over its
  -- row quota of 1, and the family has no other plan: the run stops with
  -- no output and no tuple counted.
  ("exec-row-quota",
    let req : Requirement := { bgp := [tp (sv "x") pKnows (v "y")], projection := ["x", "y"] }
    let (st?, errs) := execChecks [knowsRowQ1] req 1 {} noFaults .stopped
    errs ++ match st? with
      | some st => (if st.output.length ≤ 1 then [] else ["more than 1 row"]) ++
          (if st.rows 0 ≤ 1 then [] else [s!"{st.rows 0} tuples counted, row quota 1"])
      | none => []),
  -- The same row quota with another scan in the family: the run switches
  -- and gives the reference answers.
  ("exec-row-quota-adaptation",
    let c := [knowsRowQ1, knowsB, people]
    let (st?, errs) := execChecks c reqChain 2 {} noFaults .done
    errs ++ match st? with
      | some st => (if st.switches == 1 then [] else [s!"{st.switches} switches, want 1"]) ++
          (if usesSrc st 1 then [] else ["the final plan does not use the other scan"]) ++
          (if st.rows 0 == 0 then [] else ["tuples over the row quota were counted"])
      | none => []),
  -- After a switch, a call whose answer is known is not made again: the
  -- `knows` scan is called once, and the new plan's first access is a
  -- cache hit.
  ("exec-reuse-after-adaptation",
    let (st?, errs) := execChecks catA reqChain 2 {} noFaults .done
    errs ++ match st? with
      | some st => (if st.switches ≥ 1 then [] else ["no switch"]) ++
          (if st.calls 0 == 1 then [] else [s!"calls {callList catA st}, want 1 call of the scan"]) ++
          (if st.hits ≥ 1 then [] else ["no cache hit"])
      | none => []),
  -- Two rows need the lookup of the same person: one call, one hit.
  ("exec-cache-duplicate-input",
    let c := [knowsDup, people]
    let (st?, errs) := execChecks c reqChain 2 {} noFaults .done
    errs ++ match st? with
      | some st => (if st.calls 1 == 1 && st.hits == 1 then [] else
            [s!"calls {callList c st}, {st.hits} hits; want 1 call of the lookup and 1 hit"])
      | none => []),
  -- Measured rows choose the next plan. The scan declares 1 tuple and
  -- answers 20; the quota lookup is left after 2 calls. In family order
  -- the next plan is the other lookup (20 calls); from the measured 20
  -- tuples the driver takes a plan with the name scan (1 call).
  ("exec-adapt-measured-rows",
    let fam := family catRows reqChain 2
    let (st?, errs) := execChecks catRows reqChain 2 {} noFaults .done
    (match fam with
     | _ :: next :: _ => if next.steps.any (·.src == 2) then [] else
         ["the second admitted plan does not use the other lookup (the control of this case)"]
     | _ => ["fewer than 2 admitted plans"]) ++
    errs ++ match st? with
      | some st => (if st.switches == 1 then [] else [s!"{st.switches} switches, want 1"]) ++
          (if usesSrc st 3 then [] else ["the final plan does not use the name scan"]) ++
          (if st.calls 0 == 1 && st.calls 2 == 0 && st.calls 3 == 1 then [] else
            [s!"calls {callList catRows st}, want [1, 2, 0, 1]"])
      | none => []),
  -- Measured latency chooses the next plan. Calls at `host-b` take 1000
  -- units; lookup B (static cost 20) is at `host-b`, lookup C (60) is not.
  -- With no latency the driver takes lookup B; with `slowHostB`, lookup C.
  ("exec-adapt-measured-latency",
    let (st0?, errs0) := execChecks catLat reqChain 2 {} noFaults .done
    let (st?, errs) := match run catLat reqChain 2 {} noFaults slowHostB with
      | none => (none, ["no run"])
      | some st => (some st,
          (if st.status == Status.done then [] else [s!"status {statusName st.status}"]) ++
          (if callsWithinQuota catLat st then [] else ["a call quota is exceeded"]) ++
          (if sameMultiset (outRows reqChain st) (refRows catLat reqChain) then [] else ["output differs from the reference"]))
    errs0 ++ errs ++
    (match st0? with
     | some st => if usesSrc st 2 then [] else ["with no latency the final plan does not use lookup B"]
     | none => []) ++
    (match st? with
     | some st => (if usesSrc st 3 then [] else ["with host-b slow the final plan does not use lookup C"]) ++
         (if st.latency 1 == 1000 then [] else [s!"latency of the quota lookup {st.latency 1}, want 1000"])
     | none => []))
  ]

/-- For each answerable case of KR 2.2: with no faults, the run ends
`done`, and its output is the run (`Plan.run`) of the family's first plan
when that plan is within the call quotas (same rows, same order). -/
def execEqualsPlanRun : Nat × List String :=
  cases.foldl (fun (n, errs) c =>
    if !c.answerable then (n, errs) else
    match c.req with
    | none => (n, errs)
    | some req =>
      match (searchAdmitted c.cat req c.k).head?, run c.cat req c.k {} noFaults with
      | none, none => (n, errs)
      | some r, some st =>
        if !withinQuota c.cat r.rewriting then (n, errs) else
        let want := canon req.projection (((r.rewriting.toPlan req).run c.cat).map Row.binding)
        if st.status == .done && outRows req st == want && st.switches == 0 then (n + 1, errs)
        else (n + 1, errs ++ [s!"{c.id}: status {statusName st.status}, {st.output.length} rows, want {want.length}"])
      | _, _ => (n + 1, errs ++ [s!"{c.id}: no plan or no run"])) (0, [])

/-- Expected failures of the execution cases (`admission-without-statistic`,
KR 4.2). `exec-row-quota` and
`exec-reuse-after-adaptation` (KR 2.4) are assertions in `execCases` since
KR 4.2 (https://github.com/danbri/factoidal/issues/875). -/
def execXcases : List XCase := [
  { id := "admission-without-statistic", issue := "https://github.com/danbri/factoidal/issues/937",
    what := "admission with no statistic: the scan answers 3 tuples, so the LLM lookup (call quota 10) needs 3 calls, but the estimate (fanout 10) refuses the plan",
    test := fun _ =>
      match run [knows, ageLlm] reqAge 2 {} noFaults with
      | some st => st.status == Status.done
      | none => false }
  ]

end ExecCases

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
  -- KR 2.4: the execution state machine
  for (id, errs) in execCases do
    if errs.isEmpty then
      pass := pass + 1
      IO.println s!"PASS {id}"
    else
      fail := fail + 1
      IO.println s!"FAIL {id}: {errs}"
  let (nEq, errsEq) := execEqualsPlanRun
  if errsEq.isEmpty then
    pass := pass + 1
    IO.println s!"PASS exec-equals-plan-run ({nEq} cases)"
  else
    fail := fail + 1
    IO.println s!"FAIL exec-equals-plan-run ({nEq} cases): {errsEq}"
  for x in execXcases do
    if x.test () then
      xpass := xpass + 1
      IO.println s!"XPASS {x.id}: {x.what} now holds; flip to an assertion and update {x.issue}"
    else
      xfail := xfail + 1
      IO.println s!"xfail {x.id}: {x.what} ({x.issue})"
  -- KR 2.3: the source kinds (`Harness/PlannerKinds.lean`)
  let k ← PlannerKinds.run
  pass := pass + k.pass
  fail := fail + k.fail
  xfail := xfail + k.xfail
  xpass := xpass + k.xpass
  let failAll := fail + xpass
  IO.println s!"planner: {pass} pass, {failAll} fail, {xfail} expected-fail (out of {pass + failAll + xfail})"
  return (if failAll == 0 then 0 else 1)

end PlannerTest

def main (args : List String) : IO UInt32 :=
  match args with
  | ["sbm11-query", gen, rq] => PlannerSbm11IO.runQuery gen rq false
  | ["sbm11-query", gen, rq, "--check-pure"] => PlannerSbm11IO.runQuery gen rq true
  | [] => PlannerTest.main
  | _ => do
    IO.eprintln "usage: l4planner-test [sbm11-query GEN QUERY.rq [--check-pure]]"
    return 2
