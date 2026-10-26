/-
Harness/PlannerCheck — the case machinery shared by the planner test sets
(`Harness/PlannerTest.lean`, KR 2.2, and `Harness/PlannerKinds.lean`, KR 2.3;
https://github.com/danbri/factoidal/issues/801): requirement builders, the
reference answers over the materialised declared graph, and the checks of
one plan family (`runCase`). Moved from `Harness/PlannerTest.lean` without
change of behaviour.
-/
import L4Factoidal.Planner.Search
import L4Factoidal.Planner.FromQuery

namespace PlannerCheck

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner

def issue801 : String := "https://github.com/danbri/factoidal/issues/801"

def fallbackIri : WfIri := ⟨"http://example.org/invalid", rfl⟩

def mkWf (s : String) : WfIri := if h : isIri s = true then ⟨s, h⟩ else fallbackIri

def tp (s : PatternSubject) (p : WfIri) (o : PatternTerm) : TriplePattern :=
  { s := s, p := .iri p, o := o }

def v (n : String) : PatternTerm := .var n
def sv (n : String) : PatternSubject := .var n
def si (t : Term) : PatternSubject := match t with | .iri i => .iri i | _ => .var "bad"
def oi (t : Term) : PatternTerm := match t with | .iri i => .iri i | _ => .var "bad"
def ol (s : String) : PatternTerm := .literal (Literal.string s)

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

/-- An expected-failure case: `test` returns `true` when the missing
behaviour is present. -/
structure XCase where
  id : String
  issue : String
  what : String
  test : Unit → Bool


end PlannerCheck
