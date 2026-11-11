import WebSparql

/-!
# WebSparqlTests: the page's plan is the planners' own

For each example query of `foafnaut:sparql`, `WebSparql.explain` must report what the engine's
planners do, not a parallel account:

- the first step of each basic graph pattern is the pattern `chooseBestTpBackend` picks with
  nothing bound, with the estimate `estimateTpBackend` gives;
- the level-by-level walk gives the rows of `StorePlan.evalBgpBackend`, as a list, and as many
  rows as `GraphPattern.evalIn` gives for the BGP;
- the capability plan shown is the first plan of `Planner.search`, access for access, and its
  rows are as many as the requirement's reference answers;
- the result rows are the rows of `evalSelect`;
- each example has the operator kind it is named for.
-/

namespace WebSparqlTests
open L4Factoidal L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.SPARQL.StorePlan L4Factoidal.SPARQL.StoreBackend
open WebSparql

def graph : Graph := match Syntax.parseTurtle foafSample (some foafBase) with | .ok g => g | .error _ => []

def explained (q : String) : Option Explained := (explain q graph).toOption

def exampleQuery (name : String) : String := ((examples.find? (·.name == name)).map (·.query)).getD ""

def kinds (name : String) : List String :=
  match explained (exampleQuery name) with
  | some e => e.ops.toList.map (·.kind)
  | none => []

/-- The BGPs of an example, with their operators. -/
def bgps (e : Explained) : List (Nat × Bgp) :=
  let idx := (List.range e.ops.size).filter (fun i => (e.ops[i]?.map (·.kind)).getD "" == "bgp")
  idx.zip (bgpsOf walkDepth e.pattern)

/-- The first step under a BGP operator: follow the single-child chain down. -/
def firstStep (e : Explained) : Nat → Nat → Option Op
  | 0, _ => none
  | n + 1, i =>
    match e.ops[i]? with
    | some op => match op.children with
      | [c] => match e.ops[c]? with
        | some child => if child.kind == "scan" then some child else firstStep e n c
        | none => none
      | _ => none
    | none => none

def storePlannerAgrees (e : Explained) : Bool :=
  (bgps e).all fun (i, b) =>
    let gb := GraphBackend.list graph
    let first := match chooseBestTpBackend gb Binding.empty b, firstStep e (b.length + 1) i with
      | some (tp, _), some op => op.label == tpShort tp && op.est == some (estimateTpBackend tp gb Binding.empty)
      | none, none => true
      | _, _ => false
    let rows := traceRows gb b == evalBgpBackend b gb
    let count := (e.ops[i]?.bind (·.actual)) == some (evalBgpBackend b gb).length
    first && rows && count

open L4Factoidal.Planner in
def capabilityAgrees (e : Explained) : Bool :=
  (e.caps.zip (bgps e)).all fun (cp, (_, b)) =>
    if !cp.note.isEmpty then true else
    let req : Requirement := { bgp := b.map tpBnodeToVar, projection := (bgpVars b).eraseDups }
    let cat := capCatalog graph b
    match search cat req b.length with
    | best :: _ =>
      let names := best.rewriting.steps.map (fun a => (cat[a.src]?.map (·.cap.name)).getD "?")
      cp.steps.map (·.source) == names && cp.cost == best.cost && cp.rows == (req.answers graph).length
    | [] => false

def resultsAgree (e : Explained) : Bool :=
  let ds : Dataset := { default := graph, named := [] }
  let env : EvalEnv := { dataset := some ds, base := some foafBase }
  e.rows == (evalSelect env ds e.query).2

def allAgree (name : String) : Bool :=
  match explained (exampleQuery name) with
  | some e => storePlannerAgrees e && capabilityAgrees e && resultsAgree e
  | none => false

#guard graph.length == 40
#guard examples.length == 6
#guard allAgree "BGP join"
#guard allAgree "OPTIONAL"
#guard allAgree "FILTER"
#guard allAgree "UNION"
#guard allAgree "Aggregate"
#guard allAgree "Property path"

#guard (kinds "BGP join").contains "scan" && (kinds "BGP join").contains "probe"
#guard (kinds "OPTIONAL").contains "leftjoin"
#guard (kinds "FILTER").contains "filter"
#guard (kinds "UNION").contains "union"
#guard (kinds "Aggregate").contains "group"
#guard (kinds "Property path").contains "path"

-- The capability planner plans the BGP join example (four patterns, the limit).
#guard match explained (exampleQuery "BGP join") with
  | some e => e.caps.length == 1 && e.caps.all (fun cp => cp.note.isEmpty && cp.steps.length == 4)
  | none => false

-- Results: the BGP join gives the people with a mailbox and each friend's name.
#guard match explained (exampleQuery "BGP join") with
  | some e => e.rows.length == 5
  | none => false
#guard match explained (exampleQuery "FILTER") with
  | some e => e.rows.length == 4
  | none => false

-- A parse error is an error, not a page of nothing.
#guard (explain "SELECT WHERE {" graph).toOption.isNone

-- The address: percent-encoding round trip, and the step parameter.
#guard decode (encode "SELECT ?x WHERE { ?x <a:b> \"é\" }") == "SELECT ?x WHERE { ?x <a:b> \"é\" }"
#guard !(encode "a/b c").contains '/'
#guard param "q=ASK+%7B%7D&step=3" "q" == some "ASK {}" && param "q=ASK+%7B%7D&step=3" "step" == some "3"

-- The page: an SVG plan, the operator table and a marked step.
#guard let (src, _, next) := Id.run <| page ("q=" ++ encode (exampleQuery "OPTIONAL") ++ "&step=2") graph
  (src.splitOn "<svg").length > 2 && (src.splitOn "#ff2a2a").length == 2 && next.endsWith "&step=3"
#guard let (src, _, _) := Id.run <| page "" graph
  (src.splitOn "class=\"bad\"").length == 1 && (src.splitOn "<h2>Result").length == 2

end WebSparqlTests
