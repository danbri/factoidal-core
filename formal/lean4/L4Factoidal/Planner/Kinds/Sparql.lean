/-
Capability-aware planner, KR 2.3: a SPARQL endpoint, reached through
SERVICE, as capabilities.

https://github.com/danbri/factoidal/issues/801. Description document: a
SPARQL 1.1 Service Description (https://www.w3.org/TR/sparql11-service-description/)
in Turtle, parsed with the repository's Turtle parser (`parseTurtle`).
`readDescription` reads, for the one `sd:Service` subject:

* `sd:endpoint` (section 3.2.1): the location; required;
* `sd:supportedLanguage` (3.2.3): `sd:SPARQL11Query` or `sd:SPARQL10Query`
  is required;
* `sd:resultFormat` (3.2.5): at least one of SPARQL Results JSON, XML,
  CSV or TSV is required;
* `sd:feature` (3.2.2): kept in the record (not used by the planner);
* `sd:defaultDataset` / `sd:defaultGraph` (3.2.6, 3.3.2) and, on the
  default graph, the VoID statistics `void:triples` and
  `void:propertyPartition` (`void:property`, `void:triples`;
  https://www.w3.org/TR/void/ section 4.6). A VoID property partition is
  the source of the predicate form.

Capabilities: one triple-form scan (`sparql:triples`, no input), and for
each property partition `p` the predicate form with no input, with `S`
and with `O` as input (a bound join: one query per input row). Cost
model: `perCall` 200 (a request); `perRow` 1. Exact.

Implementation (`serviceImpl`): for each call, a SPARQL query text
`SELECT ... WHERE { SERVICE <endpoint> { s p o } }` with the inputs put in
as N-Triples terms, parsed by `parseSparql` and evaluated by the
reference evaluator (`evalSelect`) with `EvalEnv.services` mapping the
endpoint to a graph. In tests that map is the mock endpoint; no network.
The live HTTP path (`SPARQL/ProtocolClient.lean`) is not used here: open,
with an expected-failure case naming
https://github.com/danbri/factoidal/issues/801.
-/
import L4Factoidal.Planner.Kinds.Common
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.NTriples
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.ServiceDescription

namespace L4Factoidal.Planner.Kinds.Sparql

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner L4Factoidal.Planner.Kinds
open L4Factoidal.SPARQL.ServiceDescription
open L4Factoidal.Syntax

def voidNs : String := "http://rdfs.org/ns/void#"
def voidTriples : WfIri := ⟨voidNs ++ "triples", rfl⟩
def voidPropertyPartition : WfIri := ⟨voidNs ++ "propertyPartition", rfl⟩
def voidProperty : WfIri := ⟨voidNs ++ "property", rfl⟩
def rdfTypeIri : WfIri := ⟨"http://www.w3.org/1999/02/22-rdf-syntax-ns#type", rfl⟩

/-- The objects of `(s, p, ?)` in `g`. -/
def objects (g : Graph) (s : Subject) (p : WfIri) : List Term :=
  (g.filter (fun t => t.s == s && t.p == p)).map (·.o)

def iriObjects (g : Graph) (s : Subject) (p : WfIri) : List WfIri :=
  (objects g s p).filterMap (fun t => match t with | .iri i => some i | _ => none)

def natObject? (g : Graph) (s : Subject) (p : WfIri) : Option Nat :=
  (objects g s p).findSome? (fun t => match t with
    | .literal l => l.val.lexicalForm.toNat?
    | _ => none)

/-- What the planner reads from a service description. -/
structure Endpoint where
  endpoint : WfIri
  languages : List WfIri
  resultFormats : List WfIri
  features : List WfIri
  /-- `void:triples` of the default graph. -/
  triples : Option Nat
  /-- `void:propertyPartition`s of the default graph. -/
  partitions : List (WfIri × Option Nat)
  deriving Repr

def readableFormats : List WfIri :=
  [fmtSparqlResultsJson, fmtSparqlResultsXml, fmtSparqlResultsCsv, fmtSparqlResultsTsv]

def readDescription (text : String) (base : Option String := none) : Except String Endpoint := do
  let g ← match parseTurtle text base with
    | .ok g => pure g
    | .error e => throw s!"service description: Turtle: {repr e}"
  let services := ((g.filter (fun t => t.p == rdfTypeIri && t.o == .iri sdService)).map (·.s)).eraseDups
  let svc ← match services with
    | [s] => pure s
    | [] => throw "service description: no sd:Service"
    | _ => throw "service description: more than one sd:Service"
  let ep ← match iriObjects g svc sdEndpoint with
    | e :: _ => pure e
    | [] => throw "service description: no sd:endpoint"
  let langs := iriObjects g svc sdSupportedLanguage
  if !(langs.contains sdSPARQL11Query || langs.contains sdSPARQL10Query) then
    throw "service description: no SPARQL query language (sd:supportedLanguage)"
  let fmts := iriObjects g svc sdResultFormat
  if !fmts.any (readableFormats.contains ·) then
    throw "service description: no SPARQL results format the client reads (sd:resultFormat)"
  let feats := iriObjects g svc sdFeature
  let graphNodes := ((objects g svc sdDefaultDataset).filterMap Term.toSubject?).flatMap
    (fun ds => (objects g ds sdDefaultGraph).filterMap Term.toSubject?)
  let triples := graphNodes.findSome? (fun gn => natObject? g gn voidTriples)
  let parts := graphNodes.flatMap (fun gn =>
    ((objects g gn voidPropertyPartition).filterMap Term.toSubject?).filterMap (fun pn =>
      match iriObjects g pn voidProperty with
      | p :: _ => some (p, natObject? g pn voidTriples)
      | [] => none))
  pure { endpoint := ep, languages := langs, resultFormats := fmts, features := feats,
         triples := triples, partitions := parts }

def requestCost : CostModel := { perCall := 200, perRow := 1 }

def describeEndpoint (e : Endpoint) : List Described :=
  let loc := e.endpoint.val
  let scan : Described :=
    { kind := "sparql", partition := none, mapping := graphMapping none,
      cap := { name := "sparql:triples", arity := 3, inputs := [], location := loc,
               cost := requestCost, exactness := .exact } }
  let byPred := e.partitions.flatMap (fun (p, _) =>
    [([], "scan"), ([0], "s"), ([1], "o")].map (fun (ins, nm) =>
      { kind := "sparql", partition := some p, mapping := graphMapping (some p),
        cap := { name := s!"sparql:{localName p}/{nm}", arity := 2, inputs := ins, location := loc,
                 cost := requestCost, exactness := .exact } : Described }))
  scan :: byPred

def describe (text : String) (base : Option String := none) : Except String (List Described) :=
  (readDescription text base).map describeEndpoint

/-! ## The SERVICE call -/

/-- The text of a term in a query pattern; `none` for a blank node (a
blank node in a query pattern is a variable, so a blank-node input
cannot be sent) and for a triple term. -/
def termText? (t : Term) : Option String :=
  match t with
  | .bnode _ => none
  | .tripleTerm _ _ _ => none
  | _ => match Term.toNTriples .rdf11 t with
    | .ok s => some s
    | .error _ => none

def posVar (i : Nat) : String := s!"v{i}"

/-- The triple positions of each tuple position: S, P, O for the triple
form; S, O for the predicate form. -/
def slotText? (inp : InputBinding) (tp : Nat) : Option String :=
  match inp.lookup tp with
  | some t => termText? t
  | none => some ("?" ++ posVar tp)

/-- The query sent for one call, and the tuple positions it selects. -/
def callQuery? (endpoint : WfIri) (part : Option WfIri) (inp : InputBinding) :
    Option (String × List Nat) := do
  let arity := graphArity part
  let outs := (List.range arity).filter (fun i => (inp.lookup i).isNone)
  let s ← slotText? inp 0
  let (p, o) ← match part with
    | none => do pure (← slotText? inp 1, ← slotText? inp 2)
    | some pi => do pure ("<" ++ pi.val ++ ">", ← slotText? inp 1)
  let sel := if outs.isEmpty then "*" else " ".intercalate (outs.map (fun i => "?" ++ posVar i))
  pure (s!"SELECT {sel} WHERE \{ SERVICE <{endpoint.val}> \{ {s} {p} {o} } }", outs)

def tupleOfRow (arity : Nat) (inp : InputBinding) (row : Binding) : Option Tuple :=
  (List.range arity).mapM (fun i =>
    match inp.lookup i with
    | some t => some t
    | none => row.lookup (posVar i))

/-- One call through SERVICE, evaluated with `services` as the endpoint
map (the mock endpoint in tests). -/
def serviceImpl (services : List (Iri × Graph)) (endpoint : WfIri) (part : Option WfIri) :
    InputBinding → List Tuple := fun inp =>
  match callQuery? endpoint part inp with
  | none => []
  | some (text, _) =>
    match parseSparql text with
    | .error _ => []
    | .ok q =>
      let (_, rows) := evalSelect { services := services } Dataset.empty q
      rows.filterMap (tupleOfRow (graphArity part) inp)

/-- The source of one described capability: the declared extension is
the endpoint's default graph (`graphExt`), the implementation is the
SERVICE call. -/
def serviceSource (services : List (Iri × Graph)) (endpoint : WfIri) (graph : Graph)
    (d : Described) : Source where
  cap := d.cap
  mapping := graphMapping d.partition
  sem := { ext := graphExt d.partition graph, impl := serviceImpl services endpoint d.partition }

end L4Factoidal.Planner.Kinds.Sparql
