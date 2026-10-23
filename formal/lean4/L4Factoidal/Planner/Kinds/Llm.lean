/-
Capability-aware planner, OKR batch 3, KR 4.4: an operation answered by a
large language model, as capabilities with explicit approximation.

https://github.com/danbri/factoidal/issues/875 (epic
https://github.com/danbri/factoidal/issues/800). Design record
`docs/designissues/2026-10-12-capability-aware-planner.md`, section 15.

Description document: a JSON object that names the model, the prompt
template, the mapping of the model's JSON answer to triples, the cost and
latency, and an optional confidence:

    { "name": "estimate_population",
      "model": "example-model-1",
      "endpoint": "https://llm.example.org/v1",
      "prompt": "Population of the city {city}. Answer as JSON: {\"population\": <integer>}",
      "subject": "city",
      "subjectTemplate": "http://example.org/{city}",
      "predicates": { "population": "http://example.org/population" },
      "objectIri": [],
      "cost": { "perCall": 2000, "perRow": 0, "callQuota": 10, "latencyMs": 1500 },
      "confidence": 0.8 }

Rules of `readOp`:

* the exactness is always `approximate`: a model's answer is not the
  value of a declared extension. A document that states
  `"exactness": "exact"` is refused;
* the cost is `CostModel` with `latency` (milliseconds per call,
  `cost.latencyMs`); defaults: 1000 per call, 0 per row;
* `confidence`, when given, is a JSON number from 0 to 1 with at most
  three fraction digits; it is kept in thousandths
  (`Capability.confidence`). It does not change the marker of a row;
* the prompt has exactly one slot `{subject}`; the subject IRI's slot
  value (read back by `subjectTemplate`) is put in it;
* each property in `predicates` gives one predicate-form capability
  (arity 2, input `[0]`), the same form as the MCP kind;
* the location is `llm:<endpoint>`, or `llm:<model>` with no endpoint.

Implementation (`llmImpl`): one completion per call through a function
`model → prompt → Option String` (the completion text; `none` on an
error). The text is parsed by `parseJson`; a completion that is not a
JSON object gives no tuple. In tests the function is a mock; no network.
-/
import L4Factoidal.Planner.Kinds.JsonTerms

namespace L4Factoidal.Planner.Kinds.Llm

open L4Factoidal.RDF L4Factoidal.Planner L4Factoidal.Planner.Kinds L4Factoidal.Planner.Kinds.JsonTerms
open L4Factoidal.JSON

structure Op where
  name : String
  model : String
  location : String
  /-- The prompt text before and after the slot. -/
  promptBefore : String
  promptAfter : String
  subject : SubjectTemplate
  props : List PropMap
  cost : CostModel
  confidence : Option Nat
  deriving Repr

def defaultCost : CostModel := { perCall := 1000, perRow := 0 }

/-- A JSON number lexeme from 0 to 1 with at most three fraction digits,
in thousandths. -/
def thousandths? (lex : String) : Option Nat :=
  match lex.splitOn "." with
  | [w] => if w == "0" then some 0 else if w == "1" then some 1000 else none
  | [w, f] =>
    if f.isEmpty || f.length > 3 || !f.all Char.isDigit then none else
    let frac := (f ++ "".pushn '0' (3 - f.length)).toNat!
    if w == "0" then some frac
    else if w == "1" && frac == 0 then some 1000
    else none
  | _ => none

def readOp (text : String) : Except String Op := do
  let doc ← match parseJson text with
    | .ok j => pure j
    | .error e => throw s!"LLM operation: JSON: {e}"
  let some name := doc.getString? "name" | throw "LLM operation: no name"
  let some model := doc.getString? "model" | throw s!"{name}: no model"
  if doc.getString? "exactness" == some "exact" then
    throw s!"{name}: a model's answer is approximate; exactness exact is refused"
  let some subj := doc.getString? "subject" | throw s!"{name}: no subject property"
  let some tmpl := doc.getString? "subjectTemplate" | throw s!"{name}: no subjectTemplate"
  let some st := SubjectTemplate.read? tmpl subj
    | throw s!"{name}: subjectTemplate has no single slot {subj}"
  let some prompt := doc.getString? "prompt" | throw s!"{name}: no prompt"
  let (pb, pa) ← match prompt.splitOn ("{" ++ subj ++ "}") with
    | [b, a] => pure (b, a)
    | _ => throw s!"{name}: the prompt has no single slot {subj}"
  let some preds := doc.field? "predicates" | throw s!"{name}: no predicates"
  let props ← readPropMaps preds ((doc.getStringArray? "objectIri").getD [])
  let conf ← match doc.field? "confidence" with
    | none => pure none
    | some (.number n) => match thousandths? n with
      | some c => pure (some c)
      | none => throw s!"{name}: confidence {n} is not a number from 0 to 1 with at most 3 fraction digits"
    | some _ => throw s!"{name}: confidence is not a number"
  let loc := match doc.getString? "endpoint" with
    | some e => "llm:" ++ e
    | none => "llm:" ++ model
  pure { name := name, model := model, location := loc, promptBefore := pb, promptAfter := pa,
         subject := st, props := props, cost := readCost (doc.field? "cost") defaultCost,
         confidence := conf }

def describeOp (o : Op) : List Described :=
  (describeCall "llm" o.name o.location o.props o.cost .approximate).map
    (fun d => { d with cap := { d.cap with confidence := o.confidence } })

def describe (text : String) : Except String (List Described) :=
  (readOp text).map describeOp

/-- The prompt of one call. -/
def Op.prompt (o : Op) (v : String) : String := o.promptBefore ++ v ++ o.promptAfter

/-- One completion: the text parsed as a JSON object. -/
def llmImpl (complete : String → String → Option String) (o : Op) (pm : PropMap) :
    InputBinding → List Tuple := fun inp =>
  match inp.lookup 0 with
  | some (.iri i) =>
    match o.subject.slotValue? i with
    | none => []
    | some v =>
      match complete o.model (o.prompt v) with
      | none => []
      | some text =>
        match parseJson text with
        | .ok res@(.object _) => tuplesOf (.iri i) pm res
        | _ => []
  | _ => []

/-- The source of one described capability of `o`, with the declared
extension `declared` (the model's answers are not the declared ones). -/
def llmSource (complete : String → String → Option String) (o : Op) (d : Described)
    (declared : List Tuple) : Option Source := do
  let pm ← o.props.find? (fun pm => some pm.pred == d.partition)
  pure { cap := d.cap, mapping := d.mapping, sem := { ext := declared, impl := llmImpl complete o pm } }

end L4Factoidal.Planner.Kinds.Llm
