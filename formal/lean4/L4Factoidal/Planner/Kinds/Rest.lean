/-
Capability-aware planner, KR 2.3: a REST API as capabilities.

https://github.com/danbri/factoidal/issues/801. Description document: a
small OpenAPI-like JSON document (the shape of OpenAPI 3.1,
https://spec.openapis.org/oas/v3.1.0, with three extension fields; OpenAPI
permits `x-` fields on an operation and a schema):

    { "servers": [ { "url": BASE } ],
      "paths": { PATH: { "get": {
        "operationId": ID,
        "parameters": [ { "name": N, "in": "path", "required": true } ],
        "x-rdf-subject": "http://example.org/person/{N}",
        "x-cost": { "perCall": 50, "perRow": 1, "callQuota": 1000 },
        "responses": { "200": { "content": { "application/json": { "schema": {
          "type": "object",
          "properties": { KEY: { "type": "string",
                                 "x-rdf-predicate": IRI, "x-rdf-object": "iri" } } } } } } } } } } }

A path parameter is a required input: the one path parameter is tuple
position 0, the subject, read back from the subject IRI through
`x-rdf-subject`. Each response property with `x-rdf-predicate` gives one
predicate-form capability (arity 2, input `[0]`), so a requirement that
names one property does not need the others (record section 9, open
item `wide-relation-unnamed-output`). Location: `BASE PATH`. Cost:
`x-cost`, default 50 per call and 1 per row. Exact.

An operation with more than one path parameter, or a query parameter, is
refused: open, with an expected-failure case naming
https://github.com/danbri/factoidal/issues/801.

Implementation (`restImpl`): one GET per call through an HTTP function
`String → Option String` (URL to response body), the body parsed with the
repository's JSON parser. In tests the function is a mock; no network.
-/
import L4Factoidal.Planner.Kinds.JsonTerms

namespace L4Factoidal.Planner.Kinds.Rest

open L4Factoidal.RDF L4Factoidal.Planner L4Factoidal.Planner.Kinds L4Factoidal.Planner.Kinds.JsonTerms
open L4Factoidal.JSON

/-- One GET operation. -/
structure Op where
  opId : String
  /-- `BASE PATH`, with the `{param}` slot. -/
  urlTemplate : String
  param : String
  subject : SubjectTemplate
  props : List PropMap
  cost : CostModel
  deriving Repr

def defaultCost : CostModel := { perCall := 50, perRow := 1 }

def field (j : Json) (path : List String) : Option Json :=
  path.foldl (fun acc k => acc.bind (·.field? k)) (some j)

def readOp (base path : String) (get : Json) : Except String Op := do
  let opId := (get.getString? "operationId").getD path
  let params := (get.getArray? "parameters").getD []
  let pathParams := params.filter (fun p => p.getString? "in" == some "path")
  let others := params.filter (fun p => p.getString? "in" != some "path")
  if !others.isEmpty then throw s!"{opId}: a query, header or cookie parameter is not read"
  let param ← match pathParams with
    | [p] => match p.getString? "name" with
      | some n => pure n
      | none => throw s!"{opId}: a path parameter has no name"
    | [] => throw s!"{opId}: no path parameter (a call with no required input is not read)"
    | _ => throw s!"{opId}: more than one path parameter"
  let some tmpl := get.getString? "x-rdf-subject" | throw s!"{opId}: no x-rdf-subject"
  let some st := SubjectTemplate.read? tmpl param
    | throw s!"{opId}: x-rdf-subject has no single slot {param}"
  let some schemaProps := field get ["responses", "200", "content", "application/json", "schema", "properties"]
    | throw s!"{opId}: no JSON response schema properties"
  let props ← match schemaProps with
    | .object kvs => pure (kvs.filterMap (fun (k, v) =>
        match (v.getString? "x-rdf-predicate").bind mkWfIri? with
        | some p => some { key := k, pred := p, objectIri := v.getString? "x-rdf-object" == some "iri" }
        | none => none))
    | _ => throw s!"{opId}: the schema properties are not an object"
  pure { opId := opId, urlTemplate := base ++ path, param := param, subject := st, props := props,
         cost := readCost (get.field? "x-cost") defaultCost }

def readOps (text : String) : Except String (List Op) := do
  let doc ← match parseJson text with
    | .ok j => pure j
    | .error e => throw s!"OpenAPI document: JSON: {e}"
  let base := ((doc.getArray? "servers").bind (·.head?) |>.bind (·.getString? "url")).getD ""
  let paths ← match doc.field? "paths" with
    | some (.object kvs) => pure kvs
    | _ => throw "OpenAPI document: no paths object"
  paths.filterMapM (fun (path, item) => match item.field? "get" with
    | some get => (readOp base path get).map some
    | none => pure none)

def describeOp (op : Op) : List Described :=
  describeCall "rest" op.opId op.urlTemplate op.props op.cost .exact

def describe (text : String) : Except String (List Described) :=
  (readOps text).map (·.flatMap describeOp)

/-- The URL of a call. -/
def Op.url (op : Op) (v : String) : String :=
  op.urlTemplate.replace ("{" ++ op.param ++ "}") v

/-- One call: the GET of the subject's resource, the property's values. -/
def restImpl (http : String → Option String) (op : Op) (pm : PropMap) :
    InputBinding → List Tuple := fun inp =>
  match inp.lookup 0 with
  | some (.iri i) =>
    match op.subject.slotValue? i with
    | none => []
    | some v =>
      match http (op.url v) with
      | none => []
      | some body =>
        match parseJson body with
        | .ok resp => tuplesOf (.iri i) pm resp
        | .error _ => []
  | _ => []

/-- The source of one described capability of `op`. The declared
extension is the API's resources at the slot values `ids` (what the
mock serves); the implementation is the GET. -/
def restSource (http : String → Option String) (ids : List String) (op : Op) (d : Described) :
    Option Source := do
  let pm ← op.props.find? (fun pm => some pm.pred == d.partition)
  let impl := restImpl http op pm
  let ext := ids.flatMap (fun v => match op.subject.iri? v with
    | some i => impl [(0, .iri i)]
    | none => [])
  pure { cap := d.cap, mapping := d.mapping, sem := { ext := ext, impl := impl } }

end L4Factoidal.Planner.Kinds.Rest
