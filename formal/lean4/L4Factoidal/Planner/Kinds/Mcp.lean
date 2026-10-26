/-
Capability-aware planner, KR 2.3: an MCP tool as capabilities.

https://github.com/danbri/factoidal/issues/801. Description document: an
MCP tool declaration, as a server lists it in `tools/list` (Model Context
Protocol specification 2025-06-18, "Tools": `name`, `title`,
`description`, `inputSchema` and `outputSchema` as JSON Schema objects,
`annotations`, `_meta`):

    { "name": "get_weather",
      "description": "...",
      "inputSchema": { "type": "object",
                       "properties": { "city": { "type": "string" } },
                       "required": [ "city" ] },
      "outputSchema": { "type": "object",
                        "properties": { "temperature": { "type": "number" } } },
      "_meta": { "org.factoidal/rdf": {
        "subject": "city",
        "subjectTemplate": "http://example.org/city/{city}",
        "predicates": { "temperature": "http://example.org/temperature" },
        "objectIri": [],
        "exactness": "exact",
        "cost": { "perCall": 100, "perRow": 0, "callQuota": 60 } } } }

The required properties of `inputSchema` are the required inputs. The
mapping to triples is in `_meta` under `org.factoidal/rdf` (MCP reserves
`_meta` for such extension data): the required property `subject` is
tuple position 0, an IRI made by `subjectTemplate`; each property in
`predicates` gives one predicate-form capability (arity 2, input `[0]`).
`exactness` is `exact` (default) or `approximate` (a tool whose answer is
made by a model: its rows carry the marker). Location `mcp:<name>`.

A tool with a required input that the mapping does not place (a second
required property) is refused: open, with an expected-failure case
naming https://github.com/danbri/factoidal/issues/801.

Implementation (`mcpImpl`): one `tools/call` per call through a function
`String → Json → Option Json` (tool name and `arguments` to the
`CallToolResult`); the values come from `structuredContent`; a result
with `isError: true` gives no tuple. In tests the function is a mock; no
network. WebMCP tools are open, with an expected-failure case.
-/
import L4Factoidal.Planner.Kinds.JsonTerms

namespace L4Factoidal.Planner.Kinds.Mcp

open L4Factoidal.RDF L4Factoidal.Planner L4Factoidal.Planner.Kinds L4Factoidal.Planner.Kinds.JsonTerms
open L4Factoidal.JSON

structure Tool where
  name : String
  input : String
  subject : SubjectTemplate
  props : List PropMap
  exactness : Exactness
  cost : CostModel
  deriving Repr

def metaKey : String := "org.factoidal/rdf"

def defaultCost : CostModel := { perCall := 100, perRow := 1 }

def readTool (text : String) : Except String Tool := do
  let decl ← match parseJson text with
    | .ok j => pure j
    | .error e => throw s!"MCP tool declaration: JSON: {e}"
  let some name := decl.getString? "name" | throw "MCP tool declaration: no name"
  let some schema := decl.field? "inputSchema" | throw s!"{name}: no inputSchema"
  let required := (schema.getStringArray? "required").getD []
  let some m := (decl.field? "_meta").bind (·.field? metaKey)
    | throw s!"{name}: no _meta.{metaKey} mapping"
  let some subj := m.getString? "subject" | throw s!"{name}: the mapping names no subject property"
  if !required.contains subj then throw s!"{name}: the subject property {subj} is not a required input"
  match required.filter (· != subj) with
  | [] => pure ()
  | r :: _ => throw s!"{name}: required input {r} has no position in the mapping"
  let some tmpl := m.getString? "subjectTemplate" | throw s!"{name}: no subjectTemplate"
  let some st := SubjectTemplate.read? tmpl subj
    | throw s!"{name}: subjectTemplate has no single slot {subj}"
  let some preds := m.field? "predicates" | throw s!"{name}: no predicates"
  let props ← readPropMaps preds ((m.getStringArray? "objectIri").getD [])
  -- each mapped property must be an output property, when an output schema is given
  match (decl.field? "outputSchema").bind (·.field? "properties") with
  | some outProps =>
    for pm in props do
      if (outProps.field? pm.key).isNone then
        throw s!"{name}: mapped property {pm.key} is not in outputSchema"
  | none => pure ()
  let ex : Exactness := if m.getString? "exactness" == some "approximate" then .approximate else .exact
  pure { name := name, input := subj, subject := st, props := props, exactness := ex,
         cost := readCost (m.field? "cost") defaultCost }

def describeTool (t : Tool) : List Described :=
  describeCall "mcp" t.name ("mcp:" ++ t.name) t.props t.cost t.exactness

def describe (text : String) : Except String (List Described) :=
  (readTool text).map describeTool

/-- One `tools/call`. -/
def mcpImpl (call : String → Json → Option Json) (t : Tool) (pm : PropMap) :
    InputBinding → List Tuple := fun inp =>
  match inp.lookup 0 with
  | some (.iri i) =>
    match t.subject.slotValue? i with
    | none => []
    | some v =>
      match call t.name (.object [(t.input, .string v)]) with
      | none => []
      | some res =>
        if res.getBool? "isError" == some true then [] else
        match res.field? "structuredContent" with
        | some sc => tuplesOf (.iri i) pm sc
        | none => []
  | _ => []

/-- The source of one described capability of `t`; the declared
extension is the tool's answers at the slot values `ids`. For an
approximate tool, pass the declared extension in `declared`
(the implementation's answers are not the declared ones). -/
def mcpSource (call : String → Json → Option Json) (ids : List String) (t : Tool) (d : Described)
    (declared : Option (List Tuple) := none) : Option Source := do
  let pm ← t.props.find? (fun pm => some pm.pred == d.partition)
  let impl := mcpImpl call t pm
  let ext := declared.getD (ids.flatMap (fun v => match t.subject.iri? v with
    | some i => impl [(0, .iri i)]
    | none => []))
  pure { cap := d.cap, mapping := d.mapping, sem := { ext := ext, impl := impl } }

end L4Factoidal.Planner.Kinds.Mcp
