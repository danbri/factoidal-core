/-
Capability-aware planner, OKR batch 3, KR 4.4: a WebMCP tool as
capabilities.

https://github.com/danbri/factoidal/issues/875 (epic
https://github.com/danbri/factoidal/issues/800). Design record
`docs/designissues/2026-10-12-capability-aware-planner.md`, section 15.

Source: "WebMCP", Draft Community Group Report, 20 October 2026, W3C Web
Machine Learning Community Group (https://webmachinelearning.github.io/webmcp/).
A page registers a tool with `document.modelContext.registerTool(tool,
options)`. The tool is a `ModelContextTool` dictionary:

    dictionary ModelContextTool {
      required DOMString name;
      USVString title;
      required DOMString description;
      object inputSchema;
      required ToolExecuteCallback execute;
      ToolAnnotations annotations;
    };
    dictionary ToolAnnotations {
      boolean readOnlyHint = false;
      boolean untrustedContentHint = false;
      boolean consequentialHint = false;
      boolean debugging = false;
    };

`execute` returns a promise of any value; the user agent serialises the
value to a JSON string, and `executeTool(tool, inputObject, options)`
resolves to that string. The draft has no output schema.

Description document. A WebIDL dictionary drops members that it does not
define, so the RDF mapping cannot be a member of the tool. The document
gives the tool (every member except `execute`), the origin of the
document that registered it, and the mapping beside them:

    { "origin": "https://shop.example.org",
      "tool": { "name": "lookup_price", "description": "...",
                "inputSchema": { "type": "object",
                                 "properties": { "sku": { "type": "string" } },
                                 "required": [ "sku" ] },
                "annotations": { "readOnlyHint": true } },
      "org.factoidal/rdf": {
        "subject": "sku", "subjectTemplate": "http://example.org/sku/{sku}",
        "predicates": { "price": "http://example.org/price" },
        "objectIri": [], "exactness": "exact",
        "cost": { "perCall": 30, "perRow": 0, "callQuota": 50 } } }

Rules of `readTool`:

* the location is `browser:<origin>`: the call runs in the user agent of
  the page, not at a server;
* the planner calls a source any number of times and in any order, so only
  a tool with `annotations.readOnlyHint = true` and
  `annotations.consequentialHint = false` is a data source; any other tool
  is refused;
* the required properties of `inputSchema` are the required inputs; the
  property `subject` is tuple position 0, an IRI made by
  `subjectTemplate`; each property in `predicates` gives one
  predicate-form capability (arity 2, input `[0]`), the same form as the
  MCP kind;
* a second required input is refused (open, expected-failure case
  `webmcp-two-required-inputs`, https://github.com/danbri/factoidal/issues/801);
* `exactness` is `exact` (default) or `approximate`.

Implementation (`webmcpImpl`): one `executeTool` per call through a
function `origin → tool name → input object → Option String` (the JSON
string the promise resolves to; `none` when it rejects). The string is
parsed by `parseJson`; the mapped properties are read from the top-level
object. In tests the function is a mock; no browser, no network.
-/
import L4Factoidal.Planner.Kinds.JsonTerms

namespace L4Factoidal.Planner.Kinds.WebMcp

open L4Factoidal.RDF L4Factoidal.Planner L4Factoidal.Planner.Kinds L4Factoidal.Planner.Kinds.JsonTerms
open L4Factoidal.JSON

structure Tool where
  origin : String
  name : String
  input : String
  subject : SubjectTemplate
  props : List PropMap
  exactness : Exactness
  cost : CostModel
  deriving Repr

def metaKey : String := "org.factoidal/rdf"

def defaultCost : CostModel := { perCall := 30, perRow := 1 }

def readTool (text : String) : Except String Tool := do
  let doc ← match parseJson text with
    | .ok j => pure j
    | .error e => throw s!"WebMCP tool description: JSON: {e}"
  let some origin := doc.getString? "origin" | throw "WebMCP tool description: no origin"
  let some tool := doc.field? "tool" | throw "WebMCP tool description: no tool"
  let some name := tool.getString? "name" | throw "WebMCP tool: no name"
  if (tool.getString? "description").isNone then throw s!"{name}: no description"
  let ann := tool.field? "annotations"
  let readOnly := (ann.bind (·.getBool? "readOnlyHint")).getD false
  let consequential := (ann.bind (·.getBool? "consequentialHint")).getD false
  if !readOnly then throw s!"{name}: readOnlyHint is not true; only a read-only tool is a data source"
  if consequential then throw s!"{name}: consequentialHint is true; not a data source"
  let required := ((tool.field? "inputSchema").bind (·.getStringArray? "required")).getD []
  let some m := doc.field? metaKey | throw s!"{name}: no {metaKey} mapping"
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
  let ex : Exactness := if m.getString? "exactness" == some "approximate" then .approximate else .exact
  pure { origin := origin, name := name, input := subj, subject := st, props := props,
         exactness := ex, cost := readCost (m.field? "cost") defaultCost }

def describeTool (t : Tool) : List Described :=
  describeCall "webmcp" t.name ("browser:" ++ t.origin) t.props t.cost t.exactness

def describe (text : String) : Except String (List Described) :=
  (readTool text).map describeTool

/-- One `executeTool`: the JSON string the promise resolves to, parsed. -/
def webmcpImpl (exec : String → String → Json → Option String) (t : Tool) (pm : PropMap) :
    InputBinding → List Tuple := fun inp =>
  match inp.lookup 0 with
  | some (.iri i) =>
    match t.subject.slotValue? i with
    | none => []
    | some v =>
      match exec t.origin t.name (.object [(t.input, .string v)]) with
      | none => []
      | some s =>
        match parseJson s with
        | .ok res => tuplesOf (.iri i) pm res
        | .error _ => []
  | _ => []

/-- The source of one described capability of `t`; the declared
extension is the tool's answers at the slot values `ids`, or `declared`
when given (an approximate tool). -/
def webmcpSource (exec : String → String → Json → Option String) (ids : List String) (t : Tool)
    (d : Described) (declared : Option (List Tuple) := none) : Option Source := do
  let pm ← t.props.find? (fun pm => some pm.pred == d.partition)
  let impl := webmcpImpl exec t pm
  let ext := declared.getD (ids.flatMap (fun v => match t.subject.iri? v with
    | some i => impl [(0, .iri i)]
    | none => []))
  pure { cap := d.cap, mapping := d.mapping, sem := { ext := ext, impl := impl } }

end L4Factoidal.Planner.Kinds.WebMcp
