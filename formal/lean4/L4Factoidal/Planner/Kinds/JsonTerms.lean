/-
Capability-aware planner, KR 2.3: JSON values as RDF terms, and the
response-property mapping shared by the REST and MCP source kinds.

https://github.com/danbri/factoidal/issues/801. A JSON response value
gives RDF terms (one per scalar; an array gives one per scalar element):

* a string: an `xsd:string` literal, or an IRI when the mapping says the
  property's object is an IRI;
* a number: `xsd:integer` when the lexeme has no `.`, `e` or `E`,
  `xsd:decimal` when it has a `.` and no exponent, else `xsd:double`; the
  lexeme is kept (RFC 8259 section 6);
* `true` / `false`: `xsd:boolean`;
* `null`, objects: no term.

The subject of a response is the required input, an IRI made from a
template with one `{name}` slot; `slotValue?` reads the slot value back
from an input IRI.
-/
import L4Factoidal.Planner.Kinds.Common
import L4Factoidal.JSON.Parser

namespace L4Factoidal.Planner.Kinds.JsonTerms

open L4Factoidal.RDF L4Factoidal.Planner L4Factoidal.Planner.Kinds
open L4Factoidal.JSON

def typedLit? (lex : String) (dt : WfIri) : Option Term :=
  let l : Literal := { lexicalForm := lex, datatype := dt, langTag := none, direction := none }
  if h : literalWf l = true then some (.literal ⟨l, h⟩) else none

def numberTerm? (lex : String) : Option Term :=
  if lex.contains 'e' || lex.contains 'E' then typedLit? lex xsdDouble
  else if lex.contains '.' then typedLit? lex xsdDecimal
  else typedLit? lex xsdInteger

def scalarTerm? (asIri : Bool) : Json → Option Term
  | .string s => if asIri then (mkWfIri? s).map Term.iri else some (.literal (Literal.string s))
  | .number n => numberTerm? n
  | .bool b => typedLit? (if b then "true" else "false") xsdBoolean
  | _ => none

/-- The terms of a response value. -/
def termsOf (asIri : Bool) : Json → List Term
  | .array items => items.filterMap (scalarTerm? asIri)
  | v => (scalarTerm? asIri v).toList

/-- A response property mapped to a predicate. -/
structure PropMap where
  key : String
  pred : WfIri
  objectIri : Bool
  deriving Repr

/-- A subject template: the text before and after the `{name}` slot. -/
structure SubjectTemplate where
  name : String
  before : String
  after : String
  deriving Repr

def SubjectTemplate.read? (template name : String) : Option SubjectTemplate :=
  match template.splitOn ("{" ++ name ++ "}") with
  | [b, a] => some { name := name, before := b, after := a }
  | _ => none

def SubjectTemplate.iri? (t : SubjectTemplate) (v : String) : Option WfIri :=
  mkWfIri? (t.before ++ v ++ t.after)

/-- The slot value of an input IRI; `none` when the IRI does not match
the template or the value is empty or holds `/`, `?` or `#`. -/
def SubjectTemplate.slotValue? (t : SubjectTemplate) (i : WfIri) : Option String :=
  let s := i.val
  if s.startsWith t.before && s.endsWith t.after && s.length ≥ t.before.length + t.after.length then
    let v := ((s.drop t.before.length).toString.dropEnd t.after.length).toString
    if v.isEmpty || v.contains '/' || v.contains '?' || v.contains '#' then none else some v
  else none

/-- Read the mapped properties of an object `{ key: IRI }` and the list
of keys whose object is an IRI. -/
def readPropMaps (preds : Json) (iriKeys : List String) : Except String (List PropMap) :=
  match preds with
  | .object kvs => kvs.mapM (fun (k, v) => match v.asString?.bind mkWfIri? with
      | some p => .ok { key := k, pred := p, objectIri := iriKeys.contains k }
      | none => .error s!"property {k}: the predicate is not an IRI")
  | _ => .error "the property map is not an object"

def natField? (j : Json) (k : String) : Option Nat :=
  match j.field? k with
  | some (.number n) => n.toNat?
  | _ => none

/-- A cost model from an object `{ perCall, perRow, callQuota, latencyMs }`. -/
def readCost (j : Option Json) (dflt : CostModel) : CostModel :=
  match j with
  | none => dflt
  | some c => { perCall := (natField? c "perCall").getD dflt.perCall,
                perRow := (natField? c "perRow").getD dflt.perRow,
                callQuota := (natField? c "callQuota").orElse (fun _ => dflt.callQuota),
                latency := (natField? c "latencyMs").orElse (fun _ => dflt.latency) }

/-- The capabilities of one call that returns an object: one predicate
form per mapped property, the subject (tuple position 0) required. -/
def describeCall (kind name location : String) (props : List PropMap) (cost : CostModel)
    (ex : Exactness) : List Described :=
  props.map (fun pm =>
    { kind := kind, partition := some pm.pred, mapping := graphMapping (some pm.pred),
      cap := { name := s!"{kind}:{name}.{pm.key}", arity := 2, inputs := [0], location := location,
               cost := cost, exactness := ex } })

/-- The tuples of one call: the response object `resp`, the property
`pm`, the subject `subj`. -/
def tuplesOf (subj : Term) (pm : PropMap) (resp : Json) : List Tuple :=
  match resp.field? pm.key with
  | some v => (termsOf pm.objectIri v).map (fun o => [subj, o])
  | none => []

end L4Factoidal.Planner.Kinds.JsonTerms
