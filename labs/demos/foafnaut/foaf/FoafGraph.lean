import L4Factoidal.Syntax.Turtle
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

/-! A small view of one RDF document for the native FOAF graph renderer.
No RDF inference, network loading, blank-node canonicalization, or layout.
Identity stays in Factoidal's Subject type; display labels never identify nodes. -/
namespace FoafGraph
open L4Factoidal.RDF L4Factoidal.Syntax

def foaf := "http://xmlns.com/foaf/0.1/"
def rdfType := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"
def rdfsLabel := "http://www.w3.org/2000/01/rdf-schema#label"

structure Person where
  subject : Subject
  id : String
  label : String
  labelIsFallback : Bool
  deriving DecidableEq, Repr

structure Link where
  source : Nat
  target : Nat
  deriving DecidableEq, Repr

structure Data where
  people : Array Person
  links : Array Link
  /-- Distinct invalid knows triples, including literal objects. -/
  ignoredKnows : Nat
  deriving DecidableEq, Repr

structure Limits where
  maxChars : Nat := 65536
  maxPeople : Nat := 256
  maxLinks : Nat := 1024
  maxStringChars : Nat := 4096
  maxJsonChars : Nat := 2097152
  deriving Repr

/-- Collision-free within one document: constructor prefix + exact RDF value.
Blank-node labels are document-scoped, and must not be merged across documents. -/
def subjectId : Subject → String
  | .iri i => "iri:" ++ i.val
  | .bnode b => "bnode:" ++ b

def fallbackLabel : Subject → String
  | .iri i => i.val
  | .bnode b => "_:" ++ b

private def addSubject (xs : List Subject) (s : Subject) : List Subject :=
  if xs.any (·.eqb s) then xs else s :: xs

private def isPerson (t : Triple) : Bool :=
  t.p.val == rdfType && match t.o with
    | .iri i => i.val == foaf ++ "Person"
    | _ => false

private def labelFor (g : Graph) (s : Subject) : String × Bool := Id.run do
  for predicate in [foaf ++ "name", rdfsLabel] do
    let names := g.filterMap fun t =>
      if t.s.eqb s && t.p.val == predicate then
        match t.o with | .literal l => some l.val.lexicalForm | _ => none
      else none
    match names.mergeSort (· <= ·) with
    | first :: _ => return (first,false)
    | [] => pure ()
  return (fallbackLabel s,true)

/-- Exact asserted foaf:Person subjects plus both resource ends of asserted
foaf:knows links. Links are directed; self links remain. Repeated RDF triples
or links have no extra visual weight. No domain/range/RDFS/OWL inference.
The order depends on RDF identity, never parser triple order or label text. -/
def fromGraph (g : Graph) (limits : Limits := {}) : Except String Data := Id.run do
  let mut subjects : List Subject := []
  let mut pairs : List (Subject × Subject) := []
  let mut invalid : List Triple := []
  for t in g do
    if isPerson t then subjects := addSubject subjects t.s
    if t.p.val == foaf ++ "knows" then
      match t.o.toSubject? with
      | some target =>
        subjects := addSubject (addSubject subjects t.s) target
        let pair := (t.s,target)
        if !pairs.contains pair then pairs := pair :: pairs
      | none =>
        if !invalid.any (·.eqb t) then invalid := t :: invalid
  if subjects.length > limits.maxPeople then return .error "FOAF graph exceeds person limit"
  if pairs.length > limits.maxLinks then return .error "FOAF graph exceeds link limit"
  let ordered := subjects.mergeSort fun a b => subjectId a <= subjectId b
  let people := ordered.toArray.map fun s =>
    let (label,labelIsFallback) := labelFor g s
    {subject:=s,id:=subjectId s,label,labelIsFallback : Person}
  if people.any (fun p => p.id.length > limits.maxStringChars || p.label.length > limits.maxStringChars) then
    return .error "FOAF identity or label exceeds string limit"
  let mut links : List Link := []
  for (source,target) in pairs do
    -- Both endpoints were inserted above. Use checked lookup, never a fallback index.
    match ordered.idxOf? source, ordered.idxOf? target with
    | some a, some b => links := {source:=a,target:=b} :: links
    | _, _ => return .error "FOAF endpoint missing from person table"
  let sortedLinks := links.mergeSort fun a b =>
    a.source < b.source || (a.source == b.source && a.target <= b.target)
  return .ok {people,links:=sortedLinks.toArray,ignoredKnows:=invalid.length}

/-- Real Factoidal Turtle 1.1 parsing, including retrieval-base resolution.
Character limit applies before parsing; person/link limits apply after parsing.
This is not a bound on parser work, DOM depth, or arbitrary fromGraph input. -/
def fromTurtle (text : String) (base : Option String := none)
    (limits : Limits := {}) : Except String Data := do
  if text.length > limits.maxChars then throw "FOAF Turtle exceeds character limit"
  let graph ← (parseTurtle text base .rdf11).mapError toString
  fromGraph graph limits

open L4Factoidal.JSON

/-- JSON transport contains exact RDF constructor/value, derived id, and label.
Use Factoidal JSON.toStringCompact/parseJson when embedding in a UI model. -/
def Data.toJson (g : Data) : Json := .object [
  ("people", .array (g.people.toList.map fun p =>
    let (kind,value) := match p.subject with
      | .iri i => ("iri",i.val) | .bnode b => ("bnode",b)
    .object [("kind",.string kind),("value",.string value),
      ("id",.string p.id),("label",.string p.label),("labelIsFallback",.bool p.labelIsFallback)])),
  ("links", .array (g.links.toList.map fun l =>
    .object [("source",.number (toString l.source)),("target",.number (toString l.target))])),
  ("ignoredKnows", .number (toString g.ignoredKnows))]

private def fields (j : Json) (expected : List String) : Except String (List (String × Json)) :=
  match j with
  | .object fs =>
    if fs.length == expected.length && expected.all (fun k => (fs.filter (·.1 == k)).length == 1)
    then .ok fs else .error "FOAF JSON unexpected, missing, or repeated field"
  | _ => .error "FOAF JSON expected object"
private def field (fs : List (String × Json)) (name : String) : Except String Json :=
  match fs.lookup name with | some j => .ok j | none => .error "FOAF JSON missing field"
private def string (j : Json) : Except String String :=
  match j with | .string s => .ok s | _ => .error "FOAF JSON expected string"
private def items (j : Json) : Except String (List Json) :=
  match j with | .array xs => .ok xs | _ => .error "FOAF JSON expected array"
private def boolean (j : Json) : Except String Bool :=
  match j with | .bool b => .ok b | _ => .error "FOAF JSON expected boolean"
private def natural (j : Json) : Except String Nat :=
  match j with
  | .number s =>
    if s.length > 10 || !s.toList.all Char.isDigit then .error "FOAF JSON expected bounded natural"
    else match s.toNat? with | some n => .ok n | none => .error "FOAF JSON expected natural"
  | _ => .error "FOAF JSON expected number"

/-- Validate the round-tripped model: exact schema, unique RDF identities and
directed links, matching derived IDs, and in-range endpoints. This checks the
existing Core.isIri gate, not full IRI syntax or Turtle provenance. -/
def Data.fromJson (j : Json) (limits : Limits := {}) : Except String Data := do
  let fs ← fields j ["people","links","ignoredKnows"]
  let ps ← items (← field fs "people")
  let ls ← items (← field fs "links")
  if ps.length > limits.maxPeople || ls.length > limits.maxLinks then
    throw "FOAF JSON exceeds graph limits"
  let mut people : Array Person := #[]
  for p in ps do
    let f ← fields p ["kind","value","id","label","labelIsFallback"]
    let kind ← string (← field f "kind")
    let value ← string (← field f "value")
    let id ← string (← field f "id")
    let label ← string (← field f "label")
    let labelIsFallback ← boolean (← field f "labelIsFallback")
    if id.length > limits.maxStringChars || value.length > limits.maxStringChars || label.length > limits.maxStringChars then
      throw "FOAF JSON exceeds string limit"
    let subject ← if kind == "iri" then
      if h : isIri value then pure (Subject.iri ⟨value,h⟩) else throw "FOAF JSON invalid IRI identity"
      else if kind == "bnode" && !value.isEmpty then pure (Subject.bnode value)
      else throw "FOAF JSON invalid subject kind or blank identity"
    if id != subjectId subject then throw "FOAF JSON inconsistent identity"
    if labelIsFallback && label != fallbackLabel subject then throw "FOAF JSON inconsistent fallback label"
    if people.any (·.subject.eqb subject) then throw "FOAF JSON repeated identity"
    people := people.push {subject,id,label,labelIsFallback}
  let mut links : Array Link := #[]
  for l in ls do
    let f ← fields l ["source","target"]
    let source ← natural (← field f "source")
    let target ← natural (← field f "target")
    if source >= people.size || target >= people.size then throw "FOAF JSON endpoint out of range"
    let link := {source,target : Link}
    if links.contains link then throw "FOAF JSON repeated link"
    links := links.push link
  let ignoredKnows ← natural (← field fs "ignoredKnows")
  return {people,links,ignoredKnows}

def Data.encode (g : Data) : String := toStringCompact g.toJson
def Data.decode (text : String) (limits : Limits := {}) : Except String Data := do
  if text.length > limits.maxJsonChars then throw "FOAF JSON exceeds character limit"
  let json ← (parseJson text).mapError (fun _ => "FOAF JSON syntax error")
  Data.fromJson json limits

end FoafGraph
