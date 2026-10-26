/-
L4Factoidal.Dataflow.NodeSettings — the settings of a node: what each one
does to its stage's contract, the output wire they select, and their
canonical form for the evidence record
(https://github.com/danbri/factoidal/issues/975,
https://github.com/danbri/factoidal/issues/1026).

A node is a registry stage plus its settings: the inputs it takes when it is
made, not values on a wire (`Entry.params`): a reader's base IRI and syntax
name, an evaluator's query text and entailment regime, a CSVW conversion's
metadata. Design record:
`docs/designissues/2026-10-25-pipeline-settings-and-provenance.md`.

## The output wire of an evaluator node (issue 1026)

The registry gives `shippedEvaluator` the output wire `answer`. The query is
a setting of the node, so the node knows the query form when it is made:
`formWire` gives `table` for SELECT, `answer` for ASK, and `dataset` for
CONSTRUCT and DESCRIBE (the dataset whose default graph is the answer graph
and which has no named graph: the npm `Dataset` that `query` returns). Owner,
2026-10-25, verbatim: "select give table? Sure". `evalContract_wire` proves that every answer that satisfies
`EvalContract` has this wire, so `LawfulEvaluator.run_wire`: a lawful
evaluator on a well-formed input outside its assumed class answers with the
wire of the query form. A CONSTRUCT node can therefore feed a node that reads
a dataset, or (by the conversion `dataset` to `graph`, the default graph) a
graph.

## What a setting does to the contract

`SettingRole`, per stage (`settingTable`):

* `parameter`: the contract is stated for every value (the theorem
  quantifies over it), so every value keeps the proved status;
* `selectsWire`: also a parameter, and it selects the output wire;
* `inert`: the stage's computation does not read it on a node's input;
* `narrows d`: the contract covers only the default `d`; any other value
  leaves the proved domain, and the node's status is `unproved`;
* a key that the table does not name, on a `proved` stage, also leaves the
  proved domain: its effect on the contract is not stated, so no guarantee
  is claimed.

A stage that is not `proved` has no proved domain; its settings are
recorded only.

## The canonical form

`canonJson`: object members sorted by key (code point order), at every
depth, arrays in their order, number lexical forms as given. A member
`{"$nquads": text}` (how the npm host passes a Dataset value) is replaced by
`{"nquadsSha256": hex}`. The settings object of the evidence record is the
given settings plus the default of every `narrows` key that is absent, in
canonical form; its digest is the SHA-256 of its compact JSON text
(`settingsDigest`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.Registry
import L4Factoidal.SPARQL.Parser
import L4Factoidal.JSON.Value
import L4Factoidal.JSON.Serialize
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.Dataflow

open L4Factoidal.SPARQL
open L4Factoidal.JSON

/-! ## The output wire of an evaluator node -/

/-- The wire of an answer: `table` for a SELECT answer, `answer` for an ASK
answer, `dataset` for a CONSTRUCT or DESCRIBE graph (as the default graph of a
dataset with no named graph). -/
def Answer.wire : Answer → Wire
  | .select _ _ => .table
  | .ask _ => .answer
  | .graph _ => .dataset

/-- The output wire that a query form selects. -/
def formWire : QueryForm → Wire
  | .select _ => .table
  | .ask => .answer
  | .construct _ => .dataset
  | .describe _ => .dataset

/-- The name of a query form in the evidence record. -/
def formName : QueryForm → String
  | .select _ => "SELECT"
  | .ask => "ASK"
  | .construct _ => "CONSTRUCT"
  | .describe _ => "DESCRIBE"

theorem referenceAnswer_wire (inp : EvalInput) :
    (referenceAnswer inp).wire = formWire inp.query.form := by
  unfold referenceAnswer
  split <;> simp_all [Answer.wire, formWire]

theorem modifierLayer_wire {inp : EvalInput} {A : SolutionSeq} {out : Answer}
    (h : modifierLayer inp A = some out) : out.wire = formWire inp.query.form := by
  unfold modifierLayer at h
  split at h <;> simp_all [Answer.wire, formWire] <;> (cases h; rfl)

/-- **An answer that satisfies the evaluator contract has the wire of the
query form.** -/
theorem evalContract_wire {inp : EvalInput} {out : Answer} (h : EvalContract inp out) :
    out.wire = formWire inp.query.form := by
  rcases h with h | ⟨_, _, _, _, hm⟩
  · rw [h]; exact referenceAnswer_wire inp
  · exact modifierLayer_wire hm

/-- A lawful evaluator, on a well-formed input outside its assumed class,
answers with the wire of the query form. -/
theorem LawfulEvaluator.run_wire (ev : LawfulEvaluator) (inp : EvalInput) (hw : inp.Wf)
    (hna : ¬ ev.assumed_contractOn inp) : (ev.run inp).wire = formWire inp.query.form :=
  evalContract_wire (ev.sound inp hw hna)

/-- The same under the evaluator's named assumption, on every well-formed
input. -/
theorem LawfulEvaluator.run_wire_of (ev : LawfulEvaluator) (h : ev.AssumptionHolds)
    (inp : EvalInput) (hw : inp.Wf) : (ev.run inp).wire = formWire inp.query.form :=
  evalContract_wire (ev.contract h inp hw)

/-- The signature of a node: the entry's signature with the output wire that
its settings select. -/
def Entry.nodeSig (e : Entry) (outW : Wire) : StageSig Wire Lean.Name :=
  { e.sig with outW }

/-! ## Settings and the contract -/

/-- What a setting does to the contract of its stage (module header). -/
inductive SettingRole where
  | parameter (why : String)
  | selectsWire (why : String)
  | inert (why : String)
  | narrows (default : Option Json) (why : String)

def SettingRole.label : SettingRole → String
  | .parameter _ => "parameter"
  | .selectsWire _ => "selects-wire"
  | .inert _ => "inert"
  | .narrows _ _ => "narrows"

def SettingRole.why : SettingRole → String
  | .parameter w | .selectsWire w | .inert w | .narrows _ w => w

private def textInput : SettingRole :=
  .inert "read only when the input is text; a node after a reader reads a dataset"

/-- The RDF readers bound in npm. -/
def readerStages : List String :=
  [ "ntriplesDocumentReader", "nquadsDocumentReader", "turtleDocumentReader",
    "trigDocumentReader", "rdfxmlDocumentReader", "jsonldDocumentReader" ]

/-- The RDF writers bound in npm. -/
def writerStages : List String :=
  [ "ntriplesDocumentWriter", "nquadsDocumentWriter", "turtleDocumentWriter",
    "trigDocumentWriter", "rdfxmlDocumentWriter", "jsonldDocumentWriter" ]

/-- The reasoners bound in npm. -/
def reasonerStages : List String := ["rdfsReasoner", "owlRlReasoner", "rhoDfReasoner"]

/-- The CSVW stage (status `tested`; its node name is its area). -/
def csvwStageName : String := "CSVW (tabular data to RDF)"

private def readerTable : List (String × SettingRole) :=
  [ ("format", .parameter
      "names the stage's syntax and selects the RDF version mode; ReaderContract is stated for every mode"),
    ("baseIRI", .parameter "ReaderContract is stated for every base IRI"),
    ("lenient", .narrows (some (.bool false))
      "the lenient parse skips the statements that fail; ReaderContract states the strict parse (parseDocumentRaw)"),
    ("maxErrors", .inert "read only by the lenient parse") ]

private def writerTable : List (String × SettingRole) :=
  [ ("format", .parameter "names the stage's syntax"),
    ("version", .parameter "the RDF version mode; RoundTripOn is stated for each mode"),
    ("prefixes", .parameter "a TurtleRenderOptions field; RoundTripOn is stated for every options value"),
    ("literalShorthand", .parameter "a TurtleRenderOptions field; RoundTripOn is stated for every options value"),
    ("useNativeTypes", .narrows none "a JSON-LD render option; not a TurtleRenderOptions field"),
    ("useRdfType", .narrows none "a JSON-LD render option; not a TurtleRenderOptions field"),
    ("rdfDirection", .narrows none "a JSON-LD render option; not a TurtleRenderOptions field") ]

private def evaluatorTable : List (String × SettingRole) :=
  [ ("query", .selectsWire
      "the query form selects the output wire (evalContract_wire); EvalContract is stated for every parsed query"),
    ("baseIRI", .parameter "the base IRI of the query; part of the parsed query"),
    ("sparql12", .parameter "selects the SPARQL 1.2 grammar; EvalContract is stated for the parsed query"),
    ("version", .parameter "selects the SPARQL grammar; EvalContract is stated for the parsed query"),
    ("entail", .narrows (some (.string "none"))
      "a regime other than none adds an entailment step that EvalContract does not state"),
    ("output", .narrows none "the results document rendering has no stage"),
    ("format", textInput) ]

/-- The settings table of a node name (module header). A stage that is not
named here has the empty table. -/
def settingTable (stage : String) : List (String × SettingRole) :=
  if readerStages.contains stage then readerTable
  else if writerStages.contains stage then writerTable
  else if stage == "shippedEvaluator" then evaluatorTable
  else if reasonerStages.contains stage then [("format", textInput), ("baseIRI", textInput)]
  else if stage == "shaclValidator" then
    [ ("shapes", .parameter "CoreConformance is stated for every shapes graph"),
      ("format", textInput), ("baseIRI", textInput) ]
  else if stage == "rdfcStage" then [("format", textInput), ("baseIRI", textInput)]
  else if stage == "rdfsExplainGraphStage" then
    [ ("description", .parameter "ExplainGraphContract is stated for every description"),
      ("format", textInput), ("baseIRI", textInput) ]
  else if stage == csvwStageName then
    [ ("metadata", .parameter "the CSVW metadata document (csv2rdf section 4)"),
      ("mode", .parameter "standard or minimal mode (csv2rdf section 4)"),
      ("base", .parameter "the base IRI of the conversion"),
      ("url", .parameter "the URL of the tabular data") ]
  else []

/-! ## The canonical form -/

mutual
/-- Canonical JSON (module header). The recursion depth is the nesting depth
of the settings document; the member and element loops are tail calls. -/
def canonJson : Json → Json
  | .array xs => .array (canonArr xs [])
  | .object [("$nquads", .string s)] =>
    .object [("nquadsSha256", .string (L4Factoidal.Crypto.sha256Hex s))]
  | .object kvs => .object ((canonObj kvs []).mergeSort (fun a b => !(b.1 < a.1)))
  | j => j

/-- The elements in canonical form, in order (accumulator reversed at the end). -/
def canonArr : List Json → List Json → List Json
  | [], acc => acc.reverse
  | x :: xs, acc => canonArr xs (canonJson x :: acc)

/-- The members with canonical values, in order. -/
def canonObj : List (String × Json) → List (String × Json) → List (String × Json)
  | [], acc => acc.reverse
  | (k, v) :: rest, acc => canonObj rest ((k, canonJson v) :: acc)
end

/-- The compact text of the canonical form. -/
def canonText (j : Json) : String := (canonJson j).toString

/-- The digest of a settings object: `sha256:` and the hex SHA-256 of its
canonical text. -/
def settingsDigest (j : Json) : String := "sha256:" ++ L4Factoidal.Crypto.sha256Hex (canonText j)

/-! ## The settings of a node -/

/-- What `nodeSettings` reports for one node. -/
structure NodeSettings where
  /-- The settings in canonical form, with the defaults of absent `narrows` keys. -/
  settings : Json
  digest : String
  /-- `(key, role label)` for every key of `settings`. -/
  roles : List (String × String)
  /-- `(key, reason)` for every setting outside the proved domain. -/
  outside : List (String × String)
  /-- The output wire the settings select. -/
  outW : Wire
  /-- Values read from the settings (the query form). -/
  derived : List (String × Json)
  /-- `unproved` for a proved stage with a setting outside the domain, else the
  registry status. -/
  status : String
  /-- The status is `proved`. -/
  checked : Bool

private def lookupKey (kvs : List (String × Json)) (k : String) : Option Json :=
  (kvs.find? (·.1 == k)).map (·.2)

/-- The output wire and derived values of an evaluator node: the form of the
parsed query, when the settings carry one. -/
def evaluatorWire (given : List (String × Json)) : Except String (Wire × List (String × Json)) :=
  match lookupKey given "query" with
  | none => .ok (.answer, [])
  | some (.string q) =>
    let v : SparqlVersion :=
      match lookupKey given "sparql12", lookupKey given "version" with
      | some (.bool true), _ => .v12
      | _, some (.string "1.2") => .v12
      | _, _ => .v11
    let base : Option String :=
      match lookupKey given "baseIRI" with
      | some (.string b) => if b.isEmpty then none else some b
      | _ => none
    match parseSparql q base v with
    | .ok query => .ok (formWire query.form, [("form", .string (formName query.form))])
    | .error err => .error s!"the query does not parse: {err.msg} (offset {err.pos})"
  | some _ => .error "the setting query must be a string"

/-- The settings outside the proved domain of node `e`: none for a stage that
is not `proved`; else every key with a `narrows` role and a value other than
its default, and every key the table does not name. -/
def outsideOf (e : Entry) (given : List (String × Json)) : List (String × String) :=
  if e.status != .proved then [] else given.filterMap fun (k, v) =>
    match (settingTable e.nodeName).lookup k with
    | none => some (k, s!"not a setting of stage {e.nodeName} in the settings table; its effect on the contract is not stated")
    | some (.narrows d why) =>
      if d.map canonText == some (canonText v) then none else some (k, why)
    | some _ => none

/-- The node is checked: a proved stage with no setting outside the domain. -/
def nodeChecked (e : Entry) (given : List (String × Json)) : Bool :=
  e.status == .proved && (outsideOf e given).isEmpty

/-- A checked node is a proved stage with every setting in the proved domain. -/
theorem nodeChecked_iff (e : Entry) (given : List (String × Json)) :
    nodeChecked e given = true ↔ e.status = .proved ∧ outsideOf e given = [] := by
  simp [nodeChecked, List.isEmpty_iff]

/-- A proved stage given no settings is checked: the defaults are in the domain. -/
theorem nodeChecked_nil (e : Entry) (h : e.status = .proved) : nodeChecked e [] = true := by
  simp [nodeChecked, outsideOf, h]

/-- The settings of node `e` with the given settings object members. Fails on
a key given twice and on an evaluator query that is not a string or does not
parse. `outside` is `outsideOf`, `checked` is `nodeChecked`. -/
def nodeSettings (e : Entry) (given : List (String × Json)) : Except String NodeSettings := do
  let keys := given.map (·.1)
  if keys.eraseDups.length != keys.length then
    throw "a setting is given twice"
  let table := settingTable e.nodeName
  let (outW, derived) ← if e.nodeName == "shippedEvaluator" then evaluatorWire given
    else pure (e.wireOut, [])
  let defaults := table.filterMap fun (k, r) =>
    match r with
    | .narrows (some d) _ => if keys.contains k then none else some (k, d)
    | _ => none
  let settings := canonJson (.object (given ++ defaults))
  let roles := (given ++ defaults).map fun (k, _) =>
    (k, ((table.lookup k).map SettingRole.label).getD "unlisted")
  let checked := nodeChecked e given
  pure { settings, digest := settingsDigest settings,
         roles := roles.mergeSort (fun a b => !(b.1 < a.1)),
         outside := outsideOf e given, outW, derived,
         status := if e.status == .proved && !checked then "unproved" else e.status.label, checked }

/-! ## Checks -/

private def entryNamed (n : String) : Option Entry := registry.find? (·.nodeName == n)

/-- The signature of an evaluator node over query text `q`. -/
private def evaluatorSigOf (q : String) : Option (StageSig Wire Lean.Name) :=
  match entryNamed "shippedEvaluator", evaluatorWire [("query", .string q)] with
  | some e, .ok (w, _) => some (e.nodeSig w)
  | _, _ => none

private def sigOf (n : String) : Option (StageSig Wire Lean.Name) := (entryNamed n).map Entry.sig

private def checkPath (p : List (Option (StageSig Wire Lean.Name))) : Bool :=
  match p.mapM id with
  | some sigs => wellTyped Wire.conv sigs
  | none => false

private def constructQ : String := "CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }"
private def selectQ : String := "SELECT ?s WHERE { ?s ?p ?o }"

-- the form selects the wire
#guard (evaluatorSigOf constructQ).map (·.outW) == some Wire.dataset
#guard (evaluatorSigOf "DESCRIBE <urn:x>").map (·.outW) == some Wire.dataset
#guard (evaluatorSigOf selectQ).map (·.outW) == some Wire.table
#guard (evaluatorSigOf "ASK { ?s ?p ?o }").map (·.outW) == some Wire.answer
-- reader -> CONSTRUCT -> CONSTRUCT is well typed
#guard checkPath [sigOf "turtleDocumentReader", evaluatorSigOf constructQ, evaluatorSigOf constructQ]
-- reader -> SELECT -> CONSTRUCT is not
#guard !checkPath [sigOf "turtleDocumentReader", evaluatorSigOf selectQ, evaluatorSigOf constructQ]
-- CONSTRUCT feeds a reasoner (default graph); SELECT does not
#guard checkPath [sigOf "turtleDocumentReader", evaluatorSigOf constructQ, sigOf "rdfsReasoner"]
#guard !checkPath [sigOf "turtleDocumentReader", evaluatorSigOf selectQ, sigOf "rdfsReasoner"]
-- CSVW output feeds the evaluator
#guard checkPath [sigOf csvwStageName, evaluatorSigOf constructQ]
#guard (evaluatorWire [("query", .string "SELEKT")]).toOption.isNone
#guard (evaluatorWire [("query", .number "1")]).toOption.isNone

private def settingsOf (n : String) (given : List (String × Json)) : Option NodeSettings :=
  (entryNamed n).bind fun e => (nodeSettings e given).toOption

-- canonical form: sorted keys at every depth, the same digest for any member order
#guard canonText (.object [("b", .number "1"), ("a", .object [("d", .null), ("c", .bool true)])])
  == "{\"a\":{\"c\":true,\"d\":null},\"b\":1}"
#guard settingsDigest (.object [("b", .number "1"), ("a", .string "x")])
  == settingsDigest (.object [("a", .string "x"), ("b", .number "1")])
#guard (settingsDigest (.object [("a", .string "x")])).length == 7 + 64
#guard canonText (.object [("shapes", .object [("$nquads", .string "")])])
  == "{\"shapes\":{\"nquadsSha256\":\"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855\"}}"
-- a strict reader with a base IRI stays proved; the default lenient false is recorded
#guard ((settingsOf "turtleDocumentReader" [("baseIRI", .string "http://e/")]).map
  fun r => (r.status, r.checked, canonText r.settings)) ==
  some ("proved", true, "{\"baseIRI\":\"http://e/\",\"lenient\":false}")
-- lenient leaves the proved domain
#guard ((settingsOf "turtleDocumentReader" [("lenient", .bool true)]).map
  fun r => (r.status, r.checked, r.outside.map (·.1))) == some ("unproved", false, ["lenient"])
-- an evaluator with a regime other than none, or an unlisted key, is unproved
#guard ((settingsOf "shippedEvaluator" [("query", .string selectQ), ("entail", .string "RDFS")]).map
  (·.status)) == some "unproved"
#guard ((settingsOf "shippedEvaluator" [("query", .string selectQ)]).map
  fun r => (r.status, r.outW, r.derived.map (·.1))) == some ("proved", Wire.table, ["form"])
#guard ((settingsOf "shippedEvaluator" [("query", .string selectQ), ("bogus", .null)]).map
  (·.status)) == some "unproved"
-- a stage that is not proved keeps its status; its settings are recorded
#guard ((settingsOf "turtleDocumentWriter" [("bogus", .null)]).map
  fun r => (r.status, r.outside.length)) == some ("assumed", 0)
#guard ((settingsOf csvwStageName [("metadata", .string "{}")]).map
  fun r => (r.status, r.checked)) == some ("tested", false)
-- a key given twice is refused
#guard (settingsOf "rdfsReasoner" [("format", .string "turtle"), ("format", .string "nt")]).isNone

end L4Factoidal.Dataflow
