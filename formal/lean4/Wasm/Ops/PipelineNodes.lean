/-
Wasm.Ops.PipelineNodes — the `pipelineCheckNodes` op: the type check of a
pipeline of nodes (a registry stage plus its settings), with each node's
settings in canonical form, their digest, and what they do to the contract
(https://github.com/danbri/factoidal/issues/975,
https://github.com/danbri/factoidal/issues/1026).

  pipelineCheckNodes(nodesJson)
    nodesJson: [{"stage":S,"settings":{...}}]   (settings optional)
    -> {"ok":true,"wellTyped":B,"wireIn":S|null,"wireOut":S|null,
        "mismatch":{"at":N,"out":S,"in":S}|null,
        "conversions":[{"at":N,"from":S,"to":S}],
        "assumptions":[S],
        "contract":{"theorem":S,"stages":[S|null]},
        "stages":[{"name":S,"status":S,"registryStatus":S,"checked":B,
                   "contract":S|null,"assumptions":[S],"wireIn":S,"wireOut":S,
                   "settings":{...},"settingsDigest":S,"roles":{K:S},
                   "outside":[{"setting":K,"reason":S}],"derived":{...}}]}
    -> {"ok":false,"error":S} on an unknown stage name, an empty list, a
       settings value that is not an object, a key given twice, an evaluator
       query that does not parse, or a reader or writer `format` that names
       another syntax.

The same report as `pipelineCheck` (`Wasm/Ops/StageList.lean`), computed by
`pipelineReport Wire.conv` over the node signatures `Entry.nodeSig` instead of
the registry signatures: the output wire of a `shippedEvaluator` node is the
wire of its query form (`formWire`: SELECT `table`, ASK `answer`, CONSTRUCT
and DESCRIBE `dataset`; proved for every lawful evaluator answer
by `evalContract_wire`, `Dataflow/NodeSettings.lean`). Per node:

* `status`: `unproved` when the stage is `proved` and a setting is outside its
  proved domain (`outsideOf`), else the registry status (`registryStatus`);
  `checked` is `nodeChecked`;
* `settings`: the given settings plus the defaults of absent `narrows` keys,
  in canonical form (`canonJson`); `settingsDigest`: `settingsDigest`;
* `roles`: the role of each setting (`SettingRole.label`, or `unlisted`);
* `derived`: the query form of an evaluator node; the RDF version mode
  (`1.1`, `1.2`) that a reader's `format` selects.

The op reads no data (foundation/entrypoints.toml: nonstage, reflection).

Targeted imports only — never the L4Factoidal umbrella.
-/
import Wasm.Ops.StageList
import Wasm.Ops.Handles
import L4Factoidal.Dataflow.NodeSettings

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.Dataflow

/-- The parse format tag of each reader stage. -/
def readerFormatTag : String → Option String
  | "ntriplesDocumentReader" => some "ntriples"
  | "nquadsDocumentReader" => some "nquads"
  | "turtleDocumentReader" => some "turtle"
  | "trigDocumentReader" => some "trig"
  | "rdfxmlDocumentReader" => some "rdfxml"
  | "jsonldDocumentReader" => some "jsonld"
  | _ => none

/-- The writer format tag of each writer stage. -/
def writerFormatTag : String → Option String
  | "ntriplesDocumentWriter" => some "ntriples"
  | "nquadsDocumentWriter" => some "nquads"
  | "turtleDocumentWriter" => some "turtle"
  | "trigDocumentWriter" => some "trig"
  | "rdfxmlDocumentWriter" => some "rdfxml"
  | "jsonldDocumentWriter" => some "jsonld"
  | _ => none

/-- The check of a reader or writer node's `format` setting, and the RDF
version mode it selects (`derived`). -/
def formatDerived (stage : String) (given : List (String × Json)) :
    Except String (List (String × Json)) :=
  match ((given.find? (·.1 == "format")).map (·.2) : Option Json) with
  | none => .ok []
  | some (.string v) =>
    match readerFormatTag stage, writerFormatTag stage with
    | some base, _ =>
      match parseFormatNames.lookup v.toLower with
      | some tag =>
        if tag == base then .ok [("mode", .string "1.1")]
        else if tag == base ++ "12" then .ok [("mode", .string "1.2")]
        else .error s!"stage {stage} reads {base}; format '{v}' names {tag}"
      | none => .error s!"stage {stage}: unknown format '{v}'"
    | none, some base =>
      match writerFormatNames.lookup v.toLower with
      | some tag =>
        if tag == base then .ok []
        else .error s!"stage {stage} writes {base}; format '{v}' names {tag}"
      | none => .error s!"stage {stage}: unknown format '{v}'"
    | none, none => .ok []
  | some _ => .error s!"stage {stage}: the setting format must be a string"

/-- One node of the request: its entry and settings. `who` is the op name
that the error messages start with (`graphCheckNodes` reads its registry nodes
with this function too, `Wasm/Ops/GraphNodes.lean`). -/
def nodeOfJson (i : Nat) (j : Json) (who : String := "pipelineCheckNodes") :
    Except String (Entry × NodeSettings) :=
  match j with
  | .object kvs => do
    let name ← match ((kvs.find? (·.1 == "stage")).map (·.2) : Option Json) with
      | some (.string n) => pure n
      | _ => throw s!"{who}: node {i} has no string member stage"
    let e ← match entryOfName name with
      | some e => pure e
      | none => throw s!"{who}: no registered stage named '{name}'"
    let given ← match ((kvs.find? (·.1 == "settings")).map (·.2) : Option Json) with
      | none | some .null => pure []
      | some (.object g) => pure g
      | some _ => throw s!"{who}: node {i} ({name}): settings must be an object"
    let fmt ← (formatDerived name given).mapError fun m => s!"{who}: node {i}: {m}"
    let r ← (nodeSettings e given).mapError fun m => s!"{who}: node {i} ({name}): {m}"
    pure (e, { r with derived := r.derived ++ fmt })
  | _ => .error s!"{who}: node {i} is not an object"

private def wireJsonOpt : Option Wire → Json
  | some w => .string w.label
  | none => .null

private def nameJsonOpt (n : Lean.Name) : Json :=
  if isNone n then .null else .string n.toString

/-- The JSON of the check of a list of nodes. -/
def pipelineCheckNodesJson (ns : List (Entry × NodeSettings)) : String :=
  let sigs := ns.map fun (e, r) => e.nodeSig r.outW
  let rep := pipelineReport Wire.conv sigs
  let mismatch : Json := match rep.mismatch with
    | some i =>
      .object [("at", .number (toString i)), ("out", wireJsonOpt ((sigs[i]?).map (·.outW))),
               ("in", wireJsonOpt ((sigs[i + 1]?).map (·.inW)))]
    | none => .null
  okWith
    [ ("wellTyped", .bool rep.wellTyped),
      ("wireIn", wireJsonOpt rep.wireIn),
      ("wireOut", wireJsonOpt rep.wireOut),
      ("mismatch", mismatch),
      ("conversions", .array (rep.conversions.map fun (i, a, b) =>
        .object [("at", .number (toString i)), ("from", .string a.label), ("to", .string b.label)])),
      ("assumptions", .array (rep.assumptions.map fun n => .string n.toString)),
      ("contract", .object
        [ ("theorem", .string (``Pipeline.guarantee_sound).toString),
          ("stages", .array (rep.contracts.map fun c =>
            match c with | some n => .string n.toString | none => .null)) ]),
      ("stages", .array (ns.map fun (e, r) =>
        .object
          [ ("name", .string e.nodeName),
            ("status", .string r.status),
            ("registryStatus", .string e.status.label),
            ("checked", .bool r.checked),
            ("contract", nameJsonOpt e.contract),
            ("assumptions", .array (e.ioAssumptions.map fun n => .string n.toString)),
            ("wireIn", .string e.wireIn.label),
            ("wireOut", .string r.outW.label),
            ("settings", r.settings),
            ("settingsDigest", .string r.digest),
            ("roles", .object (r.roles.map fun (k, l) => (k, .string l))),
            ("outside", .array (r.outside.map fun (k, why) =>
              .object [("setting", .string k), ("reason", .string why)])),
            ("derived", .object r.derived) ])) ]

/-- `pipelineCheckNodes(nodesJson)`. -/
def pipelineCheckNodes (nodesJson : String) : String :=
  match parseJson nodesJson with
  | .error e => errJson s!"pipelineCheckNodes: nodesJson: {toString e}"
  | .ok (.array []) => errJson "pipelineCheckNodes: no nodes"
  | .ok (.array items) =>
    match (items.zipIdx.mapM fun (j, i) => nodeOfJson i j) with
    | .error e => errJson e
    | .ok ns => pipelineCheckNodesJson ns
  | .ok _ => errJson "pipelineCheckNodes: nodesJson must be a JSON array"

/-! ## Checks -/

private def subOf (hay needle : String) : Bool := (hay.splitOn needle).length > 1

private def evalNode (q : String) : String :=
  "{\"stage\":\"shippedEvaluator\",\"settings\":{\"query\":\"" ++ q ++ "\"}}"
private def cq : String := "CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }"
private def sq : String := "SELECT ?s WHERE { ?s ?p ?o }"
private def reader : String := "{\"stage\":\"turtleDocumentReader\"}"

-- issue 1026: reader -> CONSTRUCT -> CONSTRUCT is well typed
#guard subOf (pipelineCheckNodes s!"[{reader},{evalNode cq},{evalNode cq}]") "\"wellTyped\":true"
#guard subOf (pipelineCheckNodes s!"[{reader},{evalNode cq},{evalNode cq}]")
  "\"conversions\":[{\"at\":0,\"from\":\"Dataset × PrefixList\",\"to\":\"Dataset\"}],"
-- reader -> SELECT -> CONSTRUCT is not
#guard subOf (pipelineCheckNodes s!"[{reader},{evalNode sq},{evalNode cq}]") "\"wellTyped\":false"
#guard subOf (pipelineCheckNodes s!"[{reader},{evalNode sq},{evalNode cq}]")
  "\"mismatch\":{\"at\":1,\"out\":\"Table\",\"in\":\"Dataset\"}"
-- the evaluator node's settings, form and digest are reported
#guard subOf (pipelineCheckNodes s!"[{evalNode cq}]") "\"derived\":{\"form\":\"CONSTRUCT\"}"
#guard subOf (pipelineCheckNodes s!"[{evalNode cq}]")
  s!"\"settings\":\{\"entail\":\"none\",\"query\":\"{cq}\"}"
#guard subOf (pipelineCheckNodes s!"[{evalNode cq}]") "\"settingsDigest\":\"sha256:"
#guard subOf (pipelineCheckNodes s!"[{evalNode cq}]") "\"status\":\"proved\",\"registryStatus\":\"proved\",\"checked\":true"
-- a lenient reader is unproved and says why
#guard subOf (pipelineCheckNodes "[{\"stage\":\"turtleDocumentReader\",\"settings\":{\"lenient\":true}}]")
  "\"status\":\"unproved\",\"registryStatus\":\"proved\",\"checked\":false"
#guard subOf (pipelineCheckNodes "[{\"stage\":\"turtleDocumentReader\",\"settings\":{\"lenient\":true}}]")
  "\"outside\":[{\"setting\":\"lenient\""
-- a reader's format selects the mode, and must name the stage's syntax
#guard subOf (pipelineCheckNodes "[{\"stage\":\"turtleDocumentReader\",\"settings\":{\"format\":\"ttl12\"}}]")
  "\"derived\":{\"mode\":\"1.2\"}"
#guard subOf (pipelineCheckNodes "[{\"stage\":\"turtleDocumentReader\",\"settings\":{\"format\":\"nt\"}}]")
  "\"ok\":false"
#guard subOf (pipelineCheckNodes "[{\"stage\":\"turtleDocumentWriter\",\"settings\":{\"format\":\"ttl\"}}]")
  "\"ok\":true"
-- CSVW feeds the evaluator; its record is tested and unchecked
#guard subOf (pipelineCheckNodes
  s!"[\{\"stage\":\"CSVW (tabular data to RDF)\",\"settings\":\{\"metadata\":\"\{}\"}},{evalNode cq}]")
  "\"wellTyped\":true"
#guard subOf (pipelineCheckNodes "[{\"stage\":\"CSVW (tabular data to RDF)\"}]")
  "\"status\":\"tested\",\"registryStatus\":\"tested\",\"checked\":false"
-- refusals
#guard subOf (pipelineCheckNodes s!"[{evalNode "SELEKT"}]") "\"ok\":false"
#guard subOf (pipelineCheckNodes "[]") "\"ok\":false"
#guard subOf (pipelineCheckNodes "[{\"stage\":\"noSuchStage\"}]") "\"ok\":false"
#guard subOf (pipelineCheckNodes "[{\"stage\":\"rdfsReasoner\",\"settings\":[]}]") "\"ok\":false"
-- with no settings the report agrees with pipelineCheck on wellTyped and the union
#guard subOf (pipelineCheckNodes
  "[{\"stage\":\"turtleDocumentReader\"},{\"stage\":\"turtleDocumentWriter\"}]")
  "\"assumptions\":[\"L4Factoidal.Dataflow.TurtleWriterRoundTrip\"]"

end L4Wasm.Ops
