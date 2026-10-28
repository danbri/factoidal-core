/-
Wasm.Ops.GraphNodes — the `graphCheckNodes` op: the static check of a pipeline
that is an acyclic graph of nodes with named input ports, and the `datasetMerge`
op: the RDF merge of two stored datasets
(https://github.com/danbri/factoidal/issues/1130, stage 1b).

  graphCheckNodes(graphJson)
    graphJson: {"inputs":[WIRE,...],
                "nodes":[{"stage":S,"settings":{...},"from":[SRC,...]}]}
      WIRE: a wire label (`Wire.label`, `Dataflow/Wire.lean`), e.g. "String"
      SRC:  {"input":K} (graph input K) or {"node":J} (the output of node J)
      settings: optional, as for `pipelineCheckNodes`
    -> {"ok":true,
        "issues":[ISSUE],
        "wireOut":S|null,
        "assumptions":[S],
        "contract":{"theorem":S,"staticCheck":S},
        "nodes":[{"name":S,"kind":S|null,"status":S,"registryStatus":S|null,
                  "checked":B,"contract":S|null,"theorems":[S],"assumptions":[S],
                  "ports":[{"name":S,"wire":S}],"wireOut":S,
                  "settings":{...},"settingsDigest":S,"roles":{K:S},
                  "outside":[{"setting":K,"reason":S}],"derived":{...}}]}
      ISSUE: {"kind":"unknownInput","node":N,"port":N,"portName":S,"input":K}
           | {"kind":"forwardRef","node":N,"port":N,"portName":S,"ref":J}
           | {"kind":"portCount","node":N,"ports":N,"sources":N}
           | {"kind":"wireMismatch","node":N,"port":N,"portName":S,
              "source":WIRE,"portWire":WIRE}
    -> {"ok":false,"error":S} on JSON that does not parse, a document that is
       not an object, an `inputs` member that is not an array of known wire
       labels, a `nodes` member that is not a non-empty array, a node with no
       array member `from`, a `from` element that is neither form, an unknown
       stage name, or settings that `pipelineCheckNodes` refuses.

The issues are `graphIssues Wire.conv inW sigs` (`Dataflow/Graph.lean`) over
the node signatures; this module does not check a graph in any other way. So
an answer with no issue is the premise of `Graph.run_stage_error_only` (a run
on inputs of these wires fails only in a stage's own run), and `assumptions`
is `sigAssumptions sigs`, which is `Graph.assumptions` (`Graph.assumptions_eq_sigs`):
the premises of `Graph.guarantee_sound`.

The node signatures:

* a registry stage (`Dataflow/Registry.lean`): `Entry.nodeSig` with the output
  wire its settings select (`nodeSettings`, as `pipelineCheckNodes`), as a
  port signature with one port named `in` (`StageSig.toPortSig`). Its JSON
  fields are those `pipelineCheckNodes` gives, plus `kind`, `theorems`,
  `ports` and `wireOut`;
* a port stage, a stage with more than one input port, from `portStages`
  below. Today the table has `datasetMerge` (`datasetMergeSig`,
  `Dataflow/GraphStages.lean`): ports `left` and `right` on `Dataset`, output
  `Dataset`, contract `DatasetDen.IsMerge`, status `proved`, no named
  assumption. A port stage is not a registry entry (the registry has one input
  wire per stage), so its `registryStatus` is null. It takes no setting: a
  given setting is outside the proved domain, and the node is `unproved`.

  datasetMerge(handle1, handle2)
    -> the `datasetOpen` envelope of a new handle: `mergeDatasets n` of the two
       stored datasets, with two scope numbers `n`, `n + 1` read from the
       engine's document-scope counter (`documentScopeCounter`,
       `Wasm/Ops/Parse.lean`); the prefixes of the first dataset, then those of
       the second whose label the first does not declare.
    -> the unknown-handle error for a handle that is not open.

`mergeDatasets n a c` is `datasetMergeAt n (n + 1) a c`; theorem
`mergeDatasets_isMerge`: its denotation is an RDF merge of the two inputs
(RDF 1.1 Semantics section 5.2; `DatasetDen.IsMerge`). The two scope numbers
differ, so a blank node of one input is never a blank node of the other,
whatever labels they used. The counter is IO: that `n` was not used for
another document is not modelled.

Targeted imports only — never the L4Factoidal umbrella.
-/
import Wasm.Ops.PipelineNodes
import L4Factoidal.Dataflow.GraphStages

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.Dataflow

/-! ## The merge of the op `datasetMerge` -/

/-- The merge of the op `datasetMerge` (module header). -/
def mergeDatasets (n : Nat) (a c : L4Factoidal.RDF.Dataset) : L4Factoidal.RDF.Dataset :=
  datasetMergeAt n (n + 1) a c

/-- **The op's dataset denotes an RDF merge** of its two inputs, for every
value of the counter. -/
theorem mergeDatasets_isMerge (n : Nat) (a c : L4Factoidal.RDF.Dataset) :
    L4Factoidal.RDF.DatasetDen.IsMerge a.den c.den (mergeDatasets n a c).den :=
  datasetMergeAt_isMerge (Nat.ne_of_lt (Nat.lt_succ_self n)) a c

/-- The prefixes of a merge: those of the first dataset, then those of the
second whose label the first does not declare. -/
def mergePrefixes (p q : List (String × String)) : List (String × String) :=
  p ++ q.filter fun (l, _) => !(p.any (·.1 == l))

/-! ## Port stages -/

/-- A stage with more than one input port, as `graphCheckNodes` reads it. -/
structure PortStage where
  sig : PortSig Wire Lean.Name
  status : Status
  theorems : List Lean.Name

/-- The port stages (module header). -/
def portStages : List PortStage :=
  [ { sig := datasetMergeSig Wire.dataset (some ``L4Factoidal.RDF.DatasetDen.IsMerge)
      status := .proved
      theorems := [``L4Factoidal.Dataflow.datasetMerge_isMerge,
        ``L4Factoidal.Dataflow.datasetMergeAt_isMerge, ``mergeDatasets_isMerge] } ]

/-- The names of the port stages. `tools/runners-gate.py` reads this list:
each key of the npm table `PORT_RUNNERS` (`npm/factoidal/lib/nodes.mjs`) must
be in it. The `#guard` below keeps it equal to the names of `portStages`. -/
def portStageNames : List String := ["datasetMerge"]

#guard portStageNames == portStages.map (·.sig.name)

/-- The port stage named `n`. -/
def portStageOfName (n : String) : Option PortStage := portStages.find? (·.sig.name == n)

/-- The settings of a port-stage node: none are in its proved domain, so each
given key is outside it (`outsideOf` reports a key the settings table does
not name in the same way). -/
def portNodeSettings (p : PortStage) (given : List (String × Json)) :
    Except String NodeSettings := do
  let keys := given.map (·.1)
  if keys.eraseDups.length != keys.length then throw "a setting is given twice"
  let settings := canonJson (.object given)
  let outside := given.map fun (k, _) =>
    (k, s!"not a setting of stage {p.sig.name}; the stage takes no setting, so its effect on the contract is not stated")
  let checked := p.status == .proved && outside.isEmpty
  pure { settings, digest := settingsDigest settings,
         roles := (keys.map fun k => (k, "unlisted")).mergeSort (fun a b => !(b.1 < a.1)),
         outside, outW := p.sig.outW, derived := [],
         status := if p.status == .proved && !checked then "unproved" else p.status.label, checked }

/-! ## The request -/

/-- One node of a graph request, with its signature. -/
structure GraphNodeReq where
  name : String
  sig : PortSig Wire Lean.Name
  /-- The registry entry; none for a port stage. -/
  entry : Option Entry
  kind : Option String
  status : Status
  theorems : List Lean.Name
  assumptions : List Lean.Name
  settings : NodeSettings
  srcs : List Src

private def member (kvs : List (String × Json)) (k : String) : Option Json :=
  (kvs.find? (·.1 == k)).map (·.2)

/-- A source of a port: `{"input":K}` or `{"node":J}`. -/
def srcOfJson (i p : Nat) : Json → Except String Src
  | .object [("input", .number k)] =>
    match k.toNat? with
    | some k => .ok (.input k)
    | none => .error s!"graphCheckNodes: node {i}, source {p}: input must be a natural number"
  | .object [("node", .number j)] =>
    match j.toNat? with
    | some j => .ok (.node j)
    | none => .error s!"graphCheckNodes: node {i}, source {p}: node must be a natural number"
  | _ => .error s!"graphCheckNodes: node {i}, source {p} is neither \{\"input\":K} nor \{\"node\":J}"

/-- The sources of node `i`. -/
def srcsOfJson (i : Nat) (kvs : List (String × Json)) : Except String (List Src) :=
  match member kvs "from" with
  | some (.array xs) => xs.zipIdx.mapM fun (x, p) => srcOfJson i p x
  | _ => .error s!"graphCheckNodes: node {i} has no array member from"

/-- One node of the request (module header). -/
def graphNodeOfJson (i : Nat) (j : Json) : Except String GraphNodeReq := do
  let kvs ← match j with
    | .object kvs => pure kvs
    | _ => throw s!"graphCheckNodes: node {i} is not an object"
  let srcs ← srcsOfJson i kvs
  let name ← match member kvs "stage" with
    | some (.string n) => pure n
    | _ => throw s!"graphCheckNodes: node {i} has no string member stage"
  match portStageOfName name with
  | some p =>
    let given ← match member kvs "settings" with
      | none | some .null => pure []
      | some (.object g) => pure g
      | some _ => throw s!"graphCheckNodes: node {i} ({name}): settings must be an object"
    let r ← (portNodeSettings p given).mapError fun m => s!"graphCheckNodes: node {i} ({name}): {m}"
    pure { name, sig := p.sig, entry := none, kind := some "PortComponent", status := p.status,
           theorems := p.theorems, assumptions := p.sig.assumptions, settings := r, srcs }
  | none =>
    -- the stage, settings and format checks of `pipelineCheckNodes`
    let (e, r) ← nodeOfJson i (.object (kvs.filter (·.1 != "from"))) "graphCheckNodes"
    pure { name := e.nodeName, sig := (e.nodeSig r.outW).toPortSig, entry := some e,
           kind := stageEntryKind e, status := e.status, theorems := e.theorems,
           assumptions := e.ioAssumptions, settings := r, srcs }

/-- The wires of the graph inputs. -/
def inputWiresOfJson : Option Json → Except String (List Wire)
  | some (.array xs) => xs.zipIdx.mapM fun (x, k) =>
    match x with
    | .string s =>
      match Wire.ofLabel? s with
      | some w => .ok w
      | none => .error s!"graphCheckNodes: input {k}: '{s}' is not a wire label (see stageList wireIn/wireOut)"
    | _ => .error s!"graphCheckNodes: input {k} is not a string"
  | none => .ok []
  | some _ => .error "graphCheckNodes: inputs must be an array of wire labels"

/-! ## The answer -/

private def nameJsonOpt (n : Lean.Name) : Json :=
  if isNone n then .null else .string n.toString

private def optNameJson : Option Lean.Name → Json
  | some n => .string n.toString
  | none => .null

private def num (n : Nat) : Json := .number (toString n)

/-- The name of port `p` of node `i`, or the empty string. -/
private def portName (ns : List GraphNodeReq) (i p : Nat) : String :=
  match ns[i]? with
  | some n => ((n.sig.ins[p]?).map (·.1)).getD ""
  | none => ""

/-- The JSON of one issue. -/
def graphIssueJson (ns : List GraphNodeReq) : GraphIssue Wire → Json
  | .unknownInput i p k =>
    .object [("kind", .string "unknownInput"), ("node", num i), ("port", num p),
             ("portName", .string (portName ns i p)), ("input", num k)]
  | .forwardRef i p j =>
    .object [("kind", .string "forwardRef"), ("node", num i), ("port", num p),
             ("portName", .string (portName ns i p)), ("ref", num j)]
  | .portCount i ports sources =>
    .object [("kind", .string "portCount"), ("node", num i), ("ports", num ports),
             ("sources", num sources)]
  | .wireMismatch i p src portW =>
    .object [("kind", .string "wireMismatch"), ("node", num i), ("port", num p),
             ("portName", .string (portName ns i p)), ("source", .string src.label),
             ("portWire", .string portW.label)]

/-- The JSON of one node. -/
def graphNodeJson (n : GraphNodeReq) : Json :=
  let r := n.settings
  .object
    [ ("name", .string n.name),
      ("kind", match n.kind with | some k => .string k | none => .null),
      ("status", .string r.status),
      ("registryStatus", match n.entry with | some e => .string e.status.label | none => .null),
      ("checked", .bool r.checked),
      ("contract", match n.entry with
        | some e => nameJsonOpt e.contract
        | none => optNameJson n.sig.contract),
      ("theorems", .array (n.theorems.map fun t => .string t.toString)),
      ("assumptions", .array (n.assumptions.map fun a => .string a.toString)),
      ("ports", .array (n.sig.ins.map fun (pn, w) =>
        .object [("name", .string pn), ("wire", .string w.label)])),
      ("wireOut", .string n.sig.outW.label),
      ("settings", r.settings),
      ("settingsDigest", .string r.digest),
      ("roles", .object (r.roles.map fun (k, l) => (k, .string l))),
      ("outside", .array (r.outside.map fun (k, why) =>
        .object [("setting", .string k), ("reason", .string why)])),
      ("derived", .object r.derived) ]

/-- The signatures and sources that `graphIssues` reads. -/
def graphSigsOf (ns : List GraphNodeReq) : List (PortSig Wire Lean.Name × List Src) :=
  ns.map fun n => (n.sig, n.srcs)

/-- The answer for a parsed request. -/
def graphCheckNodesJson (inW : List Wire) (ns : List GraphNodeReq) : String :=
  let sigs := graphSigsOf ns
  okWith
    [ ("issues", .array ((graphIssues Wire.conv inW sigs).map (graphIssueJson ns))),
      ("wireOut", match graphOutWire sigs with | some w => .string w.label | none => .null),
      ("assumptions", .array ((sigAssumptions sigs).map fun a => .string a.toString)),
      ("contract", .object
        [ ("theorem", .string (``L4Factoidal.Dataflow.Graph.guarantee_sound).toString),
          ("staticCheck", .string (``L4Factoidal.Dataflow.Graph.run_stage_error_only).toString) ]),
      ("nodes", .array (ns.map graphNodeJson)) ]

/-- `graphCheckNodes(graphJson)`. -/
def graphCheckNodes (graphJson : String) : String :=
  match parseJson graphJson with
  | .error e => errJson s!"graphCheckNodes: graphJson: {toString e}"
  | .ok (.object kvs) =>
    match inputWiresOfJson (member kvs "inputs") with
    | .error e => errJson e
    | .ok inW =>
      match member kvs "nodes" with
      | some (.array []) => errJson "graphCheckNodes: no nodes"
      | some (.array items) =>
        match items.zipIdx.mapM fun (j, i) => graphNodeOfJson i j with
        | .error e => errJson e
        | .ok ns => graphCheckNodesJson inW ns
      | _ => errJson "graphCheckNodes: nodes must be a JSON array"
  | .ok _ => errJson "graphCheckNodes: graphJson must be a JSON object"

/-! ## The op `datasetMerge` -/

/-- `datasetMerge(handle1, handle2)` (module header). The Lean name differs
from the op name, so that it does not clash with `Dataflow.datasetMerge`. -/
def datasetMergeOp (h1 h2 : String) : IO String :=
  withHandleDataset h1 fun a pa =>
  withHandleDataset h2 fun c pc => do
    let n ← documentScopeCounter.modifyGet fun k => (k, k + 2)
    storeNewHandle (mergeDatasets n a c) (mergePrefixes pa pc)

#print axioms mergeDatasets_isMerge

end L4Wasm.Ops
