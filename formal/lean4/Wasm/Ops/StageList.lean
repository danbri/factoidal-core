/-
Wasm.Ops.StageList — the `stageList` op: the stage registry of the dataflow
inventory (`L4Factoidal.Dataflow.registry`) as JSON, for the npm node API
(https://github.com/danbri/factoidal/issues/1002, step 2;
https://github.com/danbri/factoidal/issues/975).

  stageList()
    -> {"ok":true,"count":N,
        "stages":[{"name":S,"declaration":S|null,"area":S,"dir":S,
                   "kind":S|null,"wireIn":S,"wireOut":S,"params":[S],"status":S,
                   "contract":S|null,"theorems":[S],"assumptions":[S],
                   "tests":[S],"note":S,"runnable":B}]}

One element per registry entry, in registry order, read from `registry` on
each call: no second table of stages exists.

* `name`: the stage declaration relative to `L4Factoidal.Dataflow` or
  `L4Factoidal` (as `docs/dataflow-inventory.md` writes it), or the `area`
  when the entry has no declaration (status `tested` or `missing`); unique
  (checked below).
* `kind`: the interface type of the declaration (the constant at the head of
  its type: `Stage`, `RdfReader`, `SoundReasoner`, `IOStage`, ...), from the
  generated table `Dataflow/StageKinds.lean`; `null` with no declaration.
* `status`: `proved`, `tested`, `assumed` or `missing` (`Entry.statusError`
  checks that it agrees with the fields; `tools/dataflow-inventory.lean`
  checks the declarations and their axioms).
* `contract`: the contract declaration; `assumptions`: the named assumptions
  (`ioAssumptions`); full Lean names.
* `wireIn`, `wireOut`: `Wire.label` of the entry's wires
  (`Dataflow/Wire.lean`); `params`: the inputs a node supplies when it is
  made.
* `runnable`: false exactly when the status is `missing`: a stage with no
  contract and no suite is not run as a node (issue 975, item 3).

The op reads no data; foundation/entrypoints.toml lists it as a nonstage
entry (reflection).

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.Dataflow.Registry
import L4Factoidal.Dataflow.StageKinds

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.Dataflow

/-- The node name of an entry: its declaration, else its area (`Entry.nodeName`). -/
def stageEntryName (e : Entry) : String := e.nodeName

/-- The interface type of the entry's declaration, from `stageKinds`. -/
def stageEntryKind (e : Entry) : Option String :=
  if isNone e.stage then none
  else (stageKinds.lookup e.stage.toString).map stageShortName

private def nameJson (n : Lean.Name) : Json :=
  if isNone n then .null else .string n.toString

private def optJson : Option String → Json
  | some s => .string s
  | none => .null

/-- The JSON form of one registry entry. -/
def stageEntryJson (e : Entry) : Json :=
  .object
    [ ("name", .string (stageEntryName e)),
      ("declaration", nameJson e.stage),
      ("area", .string e.area),
      ("dir", .string e.dir),
      ("kind", optJson (stageEntryKind e)),
      ("wireIn", .string e.wireIn.label),
      ("wireOut", .string e.wireOut.label),
      ("params", .array (e.params.map Json.string)),
      ("status", .string e.status.label),
      ("contract", nameJson e.contract),
      ("theorems", .array (e.theorems.map (fun n => .string n.toString))),
      ("assumptions", .array (e.ioAssumptions.map (fun n => .string n.toString))),
      ("tests", .array (e.tests.map Json.string)),
      ("note", .string e.note),
      ("runnable", .bool e.runnable) ]

/-- The stage elements, one per registry entry. -/
def stageListEntries : List Json := registry.map stageEntryJson

/-- `stageList()`. -/
def stageList : String :=
  okWith [("count", .number (toString registry.length)), ("stages", .array stageListEntries)]

/-! ## pipelineCheck

  pipelineCheck(namesJson)   namesJson: a JSON array of stage names
    -> {"ok":true,"wellTyped":B,"wireIn":S|null,"wireOut":S|null,
        "mismatch":{"at":N,"out":S,"in":S}|null,
        "conversions":[{"at":N,"from":S,"to":S}],
        "assumptions":[S],
        "contract":{"theorem":S,"stages":[S|null]},
        "stages":[{"name":S,"status":S,"checked":B,"contract":S|null,
                   "assumptions":[S],"wireIn":S,"wireOut":S}]}
    -> {"ok":false,"error":S} on a name that is not a registry `name`, or
       an empty list.

Computed by `pipelineReport Wire.conv` (`Dataflow/Pipeline.lean`) over the
signatures `Entry.sig` of the named entries, in the given order:

* `wellTyped`: `wellTyped Wire.conv`, which accepts exactly the lists that
  `WellTyped` holds of (`wellTyped_iff`); `mismatch`: the first stage `at`
  whose output wire does not feed stage `at + 1`.
* `conversions`: the places where a stage's output reaches the next stage's
  input by a `Wire.conv` conversion; the composed contract names them
  (`arrive`).
* `assumptions`: `assumptionUnion`, the union of the stages' named
  assumptions, first-seen order: the premises of
  `Pipeline.guarantee_sound` for a pipeline of components with these
  signatures (`Pipeline.guarantee_assumptions`).
* `contract.theorem`: `L4Factoidal.Dataflow.Pipeline.guarantee_sound`;
  `contract.stages`: each stage's contract declaration.
* `stages[i].checked`: the status is `proved`.

The result states what a well-typed pipeline of these stages is guaranteed
under the listed assumptions. It is not a proof that the npm runners compute
the Lean stages (the RUNNERS table binding, `tools/runners-gate.py`).
-/

/-- The registry entry of a node name. -/
def entryOfName (n : String) : Option Entry := registry.find? (·.nodeName == n)

/-- The named entries in order, or the first name that is not registered. -/
def entriesOfNames (names : List String) : Except String (List Entry) :=
  names.mapM fun n =>
    match entryOfName n with
    | some e => .ok e
    | none => .error s!"pipelineCheck: no registered stage named '{n}'"

private def wireJson : Option Wire → Json
  | some w => .string w.label
  | none => .null

/-- The JSON of the check of a list of registry entries. -/
def pipelineCheckJson (es : List Entry) : String :=
  let sigs := es.map Entry.sig
  let r := pipelineReport Wire.conv sigs
  let mismatch : Json := match r.mismatch with
    | some i =>
      let out := (sigs[i]?).map (·.outW)
      let inn := (sigs[i + 1]?).map (·.inW)
      .object [("at", .number (toString i)), ("out", wireJson out), ("in", wireJson inn)]
    | none => .null
  okWith
    [ ("wellTyped", .bool r.wellTyped),
      ("wireIn", wireJson r.wireIn),
      ("wireOut", wireJson r.wireOut),
      ("mismatch", mismatch),
      ("conversions", .array (r.conversions.map fun (i, a, b) =>
        .object [("at", .number (toString i)), ("from", .string a.label), ("to", .string b.label)])),
      ("assumptions", .array (r.assumptions.map fun n => .string n.toString)),
      ("contract", .object
        [ ("theorem", .string (``Pipeline.guarantee_sound).toString),
          ("stages", .array (r.contracts.map fun c => optJson (c.map toString))) ]),
      ("stages", .array (es.map fun e =>
        .object
          [ ("name", .string e.nodeName),
            ("status", .string e.status.label),
            ("checked", .bool (e.status == .proved)),
            ("contract", nameJson e.contract),
            ("assumptions", .array (e.ioAssumptions.map fun n => .string n.toString)),
            ("wireIn", .string e.wireIn.label),
            ("wireOut", .string e.wireOut.label) ])) ]

/-- `pipelineCheck(namesJson)`. -/
def pipelineCheck (namesJson : String) : String :=
  match decodeArgs namesJson with
  | .error e => errJson s!"pipelineCheck: {e}"
  | .ok [] => errJson "pipelineCheck: no stages"
  | .ok names =>
    match entriesOfNames names with
    | .error e => errJson e
    | .ok es => pipelineCheckJson es

/-! ## Checks: the output is derived from the registry -/

private def subOf (hay needle : String) : Bool := (hay.splitOn needle).length > 1

-- one element per registry entry
#guard stageListEntries.length == registry.length
#guard subOf stageList s!"\"count\":{registry.length}"
-- node names are unique
#guard (registry.map stageEntryName).eraseDups.length == registry.length
-- every declaration has its interface type in the generated table, and the
-- table has no other row (a stale table fails here)
#guard registry.all fun e => isNone e.stage || (stageEntryKind e).isSome
#guard stageKinds.length == (registry.filter fun e => !isNone e.stage).length
#guard stageKinds.map (·.1) == (registry.filter fun e => !isNone e.stage).map (·.stage.toString)
-- an entry with no declaration has no kind
#guard registry.all fun e => !isNone e.stage || (stageEntryKind e).isNone
-- runnable iff the status is not missing
#guard registry.all fun e => e.runnable == (e.status != .missing)
-- a few rows as the npm node API reads them
#guard subOf stageList
  "\"name\":\"rdfsExplainGraphStage\",\"declaration\":\"L4Factoidal.Dataflow.rdfsExplainGraphStage\""
#guard subOf stageList "\"name\":\"rdfsReasoner\""
#guard (registry.find? (stageEntryName · == "rdfsReasoner")).bind stageEntryKind == some "SoundReasoner"
#guard (registry.find? (stageEntryName · == "turtleDocumentReader")).bind stageEntryKind == some "RdfReader"
#guard (registry.find? (stageEntryName · == "turtleDocumentWriter")).map (·.status.label) == some "assumed"
#guard (registry.filter (·.status == .missing)).all fun e => !e.runnable

-- pipelineCheck: a well-typed three-stage path with a conversion
#guard subOf (pipelineCheck "[\"turtleDocumentReader\",\"rdfsReasoner\",\"shaclValidator\"]")
  "\"wellTyped\":true"
#guard subOf (pipelineCheck "[\"turtleDocumentReader\",\"rdfsReasoner\",\"shaclValidator\"]")
  "\"conversions\":[{\"at\":0,\"from\":\"Dataset × PrefixList\",\"to\":\"Graph\"}]"
-- ill-typed: a writer's text is not a reasoner's graph
#guard subOf (pipelineCheck "[\"turtleDocumentWriter\",\"rdfsReasoner\"]") "\"wellTyped\":false"
#guard subOf (pipelineCheck "[\"turtleDocumentWriter\",\"rdfsReasoner\"]")
  "\"mismatch\":{\"at\":0,\"out\":\"String\",\"in\":\"Graph\"}"
-- the assumption union of an assumed stage is reported
#guard subOf (pipelineCheck "[\"turtleDocumentReader\",\"turtleDocumentWriter\"]")
  "\"assumptions\":[\"L4Factoidal.Dataflow.TurtleWriterRoundTrip\"]"
#guard subOf (pipelineCheck "[\"noSuchStage\"]") "\"ok\":false"
#guard subOf (pipelineCheck "[]") "\"ok\":false"

end L4Wasm.Ops
