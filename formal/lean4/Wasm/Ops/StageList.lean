/-
Wasm.Ops.StageList — the `stageList` op: the stage registry of the dataflow
inventory (`L4Factoidal.Dataflow.registry`) as JSON, for the npm node API
(https://github.com/danbri/factoidal/issues/1002, step 2;
https://github.com/danbri/factoidal/issues/975).

  stageList()
    -> {"ok":true,"count":N,
        "stages":[{"name":S,"declaration":S|null,"area":S,"dir":S,
                   "kind":S|null,"wireIn":S,"wireOut":S,"status":S,
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

private def dropPrefix (pre s : String) : Option String :=
  if s.startsWith pre then some (String.ofList (s.toList.drop pre.length)) else none

/-- A declaration name relative to `L4Factoidal.Dataflow` or `L4Factoidal`. -/
def stageShortName (s : String) : String :=
  (dropPrefix "L4Factoidal.Dataflow." s).getD ((dropPrefix "L4Factoidal." s).getD s)

/-- The node name of an entry: its declaration, else its area. -/
def stageEntryName (e : Entry) : String :=
  if isNone e.stage then e.area else stageShortName e.stage.toString

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
      ("wireIn", .string e.wireIn),
      ("wireOut", .string e.wireOut),
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

end L4Wasm.Ops
