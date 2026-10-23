/-
L4Factoidal.Dataflow.RegistryTests — negative checks of the inventory report
(https://github.com/danbri/factoidal/issues/975): an entry whose status
disagrees with its fields must stop the report.

* `negativeRegistry`: one entry per disagreement. Each names declarations that
  exist, so only the status rule can reject it.
* The `#guard`s below check `Entry.statusError` on each entry, with the kind of
  its `stage` given by hand (the report computes it from the environment).
* `tests/dataflow/run.sh` runs the report program on `negativeRegistry`
  (`DATAFLOW_REGISTRY=negative`) and requires exit 1 with an error line for
  every entry.

No executable imports this module.
-/
import L4Factoidal.Dataflow.Registry

namespace L4Factoidal.Dataflow

/-- Entries whose status disagrees with their fields; `area` starts with
`negative N:` so the test can find each error line. -/
def negativeRegistry : List Entry := [
  -- proved with no theorems
  { area := "negative 1: proved, no theorems", dir := "Dataflow", stage := ``decodeStage
    wireIn := "Document", wireOut := "RdfFormat × String", contract := ``DecodeContract
    status := .proved },
  -- proved, but the stage is an IOStage
  { area := "negative 2: proved, stage is an IOStage", dir := "Dataflow", stage := ``sbm11Disk
    wireIn := "FileGen", wireOut := "FileGen", contract := ``ReadsWritten, status := .proved
    theorems := [``Stage.comp_ok] },
  -- assumed, but the stage is a Stage
  { area := "negative 3: assumed, stage is a Stage", dir := "Dataflow", stage := ``decodeStage
    wireIn := "Document", wireOut := "RdfFormat × String", status := .assumed
    ioAssumptions := [``ReadsWritten] },
  -- assumed with no named assumption
  { area := "negative 4: assumed, no IO assumption", dir := "Dataflow", stage := ``sbm11Disk
    wireIn := "FileGen", wireOut := "FileGen", status := .assumed },
  -- tested with a stage
  { area := "negative 5: tested, with a stage", dir := "Dataflow", stage := ``decodeStage
    wireIn := "Document", wireOut := "RdfFormat × String", status := .tested
    tests := ["a suite"] },
  -- tested with no suite
  { area := "negative 6: tested, no suite", dir := "Dataflow"
    wireIn := "Document", wireOut := "Dataset", status := .tested },
  -- missing with a contract
  { area := "negative 7: missing, with a contract", dir := "Dataflow"
    wireIn := "Document", wireOut := "Dataset", contract := ``DecodeContract, status := .missing },
  -- missing with a suite
  { area := "negative 8: missing, with a suite", dir := "Dataflow"
    wireIn := "Document", wireOut := "Dataset", status := .missing, tests := ["a suite"] },
  -- proved, but the stage is not a stage of either kind
  { area := "negative 9: proved, stage is a theorem", dir := "Dataflow"
    stage := ``documentToWhere_sound, wireIn := "Document", wireOut := "WhereOut"
    contract := ``documentToWhere_sound, status := .proved, theorems := [``documentToWhere_sound] }
]

/-- The kind of the `stage` of each negative entry, as the report computes it. -/
def negativeKinds : List StageKind :=
  [.stage, .ioStage, .stage, .ioStage, .stage, .none, .none, .none, .other]

#guard negativeRegistry.length == negativeKinds.length
-- every negative entry is rejected by the status rule
#guard (negativeRegistry.zip negativeKinds).all fun (e, k) => (e.statusError k).isSome

/-- Entries that agree with their fields, with the kind of their stage. -/
def positiveEntries : List (Entry × StageKind) := [
  ({ area := "ok proved", dir := "Dataflow", stage := ``decodeStage, wireIn := "", wireOut := ""
     contract := ``DecodeContract, status := .proved, theorems := [``fromUTF8?_toUTF8] }, .stage),
  ({ area := "ok assumed", dir := "Dataflow", stage := ``sbm11Disk, wireIn := "", wireOut := ""
     status := .assumed, ioAssumptions := [``ReadsWritten] }, .ioStage),
  ({ area := "ok tested", dir := "Syntax", wireIn := "", wireOut := "", status := .tested
     tests := ["W3C"] }, .none),
  ({ area := "ok missing", dir := "OWL", wireIn := "", wireOut := "", status := .missing }, .none)
]

-- the rule accepts entries that agree with their fields
#guard positiveEntries.all fun (e, k) => (e.statusError k).isNone

end L4Factoidal.Dataflow
