/-
tools/dataflow-inventory.lean — the report program of the dataflow inventory
(https://github.com/danbri/factoidal/issues/975, phase A3).

Run from `formal/lean4` by `tools/dataflow-inventory.py`:
`lake env lean ../../tools/dataflow-inventory.lean`. It elaborates against the
built library, so every row comes from `L4Factoidal.Dataflow.registry` as the
sources define it on this run. It stops with an error (exit 1) when:

* the registry is empty;
* a named declaration does not exist;
* a named declaration depends on an axiom other than propext,
  Classical.choice, Quot.sound (`sorryAx` included);
* a status disagrees with its fields (`Entry.statusError` in
  `Dataflow/Registry.lean`): `proved` needs a `Stage` (or `RdfReader`) value, a contract and
  theorems; `assumed` needs an `IOStage` value and an IO assumption; `tested`
  needs a suite, no stage and no contract; `missing` has no stage, no
  contract, no suite and no IO assumption.

With `DATAFLOW_REGISTRY=negative` it checks `negativeRegistry`
(`Dataflow/RegistryTests.lean`) instead; every entry there must stop it
(`tests/dataflow/run.sh`).

Output: one line per entry between `BEGIN-INVENTORY` and `END-INVENTORY`,
fields separated by a tab: area, dir, stage, wire in, wire out, contract,
status, theorems, IO assumptions, tests, note.
-/
import Lean
import L4Factoidal.Dataflow.Registry
import L4Factoidal.Dataflow.RegistryTests

open Lean Elab Command
open L4Factoidal.Dataflow

def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

def nameField (n : Name) : String := if n.isAnonymous then "" else n.toString

def listField (xs : List String) : String := ", ".intercalate xs

/-- The constant at the head of the result type of a declaration. -/
def resultHead (env : Environment) (n : Name) : Option Name := do
  let ci ← env.find? n
  ci.type.getForallBody.getAppFn.constName?

def clean (s : String) : String := (s.replace "\t" " ").replace "\n" " "

/-- The kind of the declaration a `stage` field names. -/
def stageKind (env : Environment) (n : Name) : StageKind :=
  if n.isAnonymous then .none
  else match resultHead env n with
    | some h =>
      -- an interface type (`RdfReader`, `SoundReasoner`, `LawfulValidator`,
      -- `SoundChecker`) holds its contract as a field, as a `Stage` does;
      -- so do the data-access interface types (Dataflow/Store.lean)
      if h == ``Stage || h == ``RdfReader || h == ``SoundReasoner ||
          h == ``LawfulValidator || h == ``SoundChecker then .stage
      else if h == ``LawfulStore || h == ``LawfulDataset then .iface
      else if h == ``RdfWriter then .writer
      else if h == ``IOStage then .ioStage else .other
    | Option.none => .other

#eval show CommandElabM Unit from do
  let env ← getEnv
  -- `DATAFLOW_REGISTRY=negative`: the entries of `RegistryTests.lean`, each of
  -- which must stop the report (tests/dataflow/run.sh)
  let which ← (IO.getEnv "DATAFLOW_REGISTRY" : IO (Option String))
  let entries := if which == some "negative" then negativeRegistry else registry
  if entries.isEmpty then
    throwError "dataflow registry is empty"
  let mut errs : Array String := #[]
  for e in entries do
    let named := ([e.stage, e.contract] ++ e.theorems ++ e.ioAssumptions).filter (fun n => !n.isAnonymous)
    for n in named do
      if !env.contains n then
        errs := errs.push s!"{e.area}: unknown declaration {n}"
      else
        let axs ← liftCoreM (collectAxioms n)
        for a in axs do
          if !allowedAxioms.contains a then
            errs := errs.push s!"{e.area}: {n} depends on axiom {a}"
    match e.statusError (stageKind env e.stage) with
    | some why => errs := errs.push s!"{e.area}: {why}"
    | Option.none => pure ()
  if !errs.isEmpty then
    throwError "dataflow registry check failed:\n{"\n".intercalate errs.toList}"
  IO.println "BEGIN-INVENTORY"
  for e in entries do
    let fields := [e.area, e.dir, nameField e.stage, e.wireIn, e.wireOut, nameField e.contract,
      e.status.label, listField (e.theorems.map Name.toString),
      listField (e.ioAssumptions.map Name.toString), listField e.tests, e.note]
    IO.println ("\t".intercalate (fields.map clean))
  IO.println "END-INVENTORY"
