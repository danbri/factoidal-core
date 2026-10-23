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
* a status disagrees with its fields: `proved` needs a `Stage` value, a
  contract and theorems; `assumed` needs an `IOStage` value and an IO
  assumption; `tested` needs a suite and no stage; `missing` has no stage, no
  contract and no suite.

Output: one line per entry between `BEGIN-INVENTORY` and `END-INVENTORY`,
fields separated by a tab: area, dir, stage, wire in, wire out, contract,
status, theorems, IO assumptions, tests, note.
-/
import Lean
import L4Factoidal.Dataflow.Registry

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

#eval show CommandElabM Unit from do
  let env ← getEnv
  if registry.isEmpty then
    throwError "dataflow registry is empty"
  let mut errs : Array String := #[]
  for e in registry do
    let named := ([e.stage, e.contract] ++ e.theorems ++ e.ioAssumptions).filter (fun n => !n.isAnonymous)
    for n in named do
      if !env.contains n then
        errs := errs.push s!"{e.area}: unknown declaration {n}"
      else
        let axs ← liftCoreM (collectAxioms n)
        for a in axs do
          if !allowedAxioms.contains a then
            errs := errs.push s!"{e.area}: {n} depends on axiom {a}"
    match e.status with
    | .proved =>
      if e.stage.isAnonymous || e.contract.isAnonymous || e.theorems.isEmpty then
        errs := errs.push s!"{e.area}: proved needs a stage, a contract and theorems"
      else if resultHead env e.stage != some ``Stage then
        errs := errs.push s!"{e.area}: {e.stage} is not a Stage"
    | .assumed =>
      if e.ioAssumptions.isEmpty then
        errs := errs.push s!"{e.area}: assumed needs a named IO assumption"
      else if resultHead env e.stage != some ``IOStage then
        errs := errs.push s!"{e.area}: {e.stage} is not an IOStage"
    | .tested =>
      if e.tests.isEmpty || !e.stage.isAnonymous then
        errs := errs.push s!"{e.area}: tested needs a suite and no stage"
    | .missing =>
      if !e.stage.isAnonymous || !e.contract.isAnonymous || !e.tests.isEmpty then
        errs := errs.push s!"{e.area}: missing has no stage, no contract and no suite"
  if !errs.isEmpty then
    throwError "dataflow registry check failed:\n{"\n".intercalate errs.toList}"
  IO.println "BEGIN-INVENTORY"
  for e in registry do
    let fields := [e.area, e.dir, nameField e.stage, e.wireIn, e.wireOut, nameField e.contract,
      e.status.label, listField (e.theorems.map Name.toString),
      listField (e.ioAssumptions.map Name.toString), listField e.tests, e.note]
    IO.println ("\t".intercalate (fields.map clean))
  IO.println "END-INVENTORY"
