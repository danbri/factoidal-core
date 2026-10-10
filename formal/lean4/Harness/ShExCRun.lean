/-
Harness/ShExCRun — a DIFFERENTIAL runner for the ShExC parser.

Every fixture under `third_party/testing/shex/schemas/` ships a
compact-syntax `.shex` and a ShExJ `.json` twin of the SAME schema.
This runner reads both and compares the trees.

## Why a differential and not an expectation file

A ShExC parser has no separate ground truth to check against: the
schema IS the answer. Comparing the two front doors turns the corpus
itself into the oracle, and a disagreement points at one of them
without either having to be blessed.

Four outcomes:

  * **match** — the two readers built the same tree;
  * **mismatch** — they did not, and the first differing declaration
    label is named. This is the number that means something is
    broken;
  * **declined** — the ShExC parser refused, with its message. A
    refusal is NOT a mismatch: a construct outside the implemented
    grammar is visibly unparsed, never a schema that validates the
    wrong graphs;
  * **no reference** — the JSON twin is missing or does not read, so
    there is nothing to compare against.

## The reject fixtures

`negativeSyntax/` and `negativeStructure/`, siblings of `schemas/`, hold
schemas a conforming processor must REJECT. Each directory's own
`manifest.ttl` lists them (`sht:NegativeSyntax`, 100 entries;
`sht:NegativeStructure`, 15). The manifest is read, never the
directory listing, so a fixture the manifest drops is not scored and
a fixture it names but the checkout lacks is reported MISSING.

  * negative syntax — PASS when `Compact.parseShExC` refuses the file:
    the file violates the ShExC grammar (ShEx 2.1 Appendix A);
  * negative structure — PASS when the parser refuses the file or
    `ShEx.Structure.structureErrors` reports a violation of the schema
    requirements (ShEx 2.1 §5.7: shape and triple expression
    references, the negation requirement, label collisions).

An ACCEPTED fixture is a failure, and its line names the file.

The structure check is also run over every POSITIVE schema the
parser reads, and a positive schema it rejects is a failure of the
check: an implementation that rejected everything would pass every
reject fixture.

Usage: `lake exe l4shexc [schemas-dir] [--verbose]`; `--verbose` prints
the reason each reject fixture was rejected.
-/
import L4Factoidal.ShEx.Compact
import L4Factoidal.ShEx.SchemaEq
import L4Factoidal.ShEx.FromJson
import L4Factoidal.JSON.Parser
import L4Factoidal.ShEx.Structure
import Harness.Manifest

open L4Factoidal.ShEx
open L4Factoidal.JSON

/-- One reject fixture from a ShEx test manifest: its name, its file
name, and its test type's local name. -/
structure RejectCase where
  name  : String
  file  : String
  kind  : String
deriving Inhabited

def shtNs : String := "http://www.w3.org/ns/shacl/test-suite#"
def sxNs : String := "https://shexspec.github.io/shexTest/ns#"

/-- The entries of a shexTest `manifest.ttl`, in manifest order. The
    `mf:entries` collection is walked with `Harness.collectList`, the
    W3C runner's own reader. -/
def rejectCasesOf (g : L4Factoidal.RDF.Graph) : List RejectCase :=
  let manifests := g.filter (fun t =>
    t.p.val == Harness.rdfType &&
    (match t.o with | .iri i => i.val == Harness.mfNs ++ "Manifest" | _ => false))
  manifests.flatMap (fun m =>
    let entries := (Harness.findObjects g m.s (Harness.mfNs ++ "entries")).flatMap
      (Harness.collectList g (g.length + 1))
    entries.filterMap (fun e =>
      match Harness.subjectOfTerm e with
      | none => none
      | some es =>
        let name := (Harness.findObject? g es (Harness.mfNs ++ "name")).map Harness.termKey
        let file := (Harness.findObject? g es (sxNs ++ "shex")).map
          (fun t => Harness.lastSegment (Harness.termKey t))
        let kind := (Harness.findObject? g es Harness.rdfType).map
          (fun t => Harness.lastSegment (Harness.termKey t))
        match name, file, kind with
        | some n, some f, some k => some { name := n, file := f, kind := k }
        | _, _, _ => none))

structure RejectTally where
  pass    : Nat := 0
  fail    : Nat := 0
  missing : Nat := 0
deriving Inhabited

/-- Run one reject directory. `structural` adds the §5.7 check after a
    successful parse. Prints one ACCEPTED line per failure. -/
def runRejects (dir : String) (label : String) (structural : Bool) (verbose : Bool) :
    IO (Option RejectTally) := do
  let mpath := dir ++ "/manifest.ttl"
  if !(← System.FilePath.pathExists mpath) then
    IO.println s!"shexc runner: manifest not found: {mpath}"
    return none
  let mtext ← IO.FS.readFile mpath
  match L4Factoidal.Syntax.parseTurtle mtext none with
  | .error e =>
      IO.println s!"shexc runner: manifest did not parse: {mpath}: {e}"
      return none
  | .ok g =>
    let cases := rejectCasesOf g
    if cases.isEmpty then
      IO.println s!"shexc runner: manifest parsed but named no entries: {mpath}"
      return none
    let mut t : RejectTally := {}
    for c in cases do
      let path := dir ++ "/" ++ c.file
      if !(← System.FilePath.pathExists path) then
        t := { t with missing := t.missing + 1 }
        IO.println s!"MISSING {label}/{c.name}: {c.file} is named by the manifest and absent"
      else
        let text ← IO.FS.readFile path
        let verdict : Option String :=
          match Compact.parseShExC text with
          | .error e => some ("parser: " ++ e)
          | .ok sch =>
            if structural then
              match Structure.structureErrors sch with
              | e :: _ => some ("structure: " ++ e)
              | []     => none
            else none
        match verdict with
        | some why =>
            t := { t with pass := t.pass + 1 }
            if verbose then IO.println s!"REJECTED {label}/{c.name}: {why}"
        | none =>
            t := { t with fail := t.fail + 1 }
            IO.println s!"ACCEPTED {label}/{c.name}: a {c.kind} fixture was accepted"
    return some t

/-- The file names, under `schemas/`, of the schemas the validation
    manifest (`validation/manifest.jsonld`) validates against: the
    distinct `action.schema` values, which the suite writes as
    `../schemas/<file>.shex`. -/
def validationSchemaFiles (manifestPath : String) : IO (List String) := do
  if !(← System.FilePath.pathExists manifestPath) then
    IO.println s!"shexc runner: validation manifest not found: {manifestPath}"
    return []
  let fld? (k : String) : Json → Option Json := fun j =>
    match j with
    | .object ms => (ms.find? (fun (key, _) => key == k)).map (·.2)
    | _ => none
  match parseJson? (← IO.FS.readFile manifestPath) with
  | none => return []
  | some j =>
    let graphs := match fld? "@graph" j with
      | some (.array gs) => gs
      | _ => [j]
    let entries := graphs.flatMap (fun g => match fld? "entries" g with
      | some (.array es) => es
      | _ => [])
    let files := entries.filterMap (fun e =>
      match (fld? "action" e).bind (fld? "schema") with
      | some (.string sp) => some (Harness.lastSegment sp)
      | _ => none)
    return files.foldl (fun acc f => if acc.contains f then acc else acc ++ [f]) []

/-- A schema with its IMPORTs read from `dir` and merged in: ShEx 2.1
    §5.2, imported documents contribute their shape declarations, and
    the importer's own declarations and `start` win. An import names a
    document relative to the importer; the suite's files are its stem
    plus `.shex`. Bounded by the number of distinct imports seen. -/
def importClosure (dir : String) (sch : Schema) : IO Schema := do
  let stemOf (i : String) : String :=
    let seg := Harness.lastSegment i
    if seg.endsWith ".shex" || seg.endsWith ".json" then String.ofList (seg.toList.take (seg.length - 5))
    else seg
  let mut acc := sch
  let mut pending := sch.imports
  let mut seen : List String := []
  for _ in [0:256] do
    match pending with
    | [] => pure ()
    | imp :: rest =>
      pending := rest
      let stem := stemOf imp
      if !(seen.contains stem) then
        seen := seen ++ [stem]
        let p := dir ++ "/" ++ stem ++ ".shex"
        if ← System.FilePath.pathExists p then
          match Compact.parseShExC (← IO.FS.readFile p) with
          | .ok inner =>
              acc := { acc with
                start := acc.start.orElse (fun _ => inner.start)
                shapes := acc.shapes ++ inner.shapes.filter (fun d =>
                  !(acc.shapes.any (fun o => o.id == d.id))) }
              pending := pending ++ inner.imports
          | .error _ => pure ()
  return { acc with imports := if pending.isEmpty then [] else pending }

structure Tally where
  match'   : Nat := 0
  mismatch : Nat := 0
  declined : Nat := 0
  noRef    : Nat := 0
deriving Inhabited

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "--verbose"
  let dir := (args.filter (fun a => !a.startsWith "--")).head? |>.getD "third_party/testing/shex/schemas"
  if !(← System.FilePath.pathExists dir) then
    IO.println s!"shexc runner: directory not found: {dir}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let entries ← System.FilePath.readDir dir
  let names := ((entries.toList.map (fun e => e.fileName)).filter
    (fun n => n.endsWith ".shex")).toArray.qsort (· < ·) |>.toList
  let mut t : Tally := {}
  let mut reasons : List String := []
  for n in names do
    let stem := String.ofList (n.toList.take (n.length - 5))
    let jsonPath := dir ++ "/" ++ stem ++ ".json"
    let shexText ← IO.FS.readFile (dir ++ "/" ++ n)
    if !(← System.FilePath.pathExists jsonPath) then
      t := { t with noRef := t.noRef + 1 }
    else
      let jsonText ← IO.FS.readFile jsonPath
      match (parseJson? jsonText).bind schemaOf with
      | none =>
          t := { t with noRef := t.noRef + 1 }
      | some ref =>
        match Compact.parseShExC shexText with
        | .error e =>
            t := { t with declined := t.declined + 1 }
            reasons := reasons ++ [e]
            IO.println s!"DECLINED {stem}: {e}"
        | .ok got =>
            if schemaEq got ref then t := { t with match' := t.match' + 1 }
            else
              t := { t with mismatch := t.mismatch + 1 }
              let where' := (firstDiff got ref).getD "<unknown>"
              IO.println s!"MISMATCH {stem}: first difference at {where'} \
(ShExC has {got.shapes.length} shape(s), ShExJ has {ref.shapes.length})"
              -- `SHEXC_DUMP=<stem>` prints both trees. A label alone
              -- says WHICH declaration differs, never HOW, and the
              -- difference is usually one field deep inside it.
              if (← IO.getEnv "SHEXC_DUMP") == some stem then
                IO.println s!"  ShExC: {repr got.shapes}"
                IO.println s!"  ShExJ: {repr ref.shapes}"
  let compared := t.match' + t.mismatch
  IO.println ""
  IO.println s!"ShExC DIFFERENTIAL: {t.match'} match, {t.mismatch} mismatch \
(out of {compared} compared)"
  IO.println s!"DECLINED: {t.declined} schemas the parser refused"
  IO.println s!"NO REFERENCE: {t.noRef} schemas whose ShExJ twin is missing or unreadable"
  IO.println s!"  (out of {names.length} .shex files)"
  -- Which refusals, and how many of each: one reason repeated a
  -- hundred times and a hundred one-off reasons call for very
  -- different next pieces of work.
  let uniq := reasons.eraseDups
  if !uniq.isEmpty then
    IO.println ""
    IO.println "Refusal reasons, by frequency:"
    let counted := (uniq.map (fun r => ((reasons.filter (· == r)).length, r))).toArray.qsort
      (fun a b => a.1 > b.1) |>.toList
    for (k, r) in counted.take 25 do
      IO.println s!"  {k}x  {r}"
    if counted.length > 25 then
      IO.println s!"  … and {counted.length - 25} more reasons"
  IO.println ""
  IO.println "A DECLINED schema is counted apart, never as a mismatch: a"
  IO.println "construct outside the implemented grammar is visibly unparsed,"
  IO.println "never a schema that validates the wrong graphs."
  -- The reject fixtures, beside `schemas/`.
  let root := ((System.FilePath.mk dir).parent.map (·.toString)).getD "."
  IO.println ""
  let neg ← runRejects (root ++ "/negativeSyntax") "negativeSyntax" false verbose
  let str ← runRejects (root ++ "/negativeStructure") "negativeStructure" true verbose
  -- The structure check must not reject a schema the suite treats as
  -- valid: every schema the VALIDATION manifest validates against,
  -- with its imports closure. A bare `schemas/` file is not enough:
  -- `2RefS1.shex` references `S2`, which only the documents that
  -- IMPORT it declare, so on its own it fails §5.7.2 — and it is a
  -- syntax fixture, never a validation schema.
  let roots ← validationSchemaFiles (root ++ "/validation/manifest.jsonld")
  let mut falseRejects : Nat := 0
  let mut checked : Nat := 0
  for n in roots do
    let path := dir ++ "/" ++ n
    if ← System.FilePath.pathExists path then
      match Compact.parseShExC (← IO.FS.readFile path) with
      | .error _ => pure ()
      | .ok sch =>
          checked := checked + 1
          let closed ← importClosure dir sch
          match Structure.structureErrors closed with
          | [] => pure ()
          | e :: _ =>
              falseRejects := falseRejects + 1
              IO.println s!"OVER-STRICT schemas/{n}: the structure check rejects a validation schema: {e}"
  IO.println ""
  match neg with
  | some r =>
      IO.println s!"shexc negative-syntax: {r.pass} pass, {r.fail} fail, {r.missing} missing \
(out of {r.pass + r.fail + r.missing})"
  | none => IO.println "shexc negative-syntax: not measured (manifest not read)"
  match str with
  | some r =>
      IO.println s!"shexc negative-structure: {r.pass} pass, {r.fail} fail, {r.missing} missing \
(out of {r.pass + r.fail + r.missing})"
  | none => IO.println "shexc negative-structure: not measured (manifest not read)"
  IO.println s!"shexc structure check on validation schemas: {checked - falseRejects} pass, \
{falseRejects} fail (out of {checked} parsed; the manifest names {roots.length})"
  IO.println "  (pass = a reject fixture is rejected, or a validation schema is not)"
  let negFails := (neg.map (fun r => r.fail + r.missing)).getD 1 +
                  (str.map (fun r => r.fail + r.missing)).getD 1
  return (if t.mismatch > 0 || negFails > 0 || falseRejects > 0 then 1 else 0)
