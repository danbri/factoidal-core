/-
Harness/RmlRun — the RML-Core test cases, run end to end.

Each case is a directory holding `mapping.ttl`, its source document,
and `output.nq`. The runner reads the mapping AS RDF (the Lean Turtle
parser), runs it with `RML.Eval`, and compares the result with the
expected N-Quads.

## The comparison is one graph isomorphism over the whole DATASET

A dataset is not a bag of graphs that can be compared one at a time: a
blank node may appear in the default graph and in a named one, and
comparing each graph on its own would let two different datasets
match. Every quad is encoded as a TRIPLE whose predicate carries the
graph name — `urn:x-rml-quad:<graph>:<predicate>`, both parts
percent-encoded so the encoding is injective — and the two encoded
graphs are compared once. Blank nodes then have to line up ACROSS
graphs, which is what dataset isomorphism means.

## Outcomes

  * **pass / fail** — for a positive case, the datasets matched or they
    did not; for a NEGATIVE case (`error=true` in the corpus's own
    metadata), the mapping was rejected or it was accepted;
  * **comparison gave up** — the isomorphism search hit its budget.
    Counted apart from a failure, because it is not evidence the two
    differ;
  * **fixture defect** — the case's own expected output cannot be read
    (`RMLTC0027b` writes an IRI with a space in `output.nq`). Named,
    counted, and not folded into pass or fail.

## Negative cases

A negative case has no expected output; the correct outcome is that the
processor REJECTS the mapping. The runner calls the library's
`runMappingGraph`, which validates the mapping graph (`RML.Validate`) and
then evaluates it (`RML.Eval`), and counts the case as passed when either
step rejects it. A mapping document that is not valid Turtle cannot be a
mapping graph at all, and that is a rejection too; it is counted
separately in the breakdown line so the number is not hidden inside
"pass".

Usage: `lake exe l4rml [test-cases-dir]`
-/
import L4Factoidal.RML.Eval
import L4Factoidal.RML.Run
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.JSON.Parser
import L4Factoidal.CSVW.Dialect
import Harness.Fixtures

open L4Factoidal.RML
open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- Percent-encode everything but the RFC 3986 unreserved set, so the
    encoding of a (graph, predicate) pair is injective. -/
def enc (s : String) : String :=
  let hex := fun (n : Nat) =>
    if n < 10 then Char.ofNat ('0'.toNat + n) else Char.ofNat ('A'.toNat + n - 10)
  s.toList.foldl (fun acc c =>
    if ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || ('0' ≤ c && c ≤ '9')
       || c == '-' || c == '.' || c == '_' || c == '~'
    then acc ++ String.mk [c]
    else acc ++ String.ofList ((String.mk [c]).toUTF8.toList.flatMap (fun b =>
           ['%', hex (b.toNat / 16), hex (b.toNat % 16)]))) ""

def quadPred (g : Option String) (p : String) : Option WfIri :=
  let raw := "urn:x-rml-quad:" ++ (match g with | none => "" | some x => enc x) ++ ":" ++ enc p
  if h : isIri raw then some ⟨raw, h⟩ else none

/-- A dataset as ONE graph, with the graph name folded into each
    predicate. -/
def flattenDataset (ds : Dataset) : Graph :=
  let dflt := ds.default.filterMap (fun t =>
    (quadPred none t.p.val).map (fun p => ({ s := t.s, p := p, o := t.o } : Triple)))
  let named := ds.named.flatMap (fun ng =>
    let n := match ng.name with
      | .iri i   => i.val
      | .bnode b => "_:" ++ b
    ng.graph.filterMap (fun t =>
      (quadPred (some n) t.p.val).map (fun p => ({ s := t.s, p := p, o := t.o } : Triple))))
  dflt ++ named

def flattenQuads (qs : List QuadOut) : Graph :=
  qs.filterMap (fun q =>
    let n := q.g.map (fun t => match t with
      | .iri i   => i.val
      | .bnode b => "_:" ++ b
      | _        => "")
    (quadPred n q.p.val).map (fun p => ({ s := q.s, p := p, o := q.o } : Triple)))

/-- One row of the corpus's own `metadata.csv`: the base IRI a case
    runs under, and whether it is a NEGATIVE case.

    A negative case has no `output.nq`, and reading that absence as
    "the file is missing" would report a deliberate part of the suite
    as a broken fixture. -/
structure CaseMeta where
  id      : String
  baseIri : String
  isError : Bool
deriving Inhabited

def readMetadata (src : String) : List CaseMeta :=
  let t := L4Factoidal.CSVW.read (({} : L4Factoidal.CSVW.Dialect).resolve) src
  let hdr := (t.header.head?.map (·.cells)).getD []
  let idx := fun (n : String) => hdr.findIdx? (· == n)
  match idx "ID", idx "base_iri", idx "error" with
  | some i, some b, some e =>
      t.rows.map (fun r =>
        { id := (r.cells.getD i ""), baseIri := (r.cells.getD b ""),
          isError := (r.cells.getD e "") == "true" })
  | _, _, _ => []

structure Tally where
  pass    : Nat := 0
  fail    : Nat := 0
  gaveUp  : Nat := 0
  /-- A case whose expected output is unreadable: a fixture defect. -/
  fixtureDefect : Nat := 0
  /-- A mapping or expected output that did not parse for a reason that
      is not a fixture defect. -/
  notRead : Nat := 0
  /-- Of the negative cases that passed: rejected because the mapping
      document is not Turtle, by validation, by evaluation. -/
  rejParse : Nat := 0
  rejValid : Nat := 0
  rejEval  : Nat := 0
deriving Inhabited

/-- The rejection reasons of a run, one per line, for a human. -/
def renderErrors (es : List RmlError) : String :=
  String.intercalate "\n" (es.take 3 |>.map (fun e => "    " ++ e.render))

/-- Read every JSON document in a case directory, by file name:
    `rml:path` is relative to the mapping, and reading them all keeps
    the evaluator a pure function of its inputs. -/
def readJsonDocs (caseDir : String) : IO (List (String × Json)) := do
  let mut docs : List (String × Json) := []
  for e in (← System.FilePath.readDir caseDir) do
    if e.fileName.endsWith ".json" then
      let src ← IO.FS.readFile e.path.toString
      match parseJson? src with
      | none   => pure ()
      | some j => docs := docs ++ [(e.fileName, j)]
  return docs

def docForOf (docs : List (String × Json)) : String → Option Json := fun p =>
  let base := ((p.splitOn "/").getLast?).getD p
  (docs.find? (fun (n, _) => n == base)).map (·.2)

/-- Run one module of the corpus. -/
def runCoreModule (dir : String) (dump : Option String) (verbose : Bool) : IO Tally := do
  let metaPath := dir ++ "/metadata.csv"
  let metaRows : List CaseMeta ← if ← System.FilePath.pathExists metaPath
             then do let src ← IO.FS.readFile metaPath; pure (readMetadata src)
             else pure []
  let mut t : Tally := {}
  let mut names : List String := []
  for entry in (← System.FilePath.readDir dir) do
    if ← System.FilePath.isDir entry.path then
      names := names ++ [entry.fileName]
  for name in names.mergeSort (· ≤ ·) do
    let caseDir := dir ++ "/" ++ name
    let mp := caseDir ++ "/mapping.ttl"
    let op := caseDir ++ "/output.nq"
    let m? := metaRows.find? (fun c => c.id == name)
    if !(← System.FilePath.pathExists mp) then pure ()
    else if (m?.map (·.isError)).getD false then
      -- A NEGATIVE case: the corpus's own metadata says the mapping
      -- is invalid, and there is no expected output because the
      -- correct outcome is an ERROR. It passes when the mapping is
      -- rejected, by the Turtle parser, by validation or by evaluation.
      let msrc ← IO.FS.readFile mp
      match parseTurtle msrc none with
      | .error e =>
          t := { t with pass := t.pass + 1, rejParse := t.rejParse + 1 }
          if verbose then IO.println s!"rejected {name} (Turtle parser): {e.msg}"
      | .ok mg =>
          let docs ← readJsonDocs caseDir
          let defaultBase := (m?.map (·.baseIri)).filter (fun b => b != "")
          let static := validateMapping mg
          if !static.isEmpty then
            t := { t with pass := t.pass + 1, rejValid := t.rejValid + 1 }
            if verbose then IO.println s!"rejected {name} (validation):\n{renderErrors static}"
          else
            let r := runMappingGraph mg defaultBase (docForOf docs)
            if r.rejected then
              t := { t with pass := t.pass + 1, rejEval := t.rejEval + 1 }
              if verbose then IO.println s!"rejected {name} (evaluation):\n{renderErrors r.errors}"
            else
              t := { t with fail := t.fail + 1 }
              IO.println s!"FAIL {name}: the mapping must be rejected and was accepted ({r.quads.length} quads)"
    else if !(← System.FilePath.pathExists op) then
      t := { t with notRead := t.notRead + 1 }
      IO.println s!"no expected output and the metadata does not call it an error: {name}"
    else
      let msrc ← IO.FS.readFile mp
      let osrc ← IO.FS.readFile op
      match parseTurtle msrc none, parseNQuads osrc with
      | .error e, _ =>
          t := { t with notRead := t.notRead + 1 }
          IO.println s!"NOT READ {name}: the mapping did not parse ({e.msg})"
      | _, .error _ =>
          t := { t with fixtureDefect := t.fixtureDefect + 1 }
          IO.println (s!"FIXTURE DEFECT {name}: the expected N-Quads do not parse. " ++
            "RMLTC0027b's output.nq writes <http://example.com/Person/Emily Smith>, " ++
            "and an IRIREF may not contain a space.")
      | .ok mg, .ok want =>
          let docs ← readJsonDocs caseDir
          let defaultBase := (m?.map (·.baseIri)).filter (fun b => b != "")
          let r := runMappingGraph mg defaultBase (docForOf docs)
          let got := flattenQuads r.quads
          let wantG := flattenDataset want
          if dump == some name then
            IO.println s!"--- {name} PRODUCED {got.length} ---"
            for l in ((got.map (fun x => (Graph.toNTriples [x]).toOption.getD "")).mergeSort (· ≤ ·)) do
              IO.println l.trim
            IO.println s!"--- {name} EXPECTED {wantG.length} ---"
            for l in ((wantG.map (fun x => (Graph.toNTriples [x]).toOption.getD "")).mergeSort (· ≤ ·)) do
              IO.println l.trim
          if r.rejected then
            t := { t with fail := t.fail + 1 }
            IO.println s!"FAIL {name}: a valid mapping was rejected\n{renderErrors r.errors}"
          else
            match Graph.isomorphicOutcome got wantG with
            | .equal          => t := { t with pass := t.pass + 1 }
            | .budgetExceeded =>
                t := { t with gaveUp := t.gaveUp + 1 }
                IO.println s!"GAVE UP {name}: the isomorphism search hit its budget"
            | .notEqual =>
                t := { t with fail := t.fail + 1 }
                IO.println s!"FAIL {name}: produced {got.length}, expected {wantG.length}"
  return t

/-- The score line the scoreboard reads: counts, then `(out of T)`. -/
def scoreLine (dir : String) (t : Tally) : String :=
  let total := t.pass + t.fail + t.gaveUp + t.fixtureDefect + t.notRead
  s!"{dir}: {t.pass} pass, {t.fail} fail, {t.gaveUp} comparison gave up, " ++
  s!"{t.fixtureDefect} fixture defect, {t.notRead} not read (out of {total})"

def main (args : List String) : IO UInt32 := do
  let dump := (args.find? (fun a => a.startsWith "--dump=")).map
    (fun a => String.ofList (a.toList.drop 7))
  let explicit := (args.filter (fun a => !a.startsWith "--")).head?
  let dirs : List String ← match explicit with
    | some d => pure [d]
    | none   => do
        let c ← Harness.fixtureArgOr none "third_party/testing/rml-modules/rml-core/test-cases"
        pure [c]
  let mut anyFail := false
  for dir in dirs do
    if !(← System.FilePath.isDir dir) then
      IO.println s!"rml runner: corpus not found: {dir}"
      IO.println "run tools/ensure-test-env.sh from the repository root first"
      return 1
    let t ← runCoreModule dir dump (args.contains "--verbose")
    IO.println ""
    IO.println (scoreLine dir t)
    IO.println s!"  negative cases rejected: {t.rejParse} by the Turtle parser, {t.rejValid} by validation, {t.rejEval} by evaluation"
    if t.fail > 0 then anyFail := true
  IO.println ""
  IO.println "Comparison is DATASET isomorphism: every quad is encoded as a"
  IO.println "triple carrying its graph name, so blank nodes must line up"
  IO.println "across graphs. A comparison that gives up is counted apart from"
  IO.println "a failure -- it is not evidence the two datasets differ."
  return (if anyFail then 1 else 0)
