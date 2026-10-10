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
import L4Factoidal.RML.Open
import L4Factoidal.RML.Targets
import L4Factoidal.RML.Star
import L4Factoidal.RML.Functions
import L4Factoidal.RML.SparqlSource
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

/-- One row of a module's own `metadata.csv`: the base IRI a case runs
    under (rml-core only), whether it is a NEGATIVE case, and the name of
    its expected output file.

    A negative case has no expected output, and reading that absence as
    "the file is missing" would report a deliberate part of the suite
    as a broken fixture. -/
structure CaseMeta where
  id      : String
  baseIri : String
  isError : Bool
  output1 : String
deriving Inhabited

def readMetadata (src : String) : List CaseMeta :=
  let t := L4Factoidal.CSVW.read (({} : L4Factoidal.CSVW.Dialect).resolve) src
  let hdr := (t.header.head?.map (·.cells)).getD []
  let idx := fun (n : String) => hdr.findIdx? (· == n)
  match idx "ID", idx "error" with
  | some i, some e =>
      t.rows.map (fun r =>
        { id := (r.cells.getD i ""),
          baseIri := match idx "base_iri" with | some b => r.cells.getD b "" | none => "",
          isError := (r.cells.getD e "") == "true",
          output1 := match idx "output1" with | some o => r.cells.getD o "" | none => "" })
  | _, _ => []

/-- Cases that are not scored as pass or fail, in a bucket, each with
    its own reason. -/
structure Unattempted where
  bucket : String
  /-- One entry per case: its id and why. -/
  cases  : List (String × String)
deriving Inhabited

structure Tally where
  pass    : Nat := 0
  fail    : Nat := 0
  gaveUp  : Nat := 0
  /-- Cases not scored, by bucket. -/
  buckets : List Unattempted := []
  /-- Of the negative cases that passed: rejected because the mapping
      document is not Turtle, by validation, by evaluation. -/
  rejParse : Nat := 0
  rejValid : Nat := 0
  rejEval  : Nat := 0
deriving Inhabited

def Tally.addBucket (t : Tally) (bucket reason id : String) : Tally :=
  match t.buckets.find? (fun b => b.bucket == bucket) with
  | some _ =>
      { t with buckets := t.buckets.map (fun b =>
          if b.bucket == bucket then { b with cases := b.cases ++ [(id, reason)] } else b) }
  | none => { t with buckets := t.buckets ++ [{ bucket := bucket, cases := [(id, reason)] }] }

def Tally.unattempted (t : Tally) : Nat := (t.buckets.map (·.cases.length)).foldl (· + ·) 0

/-- The rejection reasons of a run, one per line, for a human. -/
def renderErrors (es : List RmlError) : String :=
  String.intercalate "\n" (es.take 3 |>.map (fun e => "    " ++ e.render))

/-- Every file of a case directory, by file name. The files are what
    `rml:path` names: relative to the mapping, which is also the working
    directory the corpus assumes. -/
def readCaseFiles (caseDir : String) : IO (List (String × ByteArray)) := do
  let mut files : List (String × ByteArray) := []
  for e in (← System.FilePath.readDir caseDir) do
    if !(← System.FilePath.isDir e.path) then
      files := files ++ [(e.fileName, ← IO.FS.readBinFile e.path)]
  return files

def baseName (p : String) : String := ((p.splitOn "/").getLast?).getD p

/-- The seam to the file system the library asks for: a path, whatever
    its root, names a file of the case directory by its last component. -/
def fileAccessOf (files : List (String × ByteArray)) : FileAccess :=
  FileAccess.withSparql { read := fun _ p => (files.find? (fun (n, _) => n == baseName p)).map (·.2) }

/-- What a module's cases look like on disk. -/
structure Module where
  /-- Its directory under `rml-modules`. -/
  name : String
  /-- The base IRI in force where the corpus gives none. -/
  defaultBase : Option String := none

/-- The modules run by default. A module joins this list when its cases
    run; listing it earlier would score a gap as a failure. -/
def modules : List Module :=
  [ { name := "rml-core" }
  , { name := "rml-io" }
  , { name := "rml-cc", defaultBase := some "http://example.com/base/" }
  , { name := "rml-star" }
  , { name := "rml-fnml" } ]

/-- How one case came out. -/
inductive Outcome where
  | pass
  | fail (msg : String)
  | gaveUp (id : String)
  | bucket (name reason : String)

/-- Replace every literal's datatype by `xsd:string`, leaving language
    tags: the graph a writer that dropped datatypes would have written. -/
def eraseDatatypes (g : Graph) : Graph :=
  g.map (fun t => { t with o := match t.o with
    | .literal l =>
        if l.val.langTag.isSome then t.o else .literal (Literal.string l.val.lexicalForm)
    | o => o })

def sameGraph (a b : Graph) : Outcome :=
  match Graph.isomorphicOutcome a b with
  | .equal => .pass
  | .budgetExceeded => .gaveUp "the isomorphism search hit its budget"
  | .notEqual => .fail s!"produced {a.length}, expected {b.length}"

/-- A quoted triple has one reifier, whichever way the document names it
    (RML.Star): the reifiers of the same triple term are merged in every
    graph of a dataset before two datasets are compared. -/
def mergeDatasetReifiers (ds : Dataset) : Dataset :=
  { default := mergeReifiers ds.default
    named := ds.named.map (fun ng => { ng with graph := mergeReifiers ng.graph }) }

/-- Cases whose expected output differs from the natural mapping of their
    own data in literal datatypes only, each with the evidence. A case is
    on this list by decision, not by a rule that any datatype-only mismatch
    is a fixture defect: such a rule would turn a library that drops the
    datatype of every JSON number into a column of "fixture defects" and
    no failure. A case on the list whose mismatch is more than datatypes,
    or that passes, is a failure, and so is a datatype-only mismatch of a
    case that is not on it. -/
def datatypeDefects : List (String × String) :=
  let sibling := "the expected dump writes the age as a plain literal; the source holds the number 33, and the same mapping's other dumps in this module write it as xsd:integer"
  [ ("RMLTTC0004a", sibling), ("RMLTTC0004c", sibling), ("RMLTTC0004f", sibling)
  , ("RMLTTC0004g", sibling), ("RMLTTC0005b", sibling), ("RMLTTC0006b", sibling)
  , ("RMLTTC0006c", sibling), ("RMLTTC0006d", sibling), ("RMLTTC0006e", sibling)
  , ("RMLSTC0003",
      "the expected output writes the ages as xsd:integer; the data file holds plain literals, the results of a SPARQL query serialised as CSV are strings, and the mapping states no datatype") ]

/-- Compare a produced dataset with an expected one. A mismatch that
    disappears when every datatype is erased is a fixture defect only for
    a case on `datatypeDefects`. -/
def compareDatasets (id : String) (got want : Dataset) : Outcome :=
  let g := flattenDataset (mergeDatasetReifiers got)
  let w := flattenDataset (mergeDatasetReifiers want)
  match sameGraph g w with
  | .fail msg =>
      match sameGraph (eraseDatatypes g) (eraseDatatypes w) with
      | .pass =>
          match datatypeDefects.find? (fun d => d.1 == id) with
          | some d => .bucket "fixture defect" d.2
          | none => .fail (msg ++ "; the datasets differ in literal datatypes only, and the case is not on the fixture-defect list")
      | _ => .fail msg
  | o => o

/-- The first `unsupported` error of a run, if any: the case is then
    unattempted, not failed. -/
def firstUnsupported (es : List RmlError) : Option RmlError :=
  es.find? (fun e => e.kind == .unsupported)

def datasetOfQuadsOut (qs : List QuadOut) : Dataset := datasetOfQuads qs

/-- The expected output of a case. A file that quotes triples with `<< >>`
    is read as Turtle in RDF 1.2 mode, of which N-Triples-star is a subset;
    any other is read as N-Quads. -/
def parseExpected (src : String) : Except String Dataset :=
  if (src.splitOn "<<").length > 1 then
    match parseTurtle src none .rdf12 with
    | .ok g => .ok { default := g, named := [] }
    | .error e => .error e.msg
  else
    match parseNQuads src with
    | .ok d => .ok d
    | .error e => .error e.msg

/-- A CSV file whose first line is `**…**`, the label the test generator
    wrote above the data of its second input, with that line removed. -/
def withoutLabelLine (name : String) (b : ByteArray) : Option ByteArray :=
  if !name.endsWith ".csv" then none
  else
    match String.fromUTF8? b with
    | none => none
    | some s =>
        let first := (String.ofList (s.toList.takeWhile (· != '\n'))).trim
        if first.length ≥ 4 && first.startsWith "**" && first.endsWith "**" then
          some (String.ofList ((s.toList.dropWhile (· != '\n')).drop 1)).toUTF8
        else none

/-- The files of a case with every such label line removed, or `none` when
    no file has one. -/
def withoutLabelLines (files : List (String × ByteArray)) : Option (List (String × ByteArray)) :=
  let cleaned := files.map (fun (n, b) => (n, withoutLabelLine n b))
  if cleaned.any (fun (_, c) => c.isSome) then
    some (cleaned.map (fun (n, c) => (n, c.getD ((files.find? (fun (m, _) => m == n)).map (·.2) |>.getD ByteArray.empty))))
  else none

/-- Run a positive case on the given files and compare the result with the
    expected dataset: the default target first, then each logical target's
    file. -/
def judge (id : String) (mg : Graph) (baseOf : Option String) (files : List (String × ByteArray))
    (want : Dataset) : Outcome × EvalResult :=
  let r := runMappingGraphFiles mg baseOf (fileAccessOf files)
  match firstUnsupported r.errors with
  | some u => (.bucket u.bucket u.message, r)
  | none =>
    if r.rejected then (.fail s!"a valid mapping was rejected\n{renderErrors r.errors}", r)
    else
      let first := compareDatasets id (datasetOfQuads (quadsFor none r.quads)) want
      let outcome := (logicalTargetsOf mg).foldl (fun (o : Outcome) lt =>
        match o with
        | .pass =>
            let fname := baseName lt.path
            match files.find? (fun (n, _) => n == fname) with
            | none => .fail s!"the expected file '{fname}' of target {lt.id} is missing"
            | some (_, bytes) =>
                match readTarget lt bytes, ourDump lt (quadsFor (some lt.id) r.quads) with
                | .error (.unsupported b why), _ | _, .error (.unsupported b why) => .bucket b why
                | .error (.failed m), _ => .fail s!"the expected file '{fname}' cannot be read: {m}"
                | _, .error (.failed m) => .fail s!"our dump for '{fname}' cannot be made: {m}"
                | .ok wantDs, .ok gotDs => compareDatasets id gotDs wantDs
        | o => o) first
      (outcome, r)

/-- Run one case of a module. -/
def runCase (md : Module) (dir : String) (m? : Option CaseMeta) (name : String)
    (t : Tally) (dump : Option String) (verbose : Bool) : IO Tally := do
  let caseDir := dir ++ "/" ++ name
  let mp := caseDir ++ "/mapping.ttl"
  let outName := (m?.map (·.output1)).filter (· != "") |>.getD "output.nq"
  let op := caseDir ++ "/" ++ outName
  let isError := (m?.map (·.isError)).getD false
  let baseOf : Option String :=
    ((m?.map (·.baseIri)).filter (fun b => b != "")).orElse (fun _ => md.defaultBase)
  let mut t := t
  if !(← System.FilePath.pathExists mp) then return t
  let msrc ← IO.FS.readFile mp
  let files ← readCaseFiles caseDir
  if isError then
    -- A NEGATIVE case: the corpus's own metadata says the mapping
    -- is invalid, and there is no expected output because the
    -- correct outcome is an ERROR. It passes when the mapping is
    -- rejected, by the Turtle parser, by validation or by evaluation.
    --
    -- A case that is marked as an error AND ships an expected output
    -- contradicts itself (RMLSTC0009a): it is a fixture defect, not
    -- a case the processor can pass or fail.
    if (← System.FilePath.pathExists op) then
      t := t.addBucket "fixture defect"
        "the metadata marks the case as an error and the case also ships an expected output" name
      IO.println s!"FIXTURE DEFECT {name}: marked error=true and ships {outName}"
      return t
    match parseTurtle msrc none with
    | .error e =>
        t := { t with pass := t.pass + 1, rejParse := t.rejParse + 1 }
        if verbose then IO.println s!"rejected {name} (Turtle parser): {e.msg}"
    | .ok mg =>
        let static := validateMapping mg
        if !static.isEmpty then
          t := { t with pass := t.pass + 1, rejValid := t.rejValid + 1 }
          if verbose then IO.println s!"rejected {name} (validation):\n{renderErrors static}"
        else
          let r := runMappingGraphFiles mg baseOf (fileAccessOf files)
          match firstUnsupported r.errors with
          | some u =>
              t := t.addBucket u.bucket u.message name
              IO.println s!"UNATTEMPTED {name} ({u.bucket}): {u.message}"
          | none =>
              if r.rejected then
                t := { t with pass := t.pass + 1, rejEval := t.rejEval + 1 }
                if verbose then IO.println s!"rejected {name} (evaluation):\n{renderErrors r.errors}"
              else
                t := { t with fail := t.fail + 1 }
                IO.println s!"FAIL {name}: the mapping must be rejected and was accepted ({r.quads.length} quads)"
    return t
  if !(← System.FilePath.pathExists op) then
    t := t.addBucket "not read" "no expected output file" name
    IO.println s!"no expected output and the metadata does not call it an error: {name}"
    return t
  let osrc ← IO.FS.readFile op
  match parseTurtle msrc none, parseExpected osrc with
  | .error e, _ =>
      t := t.addBucket "not read" "the mapping did not parse" name
      IO.println s!"NOT READ {name}: the mapping did not parse ({e.msg})"
  | _, .error _ =>
      t := t.addBucket "fixture defect" "the expected output is not valid N-Quads" name
      IO.println (s!"FIXTURE DEFECT {name}: the expected N-Quads do not parse. " ++
        "RMLTC0027b's output.nq writes <http://example.com/Person/Emily Smith>, " ++
        "and an IRIREF may not contain a space.")
  | .ok mg, .ok want =>
      let (outcome0, r) := judge name mg baseOf files want
      if dump == some name then
        let got := flattenQuads r.quads
        let wantG := flattenDataset want
        IO.println s!"--- {name} PRODUCED {got.length} ---"
        for l in ((got.map (fun x => (Graph.toNTriples [x]).toOption.getD "")).mergeSort (· ≤ ·)) do
          IO.println l.trim
        IO.println s!"--- {name} EXPECTED {wantG.length} ---"
        for l in ((wantG.map (fun x => (Graph.toNTriples [x]).toOption.getD "")).mergeSort (· ≤ ·)) do
          IO.println l.trim
      -- A case that fails may fail because its data file starts with the
      -- generator's label line. It is a fixture defect when the case passes
      -- with that line removed, and a failure when it still does not.
      let outcome : Outcome :=
        match outcome0 with
        | .fail _ =>
            match withoutLabelLines files with
            | none => outcome0
            | some files' =>
                match (judge name mg baseOf files' want).1 with
                | .pass => .bucket "fixture defect"
                    "a data file starts with the line **Input N**, the label of the test generator, which is not CSV data"
                | _ => outcome0
        | o => o
      -- A case on the fixture-defect list that passes outright is a failure
      -- of the list: remove the entry.
      let outcome : Outcome :=
        match outcome with
        | .pass =>
            if datatypeDefects.any (fun d => d.1 == name) then
              .fail "the case is on the fixture-defect list and passes; remove it from the list"
            else .pass
        | o => o
      match outcome with
      | .pass => t := { t with pass := t.pass + 1 }
      | .gaveUp why =>
          t := { t with gaveUp := t.gaveUp + 1 }
          IO.println s!"GAVE UP {name}: {why}"
      | .bucket b why =>
          t := t.addBucket b why name
          IO.println s!"UNATTEMPTED {name} ({b}): {why}"
      | .fail msg =>
          t := { t with fail := t.fail + 1 }
          IO.println s!"FAIL {name}: {msg}"
  return t

/-- Run one module of the corpus. -/
def runModule (md : Module) (dir : String) (dump : Option String) (verbose : Bool)
    (only : Option String) : IO Tally := do
  let metaPath := dir ++ "/metadata.csv"
  let metaRows : List CaseMeta ← if ← System.FilePath.pathExists metaPath
             then do let src ← IO.FS.readFile metaPath; pure (readMetadata src)
             else pure []
  let mut names : List String := []
  for entry in (← System.FilePath.readDir dir) do
    if ← System.FilePath.isDir entry.path then
      names := names ++ [entry.fileName]
  let mut t : Tally := {}
  for name in names.mergeSort (· ≤ ·) do
    if (only.map (fun o => name.startsWith o)).getD true then
      t ← runCase md dir (metaRows.find? (fun c => c.id == name)) name t dump verbose
  return t

/-- The FnO descriptions of a module's `functions.ttl` against the
    library's registry: every function the file describes is implemented,
    with the parameters (and their `fno:required` flags) and the returns
    the file gives it. A mismatch is a failure of the library, not of one
    case, so it is reported apart from the case scores. -/
def checkFunctionDescriptions (dir : String) : IO Bool := do
  let path := dir ++ "/functions.ttl"
  if !(← System.FilePath.pathExists path) then return true
  let src ← IO.FS.readFile path
  match parseTurtle src none with
  | .error e =>
      IO.println s!"{path}: does not parse ({e.msg})"
      return false
  | .ok g =>
      let described := describedFunctions g
      let mut bad : List String := []
      for iri in described do
        match lookupFn iri with
        | none => bad := bad ++ [s!"<{iri}> has no implementation"]
        | some f =>
            if !f.agreesWith g then
              bad := bad ++ [s!"<{iri}> has other parameters or returns than the registry"]
      IO.println (s!"{path}: {described.length} functions described, " ++
        s!"{described.length - bad.length} implemented with the same parameters and returns")
      for b in bad do IO.println s!"  {b}"
      return bad.isEmpty

/-- The score line the scoreboard reads: counts, then `(out of T)`. -/
def scoreLine (dir : String) (t : Tally) : String :=
  let total := t.pass + t.fail + t.gaveUp + t.unattempted
  let buckets := t.buckets.map (fun b => s!"{b.cases.length} {b.bucket}")
  let parts := [s!"{t.pass} pass", s!"{t.fail} fail"] ++
    (if t.gaveUp > 0 then [s!"{t.gaveUp} comparison gave up"] else []) ++ buckets
  s!"{dir}: {String.intercalate ", " parts} (out of {total})"

/-- The issue each bucket that is not a fixture defect is tracked by. A
    shortfall is a failing test AND an open issue (CLAUDE.md, owner,
    2026-09-07); the coordinator files the issue and fills the URL in. -/
def issueFor (bucket : String) : String :=
  if bucket == "fixture defect" || bucket == "not read" then "none: not a shortfall of the engine"
  else "NOT YET FILED (the coordinator files it)"

def main (args : List String) : IO UInt32 := do
  let dump := (args.find? (fun a => a.startsWith "--dump=")).map
    (fun a => String.ofList (a.toList.drop 7))
  let only := (args.find? (fun a => a.startsWith "--only=")).map
    (fun a => String.ofList (a.toList.drop 7))
  let verbose := args.contains "--verbose"
  let explicit := (args.filter (fun a => !a.startsWith "--")).head?
  let mut anyFail := false
  let mut ran := 0
  for md in modules do
    let dir ← match explicit with
      | some d =>
          -- a directory given by hand runs as the module its path names
          if d.contains md.name || (md.name == "rml-core" && !(modules.any (fun x => d.contains x.name)))
          then pure (some d) else pure none
      | none => do
          let d ← Harness.fixtureArgOr none s!"third_party/testing/rml-modules/{md.name}/test-cases"
          pure (some d)
    match dir with
    | none => pure ()
    | some dir =>
      if !(← System.FilePath.isDir dir) then
        IO.println s!"rml runner: corpus not found: {dir}"
        IO.println "run tools/ensure-test-env.sh from the repository root first"
        return 1
      ran := ran + 1
      let t ← runModule md dir dump verbose only
      IO.println ""
      IO.println (scoreLine dir t)
      if t.rejParse + t.rejValid + t.rejEval > 0 then
        IO.println s!"  negative cases rejected: {t.rejParse} by the Turtle parser, {t.rejValid} by validation, {t.rejEval} by evaluation"
      for b in t.buckets do
        IO.println s!"  bucket '{b.bucket}': {b.cases.length} cases"
        let reasons := b.cases.foldl (fun (acc : List String) c =>
          if acc.contains c.2 then acc else acc ++ [c.2]) []
        for r in reasons do
          let ids := (b.cases.filter (fun c => c.2 == r)).map (·.1)
          IO.println s!"    {String.intercalate " " ids}"
          IO.println s!"      reason: {r}"
        IO.println s!"    issue: {issueFor b.bucket}"
      if t.fail > 0 then anyFail := true
      if md.name == "rml-fnml" then
        if !(← checkFunctionDescriptions dir) then anyFail := true
  if ran == 0 then
    IO.println "rml runner: no module ran"
    return 1
  IO.println ""
  IO.println "Comparison is DATASET isomorphism: every quad is encoded as a"
  IO.println "triple carrying its graph name, so blank nodes must line up"
  IO.println "across graphs. A comparison that gives up is counted apart from"
  IO.println "a failure -- it is not evidence the two datasets differ."
  return (if anyFail then 1 else 0)
