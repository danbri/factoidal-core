/-
Harness/WebAnnotationRun — the W3C Web Annotation tests (Data Model and
Vocabulary, Recommendations of 2017-02-23) in Lean.

A HARNESS: file reads and score lines only. The test semantics are in
`L4Factoidal.WebAnnotation.JsonTest` (the procedure of the suite's
`JSONtest.js`), the schemas are checked by `L4Factoidal.JSONSchema`
(dialect `draft04Ajv4`), and the vocabulary checks are in
`L4Factoidal.WebAnnotation.Vocab`.

Inputs (`third_party/testing/web-annotation/`, provenance in
`third_party/testing/web-annotation-PROVENANCE.md`):

* `annotation-model/`: 7 `.test` files, their assertion files, and the
  `definitions/` schemas that the assertions `$ref`.
* The documents to test. The suite's pages ask a tester to paste an
  annotation; the harness pastes (a) the 44 examples of the Data Model
  Recommendation (`recommendation-examples/`), which conform to the
  Recommendation, and (b) the 50 sample annotations that the suite's
  protocol server serves (`annotation-protocol/files/annotations/*.json`).
  Each `.test` file runs on each document of its kind (Annotation,
  Annotation Collection, Annotation Page). Expected: pass.
* `tests/webannotation/negative/`: project-local documents that break one
  MUST of the Recommendation each, with `manifest.tsv` naming the `.test`
  file and the assertion that must fail.
* `w3c-ns/`: the `anno.jsonld` context, `ldp.jsonld`, and the ontology as
  `oa.ttl`, `oa.rdf` and `oa.jsonld`.

Usage, from the repository root:
  formal/lean4/.lake/build/bin/l4webannotation [suite-dir] [local-dir]
-/
import L4Factoidal.WebAnnotation.JsonTest
import L4Factoidal.WebAnnotation.Vocab
import L4Factoidal.WebAnnotation.Theorems
import L4Factoidal.JSON.Parser

open L4Factoidal.JSON
open L4Factoidal.JSONSchema
open L4Factoidal.WebAnnotation
open L4Factoidal.RDF

namespace WebAnnotationRun

def readFileOpt (p : System.FilePath) : IO (Option String) := do
  try pure (some (← IO.FS.readFile p)) catch _ => pure none

def walkDir : Nat → System.FilePath → String → IO (List String)
  | 0, _, _ => pure []
  | depth + 1, root, rel => do
    let dir := if rel.isEmpty then root else root / rel
    let entries ← try dir.readDir catch _ => pure #[]
    let mut out : List String := []
    for e in entries do
      let childRel := if rel.isEmpty then e.fileName else rel ++ "/" ++ e.fileName
      if ← (dir / e.fileName).isDir then
        out := out ++ (← walkDir depth root childRel)
      else
        out := childRel :: out
    pure out

def sortStrings (xs : List String) : List String :=
  xs.mergeSort (fun a b => decide (a ≤ b))

/-- The base URI the assertion and definition files are read at. The
    assertions name definitions by file name (`annotations.json#/…`), and
    JSONtest.js adds every `definitions/` file to ajv under its `id`,
    which is that file name. -/
def defBase : String := "https://www.w3.org/annotation-model-tests/definitions/"

def readJson (p : System.FilePath) : IO (Option Json) := do
  match ← readFileOpt p with
  | none => pure none
  | some t => pure (parseJson t).toOption

/-- A document to test: its label, its JSON, and whether it should pass. -/
structure Doc where
  label : String
  json  : Json

def loadDocs (dir : System.FilePath) (label : String) (suffix : String := ".json") :
    IO (List Doc) := do
  let files := sortStrings ((← walkDir 1 dir "").filter (·.endsWith suffix))
  let mut out : List Doc := []
  for f in files do
    match ← readJson (dir / f) with
    | some j => out := { label := s!"{label}/{f}", json := j } :: out
    | none => IO.eprintln s!"l4webannotation: {dir / f} is not JSON"
  pure out.reverse

/-- Defective test data (https://github.com/danbri/factoidal/issues/1193):
    `choiceSet.json` accepts only `"type": "Choice"`, but Data Model §3.2.7
    also defines `Composite`, `List` and `Independents`, and Examples 42-44
    (and the protocol samples 11-13, the same annotations) use them. These
    runs are excluded and STALE if they pass; `tests/webannotation/local/choiceSet.json`
    (the four §3.2.7 classes) must make them pass. -/
def defectiveIssue : String := "https://github.com/danbri/factoidal/issues/1193"

def defective : List (String × String) :=
  ["recommendation-examples/example42.json", "recommendation-examples/example43.json",
   "recommendation-examples/example44.json", "protocol-samples/anno11.json",
   "protocol-samples/anno12.json", "protocol-samples/anno13.json"].map
    (·, "annotations/annotationMusts.test")

def verdictName : Verdict → String
  | .pass => "pass" | .fail => "fail" | .undetermined => "undetermined"

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := args.head?.getD "third_party/testing/web-annotation"
  let localDir : System.FilePath := (args.drop 1).head?.getD "tests/webannotation"
  let modelDir := root / "annotation-model"
  let files ← walkDir 4 modelDir ""
  if files.isEmpty then
    IO.eprintln s!"l4webannotation: no files under {modelDir}; run tools/ensure-test-env.sh"
    return 2
  -- The `definitions/` schemas, registered under `defBase`.
  let mut registry : Registry := []
  for f in files.filter (fun f => f.startsWith "definitions/" && f.endsWith ".json") do
    match ← readJson (modelDir / f) with
    | some j => registry := (defBase ++ (f.drop "definitions/".length).toString, j) :: registry
    | none => IO.eprintln s!"l4webannotation: {f} is not JSON"; return 2
  -- The assertion files, keyed by the path the `.test` files use.
  let mut cache : Cache := []
  for f in files.filter (fun f => f.endsWith ".json" && !f.startsWith "definitions/") do
    match ← readJson (modelDir / f) with
    | some j => cache := (f, j) :: cache
    | none => IO.eprintln s!"l4webannotation: {f} is not JSON"; return 2
  let mut tests : List TestFile := []
  for f in sortStrings (files.filter (·.endsWith ".test")) do
    match ← readJson (modelDir / f) with
    | some j =>
      -- The suite uses neither comparison objects nor nested lists; a
      -- new version that does is reported here, not silently run.
      let shapes := (TestFile.ofJson f j).assertions.filter (fun a => match a with
        | .string _ => false
        | _ => true)
      if !shapes.isEmpty then
        IO.eprintln s!"l4webannotation: {f} has an assertion that is not a file name"
      tests := TestFile.ofJson f j :: tests
    | none => IO.eprintln s!"l4webannotation: {f} is not JSON"; return 2
  tests := tests.reverse
  let env : Env := { cache, registry, base := defBase ++ "assertion.json" }
  let examples ← loadDocs (root / "recommendation-examples") "recommendation-examples"
  let samples ← loadDocs (root / "annotation-protocol" / "files" / "annotations") "protocol-samples"
  let positives := examples ++ samples
  let mut bad : List String := []
  -- 1. The Data Model tests on conforming documents.
  let mut pass := 0
  let mut fail := 0
  let mut undet := 0
  let mut excluded := 0
  let corrected? ← readJson (localDir / "local" / "choiceSet.json")
  let some corrected := corrected?
    | IO.eprintln s!"l4webannotation: {localDir / "local" / "choiceSet.json"} is absent"; return 2
  let envFixed : Env := { env with
    registry := (defBase ++ "choiceSet.json", corrected) ::
      registry.filter (·.1 != defBase ++ "choiceSet.json") }
  let mut fixedPass := 0
  for d in positives do
    for t in tests do
      if kindForTestPath t.path != kindOf d.json then continue
      let subs := runTestFile env t d.json
      if defective.contains (d.label, t.path) then
        if testVerdict subs == .pass then
          bad := s!"{d.label} × {t.path}: STALE exclusion, the run passes; remove it from `defective` and close {defectiveIssue}" :: bad
        else
          excluded := excluded + 1
          if testVerdict (runTestFile envFixed t d.json) == .pass then fixedPass := fixedPass + 1
          else bad := s!"{d.label} × {t.path}: fails with the corrected choiceSet.json too" :: bad
        continue
      match testVerdict subs with
      | .pass => pass := pass + 1
      | v =>
        if v == .fail then fail := fail + 1 else undet := undet + 1
        let why := (subs.filter (·.verdict != .pass)).map (fun s => s!"{s.level.name} {s.name}: {verdictName s.verdict}")
        bad := s!"{d.label} × {t.path}: {verdictName v}: {why}" :: bad
  IO.println s!"web-annotation model (conforming documents: {examples.length} Recommendation examples, {samples.length} protocol samples): {pass} pass, {fail} fail, {undet} undetermined (out of {pass + fail + undet} document × test runs); {excluded} excluded (defective test data, {defectiveIssue})"
  IO.println s!"  the excluded runs with the corrected choiceSet.json: {fixedPass} pass, {excluded - fixedPass} fail (out of {excluded})"
  -- 2. Project-local documents that break one MUST each.
  let mut negPass := 0
  let mut negTotal := 0
  match ← readFileOpt (localDir / "manifest.tsv") with
  | none =>
    IO.eprintln s!"l4webannotation: {localDir / "manifest.tsv"} is absent"
    return 2
  | some m =>
    for line in m.splitOn "\n" do
      if line.isEmpty || line.startsWith "#" then continue
      match line.splitOn "\t" with
      | [file, testPath, assertion] =>
        negTotal := negTotal + 1
        match ← readJson (localDir / "negative" / file), tests.find? (·.path == testPath) with
        | some j, some t =>
          let subs := runTestFile env t j
          let named := subs.filter (fun s => s.verdict == .fail && s.file == assertion)
          if testVerdict subs == .fail && !named.isEmpty then negPass := negPass + 1
          else
            let fails := (subs.filter (·.verdict != .pass)).map (·.file)
            bad := s!"negative/{file} × {testPath}: expected a failure of '{assertion}', got {verdictName (testVerdict subs)} {fails}" :: bad
        | none, _ => bad := s!"negative/{file}: not readable JSON" :: bad
        | _, none => bad := s!"negative/{file}: no test file {testPath}" :: bad
      | _ => bad := s!"manifest.tsv: malformed line: {line}" :: bad
  IO.println s!"web-annotation model (documents that break one MUST): {negPass} pass, {negTotal - negPass} fail (out of {negTotal})"
  -- 3. The vocabulary tests.
  let ns := root / "w3c-ns"
  let some annoCtx ← readFileOpt (ns / "anno.jsonld")
    | IO.eprintln "l4webannotation: w3c-ns/anno.jsonld is absent"; return 2
  let some ldpCtx ← readFileOpt (ns / "ldp.jsonld")
    | IO.eprintln "l4webannotation: w3c-ns/ldp.jsonld is absent"; return 2
  let loader := waLoader annoCtx ldpCtx
  let mut vPass : Nat := 0
  let mut vTotal : Nat := 0
  for d in positives do
    vTotal := vTotal + 4
    match expandWa loader d.json with
    | .error e => bad := s!"vocab 01 {d.label}: expansion failed: {reprStr e}" :: bad
    | .ok _ => vPass := vPass + 1
    match toRdfWa loader d.json with
    | .error e => bad := s!"vocab 02 {d.label}: toRdf failed: {reprStr e}" :: bad
    | .ok ds =>
      if ds.default.isEmpty then bad := s!"vocab 02 {d.label}: no triple" :: bad
      else vPass := vPass + 1
      match syntaxRoundTrips ds.default with
      | [] => vPass := vPass + 1
      | es => bad := s!"vocab 03 {d.label}: {es.map RoundTripError.render}" :: bad
      match jsonLdRoundTrip loader ds with
      | .ok () => vPass := vPass + 1
      | .error e => bad := s!"vocab 04 {d.label}: {e}" :: bad
  IO.println s!"web-annotation vocab 01-04 (per document: expand, to RDF, N-Triples/Turtle/RDF-XML round trip, JSON-LD round trip): {vPass} pass, {vTotal - vPass} fail (out of {vTotal})"
  let mut oPass := 0
  match ← readFileOpt (ns / "oa.ttl") with
  | none => bad := "vocab 05: w3c-ns/oa.ttl is absent" :: bad
  | some ttl =>
    match parseOntologyTurtle ttl with
    | .error e => bad := s!"vocab 05: oa.ttl does not parse: {e}" :: bad
    | .ok g =>
      oPass := oPass + 1
      match domainRangeProblems g with
      | [] => oPass := oPass + 1
      | ps => bad := s!"vocab 06: {ps}" :: bad
      IO.println s!"  oa.ttl: {g.length} triples, {(declaredClasses g).length} declared classes"
      -- The other two published forms of the ontology, reported apart.
      match ← readFileOpt (ns / "oa.rdf") with
      | some x =>
        match L4Factoidal.Syntax.RdfXml.parseRdfXml x (some oaNs) with
        | .ok g2 => IO.println s!"  oa.rdf: {g2.length} triples; isomorphic to oa.ttl: {g.isomorphic? g2}"
        | .error e => IO.println s!"  oa.rdf: does not parse: {reprStr e}"
      | none => pure ()
      match ← readJson (ns / "oa.jsonld") with
      | some j =>
        match toRdfWa loader j with
        | .ok ds => IO.println s!"  oa.jsonld: {ds.default.length} triples; isomorphic to oa.ttl: {g.isomorphic? ds.default}"
        | .error e => IO.println s!"  oa.jsonld: does not convert to RDF: {reprStr e}"
      | none => pure ()
  IO.println s!"web-annotation vocab 05-06 (oa.ttl parses; domains and ranges name declared classes or RDF datatypes): {oPass} pass, {2 - oPass} fail (out of 2)"
  for b in bad.reverse do IO.println s!"  FAIL {b}"
  return (if bad.isEmpty then 0 else 1)

end WebAnnotationRun

def main (args : List String) : IO UInt32 := WebAnnotationRun.main args
