/-
Harness/Sbm11W3c — `l4sbm11-w3c`: the lists and the comparisons of the W3C round
trip through the SBM11 store (`tests/sbm11/w3c_roundtrip.sh`;
https://github.com/danbri/factoidal/issues/837 item 5).

The script packs the action of a W3C test with `l4sbm11-pack`, dumps the
generation with `l4sbm11 dump`, and asks this tool whether the dump is the
expected result. This tool holds no RDF semantics of its own. It reads the
manifests with the reader of the Lean W3C runner (`Harness.loadManifest`), reads
a document through the source layer (`Source.parseDocument`), and compares two
datasets with the isomorphism of the Lean W3C runners
(`Dataset.isomorphicOutcome`, RDF 1.1 Concepts section 3.6).

  l4sbm11-w3c list-rdf [--syntax] MANIFEST...
      One row for each positive evaluation test of an RDF manifest (Turtle,
      TriG and RDF/XML eval tests, and the N-Triples and N-Quads canonicalisation
      tests of RDF 1.2), in the order of the manifest. With `--syntax`, also one
      row for each positive syntax test (no expected result). The fields, separated
      by a tab: suite, name, kind (`eval` or `syntax`), action, result (`-` for a
      syntax test), base IRI (`mf:assumedTestBase` + the path of the action
      relative to the manifest, as `Harness.fixtureBase` computes it), RDF
      version (`rdf11` or `rdf12`), format label of the action, kind of the
      result file (`nt`, `nq` or `-`), notes (`-`).
  l4sbm11-w3c list-jsonld [--syntax] MANIFEST
      The same for the JSON-LD 1.1 toRdf manifest (`jld:PositiveEvaluationTest`;
      with `--syntax`, also `jld:PositiveSyntaxTest`). The base IRI is
      `option.base`, else the manifest's `baseIri` + `input`. The result file is
      read as N-Quads, line by line (`nq-lenient`), as `Harness/JsonLdProbe.lean`
      reads it. The notes field lists the options of the test that the source layer
      cannot pass to the JSON-LD parser (`specVersion=json-ld-1.0`,
      `processingMode=...`, `rdfDirection=...`, `expandContext=...`,
      `produceGeneralizedRdf=true`), else `-`.
  l4sbm11-w3c compare EXPECTED ACTUAL --expected nt|nq|nq-lenient --mode rdf11|rdf12
      EXPECTED is a result file. ACTUAL is N-Quads in RDF 1.2 syntax (the output of
      `l4sbm11 dump`). Prints `pass`, `pass via-canonical` or `fail REASON` and
      exits 0 for a pass, 1 for a fail.
  l4sbm11-w3c check-parse SOURCE EXPECTED --format F --base IRI --expected K --mode M
      The same comparison with the dataset that `Source.parseDocument` gives for
      SOURCE (the in-memory parse, without the store).
  l4sbm11-w3c compare-source ACTUAL SOURCE --format F --base IRI --mode M
      The comparison of ACTUAL with the dataset that `Source.parseDocument` gives
      for SOURCE (a syntax test has no result file; the parse is the expected
      result).
  l4sbm11-w3c parse-ok SOURCE --format F --base IRI --mode M
      Prints `pass` when `Source.parseDocument` accepts SOURCE (the parser's
      verdict on a positive syntax test), else `fail REASON`.

  l4sbm11-w3c list-update MANIFEST...
      One row for each `mf:UpdateEvaluationTest` of a SPARQL 1.1 Update manifest,
      in the order of the manifest. The fields, separated by a tab: suite (the
      directory of the manifest), entry (the local name of the test node), the
      `mf:name`, the manifest, the `ut:request` file.
  l4sbm11-w3c prepare-update MANIFEST ENTRY OUTDIR
      Writes `OUTDIR/input.nq` (the initial Graph Store: `ut:data` as the default
      graph and each `ut:graphData` as the named graph its `rdfs:label` names;
      the loader of the Lean update runner, `Harness.loadUpdateStore`) and
      `OUTDIR/expected.nq` (the same for `mf:result`), and prints `ok`, or
      `skip REASON` (exit 3) when a file is missing or the request has a LOAD
      without SILENT (no document is fetched: the Lean update runner skips it
      too), or `fail REASON` (exit 1).
  l4sbm11-w3c run-update MANIFEST ENTRY
      The test through the in-memory reference engine, the existing Lean update
      runner (`Harness.runUpdateEvaluation`): `pass`, `fail REASON` (exit 1) or
      `skip REASON` (exit 3).

Comparison rules. Both datasets go through `normalizeDataset` first: a graph is a
set of triples (RDF 1.1 Concepts section 3; the in-memory JSON-LD toRdf output of
test #te108 lists a quad twice, the store keeps it once) and language tags are in
lower case (section 3.3; the packer folds them, `normalizeTerm`). Lexical forms
compare exactly. Blank nodes compare up to a bijection. A named graph with no
triple is dropped on both sides: an N-Quads document, the expected result of a
TriG test and the dump of a store cannot state one. When the
isomorphism search gives up (`IsoOutcome.budgetExceeded`), the RDFC-1.0 canonical
N-Quads of the two datasets are compared, as `Harness/JsonLdProbe.lean` does, and
the pass says `via-canonical`.
-/
import Harness.Manifest
import Harness.Run
import L4Factoidal.RDF.SourceJsonLd
import L4Factoidal.RDF.Isomorphism
import L4Factoidal.RDF.Canonical
import L4Factoidal.RDF.DatasetNormalize
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.NQuadsFast
-- `parseNQuads_eq_fast`: the expected results are parsed by the indexed parser.
import L4Factoidal.Syntax.NQuadsFastTheorems
import L4Factoidal.Syntax.NTriples
import L4Factoidal.JSON.Parser

open L4Factoidal.RDF
open L4Factoidal.JSON
open L4Factoidal.Syntax

namespace Sbm11W3c

/-! ## Reading the expected result -/

inductive ExpectedKind where
  | nt | nq | nqLenient
  deriving DecidableEq

def ExpectedKind.ofLabel? : String → Option ExpectedKind
  | "nt" => some .nt
  | "nq" => some .nq
  | "nq-lenient" => some .nqLenient
  | _ => none

def modeOfLabel? : String → Option Mode
  | "rdf11" => some .rdf11
  | "rdf12" => some .rdf12
  | _ => none

/-- The union of two datasets, graph by graph (the lines of an N-Quads document
    read one at a time). -/
def Dataset.append (a b : Dataset) : Dataset :=
  { default := a.default ++ b.default,
    named := b.named.foldl (fun acc ng =>
      if acc.any (fun x => x.name == ng.name) then
        acc.map (fun x => if x.name == ng.name then { x with graph := x.graph ++ ng.graph } else x)
      else acc ++ [ng]) a.named }

/-- The lines of an N-Quads document that parse, and the number that did not
    (`Harness/JsonLdProbe.lean`: the F* parser skips a line it cannot read, and
    `toRdf/0118-out.nq` relies on that). -/
def parseNQuadsLenient (text : String) : Dataset × Nat := Id.run do
  let mut ds := Dataset.empty
  let mut dropped := 0
  for line in text.splitOn "\n" do
    let t := line.trimAscii.toString
    if t.isEmpty || t.startsWith "#" then continue
    match parseNQuads t .rdf11 with
    | .error _ => dropped := dropped + 1
    | .ok one => ds := Dataset.append ds one
  pure (ds, dropped)

def parseExpected (kind : ExpectedKind) (mode : Mode) (text : String) : Except String Dataset :=
  match kind with
  | .nt =>
      match parseNTriples text mode with
      | .ok g => .ok { default := g, named := [] }
      | .error e => .error s!"expected-result N-Triples parse error at {e.pos}: {e.msg}"
  | .nq =>
      match parseNQuads text mode with
      | .ok ds => .ok ds
      | .error e => .error s!"expected-result N-Quads parse error at {e.pos}: {e.msg}"
  | .nqLenient => .ok (parseNQuadsLenient text).1

/-! ## Comparison -/

def dropEmptyNamed (ds : Dataset) : Dataset :=
  { ds with named := ds.named.filter fun ng => !ng.graph.isEmpty }

def quadCount (ds : Dataset) : Nat :=
  ds.default.length + (ds.named.map (·.graph.length)).foldl (· + ·) 0

/-- `pass`, `pass via-canonical` or `fail ...`. -/
def compareDatasets (got0 exp0 : Dataset) : Bool × String :=
  let got := dropEmptyNamed (normalizeDataset got0)
  let exp := dropEmptyNamed (normalizeDataset exp0)
  match Dataset.isomorphicOutcome got exp with
  | .equal => (true, "pass")
  | .notEqual =>
      (false, s!"fail not isomorphic to the expected dataset (got {quadCount got} quads, expected {quadCount exp})")
  | .budgetExceeded =>
      if got.canonicalNQuads == exp.canonicalNQuads then (true, "pass via-canonical")
      else
        (false, s!"fail not isomorphic to the expected dataset by RDFC-1.0 either (got {quadCount got} quads, expected {quadCount exp})")

def readFile (path : String) : IO String := IO.FS.readFile path

/-- The dataset a dump holds: N-Quads in RDF 1.2 syntax. -/
def parseDump (text : String) : Except String Dataset :=
  match parseNQuadsFast text .rdf12 with
  | .ok ds => .ok ds
  | .error e => .error s!"the dump does not parse as N-Quads at {e.pos}: {e.msg}"

def runCompare (expectedPath actualPath : String) (kind : ExpectedKind) (mode : Mode) : IO UInt32 := do
  let exp ← match parseExpected kind mode (← readFile expectedPath) with
    | .ok d => pure d
    | .error m => IO.println s!"fail {m}"; return 1
  let got ← match parseDump (← readFile actualPath) with
    | .ok d => pure d
    | .error m => IO.println s!"fail {m}"; return 1
  let (ok, line) := compareDatasets got exp
  IO.println line
  pure (if ok then 0 else 1)

/-- The dataset `Source.parseDocument` gives, with the options the source layer
    has: the format, the base IRI and the RDF version. -/
def parseSource (path : String) (fmt : RdfFormat) (base : String) (mode : Mode) : IO (Except String Dataset) := do
  let text ← readFile path
  match Source.parseDocument Source.withJsonLd fmt mode (if base == "-" then none else some base) text with
  | .ok ds => pure (.ok ds)
  | .error e => pure (.error s!"parse error at {e.pos}: {e.msg}")

def runCheckParse (source expectedPath : String) (fmt : RdfFormat) (base : String) (kind : ExpectedKind)
    (mode : Mode) : IO UInt32 := do
  let exp ← match parseExpected kind mode (← readFile expectedPath) with
    | .ok d => pure d
    | .error m => IO.println s!"fail {m}"; return 1
  match ← parseSource source fmt base mode with
  | .error m => IO.println s!"fail {m}"; pure 1
  | .ok got =>
      let (ok, line) := compareDatasets got exp
      IO.println line
      pure (if ok then 0 else 1)

def runCompareSource (actualPath source : String) (fmt : RdfFormat) (base : String) (mode : Mode) : IO UInt32 := do
  let got ← match parseDump (← readFile actualPath) with
    | .ok d => pure d
    | .error m => IO.println s!"fail {m}"; return 1
  match ← parseSource source fmt base mode with
  | .error m => IO.println s!"fail the in-memory parse failed: {m}"; pure 1
  | .ok exp =>
      let (ok, line) := compareDatasets got exp
      IO.println line
      pure (if ok then 0 else 1)

def runParseOk (source : String) (fmt : RdfFormat) (base : String) (mode : Mode) : IO UInt32 := do
  match ← parseSource source fmt base mode with
  | .error m => IO.println s!"fail {m}"; pure 1
  | .ok _ => IO.println "pass"; pure 0

/-! ## Lists of tests -/

/-- The kinds of positive evaluation test: (test type, family, format label of
    the action, kind of the result file). -/
def evalTypes : List (String × String × String × String) :=
  [ ("TestTurtleEval", "Turtle", "turtle", "nt"),
    ("TestTrigEval", "TriG", "trig", "nq"),
    ("TestXMLEval", "RDF/XML", "rdfxml", "nt"),
    ("TestNTriplesPositiveC14N", "N-Triples", "ntriples", "nt"),
    ("TestNQuadsPositiveC14N", "N-Quads", "nquads", "nq") ]

def syntaxTypes : List (String × String × String) :=
  [ ("TestTurtlePositiveSyntax", "Turtle", "turtle"),
    ("TestTrigPositiveSyntax", "TriG", "trig"),
    ("TestNTriplesPositiveSyntax", "N-Triples", "ntriples"),
    ("TestNQuadsPositiveSyntax", "N-Quads", "nquads") ]

/-- The RDF version of a manifest: 1.2 when the base it states or its path says
    `/rdf12/` (`Harness.modeOfManifest`, which `Harness/Main.lean` holds). -/
def modeOfManifest (assumedBase : Option String) (path : String) : Mode :=
  let says (s : String) : Bool := (s.splitOn "/rdf12/").length > 1
  match assumedBase with
  | some b => if says b then .rdf12 else .rdf11
  | none => if says path then .rdf12 else .rdf11

def modeLabel : Mode → String
  | .rdf11 => "rdf11"
  | .rdf12 => "rdf12"

def versionLabel : Mode → String
  | .rdf11 => "RDF 1.1"
  | .rdf12 => "RDF 1.2"

def row (fields : List String) : String := "\t".intercalate fields

def listRdf (withSyntax : Bool) (manifest : String) : IO (List String) := do
  match ← Harness.loadManifest manifest with
  | none => throw (IO.userError s!"manifest not found: {manifest} (run tools/ensure-test-env.sh)")
  | some (.error e) => throw (IO.userError s!"{manifest}: {e}")
  | some (.ok (tests, assumedBase)) =>
      let abs := (← IO.FS.realPath manifest).toString
      let manifestDir := Harness.dirname abs
      let mode := modeOfManifest assumedBase abs
      let mut out : List String := []
      for tc in tests do
        let some action := tc.action | continue
        let base := Harness.fixtureBase assumedBase manifestDir action
        match evalTypes.find? (·.1 == tc.testType) with
        | some (_, family, fmt, expKind) =>
            let some result := tc.resultFile
              | throw (IO.userError s!"{manifest}: test {tc.name} has no mf:result")
            out := out ++ [row [s!"{family} {versionLabel mode}", tc.name, "eval", action, result, base,
                                modeLabel mode, fmt, expKind, "-"]]
        | none =>
            if withSyntax then
              match syntaxTypes.find? (·.1 == tc.testType) with
              | some (_, family, fmt) =>
                  out := out ++ [row [s!"{family} {versionLabel mode} syntax", tc.name, "syntax", action, "-", base,
                                      modeLabel mode, fmt, "-", "-"]]
              | none => pure ()
      pure out

/-- The options of a JSON-LD test that the source layer's parser does not get
    (`Source.jsonLdParser` passes no document loader, no `rdfDirection`, no
    `expandContext` and no processing mode). -/
def jsonLdNotes (j : Json) : String :=
  let opt := j.field? "option"
  let str (k : String) : Option String := opt.bind fun o => o.getString? k
  let notes : List String := List.filterMap id
    [ (str "specVersion").bind fun v => if v == "json-ld-1.0" then some "specVersion=json-ld-1.0" else none,
      (str "processingMode").map fun v => s!"processingMode={v}",
      (str "rdfDirection").map fun v => s!"rdfDirection={v}",
      (str "expandContext").map fun v => s!"expandContext={v}",
      (opt.bind fun o => o.getBool? "produceGeneralizedRdf").bind fun b =>
        if b then some "produceGeneralizedRdf=true" else none ]
  if notes.isEmpty then "-" else ",".intercalate notes

def jsonTypes (j : Json) : List String :=
  match j.field? "@type" with
  | some (.array items) => items.filterMap Json.asString?
  | some (.string s) => [s]
  | _ => []

def listJsonLd (withSyntax : Bool) (manifest : String) : IO (List String) := do
  let dir := Harness.dirname (← IO.FS.realPath manifest).toString
  let raw ← match ← Harness.readOpt manifest with
    | some t => pure t
    | none => throw (IO.userError s!"manifest not found: {manifest} (run tools/ensure-test-env.sh)")
  let root ← match parseJson raw with
    | .ok r => pure r
    | .error _ => throw (IO.userError s!"{manifest}: not valid JSON")
  let baseIri := (root.getString? "baseIri").getD "https://w3c.github.io/json-ld-api/tests/"
  let mut out : List String := []
  for e in (root.getArray? "sequence").getD [] do
    let types := jsonTypes e
    let some input := e.getString? "input" | continue
    let eval := types.contains "jld:PositiveEvaluationTest"
    let syn := types.contains "jld:PositiveSyntaxTest"
    unless eval || (withSyntax && syn) do continue
    let id := (e.getString? "@id").getD input
    let base := match e.field? "option" |>.bind (fun o => o.getString? "base") with
      | some b => b
      | none => baseIri ++ input
    let notes := jsonLdNotes e
    if eval then
      let some expect := e.getString? "expect" | throw (IO.userError s!"{manifest}: test {id} has no expect")
      out := out ++ [row ["JSON-LD toRdf", id, "eval", s!"{dir}/{input}", s!"{dir}/{expect}", base, "rdf12",
                          "jsonld", "nq-lenient", notes]]
    else
      out := out ++ [row ["JSON-LD toRdf syntax", id, "syntax", s!"{dir}/{input}", "-", base, "rdf12",
                          "jsonld", "-", notes]]
  pure out

/-! ## SPARQL 1.1 Update evaluation tests -/

/-- The tests of an update manifest. -/
def updateTests (manifest : String) : IO (List Harness.TestCase) := do
  match ← Harness.loadManifest manifest with
  | none => throw (IO.userError s!"manifest not found: {manifest} (run tools/ensure-test-env.sh)")
  | some (.error e) => throw (IO.userError s!"{manifest}: {e}")
  | some (.ok (tests, _)) => pure (tests.filter (·.testType == "UpdateEvaluationTest"))

/-- The part of an entry node's IRI after the last `#` (or the whole text). -/
def entryName (tc : Harness.TestCase) : String :=
  match tc.entryId.splitOn "#" with
  | [] => tc.entryId
  | parts => parts.getLast!

def findUpdateTest (manifest entry : String) : IO Harness.TestCase := do
  match (← updateTests manifest).find? (entryName · == entry) with
  | some tc => pure tc
  | none => throw (IO.userError s!"{manifest}: no update evaluation test {entry}")

def listUpdate (manifest : String) : IO (List String) := do
  let abs := (← IO.FS.realPath manifest).toString
  let suite := Harness.basename (Harness.dirname abs)
  let mut out : List String := []
  for tc in ← updateTests manifest do
    out := out ++ [row [suite, entryName tc, tc.name, abs, tc.queryFile.getD "-"]]
  pure out

def outcomeLine : Harness.Outcome → String × UInt32
  | .pass => ("pass", 0)
  | .fail r => (s!"fail {r}", 1)
  | .skip r => (s!"skip {r}", 3)
  | .unsupported f => (s!"skip unsupported {f}", 3)

def runPrepareUpdate (manifest entry outDir : String) : IO UInt32 := do
  let tc ← findUpdateTest manifest entry
  let some qf := tc.queryFile
    | IO.println "skip mf:action carries no ut:request"; return 3
  let some text ← Harness.readOpt qf
    | IO.println s!"skip file missing: {qf}"; return 3
  match L4Factoidal.SPARQL.parseSparqlUpdate text (some ("file://" ++ qf)) .v11 with
  | .error e => IO.println s!"fail Update parse: {Harness.fmtParseError e}"; return 1
  | .ok u =>
  if u.hasNonSilentLoad then
    IO.println "skip non-silent LOAD (no document fetch)"
    return 3
  let input ← match ← Harness.loadUpdateStore tc.dataFiles tc.graphData with
    | .ok d => pure d
    | .error o => let (l, c) := outcomeLine o; IO.println l; return c
  let expected ← match ← Harness.loadUpdateStore tc.updateResultData tc.updateResultGraphData with
    | .ok d => pure d
    | .error o => let (l, c) := outcomeLine o; IO.println l; return c
  IO.FS.createDirAll outDir
  for (name, ds) in [("input.nq", input), ("expected.nq", expected)] do
    match Dataset.toNQuads ds .rdf11 with
    | .ok t => IO.FS.writeFile s!"{outDir}/{name}" t
    | .error e => IO.println s!"fail cannot write {name}: {e}"; return 1
  IO.println "ok"
  pure 0

def runRunUpdate (manifest entry : String) : IO UInt32 := do
  let tc ← findUpdateTest manifest entry
  let r ← Harness.runUpdateEvaluation tc
  let (l, c) := outcomeLine r.outcome
  IO.println l
  pure c

/-! ## Command line -/

def usage : String :=
  "usage: l4sbm11-w3c list-rdf [--syntax] MANIFEST... | list-jsonld [--syntax] MANIFEST\n" ++
  "       | compare EXPECTED ACTUAL --expected nt|nq|nq-lenient --mode rdf11|rdf12\n" ++
  "       | check-parse SOURCE EXPECTED --format F --base IRI --expected nt|nq|nq-lenient --mode rdf11|rdf12\n" ++
  "       | compare-source ACTUAL SOURCE --format F --base IRI --mode rdf11|rdf12\n" ++
  "       | parse-ok SOURCE --format F --base IRI --mode rdf11|rdf12\n" ++
  "       | list-update MANIFEST... | prepare-update MANIFEST ENTRY OUTDIR | run-update MANIFEST ENTRY"

/-- `--flag value` pairs and positional arguments, each in the order given. A
    loop with two accumulators. -/
def scanLoop : List String → List String → List (String × String) →
    List String × List (String × String)
  | [], pos, kv => (pos.reverse, kv.reverse)
  | [a], pos, kv => ((a :: pos).reverse, kv.reverse)
  | a :: v :: rest, pos, kv =>
      if a.startsWith "--" && a != "--syntax" then scanLoop rest pos ((a, v) :: kv)
      else scanLoop (v :: rest) (a :: pos) kv

def scan (args : List String) : List String × List (String × String) :=
  scanLoop args [] []

def flag (kv : List (String × String)) (k : String) : Option String := (kv.find? (·.1 == k)).map (·.2)

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | "list-rdf" :: rest =>
        let withSyntax := rest.contains "--syntax"
        for m in rest.filter (· != "--syntax") do
          for r in ← listRdf withSyntax m do IO.println r
        pure 0
    | "list-jsonld" :: rest =>
        let withSyntax := rest.contains "--syntax"
        match rest.filter (· != "--syntax") with
        | [m] =>
            for r in ← listJsonLd withSyntax m do IO.println r
            pure 0
        | _ => IO.eprintln usage; pure 2
    | "compare" :: rest =>
        let (pos, kv) := scan rest
        match pos, (flag kv "--expected").bind ExpectedKind.ofLabel?, (flag kv "--mode").bind modeOfLabel? with
        | [e, a], some k, some m => runCompare e a k m
        | _, _, _ => IO.eprintln usage; pure 2
    | "check-parse" :: rest =>
        let (pos, kv) := scan rest
        match pos, (flag kv "--format").bind formatOfLabel, flag kv "--base",
            (flag kv "--expected").bind ExpectedKind.ofLabel?, (flag kv "--mode").bind modeOfLabel? with
        | [s, e], some f, some b, some k, some m => runCheckParse s e f b k m
        | _, _, _, _, _ => IO.eprintln usage; pure 2
    | "compare-source" :: rest =>
        let (pos, kv) := scan rest
        match pos, (flag kv "--format").bind formatOfLabel, flag kv "--base", (flag kv "--mode").bind modeOfLabel? with
        | [a, s], some f, some b, some m => runCompareSource a s f b m
        | _, _, _, _ => IO.eprintln usage; pure 2
    | "parse-ok" :: rest =>
        let (pos, kv) := scan rest
        match pos, (flag kv "--format").bind formatOfLabel, flag kv "--base", (flag kv "--mode").bind modeOfLabel? with
        | [s], some f, some b, some m => runParseOk s f b m
        | _, _, _, _ => IO.eprintln usage; pure 2
    | "list-update" :: rest =>
        for m in rest do
          for r in ← listUpdate m do IO.println r
        pure 0
    | ["prepare-update", m, e, d] => runPrepareUpdate m e d
    | ["run-update", m, e] => runRunUpdate m e
    | _ => IO.eprintln usage; pure 2
  catch e =>
    IO.eprintln s!"l4sbm11-w3c: {e}"
    pure 2

end Sbm11W3c

def main (args : List String) : IO UInt32 := Sbm11W3c.main args
