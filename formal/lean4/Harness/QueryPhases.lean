/-
Harness.QueryPhases — `l4query-phases`: the phases of `l4factoidal query`,
one at a time, with the resident memory after each.

    l4query-phases FILE [--format F] [--query-string Q] [--stop-after PHASE]
    l4query-phases FILE --parse-op [--format F] [--stop-after PHASE]
    l4query-phases FILE --closure-op [--format F] [--stop-after PHASE]
    l4query-phases FILE --rdfxml-op [--stream] [--stop-after PHASE]
    l4query-phases FILE --parse-cli [--format F] [--stop-after PHASE]
    l4query-phases --walk-check LIST

PHASE is one of `read`, `parse`, `normalize`, `index`, `solutions`, `eval`,
`decode`, `render`, `output` (default `output`). The program runs the same
functions, in the same order, as `queryCmd` in `Wasm/Cli.lean` (`readInput`,
`Ops.parseTextToDataset`, `Ops.queryDatasetOf`, whose body is
`datasetForOps`, `indexedDatasetBackend` and `queryParsedDatasetWith`, then
`Cli.parseEnvelope` and `Cli.printQueryResult`), and after each phase prints
one line to standard error

    phase=NAME value=V rss_kb=R hwm_kb=H ms=T

where V is a number computed from the phase's result (so that the phase is
evaluated before the line is printed), R is `VmRSS` and H is `VmHWM` of
`/proc/self/status` (Linux only; 0 elsewhere), and T is the wall time in
milliseconds since the program started (`IO.monoNanosNow`). Run it once per
PHASE under `/usr/bin/time -v` to get the peak resident set of a process that
stops after that phase (https://github.com/danbri/factoidal/issues/729,
`docs/designissues/2026-10-10-lean-vs-fstar-performance.md` §10).

The phases after `index` (https://github.com/danbri/factoidal/issues/768
KR 2.3, the `select-star` row):

* `solutions`: the solution sequence of a SELECT alone, by the evaluator
  `queryParsedDatasetWith` calls (`runSelectQueryBackendDataset`, else
  `evalSelect`); V is the number of solutions. A process that stops here
  does not run `eval`.
* `eval`: `queryParsedDatasetWith`, the op's whole envelope string (it
  computes the solutions again, then `QueryResult.toSrj` and the envelope);
  V is its length in bytes.
* `decode`: `Cli.parseEnvelope`, the JSON parse of the envelope that the
  command line makes; V is 1.
* `render`: the text `l4factoidal query` prints for a SELECT
  (`Cli.printQueryResult`: the envelope's `srj` member, `toStringPretty`);
  V is its length in bytes.
* `output`: that text written to standard output.

`--parse-op` runs the phases of the wasm op `parseToDatasetJson` instead
(`parseToDatasetJsonWithBy` in `Wasm/Ops/Parse.lean`, the op `parse()` of the
npm package calls; https://github.com/danbri/factoidal/issues/744): `read`,
`parse` (`parseDocumentOutcomeBy`, which reads Turtle with the prefix table),
`scope` (`scopeBnodes`), `nquads` (`Dataset.toCanonicalNQuads`), `envelope`
(the op's JSON envelope, `okWith`), `output` (the envelope written to
standard output).

The memory figures are of the process, not of one data structure: the
allocator keeps freed pages, so `rss_kb` after a phase includes memory a
finished phase released. `hwm_kb` is the peak so far.
-/
import Wasm.Ops.Parse
import Wasm.Ops.ParseJsonLd
import Wasm.Ops.Query
import Wasm.Ops.Clock
import L4Factoidal.RDF.DatasetNormalize
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.Syntax.TurtleChunkFold
import Wasm.Ops.Reason
import L4Factoidal.Dataflow.Store

namespace Harness.QueryPhases

open L4Factoidal.RDF
open L4Factoidal.Syntax (Mode)
open L4Factoidal.SPARQL.StoreDataset

/-- The value in kB of `key` (`VmRSS`, `VmHWM`) in `/proc/self/status`;
0 when the file or the key is absent. -/
def procStatusKb (key : String) : IO Nat := do
  try
    let s ← IO.FS.readFile "/proc/self/status"
    let line? := (s.splitOn "\n").find? (fun l => l.startsWith (key ++ ":"))
    match line? with
    | none => pure 0
    | some l =>
        let digits := (l.drop (key.length + 1)).trim.takeWhile Char.isDigit
        pure digits.toNat!
  catch _ => pure 0

/-- Print the phase line. `t0` is `IO.monoNanosNow` at the start. -/
def report (t0 : Nat) (phase : String) (value : Nat) : IO Unit := do
  let rss ← procStatusKb "VmRSS"
  let hwm ← procStatusKb "VmHWM"
  let t ← IO.monoNanosNow
  let ms := (t - t0) / 1000000
  (← IO.getStderr).putStrLn s!"phase={phase} value={value} rss_kb={rss} hwm_kb={hwm} ms={ms}"

def phases : List String :=
  ["read", "chars", "parse", "normalize", "index", "solutions", "eval", "decode", "render",
   "output"]

open L4Factoidal.SPARQL in
/-- The solution sequence of a SELECT as `queryParsedDatasetWith` computes it
(the same environment, the backend runner first, the reference evaluator when
it answers `none` or the query has a dataset clause); the number of
solutions. `0` for another query form or a parse error. -/
def selectSolutionCount (ds : Dataset) (dsb : L4Factoidal.Dataflow.LawfulDataset) (sparql : String)
    (now : Option String) : Nat :=
  match parseSparql sparql none .v11 with
  | .error _ => 0
  | .ok q =>
    let env : EvalEnv := { base := q.base, ext := L4Wasm.Ops.extFnsWith [],
                           dataset := some ds, services := [], now := now }
    match q.form with
    | .select _ =>
        match (if q.dataset.isEmpty then dsb.runSelect env q else none) with
        | some rows => rows.length
        | none => (evalSelect env ds q).2.length
    | _ => 0

def flagValue (args : List String) (flag : String) : Option String :=
  match args.dropWhile (· != flag) with
  | _ :: v :: _ => some v
  | _ => none

/-- `--walk-check LIST`: for every file named in LIST (one path per line),
in both RDF modes, with and without a base IRI, compare the scanner walk of
`Syntax.parseTurtleText` alone (`parseTurtleWalk`, no fallback) with
`parseTurtle`. Counts the cases `parseTurtle` accepts and, among them, where
the walk gives the same graph, refuses (so `parseTurtleText` falls back), or
gives a different graph (exit 1). A document with `<<` is not walked. -/
def walkCheck (listFile : String) : IO UInt32 := do
  let files := (← IO.FS.readFile listFile).splitOn "\n" |>.filter (· ≠ "")
  let mut refOk := 0
  let mut agree := 0
  let mut fallback := 0
  let mut differ := 0
  let mut refErr := 0
  let mut skipped := 0
  for f in files do
    let text ← IO.FS.readFile f
    for mode in [Mode.rdf11, Mode.rdf12] do
      for base in [none, some "http://example.org/base/dir/doc"] do
        if L4Factoidal.Syntax.hasDoubleLt text then skipped := skipped + 1 else
        match L4Factoidal.Syntax.parseTurtle text base mode with
        | .error _ => refErr := refErr + 1
        | .ok g =>
          refOk := refOk + 1
          match L4Factoidal.Syntax.parseTurtleWalk text base mode with
          | .error _ => fallback := fallback + 1
          | .ok g' =>
            if g' == g then agree := agree + 1
            else
              differ := differ + 1
              IO.println s!"DIFFER {f}"
  IO.println s!"files {files.length}; cases: parseTurtle accepts {refOk} (walk agrees {agree}, walk refuses {fallback}, walk differs {differ}); parseTurtle refuses {refErr}; with << {skipped}"
  pure (if differ == 0 then 0 else 1)

def parseOpPhases : List String := ["read", "parse", "scope", "nquads", "envelope", "output"]

/-- `--parse-op`: the phases of `parseToDatasetJsonWithBy noExtraReader (some "d0_")`. -/
def parseOpMain (file format stop : String) : IO UInt32 := do
  unless parseOpPhases.contains stop do
    IO.eprintln s!"l4query-phases: unknown --parse-op phase '{stop}' ({String.intercalate " | " parseOpPhases})"
    return 2
  let t0 ← IO.monoNanosNow
  let report := report t0
  report "start" 0
  let text ← IO.FS.readFile file
  report "read" text.utf8ByteSize
  if stop == "read" then return 0
  match L4Wasm.Ops.parseDocumentOutcomeBy L4Wasm.Ops.noExtraReader text format "" with
  | .error f => IO.eprintln f.message; pure 1
  | .ok o =>
    report "parse" (L4Wasm.Ops.datasetQuadCount o.ds)
    if stop == "parse" then return 0
    let ds := L4Wasm.Ops.scopeBnodes "d0_" o.ds
    report "scope" (L4Wasm.Ops.datasetQuadCount ds)
    if stop == "scope" then return 0
    let nq := L4Factoidal.Syntax.Dataset.toCanonicalNQuads ds
    report "nquads" nq.utf8ByteSize
    if stop == "nquads" then return 0
    let env := L4Wasm.Ops.okWith
      [("count", .number (toString (L4Wasm.Ops.datasetQuadCount ds))),
       ("nquads", .string nq),
       ("prefixes", L4Wasm.Ops.prefixesJson o.prefixes)]
    report "envelope" env.utf8ByteSize
    if stop == "envelope" then return 0
    IO.println env
    report "output" env.utf8ByteSize
    pure 0

def closureOpPhases : List String :=
  ["read", "parse", "normalize", "closure", "ntriples", "envelope", "decode", "output"]

/-- `--closure-op`: the phases of `l4factoidal closure --regime owl-rl` as it
was until https://github.com/danbri/factoidal/issues/758: `read`, `parse`
(`Ops.parseTextToDataset`), `normalize` (`datasetForOps .rdf11`, the dataset
`Ops.owlClosureOf` closes), `closure` (`OWL.RL.closureFix` of the default
graph; V is its length), `ntriples` (`Graph.toNTriples`; V is its length in
bytes), `envelope` (`okWith`, the op's JSON string), `decode` (the JSON parse
of the envelope `Cli.parseEnvelope` makes, and the `nquads` member), `output`
(that member written). -/
def closureOpMain (file format stop : String) : IO UInt32 := do
  unless closureOpPhases.contains stop do
    IO.eprintln s!"l4query-phases: unknown --closure-op phase '{stop}' ({String.intercalate " | " closureOpPhases})"
    return 2
  let t0 ← IO.monoNanosNow
  let report := report t0
  report "start" 0
  let text ← IO.FS.readFile file
  report "read" text.utf8ByteSize
  if stop == "read" then return 0
  match L4Wasm.Ops.parseTextToDataset text format "" with
  | .error e => IO.eprintln e; pure 1
  | .ok ds =>
    report "parse" (L4Wasm.Ops.datasetQuadCount ds)
    if stop == "parse" then return 0
    match datasetForOps .rdf11 ds with
    | .error _ => IO.eprintln "normalize: parse error"; pure 1
    | .ok nds =>
      report "normalize" (L4Wasm.Ops.datasetQuadCount nds)
      if stop == "normalize" then return 0
      let g := L4Factoidal.OWL.RL.closureFix nds.default
      report "closure" g.length
      if stop == "closure" then return 0
      match L4Factoidal.Syntax.Graph.toNTriples g with
      | .error e => IO.eprintln e; pure 1
      | .ok lines =>
        report "ntriples" lines.utf8ByteSize
        if stop == "ntriples" then return 0
        let env := L4Wasm.Ops.okWith [("nquads", .string lines)]
        report "envelope" env.utf8ByteSize
        if stop == "envelope" then return 0
        match L4Factoidal.JSON.parseJson env with
        | .error e => IO.eprintln s!"internal: op result was not JSON ({e})"; pure 1
        | .ok j =>
          let out := (j.getString? "nquads").getD ""
          report "decode" out.utf8ByteSize
          if stop == "decode" then return 0
          IO.println out
          report "output" out.utf8ByteSize
          pure 0

def rdfxmlOpPhases : List String := ["read", "chars", "xml", "grammar", "stream", "nquads", "output"]

/-- `--rdfxml-op`: the phases of `l4factoidal parse FILE --format rdfxml --out
nquads` (https://github.com/danbri/factoidal/issues/814,
https://github.com/danbri/factoidal/issues/771): `read` (the file as a
`String`), `chars` (the XML layer's character array alone,
`XML.documentChars`; V is its size; a process that stops here does not run
`xml`), `xml` (`XML.parseXML`, the tokenizer and the element tree of XML 1.0;
V is the number of children of the document element), `grammar`
(`RdfXml.processDocument` with the fuel and state `RdfXml.parseRdfXml` gives
it, the productions of RDF 1.1 XML Syntax section 7; V is the number of
triples), `nquads` (`Dataset.toCanonicalNQuads` of the graph as the default
graph; V is its length in bytes), `output` (that text written). With
`--stream` the phases `xml` and `grammar` are replaced by `stream`:
`RdfXml.parseRdfXml` as compiled, which runs `parseRdfXmlStream` and builds no
element tree of the document element (`RdfXml.parseRdfXml_eq_stream`); V is
the number of triples. -/
def rdfxmlOpMain (file stop : String) (stream : Bool) : IO UInt32 := do
  unless rdfxmlOpPhases.contains stop do
    IO.eprintln s!"l4query-phases: unknown --rdfxml-op phase '{stop}' ({String.intercalate " | " rdfxmlOpPhases})"
    return 2
  let t0 ← IO.monoNanosNow
  let report := report t0
  report "start" 0
  let text ← IO.FS.readFile file
  report "read" text.utf8ByteSize
  if stop == "read" then return 0
  if stop == "chars" then
    report "chars" (L4Factoidal.XML.documentChars false text).1.size
    return 0
  if stream then
    -- `parseRdfXml`, which runs `parseRdfXmlStream` (no element tree).
    match L4Factoidal.Syntax.RdfXml.parseRdfXml text with
    | .error e => IO.eprintln e.msg; return 1
    | .ok g =>
      report "stream" g.length
      if stop == "stream" then return 0
      let nq := L4Factoidal.Syntax.Dataset.toCanonicalNQuads { default := g, named := [] }
      report "nquads" nq.utf8ByteSize
      if stop == "nquads" then return 0
      IO.println nq
      report "output" nq.utf8ByteSize
      return 0
  match L4Factoidal.XML.parseXML text with
  | .error e => IO.eprintln s!"XML: {e.message}"; pure 1
  | .ok doc =>
    report "xml" doc.root.elementChildren.length
    if stop == "xml" then return 0
    let res := L4Factoidal.Syntax.RdfXml.processDocument (text.length + 2)
      (L4Factoidal.Syntax.RdfXml.St.init "") doc.root
    match res.st.err with
    | some e => IO.eprintln e.msg; pure 1
    | none =>
      report "grammar" res.triples.length
      if stop == "grammar" then return 0
      let nq := L4Factoidal.Syntax.Dataset.toCanonicalNQuads { default := res.triples, named := [] }
      report "nquads" nq.utf8ByteSize
      if stop == "nquads" then return 0
      IO.println nq
      report "output" nq.utf8ByteSize
      pure 0

def parseCliPhases : List String := ["read", "chars", "parse", "normalize", "nquads", "output"]

/-- `--parse-cli`: the phases of `l4factoidal parse FILE [--out nquads]` as
`parseCmd` in `Wasm/Cli.lean` ran them before
https://github.com/danbri/factoidal/issues/813: `read` (`readInput`, the
whole file as one `String`), `chars` (the whole-document `String.toList`
that `parseNTriples` and `parseNQuadsFast` start with; V is its length),
`parse` (`Ops.parseTextToDataset`; V is the quad count), `normalize` (the
count `parse` prints without `--out`: `normalizeDataset`, then the quad
count), `nquads` (`Dataset.toCanonicalNQuads` of the parsed dataset, what
`--out nquads` prints; V is its length in bytes), `output` (that text
written). `chars` is a phase of its own only when `--stop-after chars`
asks for it; otherwise the list is built inside `parse`. -/
def parseCliMain (file format stop : String) : IO UInt32 := do
  unless parseCliPhases.contains stop do
    IO.eprintln s!"l4query-phases: unknown --parse-cli phase '{stop}' ({String.intercalate " | " parseCliPhases})"
    return 2
  let t0 ← IO.monoNanosNow
  let report := report t0
  report "start" 0
  let text ← IO.FS.readFile file
  report "read" text.utf8ByteSize
  if stop == "read" then return 0
  if stop == "chars" then
    report "chars" text.toList.length
    return 0
  match L4Wasm.Ops.parseTextToDataset text format "" with
  | .error e => IO.eprintln e; pure 1
  | .ok ds =>
    report "parse" (L4Wasm.Ops.datasetQuadCount ds)
    if stop == "parse" then return 0
    if stop == "normalize" then
      report "normalize" (L4Wasm.Ops.datasetQuadCount (normalizeDataset ds))
      return 0
    let nq := L4Factoidal.Syntax.Dataset.toCanonicalNQuads ds
    report "nquads" nq.utf8ByteSize
    if stop == "nquads" then return 0
    IO.println nq
    report "output" nq.utf8ByteSize
    pure 0

/-- The phases of `l4factoidal query` on `file`. -/
def queryMain (file : String) (rest : List String) : IO UInt32 := do
    let format := (flagValue rest "--format").getD "turtle"
    let sparql := (flagValue rest "--query-string").getD
      "SELECT (COUNT(*) AS ?c) WHERE { ?s ?p ?o }"
    let stop := (flagValue rest "--stop-after").getD "output"
    unless phases.contains stop do
      IO.eprintln s!"l4query-phases: unknown phase '{stop}' ({String.intercalate " | " phases})"
      return 2
    let t0 ← IO.monoNanosNow
    let report := report t0
    report "start" 0
    let text ← IO.FS.readFile file
    report "read" text.utf8ByteSize
    if stop == "read" then return 0
    if stop == "chars" then
      report "chars" text.toList.length
      return 0
    match L4Wasm.Ops.parseTextToDataset text format "" with
    | .error e => IO.eprintln e; pure 1
    | .ok ds =>
      report "parse" (L4Wasm.Ops.datasetQuadCount ds)
      if stop == "parse" then return 0
      match datasetForOps .rdf12 ds with
      | .error _ => IO.eprintln "normalize: parse error"; pure 1
      | .ok nds =>
        report "normalize" (L4Wasm.Ops.datasetQuadCount nds)
        if stop == "normalize" then return 0
        -- `--no-index` (diagnostic): the reference evaluator, no backend.
        let dsb := L4Factoidal.Dataflow.LawfulDataset.ofDataset nds
        -- NOW() (SPARQL 1.1 §17.4.5.1): the clock is read once per execution,
        -- as `l4factoidal query` does (https://github.com/danbri/factoidal/issues/748).
        let now ← L4Wasm.Ops.nowDateTime
        if rest.contains "--no-index" then
          let out := L4Wasm.Ops.queryParsedDatasetWith nds none sparql (now := some now)
          report "eval-no-index" out.utf8ByteSize
          return 0
        report "index" (match dsb.backend.default with
          | .indexed ix => ix.all.size
          | _ => 0)
        if stop == "index" then return 0
        if stop == "solutions" then
          report "solutions" (selectSolutionCount nds dsb sparql (some now))
          return 0
        let out := L4Wasm.Ops.queryParsedDatasetWith nds (some dsb) sparql (now := some now)
        report "eval" out.utf8ByteSize
        if stop == "eval" then return 0
        -- `Cli.parseEnvelope` (Wasm/Cli.lean, which this harness cannot import:
        -- it defines `main`): parse the envelope, require `"ok":true`.
        match L4Factoidal.JSON.parseJson out with
        | .error e => IO.eprintln s!"internal: op result was not JSON ({e})"; pure 1
        | .ok j =>
          if j.getBool? "ok" != some true then
            IO.eprintln ((j.getString? "error").getD "unknown error"); return 1
          report "decode" 1
          if stop == "decode" then return 0
          -- `printQueryResult` of a SELECT: the `srj` member, pretty-printed.
          match j.getString? "kind", j.field? "srj" with
          | some "select", some srj =>
            let txt := srj.toStringPretty
            report "render" txt.utf8ByteSize
            if stop == "render" then return 0
            IO.println txt
            report "output" txt.utf8ByteSize
            pure 0
          | _, _ =>
            IO.eprintln "l4query-phases: the render and output phases are for SELECT only"
            pure 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--walk-check", listFile] => walkCheck listFile
  | file :: rest =>
    if rest.contains "--parse-op" then
      parseOpMain file ((flagValue rest "--format").getD "turtle")
        ((flagValue rest "--stop-after").getD "output")
    else if rest.contains "--rdfxml-op" then
      rdfxmlOpMain file ((flagValue rest "--stop-after").getD "output") (rest.contains "--stream")
    else if rest.contains "--parse-cli" then
      parseCliMain file ((flagValue rest "--format").getD "turtle")
        ((flagValue rest "--stop-after").getD "output")
    else if rest.contains "--closure-op" then
      closureOpMain file ((flagValue rest "--format").getD "nquads")
        ((flagValue rest "--stop-after").getD "output")
    else queryMain file rest
  | [] =>
      IO.eprintln "usage: l4query-phases FILE [--format F] [--query-string Q] [--stop-after PHASE]"
      pure 2

end Harness.QueryPhases

def main (args : List String) : IO UInt32 := Harness.QueryPhases.main args
