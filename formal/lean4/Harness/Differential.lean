/-
Harness.Differential — `l4diff`: the same (dataset, query) pair run
through the F* native binary (`bin/<platform>/factoidal`) and through
the Lean evaluator, compared with the W3C harness's own comparator.

    l4diff [--fstar BIN] [--lean-cli PATH] [--gen N] [--seed S] [--tmp DIR] [--verbose]
           [manifest.ttl ...]

Corpus:
  * every `QueryEvaluationTest` / `CSVResultFormatTest` of the
    manifests given (`sparql11/manifest-all.ttl` follows its
    `mf:include`s, as `Harness.Main` does) — the real W3C files, read
    off disk by both trees; a test the CLI cannot express (SERVICE
    data, an entailment regime) is `skipped`, named and counted;
  * `--gen N` seeded cases from `L4Factoidal.Testing.Gen` (seeds
    S .. S+N-1): the graph is written as N-Triples and the query as
    text under `--tmp`, and BOTH trees read those files.

The F* side is driven through `IO.Process` — that is harness code,
outside `L4Factoidal/`. The query is run with `-o json` (SELECT / ASK,
read back with `parseSrj`) or `-o ntriples` (CONSTRUCT, read back with
`parseNTriples`); the Lean side is `parseSparql` + `evalSelect` /
`evalAsk` / `evalConstruct`, the path `Harness/Run.lean` takes.

`--lean-cli PATH` runs the Lean side through the Lean command line
(`l4factoidal query`, `Wasm/Cli.lean`) instead of the library, with the
query FILE the F* side gets, and compares its PRINTED answer: SPARQL
Results JSON for SELECT, `true`/`false` for ASK, N-Triples for CONSTRUCT.
The data: a test with one `qt:data` file and no `qt:graphData` gives the
CLI that file (format by extension, base = the file's IRI, as
`parseDataFile`); any other test gives it the test's dataset as one
N-Quads file under `--tmp` (the CLI reads one dataset), each `qt:graphData`
graph named by its file's IRI. A generated case gives the CLI the same
`.nt` and `.rq` files as the F* side. The default mode compares the Lean
LIBRARY with the F* COMMAND LINE, so it cannot see a defect of the Lean
command line or of the Lean serialisers; on 2026-10-10 two such defects
(https://github.com/danbri/factoidal/issues/741 and
https://github.com/danbri/factoidal/issues/742) were in the items the
default mode reported as Lean-correct (design note,
`docs/designissues/2026-10-10-lean-vs-fstar-differential.md`, "Correction").

Outcomes per case: `agree` / `disagree` / `tie-order` / `fstar-error`
/ `lean-error` / `skipped`. `tie-order` is a disagreement that
disappears when ORDER BY row positions are not pinned: the comparator
pins positions only for rows with blank nodes, and two correct engines
may order tied blank-node rows differently (§15.1 fixes no order
between blank nodes), so it is reported separately rather than as a
disagreement or an agreement. Every disagreement is printed as (query,
F* rows, Lean rows). The harness never "fixes" a comparison to make it
pass: a disagreement is a finding about one of the two trees and is
attributed by reading the specification, in the design note.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import Harness.Run
import L4Factoidal.Testing.Props

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Syntax L4Factoidal.Testing

namespace Harness.Diff

inductive DiffOutcome where
  | agree      (rows : Nat)
  | disagree   (detail : String) (rows : Nat)
  | tieOrder   (detail : String) (rows : Nat)
  | fstarError (msg : String)
  | leanError  (msg : String)
  | skipped    (reason : String)

structure DiffScore where
  agree      : Nat := 0
  disagree   : Nat := 0
  tieOrder   : Nat := 0
  fstarError : Nat := 0
  leanError  : Nat := 0
  skipped    : Nat := 0
  rows       : Nat := 0

def DiffScore.total (s : DiffScore) : Nat :=
  s.agree + s.disagree + s.tieOrder + s.fstarError + s.leanError + s.skipped

def DiffScore.add (a b : DiffScore) : DiffScore :=
  { agree := a.agree + b.agree, disagree := a.disagree + b.disagree,
    tieOrder := a.tieOrder + b.tieOrder, fstarError := a.fstarError + b.fstarError,
    leanError := a.leanError + b.leanError, skipped := a.skipped + b.skipped,
    rows := a.rows + b.rows }

def DiffScore.bump (s : DiffScore) : DiffOutcome → DiffScore
  | .agree n        => { s with agree := s.agree + 1, rows := s.rows + n }
  | .disagree _ n   => { s with disagree := s.disagree + 1, rows := s.rows + n }
  | .tieOrder _ n   => { s with tieOrder := s.tieOrder + 1, rows := s.rows + n }
  | .fstarError _   => { s with fstarError := s.fstarError + 1 }
  | .leanError _    => { s with leanError := s.leanError + 1 }
  | .skipped _      => { s with skipped := s.skipped + 1 }

/-- The score line: every numerator labelled, denominator present,
and the measurement check (rows + triples compared) on the same line. -/
def DiffScore.line (label : String) (s : DiffScore) : String :=
  s!"DIFF {label}: {s.agree} agree, {s.disagree} disagree, {s.tieOrder} tie-order, " ++
  s!"{s.fstarError} fstar-error, {s.leanError} lean-error, {s.skipped} skipped " ++
  s!"(out of {s.total}); rows_or_triples_compared={s.rows}"

def DiffOutcome.line (name : String) : DiffOutcome → String
  | .agree _        => s!"AGREE {name}"
  | .disagree d _   => s!"DISAGREE {name}: {d}"
  | .tieOrder d _   => s!"TIE-ORDER {name}: {d}"
  | .fstarError m   => s!"FSTAR-ERROR {name}: {m}"
  | .leanError m    => s!"LEAN-ERROR {name}: {m}"
  | .skipped r      => s!"SKIP {name}: {r}"

def DiffOutcome.isQuiet : DiffOutcome → Bool
  | .agree _ => true
  | _        => false

/-! ## Running the F* binary -/

/-- Run the binary under `perl -e 'alarm …'` so a hung query cannot
hang the run (anti-pattern #17). -/
def runFstar (bin : String) (args : List String) (timeoutSec : Nat := 60) :
    IO (UInt32 × String × String) := do
  let out ← IO.Process.output
    { cmd := "perl",
      args := #["-e", "alarm shift; exec @ARGV", toString timeoutSec, bin] ++ args.toArray }
  return (out.exitCode, out.stdout, out.stderr)

def firstLine (s : String) : String :=
  match s.splitOn "\n" with
  | l :: _ => l
  | []     => s

def showRows (rows : List Binding) : String :=
  let shown := String.intercalate " | " (rows.take 25 |>.map (fun r => "[" ++ rowShow r ++ "]"))
  if rows.length > 25 then shown ++ s!" … ({rows.length} rows)" else shown

def showGraph (g : Graph) : String :=
  match Graph.toNTriples (g.take 25) .rdf11 with
  | .ok s    => s.replace "\n" " "
  | .error e => s!"<<unserialisable: {e}>>"

/-! ## The comparison — pure -/

/-- The Lean side's answer: from the library (`leanLibAnswer`) or read
back from the Lean command line's output (`leanCliAnswer`). -/
inductive LeanAnswer where
  | rows    (rows : List Binding)
  | boolean (b : Bool)
  | graph   (g : Graph)
  | failed  (msg : String)
  | skip    (reason : String)

def describeSkip : String := "DESCRIBE (the F* tree answers it with the empty graph)"

/-- The Lean library's answer to `q` over `ds`. -/
def leanLibAnswer (env : EvalEnv) (ds : Dataset) (q : Query) : LeanAnswer :=
  -- Federated Query §2.3: the Lean answer is the error when a SERVICE
  -- call without SILENT fails (`Query.serviceFailure`).
  match q.serviceFailure env ds with
  | some f => .failed f.message
  | none =>
  match q.form with
  | .describe _  => .skip describeSkip
  | .ask         => .boolean (evalAsk env ds q)
  | .select _    => .rows (evalSelect env ds q).2
  | .construct _ => .graph (evalConstruct env ds q)

/-- SELECT: the F* rows against the Lean rows. -/
def selectOutcome (tag : String) (q : Query) (frows lrows : List Binding) : DiffOutcome :=
  let n := frows.length + lrows.length
  let ordered := q.modifier.orderBy.isSome
  let detail := s!"{tag}; F* rows: {showRows frows}; Lean rows: {showRows lrows}"
  match compareSelectRows ordered false frows lrows with
  | .equal => .agree n
  | .budgetExceeded => .disagree s!"{tag}; bijection budget exceeded" n
  | .notEqual =>
      if ordered && compareSelectRows false false frows lrows == .equal then
        .tieOrder detail n
      else .disagree detail n

/-- CONSTRUCT: the F* graph against the Lean graph. -/
def constructOutcome (tag : String) (fg lg : Graph) : DiffOutcome :=
  let n := fg.length + lg.length
  match Graph.isomorphicOutcome fg lg with
  | .equal => .agree n
  | .budgetExceeded => .disagree s!"{tag}; isomorphism budget exceeded" n
  | .notEqual => .disagree s!"{tag}; F* graph: {showGraph fg}; Lean graph: {showGraph lg}" n

/-- Compare the F* output text with the Lean answer to `q`. `queryText`
is echoed into every non-agreeing line. -/
def compareAnswers (queryText : String) (q : Query) (fstarOut : String)
    (lean : LeanAnswer) : DiffOutcome :=
  let tag := s!"query: {queryText.replace "\n" " "}"
  match lean with
  | .failed m => .leanError s!"{m}; {tag}"
  | .skip r   => .skipped r
  | _ =>
  match q.form with
  | .describe _ => .skipped describeSkip
  | .ask =>
      match parseSrj fstarOut with
      | .error e => .fstarError s!"F* JSON did not parse ({e}): {firstLine fstarOut}"
      | .ok (.boolean b) =>
          match lean with
          | .boolean a =>
              if a == b then .agree 1 else .disagree s!"{tag}; F* {b}; Lean {a}" 1
          | _ => .leanError s!"the Lean side gave no boolean for an ASK; {tag}"
      | .ok (.bindings _ _) => .disagree s!"{tag}; F* returned bindings for an ASK" 0
  | .select _ =>
      match parseSrj fstarOut with
      | .error e => .fstarError s!"F* JSON did not parse ({e}): {firstLine fstarOut}"
      | .ok (.boolean _) => .disagree s!"{tag}; F* returned a boolean for a SELECT" 0
      | .ok (.bindings _ frows) =>
          match lean with
          | .rows lrows => selectOutcome tag q frows lrows
          | _ => .leanError s!"the Lean side gave no rows for a SELECT; {tag}"
  | .construct _ =>
      match parseNTriples fstarOut .rdf11 with
      | .error e => .fstarError s!"F* N-Triples did not parse ({e.msg} at {e.pos}): {firstLine fstarOut}"
      | .ok fg =>
          match lean with
          | .graph lg => constructOutcome tag fg lg
          | _ => .leanError s!"the Lean side gave no graph for a CONSTRUCT; {tag}"

/-- The default mode: the F* output against the Lean library's answer. -/
def compareOutputs (queryText : String) (env : EvalEnv) (ds : Dataset) (q : Query)
    (fstarOut : String) : DiffOutcome :=
  compareAnswers queryText q fstarOut (leanLibAnswer env ds q)

/-! ## The Lean command line (`--lean-cli`) -/

/-- Read the Lean command line's printed answer back (`l4factoidal query`:
SPARQL Results JSON for SELECT; `true` exit 0 / `false` exit 1 for ASK;
N-Triples for CONSTRUCT; an error is exit 1 with the message on stderr). -/
def leanCliAnswer (cli : String) (q : Query) (args : List String) : IO LeanAnswer := do
  match q.form with
  | .describe _ => return .skip describeSkip
  | _ =>
  let (rc, out, err) ← runFstar cli ("query" :: args)
  let failed := LeanAnswer.failed s!"Lean CLI exit {rc}: {firstLine (err ++ out)}"
  let word := String.ofList (out.toList.filter (fun c => !c.isWhitespace))
  match q.form with
  | .ask =>
      if rc == 0 && word == "true" then return .boolean true
      else if rc == 1 && word == "false" then return .boolean false
      else return failed
  | .select _ =>
      if rc != 0 then return failed
      match parseSrj out with
      | .ok (.bindings _ rows) => return .rows rows
      | .ok (.boolean _) => return .failed "Lean CLI printed a boolean for a SELECT"
      | .error e => return .failed s!"Lean CLI JSON did not parse ({e}): {firstLine out}"
  | _ =>
      if rc != 0 then return failed
      match parseNTriples out .rdf11 with
      | .ok g => return .graph g
      | .error e =>
          return .failed s!"Lean CLI N-Triples did not parse ({e.msg} at {e.pos}): {firstLine out}"

/-- The outcome in `--lean-cli` mode. The Lean command line runs even when
the F* run failed, and its failure is counted first: a defect the two command
lines share (issues 739 and 741: no base IRI for the query) is then a
`lean-error`, and is not hidden behind the `fstar-error`. -/
def cliOutcome (queryText : String) (q : Query) (rc : UInt32) (out err : String)
    (lean : LeanAnswer) : DiffOutcome :=
  let tag := s!"query: {queryText.replace "\n" " "}"
  match lean with
  | .failed m =>
      if rc != 0 then .leanError s!"{m}; F* also failed, exit {rc}: {firstLine (err ++ out)}; {tag}"
      else .leanError s!"{m}; {tag}"
  | _ =>
      if rc != 0 then .fstarError s!"exit {rc}: {firstLine (err ++ out)}; {tag}"
      else compareAnswers queryText q out lean

/-- The `--format` tag for a data file, by extension (as `parseDataFile`). -/
def cliFormatOf (path : String) : String :=
  if path.endsWith ".nt" then "ntriples"
  else if path.endsWith ".nq" then "nquads"
  else if path.endsWith ".trig" then "trig"
  else if path.endsWith ".rdf" then "rdfxml"
  else "turtle"

/-- The Lean command line's data arguments for a W3C test: its one data
file, or the loaded dataset as one N-Quads file under `tmp`. -/
def cliDataArgs (tmp : String) (tc : TestCase) (ds : Dataset) : IO (List String) := do
  match tc.dataFiles, tc.graphData with
  | [f], [] => return [f, "--format", cliFormatOf f, "--base", "file://" ++ f]
  | _, _ =>
      IO.FS.createDirAll tmp
      let nq := tmp ++ "/lean_cli_dataset.nq"
      IO.FS.writeFile nq (Dataset.toCanonicalNQuads ds)
      return [nq, "--format", "nquads"]

/-! ## W3C corpus -/

def diffTestCase (bin : String) (leanCli : Option String) (tmp : String) (tc : TestCase) :
    IO DiffOutcome := do
  if tc.testType != "QueryEvaluationTest" && tc.testType != "CSVResultFormatTest" then
    return .skipped s!"not a query evaluation test ({tc.testType})"
  if !tc.entailmentRegimes.isEmpty then
    return .skipped s!"entailment regime {String.intercalate "/" tc.entailmentRegimes} (not driven through the CLI)"
  if !tc.serviceData.isEmpty then
    return .skipped "SERVICE data (the CLI has no qt:serviceData form)"
  let some qf := tc.queryFile
    | return .skipped "mf:action carries no qt:query"
  let some qtext ← readOpt qf
    | return .skipped s!"file missing: {qf}"
  match parseSparql qtext (some ("file://" ++ qf)) with
  | .error e => return .leanError s!"SPARQL parse: {fmtParseError e}; query: {qtext.replace "\n" " "}"
  | .ok q =>
  match ← loadFixtures tc with
  | .error o => return .skipped (Outcome.line "fixtures" o)
  | .ok (ds, services) =>
  let fmt := match q.form with
    | .construct _ => "ntriples"
    | _            => "json"
  -- No `-b`: the CLI parses the query with NO base at all
  -- (`bin/factoidal-cli/factoidal_cli.ml` calls `parse_sparql
  -- query_text`; `-b` rebases only the DATA files), so a query with a
  -- relative IRI (`FROM <data.ttl>`, `GRAPH <ng-01.ttl>`) is an
  -- `fstar-error` here — counted and named, not hidden. Passing `-b`
  -- was tried (2026-08-22): it does not reach the query parser and it
  -- changes the data files' base, which broke one exists test.
  let args := tc.dataFiles.flatMap (fun f => ["-d", f]) ++
              tc.graphData.flatMap (fun (iri, f) => ["-n", iri ++ "=" ++ f]) ++
              ["--query", qf, "-o", fmt]
  let (rc, out, err) ← runFstar bin args
  match leanCli with
  | some cli =>
      let dataArgs ← cliDataArgs tmp tc ds
      let lean ← leanCliAnswer cli q (dataArgs ++ ["--query", qf])
      return cliOutcome qtext q rc out err lean
  | none =>
  if rc != 0 then
    return .fstarError s!"exit {rc}: {firstLine (err ++ out)}; query: {qtext.replace "\n" " "}"
  let env : EvalEnv := { now := some fixedNow, services := services, base := q.base }
  return compareOutputs qtext env ds q out

/-- Walk one manifest (following includes) and diff every entry. -/
def diffManifest : Nat → String → Option String → String → System.FilePath → Bool → IO DiffScore
  | 0, _, _, _, path, _ => do
      IO.println s!"  (mf:include nesting too deep: {path})"
      return {}
  | depth + 1, bin, leanCli, tmp, path, verbose => do
    let label := suiteLabel path.toString
    match ← loadManifest path with
    | none =>
        IO.println (DiffScore.line label {})
        IO.println s!"  (manifest not found: {path} — run tools/ensure-test-env.sh)"
        return {}
    | some (.error e) =>
        IO.println (DiffScore.line label {})
        IO.println s!"  (manifest did NOT parse: {e})"
        return {}
    | some (.ok (tests, _)) =>
        let abs := (← IO.FS.realPath path).toString
        let includes ← if tests.isEmpty then
            (match ← readOpt path with
             | some text => pure (parseManifestIncludes abs text)
             | none      => pure [])
          else pure []
        if tests.isEmpty && !includes.isEmpty then
          let mut total : DiffScore := {}
          for inc in includes do
            total := total.add (← diffManifest depth bin leanCli tmp (System.FilePath.mk inc) verbose)
          IO.println (DiffScore.line (label ++ " (all)") total)
          return total
        else
          let mut score : DiffScore := {}
          for tc in tests do
            let r ← diffTestCase bin leanCli tmp tc
            score := score.bump r
            if verbose || !r.isQuiet then IO.println (r.line tc.name)
          IO.println (DiffScore.line label score)
          return score

/-! ## Generated corpus -/

def diffGenerated (bin : String) (leanCli : Option String) (tmp : String) (seed : Nat) :
    IO (Case × DiffOutcome) := do
  let c := genCase seed
  let nt := tmp ++ "/case_" ++ toString seed ++ ".nt"
  let rq := tmp ++ "/case_" ++ toString seed ++ ".rq"
  IO.FS.writeFile nt c.graphText
  IO.FS.writeFile rq c.queryText
  -- Both trees read the files back: the Lean side through the same
  -- parsers the harness uses, so the serialiser is exercised too.
  let some ntText ← readOpt nt | return (c, .leanError "could not re-read the N-Triples file")
  let some rqText ← readOpt rq | return (c, .leanError "could not re-read the query file")
  match parseNTriples ntText .rdf11 with
  | .error e => return (c, .leanError s!"N-Triples parse: {e.msg} (offset {e.pos})")
  | .ok g =>
  match parseSparql rqText none with
  | .error e => return (c, .leanError s!"SPARQL parse: {fmtParseError e}; query: {rqText}")
  | .ok q =>
  let fmt := match q.form with
    | .construct _ => "ntriples"
    | _            => "json"
  let (rc, out, err) ← runFstar bin ["-d", nt, "--query", rq, "-o", fmt]
  match leanCli with
  | some cli =>
      let lean ← leanCliAnswer cli q [nt, "--format", "ntriples", "--query", rq]
      return (c, cliOutcome rqText q rc out err lean)
  | none =>
  if rc != 0 then
    return (c, .fstarError s!"exit {rc}: {firstLine (err ++ out)}; query: {rqText}")
  let env : EvalEnv := { now := some fixedNow, base := q.base }
  return (c, compareOutputs rqText env { default := g, named := [] } q out)

/-! ## main -/

def findFlag : List String → String → Option String
  | [], _ => none
  | a :: rest, flag => if a == flag then rest.head? else findFlag rest flag

def parseNatArg (args : List String) (flag : String) (dflt : Nat) : Nat :=
  match findFlag args flag with
  | some v => v.toNat?.getD dflt
  | none   => dflt

def parseStrArg (args : List String) (flag : String) (dflt : String) : String :=
  (findFlag args flag).getD dflt

/-- Positional arguments: everything that is neither a flag nor a
flag's value. -/
def positional (args : List String) : List String :=
  let valued := ["--fstar", "--lean-cli", "--gen", "--seed", "--tmp"]
  let rec go : List String → List String
    | []          => []
    | a :: b :: rest => if valued.contains a then go rest
                        else if a.startsWith "--" then go (b :: rest)
                        else a :: go (b :: rest)
    | [a]         => if a.startsWith "--" then [] else [a]
  go args

def main (args : List String) : IO UInt32 := do
  let bin := parseStrArg args "--fstar" "bin/darwin-arm64/factoidal"
  let genN := parseNatArg args "--gen" 0
  let seed0 := parseNatArg args "--seed" 0
  let tmp := parseStrArg args "--tmp" ".claude-runs/l4diff-cases"
  let verbose := args.contains "--verbose"
  let leanCli := findFlag args "--lean-cli"
  let manifests := positional args
  if manifests.isEmpty && genN == 0 then
    IO.eprintln "usage: l4diff [--fstar BIN] [--lean-cli PATH] [--gen N] [--seed S] [--tmp DIR] [--verbose] [manifest.ttl ...]"
    IO.eprintln "  run from the repository root so bin/<platform>/factoidal and the manifests resolve"
    return 2
  if !(← System.FilePath.pathExists bin) then
    IO.eprintln s!"F* binary not found: {bin} (pass --fstar PATH; run from the repository root)"
    return 2
  match leanCli with
  | some cli =>
      if !(← System.FilePath.pathExists cli) then
        IO.eprintln s!"Lean CLI not found: {cli} (pass --lean-cli PATH, e.g. formal/lean4/.lake/build/bin/l4factoidal)"
        return 2
      IO.println s!"Lean side: the command line {cli} (query FILE), not the library"
  | none => IO.println "Lean side: the library (parseSparql + evalSelect / evalAsk / evalConstruct)"
  let mut total : DiffScore := {}
  for m in manifests do
    total := total.add (← diffManifest 4 bin leanCli tmp (System.FilePath.mk m) verbose)
  if genN > 0 then
    IO.FS.createDirAll tmp
    let mut score : DiffScore := {}
    for i in List.range genN do
      let (c, r) ← diffGenerated bin leanCli tmp (seed0 + i)
      score := score.bump r
      if verbose || !r.isQuiet then
        IO.println (r.line s!"generated seed {c.seed}")
        if !r.isQuiet then
          IO.println s!"  graph (N-Triples): {c.graphText.replace "\n" " "}"
    IO.println (DiffScore.line s!"generated ({genN} cases from seed {seed0})" score)
    total := total.add score
  IO.println (DiffScore.line "TOTAL" total)
  return (if total.disagree == 0 && total.fstarError == 0 && total.leanError == 0 then 0 else 1)

end Harness.Diff

def main (args : List String) : IO UInt32 := Harness.Diff.main args
