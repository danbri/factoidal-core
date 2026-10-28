/-
Harness/N3Run — the W3C N3 Community Group test suite, run with the Lean
Notation3 reader (`L4Factoidal/N3/`).

Suite: https://github.com/w3c/N3 `tests/`, vendored as the submodule
`third_party/testing/n3` (commit and versions in
`third_party/testing/n3-PROVENANCE.md`). Tracking:
https://github.com/danbri/factoidal/issues/1165.

## What each test type checks

  * `test:TestN3PositiveSyntax`: the document reads; then the writer's text
    for it reads again to the same triples in the same order, up to the
    names of blank nodes (`relabel`, `N3/Compare.lean`), so every positive
    syntax test is also a writer round-trip test.
  * `test:TestN3NegativeSyntax`: the reader refuses the document.
  * `test:TestN3Eval`: the document reads to a graph isomorphic to the one in
    `mf:result` (`readExpected`, `compareExpected`).
  * `rdft:TestTurtle*` (the suite's `TurtleTests`, or any RDF Turtle manifest
    given on the command line): the Turtle types, run with the N3 reader. An
    eval test converts the N3 graph to RDF (`N3/Rdf.lean`) and compares it with
    the N-Triples result. Each of these tests also runs the Turtle reader on
    the same text and counts in a second line, `turtle-agreement`, whether the
    two readers agree: both refuse, or both accept with isomorphic graphs.
  * `test:TestN3Reason`: the reasoner (`N3/Reason.lean`) on the document, with
    the entry's `test:options` (`optionsOf`), gives a graph isomorphic to the
    one in `mf:result`.

A test in `defective` is reported as `EXCLUDED`, apart from the total, with
its issue. A test in `expectedFail` that fails is counted as `expected-fail`
with its issue.

## Approval

The suite's README: tests marked `rdft:Rejected` "are non-conformance
compatibility tests and should be reported separately rather than counted as
current-spec failures" (for example the `@forAll`/`@forSome` cases, which the
current specification removed). They run, and are counted in their own score
line, `<suite> (rdft:Rejected)`, which does not make the run fail.

## Base IRI

The suite's README: "Tests should be run with an assumed base URI of their
associated manifest, either `https://w3c.github.io/N3/tests/N3Tests` or
`https://w3c.github.io/N3/tests/TurtleTests`". The expected results resolve
relative references as `https://w3c.github.io/N3/tests/N3Tests/<path>` and
`https://w3c.github.io/N3/tests/TurtleTests/<file>`. A manifest's `mf:assumedTestBase` wins over both.
A result file is read with the base of its action.

Usage: `lake exe l4n3 [--rdf12] [--quiet] <manifest.ttl>...`
Exit code 0 when no counted test failed.
-/
import Harness.Manifest
import L4Factoidal.N3.Compare
import L4Factoidal.N3.Rdf
import L4Factoidal.N3.Reason
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.NQuadsFastTheorems
import L4Factoidal.Syntax.NTriples

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.N3

namespace Harness.N3Run

/-- An RDF graph as an N3 graph. -/
def ofRdf (g : Graph) : N3Graph := g.map ofRdfTriple

def isoOutcome (label : String) : IsoOutcome → Outcome
  | .equal => .pass
  | .notEqual => .fail label
  | .budgetExceeded => .fail s!"comparison undecided, symmetric blank nodes ({label})"

/-- The base for a manifest without `mf:assumedTestBase` (module header). -/
def defaultBase (manifestPath : String) : String :=
  if (manifestPath.splitOn "TurtleTests").length > 1 then "https://w3c.github.io/N3/tests/TurtleTests/"
  else "https://w3c.github.io/N3/tests/N3Tests/"

/-- The Turtle reader and the N3 reader on one text: agree or not. -/
def turtleAgreement (text base : String) (mode : Mode) : Option String :=
  match parseTurtle text (some base) mode, parseN3ToRdf text (some base) mode with
  | .error _, .error _ => none
  | .ok _, .error e => some s!"Turtle reads it, N3 refuses: {e}"
  -- N3 is a superset of Turtle: a text Turtle refuses may be N3.
  | .error _, .ok _ => none
  | .ok g, .ok h =>
      match Graph.isomorphicOutcome g h with
      | .equal => none
      | .notEqual => some "the two graphs are not isomorphic"
      | .budgetExceeded => some "isomorphism budget exceeded"

/-- Turtle negative syntax tests whose text is an N3 document: the Turtle
grammar refuses them, the N3 grammar (Notation3 Language § "Grammar",
production numbers of `reports/20230703/n3.ebnf`) admits them, so the N3
reader must read them. Each entry names the production. A refusal of one of
them is a failure of this run. -/
def n3ValidTurtleNegative : List (String × String) :=
  [ ("turtle-syntax-bad-struct-02", "[12] verb '='"),
    ("turtle-syntax-bad-struct-04", "[13] subject: a literal is a pathItem [18]"),
    ("turtle-syntax-bad-struct-05", "[14] predicate: a literal is a pathItem [18]"),
    ("turtle-syntax-bad-struct-06", "[14] predicate: a blank node is a pathItem [18]"),
    ("turtle-syntax-bad-struct-07", "[14] predicate: a blank node is a pathItem [18]"),
    ("turtle-syntax-bad-struct-14", "[13] subject: a literal is a pathItem [18]"),
    ("turtle-syntax-bad-struct-15", "[14] predicate: a literal is a pathItem [18]"),
    ("turtle-syntax-bad-struct-16", "[14] predicate: a blank node is a pathItem [18]"),
    ("turtle-syntax-bad-struct-17", "[14] predicate: a blank node is a pathItem [18]"),
    ("turtle-syntax-bad-kw-04", "[13] subject: the literal true [19], [31]"),
    ("turtle-syntax-bad-kw-05", "[14] predicate: the literal true [19], [31]"),
    ("turtle-syntax-bad-n3-extras-01", "[23] formula"),
    ("turtle-syntax-bad-n3-extras-02", "[12] verb '='"),
    ("turtle-syntax-bad-n3-extras-03", "[9] triples ::= subject predicateObjectList? (three statements)"),
    ("turtle-syntax-bad-n3-extras-04", "[17] path '^'"),
    ("turtle-syntax-bad-n3-extras-05", "[12] verb 'is' expression 'of'"),
    ("turtle-syntax-bad-n3-extras-06", "[9] a subject alone; ':a.:b.:c' is one PNAME_LN"),
    ("turtle-syntax-bad-n3-extras-09", "[12] verb '=>'"),
    ("turtle-syntax-bad-n3-extras-10", "[12] verb '<='"),
    ("turtle-syntax-bad-prefix-01", "the empty prefix is bound to <#> (decision 2 of docs/designissues/2026-10-28-n3.md)"),
    ("turtle-syntax-bad-prefix-02", "the empty prefix is bound to <#> (decision 2 of docs/designissues/2026-10-28-n3.md)"),
    -- RDF 1.2 Turtle syntax suite, read in RDF 1.2 mode (decision 3).
    ("Turtle 1.2 - bad - reified triple as predicate", "[14] predicate: a reified triple is a pathItem in RDF 1.2 mode"),
    ("N-Triples 1.2 as Turtle 1.2 - Bad - triple term as predicate", "[14] predicate: a triple term is a pathItem in RDF 1.2 mode"),
    ("N-Triples 1.2 as Turtle 1.2 - Bad - triple term as subject", "[13] subject: a triple term is a pathItem in RDF 1.2 mode"),
    ("N-Triples 1.2 as Turtle 1.2 - Bad - reified triple as predicate", "[14] predicate: a reified triple is a pathItem in RDF 1.2 mode") ]

/-- Tests whose upstream data is defective (skill test-suites, "Defective test
data"): reported apart, after the total, with the issue that gives the
evidence. A pass of one of them fails the run, so the exclusion cannot outlive
a corrected test. -/
def defective : List (String × String × String) :=
  [ ("N3Tests/manifest-parser.ttl", "numbers.n3", "https://github.com/danbri/factoidal/issues/1170") ] ++
  (["includes-conclusion-simple.n3", "includes-conclusion.n3", "includes-t10.n3",
    "unify-unify1.n3", "rounded.n3", "log-parsedAsN3.n3"].map fun n =>
    ("N3Tests/manifest-reasoner.ttl", n, "https://github.com/danbri/factoidal/issues/1174"))

/-- Expected failures (skill test-suites, "Expected failures"): an engine
shortfall with an open issue. A FAIL is counted as `expected-fail`; a PASS
fails the run, so the entry is removed in the fixing commit. -/
def expectedFail : List (String × String × String) :=
  ["exponentiation.n3", "math-trig.n3", "string-concatenation.n3", "string-format.n3",
   "string-scrape.n3", "string-roughly.n3", "string-uriEncode.n3", "time-t1.n3",
   "supports-simple.n3", "includes-t11.n3", "log-content.n3", "includes-xsd.n3"].map fun n =>
    ("N3Tests/manifest-reasoner.ttl", n, "https://github.com/danbri/factoidal/issues/1175")

def expectedFail? (manifestPath name : String) : Option String :=
  (expectedFail.find? fun (m, n, _) => manifestPath.endsWith m && n == name).map (·.2.2)

def defective? (manifestPath name : String) : Option String :=
  (defective.find? fun (m, n, _) => manifestPath.endsWith m && n == name).map (·.2.2)

/-- Read an expected-result file: with the N3 reader, except an `.nq`
result, which is read with the N-Quads reader and must have a default graph
only. The suite's `.nt` results are not all N-Triples: some indent their
lines, some have a blank node as predicate or a literal as subject
(generalized RDF, as cwm wrote it); N3 reads all of them. -/
def readExpected (path text base : String) (mode : Mode) : Except String N3Graph :=
  if path.endsWith ".nq" then
    match parseNQuads text mode with
    | .error e => .error s!"result N-Quads: {e.msg} (offset {e.pos})"
    | .ok ds =>
        if !ds.named.isEmpty then .error "result has named graphs"
        else .ok (ofRdf ds.default)
  else
    match parseN3 text (some base) mode with
    | .error e => .error s!"result: {e.msg} (offset {e.pos})"
    | .ok d => .ok d.triples

/-- Compare a document with an expected result. An `.n3` result is compared
as an N3 graph. An `.nt` or `.nq` result writes lists as collections, so the
document's lists are expanded first (`expandLists`). -/
def compareExpected (rf : String) (d : N3Document) (exp : N3Graph) : Outcome :=
  let why (g : N3Graph) : String :=
    let a := graphKeys g {}
    let b := graphKeys exp {}
    let missing := (b.filter fun k => !a.contains k).take 2
    let extra := (a.filter fun k => !b.contains k).take 2
    s!"not isomorphic to the result ({g.length} triples, expected {exp.length}; " ++
      s!"missing {missing}; extra {extra})"
  if rf.endsWith ".n3" then isoOutcome (why d.triples) (n3Isomorphic d.triples exp)
  else
    match expandLists (d.bnodePrefix ++ "c") d.triples with
    | .error e => .fail e
    | .ok g => isoOutcome (why g) (n3Isomorphic g exp)

def testNs : String := "https://w3c.github.io/N3/tests/test.n3#"

/-- The `test:options` of a reasoning test (`tests/test.n3` of the suite):
`test:think` rounds to a fixpoint, `test:rules` one round, `test:conclusions`
outputs the concluded triples only, `test:data` keeps plain triples only. -/
def optionsOf (g : Graph) (entry : String) : ReasonOptions :=
  match g.find? (fun t => subjKey t.s == entry && t.p.val == testNs ++ "options") with
  | none => {}
  | some t =>
      let node := termKey t.o
      let on (n : String) : Bool :=
        g.any fun u => subjKey u.s == node && u.p.val == testNs ++ n && termKey u.o == "true"
      let conclusions := g.any fun u => subjKey u.s == node && u.p.val == testNs ++ "conclusions"
      { think := on "think" || !on "rules", conclusions, data := on "data" }

/-- One test: its outcome, and for a Turtle type the agreement note. -/
def runOne (mode : Mode) (base : String) (manifestDir : String) (mg : Graph) (tc : TestCase) :
    IO (Outcome × Option (Option String)) := do
  let some path := tc.action | return (.skip "no mf:action", none)
  let some text ← readOpt path | return (.skip s!"file missing: {path}", none)
  let b := base ++ relpathUnder manifestDir path
  let turtleType := tc.testType.startsWith "TestTurtle"
  let agree := if turtleType then some (turtleAgreement text b mode) else none
  let out : Outcome ←
    match tc.testType with
    | "TestN3PositiveSyntax" | "TestTurtlePositiveSyntax" =>
        match parseN3 text (some b) mode with
        | .error e => pure (.fail s!"refused: {e.msg} (offset {e.pos})")
        | .ok d =>
            let written := writeN3 (prefixTableOf d.prefixes) d.triples
            match parseN3 written (some b) mode with
            | .error e => pure (.fail s!"writer output refused: {e.msg} (offset {e.pos})")
            | .ok d2 =>
                pure (if relabel d.triples == relabel d2.triples then .pass
                      else .fail "writer round trip: the graph read back differs")
    | "TestTurtleNegativeSyntax" =>
        match n3ValidTurtleNegative.lookup tc.name, parseN3 text (some b) mode with
        | some _, .ok _ => pure .pass
        | some why, .error e => pure (.fail s!"refused, but N3 admits it by {why}: {e.msg} (offset {e.pos})")
        | none, .error _ => pure .pass
        | none, .ok _ => pure (.fail "read a document that must be refused")
    | "TestN3NegativeSyntax" | "TestTurtleNegativeEval" =>
        match parseN3 text (some b) mode with
        | .error _ => pure .pass
        | .ok _ => pure (.fail "read a document that must be refused")
    | "TestN3Eval" =>
        let some rf := tc.resultFile | pure (.skip "no mf:result")
        let some rtext ← readOpt rf | pure (.skip s!"file missing: {rf}")
        match parseN3 text (some b) mode, readExpected rf rtext b mode with
        | .error e, _ => pure (.fail s!"refused: {e.msg} (offset {e.pos})")
        | _, .error e => pure (.fail e)
        | .ok d, .ok exp => pure (compareExpected rf d exp)
    | "TestTurtleEval" =>
        let some rf := tc.resultFile | pure (.skip "no mf:result")
        let some rtext ← readOpt rf | pure (.skip s!"file missing: {rf}")
        match parseN3ToRdf text (some b) mode, parseNTriples rtext mode with
        | .error e, _ => pure (.fail s!"refused or not RDF: {e}")
        | _, .error e => pure (.fail s!"result N-Triples: {e.msg} (offset {e.pos})")
        | .ok g, .ok exp =>
            pure (match Graph.isomorphicOutcome g exp with
              | .equal => .pass
              | .notEqual => .fail s!"not isomorphic to the result (got {g.length} triples, expected {exp.length})"
              | .budgetExceeded => .fail "isomorphism budget exceeded")
    | "TestN3Reason" =>
        let some rf := tc.resultFile | pure (.skip "no mf:result")
        let some rtext ← readOpt rf | pure (.skip s!"file missing: {rf}")
        match parseN3 text (some b) mode, readExpected rf rtext b mode with
        | .error e, _ => pure (.fail s!"refused: {e.msg} (offset {e.pos})")
        | _, .error e => pure (.fail e)
        | .ok d, .ok exp =>
            let (out, limit) := reason (optionsOf mg tc.entryId) d.triples
            if limit then pure (.fail "a reasoning bound stopped the run")
            else pure (compareExpected rf { d with triples := out } exp)
    | t => pure (.unsupported s!"test type {t}")
  return (out, agree)

structure Tally where
  current  : Score := {}
  rejected : Score := {}
  agree    : Score := {}
  excluded : Nat := 0

def runManifest (mode : Mode) (quiet : Bool) (path : String) : IO (Option Tally) := do
  match ← loadManifest path with
  | none =>
      IO.println s!"NO MANIFEST {path}"
      return none
  | some (.error e) =>
      IO.println s!"MANIFEST ERROR {path}: {e}"
      return none
  | some (.ok (tcs, assumed)) =>
      let abs ← IO.FS.realPath path
      let dir := dirname abs.toString
      let base := assumed.getD (defaultBase abs.toString)
      let mg : Graph :=
        match parseTurtle ((← readOpt path).getD "") (some ("file://" ++ abs.toString)) with
        | .ok g => g
        | .error _ => []
      let mut t : Tally := {}
      for tc in tcs do
        let (o0, ag) ← runOne mode base dir mg tc
        let rej := tc.approval == "Rejected"
        match defective? abs.toString tc.name, o0 with
        | some url, .fail _ =>
            t := { t with excluded := t.excluded + 1 }
            IO.println s!"EXCLUDED {tc.name}: defective test data, {url}"
        | none, .fail why =>
            match expectedFail? abs.toString tc.name with
            | some url =>
                t := { t with current := { t.current with xfail := t.current.xfail + 1 } }
                if !quiet then IO.println s!"XFAIL {tc.name}: {url} ({why})"
            | none =>
                if rej then t := { t with rejected := t.rejected.bump o0 }
                else t := { t with current := t.current.bump o0 }
                if !quiet || !rej then
                  IO.println ((if rej then "[rejected] " else "") ++ o0.line tc.name)
        | d, _ =>
            let o : Outcome := match d, o0, expectedFail? abs.toString tc.name with
              | none, .pass, some url => .fail s!"unexpected pass: remove the expected failure and update {url}"
              | some url, .pass, _ => .fail s!"unexpected pass: remove the defective-data exclusion and close {url}"
              | _, _, _ => o0
            if rej then t := { t with rejected := t.rejected.bump o }
            else t := { t with current := t.current.bump o }
            if !quiet || (o.isFail && !rej) then
              IO.println ((if rej then "[rejected] " else "") ++ o.line tc.name)
        (← IO.getStdout).flush
        match ag with
        | some none => t := { t with agree := t.agree.bump .pass }
        | some (some why) =>
            t := { t with agree := t.agree.bump (.fail why) }
            IO.println s!"DISAGREE {tc.name}: {why}"
        | none => pure ()
      let suite := lastAfter dir "/" ++ "/" ++ lastAfter abs.toString "/"
      IO.println (Score.line suite t.current ++
        (if t.excluded == 0 then "" else s!"; {t.excluded} excluded (defective test data)"))
      if t.rejected.total > 0 then IO.println (Score.line (suite ++ " (rdft:Rejected)") t.rejected)
      if t.agree.total > 0 then IO.println (Score.line (suite ++ " turtle-agreement") t.agree)
      return some t

def main (args : List String) : IO UInt32 := do
  let mode := if args.contains "--rdf12" then Mode.rdf12 else Mode.rdf11
  let quiet := args.contains "--quiet"
  let paths := args.filter (fun a => !a.startsWith "--")
  if paths.isEmpty then
    IO.eprintln "usage: lake exe l4n3 [--rdf12] [--quiet] <manifest.ttl>..."
    return 2
  let mut bad := false
  for p in paths do
    match ← runManifest mode quiet p with
    | none => bad := true
    | some t => if t.current.fail > 0 || t.agree.fail > 0 then bad := true
  return (if bad then 1 else 0)

end Harness.N3Run

def main (args : List String) : IO UInt32 := Harness.N3Run.main args
