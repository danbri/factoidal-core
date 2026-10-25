/-
Harness/RifRun — the RIF Core test suite, run end to end.

`third_party/testing/rif-core-suite/Core_v1.22/Approved` holds five
kinds of case, one directory each:

  * `PositiveSyntaxTest` / `NegativeSyntaxTest` — does the document
    parse?
  * `PositiveEntailmentTest` / `NegativeEntailmentTest` — does the
    premise entail the conclusion?
  * `ImportRejectionTest` — must the document be REJECTED for what it
    imports? Not attempted: this port has no import profile checker,
    and it says so rather than scoring them.

## Three outcomes on the entailment tests

  * **pass / fail** — the verdict matched, or it did not;
  * **undecided** — a built-in outside `RIF/Builtins.lean` blocked a
    rule, or the forward chain hit its round bound. Counted apart,
    because a closure missing a rule is not the closure and reading
    "does not entail" off it would be a guess. RIF-DTB defines 197
    built-ins; naming which are decided is what keeps this honest.

## Imports under the OWL Direct profile

When every `Import` names `…/entailment/OWL-Direct`, the imported graph
is read as an OWL 2 DL ontology and the verdict is
`L4Factoidal.RIF.OwlDirect.entailsOwlDirect`'s (RIF-RDF-OWL §4.2.2,
decided through the §9.2 embedding). The graph's triples are NOT facts
under that profile: a declaration or an annotation has no
Direct-Semantics content. An import published only as RDF/XML
(`Modeling_Brain_Anatomy`) is read with `Syntax.RdfXml`.

## The conclusion's prefixes

A conclusion file is a BARE FORMULA with no prologue —
`ex:myOnto[ex:hasTitle -> "Example ontology"]`. Its prefixes come
from the premise beside it, and where the premise only IMPORTS an RDF
graph, from that graph's own `@prefix` lines. That is the suite's
convention rather than a RIF rule, and it is applied here because the
alternative is calling a well-formed conclusion unparsable.

Usage: `lake exe l4rif [suite-dir]`
-/
import L4Factoidal.RIF.Engine
import L4Factoidal.RIF.Conformance
import L4Factoidal.RIF.OwlDirect
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.XML.Parser
import L4Factoidal.RIF.Ps
import L4Factoidal.Syntax.Turtle
import L4Factoidal.RDFS.Closure
import Harness.Fixtures
import Harness.RifImport
import L4Factoidal.RIF.RdfMapping

open L4Factoidal.RIF
open L4Factoidal.RIF.RdfMapping
open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.XML (parseXML)

/-- The last `/`-separated segment of an import location. The corpus
publishes every import under a W3C URL whose last segment is the local
file's stem, so `.../RDF_Combination_Invalid_Profiles_1-import001`
resolves against `RDF_Combination_Invalid_Profiles_1-import001.ttl` or
`…-import001.rif` beside the case. -/
def lastSegment (url : String) : String :=
  match (url.splitOn "/").reverse with
  | seg :: _ => seg
  | []       => url

/-- The local file STEM an import location names. Some locations carry
the extension (`…-import001.rif`) and some do not (`…-import001`), so
a known extension is stripped and the candidate names are rebuilt from
the stem. -/
def importStem (url : String) : String :=
  let seg := lastSegment url
  let chop := fun (x : String) => String.ofList (x.toList.take (x.length - 4))
  if seg.endsWith ".rif" || seg.endsWith ".ttl" || seg.endsWith ".rdf" then chop seg
  else seg

/-- Load a document's imports closure: RIF-XML imports as XML trees,
RDF imports as graphs. Reading files is the runner's job; the verdict
is `L4Factoidal.RIF.Conformance.importRejectionReason`'s. -/
def loadImportClosure (cdir : String) (files : List String) (root : L4Factoidal.XML.Node)
    : IO L4Factoidal.RIF.Conformance.ImportClosure := do
  let mut rifRoots : List L4Factoidal.XML.Node := []
  let mut graphs : List (List Triple) := []
  for site in L4Factoidal.RIF.Conformance.documentImports root do
    match site.location with
    | none     => pure ()
    | some loc =>
      let stem := importStem loc
      for f in files do
        if f == stem ++ ".rif" then
          let src ← IO.FS.readFile (cdir ++ "/" ++ f)
          match parseXML src with
          | .ok d    => rifRoots := rifRoots ++ [d.root]
          | .error _ => pure ()
        else if f == stem ++ ".ttl" then
          let src ← IO.FS.readFile (cdir ++ "/" ++ f)
          match parseTurtle src none with
          | .ok g    => graphs := graphs ++ [g]
          | .error _ => graphs := graphs ++ [[]]
  return { root := root, importedRifRoots := rifRoots, importedGraphs := graphs }

/-- A conclusion companion, in either of the two names the corpus uses.
Excluded from the imported graphs: it is what must be PROVED. -/
def isConclusionFile (f : String) : Bool :=
  f.endsWith "-conclusion.ttl" || f.endsWith "-nonconclusion.ttl"

/-- A conclusion that is an RDF GRAPH rather than a RIF condition. One
Approved case has this shape: no `-conclusion.rifps` was ever published
for it, and the vendored `-conclusion.ttl` beside it carries the
conclusion (see the PROVENANCE.md in that directory). Every triple
becomes a frame atom and the conjunction is the goal, which is the
same reading `RIF.Core.Translation.graph_to_bgp` gives it in the F*
tree. -/
def tmOfGround : GTerm → Tm
  | .const l sp   => .const l sp
  | .list xs      => .list (xs.map tmOfGround)
  | .fapp f sp xs => .fapp f sp (xs.map tmOfGround)

def goalOfGraph (g : List Triple) : Option Formula :=
  match g.filterMap (fun t =>
          match gOfTerm t.o with
          | none   => none
          | some o =>
            some (Formula.atom (.frame (tmOfGround (gOfSubject t.s))
                                       (tmOfGround (gIri t.p.val))
                                       (tmOfGround o)))) with
  | []  => none
  | fs  => some (.and fs)

/-! ## Local overrides

`tests/local-overrides/rif/<TestName>.override` records a documented
disagreement with a DEFECTIVE fixture (see
`tests/local-overrides/README.md`). It is a disposition, not a semantic
change: the engine still runs and still reports its real answer, and
the override only moves one named divergence out of the fail bucket
into a distinctly-counted one. Reading it here is consumer-tool
bookkeeping, which is why it lives in the runner and not in
`L4Factoidal/RIF/`.

An override never masks a success: a test that passes on its own is
reported PASS and its override is flagged stale. -/

/-- The header value for a key, from an `.override` file's `key: value`
block above the `---` line. -/
def overrideHeader (src : String) (key : String) : Option String :=
  let headerLines := (src.splitOn "\n").takeWhile (fun l => l.trimAscii.toString != "---")
  headerLines.findSome? (fun line =>
    if line.startsWith (key ++ ":") then
      some ((String.ofList (line.toList.drop (key.length + 1))).trimAscii.toString)
    else none)

/-- The test names dispositioned `local-override` for the rif suite. -/
def loadOverrides (dir : String) : IO (List String) := do
  if !(← System.FilePath.isDir dir) then return []
  let mut names : List String := []
  for e in ← System.FilePath.readDir dir do
    if e.fileName.endsWith ".override" then
      let src ← IO.FS.readFile e.path
      if (overrideHeader src "disposition") == some "local-override" then
        match overrideHeader src "test" with
        | some n => names := names ++ [n]
        | none   => pure ()
  return names

structure Tally where
  pass      : Nat := 0
  fail      : Nat := 0
  undecided : Nat := 0
  notRead   : Nat := 0
  skipped   : Nat := 0
  overridden : Nat := 0
  staleOverrides : List String := []
  excluded  : Nat := 0
  staleExclusions : List String := []
deriving Inhabited

/-- W3C cases whose test data is defective, each with the open issue that
records the evidence (skill test-suites, "Defective test data"; owner,
2026-10-21: "Dont list bad tests as our failing"; owner, 2026-10-25, on
https://github.com/danbri/factoidal/issues/1031: "1 yes excude bad
issues, create cleaned up. Project-local unit tests to feplace them").
They are reported as `excluded (defective test data)`, outside pass, fail,
undecided and the total. One that passes fails the run. The corrected
copies are in `tests/rif-local/` and run as the `rif-local` line.

* `EBusiness_Contract`: the rule guards with `pred:is-literal-dateTime`
  and `func:subtract-dateTimes`, and the facts are `xs:date` literals.
  The value spaces of `xs:date` and `xs:dateTime` are disjoint (XSD 1.1
  Part 2 §3.3.9 and §3.3.7), so the guard is false and the conclusion is
  not entailed.
* `Builtins_Time`: premise line 65 compares with
  `"2000-11-02T12:27:00"^^xs:dayTime`. XSD has no datatype `dayTime`;
  `func:add-dayTimeDuration-to-dateTime` returns `xs:dateTime`.
* `Builtins_PlainLiteral`: premise line 18 compares with `"en"^^xs:lang`.
  XSD has no datatype `lang`. -/
def defectiveData : List (String × String) :=
  [("EBusiness_Contract",    "https://github.com/danbri/factoidal/issues/1031"),
   ("Builtins_Time",         "https://github.com/danbri/factoidal/issues/1031"),
   ("Builtins_PlainLiteral", "https://github.com/danbri/factoidal/issues/1031")]

def rounds : Nat := 24

/-- Run every case under `dir` (one subdirectory per test kind, one per
case). Used for the W3C corpus and for the project-local corrected copies
in `tests/rif-local/`. -/
def runSuite (dir : String) (verbose : Bool) (overrides : List String)
    (defective : List (String × String)) : IO Tally := do
  let mut t : Tally := {}
  for kindEntry in (← System.FilePath.readDir dir) do
    if ← System.FilePath.isDir kindEntry.path then
      let kind := kindEntry.fileName
      for caseEntry in (← System.FilePath.readDir kindEntry.path) do
        if ← System.FilePath.isDir caseEntry.path then
          let name := caseEntry.fileName
          let cdir := caseEntry.path.toString
          let files := (← System.FilePath.readDir cdir).toList.map (·.fileName)
          let readOne := fun (suffix : String) => do
            match files.find? (·.endsWith suffix) with
            | none   => pure none
            | some f => (IO.FS.readFile (cdir ++ "/" ++ f)).map some
          if kind == "ImportRejectionTest" then
            -- The import combination must be REJECTED. The verdict is
            -- the library's disjunction of the RIF-RDF/OWL Combination
            -- import-validity conditions; the runner only resolves the
            -- imported files off disk.
            match ← readOne "-input.rif" with
            | none => t := { t with notRead := t.notRead + 1 }
            | some raw =>
              match parseXML raw with
              | .error _ =>
                  t := { t with notRead := t.notRead + 1 }
                  IO.println s!"NOT READ {kind}/{name}: input.rif did not parse as XML"
              | .ok d =>
                let closure ← loadImportClosure cdir files d.root
                match L4Factoidal.RIF.Conformance.importRejectionReason closure with
                | some why =>
                    t := { t with pass := t.pass + 1 }
                    if verbose then IO.println s!"PASS {kind}/{name}: {why}"
                | none =>
                    t := { t with fail := t.fail + 1 }
                    IO.println s!"FAIL {kind}/{name}: this import combination must be rejected, and the checked conditions found no violation"
          else if kind == "PositiveSyntaxTest" || kind == "NegativeSyntaxTest" then
            match ← readOne "-input.rifps" with
            | none => t := { t with notRead := t.notRead + 1 }
            | some src =>
                -- SAFENESS is part of being a RIF Core document, and
                -- a parser cannot see it: `Core_NonSafeness` parses
                -- and is still not RIF Core.
                let parsed := match parseDocument src with
                  | .error _ => false
                  | .ok d    => documentSafe d.rules
                let want := kind == "PositiveSyntaxTest"
                if parsed == want then t := { t with pass := t.pass + 1 }
                else
                  t := { t with fail := t.fail + 1 }
                  IO.println s!"FAIL {kind}/{name}: parsed = {parsed}, expected {want}"
          else
            match ← readOne "-premise.rifps" with
            | none => t := { t with notRead := t.notRead + 1 }
            | some psrc =>
              let csrc? ← (do
                match ← readOne "-conclusion.rifps" with
                | some c => pure (some c)
                | none   => readOne "-nonconclusion.rifps")
              -- A conclusion published only as an RDF graph.
              let cgraph? ← (do
                match files.find? (fun f => f.endsWith "-conclusion.ttl") with
                | none   => pure none
                | some f => (IO.FS.readFile (cdir ++ "/" ++ f)).map some)
              if csrc?.isNone && cgraph?.isNone then
                t := { t with notRead := t.notRead + 1 }
              else
                match parseDocument psrc with
                | .error e =>
                    t := { t with notRead := t.notRead + 1 }
                    IO.println s!"NOT READ {kind}/{name}: premise — {e.msg}"
                | .ok doc =>
                    -- Only declared import documents supply facts; unrelated
                    -- sibling fixtures (including conclusions) are never premises.
                    let mut imported : Graph := []
                    let mut extraPrefixes : List (String × String) := []
                    let mut importErrors : List String := []
                    for (url, _) in doc.imports do
                      match ← Harness.RifImport.load cdir url with
                      | .ok loaded =>
                          imported := imported ++ loaded.graph
                          extraPrefixes := extraPrefixes ++ loaded.prefixes
                      | .error why => importErrors := importErrors ++ [why]
                    if !importErrors.isEmpty then
                      t := { t with notRead := t.notRead + 1 }
                      IO.println s!"NOT READ {kind}/{name}: {String.intercalate "; " importErrors}"
                    else
                      let ctx : Ctx :=
                        { base := doc.base, prefixes := doc.prefixes ++ extraPrefixes }
                      -- The conclusion, from the RIF condition when the
                      -- corpus published one and from the vendored RDF
                      -- graph when it did not.
                      let goal? : Except String Formula :=
                        match csrc? with
                        | some csrc =>
                            match parseFormulaText ctx csrc with
                            | .error e => .error e.msg
                            | .ok f    => .ok f
                        | none =>
                            match cgraph? with
                            | none => .error "no conclusion"
                            | some gsrc =>
                              match parseTurtle gsrc none with
                              | .error e => .error s!"conclusion graph — {e}"
                              | .ok cg =>
                                match goalOfGraph cg with
                                | none   => .error "the conclusion graph has no usable triple"
                                | some f => .ok f
                      match goal? with
                      | .error e =>
                          t := { t with notRead := t.notRead + 1 }
                          IO.println s!"NOT READ {kind}/{name}: conclusion — {e}"
                      | .ok goal =>
                          -- An IMPORT names an entailment regime. An
                          -- `Import` naming RDFS means the imported
                          -- graph is RDFS-CLOSED before it becomes facts.
                          -- OWL-Direct is NOT a closure of the graph: the
                          -- graph is read as an OWL 2 DL ontology and its
                          -- axioms become rules (RIF-RDF-OWL §9.2), which
                          -- `L4Factoidal.RIF.OwlDirect` does. Reading the
                          -- graph as plain RDF triples made
                          -- `Non-Annotation_Entailment` entail a triple
                          -- that OWL puts inside an annotation.
                          -- OWL-RDF-Based is not implemented and stays
                          -- UNDECIDED.
                          let profiles := doc.imports.filterMap (·.2)
                          -- OWL-Direct is decided by
                          -- `RIF.OwlDirect.entailsOwlDirect` when EVERY
                          -- import names it. Mixed with Simple, RDF or
                          -- RDFS there is no single highest profile and
                          -- RIF-RDF-OWL §5.2 rejects the document; mixed
                          -- with OWL-RDF-Based the highest is a profile
                          -- this port does not implement.
                          let owlDirectOnly := !profiles.isEmpty &&
                            profiles.all (· == L4Factoidal.RIF.Conformance.owlDirectProfile)
                          let unsupportedRegime := !owlDirectOnly && profiles.any (fun p =>
                            (p.splitOn "OWL").length > 1 || (p.splitOn "entailment/RIF").length > 1)
                          let wantsRdfs := profiles.any (fun p =>
                            (p.splitOn "RDFS").length > 1)
                          let g := if wantsRdfs && !imported.isEmpty
                                   then L4Factoidal.RDFS.closureFix imported
                                   else imported
                          let facts := g.flatMap factsOfTriple
                          let want := kind == "PositiveEntailmentTest"
                          -- Local constants are DOCUMENT-scoped, so
                          -- the premise's `_p` and the conclusion's are
                          -- different symbols.
                          let rules := doc.rules.map (qualifyRule "premise")
                          let goal := qualifyFormula "conclusion" goal
                          -- An OWL-Direct combination that violates the
                          -- individual/data-value VOCABULARY SEPARATION
                          -- is INCONSISTENT and entails everything. That
                          -- verdict is part of `entailsOwlDirect`
                          -- (ROWL-Direct rows (ii)-(vii), RIF-RDF-OWL
                          -- §9.2.2.2). The narrower
                          -- `Conformance.owlDirectSeparationInconsistent`
                          -- used to be called here for EVERY profile,
                          -- which would have made a Simple import
                          -- inconsistent for a fact a Simple combination
                          -- allows.
                          let verdict : Verdict :=
                            (if unsupportedRegime
                                   then Verdict.undecided
                                     "the case imports under an entailment regime this port does not implement"
                                   else if owlDirectOnly
                                   then L4Factoidal.RIF.OwlDirect.entailsOwlDirect rules imported goal rounds
                                   else if !graphMappingSupported g then Verdict.undecided
                                     "RDF input cannot be represented in RIF (direction or triple term)"
                                   else entails rules facts goal rounds)
                          let ok := match verdict with
                            | .holds => want
                            | .doesNotHold => !want
                            | .undecided _ => false
                          -- Defective W3C test data (skill test-suites, "Defective test
                          -- data"): reported apart, never in pass, fail or the total. A pass
                          -- fails the run, so the exclusion cannot outlive a corrected test.
                          if let some (_, url) := defective.find? (·.1 == name) then
                            if ok then
                              t := { t with staleExclusions := t.staleExclusions ++ [name] }
                              IO.println s!"FAIL {kind}/{name}: unexpected pass: the defective-test-data exclusion is stale; remove it from defectiveData and close {url}"
                            else
                              t := { t with excluded := t.excluded + 1 }
                              IO.println s!"EXCLUDED {name}: defective test data, {url}"
                          else
                            match verdict with
                            | .holds =>
                                if want then
                                  t := { t with pass := t.pass + 1 }
                                  if overrides.contains name then
                                    t := { t with staleOverrides := t.staleOverrides ++ [name] }
                                else if overrides.contains name then
                                  t := { t with overridden := t.overridden + 1 }
                                  IO.println s!"OVERRIDE {kind}/{name}: entailed, and the fixture says it must not be"
                                else
                                  t := { t with fail := t.fail + 1 }
                                  IO.println s!"FAIL {kind}/{name}: entailed, and must not be"
                            | .doesNotHold =>
                                if !want then
                                  t := { t with pass := t.pass + 1 }
                                  if overrides.contains name then
                                    t := { t with staleOverrides := t.staleOverrides ++ [name] }
                                else if overrides.contains name then
                                  t := { t with overridden := t.overridden + 1 }
                                  IO.println s!"OVERRIDE {kind}/{name}: not entailed, and the fixture says it must be"
                                else
                                  t := { t with fail := t.fail + 1 }
                                  IO.println s!"FAIL {kind}/{name}: not entailed, and must be"
                            | .undecided why =>
                                t := { t with undecided := t.undecided + 1 }
                                -- Name the built-ins the case USES. They
                                -- are candidates, not the measured cause:
                                -- the engine threads a Bool, so it cannot
                                -- say which one blocked.
                                let used := externalIrisUsed rules goal
                                let usedStr :=
                                  if used.isEmpty then ""
                                  else if verbose then
                                    " — built-ins used: " ++ String.intercalate ", " used
                                  else s!" — {used.length} built-ins used, --verbose names them"
                                IO.println s!"UNDECIDED {kind}/{name}: {why}{usedStr}"
  return t

def main (args : List String) : IO UInt32 := do
  let dir ← Harness.fixtureArgOr ((args.filter (fun a => !a.startsWith "--")).head?)
    "third_party/testing/rif-core-suite/Core_v1.22/Approved"
  let verbose := args.contains "--verbose"
  let overrideDir ← Harness.resolveFixtureOr "tests/local-overrides/rif"
  let overrides ← loadOverrides overrideDir
  if !(← System.FilePath.isDir dir) then
    IO.println s!"rif runner: corpus not found: {dir}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let t ← runSuite dir verbose overrides defectiveData
  let decided := t.pass + t.fail
  -- The project-local corrected copies of the excluded cases
  -- (https://github.com/danbri/factoidal/issues/1031). Exclusions do not
  -- apply here: these must pass.
  let localDir ← Harness.resolveFixtureOr "tests/rif-local"
  let localTally ← if ← System.FilePath.isDir localDir
    then runSuite localDir verbose [] [] else pure {}
  let localTotal := localTally.pass + localTally.fail + localTally.undecided + localTally.notRead
  IO.println ""
  IO.println (s!"rif-core DECIDED: {t.pass} pass, {t.fail + t.staleExclusions.length} fail " ++
    s!"(out of {decided + t.staleExclusions.length} decided); " ++
    s!"{t.excluded} excluded (defective test data)")
  IO.println s!"UNDECIDED: {t.undecided} cases — a built-in outside this port's slice"
  IO.println s!"  blocked a rule, the chain reached its round bound, or an import's"
  IO.println s!"  regime or ontology is outside what this port decides"
  IO.println s!"NOT READ: {t.notRead} cases"
  -- Printed also when zero: `tools/lean-scoreboard.sh` reads the count.
  IO.println s!"LOCAL OVERRIDE: {t.overridden} cases — a documented disagreement with a"
  IO.println s!"  DEFECTIVE fixture, read from {overrideDir}. The engine still ran and"
  IO.println "  its observed verdict is printed on the OVERRIDE line above."
  for stale in t.staleOverrides do
    IO.println s!"STALE OVERRIDE {stale}: this test now passes on its own — remove its .override file"
  if t.skipped > 0 then
    IO.println s!"IMPORT REJECTION: {t.skipped} cases, not attempted"
  IO.println ""
  IO.println "An UNDECIDED case is counted apart, never as a pass and never as a"
  IO.println "failure: a closure computed without a rule is not the closure, and"
  IO.println "reading `does not entail` off it would be a guess."
  let inventory := t.pass + t.fail + t.undecided + t.notRead + t.skipped + t.overridden + t.excluded
  if inventory == 0 then
    IO.eprintln "rif runner: empty inventory; no cases were scored or classified"
  IO.println ""
  IO.println (s!"rif-local: {localTally.pass} pass, {localTally.fail} fail, " ++
    s!"{localTally.undecided} undecided, {localTally.notRead} not read (out of {localTotal}) " ++
    s!"— corrected copies of the excluded W3C cases, {localDir}")
  if localTotal == 0 then
    IO.eprintln s!"rif runner: no project-local cases found under {localDir}"
  let localOk := localTally.pass == localTotal && localTotal > 0
  return if t.fail > 0 || !t.staleOverrides.isEmpty || !t.staleExclusions.isEmpty
            || inventory == 0 || !localOk then 1 else 0
