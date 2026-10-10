/-
Harness/GrddlRun — a GRDDL conformance runner over the vendored W3C
GRDDL test suite.

It parses `third_party/testing/grddl/grddl-tests-normative.rdf` with
this project's own RDF/XML parser, asks `GRDDL.Agent.glean` for the
GRDDL result of each test's input document (all four discovery rules,
namespace and profile documents to a fixpoint, stylesheets through the
Lean XSLT engine), and compares it with the expected graph BY
ISOMORPHISM over SETS of triples — blank-node labels and repeated
triples are not part of what a GRDDL result means.

## No network, and that is visible in the score

The suite's documents live under two URL trees which
`third_party/testing/grddl/docroot/` mirrors; `docroot/redirects.tsv`
records the five redirections the base-URI tests depend on, and
`docroot/variants.tsv` records the one resource the W3C server
negotiates over language (`td/conneg.html`, English and German), which
the language cases `langconneg1` to `langconneg3` read.
`iriToLocal` maps an absolute suite IRI to a file there. A document
inside those trees that is not mirrored makes the case UNAVAILABLE with
the IRI named. Documents outside them (the XHTML, RDF and SVG namespace
documents) are not vendored on purpose (PROVENANCE.md); a failing case
names the ones it did not retrieve.

## Six outcomes

  * **pass** — the result is isomorphic to the expected graph;
  * **fail** — it is not. A failure that differs only by the http/https
    scheme is also counted as vendoring drift (a sub-count, not a
    bucket);
  * **no-transformation** — the agent found no transformation and the
    source is not RDF/XML;
  * **unavailable** — a suite document the case needs is not vendored;
  * **refused** — the XSLT engine declined a stylesheet, an output was
    not RDF/XML, or the isomorphism search exceeded its budget;
  * **related-pass** — not passed, but a test related by `g:alternative`
    or `g:subsumes` passed, which the W3C driver `testft.py` counts as
    passed (GRDDL Test Cases, "Tests with Multiple GRDDL Results").
    Counted apart from pass.

Usage: `lake exe l4grddl [tests-dir]`
-/
import L4Factoidal.GRDDL.Agent
import L4Factoidal.Syntax.NTriples
import L4Factoidal.JSON.Parser

open L4Factoidal.RDF
open L4Factoidal.XML
open L4Factoidal.GRDDL
open L4Factoidal.Syntax

/-! ## Mapping a suite IRI to a vendored file -/

def tdPrefix : String := "http://www.w3.org/2001/sw/grddl-wg/td/"
def tdPrefixHttps : String := "https://www.w3.org/2001/sw/grddl-wg/td/"
def gPrefixHttp : String := "http://www.w3.org/2003/g/"
def gPrefixHttps : String := "https://www.w3.org/2003/g/"

def stripFragment (iri : String) : String :=
  match iri.toList.findIdx? (· == '#') with
  | some i => String.ofList (iri.toList.take i)
  | none   => iri

/-- The two host trees the suite references, and nothing else, under
    either scheme: www.w3.org answers the `http` IRI with a redirection
    to the same path under `https`, so both name one representation. An
    IRI outside them has no local file, which the caller reports as
    UNAVAILABLE with the IRI named. -/
def iriToLocal (docroot : String) (iri0 : String) : Option String :=
  let iri := stripFragment iri0
  let after (p : String) : String := String.ofList (iri.toList.drop p.length)
  if iri.startsWith tdPrefix then some (docroot ++ "/td/" ++ after tdPrefix)
  else if iri.startsWith tdPrefixHttps then some (docroot ++ "/td/" ++ after tdPrefixHttps)
  else if iri.startsWith gPrefixHttp then some (docroot ++ "/g/" ++ after gPrefixHttp)
  else if iri.startsWith gPrefixHttps then some (docroot ++ "/g/" ++ after gPrefixHttps)
  else none

def readIri (docroot iri : String) : IO (Option String) := do
  match iriToLocal docroot iri with
  | none      => return none
  | some path =>
      if ← System.FilePath.pathExists path then
        return some (← IO.FS.readFile path)
      else return none

/-! ## The manifest -/

def tsNS : String := "http://www.w3.org/2000/10/rdf-tests/rdfcore/testSchema#"
def rdfTypeIri : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

structure GTest where
  subject : String
  input   : Option String := none
  output  : Option String := none
  types   : List String := []
deriving Repr, Inhabited

def subjIri : Subject → Option String
  | .iri i   => some i.val
  | .bnode _ => none

def objIri : Term → Option String
  | .iri i => some i.val
  | _      => none

/-- Every `rdfcore:Test` in the manifest, with its input and output
    documents. -/
def testsOf (g : Graph) : List GTest :=
  let subjects := (g.filterMap (fun t =>
    if t.p.val == rdfTypeIri then subjIri t.s else none)).eraseDups
  subjects.filterMap (fun s =>
    let mine := g.filter (fun t => subjIri t.s == some s)
    let get (p : String) : Option String :=
      (mine.find? (fun t => t.p.val == tsNS ++ p)).bind (fun t => objIri t.o)
    let types := mine.filterMap (fun t =>
      if t.p.val == rdfTypeIri then objIri t.o else none)
    if types.contains (tsNS ++ "Test") then
      some { subject := s, input := get "inputDocument",
             output := get "outputDocument", types := types }
    else none)

/-! ## Outcomes -/

/-- Replace every `https://` with `http://`, and every blank-node
    label with one placeholder, in an N-Triples serialisation.

    This is a DIAGNOSIS, never a verdict. Several of the vendored
    inputs were re-fetched from a W3C server that had upgraded its
    own links to `https`, while the expected-output files beside them
    still say `http` — so a transform can be exactly right and still
    produce a different IRI. Saying so on the FAIL line is what tells
    a reader the residue is corpus drift rather than an engine
    defect; the case still counts as a failure, because the two
    graphs really are different graphs. -/
def schemeBlind (s : String) : String :=
  let noScheme := String.intercalate "http://" (s.splitOn "https://")
  let lines := (noScheme.splitOn "\n").map (fun l =>
    -- Collapse every `_:label` to `_:b`.
    match l.splitOn "_:" with
    | []           => l
    | head :: segs =>
        head ++ String.intercalate "" (segs.map (fun seg =>
          "_:b" ++ String.ofList (seg.toList.dropWhile (fun c =>
            c.isAlphanum || c == '-' || c == '_' || c == '.')))))
  String.intercalate "\n" ((lines.filter (· != "")).toArray.qsort (· < ·) |>.toList)

inductive Verdict where
  | pass
  | fail (why : String)
  | noTransformation
  | unavailable (iri : String)
  | refused (why : String)
deriving Repr, Inhabited

structure Tally where
  pass    : Nat := 0
  fail    : Nat := 0
  /-- How many of the failures differ only by the http/https scheme.
      A SUB-COUNT of `fail`, never a separate bucket: the graphs
      really are different graphs. -/
  drift   : Nat := 0
  noTx    : Nat := 0
  unavail : Nat := 0
  refused : Nat := 0
  /-- Not passed, but a related test (`g:alternative`, `g:subsumes`)
      passed: the case `testft.py` counts as passed. Apart from `pass`. -/
  related : Nat := 0
  /-- Cases a file in `tests/local-overrides` marks not a valid test
      (each file names its issue). Counted apart; a case that passes while
      overridden is a STALE override and counts as a failure. -/
  override : Nat := 0
deriving Inhabited

/-! ## Retrieval

The runner's only job besides comparing: answer a retrieval request
from the vendored files. `docroot/redirects.tsv` records the HTTP
redirections the W3C server answers for suite IRIs; they are followed
first (at most five hops), so the representation carries the IRI it was
finally retrieved from — the base IRI the base-URI tests exercise
(RFC 3986 section 5.1.3). Every decision over the retrieved documents is
`GRDDL.Agent`'s. -/

/-- `requested IRI -> Location`, from `redirects.tsv`. -/
def readRedirects (docroot : String) : IO (List (String × String)) := do
  let path := docroot ++ "/redirects.tsv"
  if !(← System.FilePath.pathExists path) then return []
  let text ← IO.FS.readFile path
  return (text.splitOn "\n").filterMap (fun l =>
    if l.startsWith "#" then none else
    match l.splitOn "\t" with
    | [src, _, loc] => some (src, (loc.trimAsciiEnd).toString)
    | _ => none)

def followRedirects (redirects : List (String × String)) : Nat → String → String
  | 0, iri => iri
  | n + 1, iri =>
      match redirects.find? (·.1 == iri) with
      | some (_, loc) => followRedirects redirects n loc
      | none => iri

/-! ### Language content negotiation

A resource the server negotiates has several representations. The
docroot records them as data in `variants.tsv`: resource IRI,
`Content-Language`, file. The agent sends one language range
(`Accept-Language`, RFC 9110 section 12.5.4). The server's choice is
reproduced as follows.

  * The range is matched against the variants' languages by RFC 4647
    section 3.4 (Lookup): the range itself, then the range with its last
    subtag removed, and so on, a trailing single-character subtag
    removed with it. `de-AT` therefore reaches `de`; the range `*` is
    ignored by Lookup. Measured 2026-10-10 against www.w3.org: `de` and
    `de-AT` receive the `de` variant.
  * With no range, or a range that matches no variant, the server sends
    its default variant, which is the FIRST row of the resource in
    `variants.tsv` (measured: no header, `*`, `fr` and `de;q=0, en;q=0`
    receive the `en` variant). RFC 9110 section 12.5.4 allows this: a
    server may disregard `Accept-Language` instead of answering 406.

The representation reports the IRI the agent requested (after any
redirection) as `retrievedFrom`, the retrieval URI of RFC 3986 section
5.1.3, not the `Content-Location` of the variant: the
`Content-Location` names the variant, and the suite's documents
resolve their relative references (`glean_title.xsl`) the same way
from either. -/

/-- One representation of a negotiated resource. -/
structure Variant where
  iri : String
  language : String
  /-- Path of the representation under the docroot. -/
  file : String
deriving Repr, BEq

/-- Rows of `variants.tsv`: `iri TAB language TAB file`. -/
def parseVariants (text : String) : List Variant :=
  (text.splitOn "\n").filterMap (fun l =>
    if l.startsWith "#" then none else
    match l.splitOn "\t" with
    | [iri, lang, file] =>
        some { iri, language := lang.trimAscii.toString,
               file := file.trimAscii.toString }
    | _ => none)

def readVariants (docroot : String) : IO (List Variant) := do
  let path := docroot ++ "/variants.tsv"
  if !(← System.FilePath.pathExists path) then return []
  return parseVariants (← IO.FS.readFile path)

/-- RFC 4647 section 3.4: the tags a range is tried as, longest first.
A candidate whose last subtag is a single character is skipped, which is
the "remove the single-character subtag together with the subtag before
it" step; `*` is a single character, so Lookup never tries it. -/
def languageCandidates (range : String) : List String :=
  let subtags := range.toLower.splitOn "-"
  ((List.range subtags.length).map (fun i => subtags.take (subtags.length - i))).filterMap
    (fun prefixTags =>
      match prefixTags.getLast? with
      | some last => if last.length > 1 then some (String.intercalate "-" prefixTags) else none
      | none => none)

/-- The variants of the resource `iri`. Both schemes of a suite IRI name
one resource (`iriToLocal`). -/
def variantsOf (variants : List Variant) (iri : String) : List Variant :=
  let here := iriToLocal "" iri
  variants.filter (fun v => here.isSome && iriToLocal "" v.iri == here)

/-- The variant a server sends for `range`; `none` when the resource has
no variants. -/
def chooseVariant (vs : List Variant) (range : Option String) : Option Variant :=
  match vs with
  | [] => none
  | default :: _ =>
      match range with
      | none => some default
      | some r =>
          some (((languageCandidates r).findSome?
                  (fun c => vs.find? (fun v => v.language.toLower == c))).getD default)

/-! Pins for the selection, over the rows of `variants.tsv`. Each has a
positive case and a case built so that a server which ignores the
language, or matches it by string equality only, answers wrongly. -/

def conneg : String := "http://www.w3.org/2001/sw/grddl-wg/td/conneg.html"

def connegRows : List Variant :=
  parseVariants
    ("# a comment row\n" ++ conneg ++ "\ten\ttd/conneg.html\n" ++
     conneg ++ "\tde\ttd/conneg.html.de\n" ++
     "http://www.w3.org/2001/sw/grddl-wg/td/other\tfr\ttd/other.fr\n")

-- Rows: comments skipped, columns read, nothing else invented.
#guard connegRows.length == 3
#guard (connegRows.map (·.language)) == ["en", "de", "fr"]
#guard (parseVariants "only two\tcolumns\n").isEmpty
-- RFC 4647 section 3.4: truncate from the end; `*` and the empty range are never tried.
#guard languageCandidates "de-AT" == ["de-at", "de"]
#guard languageCandidates "zh-Hant-CN-x-private1" == ["zh-hant-cn-x-private1", "zh-hant-cn", "zh-hant", "zh"]
#guard languageCandidates "*" == []
#guard languageCandidates "" == []
-- The variants of a resource: its own rows only, under either scheme.
#guard (variantsOf connegRows conneg).map (·.language) == ["en", "de"]
#guard (variantsOf connegRows "https://www.w3.org/2001/sw/grddl-wg/td/conneg.html").map (·.language) == ["en", "de"]
#guard (variantsOf connegRows "http://www.w3.org/2001/sw/grddl-wg/td/glean_title.xsl").isEmpty
#guard (variantsOf connegRows "http://example.org/conneg.html").isEmpty
-- Selection: the language asked for.
#guard (chooseVariant (variantsOf connegRows conneg) (some "de")).map (·.file) == some "td/conneg.html.de"
#guard (chooseVariant (variantsOf connegRows conneg) (some "en")).map (·.file) == some "td/conneg.html"
#guard (chooseVariant (variantsOf connegRows conneg) (some "DE")).map (·.file) == some "td/conneg.html.de"
#guard (chooseVariant (variantsOf connegRows conneg) (some "de-AT")).map (·.file) == some "td/conneg.html.de"
-- Selection: no range, or no match, receives the first row (the server's default).
#guard (chooseVariant (variantsOf connegRows conneg) none).map (·.file) == some "td/conneg.html"
#guard (chooseVariant (variantsOf connegRows conneg) (some "fr")).map (·.file) == some "td/conneg.html"
#guard (chooseVariant (variantsOf connegRows conneg) (some "*")).map (·.file) == some "td/conneg.html"
-- Negative: "d" is not a prefix match for "de", and a resource without rows has no variant.
#guard (chooseVariant (variantsOf connegRows conneg) (some "d")).map (·.file) == some "td/conneg.html"
#guard (chooseVariant (variantsOf connegRows "http://example.org/x") (some "de")) == none

/-- Answer a retrieval request from the vendored files, as an agent whose
language range is `range` would be answered. -/
def vendoredFetch (docroot : String) (redirects : List (String × String))
    (variants : List Variant) (range : Option String)
    (iri0 : String) : IO (Option Representation) := do
  let iri := followRedirects redirects 5 (stripFragment iri0)
  match chooseVariant (variantsOf variants iri) range with
  | some v =>
      let path := docroot ++ "/" ++ v.file
      if ← System.FilePath.pathExists path then
        return some { retrievedFrom := iri, text := ← IO.FS.readFile path }
      else return none
  | none =>
      match ← readIri docroot iri with
      | some text => return some { retrievedFrom := iri, text }
      | none      => return none

/-- Is this IRI inside the two trees the docroot mirrors? A document
    outside them (the XHTML, RDF and SVG namespace documents,
    `http://www.example.org/...`) is not vendored on purpose; see
    PROVENANCE.md. -/
def inSuiteTrees (iri : String) : Bool :=
  (iriToLocal "" iri).isSome

/-! ## The agent's language

The manifest does not say which language a case's agent asks for; the
GRDDL Test Cases document does, in the text of the three language
cases (section "Testing for Multiple Representations", and the entries
for the cases themselves):

  * `langconneg1`, "Content Negotiation with GRDDL (1 of 2)": "This
    result follows from retrieving a English version of the HTML
    representation".
  * `langconneg2`, "(2 of 2)": "This result follows from retrieving a
    German version of the HTML representation".
  * `langconneg3`, "(3 of 3)": "A GRDDL aware agent may retrieve both
    representations, for example, by using transparent content
    negotiation. This GRDDL result is the merge of the previous two."

Every other case runs with the language `en`: the server's default, so
for a resource without variants the choice changes nothing. -/

inductive AgentLanguage where
  /-- The agent sends this one language range. -/
  | prefers (range : String)
  /-- The agent retrieves every variant of the input resource and
      merges their GRDDL results (GRDDL section 2). -/
  | everyVariant

/-- The manifest fragment of a test IRI: `langconneg2` for
`.../grddl-tests#langconneg2`. -/
def shortName (subject : String) : String :=
  match (subject.splitOn "#").getLast? with
  | some s => s
  | none   => subject

/-- The language of the agent that runs the case `short` (the manifest
fragment). -/
def agentLanguage (short : String) : AgentLanguage :=
  match short with
  | "langconneg2" => .prefers "de"
  | "langconneg3" => .everyVariant
  | _             => .prefers "en"

/-- The GRDDL result of an agent that retrieved several representations
of one resource: the merge of the graphs, blank nodes renamed apart
(`mergeApart`, as `glean` merges several transformations' outputs), and
the reports of all of them together. -/
def combineGleaned (g0 : Gleaned) (rest : List Gleaned) : Gleaned :=
  if rest.isEmpty then g0 else
  let all := g0 :: rest
  { graph := mergeApart (all.map (·.graph) |>.filter (!·.isEmpty))
    transformations := (all.flatMap (·.transformations)).eraseDups
    base := g0.base
    isRdfXml := all.any (·.isRdfXml)
    unretrieved := (all.flatMap (·.unretrieved)).eraseDups
    notXml := (all.flatMap (·.notXml)).eraseDups
    refusals := (all.flatMap (·.refusals)).eraseDups
    converged := all.all (·.converged) }

/-- The GRDDL result for an agent with language `lang`. -/
def gleanAs (docroot : String) (redirects : List (String × String))
    (variants : List Variant) (lang : AgentLanguage) (iri : String) :
    IO (Except String Gleaned) := do
  let ranges : List (Option String) := match lang with
    | .prefers r => [some r]
    | .everyVariant =>
        match (variantsOf variants (followRedirects redirects 5 (stripFragment iri))).map
                (·.language) with
        | []   => [none]
        | langs => langs.map some
  let mut results : List Gleaned := []
  for range in ranges do
    match ← glean (vendoredFetch docroot redirects variants range) iri with
    | .error why => return .error why
    | .ok g      => results := results ++ [g]
  match results with
  | []          => return .error s!"{iri}: no representation retrieved"
  | g0 :: rest  => return .ok (combineGleaned g0 rest)

def runTest (docroot : String) (redirects : List (String × String))
    (variants : List Variant) (t : GTest) :
    IO Verdict := do
  match t.input, t.output with
  | none, _ | _, none => return .fail "the manifest entry names no input or output document"
  | some inIri, some outIri =>
    match ← gleanAs docroot redirects variants (agentLanguage (shortName t.subject)) inIri with
    | .error why =>
        if (iriToLocal docroot inIri).isNone ||
           (why.splitOn "not retrieved").length > 1 then return .unavailable inIri
        else return .refused why
    | .ok g =>
      let missing := g.unretrieved.filter inSuiteTrees
      if g.transformations.isEmpty && !g.isRdfXml then
        if !missing.isEmpty then return .unavailable (String.intercalate ", " missing)
        else return .noTransformation
      else
        match ← readIri docroot outIri with
        | none => return .unavailable outIri
        | some expectedText =>
          -- The expected output describes the SOURCE (`rdf:about=""`
          -- denotes it), so it is read against the input document's IRI
          -- as the manifest names it, never the output file's URL. This
          -- is what the W3C driver testft.py does
          -- (`parse(outputUri, publicID=inputUri)`). The source's
          -- in-document base is NOT applied a second time: an output that
          -- carries its own `xml:base="../.."` (inline-rdf4) means it
          -- relative to the input IRI.
          match L4Factoidal.Syntax.RdfXml.parseRdfXml expectedText (some inIri) with
          | .error e => return .refused s!"the expected output is not RDF/XML: {e.msg}"
          | .ok expected0 =>
            -- An RDF graph is a SET of triples. The parser's list can
            -- repeat a triple (hl7-rim-pomr.rdf states 27 triples twice),
            -- so the comparison deduplicates before the isomorphism test.
            let expected := Graph.union [] expected0
            let outcome := Graph.isomorphicOutcome g.graph expected
            if outcome == .equal then return .pass
            else if outcome == .budgetExceeded then
              return .refused "the isomorphism search exceeded its budget; the graphs are not decided"
            else if !missing.isEmpty then
              return .unavailable (String.intercalate ", " missing)
            else if !g.refusals.isEmpty then
              return .refused (String.intercalate "; " g.refusals)
            else
              -- `GRDDL_DEBUG=<suffix of the input IRI>` prints both graphs.
              let want := (← IO.getEnv "GRDDL_DEBUG").getD ""
              if want != "" && inIri.endsWith want then
                IO.println "--- produced ---"
                IO.println ((Graph.toNTriples g.graph).toOption.getD "(unserialisable)")
                IO.println "--- expected ---"
                IO.println ((Graph.toNTriples expected).toOption.getD "(unserialisable)")
                IO.println s!"--- transformations: {g.transformations}"
                IO.println s!"--- not retrieved: {g.unretrieved}; not XML: {g.notXml}"
              let rt := (Graph.toNTriples g.graph).toOption.getD ""
              let et := (Graph.toNTriples expected).toOption.getD ""
              let drift := rt != "" && schemeBlind rt == schemeBlind et
              let outside := g.unretrieved.filter (fun i => !inSuiteTrees i)
              return Verdict.fail
                (s!"produced {g.graph.length} triple(s), expected {expected.length}"
                 ++ (if drift then
                       " — the two differ ONLY by the http/https scheme, which is"
                       ++ " vendoring drift in the corpus, not a transform defect"
                     else "")
                 ++ (if !g.converged then " (the fixpoint was not reached)" else "")
                 ++ (if outside.isEmpty then "" else
                       s!" (not retrieved, outside the suite trees: {String.intercalate ", " outside})"))

/-! ## Related tests (GRDDL Test Cases, "Tests with Multiple GRDDL Results")

`g:alternative` (symmetric) joins tests whose source has several
equally valid GRDDL results; an agent "should output at least one".
`g:subsumes` points from the maximal-result test to the tests it
merges. The W3C driver `testft.py`, shipped in the Recommendation's
archive, counts a failing test as passed when a test it subsumes, a
test subsuming it, or an alternative of it passed. This runner counts
those cases in their own bucket, apart from pass. -/

def gvNS : String := "http://www.w3.org/2001/sw/grddl-wg/td/grddl-test-vocabulary#"

def relatedPairs (g : Graph) (p : String) : List (String × String) :=
  g.filterMap (fun t =>
    if t.p.val == gvNS ++ p then
      match subjIri t.s, objIri t.o with
      | some a, some b => some (a, b)
      | _, _ => none
    else none)

/-- The tests reachable from `t` over `edges`, `fuel` steps deep. -/
def reach (edges : List (String × String)) : Nat → List String → List String
  | 0, seen => seen
  | n + 1, seen =>
      let next := (edges.filterMap (fun (a, b) => if seen.contains a then some b else none)).filter
        (fun b => !seen.contains b)
      if next.isEmpty then seen else reach edges n (seen ++ next.eraseDups)

/-- Tests related to `t` the way `testft.py` reads the manifest:
    subsuming (transitively), subsumed (transitively), and alternatives
    in either direction (transitively). -/
def relatedTests (mg : Graph) (t : String) : List String :=
  let subs := relatedPairs mg "subsumes"
  let alts := relatedPairs mg "alternative"
  let n := mg.length + 1
  let down := reach subs n [t]
  let up := reach (subs.map (fun (a, b) => (b, a))) n [t]
  let side := reach (alts ++ alts.map (fun (a, b) => (b, a))) n [t]
  ((down ++ up ++ side).filter (· != t)).eraseDups

/-- Read `tests/local-overrides/*.json` (relative to the repository root)
and return the `test_id`s whose `suite` is `suite`. The same file format the
JSON-LD runners read; each file names the issue that tracks the dispute. An
absent directory means no overrides. -/
def loadLocalOverrides (suite : String) : IO (List String) := do
  let dir : System.FilePath := "tests" / "local-overrides"
  let entries ← try dir.readDir catch _ => pure #[]
  let mut ids : List String := []
  for f in entries do
    if !f.fileName.endsWith ".json" then continue
    let txt? ← try pure (some (← IO.FS.readFile (dir / f.fileName))) catch _ => pure none
    match txt? with
    | none => pure ()
    | some txt =>
      match L4Factoidal.JSON.parseJson txt with
      | .error _ => pure ()
      | .ok j =>
        if (j.getString? "suite").getD "" == suite then
          match j.getString? "test_id" with
          | some i => ids := i :: ids
          | none   => pure ()
  pure ids

def main (args : List String) : IO UInt32 := do
  let dir := args.head? |>.getD "third_party/testing/grddl"
  let manifestPath := dir ++ "/grddl-tests-normative.rdf"
  let docroot := dir ++ "/docroot"
  if !(← System.FilePath.pathExists manifestPath) then
    IO.println s!"grddl runner: manifest not found: {manifestPath}"
    IO.println "run tools/ensure-test-env.sh from the repository root first"
    return 1
  let mtext ← IO.FS.readFile manifestPath
  match L4Factoidal.Syntax.RdfXml.parseRdfXml mtext
          (some "http://www.w3.org/2001/sw/grddl-wg/td/grddl-tests-normative.rdf") with
  | .error e =>
      IO.println s!"grddl runner: the manifest did not parse as RDF/XML: {e.msg}"
      return 1
  | .ok mg =>
    let tests := testsOf mg
    let redirects ← readRedirects docroot
    let variants ← readVariants docroot
    let mut verdicts : List (GTest × Verdict) := []
    for gt in tests do
      verdicts := verdicts ++ [(gt, ← runTest docroot redirects variants gt)]
    let passed := verdicts.filterMap (fun (gt, v) =>
      match v with | .pass => some gt.subject | _ => none)
    let overrides ← loadLocalOverrides "grddl"
    let mut t : Tally := {}
    for (gt, v) in verdicts do
      let short := shortName gt.subject
      if overrides.contains short then
        match v with
        | .pass =>
            t := { t with fail := t.fail + 1 }
            IO.println s!"FAIL {short}: STALE local override (the test now passes; delete its file in tests/local-overrides/ and close its issue)"
        | _ =>
            t := { t with override := t.override + 1 }
            IO.println s!"LOCAL-OVERRIDE {short}: marked not a valid test (tests/local-overrides/grddl__{short}.json)"
        continue
      let proxy := (relatedTests mg gt.subject).find? passed.contains
      match v, proxy with
      | .pass, _ => t := { t with pass := t.pass + 1 }
      | _, some other =>
          t := { t with related := t.related + 1 }
          let why := match v with
            | .fail w => w | .noTransformation => "no transformation found"
            | .unavailable i => s!"not in the vendored docroot: {i}"
            | .refused w => w | .pass => ""
          let otherShort := ((other.splitOn "#").getLast?).getD other
          IO.println s!"RELATED-PASS {short}: related test {otherShort} passed ({why})"
      | .fail why, none =>
          t := { t with fail := t.fail + 1,
                        drift := t.drift + (if (why.splitOn "http/https").length > 1
                                            then 1 else 0) }
          IO.println s!"FAIL {short}: {why}"
      | .noTransformation, none =>
          t := { t with noTx := t.noTx + 1 }
          IO.println s!"NO-TRANSFORMATION {short}"
      | .unavailable iri, none =>
          t := { t with unavail := t.unavail + 1 }
          IO.println s!"UNAVAILABLE {short}: not in the vendored docroot: {iri}"
      | .refused why, none =>
          t := { t with refused := t.refused + 1 }
          IO.println s!"REFUSED {short}: {why}"
    let decided := t.pass + t.fail
    IO.println ""
    IO.println s!"grddl DECIDED: {t.pass} pass, {t.fail} fail (out of {decided} decided)"
    IO.println s!"  of those failures, {t.drift} differ ONLY by the http/https scheme"
    IO.println "  (vendoring drift: several inputs were re-fetched from a W3C server"
    IO.println "   that had upgraded its own links, while the expected files beside"
    IO.println "   them still say http. Counted as failures, because the graphs"
    IO.println "   really are different graphs.)"
    IO.println s!"NO TRANSFORMATION FOUND: {t.noTx} cases name no transformation this stage can follow"
    IO.println s!"UNAVAILABLE: {t.unavail} cases need a document the vendored docroot does not carry"
    IO.println s!"REFUSED: {t.refused} cases the engine declined"
    IO.println s!"RELATED TEST PASSED: {t.related} cases did not pass, but a test related by g:alternative or g:subsumes did (testft.py counts these as passed; counted apart here)"
    IO.println s!"LOCAL OVERRIDE: {t.override} cases marked not a valid test (tests/local-overrides, each file names its issue; a passing one is reported STALE as a failure)"
    IO.println s!"  (out of {tests.length} tests in the manifest)"
    IO.println ""
    IO.println "Comparison is by graph ISOMORPHISM: blank-node labels are not"
    IO.println "part of what a GRDDL result means. A case whose documents are"
    IO.println "not mirrored locally is counted apart with the IRI named — this"
    IO.println "runner makes no network request."
    return (if t.fail > 0 then 1 else 0)
