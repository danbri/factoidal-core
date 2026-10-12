/-
L4Factoidal.SPARQL.FullText — the `text:query` extension, slice 1.

Port of `formal/fstar/SPARQL.FullText.fst` (223 lines). Design:
`docs/designissues/2026-07-05-fulltext-sparql-design.md`.

Slice 1 is exact token match with no scoring: the `text:query` AST, a
pure default tokeniser, and the match predicate over token lists. There
is no `score_bm25` and no `rank_results` — this module makes **no
ranking claim**. A caller applies `limit` in dataset order only.

## Where it is wired (https://github.com/danbri/factoidal/issues/727)

* The parser (`SPARQL/Parser.lean`, `pFulltextObject`) reads the jena-text
  object argument after a `text:query` predicate and builds ONE triple
  pattern whose object is the marker literal below.
* The reference evaluator (`SPARQL/Query.lean`, `lowerBgp`) takes each such
  pattern out of its BGP and joins back `fulltextSolutions`, computed from
  the ACTIVE graph, so `GRAPH` chooses the graph that is searched.
* The backend evaluator (`SPARQL/StoreDataset.lean`) and its fast paths
  (LIMIT push-down, streaming `COUNT(*)`, ASK) would read the pattern as an
  ordinary triple and answer nothing; `runSelectQueryBackendDataset` and
  `runAskQueryBackendDataset` answer `none` for such a query
  (`QueryPattern.mentionsFulltext`), and the caller's reference evaluator
  answers.
* The persisted-store planner (`DatasetRestriction.plannerFragment`,
  `ShardManifest.nativeConstantPredicates?`) refuses such a pattern, so no
  shard is skipped: the search reads every literal.

Slice 1 over a persisted store is a SCAN of the decoded dataset; the
`LiteralGramIndex` sidecar is not used. Record, parity check and cost:
`docs/designissues/2026-10-10-lean-geo-distance-fulltext.md`.

## The tokeniser floor, stated

Lowercase and split on anything that is not ASCII alphanumeric. Non-ASCII
bytes act as word separators. That is the documented floor, not a defect:
Unicode-aware analysis is the design doc's slice-3 `analyze_text` seam.

The F\* module folds case with a self-contained ASCII fold rather than
reusing `SPARQL11.Algebra`'s `string_lowercase_unicode` `assume val`,
because that module ends up depending on this one and reusing it would
cycle the graph.

This port keeps an explicit ASCII fold too, and the reason is NOT the
one I first wrote here. I assumed Lean's `String.toLower` was
Unicode-aware and would widen the floor. **Measured: it is not.**
`"ÉCOLE".toLower` is `"École"` — `Char.toLower` maps `A`–`Z` and
nothing else, so on this input it agrees with the F\* fold exactly.

The fold stays explicit anyway, for a smaller reason: the tokeniser's
floor is a documented part of the slice-1 contract, and it should not be
able to move because a standard-library function's case-folding scope
widened in a later toolchain. A `#guard` pins the current agreement
rather than asserting a difference that does not exist.

## Why the object argument is encoded into a literal

jena-text's list form `(property "term" limit)` is ordinary SPARQL
collection syntax, which the parser desugars into an
`rdf:first`/`rdf:rest` chain in a SIBLING group graph pattern joined to
the main triple — not a second triple pattern in the same BGP that a
per-triple evaluation hook sees. Resolving that generically needs a
pattern-level rewrite pass, and it is not what real magic-property
engines do either: Jena's ARQ intercepts the argument list during
algebra compilation, before it could become literal `rdf:first` matching
against data that has no such triples.

So the parser recognises `text:query` directly, before the generic
collection desugaring runs, and encodes the resolved query into a single
internally-tagged literal that the evaluator decodes back out of the
object position (`TriplePattern.fulltext?`). User-visible SPARQL syntax is
unaffected.
-/
import L4Factoidal.SPARQL.Algebra

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-! ## Vocabulary — jena-text's namespace, reused verbatim for tool
compatibility. -/

def fulltextQueryPred : WfIri := ⟨"http://jena.apache.org/text#query", rfl⟩

/-- The internal marker datatype carrying the parsed `(field, term,
    limit)` tuple through the ordinary literal AST. It never appears in
    user-visible RDF data: the parser is the only producer and
    `TriplePattern.fulltext?` the only consumer. -/
def fulltextArgsDatatype : WfIri := ⟨"http://jena.apache.org/text#query-args", rfl⟩

/-- `field = none` is jena-text's bare-string two-arity form. -/
structure FulltextQuery where
  field : Option WfIri
  terms : String
  limit : Option Nat
  deriving Repr, DecidableEq, Inhabited

/-! ## The default tokeniser -/

def isAsciiDigitC (c : Char) : Bool := c.toNat ≥ 0x30 && c.toNat ≤ 0x39
def isAsciiUpper (c : Char) : Bool := c.toNat ≥ 0x41 && c.toNat ≤ 0x5A
def isAsciiLowerC (c : Char) : Bool := c.toNat ≥ 0x61 && c.toNat ≤ 0x7A
def isAsciiAlnum (c : Char) : Bool := isAsciiDigitC c || isAsciiUpper c || isAsciiLowerC c

/-- ASCII-only case fold, written out here and not taken from a library
    function — see the module header on why the floor is deliberate. This
    tokeniser is not an `UCASE` / `LCASE` consumer, and
    `Text.CaseMap.lowerCase` (Unicode default case mapping) does not apply to
    it. -/
def asciiFoldChar (c : Char) : Char :=
  if isAsciiUpper c then Char.ofNat (c.toNat + 32) else c

def asciiLowercase (s : String) : String :=
  String.ofList (s.toList.map asciiFoldChar)

def splitWordsAcc : List Char → List Char → List String → List String
  | [],      cur, acc =>
      if cur.isEmpty then acc.reverse
      else (String.ofList cur.reverse :: acc).reverse
  | c :: rest, cur, acc =>
      if isAsciiAlnum c then splitWordsAcc rest (c :: cur) acc
      else if cur.isEmpty then splitWordsAcc rest [] acc
      else splitWordsAcc rest [] (String.ofList cur.reverse :: acc)

def defaultTokenizer (s : String) : List String :=
  splitWordsAcc (asciiLowercase s).toList [] []

/-! ## Match semantics — all tokens (AND), the design doc's slice-1
recommendation. -/

def matchTokens (queryTokens candidateTokens : List String) : Bool :=
  queryTokens.all (fun qt => candidateTokens.contains qt)

def literalMatchesQuery (ftq : FulltextQuery) (l : WfLiteral) : Bool :=
  matchTokens (defaultTokenizer ftq.terms) (defaultTokenizer l.val.lexicalForm)

/-! ## The object-argument codec

`unitSep` (ASCII Unit Separator, 0x1F) is a control byte no realistic
search term or field IRI contains. The field and limit ride in the
LEXICAL FORM rather than the datatype IRI, so the user's raw search term
is never itself parsed or escaped — only split out of its two
delimiter-bounded neighbours. -/

def unitSep : Char := Char.ofNat 31
def unitSepStr : String := String.ofList [unitSep]

def splitOnCharAcc (delim : Char) : List Char → List Char → List String → List String
  | [],        cur, acc => (String.ofList cur.reverse :: acc).reverse
  | c :: rest, cur, acc =>
      if c == delim then splitOnCharAcc delim rest [] (String.ofList cur.reverse :: acc)
      else splitOnCharAcc delim rest (c :: cur) acc

def splitOnChar (delim : Char) (s : String) : List String :=
  splitOnCharAcc delim s.toList [] []

def chartsToNatDigits : List Char → Nat → Nat
  | [],        acc => acc
  | c :: rest, acc => chartsToNatDigits rest (acc * 10 + (c.toNat - 0x30))

def stringToNat (s : String) : Option Nat :=
  let cs := s.toList
  if cs.isEmpty then none
  else if cs.all isAsciiDigitC then some (chartsToNatDigits cs 0)
  else none

def encodeFulltextLiteral (ftq : FulltextQuery) : WfLiteral :=
  let fieldPart := match ftq.field with | none => "" | some f => f.val
  let limitPart := match ftq.limit with | none => "" | some n => toString n
  ⟨{ lexicalForm := fieldPart ++ unitSepStr ++ ftq.terms ++ unitSepStr ++ limitPart,
     datatype := fulltextArgsDatatype, langTag := none, direction := none }, rfl⟩

def decodeFulltextLiteral (l : WfLiteral) : Option FulltextQuery :=
  if l.val.datatype != fulltextArgsDatatype then none
  else
    match splitOnChar unitSep l.val.lexicalForm with
    | [fieldPart, term, limitPart] =>
        let field : Option WfIri :=
          if fieldPart.isEmpty then none
          else if h : isIri fieldPart then some ⟨fieldPart, h⟩ else none
        let limit := if limitPart.isEmpty then none else stringToNat limitPart
        some { field := field, terms := term, limit := limit }
    | _ => none

/-- The per-candidate filter the evaluation (`fulltextCandidates`)
    applies to each candidate triple. Takes the object as a `Term`
    because that is what a triple's object position holds. -/
def objectMatchesQuery (ftq : FulltextQuery) : Term → Bool
  | .literal l => literalMatchesQuery ftq l
  | _          => false

/-! ## Evaluation — slice 1, over one graph

Port of the F\* `eval_fulltext_tp_store` (`SPARQL11.Algebra.fst`). The
candidates are the triples of the active graph whose predicate is the
field (every triple when there is no field), in graph order; a candidate
matches when its object is a literal whose tokens include every query
token; the limit, when there is one, keeps the first `n` matches; and
only then is the subject bound. So the limit counts MATCHING TRIPLES, not
subjects, and it is applied before the subject pattern is checked —
exactly the F\* order (`list_take n matched`, then `try_bind_subject`).

`fulltextScan` stops reading the graph once the limit is reached and
tokenises the query once rather than once per candidate. `fulltextScan_eq`
proves it returns exactly the list the spec-shaped `fulltextCandidates`
describes. -/

/-- The object test with the query already tokenised. -/
def objectMatchesTokens (queryTokens : List String) : Term → Bool
  | .literal l => matchTokens queryTokens (defaultTokenizer l.val.lexicalForm)
  | _          => false

theorem objectMatchesTokens_eq (ftq : FulltextQuery) (o : Term) :
    objectMatchesTokens (defaultTokenizer ftq.terms) o = objectMatchesQuery ftq o := by
  cases o <;> rfl

/-- Is this triple a candidate: its predicate is the field, when there is one. -/
def inField (field : Option WfIri) (t : Triple) : Bool :=
  match field with
  | none   => true
  | some f => t.p == f

/-- The specification of the candidate list: filter by field, filter by
match, take the limit. -/
def fulltextCandidates (ftq : FulltextQuery) (g : Graph) : List Triple :=
  let matched := g.filter (fun t => inField ftq.field t && objectMatchesQuery ftq t.o)
  match ftq.limit with
  | some n => matched.take n
  | none   => matched

/-- The same list, computed in one tail-recursive pass that stops at the
limit. `remaining = none` means no limit. -/
def fulltextScanGo (queryTokens : List String) (field : Option WfIri) :
    List Triple → Option Nat → List Triple → List Triple
  | [],        _,            acc => acc.reverse
  | _,         some 0,       acc => acc.reverse
  | t :: rest, remaining,    acc =>
      if inField field t && objectMatchesTokens queryTokens t.o then
        fulltextScanGo queryTokens field rest (remaining.map (· - 1)) (t :: acc)
      else fulltextScanGo queryTokens field rest remaining acc

def fulltextScan (ftq : FulltextQuery) (g : Graph) : List Triple :=
  fulltextScanGo (defaultTokenizer ftq.terms) ftq.field g ftq.limit []

private theorem fulltextScanGo_none (qt : List String) (field : Option WfIri) :
    ∀ (g acc : List Triple),
      fulltextScanGo qt field g none acc
        = acc.reverse ++ g.filter (fun t => inField field t && objectMatchesTokens qt t.o)
  | [], acc => by simp [fulltextScanGo]
  | t :: rest, acc => by
      by_cases h : (inField field t && objectMatchesTokens qt t.o) = true
      · simp only [fulltextScanGo, h, if_true, Option.map_none,
          fulltextScanGo_none qt field rest (t :: acc), List.filter_cons, List.reverse_cons]
        simp
      · simp only [fulltextScanGo, h, Bool.false_eq_true, if_false,
          fulltextScanGo_none qt field rest acc, List.filter_cons]

private theorem fulltextScanGo_some (qt : List String) (field : Option WfIri) :
    ∀ (n : Nat) (g acc : List Triple),
      fulltextScanGo qt field g (some n) acc
        = acc.reverse ++ (g.filter (fun t => inField field t && objectMatchesTokens qt t.o)).take n
  | 0, [], acc => by simp [fulltextScanGo]
  | 0, _ :: _, acc => by simp [fulltextScanGo]
  | n + 1, [], acc => by simp [fulltextScanGo]
  | n + 1, t :: rest, acc => by
      by_cases h : (inField field t && objectMatchesTokens qt t.o) = true
      · simp only [fulltextScanGo, h, if_true, Option.map_some,
          Nat.add_sub_cancel, fulltextScanGo_some qt field n rest (t :: acc),
          List.filter_cons, List.reverse_cons]
        simp
      · simp only [fulltextScanGo, h, Bool.false_eq_true, if_false,
          fulltextScanGo_some qt field (n + 1) rest acc, List.filter_cons]

/-- The one-pass scan is the specification's list, order included. -/
theorem fulltextScan_eq (ftq : FulltextQuery) (g : Graph) :
    fulltextScan ftq g = fulltextCandidates ftq g := by
  have hf : (fun t : Triple => inField ftq.field t
              && objectMatchesTokens (defaultTokenizer ftq.terms) t.o)
          = (fun t => inField ftq.field t && objectMatchesQuery ftq t.o) := by
    funext t; rw [objectMatchesTokens_eq]
  unfold fulltextScan fulltextCandidates
  cases hl : ftq.limit with
  | none => rw [fulltextScanGo_none, hf]; simp
  | some n => rw [fulltextScanGo_some, hf]; simp

/-- The solutions of one `text:query` pattern over the active graph: the
matched triples' subjects, bound to the pattern's subject. One row per
MATCHED TRIPLE, so a subject with two matching literals gives two rows,
as in the F\* engine. -/
def fulltextSolutions (ftq : FulltextQuery) (s : PatternSubject) (g : Graph) :
    SolutionSeq :=
  (fulltextScan ftq g).filterMap (fun t => tryBindSubject s t.s Binding.empty)

/-! ## Recognising a `text:query` triple pattern

A triple pattern is a `text:query` pattern when its predicate is the
`text:query` IRI and its object is the marker-typed literal the parser
builds. A `text:query` predicate with any other object is an ordinary
triple pattern, which matches the data as written — the F\*
`eval_single_tp_store` falls through to `eval_single_tp_store_default`
in that case, and so does this port. -/

def TriplePattern.fulltext? (tp : TriplePattern) : Option FulltextQuery :=
  match tp.p, tp.o with
  | .iri p, .literal l => if p == fulltextQueryPred then decodeFulltextLiteral l else none
  | _, _ => none

/-- Does a BGP hold a `text:query` pattern? -/
def bgpHasFulltext (b : Bgp) : Bool := b.any (fun tp => tp.fulltext?.isSome)

/-! ## Build-time checks

### The tokeniser -/

#guard defaultTokenizer "Hello, World!" == ["hello", "world"]
#guard defaultTokenizer "" == []
#guard defaultTokenizer "   " == []
#guard defaultTokenizer "a1 B2" == ["a1", "b2"]
#guard defaultTokenizer "one--two__three" == ["one", "two", "three"]

/-! Punctuation at both ends must not produce empty tokens. -/

#guard defaultTokenizer ",hello," == ["hello"]
#guard !(defaultTokenizer ",hello,").contains ""

/-! ### The fold is ASCII, and the floor is deliberate

`É` is uppercase and this fold does NOT touch it; the tokeniser then
treats it as a separator, so `"ÉCOLE"` yields `["cole"]`. That is the
documented slice-1 floor.

Lean's `String.toLower` currently agrees — MEASURED, not assumed:
`"ÉCOLE".toLower` is `"École"`, because `Char.toLower` maps `A`–`Z` and
nothing else. The guard pins that agreement. If a later toolchain widens
`toLower`, this fold does not move with it and the guard says so. -/

#guard asciiLowercase "ÉCOLE" == "École"
#guard "ÉCOLE".toLower == asciiLowercase "ÉCOLE"
#guard defaultTokenizer "ÉCOLE" == ["cole"]

/-! ### Match is AND over tokens, and it is a SUBSET test -/

#guard matchTokens ["a"] ["a", "b"]
#guard matchTokens ["a", "b"] ["a", "b", "c"]
#guard !matchTokens ["a", "z"] ["a", "b"]
#guard matchTokens [] ["a"]          -- an empty query matches anything
#guard !matchTokens ["a"] []

/-! Order does not matter and repetition does not matter — the property
    that makes it a token-set test rather than a substring test. -/

#guard matchTokens ["b", "a"] ["a", "b"]
#guard matchTokens ["a", "a"] ["a"]

/-! ### The codec round-trips, including the empty-field and
    empty-limit forms — those are the two-arity and three-arity jena
    shapes, and a codec that lost them would still round-trip the full
    form. -/

private def rt (q : FulltextQuery) : Bool :=
  decodeFulltextLiteral (encodeFulltextLiteral q) == some q

#guard rt { field := none, terms := "hello", limit := none }
#guard rt { field := none, terms := "hello", limit := some 10 }
#guard rt { field := some ⟨"http://www.w3.org/2000/01/rdf-schema#label", by rfl⟩,
            terms := "hello", limit := none }
#guard rt { field := some ⟨"http://www.w3.org/2000/01/rdf-schema#label", by rfl⟩,
            terms := "hello world", limit := some 5 }

/-! A term containing SPACES and PUNCTUATION survives the codec
    untouched — the whole reason the metadata rides in delimited slots
    rather than being escaped into the datatype IRI. -/

#guard rt { field := none, terms := "a, b; c \"d\"", limit := none }
#guard rt { field := none, terms := "", limit := none }

/-! ### A literal of any other datatype decodes to nothing

The marker datatype is the gate. Without this check the codec would
happily read a user's ordinary string literal as a query. -/

#guard (decodeFulltextLiteral (Literal.string "anything")).isNone
#guard (decodeFulltextLiteral (Literal.langString "x" "en")).isNone

/-! ### Only a literal object can match -/

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

#guard objectMatchesQuery { field := none, terms := "hello", limit := none }
        (.literal (Literal.string "Hello there"))
#guard !objectMatchesQuery { field := none, terms := "hello", limit := none }
        (.iri ⟨"http://e/hello", exIri "hello"⟩)
#guard !objectMatchesQuery { field := none, terms := "hello", limit := none }
        (.bnode "hello")
#guard !objectMatchesQuery { field := none, terms := "missing", limit := none }
        (.literal (Literal.string "Hello there"))

/-! Matching is on TOKENS, not substrings: `"ell"` must not match
    `"Hello"`. That is the difference between this and a `CONTAINS`
    filter, and it is what "exact token match" in slice 1 means. -/

#guard !objectMatchesQuery { field := none, terms := "ell", limit := none }
        (.literal (Literal.string "Hello there"))

/-! ### Evaluation over a graph

A five-triple graph: two labels with "panel", one title with "panel", one
label without it, and a non-literal object carrying the word in its IRI. -/

private def ex (s : String) : WfIri := ⟨"http://e/" ++ s, exIri s⟩
private def lbl : WfIri := ⟨"http://www.w3.org/2000/01/rdf-schema#label", rfl⟩
private def ttl : WfIri := ⟨"http://purl.org/dc/elements/1.1/title", rfl⟩

private def gPanels : Graph :=
  [ { s := .iri (ex "a"), p := lbl, o := .literal (Literal.string "Solar panel array") },
    { s := .iri (ex "b"), p := lbl, o := .literal (Literal.string "Solar panel kit") },
    { s := .iri (ex "c"), p := ttl, o := .literal (Literal.string "Control panel") },
    { s := .iri (ex "d"), p := lbl, o := .literal (Literal.string "Water heater") },
    { s := .iri (ex "e"), p := lbl, o := .iri (ex "panel") } ]

private def subjectsOf (rows : SolutionSeq) : List String :=
  rows.filterMap (fun mu => match mu.lookup "s" with
    | some (.iri i) => some i.val
    | _ => none)

private def q (terms : String) (field : Option WfIri := none) (limit : Option Nat := none) :
    FulltextQuery := { field := field, terms := terms, limit := limit }

-- No field: every literal is searched, in graph order; the IRI object is not.
#guard subjectsOf (fulltextSolutions (q "panel") (.var "s") gPanels)
         == ["http://e/a", "http://e/b", "http://e/c"]
-- AND of tokens.
#guard subjectsOf (fulltextSolutions (q "solar PANEL") (.var "s") gPanels)
         == ["http://e/a", "http://e/b"]
#guard subjectsOf (fulltextSolutions (q "solar heater") (.var "s") gPanels) == []
-- A field restricts the predicate.
#guard subjectsOf (fulltextSolutions (q "panel" (some lbl)) (.var "s") gPanels)
         == ["http://e/a", "http://e/b"]
#guard subjectsOf (fulltextSolutions (q "panel" (some ttl)) (.var "s") gPanels)
         == ["http://e/c"]
-- A limit keeps the first n matches in graph order; zero keeps none.
#guard subjectsOf (fulltextSolutions (q "panel" none (some 2)) (.var "s") gPanels)
         == ["http://e/a", "http://e/b"]
#guard (fulltextSolutions (q "panel" none (some 0)) (.var "s") gPanels).isEmpty
-- The limit counts MATCHES before the subject is checked, as in the F*:
-- a constant subject outside the first n matches gets no row.
#guard (fulltextSolutions (q "panel" none (some 1)) (.iri (ex "b")) gPanels).isEmpty
#guard (fulltextSolutions (q "panel") (.iri (ex "b")) gPanels).length == 1
#guard (fulltextSolutions (q "panel") (.iri (ex "d")) gPanels).isEmpty
-- The one-pass scan and the specification list agree on these graphs.
#guard fulltextScan (q "panel" none (some 2)) gPanels == fulltextCandidates (q "panel" none (some 2)) gPanels
#guard fulltextScan (q "panel" (some lbl)) gPanels == fulltextCandidates (q "panel" (some lbl)) gPanels

/-! ### Recognising the pattern -/

private def ftTp (obj : PatternTerm) : TriplePattern :=
  { s := .var "s", p := .iri fulltextQueryPred, o := obj }

#guard (ftTp (.literal (encodeFulltextLiteral (q "panel")))).fulltext? == some (q "panel")
#guard bgpHasFulltext [ftTp (.literal (encodeFulltextLiteral (q "panel")))]
-- A text:query predicate with an ordinary object is an ordinary triple pattern.
#guard (ftTp (.literal (Literal.string "panel"))).fulltext?.isNone
#guard (ftTp (.var "o")).fulltext?.isNone
#guard !bgpHasFulltext [ftTp (.var "o")]
-- The marker literal under any other predicate is an ordinary object.
#guard ({ s := .var "s", p := .iri lbl,
          o := .literal (encodeFulltextLiteral (q "panel")) } : TriplePattern).fulltext?.isNone

end L4Factoidal.SPARQL
