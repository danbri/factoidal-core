/-
L4Factoidal.Syntax.TurtleSerialize — the Turtle pretty-printer.

Port of `formal/fstar/RDF.Turtle.Serialize.fst` (502 lines).

The wire-correct serialisers exist for round-trip and hashing fidelity;
this one targets a HUMAN-FACING rendering of the same graph — a
`@prefix` header, `;`-joined predicate lists, `,`-joined object lists,
one block per subject. The owner's brief for it was "ensure serializers
are not gratuitously ugly".

## The correctness anchor, and what it forbids

`parseTurtle (turtleOfGraph table g)` must give back `g`. So an
abbreviation may be emitted only when the parser would accept it, which
is why `tsAbbreviateIri` calls the SAME `Syntax.validatePnLocal` the
parser uses rather than approximating the Turtle grammar a second time.
An IRI whose remainder is not `PN_LOCAL`-safe falls back to `<iri>`.

Two abbreviations are used, both round-trip safe: a prefixed name when
the local part validates, and the `a` keyword for `rdf:type`, which
Turtle defines as its shorthand and the parser accepts unconditionally.

Numeric and boolean literals are printed in their bare Turtle form (`42`,
`1.5`, `1e3`, `true`) when the option `literalShorthand` is on, which is the
default, AND the lexical form matches the grammar terminal of the literal's
datatype (`literalShorthand` below: INTEGER, DECIMAL, DOUBLE and
BooleanLiteral of Turtle §6.5). A lexical form that does not match, such as
`"5."^^xsd:decimal` or one with a leading space, keeps the quoted form, so the
printed text always reads back to the same (lexical form, datatype) pair. The
datatype IRI in the quoted form is abbreviated, since that is pure compaction
with no ambiguity.

This follows `RDF.Turtle.Serialize.fst` as changed by
https://github.com/danbri/factoidal/issues/681, which superseded the earlier
quoted-only decision ("correctness over sugar") both trees carried. The Lean
tree changed with it so that the two engines print the same text
(https://github.com/danbri/factoidal/issues/685).

## Options

`TurtleRenderOptions.prefixes` is a caller-supplied table of (namespace IRI,
`label:`) pairs that WINS over the derived one: a pair is emitted only when some
IRI of the graph lies under its namespace, in the caller's order, the first
occurrence of a namespace winning, and a derived label is never one a caller
pair already took. `turtleOfGraphOpts` is the entry point; `turtleOfGraphAuto`
is `turtleOfGraphOpts` with the defaults.

## Auto prefix derivation

Split each IRI at its last `#` or `/`, count the namespaces whose
remainder is `PN_LOCAL`-safe, prefer the eight well-known prefixes when
they occur, and fill the rest with `ns1:`…`ns8:`. A namespace whose
IRIs never compact cleanly earns no header line, because the per-term
fallback already covers it.

## What the F\* module proves, and what it does not

It carries `lemma_ts_abbreviate_iri_pname_safe`, a structural fact
about the abbreviator, and its banner is explicit that the term-level
round trip is out of reach there: the literal path goes through byte
primitives that stay opaque to the solver, so even
`nq_escape_literal "a" == "a"` fails to reduce. Wire correctness of the
literal path is pinned at the CLI level instead.

Lean has the opposite situation. `Syntax.escapeLiteral` is an ordinary
computable function, so the round trip is CHECKABLE by `#guard` on
concrete graphs, through the real `parseTurtle` — which is what the
checks at the end do. That is evidence at the checked shapes, not a
theorem for all graphs, and this note says which it is.
-/
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.NTriples
import L4Factoidal.RDFS.Vocabulary

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## Joins

One reverse-accumulate then one concat, so a graph whose triples all
share a subject and predicate stays linear rather than quadratic. -/

def joinWithAcc (sep : String) : List String → List String → List String
  | [], acc => acc
  | [x], acc => x :: acc
  | x :: rest, acc => joinWithAcc sep rest (sep :: x :: acc)

def joinWith (sep : String) (xs : List String) : String :=
  String.join (joinWithAcc sep xs []).reverse

/-! ## The prefix table

`(namespace IRI, "label:")` pairs — the label already carries its
colon. -/

abbrev PrefixTable := List (String × String)

def tsStartsWithStrict (s pfx : String) : Bool :=
  s.length > pfx.length && s.startsWith pfx

def tsFindPrefix (table : PrefixTable) (iri : String) : Option (String × String) :=
  table.find? (fun p => tsStartsWithStrict iri p.1)

/-- `PN_LOCAL` may legally be empty (a bare `ex:`); anything non-empty
    must satisfy the parser's own validator. -/
def tsLocalOk (loc : String) : Bool :=
  loc.isEmpty || validatePnLocal loc.toList true

/-- Compact to a prefixed name only when the parser would read it back;
    otherwise emit the full `<iri>`. -/
def tsAbbreviateIri (table : PrefixTable) (iri : String) : String :=
  match tsFindPrefix table iri with
  | some (ns, abbr) =>
      let loc := String.ofList (iri.toList.drop ns.length)
      if tsLocalOk loc then abbr ++ loc else "<" ++ iri ++ ">"
  | none => "<" ++ iri ++ ">"

/-! ## Bare literals — Turtle §6.5 terminals

```
INTEGER        ::= [+-]? [0-9]+
DECIMAL        ::= [+-]? [0-9]* '.' [0-9]+
DOUBLE         ::= [+-]? ( [0-9]+ '.' [0-9]* EXPONENT | '.' [0-9]+ EXPONENT | [0-9]+ EXPONENT )
EXPONENT       ::= [eE] [+-]? [0-9]+
BooleanLiteral ::= 'true' | 'false'
```

Each checker accepts a lexical form only when the terminal consumes the WHOLE
string. Port of `is_turtle_integer_lexical` and its siblings. -/

def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `[+-]?` at the front. -/
def dropSign : List Char → List Char
  | '+' :: r => r
  | '-' :: r => r
  | cs => cs

/-- `[0-9]*`: how many digits there are at the front, and what follows them. -/
def scanDigits (cs : List Char) : Nat × List Char :=
  ((cs.takeWhile isAsciiDigit).length, cs.dropWhile isAsciiDigit)

/-- `[0-9]+` and nothing else. -/
def allDigitsNonEmpty (cs : List Char) : Bool := !cs.isEmpty && cs.all isAsciiDigit

/-- `EXPONENT`, consuming the whole remainder. -/
def isExponentSuffix : List Char → Bool
  | e :: r => (e == 'e' || e == 'E') && allDigitsNonEmpty (dropSign r)
  | [] => false

def isTurtleIntegerLexical (s : String) : Bool := allDigitsNonEmpty (dropSign s.toList)

def isTurtleDecimalLexical (s : String) : Bool :=
  match (scanDigits (dropSign s.toList)).2 with
  | '.' :: frac => allDigitsNonEmpty frac
  | _ => false

def isTurtleDoubleLexical (s : String) : Bool :=
  let r := dropSign s.toList
  match r with
  | '.' :: rest =>
      let (n, after) := scanDigits rest
      n > 0 && isExponentSuffix after
  | c :: _ =>
      if isAsciiDigit c then
        let (_, afterInt) := scanDigits r
        match afterInt with
        | '.' :: rest => isExponentSuffix (scanDigits rest).2
        | _ => isExponentSuffix afterInt
      else false
  | [] => false

def isTurtleBooleanLexical (s : String) : Bool := s == "true" || s == "false"

/-- The bare text of a literal whose datatype is `xsd:integer`, `xsd:decimal`,
`xsd:double` or `xsd:boolean` AND whose lexical form matches that datatype's
terminal; `none` otherwise, and the caller prints the quoted form. Port of
`literal_shorthand`. -/
def literalShorthand (l : Literal) : Option String :=
  if l.datatype == xsdInteger && isTurtleIntegerLexical l.lexicalForm then some l.lexicalForm
  else if l.datatype == xsdDecimal && isTurtleDecimalLexical l.lexicalForm then some l.lexicalForm
  else if l.datatype == xsdDouble && isTurtleDoubleLexical l.lexicalForm then some l.lexicalForm
  else if l.datatype == xsdBoolean && isTurtleBooleanLexical l.lexicalForm then some l.lexicalForm
  else none

/-! ## Terms -/

def tsTermToTurtle (table : PrefixTable) (shorthand : Bool) : Term → String
  | .iri i => tsAbbreviateIri table i.val
  | .bnode b => "_:" ++ b
  | .literal l =>
      let esc := escapeLiteral l.val.lexicalForm
      match l.val.langTag with
      | some tag =>
          let ds := match l.val.direction with
                    | some .ltr => "--ltr"
                    | some .rtl => "--rtl"
                    | none => ""
          "\"" ++ esc ++ "\"@" ++ tag ++ ds
      | none =>
          if l.val.datatype == xsdString then "\"" ++ esc ++ "\""
          else
            match (if shorthand then literalShorthand l.val else none) with
            | some bare => bare
            | none => "\"" ++ esc ++ "\"^^" ++ tsAbbreviateIri table l.val.datatype.val
  | .tripleTerm s p o =>
      let subjStr := match s with
                     | .iri i => tsAbbreviateIri table i.val
                     | .bnode b => "_:" ++ b
      let predStr := if p == rdfType then "a" else tsAbbreviateIri table p.val
      "<<( " ++ subjStr ++ " " ++ predStr ++ " " ++ tsTermToTurtle table shorthand o ++ " )>>"

def tsSubjectToTurtle (table : PrefixTable) : Subject → String
  | .iri i => tsAbbreviateIri table i.val
  | .bnode b => "_:" ++ b

/-- `a` is Turtle's own shorthand for `rdf:type`, accepted back by the
    parser, and needs no prefix-table entry. -/
def tsPredicateToTurtle (table : PrefixTable) (p : WfIri) : String :=
  if p == rdfType then "a" else tsAbbreviateIri table p.val

/-! ## Sorting and subject grouping

The sort key is subject, separator, predicate, separator, object — the
same discipline the closure path's dedup uses. The separator is U+001F,
which the F\* source documents as forbidden inside an IRI, so the join
is unambiguous. -/

def unitSep : String := String.singleton (Char.ofNat 31)

def tsTermKey : Term → String
  | .iri i => "1" ++ i.val
  | .bnode b => "0" ++ b
  | .literal l => "2" ++ l.val.lexicalForm ++ unitSep ++ l.val.datatype.val ++
      unitSep ++ l.val.langTag.getD ""
  | .tripleTerm _ _ _ => "3"

def tsSubjKey : Subject → String
  | .iri i => "1" ++ i.val
  | .bnode b => "0" ++ b

def tsTripleKey (t : Triple) : String :=
  tsSubjKey t.s ++ unitSep ++ t.p.val ++ unitSep ++ tsTermKey t.o

/-- Lean's own merge sort, keyed by `tsTripleKey`. The F\* module uses
    `List.Tot.sortWith triple_cmp`; this is the same O(n log n) sort
    with the comparator expressed as a `≤` on the key string. -/
def sortTriples (g : List Triple) : List Triple :=
  g.mergeSort (fun a b => tsTripleKey a ≤ tsTripleKey b)

structure SubjState where
  subj        : Subject
  subjText    : String
  curPred     : WfIri
  curPredText : String
  curObjs     : List String
  predChunks  : List String

def finishPred (st : SubjState) : List String :=
  (st.curPredText ++ " " ++ joinWith " , " st.curObjs.reverse) :: st.predChunks

def finishSubj (st : SubjState) : String :=
  st.subjText ++ " " ++ joinWith " ;\n    " (finishPred st).reverse ++ " .\n\n"

def walkTriples (table : PrefixTable) (shorthand : Bool) : List Triple → Option SubjState →
    List String → List String
  | [], none, acc => acc
  | [], some s, acc => finishSubj s :: acc
  | t :: rest, none, acc =>
      walkTriples table shorthand rest (some
        { subj := t.s, subjText := tsSubjectToTurtle table t.s,
          curPred := t.p, curPredText := tsPredicateToTurtle table t.p,
          curObjs := [tsTermToTurtle table shorthand t.o], predChunks := [] }) acc
  | t :: rest, some s, acc =>
      let objText := tsTermToTurtle table shorthand t.o
      if s.subj == t.s then
        if s.curPred == t.p then
          walkTriples table shorthand rest (some { s with curObjs := objText :: s.curObjs }) acc
        else
          walkTriples table shorthand rest (some
            { s with curPred := t.p, curPredText := tsPredicateToTurtle table t.p,
                     curObjs := [objText], predChunks := finishPred s }) acc
      else
        walkTriples table shorthand rest (some
          { subj := t.s, subjText := tsSubjectToTurtle table t.s,
            curPred := t.p, curPredText := tsPredicateToTurtle table t.p,
            curObjs := [objText], predChunks := [] }) (finishSubj s :: acc)

def renderTriples (table : PrefixTable) (shorthand : Bool) (g : Graph) : String :=
  String.join (walkTriples table shorthand (sortTriples g) none []).reverse

/-! ## The header and the entry point -/

def renderPrefixHeader (table : PrefixTable) : List String :=
  table.map (fun (ns, abbr) => "@prefix " ++ abbr ++ " <" ++ ns ++ "> .\n")

def turtleOfGraph (table : PrefixTable) (shorthand : Bool) (g : Graph) : String :=
  let headerLines := renderPrefixHeader table
  String.join headerLines ++ (if headerLines.isEmpty then "" else "\n") ++
    renderTriples table shorthand g

/-! ## Auto prefix derivation -/

/-- The last `#` or `/`, as a split into `(namespace-with-delimiter,
    local)`. `none` when the IRI has neither and so cannot be
    compacted. -/
def nsSplit (iri : String) : Option (String × String) :=
  let cs := iri.toList
  let idx := cs.zipIdx.foldl (fun best (ci : Char × Nat) =>
    if ci.1 == '#' || ci.1 == '/' then some ci.2 else best) none
  match idx with
  | none => none
  | some i => some (String.ofList (cs.take (i + 1)), String.ofList (cs.drop (i + 1)))

/-- Every IRI in the graph: subjects, predicates, object IRIs, and
    literal datatypes other than the implicit `xsd:string` and language
    cases, which never print with a suffix. The IRIs nested inside a
    triple term are skipped, as in F\* — they print un-abbreviated,
    which is correct if less pretty. -/
def collectIris (g : Graph) : List String :=
  g.flatMap (fun t =>
    [t.p.val] ++
    (match t.s with | .iri i => [i.val] | _ => []) ++
    (match t.o with
     | .iri i => [i.val]
     | .literal l => match l.val.langTag with
                     | some _ => []
                     | none => if l.val.datatype == xsdString then []
                               else [l.val.datatype.val]
     | _ => []))

def candidateNamespaces (iris : List String) : List String :=
  iris.filterMap (fun i =>
    match nsSplit i with
    | none => none
    | some (ns, loc) =>
        if !loc.isEmpty && validatePnLocal loc.toList true then some ns else none)

def countRuns : List String → List (String × Nat)
  | [] => []
  | [x] => [(x, 1)]
  | x :: y :: rest =>
      if x == y then
        match countRuns (y :: rest) with
        | (y2, n) :: more => (y2, n + 1) :: more
        | [] => [(x, 1)]
      else (x, 1) :: countRuns (y :: rest)

/-- Descending by count, STABLE: namespaces of equal count keep the order they
had, which is what F\*'s `List.Tot.sortWith count_desc_compare` gives. (An
insertion sort that places each element after its equals reverses the ties, and
with them the order in which `ns1:`, `ns2:` … are handed out.) -/
def sortByCountDesc (xs : List (String × Nat)) : List (String × Nat) :=
  xs.mergeSort (fun a b => decide (b.2 ≤ a.2))

/-- Ascending, as F\*'s `List.Tot.sortWith String.compare`. -/
def sortStrs (xs : List String) : List String :=
  xs.mergeSort (fun a b => decide (a ≤ b))

def assignLabels : Nat → List (String × Nat) → List (String × String)
  | _, [] => []
  | idx, (ns, _) :: rest =>
      if idx < 9 then (ns, "ns" ++ toString idx ++ ":") :: assignLabels (idx + 1) rest
      else []

/-- Preferred over auto-numbered labels when the graph uses them: real
    graphs are dominated by `rdf:type` and `xsd:` datatypes, and a
    numbered prefix for those would be needless ugliness. -/
def wellKnownPrefixes : PrefixTable :=
  [ ("http://www.w3.org/1999/02/22-rdf-syntax-ns#", "rdf:")
  , ("http://www.w3.org/2000/01/rdf-schema#",       "rdfs:")
  , ("http://www.w3.org/2001/XMLSchema#",           "xsd:")
  , ("http://www.w3.org/2002/07/owl#",              "owl:")
  , ("http://xmlns.com/foaf/0.1/",                  "foaf:")
  , ("http://purl.org/dc/terms/",                   "dcterms:")
  , ("http://purl.org/dc/elements/1.1/",            "dc:")
  , ("http://schema.org/",                          "schema:") ]

/-- Render options. -/
structure TurtleRenderOptions where
  /-- Caller-supplied (namespace IRI, `label:`) pairs; they win over the derived
  table. -/
  prefixes : PrefixTable := []
  /-- Bare INTEGER, DECIMAL, DOUBLE and BooleanLiteral when the lexical form
  qualifies. -/
  literalShorthand : Bool := true

/-- Does some IRI of the graph lie strictly under namespace `ns`? -/
def tsAnyIriUsesNs (iris : List String) (ns : String) : Bool :=
  iris.any (fun i => tsStartsWithStrict i ns)

/-- The caller's pairs whose namespace some IRI of the graph uses, in the
caller's order. The first occurrence of a namespace wins: a repeat is dropped
even when the first occurrence went unused, and a namespace no IRI uses is not
emitted. Port of `ts_user_used`. -/
def tsUserUsed (iris : List String) : PrefixTable → List String → PrefixTable
  | [], _ => []
  | (ns, label) :: rest, seenNs =>
      if seenNs.contains ns then tsUserUsed iris rest seenNs
      else if tsAnyIriUsesNs iris ns then (ns, label) :: tsUserUsed iris rest (ns :: seenNs)
      else tsUserUsed iris rest (ns :: seenNs)

/-- `ns1:` … `ns8:`, skipping any label already taken by the caller's table or
the well-known table, so a caller label `ns1:` is never given to another
namespace. `idx` only grows, which is the termination measure. Port of
`assign_labels_avoiding`. -/
def assignLabelsAvoiding (reserved : List String) :
    (fuel : Nat) → (idx : Nat) → List (String × Nat) → List (String × String)
  | 0, _, _ => []
  | _, _, [] => []
  | fuel + 1, idx, (ns, n) :: rest =>
      if idx ≥ 9 then []
      else
        let label := "ns" ++ toString idx ++ ":"
        if reserved.contains label then assignLabelsAvoiding reserved fuel (idx + 1) ((ns, n) :: rest)
        else (ns, label) :: assignLabelsAvoiding reserved fuel (idx + 1) rest

/-- The prefix table for a graph and its options, then the document. Caller
pairs first, then the well-known labels the graph uses, then at most
`8 - (those)` numbered ones for the most frequent remaining namespaces. Port of
`turtle_of_graph_opts`. -/
def turtleOfGraphOpts (opts : TurtleRenderOptions) (g : Graph) : String :=
  let iris := collectIris g
  let counted := countRuns (sortStrs (candidateNamespaces iris))
  let presentNs := counted.map (·.1)
  let userUsed := tsUserUsed iris opts.prefixes []
  let userNs := userUsed.map (·.1)
  let userLabels := userUsed.map (·.2)
  let known := (wellKnownPrefixes.filter (fun p => presentNs.contains p.1)).filter
    (fun p => !userNs.contains p.1 && !userLabels.contains p.2)
  let knownNs := known.map (·.1)
  let knownLabels := known.map (·.2)
  let coveredNs := userNs ++ knownNs
  let fresh := (sortByCountDesc counted).filter (fun p => !coveredNs.contains p.1)
  let coveredLen := userUsed.length + known.length
  let budget := if coveredLen ≥ 8 then 0 else 8 - coveredLen
  let freshTop := fresh.take budget
  let auto := assignLabelsAvoiding (userLabels ++ knownLabels) 10 1 freshTop
  turtleOfGraph (userUsed ++ known ++ auto) opts.literalShorthand g

/-- The default rendering: no caller prefixes, bare literals on. -/
def turtleOfGraphAuto (g : Graph) : String := turtleOfGraphOpts {} g

/-! ## Build-time checks

### Abbreviation happens only when the parser would read it back -/

private def wi (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩
  else ⟨"http://example.org/not-an-iri", by simp [isIri, String.isEmpty]⟩

private def exTable : PrefixTable := [("http://example.org/", "ex:")]

#guard tsAbbreviateIri exTable "http://example.org/a" == "ex:a"
#guard tsAbbreviateIri exTable "http://other.org/a" == "<http://other.org/a>"

/-! A local part the parser would reject is NOT compacted: a space
    cannot appear in `PN_LOCAL`, so the full form is emitted. -/

#guard tsAbbreviateIri exTable "http://example.org/a b"
       == "<http://example.org/a b>"

/-! The strict prefix test needs the IRI to be LONGER than the
    namespace, so an IRI equal to it does not compact. -/

#guard tsAbbreviateIri exTable "http://example.org/" == "<http://example.org/>"

/-! ### `rdf:type` renders as `a`, in PREDICATE position only -/

#guard tsPredicateToTurtle [] rdfType == "a"
#guard tsPredicateToTurtle exTable (wi "http://example.org/p") == "ex:p"
#guard tsTermToTurtle [] true (.iri rdfType) ==
       "<http://www.w3.org/1999/02/22-rdf-syntax-ns#type>"

/-! ### Literals -/

private def litT (lex : String) (dt : String) : Term :=
  let l : Literal := { lexicalForm := lex, datatype := wi dt,
                       langTag := none, direction := none }
  if h : literalWf l then .literal ⟨l, h⟩ else .bnode "bad"

#guard tsTermToTurtle [] true (litT "x" "http://www.w3.org/2001/XMLSchema#string")
       == "\"x\""
-- With shorthand OFF the quoted form is the only one (the pre-681 behaviour).
#guard tsTermToTurtle [("http://www.w3.org/2001/XMLSchema#", "xsd:")] false
         (litT "1" "http://www.w3.org/2001/XMLSchema#integer") == "\"1\"^^xsd:integer"
#guard tsTermToTurtle [] true (litT "a\"b" "http://www.w3.org/2001/XMLSchema#string")
       == "\"a\\\"b\""

/-! ### Bare literals: the grammar terminals, in both directions

A bare form is printed only when the lexical form is exactly an INTEGER,
DECIMAL, DOUBLE or BooleanLiteral of the literal's own datatype. -/

private def xsd (n : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ n
private def bare (lex dt : String) : String := tsTermToTurtle [] true (litT lex (xsd dt))
private def quoted (lex dt : String) : String := tsTermToTurtle [] false (litT lex (xsd dt))

#guard bare "42" "integer" == "42"
#guard bare "-7" "integer" == "-7"
#guard bare "+7" "integer" == "+7"
#guard bare "0" "integer" == "0"
#guard bare "1.5" "decimal" == "1.5"
#guard bare ".5" "decimal" == ".5"
#guard bare "-0.50" "decimal" == "-0.50"
#guard bare "1e3" "double" == "1e3"
#guard bare "1.5E-3" "double" == "1.5E-3"
#guard bare "1.e3" "double" == "1.e3"
#guard bare ".5e+2" "double" == ".5e+2"
#guard bare "true" "boolean" == "true"
#guard bare "false" "boolean" == "false"
-- Not a terminal of the datatype's own production: stays quoted.
#guard bare "" "integer" == "\"\"^^<" ++ xsd "integer" ++ ">"
#guard bare "+" "integer" == "\"+\"^^<" ++ xsd "integer" ++ ">"
#guard bare "1.0" "integer" == "\"1.0\"^^<" ++ xsd "integer" ++ ">"
#guard bare " 1" "integer" == "\" 1\"^^<" ++ xsd "integer" ++ ">"
#guard bare "5." "decimal" == "\"5.\"^^<" ++ xsd "decimal" ++ ">"
#guard bare "5" "decimal" == "\"5\"^^<" ++ xsd "decimal" ++ ">"
#guard bare "." "decimal" == "\".\"^^<" ++ xsd "decimal" ++ ">"
#guard bare "1.5" "double" == "\"1.5\"^^<" ++ xsd "double" ++ ">"
#guard bare "1e" "double" == "\"1e\"^^<" ++ xsd "double" ++ ">"
#guard bare "e5" "double" == "\"e5\"^^<" ++ xsd "double" ++ ">"
#guard bare "INF" "double" == "\"INF\"^^<" ++ xsd "double" ++ ">"
#guard bare "1" "boolean" == "\"1\"^^<" ++ xsd "boolean" ++ ">"
#guard bare "True" "boolean" == "\"True\"^^<" ++ xsd "boolean" ++ ">"
-- The datatype decides: a digit string typed as a string or a date is quoted.
#guard bare "42" "string" == "\"42\""
#guard bare "42" "long" == "\"42\"^^<" ++ xsd "long" ++ ">"
-- Turned off, every one of them is quoted.
#guard quoted "42" "integer" == "\"42\"^^<" ++ xsd "integer" ++ ">"
#guard quoted "true" "boolean" == "\"true\"^^<" ++ xsd "boolean" ++ ">"

-- Whole-graph output: the bare form reads back to the same graph, the quoted
-- form too, and the two differ.
private def numGraph : Graph :=
  [ ⟨.iri (wi "http://x/a"), wi "http://x/n", litT "42" (xsd "integer")⟩
  , ⟨.iri (wi "http://x/a"), wi "http://x/d", litT "1.5" (xsd "decimal")⟩
  , ⟨.iri (wi "http://x/a"), wi "http://x/e", litT "1e3" (xsd "double")⟩
  , ⟨.iri (wi "http://x/a"), wi "http://x/b", litT "true" (xsd "boolean")⟩
  , ⟨.iri (wi "http://x/a"), wi "http://x/q", litT "5." (xsd "decimal")⟩ ]

#guard ((turtleOfGraphOpts {} numGraph).splitOn "^^").length == 2
#guard ((turtleOfGraphOpts { literalShorthand := false } numGraph).splitOn "^^").length == 6
#guard (match parseTurtle (turtleOfGraphOpts {} numGraph) none .rdf12 with
        | .ok g2 => sortTriples g2 == sortTriples numGraph
        | .error _ => false)
#guard (match parseTurtle (turtleOfGraphOpts { literalShorthand := false } numGraph) none .rdf12 with
        | .ok g2 => sortTriples g2 == sortTriples numGraph
        | .error _ => false)

/-! ### Caller prefixes win, and are emitted only when used -/

private def exOpts : TurtleRenderOptions :=
  { prefixes := [("http://x/", "ex:"), ("http://unused.example/", "un:")] }

#guard ((turtleOfGraphOpts exOpts numGraph).splitOn "@prefix ex: <http://x/> .").length == 2
-- A namespace no IRI uses gets no header line.
#guard ((turtleOfGraphOpts exOpts numGraph).splitOn "un:").length == 1
-- The caller's label is the one used in the body.
#guard ((turtleOfGraphOpts exOpts numGraph).splitOn "ex:a ex:").length == 2
-- Without a caller table the derived one names the same namespace `ns1:`.
#guard ((turtleOfGraphOpts {} numGraph).splitOn "@prefix ns1: <http://x/> .").length == 2
-- A derived label never takes one the caller used: `ns1:` is reserved here.
private def ns1Taken : TurtleRenderOptions := { prefixes := [("http://y/", "ns1:")] }
private def twoNs : Graph :=
  [ ⟨.iri (wi "http://y/a"), wi "http://x/p", .iri (wi "http://x/b")⟩ ]
#guard ((turtleOfGraphOpts ns1Taken twoNs).splitOn "@prefix ns1: <http://y/> .").length == 2
#guard ((turtleOfGraphOpts ns1Taken twoNs).splitOn "@prefix ns2: <http://x/> .").length == 2
-- The first occurrence of a namespace wins over a later repeat.
private def dup : TurtleRenderOptions :=
  { prefixes := [("http://x/", "ex:"), ("http://x/", "other:")] }
#guard ((turtleOfGraphOpts dup numGraph).splitOn "other:").length == 1
-- Ties in count keep their order: `ns1:` goes to the namespace that sorts first.
private def tie : Graph :=
  [ ⟨.iri (wi "http://b.example/a"), wi "http://a.example/p", .iri (wi "http://c.example/c")⟩ ]
#guard ((turtleOfGraphOpts {} tie).splitOn "@prefix ns1: <http://a.example/> .").length == 2

/-! ### The round trip, through the real parser

The F\* banner records that this could not be proved OR
`assert_norm`-witnessed there, because the literal path goes through
byte primitives that stay opaque to the solver. In Lean these are
ordinary computable functions, so the round trip is checkable — at
these shapes, which is evidence and not a theorem. -/

private def g1 : Graph :=
  [ ⟨.iri (wi "http://example.org/a"), rdfType, .iri (wi "http://example.org/C")⟩
  , ⟨.iri (wi "http://example.org/a"), wi "http://example.org/p",
     .iri (wi "http://example.org/b")⟩
  , ⟨.iri (wi "http://example.org/a"), wi "http://example.org/p",
     litT "hello" "http://www.w3.org/2001/XMLSchema#string"⟩
  , ⟨.bnode "b0", wi "http://example.org/q",
     litT "a\"b\\c" "http://www.w3.org/2001/XMLSchema#string"⟩ ]

private def roundTrips (g : Graph) : Bool :=
  match parseTurtle (turtleOfGraphAuto g) none .rdf12 with
  | .error _ => false
  | .ok g2 => sortTriples g2 == sortTriples g

#guard roundTrips g1
#guard roundTrips []
#guard roundTrips [⟨.iri (wi "http://x/y"), wi "http://x/p", .iri (wi "http://x/z")⟩]

/-! An IRI that cannot be compacted round-trips through the `<…>`
    fallback. -/

#guard roundTrips [⟨.iri (wi "http://x/a"), wi "http://x/p",
                    litT "1" "http://www.w3.org/2001/XMLSchema#integer"⟩]

/-! ### Grouping: `;` between predicates, `,` between objects -/

#guard ((turtleOfGraphAuto g1).splitOn " ;\n    ").length == 2
#guard ((turtleOfGraphAuto g1).splitOn " , ").length == 2

/-! ### The auto table prefers a well-known label over a numbered one -/

#guard ((turtleOfGraphAuto
  [⟨.iri (wi "http://example.org/a"), rdfType,
    .iri (wi "http://www.w3.org/2000/01/rdf-schema#Class")⟩]).splitOn
  "@prefix rdfs:").length == 2

end L4Factoidal.Syntax
