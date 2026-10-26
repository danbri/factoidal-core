/- Build-time equivalence checks for grammar-validated decoded Turtle chunks. -/
import L4Factoidal.Syntax.TurtleChunkFold

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

def chunkGraph (source : String) (chunks : List String) : Except ParseError Graph := do
  let reversed ← parseTurtleChunksFold (freshBnodePrefix source)
    (fun accRev triples => triples.reverse ++ accRev) [] chunks
  pure reversed.reverse

def chunksMatchParser (source : String) (chunks : List String) : Bool :=
  match chunkGraph source chunks, parseTurtle source with
  | .ok chunked, .ok ordinary => chunked == ordinary
  | .error _, .error _ => true
  | _, _ => false

def charChunks (source : String) : List String := source.toList.map String.singleton

private def basic : String :=
  "@prefix ex: <http://example.org/> .\nex:s ex:p ex:o .\n"
#guard chunksMatchParser basic ["@prefix ex: <http://exa", "mple.org/> .\nex:s ex:p ex:o .", "\n"]

/- The scanner must carry all of these lexical states across chunk cuts; only
`readStatement` establishes the actual Turtle meaning. -/
private def lexical : String :=
  "PREFIX ex: <http://example.org/>\nex:s ex:p \"\"\"dot.\nand []\"\"\" .\n[] ex:p ex:o .\n"
#guard chunksMatchParser lexical [
  "PREFIX ex: <http://example.org/>", "\nex:s ex:p \"\"", "\"dot.\n",
  "and []\"\"\" .\n[", "] ex:p ex:o .\n"]
#guard chunksMatchParser lexical (charChunks lexical)

/- A decimal dot and dots within a prefixed IRI must not become separate
statements when their following chunks arrive. -/
private def dotted : String :=
  "@prefix ex: <http://example.org/a.b/> .\nex:s ex:p 1.0 .\n"
#guard chunksMatchParser dotted ["@prefix ex: <http://example.org/a", ".b/> .\nex:s ex:p 1.", "0 .\n"]


/-! ## Comments and the no-dot directives (owner question, 2026-09-03)

The scanner's directive test reads the first seven characters of the
current candidate after leading whitespace. When a comment precedes a
`PREFIX`/`BASE` line inside the same candidate, the test sees `# ...` and
does not cut at that line end; the directive then stays in the candidate
until the next dot or the end of input. That is safe because a candidate
may hold several statements and `consumeText` runs the grammar in a loop
over it; the test only decides where boundaries fall, never what the text
means. Every two-way split of each source below, plus one-character chunks,
agrees with `parseTurtle` (1,115 chunkings on 2026-09-03). -/

private def allSplits (source : String) : List (List String) :=
  let cs := source.toList
  (List.range (cs.length + 1)).map
    (fun i => [String.ofList (cs.take i), String.ofList (cs.drop i)]) ++ [charChunks source]

private def allSplitsMatch (source : String) : Bool :=
  (allSplits source).all (chunksMatchParser source)

#guard allSplitsMatch "# leading comment\nPREFIX ex: <http://example.org/>\nex:s ex:p ex:o .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\n# note\nPREFIX ex2: <http://example.org/2/>\nex:s ex:p ex2:o .\n"
#guard allSplitsMatch "# PREFIX not: <http://nope/>\nPREFIX ex: <http://example.org/>\nex:s ex:p ex:o .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p ex:o . # trailing\nBASE <http://base.example/>\n<rel> ex:p ex:o .\n"
#guard allSplitsMatch "\n\n  # c\n   prefix ex: <http://example.org/>\nex:s ex:p ex:o .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p \"\"\"line one\nPREFIX fake: <http://x/>\nline three\"\"\" .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p \"PREFIX ex: <http://x/>\" .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p <http://example.org/doc#PREFIX> .\n"
#guard allSplitsMatch "<http://example.org/s> <http://example.org/p> <http://example.org/o> .\nPREFIX ex: <http://example.org/>"
#guard allSplitsMatch "PREFIX a: <http://a/>\nPREFIX b: <http://b/>\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/> ex:s ex:p ex:o .\n"
#guard allSplitsMatch "# c\n@prefix ex: <http://example.org/> .\nex:s ex:p ex:o .\n"
#guard allSplitsMatch "# c\r\nPREFIX ex: <http://example.org/>\r\nex:s ex:p ex:o .\r\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p ex:o ;\n   ex:q ex:PREFIXED .\n"


/- Dots inside comments are not candidate boundaries: `pendingDot` is set only
when the mode after the character is `normal`, and a comment keeps mode
`comment` until its line end. The directive after such a comment is
therefore deferred past the comment's dots too. -/
#guard allSplitsMatch "# comment with a dot. and more text\nPREFIX ex: <http://example.org/>\nex:s ex:p ex:o .\n"
#guard allSplitsMatch "# note.\nPREFIX ex: <http://example.org/>\nex:s ex:p ex:o .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p ex:o . # ends with a dot.\nex:s ex:q ex:o .\n"
#guard allSplitsMatch "PREFIX ex: <http://example.org/>\nex:s ex:p ex:o ; # mid-statement comment.\n  ex:q ex:o .\n"

/-! ## `parseTurtleText` against `parseTurtle` (https://github.com/danbri/factoidal/issues/729)

`parseTurtleText` is what `l4factoidal` and the wasm `parse` ops read Turtle
with. Each guard compares the whole result, error message and offset
included. `walkMatches` checks the scanner walk ALONE (no fallback) on a
document `parseTurtle` accepts, so the guards cannot pass by falling back to
`parseTurtle` everywhere. -/

def sameParse : Except ParseError Graph → Except ParseError Graph → Bool
  | .ok a, .ok b => a == b
  | .error a, .error b => a == b
  | _, _ => false

def textMatches (source : String) (mode : Mode := .rdf11) (base : Option String := none) : Bool :=
  sameParse (parseTurtleText source base mode) (parseTurtle source base mode)

/-- The walk alone gives `parseTurtle`'s graph, and that graph is not an error. -/
def walkMatches (source : String) (mode : Mode := .rdf11) (base : Option String := none) : Bool :=
  match parseTurtleWalk source base mode, parseTurtle source base mode with
  | .ok a, .ok b => a == b
  | _, _ => false

/-- The walk fails where `parseTurtle` succeeds: `parseTurtleText` needs its fallback. -/
def walkNeedsFallback (source : String) (mode : Mode := .rdf11) : Bool :=
  match parseTurtleWalk source none mode, parseTurtle source none mode with
  | .error _, .ok _ => true
  | _, _ => false

private def acceptedSources : List String := [
  basic, lexical, dotted,
  "# leading comment\nPREFIX ex: <http://example.org/>\nex:s ex:p ex:o .\n",
  "PREFIX ex: <http://example.org/>\n# note\nPREFIX ex2: <http://example.org/2/>\nex:s ex:p ex2:o .\n",
  "# PREFIX not: <http://nope/>\nPREFIX ex: <http://example.org/>\nex:s ex:p ex:o .\n",
  "PREFIX ex: <http://example.org/>\nex:s ex:p ex:o . # trailing\nBASE <http://base.example/>\n<rel> ex:p ex:o .\n",
  "PREFIX ex: <http://example.org/>\nex:s ex:p \"\"\"line one\nPREFIX fake: <http://x/>\nline three\"\"\" .\n",
  "PREFIX ex: <http://example.org/>\nex:s ex:p <http://example.org/doc#PREFIX> .\n",
  "<http://example.org/s> <http://example.org/p> <http://example.org/o> .\nPREFIX ex: <http://example.org/>",
  "PREFIX ex: <http://example.org/> ex:s ex:p ex:o .\n",
  "# c\r\nPREFIX ex: <http://example.org/>\r\nex:s ex:p ex:o .\r\n",
  "PREFIX ex: <http://example.org/>\nex:s ex:p ex:o ; # mid-statement comment.\n  ex:q ex:o .\n",
  -- blank nodes, property lists, collections; a document label that is a
  -- prefix of the generated ones
  "@prefix ex: <http://example.org/> .\n_:anon_x ex:p [ ex:q ( 1 2.5 -3e2 ) ; ex:r [] ] .\n[] ex:p _:b1 .\n",
  -- literals: decimals, a dot after an integer, language tags, datatypes,
  -- long strings holding dots, quotes and line breaks
  "@prefix ex: <http://example.org/> .\n@prefix xsd: <http://www.w3.org/2001/XMLSchema#> .\nex:s ex:p 1.5, 2 , \"x\"@en-GB, \"7\"^^xsd:int, '''a. \"b\".\nc''', \"q\\\". \" .\n",
  -- an integer directly before the statement's dot
  "@prefix ex: <http://example.org/> .\nex:s ex:p 2.\nex:s ex:q 3.0 .\n",
  -- no final line break; a final dot with no whitespace after it
  "@prefix ex: <http://example.org/> .\nex:s ex:p ex:o .",
  "@prefix ex: <http://example.org/> .\nex:s ex:p ex:o .# end",
  -- empty and comment-only documents
  "", "  \n\t\n", "# only a comment",
  -- relative IRIs against a changing base
  "BASE <http://a.example/x/>\n<s> <p> <o> .\n@base <../y/> .\n<s> <p> <#o> .\n",
  -- prefixed names with dots inside
  "@prefix ex: <http://example.org/> .\nex:a.b ex:p.q ex:c.d .\nex:e ex:f ex:g.\n" ]

#guard acceptedSources.all (fun s => walkMatches s)
#guard acceptedSources.all (fun s => textMatches s)
#guard acceptedSources.all (fun s => walkMatches s .rdf12)
#guard textMatches "<s> <p> <o> .\n" .rdf11 (some "http://base.example/dir/")

-- A collection read through the scanner walk, nested and long, with a dot
-- inside a string and a decimal, and its chunked fold at every 97th
-- character: the same
-- graph and the same blank-node labels as `parseTurtle`
-- (https://github.com/danbri/factoidal/issues/678).
private def collectionSource : String :=
  "@prefix ex: <http://example.org/> .\nex:s ex:p ( [ ex:q ( 1 2 ) ] ( ) ex:o \"a. b\"\n  3.0 ) .\n" ++
  "( " ++ " ".intercalate ((List.range 500).map toString) ++ " ) ex:p ( ( ( 4 ) ) ) .\n"
#guard walkMatches collectionSource
#guard textMatches collectionSource
#guard chunksMatchParser collectionSource
  ((List.range (collectionSource.length / 97 + 1)).map
    (fun i => String.ofList ((collectionSource.toList.drop (97 * i)).take 97)))
-- Negative: an unterminated collection is refused with `parseTurtle`'s error.
#guard textMatches "@prefix ex: <http://example.org/> .\nex:s ex:p ( 1 2 .\n"
#guard match parseTurtleText "@prefix ex: <http://example.org/> .\nex:s ex:p ( 1 2 .\n" with
  | .error _ => true | .ok _ => false
-- Long object lists and many `;` groups read through the scanner walk, with
-- `[ ]` objects that have their own groups, a `;;` run, a trailing `;`, a dot
-- inside a string, and the chunked fold at every 97th character: the same
-- graph and the same blank-node labels as `parseTurtle`
-- (https://github.com/danbri/factoidal/issues/754).
private def listsSource : String :=
  "@prefix ex: <http://example.org/> .\nex:s ex:p 1, [ ex:q 2 ; ex:r 3, \"a. b\" ], ( 4 ) ;; ex:t [ ex:u [ ex:v 5 ] ] ; .\n" ++
  "ex:s ex:p " ++ ", ".intercalate ((List.range 500).map toString) ++ " .\n" ++
  "ex:s " ++ " ; ".intercalate ((List.range 500).map fun i => s!"ex:p{i} [ ex:q {i} ; ex:r {i}, {i} ]") ++ " ; .\n"
#guard walkMatches listsSource
#guard textMatches listsSource
#guard chunksMatchParser listsSource
  ((List.range (listsSource.length / 97 + 1)).map
    (fun i => String.ofList ((listsSource.toList.drop (97 * i)).take 97)))
-- Negative: a `,` with no object after it is refused with `parseTurtle`'s error.
#guard textMatches "@prefix ex: <http://example.org/> .\nex:s ex:p 1, 2, ; ex:q 3 .\n"
#guard match parseTurtleText "@prefix ex: <http://example.org/> .\nex:s ex:p 1, 2, ; ex:q 3 .\n" with
  | .error _ => true | .ok _ => false
#guard walkMatches "<s> <p> <o> .\n" .rdf11 (some "http://base.example/dir/")

-- Documents `parseTurtle` refuses: `parseTurtleText` reports the same error,
-- message and offset (`parseTurtleText_error` proves it for every error).
private def refusedSources : List String := [
  "ex:s ex:p ex:o .\n",
  "@prefix ex: <http://example.org/> .\nex:s ex:p ex:o\n",
  "@prefix ex: <http://example.org/> .\nex:s ex:p \"open .\n",
  "@prefix ex: <http://example.org/> .\nex:s ex:p ex:o . ex:t ex:p .\n",
  "@prefix ex: <http://example.org/> .\nex:s ex:p [ ex:q ex:o . ] .\n",
  "PREFIX ex:\n",
  -- `2.` ends the statement, so the `,` after it starts nothing
  "@prefix ex: <http://example.org/> .\nex:s ex:p 1.5, 2., ex:o .\n" ]
#guard refusedSources.all (fun s => textMatches s)
#guard refusedSources.all (fun s => match parseTurtle s with | .error _ => true | .ok _ => false)

-- Documents the walk alone refuses where `parseTurtle` succeeds: a
-- SPARQL-style directive split over two lines, and a statement whose subject
-- starts with `base:` and goes on to the next line (the scanner cuts both at
-- the line end). `parseTurtleText` falls back and agrees.
private def splitDirective : String := "PREFIX ex:\n  <http://example.org/>\nex:s ex:p ex:o .\n"
private def baseLike : String := "@prefix base: <http://b.example/> .\nbase:s base:p\n  base:o .\n"
#guard walkNeedsFallback splitDirective
#guard walkNeedsFallback baseLike
#guard textMatches splitDirective
#guard textMatches baseLike

-- RDF 1.2 triple terms: `hasDoubleLt` sends the document to `parseTurtle`.
private def tripleTerm : String :=
  "@prefix ex: <http://example.org/> .\nex:s ex:p <<( ex:a ex:b \"x>y. z\" )>> .\n<< ex:a ex:b ex:c >> ex:q ex:o .\n"
#guard hasDoubleLt tripleTerm
#guard !hasDoubleLt "@prefix ex: <http://example.org/> .\nex:s ex:p \"a < b\" , <http://x/> .\n"
#guard !hasDoubleLt "< <"
#guard hasDoubleLt "x<<"
#guard textMatches tripleTerm .rdf12
#guard (match parseTurtle tripleTerm none .rdf12 with | .ok g => g.length == 3 | .error _ => false)

-- The generated blank-node prefix read from the `String` is the one read from
-- its characters (`freshBnodePrefixText_eq`): one more underscore than the
-- longest run in the document.
#guard freshBnodePrefixText "_:a__b" == "anon___"
#guard freshBnodePrefixText "" == "anon_"

-- `parseTurtleTextWithPrefixes` (the reader of the wasm `datasetOpen` op since
-- 2026-10-24) gives the graph AND the prefixes of `parseTurtleWithPrefixes`
-- (the character-list parser the op used before), errors included. The graph
-- part is `parseTurtleTextWithPrefixes_map_fst`; the prefixes from the walk's
-- Turtle state are pinned here, not proved.
def samePrefixParse (source : String) (mode : Mode := .rdf11) (base : Option String := none) : Bool :=
  match parseTurtleTextWithPrefixes source base mode, parseTurtleWithPrefixes source base mode with
  | .ok (g1, p1), .ok (g2, p2) => decide (g1 = g2) && p1 == p2
  | .error e1, .error e2 => decide (e1 = e2)
  | _, _ => false

private def prefixSources : List String := [
  "",
  "@prefix ex: <http://example.org/> .\nex:s ex:p ex:o .\n",
  "PREFIX ex: <http://example.org/>\nPREFIX : <http://d/>\n:s ex:p :o .\n",
  "@prefix a: <http://a/> .\n@prefix a: <http://b/> .\na:s a:p a:o .\n",
  "@base <http://b/> .\n@prefix : <x#> .\n:s :p :o .\nBASE <http://c/>\nPREFIX q: <y#>\nq:s :p q:o .",
  "@prefix ex: <http://example.org/> .\nex:s ex:p [ ex:q ex:r ] , ( 1 2 ) .\n",
  "@prefix ex: <http://example.org/> .\nex:s ex:p",
  "@prefix ex: <http://example.org/> .\nex:s ex:p ex:o ; .\nex:t ex:p ex:o .",
  "@prefix ex: <http://example.org/> .\nex:s ex:p \"a . b\" .\n@prefix ex2: <http://e2/> .\nex2:s ex:p ex2:o"
]
#guard prefixSources.all (fun d => samePrefixParse d)
#guard prefixSources.all (fun d => samePrefixParse d .rdf12)
#guard samePrefixParse tripleTerm .rdf12
#guard samePrefixParse splitDirective
#guard samePrefixParse baseLike
#guard acceptedSources.all (fun d => samePrefixParse d)
#guard refusedSources.all (fun d => samePrefixParse d)

end L4Factoidal.Syntax
