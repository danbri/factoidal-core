/-
L4Factoidal.SPARQL.LangTagCanonicalTests — one RDF term has one spelling of
its language tag, so a SPARQL answer does not depend on the order of the
triple patterns.

RDF 1.2 Concepts §3.4: language tags are compared case-insensitively, so
`"x"@en` and `"x"@EN` are one RDF term, and "lexical representations of
language tags MAY be converted to lower case". SPARQL 1.1 §18.1.7: a
solution maps a variable to an RDF term. Before the repair the reference
evaluator bound `?o` to the spelling of the pattern it matched FIRST
(`tryBindTerm` keeps the first term and compares later ones with the
case-folding `Term.eqb`), so `FILTER(LANG(?o) = "en")` kept one row for one
pattern order and no row for the other.

The repair (https://github.com/danbri/factoidal/issues/1001): the
well-formedness rule `RDF.literalWf` requires the canonical (lower-case)
tag, so no `WfLiteral` has an upper-case tag, and every reader and every
literal constructor writes the tag in lower case. The guards below pin the
issue's query in both orders on both evaluation paths, `LANG()`, `STRLANG`,
and the tag that each reader gives for an upper-case input tag.

Every `#guard` is evaluated by `lake build`, so a wrong answer fails the
build.
-/
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.SPARQL.ResultsXml
import L4Factoidal.SPARQL.ResultsJson
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.NQuadsFast
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.Syntax.RdfJson
import L4Factoidal.JSONLD.ToRdf

namespace L4Factoidal.SPARQL.LangTagCanonicalTests

open L4Factoidal.RDF L4Factoidal.SPARQL

/-! ### The data and the query of issue 1001 -/

private def data : Graph :=
  (Syntax.parseTurtle ("@prefix : <http://example.org/> . " ++
    ":a :p \"x\"@en . :b :p \"y\" . :a :q \"x\"@EN .")).toOption.getD []

#guard data.length == 3

private def ds : Dataset := { default := data, named := [] }

private def refRows (q : String) : Option SolutionSeq := do
  let query ← (parseSparql q).toOption
  return (evalSelect emptyEnv ds query).2

private def idxRows (q : String) : Option SolutionSeq := do
  let query ← (parseSparql q).toOption
  StoreDataset.runSelectQueryBackendDataset emptyEnv query (StoreDataset.indexedDatasetBackend ds)

private def pq : String :=
  "PREFIX : <http://example.org/> " ++
  "SELECT * WHERE { ?s :p ?o . ?s :q ?o FILTER(LANG(?o) = \"en\") }"

private def qp : String :=
  "PREFIX : <http://example.org/> " ++
  "SELECT * WHERE { ?s :q ?o . ?s :p ?o FILTER(LANG(?o) = \"en\") }"

private def en : Option Term := some (.literal (Literal.langString "x" "en"))

-- Both pattern orders, both evaluation paths: one row, `?o` = `"x"@en`.
#guard (refRows pq).map (·.map (Binding.lookup "o")) == some [en]
#guard (refRows qp).map (·.map (Binding.lookup "o")) == some [en]
#guard (idxRows pq).map (·.map (Binding.lookup "o")) == some [en]
#guard (idxRows qp).map (·.map (Binding.lookup "o")) == some [en]

-- LANG() returns the canonical tag, whatever the spelling in the data.
private def langOf (q : String) : Option (List (Option Term)) :=
  (refRows q).map (·.map (Binding.lookup "l"))

#guard langOf ("PREFIX : <http://example.org/> " ++
  "SELECT (LANG(?o) AS ?l) WHERE { :a :q ?o }") ==
  some [some (.literal (Literal.string "en"))]
#guard langOf ("SELECT (LANG(\"x\"@EN-gb) AS ?l) WHERE { }") ==
  some [some (.literal (Literal.string "en-gb"))]
#guard langOf ("SELECT (LANG(STRLANG(\"x\", \"EN-GB\")) AS ?l) WHERE { }") ==
  some [some (.literal (Literal.string "en-gb"))]
-- `sameTerm` and `=` see one term (the two spellings are one RDF term).
#guard (refRows ("SELECT * WHERE { FILTER(sameTerm(\"x\"@en, \"x\"@EN)) }")).map (·.length) ==
  some 1

/-! ### Every reader writes the tag in lower case -/

private def tagsOfGraph (g : Graph) : List (Option String) :=
  g.filterMap fun t => match t.o with
    | .literal l => some l.val.langTag
    | _ => none

private def tagsOfDataset (d : Dataset) : List (Option String) :=
  tagsOfGraph (d.default ++ d.named.flatMap (·.graph))

#guard tagsOfGraph data == [some "en", none, some "en"]

#guard ((Syntax.parseNTriples "<http://e/s> <http://e/p> \"x\"@en-US .\n").toOption.map
  tagsOfGraph) == some [some "en-us"]
#guard ((Syntax.parseNTriples "<http://e/s> <http://e/p> \"x\"@en-US--rtl .\n" .rdf12).toOption.map
  tagsOfGraph) == some [some "en-us"]
#guard ((Syntax.parseNQuads "<http://e/s> <http://e/p> \"x\"@EN <http://e/g> .\n").toOption.map
  tagsOfDataset) == some [some "en"]
#guard ((Syntax.parseNQuadsFast "<http://e/s> <http://e/p> \"x\"@EN <http://e/g> .\n").toOption.map
  tagsOfDataset) == some [some "en"]
#guard ((Syntax.parseTurtle "<http://e/s> <http://e/p> \"x\"@En-Latn-US .").toOption.map
  tagsOfGraph) == some [some "en-latn-us"]
#guard ((Syntax.parseTriG "<http://e/g> { <http://e/s> <http://e/p> \"x\"@EN . }").toOption.map
  tagsOfDataset) == some [some "en"]
#guard ((Syntax.RdfXml.parseRdfXml ("<rdf:RDF xmlns:rdf=\"http://www.w3.org/1999/02/22-rdf-syntax-ns#\" " ++
  "xmlns:e=\"http://e/\"><rdf:Description rdf:about=\"http://e/s\" xml:lang=\"EN-gb\">" ++
  "<e:p>x</e:p></rdf:Description></rdf:RDF>")).toOption.map tagsOfGraph) == some [some "en-gb"]
#guard ((Syntax.RdfJson.parseRdfJson ("{\"http://e/s\": {\"http://e/p\": " ++
  "[{\"type\": \"literal\", \"value\": \"x\", \"lang\": \"EN\"}]}}")).toOption.map
  tagsOfGraph) == some [some "en"]
#guard ((JSONLD.parseJsonLd JSONLD.Loader.none
  "[{\"@id\": \"http://e/s\", \"http://e/p\": [{\"@value\": \"x\", \"@language\": \"EN-US\"}]}]"
  none none none none).toOption.map tagsOfDataset) == some [some "en-us"]

private def resultTag (r : Except ResultsError QueryResult) : Option (Option String) :=
  match r with
  | .ok (.bindings _ rows) => match rows with
    | [mu] => match mu.lookup "o" with
      | some (.literal l) => some l.val.langTag
      | _ => none
    | _ => none
  | _ => none

#guard resultTag (parseSrx ("<?xml version=\"1.0\"?><sparql xmlns=\"http://www.w3.org/2005/sparql-results#\">" ++
  "<head><variable name=\"o\"/></head><results><result><binding name=\"o\">" ++
  "<literal xml:lang=\"EN\">x</literal></binding></result></results></sparql>")) ==
  some (some "en")
#guard resultTag (parseSrj ("{\"head\": {\"vars\": [\"o\"]}, \"results\": {\"bindings\": " ++
  "[{\"o\": {\"type\": \"literal\", \"value\": \"x\", \"xml:lang\": \"EN\"}}]}}")) ==
  some (some "en")

/-! ### The constructors -/

#guard (Literal.langString "x" "EN-gb").val.langTag == some "en-gb"
#guard (Literal.dirLangString "x" "AR" .rtl).val.langTag == some "ar"
#guard (mkLangLiteral "x" "EN").val.langTag == some "en"

/-! ### Reader statements

Every term is canonical (`RDF.Term.canonical`), so each reader's output is.
The statements name the readers; the proof is the term-model theorem. -/

theorem parseNTriples_canonical {s : String} {m : Syntax.Mode} {g : Graph}
    (_h : Syntax.parseNTriples s m = .ok g) : ∀ t ∈ g, t.o.Canonical :=
  fun t _ => Term.canonical t.o

theorem parseNQuads_canonical {s : String} {m : Syntax.Mode} {d : Dataset}
    (_h : Syntax.parseNQuads s m = .ok d) :
    (∀ t ∈ d.default, t.o.Canonical) ∧ ∀ ng ∈ d.named, ∀ t ∈ ng.graph, t.o.Canonical :=
  ⟨fun t _ => Term.canonical t.o, fun _ _ t _ => Term.canonical t.o⟩

theorem parseTurtle_canonical {s : String} {b : Option String} {m : Syntax.Mode} {g : Graph}
    (_h : Syntax.parseTurtle s b m = .ok g) : ∀ t ∈ g, t.o.Canonical :=
  fun t _ => Term.canonical t.o

theorem parseTriG_canonical {s : String} {b : Option String} {m : Syntax.Mode} {d : Dataset}
    (_h : Syntax.parseTriG s b m = .ok d) :
    (∀ t ∈ d.default, t.o.Canonical) ∧ ∀ ng ∈ d.named, ∀ t ∈ ng.graph, t.o.Canonical :=
  ⟨fun t _ => Term.canonical t.o, fun _ _ t _ => Term.canonical t.o⟩

#print axioms parseNTriples_canonical
#print axioms parseNQuads_canonical
#print axioms parseTurtle_canonical
#print axioms parseTriG_canonical

end L4Factoidal.SPARQL.LangTagCanonicalTests
