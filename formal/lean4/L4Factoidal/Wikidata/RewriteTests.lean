import L4Factoidal.Wikidata.Rewrite
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.Wikidata
open L4Factoidal.SPARQL L4Factoidal.RDF L4Factoidal.Syntax

private def original : String :=
  "SELECT ?item ?itemLabel WHERE {\n" ++
  "  ?item <urn:class> <urn:test> .\n" ++
  "  SERVICE wikibase:label { bd:serviceParam wikibase:language \"[AUTO_LANGUAGE],en\". }\n" ++
  "}"

private def fixture : String :=
  "@prefix wd: <http://www.wikidata.org/entity/> .\n" ++
  "@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .\n" ++
  "wd:Q1 <urn:class> <urn:test> ; rdfs:label \"English\"@en, \"British\"@en-gb .\n" ++
  "wd:Q2 <urn:class> <urn:test> .\n"

private def labels (language : String) : Option (List String) := do
  let text ← (rewriteQuery original language).rewritten_query
  let query ← (parseSparql text).toOption
  let graph ← (parseTurtle fixture).toOption
  let (_, rows) := evalSelect {} { default := graph, named := [] } query
  pure (rows.filterMap fun row => (row.lookup "itemLabel").bind fun value =>
    match value with
    | .literal literal => some literal.val.lexicalForm
    | _ => none)

#guard ((labels "").map (·.mergeSort (· ≤ ·))) == some ["English", "Q2"]
#guard ((labels "en_GB.UTF-8").map (·.mergeSort (· ≤ ·))) == some ["British", "Q2"]

private def hintExample : String :=
  "SELECT ?s WHERE { ?s wdt:P31 wd:Q5 . hint:Query hint:optimizer \"None\" . }"
#guard (rewriteQuery hintExample).rewrite_status == "rewritten"
#guard (rewriteQuery "ASK { FILTER(wikibase:isSomeValue()) }").rewrite_status == "blazegraph_error"
#guard (rewriteQuery "SELECT * WHERE { SERVICE wdsubgraph:scholarly_articles { ?s ?p ?o } }").rewrite_status == "rewritten"
#guard (rewriteQuery "PREFIX wikibase: <urn:user:> ASK { FILTER(wikibase:isSomeValue(?v)) }").rewrite_status == "unchanged"
#guard (rewriteQuery "ASK { FILTER(wikibase:isSomeValue(?v, wd:Q42)) }").rewrite_status == "rewritten"
#guard (rewriteQuery "ASK { SERVICE wikibase:mwapi { ?s ?p ?o } }").rewrite_status == "skipped_unsupported"

end L4Factoidal.Wikidata
