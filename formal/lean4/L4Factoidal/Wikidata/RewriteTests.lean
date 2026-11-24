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

#guard (rewriteQuery "SELECT (SUM(?n) AS ?total) WHERE { ?s ?p ?n }").rewrite_status == "unchanged"

private def aliasExample :=
  "SELECT (SUM(?n) AS ?n) (MAX($n) AS ?peak) WHERE { VALUES ?n { 2 3 } } " ++
  "HAVING (SUM(?n) > 0) ORDER BY DESC(?n)"

private def repairedAliasRows : Option (List String × Binding) := do
  let rewritten ← (rewriteQuery aliasExample).rewritten_query
  let query ← (parseSparql rewritten).toOption
  let (columns, rows) := evalSelect {} { default := [], named := [] } query
  return (columns, ← rows.head?)

private def aliasAggregate (name : String) : Option String := do
  let (_, row) ← repairedAliasRows
  let .literal value ← row.lookup name | none
  return value.val.lexicalForm

#guard (rewriteQuery aliasExample).rewrites.map (·.rule_id) == ["rewrite-legacy-select-alias"]
#guard (repairedAliasRows.map (·.1)) == some ["n", "peak"]
#guard aliasAggregate "n" == some "5"
#guard aliasAggregate "peak" == some "3"
#guard (rewriteQuery "SELECT (SUM(?n) AS ?n) WHERE { { SELECT ?n { VALUES ?n { 1 } } } }").rewrite_status == "parse_error"
#guard (rewriteQuery "SELECT (SAMPLE(?n) AS ?n) WHERE { ?s ?p ?n } }").rewrite_status == "parse_error"

private def exactHintInput :=
  "#title:People\r\nPREFIX unused: <urn:unused:>\r\nSELECT ?s WHERE {\r\n" ++
  "  ?s wdt:P31 wd:Q5 .\r\n  hint:Query hint:optimizer \"None\" .\r\n}\r\n"

private def exactHintOutput :=
  "#title:People\r\nPREFIX wd: <http://www.wikidata.org/entity/>\n" ++
  "PREFIX wdt: <http://www.wikidata.org/prop/direct/>\nSELECT ?s WHERE {\r\n" ++
  "  ?s wdt:P31 wd:Q5 .\r\n}\r\n\n# Original query:\n" ++
  "# #title:People\n# PREFIX unused: <urn:unused:>\n# SELECT ?s WHERE {\n" ++
  "#   ?s wdt:P31 wd:Q5 .\n#   hint:Query hint:optimizer \"None\" .\n# }\n"

#guard (rewriteQuery exactHintInput).rewritten_query == some exactHintOutput

end L4Factoidal.Wikidata
