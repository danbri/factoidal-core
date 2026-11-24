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

-- ARQ retains FILTER placement and prints a path alternative as a path.
-- This also exercises blank node labels, the shorthand VALUES form and ASC.
private def layoutInput :=
  "PREFIX ex: <urn:ex:>\nSELECT ?s WHERE { VALUES ?s { ex:s }\n" ++
  "?s (ex:a|ex:b) ?o . FILTER(BOUND(?o)) OPTIONAL { ?s ex:c [] } } ORDER BY ASC(?s)"

private def layoutExpected :=
  "PREFIX  ex:   <urn:ex:>\n\nSELECT  ?s\nWHERE\n  { VALUES ?s { ex:s }\n" ++
  "    ?s ex:a|ex:b ?o\n    FILTER bound(?o)\n    OPTIONAL\n      { ?s  ex:c  _:b0 }\n  }\nORDER BY ASC(?s)\n"

#guard formatParsedRewrite layoutInput == some layoutExpected
#guard (rewriteQuery "ASK { ?item wdt:P31 wd:Q5 . SERVICE wikibase:label { bd:serviceParam wikibase:language \"en\" } }").rewrite_status == "rewritten"

private def sliceRangeInput :=
  "SELECT (COUNT(*) AS ?total) WHERE { SERVICE bd:slice { " ++
  "?item wdt:P31 wd:Q5 . bd:serviceParam bd:slice.range ?count . } }"

#guard (rewriteQuery sliceRangeInput).rewrites.map (·.variant_id) == ["range-count"]
#guard (rewriteQuery sliceRangeInput).rewritten_query.any fun text =>
  let rewritten := ((text.splitOn "\n# Original query:").headD "")
  (rewritten.splitOn "(COUNT(*) AS ?total)").length == 2 &&
  (rewritten.splitOn "(count(*) AS ?count)").length == 2
#guard (rewriteQuery "ASK { SERVICE bd:slice { { ?item wdt:P31 wd:Q5 } } }").rewrite_status ==
  "skipped_unsupported"

private def distanceExample :=
  "SELECT ?d WHERE { BIND(geof:distance(?a, CONCAT(\"x\", \"y\"), \"meter\") AS ?d) }"
private def distanceOutput :=
  "PREFIX  geof: <http://www.opengis.net/def/function/geosparql/>\n\nSELECT  ?d\nWHERE\n" ++
  "  { BIND(geof:distance(?a, concat(\"x\", \"y\")) AS ?d) }\n"
#guard (rewriteQuery distanceExample).rewritten_query == some (appendOriginalQuery distanceOutput distanceExample)
#guard (rewriteQuery "ASK { FILTER(geof:distance(?point)) }").rewrite_status == "blazegraph_error"

private def laterBinder :=
  "SELECT ?item ?itemLabel WHERE { SERVICE wikibase:label { bd:serviceParam wikibase:language \"en\" } " ++
  "?item wdt:P31 wd:Q5 }"
private def labelAfterBinding : Bool :=
  match (rewriteQuery laterBinder).rewritten_query with
  | some output => (output.splitOn "?item  wdt:P31  wd:Q5\n    BIND(if(bound(?item)").length == 2
  | none => false
#guard labelAfterBinding

-- Compare the complete source-preserving output with the pinned Java oracle.
private def namedInput :=
  "SELECT ?s WITH { SELECT ?s WHERE { ?s wdt:P31 wd:Q5 } LIMIT 1 } AS %rows WHERE { INCLUDE %rows . }"

private def namedOutput :=
  "PREFIX wd: <http://www.wikidata.org/entity/>\nPREFIX wdt: <http://www.wikidata.org/prop/direct/>\n" ++
  "WITH %rows AS {\n?s wdt:P31 wd:Q5\n}\nSELECT ?s  WHERE { { SELECT ?s WHERE { INCLUDE %rows } LIMIT 1 }\n }"

#guard (rewriteQuery namedInput).rewritten_query == some (appendOriginalQuery namedOutput namedInput)
#guard (rewriteQuery "ASK { BIND(\"INCLUDE %fake\" AS ?text) }").rewrite_status == "unchanged"
#guard ((rewriteQuery "SELECT ?s WHERE { INCLUDE %missing }").errors.map (·.code)) ==
  ["named_subquery_undefined_reference"]

private def nestedLabelInput :=
  "SELECT ?sLabel WHERE { { SELECT ?sLabel WHERE { ?s wdt:P31 wd:Q5 . " ++
  "SERVICE wikibase:label { bd:serviceParam wikibase:language \"en\". } } } }"

#guard (rewriteQuery nestedLabelInput).rewrites.map (·.variant_id) == ["automatic"]
#guard (rewriteQuery nestedLabelInput).rewritten_query.any fun text =>
  (text.splitOn "?s  rdfs:label  ?s__label_value").length == 3

end L4Factoidal.Wikidata
