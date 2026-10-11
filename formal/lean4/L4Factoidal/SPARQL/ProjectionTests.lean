import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.SPARQL.ProjectionTests

open L4Factoidal.RDF

-- SELECT * header order is unspecified; membership and uniqueness are not.
private def header (text : String) : Option (List VarName) := do
  let query ← (parseSparql text).toOption
  return (evalSelect emptyEnv Dataset.empty query).1

private def names (text : String) (expected : List VarName) : Bool :=
  match header text with
  | none => false
  | some actual => actual.length == expected.length && expected.all actual.contains

#guard names "SELECT * WHERE { ?s ?p ?o } LIMIT 0" ["s", "p", "o"]
#guard names "SELECT * WHERE { ?s <urn:absent> ?o }" ["s", "o"]
#guard names "SELECT * WHERE { ?s <urn:p> ?s }" ["s"]
#guard names "SELECT * WHERE { ?s <urn:p> ?o OPTIONAL { ?s <urn:q> ?never } }" ["s", "o", "never"]
#guard names "SELECT * WHERE { ?s <urn:p> ?o MINUS { ?s <urn:q> ?hidden } }" ["s", "o"]
#guard names "SELECT * WHERE { ?s <urn:p> ?o FILTER(?hidden) }" ["s", "o"]
#guard names "SELECT * WHERE { ?s <urn:p> ?o FILTER EXISTS { ?s <urn:q> ?hidden } }" ["s", "o"]
#guard names "SELECT * WHERE { BIND(?outside AS ?made) }" ["made"]
#guard names "SELECT * WHERE { VALUES (?x ?y) { (UNDEF UNDEF) } }" ["x", "y"]
#guard names "SELECT * WHERE {} VALUES (?x ?y) { (UNDEF UNDEF) }" ["x", "y"]
#guard names "SELECT * WHERE {} VALUES (?x ?y) {}" ["x", "y"]
#guard names "SELECT * WHERE { GRAPH ?graph { ?s <urn:p> ?o } }" ["graph", "s", "o"]
#guard names "SELECT * WHERE { SERVICE SILENT ?endpoint { ?s <urn:p> ?o } }" ["endpoint", "s", "o"]
#guard names "SELECT * WHERE { ?s <urn:p>/<urn:q> ?o }" ["s", "o"]
#guard names "SELECT * WHERE { _:queryBlank <urn:p> ?o }" ["o"]
#guard names "SELECT * WHERE { { SELECT ?shown (?bad AS ?alias) WHERE { ?hidden ?p ?shown } } }" ["shown", "alias"]
#guard names "SELECT * WHERE { { SELECT * WHERE { ?s <urn:p> ?o } LIMIT 0 } }" ["s", "o"]
#guard names "SELECT * WHERE { { ?s <urn:p> ?a } UNION { ?s <urn:q> ?b } }" ["s", "a", "b"]
#guard header "SELECT ?z ?x WHERE { ?x <urn:p> ?z } LIMIT 0" == some ["z", "x"]
#guard names "SELECT * WHERE {}" []

end L4Factoidal.SPARQL.ProjectionTests
