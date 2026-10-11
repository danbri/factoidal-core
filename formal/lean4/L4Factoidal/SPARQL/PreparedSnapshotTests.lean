import L4Factoidal.SPARQL.PreparedSnapshot
import L4Factoidal.SPARQL.Parser
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.SPARQL.PreparedSnapshotTests

open L4Factoidal.RDF L4Factoidal.SPARQL.PreparedSnapshot

private def graph : Graph :=
  (Syntax.parseTurtle "<urn:a> <urn:type> <urn:Person> ; <urn:name> \"Alice\" ; <urn:lang> \"colour\"@en .
    <urn:b> <urn:type> <urn:Person> ; <urn:name> \"Bob\", \"Bób\" ; <urn:member> <urn:team1>, <urn:team2> .").toOption.getD []

private def snapshot := prepare graph

private def answer (text : String) : Option QueryResult := do
  let query ← (parseSparql text).toOption
  (run snapshot query).toOption

private def agrees (text : String) : Bool :=
  match parseSparql text with
  | .error _ => false
  | .ok query =>
      let expected := match query.form with
        | .select _ => let (vars, rows) := evalSelect emptyEnv { default := graph, named := [] } query
                       QueryResult.bindings vars rows
        | .ask => .boolean (evalAsk emptyEnv { default := graph, named := [] } query)
        | _ => .boolean false
      answer text == some expected

#guard graph.length == 8
#guard answer "ASK { ?s <urn:type> <urn:Person> }" == some (.boolean true)
#guard answer "ASK { ?s <urn:type> <urn:Missing> }" == some (.boolean false)
#guard answer "ASK { ?s <urn:lang> \"colour\"@EN }" == some (.boolean true)
#guard agrees "ASK { ?s <urn:member> ?s }"
#guard agrees "ASK { _:x <urn:name> \"Alice\" }"
#guard agrees "ASK { ?s <urn:name> ?name } VALUES ?name { \"missing\" }"
#guard agrees "ASK { ?s <urn:name> ?name } VALUES ?s { \"invalid subject\" }"
#guard answer "SELECT ?name WHERE { ?s <urn:name> ?name } ORDER BY ?name" ==
  some (.bindings ["name"] [[("name", .literal (Literal.string "Alice"))],
    [("name", .literal (Literal.string "Bob"))], [("name", .literal (Literal.string "Bób"))]])
#guard agrees "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:name> ?name }"
#guard agrees "SELECT (COUNT(*) AS ?total) WHERE { ?s ?p ?o }"
#guard agrees "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:missing> ?o }"
#guard agrees "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:name> ?o } OFFSET 1 LIMIT 3"
#guard agrees "SELECT (COUNT(*) AS ?n) WHERE { _:x <urn:name> ?o }"
#guard agrees "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:member> ?s }"
#guard agrees "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:type> <urn:Person> }"
#guard agrees "SELECT (COUNT(*) AS ?n) FROM <urn:unavailable> WHERE { ?s ?p ?o }"
#guard agrees "SELECT ?name ?team WHERE { ?s <urn:type> <urn:Person> ; <urn:name> ?name ; <urn:member> ?team } ORDER BY ?name ?team"
#guard agrees "SELECT ?s ?team WHERE { ?s <urn:type> <urn:Person> OPTIONAL { ?s <urn:member> ?team } } ORDER BY ?s ?team"
#guard agrees "SELECT ?s WHERE { ?s <urn:type> <urn:Person> MINUS { ?s <urn:member> ?team } } ORDER BY ?s"
#guard agrees "SELECT ?s WHERE { ?s <urn:type> <urn:Person> FILTER EXISTS { ?s <urn:name> \"Alice\" } } ORDER BY ?s"
#guard agrees "ASK { ?s <urn:type> <urn:Person> FILTER NOT EXISTS { ?s <urn:member> ?team } }"
#guard agrees "SELECT ?s WHERE { ?s <urn:type> <urn:Person> } VALUES ?s { <urn:a> }"
#guard agrees "SELECT ?s WHERE { { SELECT ?s WHERE { ?s <urn:type> <urn:Person> } } } ORDER BY ?s LIMIT 1"
#guard agrees "SELECT ?name WHERE { ?s <urn:name> ?name } ORDER BY DESC(?s) ?name OFFSET 1 LIMIT 1"
#guard agrees "SELECT DISTINCT ?s WHERE { ?s <urn:name> ?name } ORDER BY ?s OFFSET 1 LIMIT 1"
#guard agrees "SELECT REDUCED ?s WHERE { ?s <urn:name> ?name } ORDER BY ?s OFFSET 1 LIMIT 1"
#guard agrees "SELECT ?s (COUNT(*) AS ?n) WHERE { ?s <urn:name> ?name } GROUP BY ?s HAVING(COUNT(*) > 0) ORDER BY DESC(?n) OFFSET 1 LIMIT 1"
#guard agrees "SELECT (BNODE() AS ?made) ?name WHERE { ?s <urn:name> ?name } ORDER BY DESC(?name) OFFSET 1 LIMIT 1"
#guard answer "ASK FROM <urn:unavailable> { ?s ?p ?o }" == some (.boolean false)
#guard agrees "SELECT ?s FROM <urn:unavailable> WHERE { ?s ?p ?o }"
#guard agrees "SELECT (COUNT(*) AS ?n) FROM NAMED <urn:unavailable> WHERE { ?s ?p ?o }"
#guard answer "CONSTRUCT { ?s ?p ?o } WHERE { ?s ?p ?o }" == none
#guard answer "DESCRIBE <urn:a>" == none
#guard answer "SELECT ?s WHERE { ?s <urn:type> <urn:Person> } LIMIT 0" ==
  some (.bindings ["s"] [])
#guard answer "SELECT * WHERE { ?s ?p ?o } OFFSET 100 LIMIT 0" ==
  some (.bindings ["s", "p", "o"] [])
#guard answer "SELECT (COUNT(*) AS ?n) FROM <urn:unavailable> WHERE { ?s ?p ?o } LIMIT 0" ==
  some (.bindings ["n"] [])
#guard answer "BASE <http://example.org/base/> SELECT (IRI(\"child\") AS ?iri) WHERE {}" ==
  some (.bindings ["iri"] [[("iri", .iri ⟨"http://example.org/base/child", rfl⟩)]])

#guard match parseSparql "ASK { FILTER(NOW() = NOW()) }" with
  | .ok query => run snapshot query { now := some "2026-10-11T12:00:00Z" } ==
      .ok (.boolean true)
  | _ => false

end L4Factoidal.SPARQL.PreparedSnapshotTests
