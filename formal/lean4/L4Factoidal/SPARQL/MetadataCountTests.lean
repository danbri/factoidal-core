import L4Factoidal.SPARQL.MetadataCount
import L4Factoidal.SPARQL.Parser
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.SPARQL.MetadataCountTests

open L4Factoidal.RDF L4Factoidal.SPARQL.MetadataCount

private def graph : Graph :=
  (Syntax.parseTurtle "<urn:a> <urn:p> <urn:a>, <urn:b> . <urn:b> <urn:q> \"text\" .").toOption.getD []
private def source := OWL.RL.Index.ofGraph (graph ++ graph.take 1)
private def ordered := OrderedSubject.prepare source
private def p : WfIri := ⟨"urn:p", rfl⟩
private def absent : WfIri := ⟨"urn:absent", rfl⟩

#guard cardinality? ordered {} == some 4
#guard cardinality? ordered { p := some p } == some 3
#guard cardinality? ordered { p := some absent } == some 0
#guard cardinality? ordered { s := some (.iri p) } == none
#guard cardinality? ordered { o := some (.iri p) } == none

private def agrees (text : String) : Bool :=
  match parseSparql text with
  | .error _ => false
  | .ok query => match countRows? ordered query with
    | none => false
    | some rows => some rows == StoreDataset.runSelectQueryBackendDataset emptyEnv query
        { default := .indexed source, named := [] }

#guard agrees "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:p> ?o }"
#guard agrees "SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }"
#guard agrees "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:absent> ?o }"
#guard agrees "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:p> ?o } OFFSET 1 LIMIT 3"
#guard agrees "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:p> ?o } LIMIT 0"
#guard agrees "SELECT (COUNT(*) AS ?n) WHERE { _:x <urn:p> ?o }"

private def rejected (text : String) : Bool :=
  match parseSparql text with
  | .error _ => false
  | .ok query => (countRows? ordered query).isNone

#guard rejected "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:p> ?s }"
#guard rejected "SELECT (COUNT(DISTINCT *) AS ?n) WHERE { ?s <urn:p> ?o }"
#guard rejected "SELECT (COUNT(?o) AS ?n) WHERE { ?s <urn:p> ?o }"
#guard rejected "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:p> <urn:a> }"
#guard rejected "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:p> ?o FILTER(?s = ?o) }"
#guard rejected "SELECT (COUNT(*) AS ?n) WHERE { GRAPH <urn:g> { ?s <urn:p> ?o } }"
#guard rejected "SELECT (COUNT(*) AS ?n) WHERE {}"
#guard rejected "SELECT ?p (COUNT(*) AS ?n) WHERE { ?s ?p ?o } GROUP BY ?p"

/-- `rejected` with the SPARQL 1.2 grammar: the query parses and the count
    is refused. A triple term in a pattern is matched structurally, and the
    bound of `patternBoundFor` does not express it, so `countRows?` must not
    count it from the indexes (`StoreFastPath.triplePatternFlat`;
    https://github.com/danbri/factoidal/issues/792 item 1). -/
private def rejected12 (text : String) : Bool :=
  match parseSparql text none .v12 with
  | .error _ => false
  | .ok query => (countRows? ordered query).isNone

#guard rejected12 "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:p> <<( ?a <urn:q> ?b )>> }"
#guard rejected12 "SELECT (COUNT(*) AS ?n) WHERE { ?s ?p <<( <urn:a> <urn:q> <urn:b> )>> }"
#guard rejected12 "SELECT (COUNT(*) AS ?n) WHERE { << <urn:a> <urn:q> <urn:b> >> <urn:p> ?o }"
-- the SPARQL 1.2 grammar parses a plain count the same, and it is counted
#guard (match parseSparql "SELECT (COUNT(*) AS ?n) WHERE { ?s <urn:p> ?o }" none .v12 with
  | .ok query => (countRows? ordered query).isSome
  | .error _ => false)

end L4Factoidal.SPARQL.MetadataCountTests
