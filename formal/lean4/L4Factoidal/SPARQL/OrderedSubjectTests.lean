import L4Factoidal.SPARQL.OrderedSubject
import L4Factoidal.SPARQL.Parser
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.SPARQL.OrderedSubjectTests

open L4Factoidal.RDF L4Factoidal.SPARQL.OrderedSubject

private def graph : Graph :=
  (Syntax.parseTurtle "<urn:b> <urn:p> \"one\", \"two\" .
    <urn:a> <urn:p> \"three\" . _:blank <urn:p> \"four\" .
    <urn:a> <urn:q> \"other\" .").toOption.getD []
private def index := OWL.RL.Index.ofGraph (graph ++ graph.take 1)
private def ordered := prepare index

private def agrees (text : String) : Bool :=
  match parseSparql text with
  | .error _ => false
  | .ok query => match detect query with
    | none => false
    | some plan =>
        some (execute ordered plan) ==
          StoreDataset.runSelectQueryBackendDataset emptyEnv query { default := .indexed index, named := [] }

#guard agrees "SELECT ?s ?o WHERE { ?s <urn:p> ?o } ORDER BY ?s OFFSET 1 LIMIT 3"
#guard agrees "SELECT * WHERE { ?s <urn:p> ?o } ORDER BY DESC(?s) LIMIT 10"
#guard agrees "SELECT ?o WHERE { ?s <urn:p> ?o } ORDER BY ?s OFFSET 2 LIMIT 1"
#guard agrees "SELECT ?s WHERE { ?s <urn:missing> ?o } ORDER BY ?s LIMIT 1"
#guard agrees "SELECT ?s WHERE { ?s <urn:p> ?o } ORDER BY ?s OFFSET 100 LIMIT 1"
#guard agrees "SELECT ?s WHERE { ?s <urn:p> ?o } ORDER BY ?s LIMIT 0"
#guard agrees "SELECT ?notBound WHERE { ?s <urn:p> ?o } ORDER BY ?s LIMIT 2"

private def rejected (text : String) : Bool :=
  match parseSparql text with
  | .error _ => false
  | .ok query => (detect query).isNone

#guard rejected "SELECT ?s WHERE { ?s <urn:p> ?s } ORDER BY ?s LIMIT 1"
#guard rejected "SELECT DISTINCT ?s WHERE { ?s <urn:p> ?o } ORDER BY ?s LIMIT 1"
#guard rejected "SELECT REDUCED ?s WHERE { ?s <urn:p> ?o } ORDER BY ?s LIMIT 1"
#guard rejected "SELECT (BNODE() AS ?fresh) WHERE { ?s <urn:p> ?o } ORDER BY ?s LIMIT 1"
#guard rejected "SELECT ?s WHERE { ?s <urn:p> ?o } ORDER BY ?s ?o LIMIT 1"
#guard rejected "SELECT ?s WHERE { ?s <urn:p> ?o } ORDER BY ?o LIMIT 1"
#guard rejected "SELECT ?s WHERE { ?s <urn:p> \"one\" } ORDER BY ?s LIMIT 1"
#guard rejected "SELECT ?s WHERE { ?s ?p ?o } ORDER BY ?s LIMIT 1"
#guard rejected "SELECT ?s WHERE { ?s <urn:p> ?o } ORDER BY ?s"
#guard rejected "SELECT ?s FROM <urn:other> WHERE { ?s <urn:p> ?o } ORDER BY ?s LIMIT 1"
#guard rejected "SELECT ?s WHERE { ?s <urn:p> ?o FILTER(?o = \"one\") } ORDER BY ?s LIMIT 1"
#guard rejected "SELECT ?s WHERE { ?s <urn:p> ?o } ORDER BY ?s LIMIT 1 VALUES ?o { \"one\" }"

#guard [false, true].all fun descending =>
  ([none, some 0, some 1, some 3, some 100] : List (Option Nat)).all fun offset =>
    [0, 1, 3, 100].all fun limit =>
      ([.all, .vars [.var "o"], .vars [.var "s", .var "absent"]] : List SelectClause).all fun selection =>
        let query := mkQuery (.select selection)
          (.bgp [⟨.var "s", .iri ⟨"urn:p", rfl⟩, .var "o"⟩])
          (modifier := { orderBy := some [if descending then .desc (.var "s") else .asc (.var "s")],
                         offset := offset, limit := some limit })
        match detect query with
        | none => false
        | some plan => some (execute ordered plan) ==
            StoreDataset.runSelectQueryBackendDataset emptyEnv query { default := .indexed index, named := [] }

end L4Factoidal.SPARQL.OrderedSubjectTests
