/-
L4Factoidal.RML.SparqlSource — a SPARQL SELECT query over an RDF file as a
logical source.

Spec: RML-IO (https://w3id.org/rml/io/spec), "Reference formulations":
`formats:SPARQL_Results_CSV`. The source is an RDF file, the iterator is a
SPARQL SELECT query, each solution of the query is one logical iteration,
and a reference expression names a variable. The values are the strings the
CSV serialisation of results (SPARQL 1.1 Query Results CSV and TSV Formats)
writes, so a literal's datatype is not part of the value.

This module is the SPARQL engine a host hands to `RML.Open` through
`FileAccess.sparql`. It is a module of its own, and `RML.Open` does not import
it, so that the SPARQL parser is not part of the import closure of every
module that reads RML sources.
-/
import L4Factoidal.RML.Open
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Parser
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.NQuads
-- `parseNQuads_eq_fast` (@[csimp]): the calls of `parseNQuads` here run `parseNQuadsFast`
-- (https://github.com/danbri/factoidal/issues/868; `tools/lean-csimp-reach.py`, not-imported).
import L4Factoidal.Syntax.NQuadsFastTheorems

namespace L4Factoidal.RML

/-- The text a SPARQL solution gives a variable in the CSV serialisation of
    results (SPARQL 1.1 Query Results CSV and TSV Formats, 3): an IRI as it
    is, a literal by its lexical form, a blank node as `_:label`. -/
def solutionText : L4Factoidal.RDF.Term → String
  | .iri i => i.val
  | .bnode b => "_:" ++ b
  | .literal l => l.val.lexicalForm
  | .tripleTerm .. => "<<triple term>>"

/-- The rows of a SPARQL SELECT query over an RDF file
    (`formats:SPARQL_Results_CSV`, RML-IO "Reference formulations"): the
    file is read as RDF in the syntax its name gives, the query is the
    iterator, each solution is one iteration, and a variable is a column.
    A variable a solution leaves unbound has no cell. -/
def sparqlRecords (path text query : String) : Except String (List Record) :=
  let ds : Except String L4Factoidal.RDF.Dataset :=
    if path.endsWith ".nq" then
      (L4Factoidal.Syntax.parseNQuads text).mapError (·.msg)
    else if path.endsWith ".nt" || path.endsWith ".ttl" then
      ((L4Factoidal.Syntax.parseTurtle text none).mapError (·.msg)).map
        (fun g => { default := g, named := [] })
    else .error s!"'{path}' has no file name extension of an RDF syntax this port reads (.nt, .ttl, .nq)"
  match ds with
  | .error m => .error s!"the RDF file cannot be read: {m}"
  | .ok data =>
      match L4Factoidal.SPARQL.parseSparql query with
      | .error e => .error s!"the iterator is not a SPARQL query: {e.msg}"
      | .ok q =>
          match q.form with
          | .select _ =>
              let (vars, rows) := L4Factoidal.SPARQL.evalSelect { dataset := some data } data q
              .ok (rows.map (fun mu =>
                Record.ofColumns vars (vars.filterMap (fun v =>
                  (mu.lookup v).map (fun t => (v, solutionText t))))))
          | _ => .error "the iterator is a SPARQL query that is not a SELECT query"

/-- A file access with the SPARQL engine of this module. -/
def FileAccess.withSparql (fa : FileAccess) : FileAccess :=
  { fa with sparql := some sparqlRecords }

/-! ## Build-time checks -/

private def files (entries : List (String × String)) : FileAccess :=
  FileAccess.withSparql { read := fun _ p => (entries.find? (fun e => e.1 == p)).map (fun e => e.2.toUTF8) }

-- A SPARQL SELECT over an RDF file: one iteration per solution, one column
-- per variable; an unbound variable has no cell.
private def friendsNt : String :=
  "<http://example.org/0> <http://xmlns.com/foaf/0.1/name> \"Monica\" .\n" ++
  "<http://example.org/0> <http://xmlns.com/foaf/0.1/age> \"33\" .\n" ++
  "<http://example.org/1> <http://xmlns.com/foaf/0.1/name> \"Rachel\" .\n"

private def sparqlLs (q : String) : LogicalSource :=
  { path := "Friends.nt", iterator := some q, refFormulation := sparqlResultsCsvIri }

private def selectAll : String :=
  "PREFIX foaf: <http://xmlns.com/foaf/0.1/> SELECT ?p ?n ?a WHERE { ?p foaf:name ?n . OPTIONAL { ?p foaf:age ?a } } ORDER BY ?p"

#guard match openRecords (sparqlLs selectAll) (files [("Friends.nt", friendsNt)]) with
       | .ok [r0, r1] =>
           (r0.values "p").1 == [{ lexical := "http://example.org/0" }] &&
           (r0.values "n").1 == [{ lexical := "Monica" }] &&
           (r0.values "a").1 == [{ lexical := "33" }] &&
           (r1.values "n").1 == [{ lexical := "Rachel" }] &&
           (r1.values "a").1.isEmpty && (r1.values "a").2.isEmpty
       | _ => false
-- a variable the query does not name is not a column
#guard match openRecords (sparqlLs selectAll) (files [("Friends.nt", friendsNt)]) with
       | .ok (r :: _) => (r.values "z").2.length == 1
       | _ => false
-- a query that selects nothing gives no iteration
#guard match openRecords (sparqlLs "SELECT ?s WHERE { ?s <http://example.org/none> ?o }")
         (files [("Friends.nt", friendsNt)]) with
       | .ok rs => rs.isEmpty | .error _ => false
-- a query that does not parse, a query that is not a SELECT, a file in a
-- syntax this reader does not have, and no query at all are source errors
#guard match openRecords (sparqlLs "SELECT WHERE") (files [("Friends.nt", friendsNt)]) with
       | .error e => e.kind == .source | .ok _ => false
#guard match openRecords (sparqlLs "ASK { ?s ?p ?o }") (files [("Friends.nt", friendsNt)]) with
       | .error e => e.kind == .source | .ok _ => false
#guard match openRecords { sparqlLs selectAll with path := "Friends.csv" }
         (files [("Friends.csv", friendsNt)]) with
       | .error e => e.kind == .source | .ok _ => false
#guard match openRecords { sparqlLs selectAll with iterator := none }
         (files [("Friends.nt", friendsNt)]) with
       | .error e => e.kind == .source | .ok _ => false
#guard match openRecords (sparqlLs selectAll) (files [("Friends.nt", "not rdf")]) with
       | .error e => e.kind == .source | .ok _ => false

end L4Factoidal.RML
