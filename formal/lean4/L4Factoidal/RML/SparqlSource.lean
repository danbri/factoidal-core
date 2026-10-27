/-
L4Factoidal.RML.SparqlSource — a SPARQL SELECT query over an RDF file as a
logical source.

Spec: RML-IO (https://w3id.org/rml/io/spec), "Reference formulations":
`formats:SPARQL_Results_CSV`. The source is an RDF file, the iterator is a
SPARQL SELECT query, each solution of the query is one logical iteration,
and a reference expression names a variable. The lexical form of a value is
the string the CSV serialisation of results (SPARQL 1.1 Query Results CSV and
TSV Formats) writes. A literal's datatype is the value's natural datatype
(`RVal.natural`), as a JSON number's is: a reference to `"5"^^xsd:integer`
gives `"5"^^xsd:integer` when the term map states no datatype
(https://github.com/danbri/factoidal/issues/1034). A language tag is not
kept, because `RVal` has no field for it.

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

/-- The source value of a term in a SPARQL solution: the text of
    `solutionText`, and for a literal its datatype as the natural datatype.
    A simple literal (`xsd:string`) and a language-tagged literal have no
    natural datatype, as in `constantRVal`
    (https://github.com/danbri/factoidal/issues/1034). -/
def solutionValue (t : L4Factoidal.RDF.Term) : RVal :=
  match t with
  | .literal l =>
      { lexical := l.val.lexicalForm
        natural := if l.val.langTag.isSome || l.val.datatype.val == xsdNs ++ "string"
                   then none else some l.val.datatype.val }
  | _ => { lexical := solutionText t }

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
                Record.table (vars.filterMap (fun v =>
                  (mu.lookup v).map (fun t => (v, solutionValue t)))) vars))
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
-- a typed literal keeps its datatype as the natural datatype; a simple
-- literal, a language-tagged literal and an IRI have none
-- (https://github.com/danbri/factoidal/issues/1034)
private def typedNt : String :=
  "<http://example.org/0> <http://example.org/n> \"5\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n" ++
  "<http://example.org/0> <http://example.org/d> \"2026-10-26\"^^<http://www.w3.org/2001/XMLSchema#date> .\n" ++
  "<http://example.org/0> <http://example.org/s> \"x\" .\n" ++
  "<http://example.org/0> <http://example.org/l> \"chat\"@fr .\n"
#guard match openRecords { sparqlLs "SELECT ?s ?n ?d ?x ?l WHERE { ?s <http://example.org/n> ?n ; <http://example.org/d> ?d ; <http://example.org/s> ?x ; <http://example.org/l> ?l }" with path := "Typed.nt" }
         (files [("Typed.nt", typedNt)]) with
       | .ok [r] =>
           (r.values "n").1 == [{ lexical := "5", natural := some (xsdNs ++ "integer") }] &&
           (r.values "d").1 == [{ lexical := "2026-10-26", natural := some (xsdNs ++ "date") }] &&
           (r.values "x").1 == [{ lexical := "x" }] &&
           (r.values "l").1 == [{ lexical := "chat" }] &&
           (r.values "s").1 == [{ lexical := "http://example.org/0" }]
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
