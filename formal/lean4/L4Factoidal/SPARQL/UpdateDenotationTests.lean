/-
L4Factoidal.SPARQL.UpdateDenotationTests — build-time checks of the SPARQL 1.1
Update effects that `SPARQL/UpdateDenotation.lean` states on the dataset
denotation (https://github.com/danbri/factoidal/issues/975, phase D).

Each check parses a request, applies it, and reads the result through the Bool
view of the denotation (`Dataset.memQuadB` for triples, `Dataset.names` for
graph names). Graph existence is separate from triples:

* `CLEAR GRAPH` keeps the name (an empty named graph stays);
* `DROP GRAPH` removes the name;
* `CREATE GRAPH` adds the name with no triple;
* `DELETE DATA` of the last triple of a named graph keeps the name;
* `INSERT DATA` into a graph that the store does not hold adds the name;
* `DELETE DATA` from a graph that the store does not hold adds no name;
* `DELETE ... INSERT ... WHERE` deletes first, then inserts (§3.1.3): a quad in
  both templates is in the result;
* `CLEAR DEFAULT` and `DROP DEFAULT` both empty the default graph and keep the
  named graphs.

The input dataset is a value: the checks also read it after the run and find
it unchanged.

No executable imports this module.
-/
import L4Factoidal.RDF.DatasetDenotation
import L4Factoidal.SPARQL.UpdateParser

namespace L4Factoidal.SPARQL.UpdateDenotationTests

open L4Factoidal.RDF L4Factoidal.SPARQL

private def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def exS : WfIri := iri! "http://example.org/s"
private def exP : WfIri := iri! "http://example.org/p"
private def exO : WfIri := iri! "http://example.org/o"
private def exO2 : WfIri := iri! "http://example.org/o2"
private def g1 : WfIri := iri! "http://example.org/g1"
private def g2 : WfIri := iri! "http://example.org/g2"

private def tSPO : Triple := { s := .iri exS, p := exP, o := .iri exO }
private def tSPO2 : Triple := { s := .iri exS, p := exP, o := .iri exO2 }

private def ds0 : Dataset :=
  { default := [tSPO2], named := [{ name := .iri g1, graph := [tSPO] }] }

private def run? (ds : Dataset) (text : String) : Option Dataset :=
  match parseSparqlUpdate text with
  | .ok u => (applyUpdate ds u).toOption
  | .error _ => none

private def hasName (ds : Dataset) (g : WfIri) : Bool := ds.names.contains (.iri g)
private def holds (ds : Dataset) (gn : Option WfIri) (t : Triple) : Bool :=
  ds.memQuadB t (gn.map Subject.iri)

-- the input is a set, so `applyUpdateIn_den` applies to it
#guard ds0.IsSetB

-- CLEAR GRAPH keeps the name, removes the triples
#guard match run? ds0 "CLEAR GRAPH <http://example.org/g1>" with
  | some ds => hasName ds g1 && !holds ds (some g1) tSPO && holds ds none tSPO2
  | none => false
-- DROP GRAPH removes the name
#guard match run? ds0 "DROP GRAPH <http://example.org/g1>" with
  | some ds => !hasName ds g1 && !holds ds (some g1) tSPO && holds ds none tSPO2
  | none => false
-- CREATE GRAPH adds the name and no triple
#guard match run? ds0 "CREATE GRAPH <http://example.org/g2>" with
  | some ds => hasName ds g2 && !holds ds (some g2) tSPO && hasName ds g1
  | none => false
-- CREATE then DROP: the name goes again
#guard match run? ds0 "CREATE GRAPH <http://example.org/g2> ; DROP GRAPH <http://example.org/g2>" with
  | some ds => !hasName ds g2
  | none => false
-- DELETE DATA of the last triple of g1 keeps the empty named graph
#guard match run? ds0 "DELETE DATA { GRAPH <http://example.org/g1> { <http://example.org/s> <http://example.org/p> <http://example.org/o> } }" with
  | some ds => hasName ds g1 && !holds ds (some g1) tSPO
  | none => false
-- INSERT DATA into a graph the store does not hold adds the name
#guard match run? ds0 "INSERT DATA { GRAPH <http://example.org/g2> { <http://example.org/s> <http://example.org/p> <http://example.org/o> } }" with
  | some ds => hasName ds g2 && holds ds (some g2) tSPO
  | none => false
-- DELETE DATA from a graph the store does not hold adds no name
#guard match run? ds0 "DELETE DATA { GRAPH <http://example.org/g2> { <http://example.org/s> <http://example.org/p> <http://example.org/o> } }" with
  | some ds => !hasName ds g2 && ds == ds0
  | none => false
-- DELETE/INSERT WHERE: delete first, then insert; a quad in both templates stays
#guard match run? ds0 "DELETE { ?s ?p ?o } INSERT { ?s ?p ?o } WHERE { ?s ?p ?o }" with
  | some ds => holds ds none tSPO2
  | none => false
-- DELETE/INSERT WHERE moves a triple from the default graph to g2
#guard match run? ds0 "DELETE { ?s ?p ?o } INSERT { GRAPH <http://example.org/g2> { ?s ?p ?o } } WHERE { ?s ?p ?o }" with
  | some ds => !holds ds none tSPO2 && holds ds (some g2) tSPO2 && holds ds (some g1) tSPO
  | none => false
-- CLEAR DEFAULT and DROP DEFAULT both empty the default graph and keep g1
#guard match run? ds0 "CLEAR DEFAULT", run? ds0 "DROP DEFAULT" with
  | some a, some b => a == b && !holds a none tSPO2 && hasName a g1 && holds a (some g1) tSPO
  | _, _ => false
-- CLEAR ALL keeps every name; DROP ALL removes every name
#guard match run? ds0 "CLEAR ALL", run? ds0 "DROP ALL" with
  | some a, some b => hasName a g1 && !holds a (some g1) tSPO && !hasName b g1
  | _, _ => false
-- the input value is unchanged after a run
#guard (run? ds0 "DROP ALL").isSome && ds0.names == [.iri g1] && ds0.default == [tSPO2]

end L4Factoidal.SPARQL.UpdateDenotationTests
