/-
L4Factoidal.SPARQL.DescribeTests — build-time checks for DESCRIBE
(SPARQL 1.1 Query §16.4): `evalDescribe` over queries parsed from text.

Every `#guard` is evaluated during `lake build`, so a wrong answer is a
BUILD ERROR. The W3C test suites hold no evaluation test for DESCRIBE,
because the specification leaves the description to the query service
(https://www.w3.org/TR/sparql11-query/#describe). These are therefore
unit checks of the description this tree chooses, the Concise Bounded
Description (`RDF/ConciseBoundedDescription.lean`), and of which
resources the clause names. Tracked at
https://github.com/danbri/factoidal/issues/698.

The graph under test, with `:` for `http://example.org/`:

    :alice :name "Alice" ; :address _:a1 ; :knows :bob .
    _:a1   :street "1 High St" ; :geo _:g1 .
    _:g1   :lat "51.5" .
    :bob   :name "Bob" ; :age 30 .
    :carol :name "Carol" .

`:dave` occurs nowhere. The triples of each description are named by
their index in `people`, and a description keeps that order.
-/
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.Query
import L4Factoidal.RDF.ConciseBoundedDescription

namespace L4Factoidal.SPARQL.DescribeTests

open L4Factoidal.RDF

private def iri (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def alice : WfIri := iri "http://example.org/alice"
private def bob   : WfIri := iri "http://example.org/bob"
private def carol : WfIri := iri "http://example.org/carol"
private def pName    : WfIri := iri "http://example.org/name"
private def pAddress : WfIri := iri "http://example.org/address"
private def pKnows   : WfIri := iri "http://example.org/knows"
private def pStreet  : WfIri := iri "http://example.org/street"
private def pGeo     : WfIri := iri "http://example.org/geo"
private def pLat     : WfIri := iri "http://example.org/lat"
private def pAge     : WfIri := iri "http://example.org/age"

private def str (s : String) : Term := .literal (Literal.string s)
private def tr (s : Subject) (p : WfIri) (o : Term) : Triple := { s := s, p := p, o := o }
private def age30 : Term := .literal (mkTypedLiteral "30" L4Factoidal.RDF.xsdInteger)

/-- Only so that `people[i]!` can name a triple in a guard. -/
private instance : Inhabited Triple := ⟨tr (.bnode "none") pName (str "none")⟩

private def people : Graph :=
  [ tr (.iri alice) pName (str "Alice")           -- 0
  , tr (.iri alice) pAddress (.bnode "a1")        -- 1
  , tr (.iri alice) pKnows (.iri bob)             -- 2
  , tr (.bnode "a1") pStreet (str "1 High St")    -- 3
  , tr (.bnode "a1") pGeo (.bnode "g1")           -- 4
  , tr (.bnode "g1") pLat (str "51.5")            -- 5
  , tr (.iri bob) pName (str "Bob")               -- 6
  , tr (.iri bob) pAge age30                      -- 7
  , tr (.iri carol) pName (str "Carol") ]         -- 8

private def aliceDescription : Graph :=
  [people[0]!, people[1]!, people[2]!, people[3]!, people[4]!, people[5]!]
private def bobDescription : Graph := [people[6]!, people[7]!]
private def carolDescription : Graph := [people[8]!]

private def dsPeople : Dataset := { default := people, named := [] }

/-- The description a query text gets over a dataset; `none` when the
text does not parse, so that a parse failure fails the guard that
expects a graph. -/
private def describe (ds : Dataset) (text : String) : Option Graph :=
  match parseSparql text with
  | .ok q    => some (evalDescribe emptyEnv ds q)
  | .error _ => none

private def prefixes : String := "PREFIX : <http://example.org/> "

private def run (text : String) : Option Graph := describe dsPeople (prefixes ++ text)

/-! ### §16.4.1 an IRI in the clause -/

-- The chain of blank nodes is followed to its end (CBD clause 2). The
-- IRI object :bob is not followed, and :carol is unrelated.
#guard run "DESCRIBE :alice" == some aliceDescription
#guard (run "DESCRIBE :alice").map (·.length) == some 6
-- The unrelated subjects are not in the description.
#guard (run "DESCRIBE :alice").map (·.contains (people[6]!)) == some false
#guard (run "DESCRIBE :alice").map (·.contains (people[8]!)) == some false
-- A description that is the whole graph would pass the first guard only
-- if the graph were just alice's; these two fix the other subjects apart.
#guard run "DESCRIBE :bob" == some bobDescription
#guard run "DESCRIBE :carol" == some carolDescription
-- An IRI with no statements has the empty description.
#guard run "DESCRIBE :dave" == some []
-- Two IRIs: the union, in the order of the graph.
#guard run "DESCRIBE :carol :bob" == some (bobDescription ++ carolDescription)
-- The same IRI twice adds nothing.
#guard run "DESCRIBE :alice :alice" == some aliceDescription
-- Starting at the blank node's own label is not possible in the query
-- (a blank node in a DESCRIBE clause is not in the grammar), but a
-- variable can be bound to it:
#guard run "DESCRIBE ?a WHERE { :alice :address ?a }"
  == some [people[3]!, people[4]!, people[5]!]

/-! ### §16.4.2 a variable in the clause -/

-- Two bindings: both resources are described, the third is not.
#guard run "DESCRIBE ?x WHERE { ?x :name ?n FILTER(?n IN (\"Bob\", \"Carol\")) }"
  == some (bobDescription ++ carolDescription)
-- Every binding.
#guard (run "DESCRIBE ?x WHERE { ?x :name ?n }").map (·.length) == some 9
-- LIMIT after ORDER BY: only the first solution's resource.
#guard run "DESCRIBE ?x WHERE { ?x :name ?n } ORDER BY ?n LIMIT 1"
  == some aliceDescription
#guard run "DESCRIBE ?x WHERE { ?x :name ?n } ORDER BY DESC(?n) LIMIT 1"
  == some carolDescription
#guard run "DESCRIBE ?x WHERE { ?x :name ?n } ORDER BY ?n OFFSET 1 LIMIT 1"
  == some bobDescription
-- LIMIT 0 leaves no solution and so no variable binding.
#guard run "DESCRIBE ?x WHERE { ?x :name ?n } LIMIT 0" == some []
-- A literal binding names no resource.
#guard run "DESCRIBE ?n WHERE { :bob :name ?n }" == some []
-- A literal and an IRI together: only the IRI is described.
#guard run "DESCRIBE ?n ?b WHERE { ?b :name ?n FILTER(?n = \"Bob\") }"
  == some bobDescription
-- An unbound variable names nothing.
#guard run "DESCRIBE ?u WHERE { :bob :name ?n OPTIONAL { :bob :unknown ?u } }" == some []
-- A pattern with no solution describes no variable.
#guard run "DESCRIBE ?x WHERE { ?x :name \"Nobody\" }" == some []
-- VALUES supplies the bindings.
#guard run "DESCRIBE ?x WHERE { VALUES ?x { :bob :carol } }"
  == some (bobDescription ++ carolDescription)
-- An IRI of the clause is described whether or not the pattern matches.
#guard run "DESCRIBE :carol WHERE { ?s :unknown ?o }" == some carolDescription
#guard run "DESCRIBE :carol ?x WHERE { ?x :age ?n }"
  == some (bobDescription ++ carolDescription)
-- GROUP BY: after grouping only the group variable is in scope.
#guard run "DESCRIBE ?x WHERE { ?x :name ?n } GROUP BY ?x HAVING (STR(?x) = \"http://example.org/carol\")"
  == some carolDescription
-- ?o is not a GROUP BY variable, so it is unbound in the group and :bob
-- is not described; without GROUP BY both are.
#guard run "DESCRIBE ?x ?o WHERE { ?x :knows ?o } GROUP BY ?x" == some aliceDescription
#guard run "DESCRIBE ?x ?o WHERE { ?x :knows ?o }" == some (aliceDescription ++ bobDescription)

/-! ### DESCRIBE * -/

-- Every variable in scope: ?x and ?y both bound.
#guard run "DESCRIBE * WHERE { ?x :knows ?y }" == some (aliceDescription ++ bobDescription)
-- A blank node of the WHERE clause is not a variable the user wrote, so
-- it is not described; ?s is bound to a literal.
#guard run "DESCRIBE * WHERE { :alice :address [ :street ?s ] }" == some []
-- ... while a named variable bound to the same node is.
#guard run "DESCRIBE * WHERE { :alice :address ?a . ?a :street ?s }"
  == some [people[3]!, people[4]!, people[5]!]

/-! ### The dataset -/

private def gOne : WfIri := iri "http://example.org/g1"

-- The default graph has one statement about :alice; the named graph g1
-- has another and a blank-node chain.
private def dsNamed : Dataset :=
  { default := [tr (.iri alice) pName (str "Alice in the default graph")]
  , named := [ { name := .iri gOne
               , graph := [ tr (.iri alice) pAddress (.bnode "n")
                          , tr (.bnode "n") pStreet (str "in g1") ] } ] }

#guard describe dsNamed (prefixes ++ "DESCRIBE :alice")
  == some [tr (.iri alice) pName (str "Alice in the default graph")]
-- FROM replaces the default graph for the description.
#guard describe dsNamed (prefixes ++ "DESCRIBE :alice FROM <http://example.org/g1>")
  == some [tr (.iri alice) pAddress (.bnode "n"), tr (.bnode "n") pStreet (str "in g1")]
-- FROM NAMED alone leaves an empty default graph.
#guard describe dsNamed (prefixes ++ "DESCRIBE :alice FROM NAMED <http://example.org/g1>")
  == some []
-- A graph named in a GRAPH clause supplies the bindings, but the
-- description still comes from the active default graph.
#guard describe dsNamed
    (prefixes ++ "DESCRIBE ?s WHERE { GRAPH <http://example.org/g1> { ?s :address ?a } }")
  == some [tr (.iri alice) pName (str "Alice in the default graph")]

/-! ### The empty dataset, and the other forms -/

#guard describe Dataset.empty "DESCRIBE <http://example.org/alice>" == some []
#guard describe Dataset.empty "DESCRIBE * WHERE { ?s ?p ?o }" == some []
-- The other query forms describe nothing.
#guard (match parseSparql (prefixes ++ "SELECT * WHERE { ?s ?p ?o }") with
  | .ok q => evalDescribe emptyEnv dsPeople q == []
  | .error _ => false)

/-! ### RDF 1.2 reifiers (CBD clause 3) -/

private def reifies : WfIri := L4Factoidal.RDFS.rdfReifies
private def pSource : WfIri := iri "http://example.org/source"

private def withReifier : Graph :=
  [ tr (.iri alice) pName (str "Alice")                                          -- 0
  , tr (.bnode "r") reifies (.tripleTerm (.iri alice) pName (str "Alice"))       -- 1
  , tr (.bnode "r") pSource (.iri bob)                                           -- 2
  , tr (.iri bob) pName (str "Bob")                                              -- 3
  , tr (.iri carol) pName (str "Carol")                                          -- 4
  , tr (.bnode "q") reifies (.tripleTerm (.iri carol) pName (str "Carol"))       -- 5
  , tr (.bnode "q") pSource (.iri alice) ]                                       -- 6

-- Describing :alice takes the statement that reifies her statement, and
-- what that reifier says; :bob, named by IRI in it, is not followed.
#guard describe { default := withReifier, named := [] } (prefixes ++ "DESCRIBE :alice")
  == some [withReifier[0]!, withReifier[1]!, withReifier[2]!]
-- The reifier of :carol's statement says something about :alice, but that
-- does not make it part of :alice's description.
#guard (describe { default := withReifier, named := [] } (prefixes ++ "DESCRIBE :alice")).map
    (·.contains (withReifier[6]!)) == some false

#print axioms evalDescribe

end L4Factoidal.SPARQL.DescribeTests
