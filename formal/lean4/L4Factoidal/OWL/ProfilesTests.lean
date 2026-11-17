/-
L4Factoidal.OWL.ProfilesTests — the profile checkers and the reverse
mapping on small ontologies.

Each ontology is written in the functional-style syntax and read twice:
as parsed (`FS.parseOntology`), and through its RDF graph
(`FS.parseFunctionalSyntax`, then `Struct.FromRdf.ontologyOfGraph`). The
guards state the three verdicts (EL, QL, RL) and that the two readings
give the same verdicts and the same axiom kinds.
-/
import L4Factoidal.OWL.Profiles
import L4Factoidal.OWL.StructureFromRdf
import L4Factoidal.OWL.FunctionalSyntax

namespace L4Factoidal.OWL.ProfilesTests

open L4Factoidal.OWL.Struct
open L4Factoidal.OWL.Profiles

def verdicts (o : Ontology) : List Bool := [inEL o, inQL o, inRL o]

def wrap (body : String) : String :=
  "Prefix(:=<http://example.org/>)\n\
   Prefix(owl:=<http://www.w3.org/2002/07/owl#>)\n\
   Prefix(xsd:=<http://www.w3.org/2001/XMLSchema#>)\n\
   Ontology(<http://example.org/o>\n\
   Declaration(Class(:A)) Declaration(Class(:B)) Declaration(Class(:C))\n\
   Declaration(ObjectProperty(:p)) Declaration(ObjectProperty(:q)) Declaration(ObjectProperty(:r))\n\
   Declaration(DataProperty(:d)) Declaration(NamedIndividual(:a)) Declaration(NamedIndividual(:b))\n"
    ++ body ++ "\n)"

/-- The verdicts of the functional-style document as parsed. -/
def direct (body : String) : Option (List Bool) :=
  (FS.parseOntology (wrap body)).map verdicts

/-- The verdicts through the RDF graph and the reverse mapping. -/
def viaRdf (body : String) : Option (List Bool) :=
  match FS.parseFunctionalSyntax (wrap body) with
  | none => none
  | some g =>
      match FromRdf.ontologyOfGraph g with
      | .ok o => some (verdicts o)
      | .error _ => none

def sortedNames (o : Ontology) : List String :=
  ((o.axioms.map axiomName).filter (· != "AnnotationAssertion")).mergeSort (fun a b => !decide (b < a))

/-- Both readings give the same axiom kinds. -/
def sameKinds (body : String) : Bool :=
  match FS.parseOntology (wrap body), FS.parseFunctionalSyntax (wrap body) with
  | some o, some g =>
      match FromRdf.ontologyOfGraph g with
      | .ok o2 => sortedNames o == sortedNames o2
      | .error _ => false
  | _, _ => false

/-- The verdicts, required to agree between the two readings. -/
def both (body : String) : Option (List Bool) :=
  if direct body == viaRdf body && sameKinds body then direct body else none

-- In all three profiles.
#guard both "SubClassOf(:A :B)" == some [true, true, true]
#guard both "ClassAssertion(:A :a) ObjectPropertyAssertion(:p :a :b)" == some [true, true, true]
-- An existential on the right: EL and QL (class filler), not RL.
#guard both "SubClassOf(:A ObjectSomeValuesFrom(:p :B))" == some [true, true, false]
-- An existential on the left with a class other than owl:Thing: EL and RL, not QL.
#guard both "SubClassOf(ObjectSomeValuesFrom(:p :B) :A)" == some [true, false, true]
#guard both "SubClassOf(ObjectSomeValuesFrom(:p owl:Thing) :A)" == some [true, true, true]
-- Universal quantification on the right: RL only.
#guard both "SubClassOf(:A ObjectAllValuesFrom(:p :B))" == some [false, false, true]
-- ... and on the left: no profile.
#guard both "SubClassOf(ObjectAllValuesFrom(:p :B) :A)" == some [false, false, false]
-- Union on the left: RL only. Union on the right: none.
#guard both "SubClassOf(ObjectUnionOf(:A :B) :C)" == some [false, false, true]
#guard both "SubClassOf(:C ObjectUnionOf(:A :B))" == some [false, false, false]
-- Max cardinality 1 on the right is RL; 2 is not.
#guard both "SubClassOf(:A ObjectMaxCardinality(1 :p))" == some [false, false, true]
#guard both "SubClassOf(:A ObjectMaxCardinality(2 :p))" == some [false, false, false]
#guard both "SubClassOf(:A ObjectMinCardinality(1 :p))" == some [false, false, false]
-- Complement of a subclass expression on the right: QL and RL.
#guard both "SubClassOf(:A ObjectComplementOf(:B))" == some [false, true, true]
-- Inverse properties: QL and RL, not EL.
#guard both "SubObjectPropertyOf(ObjectInverseOf(:p) :q)" == some [false, true, true]
#guard both "InverseObjectProperties(:p :q)" == some [false, true, true]
-- Property chains: EL and RL, not QL.
#guard both "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r)" == some [true, false, true]
-- Characteristics.
#guard both "TransitiveObjectProperty(:p)" == some [true, false, true]
#guard both "ReflexiveObjectProperty(:p)" == some [true, true, false]
#guard both "SymmetricObjectProperty(:p)" == some [false, true, true]
-- Irreflexive: the QL production has no such alternative (section 3.2.5).
#guard both "IrreflexiveObjectProperty(:p)" == some [false, false, true]
#guard both "FunctionalObjectProperty(:p)" == some [false, false, true]
#guard both "FunctionalDataProperty(:d)" == some [true, false, true]
-- Equality of individuals: not QL.
#guard both "SameIndividual(:a :b)" == some [true, false, true]
#guard both "DifferentIndividuals(:a :b)" == some [true, true, true]
-- DisjointUnion: no profile.
#guard both "DisjointUnion(:A :B :C)" == some [false, false, false]
-- Datatypes: xsd:int is RL only; owl:real is EL and QL only.
#guard both "DataPropertyRange(:d xsd:int)" == some [false, false, true]
#guard both "DataPropertyRange(:d owl:real)" == some [true, true, false]
#guard both "DataPropertyAssertion(:d :a \"1\"^^xsd:integer)" == some [true, true, true]
#guard both "DataPropertyAssertion(:d :a \"1\"^^xsd:boolean)" == some [false, false, true]
-- owl:Thing as a superclass is outside RL.
#guard both "SubClassOf(:A owl:Thing)" == some [true, true, false]
-- Equivalent classes: RL wants equivClassExpression, QL subClassExpression.
#guard both "EquivalentClasses(:A ObjectIntersectionOf(:B :C))" == some [true, false, true]
#guard both "EquivalentClasses(:A ObjectSomeValuesFrom(:p owl:Thing))" == some [true, true, false]
-- Keys: EL and RL.
#guard both "HasKey(:A (:p) (:d))" == some [true, false, true]
-- Nominals: one individual is EL; several on the left are RL.
#guard both "SubClassOf(ObjectOneOf(:a) :A)" == some [true, false, true]
#guard both "SubClassOf(ObjectOneOf(:a :b) :A)" == some [false, false, true]
-- Negative assertions: not QL.
#guard both "NegativeObjectPropertyAssertion(:p :a :b)" == some [true, false, true]
-- Disjoint properties: not EL.
#guard both "DisjointObjectProperties(:p :q)" == some [false, true, true]
-- Self restriction: EL only.
#guard both "SubClassOf(:A ObjectHasSelf(:p))" == some [true, false, false]

/-! ### The EL restriction on ranges and chains (section 2.2.6) -/

-- A range on the super-property of a chain must also be imposed on the
-- last property of the chain.
#guard direct "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r) ObjectPropertyRange(:r :A)"
  == some [false, false, true]
#guard direct "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r) ObjectPropertyRange(:r :A) \
               ObjectPropertyRange(:q :A)" == some [true, false, true]
-- ... also through a super-property of the last property.
#guard direct "SubObjectPropertyOf(ObjectPropertyChain(:p :q) :r) ObjectPropertyRange(:r :A) \
               SubObjectPropertyOf(:q :p) ObjectPropertyRange(:p :A)" == some [true, false, true]

end L4Factoidal.OWL.ProfilesTests
