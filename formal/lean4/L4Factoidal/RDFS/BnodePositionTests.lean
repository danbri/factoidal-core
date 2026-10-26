/-
L4Factoidal.RDFS.BnodePositionTests — blank nodes in the positions that
RDF 1.1 Semantics §9.2 leaves open (https://github.com/danbri/factoidal/issues/982).

Rule table, §9.2 (quoted):

  rdfs2   aaa rdfs:domain xxx . yyy aaa zzz .            gives  yyy rdf:type xxx .
  rdfs3   aaa rdfs:range xxx . yyy aaa zzz .             gives  zzz rdf:type xxx .
  rdfs4a  xxx aaa yyy .                                  gives  xxx rdf:type rdfs:Resource .
  rdfs4b  xxx aaa yyy .                                  gives  yyy rdf:type rdfs:Resource .
  rdfs5   xxx rdfs:subPropertyOf yyy . yyy rdfs:subPropertyOf zzz .
                                                         gives  xxx rdfs:subPropertyOf zzz .
  rdfs6   xxx rdf:type rdf:Property .                    gives  xxx rdfs:subPropertyOf xxx .
  rdfs7   aaa rdfs:subPropertyOf bbb . xxx aaa yyy .     gives  xxx bbb yyy .
  rdfs8   xxx rdf:type rdfs:Class .                      gives  xxx rdfs:subClassOf rdfs:Resource .
  rdfs9   xxx rdfs:subClassOf yyy . zzz rdf:type xxx .   gives  zzz rdf:type yyy .
  rdfs10  xxx rdf:type rdfs:Class .                      gives  xxx rdfs:subClassOf xxx .
  rdfs11  xxx rdfs:subClassOf yyy . yyy rdfs:subClassOf zzz .
                                                         gives  xxx rdfs:subClassOf zzz .
  rdfs12  xxx rdf:type rdfs:ContainerMembershipProperty . gives xxx rdfs:subPropertyOf rdfs:member .
  rdfs13  xxx rdf:type rdfs:Datatype .                   gives  xxx rdfs:subClassOf rdfs:Literal .

Positions that must stay IRI-only, because the position holds a property
name (the predicate of a triple): `aaa` in rdfs2, rdfs3 and rdfs7, `bbb`
in rdfs7. A blank node there would be a generalised triple.
Positions that must take a blank node: every other variable. A literal
cannot be a subject of an RDF 1.1 triple, so a conclusion with a literal
subject is not built (rdfs3, rdfs4b); nothing here tests that, the term
model cannot state such a triple.
-/
import L4Factoidal.RDFS.DerivationCheck
import L4Factoidal.RDFS.DerivationTests

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

private def eP : WfIri := ⟨"http://example.org/p", by rfl⟩
private def eAlice : WfIri := ⟨"http://example.org/alice", by rfl⟩
private def ePerson : WfIri := ⟨"http://example.org/Person", by rfl⟩
private def eAgent : WfIri := ⟨"http://example.org/Agent", by rfl⟩

private def bC : Subject := .bnode "c"
private def bD : Subject := .bnode "d"

private def has (g : Graph) (t : Triple) : Bool := g.contains t

/-- rdfs9 with a blank-node class (the issue 982 case). -/
private def g9 : Graph :=
  [⟨.iri eAlice, rdfType, bC.toTerm⟩, ⟨bC, rdfsSubClassOf, .iri ePerson⟩]
private def t9 : Triple := ⟨.iri eAlice, rdfType, .iri ePerson⟩
/-- rdfs9 with a blank-node subject and blank-node classes on both sides. -/
private def g9b : Graph :=
  [⟨.bnode "i", rdfType, bC.toTerm⟩, ⟨bC, rdfsSubClassOf, bD.toTerm⟩]
private def t9b : Triple := ⟨.bnode "i", rdfType, bD.toTerm⟩

#guard has (fullClosure [] [] g9) t9
#guard has (fullClosure [] [] g9b) t9b
#guard has (closure g9 100) t9
#guard has (closure g9b 100) t9b

/-- The emitter gives a derivation whose conclusion list is the closure,
and the checker accepts it. -/
private def w9 : Graph × Derivation := fullClosureWithProof [] [] g9
#guard has w9.1 t9
#guard (w9.2.toList.filter (fun a => a.rule == .rdfs9 && a.conclusion == t9)).length == 1
#guard checkDerivation (axiomaticTriples [] []) g9 w9.2
private def w9b : Graph × Derivation := fullClosureWithProof [] [] g9b
#guard checkDerivation (axiomaticTriples [] []) g9b w9b.2

-- Controls: rows that already accept blank nodes in each open position.
-- rdfs2: blank-node subject, blank-node domain class.
#guard has (fullClosure [] [] [⟨.bnode "x", eP, .iri eAlice⟩, ⟨.iri eP, rdfsDomain, bC.toTerm⟩])
  ⟨.bnode "x", rdfType, bC.toTerm⟩
-- rdfs3: blank-node object, blank-node range class.
#guard has (fullClosure [] [] [⟨.iri eAlice, eP, .bnode "x"⟩, ⟨.iri eP, rdfsRange, bC.toTerm⟩])
  ⟨.bnode "x", rdfType, bC.toTerm⟩
-- rdfs4a, rdfs4b: blank-node subject and object.
#guard has (fullClosure [] [] [⟨.bnode "x", eP, .bnode "y"⟩]) ⟨.bnode "x", rdfType, .iri rdfsResource⟩
#guard has (fullClosure [] [] [⟨.bnode "x", eP, .bnode "y"⟩]) ⟨.bnode "y", rdfType, .iri rdfsResource⟩
-- rdfs5, rdfs11: blank-node middle term.
#guard has (fullClosure [] [] [⟨bC, rdfsSubPropertyOf, bD.toTerm⟩, ⟨bD, rdfsSubPropertyOf, .iri eP⟩])
  ⟨bC, rdfsSubPropertyOf, .iri eP⟩
#guard has (fullClosure [] [] [⟨bC, rdfsSubClassOf, bD.toTerm⟩, ⟨bD, rdfsSubClassOf, .iri ePerson⟩])
  ⟨bC, rdfsSubClassOf, .iri ePerson⟩
-- rdfs6, rdfs8, rdfs10, rdfs12, rdfs13: blank-node subject.
#guard has (fullClosure [] [] [⟨bC, rdfType, .iri rdfProperty⟩]) ⟨bC, rdfsSubPropertyOf, bC.toTerm⟩
#guard has (fullClosure [] [] [⟨bC, rdfType, .iri rdfsClass⟩]) ⟨bC, rdfsSubClassOf, .iri rdfsResource⟩
#guard has (fullClosure [] [] [⟨bC, rdfType, .iri rdfsClass⟩]) ⟨bC, rdfsSubClassOf, bC.toTerm⟩
#guard has (fullClosure [] [] [⟨bC, rdfType, .iri rdfsContainerMembershipProperty⟩])
  ⟨bC, rdfsSubPropertyOf, .iri rdfsMember⟩
#guard has (fullClosure [] [] [⟨bC, rdfType, .iri rdfsDatatype⟩]) ⟨bC, rdfsSubClassOf, .iri rdfsLiteral⟩
-- rdfs7: the property positions stay IRIs; a data triple with a
-- blank-node subject and object is carried over.
#guard has (fullClosure [] [] [⟨.iri eP, rdfsSubPropertyOf, .iri eP⟩, ⟨.bnode "x", eP, .bnode "y"⟩])
  ⟨.bnode "x", eP, .bnode "y"⟩

/-! ## Axiom audit — expect propext / Classical.choice / Quot.sound only -/

#print axioms L4Factoidal.RDFS.rdfs9For_sound
#print axioms L4Factoidal.RDFS.closure_sound
#print axioms L4Factoidal.RDFS.fullClosure_sound
#print axioms L4Factoidal.RDFS.fullClosureWithProof_sound
#print axioms L4Factoidal.RDFS.checkDerivation_sound

end L4Factoidal.RDFS
