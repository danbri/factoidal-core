/-
L4Factoidal.RDFS.TripleTermClosureTests — the RDFS and OWL 2 RL closures on
graphs that hold RDF 1.2 triple terms
(https://github.com/danbri/factoidal/issues/873).

RDF 1.2 Semantics, section "Simple Interpretations": a triple term denotes a
proposition, and a triple term is not asserted. The entailment rules of
RDF 1.2 Semantics §8 and §9 (and the OWL 2 RL rules of OWL 2 Profiles §4.3)
match ASSERTED triples. A triple term is one term in the object position of
an asserted triple; no rule reads the triple inside it. So:

* the closure keeps every asserted triple that has a triple term as object;
* it derives nothing from the triple inside a triple term: from
  `ex:a ex:says <<( ex:s rdf:type ex:C )>>` and `ex:C rdfs:subClassOf ex:D`
  it does not derive `ex:s rdf:type ex:D` (nor `ex:s rdf:type ex:C`);
* the OWL 2 RL closure applies the rule table of OWL 2 Profiles §4.3, whose
  eq-rep-o replaces a whole object term; it does not substitute inside a
  triple term. RDF 1.2 Semantics makes the IRIs inside a triple term
  transparent, so `ex:s owl:sameAs ex:t` does entail
  `ex:a ex:says <<( ex:t rdf:type ex:C )>>` (W3C rdf12 rdf-semantics test
  `opaque-iri`, which the manifest lists but leaves out of its entries, "relies
  on non-standard entailment regime"). `RDF.regimeEntails .rdfsPlus` decides
  that case (`RDF/EntailmentTests.lean`); the closure op does not derive it,
  an expected failure in `npm/factoidal/test/rdf12-terms.test.js`
  (https://github.com/danbri/factoidal/issues/873);
* the derivations from asserted triples stay (`ex:x rdf:type ex:D`).

Each fixture checks a triple the rules must derive AND triples they must not
derive (`skills/measuring-inference/SKILL.md`).
-/
import L4Factoidal.RDF.Datatypes
import L4Factoidal.RDFS.Closure
import L4Factoidal.RDFS.FullClosure
import L4Factoidal.RDFS.RDFSPlus
import L4Factoidal.OWL.RLClosure
import L4Factoidal.OWL.RLClosureIndexed

namespace L4Factoidal.RDFS.TripleTermClosureTests

open L4Factoidal.RDF
open L4Factoidal.RDFS

private def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def a : WfIri := iri! "http://example.com/a"
private def s : WfIri := iri! "http://example.com/s"
private def t : WfIri := iri! "http://example.com/t"
private def x : WfIri := iri! "http://example.com/x"
private def says : WfIri := iri! "http://example.com/says"
private def C : WfIri := iri! "http://example.com/C"
private def D : WfIri := iri! "http://example.com/D"
private def sameAs : WfIri := iri! "http://www.w3.org/2002/07/owl#sameAs"

private def tr (s' p o : WfIri) : Triple := ⟨.iri s', p, .iri o⟩

/-- `ex:a ex:says <<( subj rdf:type ex:C )>>`. -/
private def saysType (subj : Subject) : Triple :=
  ⟨.iri a, says, .tripleTerm subj rdfType (.iri C)⟩

/-- The fixture: a triple term with an IRI subject, one with a blank node
subject, the schema triple, one asserted instance, and an `owl:sameAs`. -/
private def g : Graph :=
  [ saysType (.iri s),
    saysType (.bnode "b1"),
    tr C rdfsSubClassOf D,
    tr x rdfType C,
    tr s sameAs t ]

/-- The four closures the RDFS and OWL ops run (`Wasm/Ops/Reason.lean`). -/
private def closures : List Graph :=
  [ RDFS.closureFix g,
    fullClosure (withMinimalD []) [rdf1] g,
    rdfsPlusClosureFix g,
    OWL.RL.closureFix g ]

-- Kept: the asserted triples whose object is a triple term.
#guard closures.all (fun c => Graph.mem (saysType (.iri s)) c)
#guard closures.all (fun c => Graph.mem (saysType (.bnode "b1")) c)
-- Kept: the derivation from asserted triples (rdfs9; OWL 2 RL cax-sco).
#guard closures.all (fun c => Graph.mem (tr x rdfType D) c)
-- Not derived: the triple inside a triple term is not asserted.
#guard closures.all (fun c => !Graph.mem (tr s rdfType C) c)
#guard closures.all (fun c => !Graph.mem (tr s rdfType D) c)
#guard closures.all (fun c => !Graph.mem ⟨.bnode "b1", rdfType, .iri C⟩ c)
#guard closures.all (fun c => !Graph.mem ⟨.bnode "b1", rdfType, .iri D⟩ c)
-- Not derived: no new triple term made from the inside of a triple term.
#guard closures.all (fun c => !c.any (fun u =>
  u.o == .tripleTerm (.iri s) rdfType (.iri D)))
-- Derived: OWL 2 RL eq-sym on the asserted `owl:sameAs`.
#guard Graph.mem (tr t sameAs s) (OWL.RL.closureFix g)

end L4Factoidal.RDFS.TripleTermClosureTests
