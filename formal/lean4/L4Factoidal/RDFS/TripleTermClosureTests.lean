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
* the one exception is `owl:sameAs`. RDF 1.2 Semantics makes the IRIs inside
  a triple term transparent, so `ex:s owl:sameAs ex:t` entails
  `ex:a ex:says <<( ex:t rdf:type ex:C )>>` (W3C rdf12 rdf-semantics test
  `opaque-iri`, which the manifest lists but leaves out of its entries, "relies
  on non-standard entailment regime"). The OWL 2 RL closure derives it with
  the `[ext]` row eq-rep-tt (`OWL.RL.eqRepTtFor`, `Derives.eqRepTt`): one
  occurrence of an IRI in subject, predicate or object position of a triple
  term, at any nesting depth, is replaced by an IRI it is `owl:sameAs` to.
  The RDFS-Plus closure (`rdfsPlusClosureFix`) runs the same row, because
  the W3C test's regime is "RDFS-Plus" (added 2026-10-23). The RDFS and
  rho-df closures have no `owl:sameAs` semantics and do not substitute;
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

-- eq-rep-tt (issue 873, W3C `opaque-iri`): the OWL 2 RL closure, in the
-- list form and in the indexed semi-naive form, and the RDFS-Plus closure
-- substitute `owl:sameAs` inside a triple term.
private def owlClosures (h : Graph) : List Graph :=
  [ OWL.RL.closureFix h,
    OWL.RL.indexedClosureSN h (OWL.RL.closureFuelBound h),
    rdfsPlusClosureFix h ]

private def saysTypeC (subj : WfIri) : Triple :=
  ⟨.iri a, says, .tripleTerm (.iri subj) rdfType (.iri C)⟩

#guard (owlClosures g).all (fun c => Graph.mem (saysTypeC t) c)
-- Not derived: the RDFS closures have no `owl:sameAs` semantics.
#guard !Graph.mem (saysTypeC t) (RDFS.closureFix g)
#guard !Graph.mem (saysTypeC t) (fullClosure (withMinimalD []) [rdf1] g)
-- Not derived: the substituted triple term is still not asserted, and no
-- rule reads inside it.
#guard (owlClosures g).all (fun c => !Graph.mem (tr t rdfType C) c)
#guard (owlClosures g).all (fun c => !Graph.mem (tr t rdfType D) c)
#guard (owlClosures g).all (fun c => !c.any (fun u =>
  u.o == .tripleTerm (.iri t) rdfType (.iri D)))
-- Not derived: a blank node inside a triple term is not replaced by an IRI.
#guard (owlClosures g).all (fun c => !c.any (fun u =>
  u.s == .iri a && u.o == .tripleTerm (.bnode "b1") rdfType (.iri t)))

-- Nested triple term, and the predicate and object positions.
private def p1 : WfIri := iri! "http://example.com/p1"
private def p2 : WfIri := iri! "http://example.com/p2"
private def inner (u : WfIri) : Term := .tripleTerm (.iri u) rdfType (.iri C)
private def nested (u v : WfIri) : Triple :=
  ⟨.iri a, says, .tripleTerm (.iri u) p1 (inner v)⟩
private def g2 : Graph :=
  [ nested s s,
    tr s sameAs t,
    tr p1 sameAs p2,
    ⟨.iri a, says, .tripleTerm (.iri x) p1 (.iri s)⟩ ]

-- Every combination of the two occurrences of `ex:s`, at depth 1 and 2.
#guard (owlClosures g2).all (fun c => Graph.mem (nested t s) c)
#guard (owlClosures g2).all (fun c => Graph.mem (nested s t) c)
#guard (owlClosures g2).all (fun c => Graph.mem (nested t t) c)
-- Predicate position.
#guard (owlClosures g2).all (fun c =>
  Graph.mem ⟨.iri a, says, .tripleTerm (.iri s) p2 (inner s)⟩ c)
-- Object position.
#guard (owlClosures g2).all (fun c =>
  Graph.mem ⟨.iri a, says, .tripleTerm (.iri x) p1 (.iri t)⟩ c)
-- Not derived: `ex:C` has no `owl:sameAs` partner, so it is not replaced;
-- the inner triple is not asserted.
#guard (owlClosures g2).all (fun c => !c.any (fun u =>
  u.o == .tripleTerm (.iri s) p1 (.tripleTerm (.iri s) rdfType (.iri D))))
#guard (owlClosures g2).all (fun c => !Graph.mem (tr t rdfType C) c)
#guard (owlClosures g2).all (fun c => !Graph.mem ⟨.iri s, p1, inner s⟩ c)

-- The W3C `opaque-iri` case (as `RDF/EntailmentTests.lean` transcribes it):
-- `ex:clark owl:sameAs ex:superman`,
-- `ex:clark ex:reports <<( ex:superman ex:can ex:fly )>>` gives
-- `ex:clark ex:reports <<( ex:clark ex:can ex:fly )>>`.
private def clark : WfIri := iri! "http://example.com/clark"
private def superman : WfIri := iri! "http://example.com/superman"
private def reports : WfIri := iri! "http://example.com/reports"
private def can : WfIri := iri! "http://example.com/can"
private def fly : WfIri := iri! "http://example.com/fly"
private def clarkG : Graph :=
  [ tr clark sameAs superman,
    ⟨.iri clark, reports, .tripleTerm (.iri superman) can (.iri fly)⟩ ]
#guard (owlClosures clarkG).all (fun c =>
  Graph.mem ⟨.iri clark, reports, .tripleTerm (.iri clark) can (.iri fly)⟩ c)
#guard (owlClosures clarkG).all (fun c => !Graph.mem (tr superman can fly) c)
#guard (owlClosures clarkG).all (fun c => !Graph.mem (tr clark can fly) c)

end L4Factoidal.RDFS.TripleTermClosureTests
