/-
L4Factoidal.Dataflow.ExplainGraphTests — checks of `Dataflow/GraphClaim.lean`
and `Dataflow/ExplainGraph.lean`, evaluated during `lake build`
(https://github.com/danbri/factoidal/issues/1002).

Sources: `ex:alice ex:worksFor ex:acme . ex:worksFor rdfs:domain ex:Employee .
ex:Employee rdfs:subClassOf ex:Person . ex:bob ex:name ex:BobName .`

1. Entailed: the description `_:x rdf:type ex:Person . _:x rdf:type
   ex:Employee . _:x ex:worksFor ex:acme .` (three triples, one shared blank
   node) by rdfs2 (domain) and rdfs9 (subClassOf). The mapping sends `_:x` to
   `ex:alice`; the cut derivation has the base, rdfs2 and rdfs9 steps; the
   graph checker accepts the bundle.
2. Not entailed, `noMatch`: `_:x rdf:type ex:Person . _:x ex:worksFor
   ex:globex .`. The rejection names triple 1 and that triple; triple 0 alone
   HAS an instance in the closure, and the closure holds `ex:alice rdf:type
   ex:Person`, so the verdict is not the result of an empty closure.
3. Not entailed, `noJointMapping`: `_:x ex:worksFor ex:acme . _:x ex:name
   ex:BobName .`. Each triple alone has an instance; no one node does both.
4. Tampered bundles, each refused by the graph checker: the mapping sends
   `_:x` to `ex:bob`; a description triple is added; a support index points at
   another step; a derivation step is changed to a conclusion its rule does
   not license; the sources lose the domain triple.

No executable imports this module.
-/
import L4Factoidal.Dataflow.ExplainGraph

namespace L4Factoidal.Dataflow.ExplainGraphTests

open L4Factoidal.RDF
open L4Factoidal.RDFS
open L4Factoidal.Dataflow

private def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def exAlice : WfIri := iri! "http://example.org/alice"
private def exBob : WfIri := iri! "http://example.org/bob"
private def exAcme : WfIri := iri! "http://example.org/acme"
private def exGlobex : WfIri := iri! "http://example.org/globex"
private def exWorksFor : WfIri := iri! "http://example.org/worksFor"
private def exName : WfIri := iri! "http://example.org/name"
private def exEmployee : WfIri := iri! "http://example.org/Employee"
private def exPerson : WfIri := iri! "http://example.org/Person"

private def bobLit : Term := .iri (iri! "http://example.org/BobName")

private def sources : Graph :=
  [ { s := .iri exAlice, p := exWorksFor, o := .iri exAcme },
    { s := .iri exWorksFor, p := rdfsDomain, o := .iri exEmployee },
    { s := .iri exEmployee, p := rdfsSubClassOf, o := .iri exPerson },
    { s := .iri exBob, p := exName, o := bobLit } ]

private def ds : Dataset := { default := sources, named := [] }
private def defaultOnly : GraphSelection := { default := true }

private def accepted (b : GraphBundle) : Bool :=
  match checkGraphRun [] b with
  | .ok _ => true
  | .error _ => false

private def run (E : Graph) : ExplainGraphResult :=
  match (rdfsExplainGraphStage [] defaultOnly).run (ds, E) with
  | .ok r => r
  | .error _ => { entailed := false, bundle := none, assumptions := [], rejection := none }

/-! ## 1. Entailed: three triples, one shared blank node -/

private def described : Graph :=
  [ { s := .bnode "x", p := rdfType, o := .iri exPerson },
    { s := .bnode "x", p := rdfType, o := .iri exEmployee },
    { s := .bnode "x", p := exWorksFor, o := .iri exAcme } ]

private def r1 : ExplainGraphResult := run described

#guard r1.entailed
#guard r1.rejection == none
#guard r1.assumptions.isEmpty
#guard match r1.bundle with
  | some b => b.mapping.subst "x" == .iri exAlice
  | none => false
-- the graph checker accepts the bundle the stage returns
#guard match r1.bundle with
  | some b => accepted b
  | none => false
-- one support index per description triple; the cut derivation uses rdfs2
-- (domain) and rdfs9 (subClassOf), and keeps fewer steps than the closure
#guard match r1.bundle with
  | some b => b.support.length == 3 &&
      b.witness.toList.any (·.rule == .rdfs2) && b.witness.toList.any (·.rule == .rdfs9) &&
      b.witness.size < (fullClosureWithProof [] (graphCmps sources described) sources).2.size
  | none => false
-- the step cited for triple 0 concludes ex:alice rdf:type ex:Person, by rdfs9
#guard match r1.bundle with
  | some b => match b.support.head? >>= (b.witness[·]?) with
    | some st => st.rule == .rdfs9 && st.conclusion == { s := .iri exAlice, p := rdfType, o := .iri exPerson }
    | none => false
  | none => false

/-! ## 2. Not entailed: one triple has no instance -/

private def notDescribed : Graph :=
  [ { s := .bnode "x", p := rdfType, o := .iri exPerson },
    { s := .bnode "x", p := exWorksFor, o := .iri exGlobex } ]

private def r2 : ExplainGraphResult := run notDescribed

#guard !r2.entailed
#guard r2.bundle.isNone
#guard r2.rejection == some (.noMatch 1 { s := .bnode "x", p := exWorksFor, o := .iri exGlobex })
#guard r2.assumptions == notEntailedAssumptions
-- not the result of deriving nothing: triple 0 alone has an instance in the
-- closure, and the closure holds the derived type triple
private def cl2 : Graph := fullClosure [] (graphCmps sources notDescribed) sources
#guard !unmatchedIn cl2 { s := .bnode "x", p := rdfType, o := .iri exPerson }
#guard cl2.contains { s := .iri exAlice, p := rdfType, o := .iri exPerson }

/-! ## 3. Not entailed: no one mapping serves both triples -/

private def noJoint : Graph :=
  [ { s := .bnode "x", p := exWorksFor, o := .iri exAcme },
    { s := .bnode "x", p := exName, o := bobLit } ]

private def r3 : ExplainGraphResult := run noJoint

#guard !r3.entailed
#guard r3.rejection == some .noJointMapping
-- each triple alone is entailed
#guard (run [{ s := .bnode "x", p := exWorksFor, o := .iri exAcme }]).entailed
#guard (run [{ s := .bnode "x", p := exName, o := bobLit }]).entailed

/-! ## 4. Tampered bundles -/

private def good : GraphBundle :=
  r1.bundle.getD { sources := [], description := [], mapping := [], witness := #[], support := [] }

private def refused (b : GraphBundle) : Bool := !accepted b

#guard !refused good
-- the mapping sends _:x to ex:bob
#guard refused { good with mapping := [("x", .iri exBob)] }
-- a description triple is added, with no support index
private def globexTriple : Triple := { s := .bnode "x", p := exWorksFor, o := .iri exGlobex }
#guard refused { good with description := good.description ++ [globexTriple] }
-- ... and with a support index that points at a step for another triple
private def addedWithIndex : GraphBundle :=
  { good with description := good.description ++ [globexTriple], support := good.support ++ [good.support.headD 0] }
#guard refused addedWithIndex
-- triple 0 cites the step of triple 2
#guard refused { good with support := good.support.reverse }
-- the rdfs9 step concludes ex:bob rdf:type ex:Person
private def bobPerson : Triple := { s := .iri exBob, p := rdfType, o := .iri exPerson }
private def badStep (st : Step) : Step := if st.rule == .rdfs9 then { st with conclusion := bobPerson } else st
#guard refused { good with witness := good.witness.map badStep }
-- the sources lose the domain triple
#guard refused { good with sources := sources.filter (·.p != rdfsDomain) }

end L4Factoidal.Dataflow.ExplainGraphTests
