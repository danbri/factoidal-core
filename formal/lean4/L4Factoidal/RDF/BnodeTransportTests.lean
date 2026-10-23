/-
Tests of `RDF/BnodeTransport.lean` and `RDF/DocumentScope.lean`
(https://github.com/danbri/factoidal/issues/975, phases B3 and C).
-/
import L4Factoidal.RDF.DocumentScope

namespace L4Factoidal.RDF.BnodeTransportTests

open L4Factoidal.RDF

private def p : WfIri := ⟨"urn:p", by decide⟩
private def q : WfIri := ⟨"urn:q", by decide⟩
private def g : WfIri := ⟨"urn:g", by decide⟩
private def o : Term := .literal (Literal.string "x")

/-- `_:b0 urn:p <<( _:b0 urn:q "x" )>>` in the default graph, and the blank
node `_:b0` as a graph name. -/
private def nested : Dataset :=
  { default := [⟨.bnode "b0", p, .tripleTerm (.bnode "b0") q o⟩],
    named := [{ name := .bnode "b0", graph := [⟨.bnode "b1", p, o⟩] }] }

/-! The relabelling reaches subjects, triple terms, graph names and named
graphs. -/

#guard nested.scopeDocument 0 ==
  { default := [⟨.bnode "d0_b0", p, .tripleTerm (.bnode "d0_b0") q o⟩],
    named := [{ name := .bnode "d0_b0", graph := [⟨.bnode "d0_b1", p, o⟩] }] }

/-! One blank node stays one blank node: the relabelled dataset has as many
distinct blank nodes as the input. -/

#guard nested.bnodes.length == 2
#guard (nested.scopeDocument 0).bnodes.length == 2

/-! The relabelled dataset is isomorphic to the input (the search of
`RDF/Isomorphism.lean` finds the bijection). -/

#guard Dataset.isomorphic? nested (nested.scopeDocument 7)

/-! Two documents that both use `_:b0`. -/

private def docA : Dataset := { default := [⟨.bnode "b0", p, o⟩], named := [] }
private def docB : Dataset := { default := [⟨.bnode "b0", q, o⟩], named := [] }

/-! Combined without a scope (the union): one blank node, with both triples. -/

#guard (docA.combine docB).bnodes.length == 1

/-! Combined after scoping each document (the merge): two blank nodes. -/

#guard ((docA.scopeDocument 0).combine (docB.scopeDocument 1)).bnodes.length == 2

/-! The merge is not isomorphic to the union: the union says one node has both
properties. -/

#guard !Dataset.isomorphic? (docA.combine docB)
  ((docA.scopeDocument 0).combine (docB.scopeDocument 1))

/-! The scope labels of `docLabel` do not collide across scope numbers whose
decimal forms share a prefix (`d1_` and `d10_`). -/

#guard docLabel 1 "0_x" != docLabel 10 "x"
#guard docLabel 1 "0_x" = "d1_0_x"

end L4Factoidal.RDF.BnodeTransportTests
