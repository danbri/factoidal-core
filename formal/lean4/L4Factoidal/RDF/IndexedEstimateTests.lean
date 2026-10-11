import L4Factoidal.RDF.StoreCapabilities

namespace L4Factoidal.RDF.IndexedEstimateTests

open L4Factoidal.SPARQL

private def a : WfIri := ⟨"urn:a", rfl⟩
private def b : WfIri := ⟨"urn:b", rfl⟩
private def p : WfIri := ⟨"urn:p", rfl⟩
private def q : WfIri := ⟨"urn:q", rfl⟩
private def missing : WfIri := ⟨"urn:missing", rfl⟩
private def graph : Graph :=
  [⟨.iri a, p, .iri b⟩, ⟨.iri a, p, .iri b⟩,
   ⟨.iri b, p, .iri a⟩,
   ⟨.iri a, q, .literal (Literal.langString "colour" "en")⟩]
private def index := OWL.RL.Index.ofGraph graph

#guard igEstimateFast index {} == 4
#guard igEstimateFast index { p := some p } == 3
#guard igEstimateFast index { p := some q } == 1
#guard igEstimateFast index { p := some missing } == 0
#guard igEstimateFast OWL.RL.Index.empty {} == 0
#guard igEstimateFast OWL.RL.Index.empty { p := some p } == 0
#guard igEstimateFast (index.push ⟨.iri a, p, .iri b⟩) { p := some p } == 4
#guard igEstimateFast index { p := some q, o := some (.literal (Literal.langString "colour" "EN")) } == 1

private def bounds : List PatternBound :=
  ([none, some (.iri a), some (.iri b), some (.bnode "missing")] : List (Option Subject)).flatMap fun s =>
    ([none, some p, some q, some missing] : List (Option WfIri)).flatMap fun pred =>
      ([none, some (.iri a), some (.iri b), some (.literal (Literal.langString "colour" "EN"))] :
        List (Option Term)).map fun o => ⟨s, pred, o⟩

-- Duplicate triples, missing keys and case-insensitive object equality.
#guard bounds.all fun bound => igEstimateFast index bound == igEstimate index bound
#guard bounds.all fun bound => igEstimateFast OWL.RL.Index.empty bound == igEstimate OWL.RL.Index.empty bound

end L4Factoidal.RDF.IndexedEstimateTests
