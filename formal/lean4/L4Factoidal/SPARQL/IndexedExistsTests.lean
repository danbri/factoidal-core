import L4Factoidal.SPARQL.IndexedExists

namespace L4Factoidal.SPARQL.IndexedExistsTests

open L4Factoidal.RDF L4Factoidal.SPARQL.StoreBackend L4Factoidal.SPARQL.StorePlan

private def a : WfIri := ⟨"urn:a", rfl⟩
private def b : WfIri := ⟨"urn:b", rfl⟩
private def p : WfIri := ⟨"urn:p", rfl⟩
private def q : WfIri := ⟨"urn:q", rfl⟩
private def graph : Graph :=
  [⟨.iri a, p, .iri b⟩, ⟨.iri b, p, .iri b⟩,
   ⟨.iri a, q, .literal (Literal.langString "colour" "en")⟩]
private def index := OWL.RL.Index.ofGraph graph

private def self : TriplePattern := ⟨.var "x", .iri p, .var "x"⟩
#guard indexedSingleTpExists index self []
#guard !indexedSingleTpExists (OWL.RL.Index.ofGraph [⟨.iri a, p, .iri b⟩]) self []
#guard !indexedSingleTpExists (OWL.RL.Index.ofGraph []) self []
#guard indexedSingleTpExists index ⟨.var "s", .iri q, .literal (Literal.langString "colour" "EN")⟩ []
#guard !indexedSingleTpExists index ⟨.var "s", .iri p, .var "o"⟩ [("s", .literal (Literal.string "invalid subject"))]
#guard !indexedSingleTpExists index ⟨.var "s", .var "p", .var "o"⟩ [("p", .bnode "invalid predicate")]

private def patterns : List TriplePattern :=
  ([.var "x", .var "y", .iri a, .bnode "absent"] : List PatternSubject).flatMap fun s =>
    ([.var "x", .iri p, .var "p"] : List PatternTerm).flatMap fun pred =>
      ([.var "x", .var "y", .iri b, .literal (Literal.langString "colour" "EN")] : List PatternTerm).map fun o =>
        ⟨s, pred, o⟩

#guard patterns.all fun tp =>
  ([[], [("x", .iri a)], [("x", .literal (Literal.string "value"))], [("p", .bnode "value")]] : List Binding).all fun mu =>
    indexedSingleTpExists index tp mu == !(evalSingleTpBackend tp (.indexed index) mu).isEmpty

end L4Factoidal.SPARQL.IndexedExistsTests
