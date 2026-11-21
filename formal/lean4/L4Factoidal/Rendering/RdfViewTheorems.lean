import L4Factoidal.Rendering.RdfView

namespace L4Factoidal.Rendering.RdfView

open RDF DOM

/-- Kind: admission invariant.
Says: a successful conversion to a browser DOM admits at most 256 triples
in the full graph supplied, before applying the view filter.
Does not say: how many rows or pixels the resulting view shows. -/
theorem toDOM_graph_length_le {graph : Graph} {filter : Filter} {dom : Dom}
    (h : toDOM graph filter = .ok dom) : graph.length ≤ 256 := by
  by_cases hlarge : graph.length > 256
  · unfold toDOM at h
    rw [if_pos hlarge] at h
    cases h
  · exact Nat.le_of_not_gt hlarge

/-- Kind: adapter soundness and resource bound.
Says: a successful RDF view returns the exact strict RDF 1.1 N-Triples
parser graph and the actual DOM adapter result, with the source-byte and full
graph caps satisfied.
Does not say: that the DOM preserves a particular row or paint observation. -/
theorem parse_graph_and_caps {source : String} {filter : Filter} {graph : Graph} {dom : Dom}
    (h : parse source filter = .ok (graph, dom)) :
    source.utf8ByteSize ≤ 1048576 ∧ Syntax.parseNTriples source .rdf11 = .ok graph ∧
      graph.length ≤ 256 ∧ toDOM graph filter = .ok dom := by
  have hstrict : Syntax.parseNTriplesDocument source .rdf11 = Syntax.parseNTriples source .rdf11 := by
    unfold Syntax.parseNTriplesDocument
    split
    · rename_i hp
      exact hp.symm
    · rename_i hp
      exact hp.symm
  unfold parse at h
  by_cases hlarge : source.utf8ByteSize > 1048576
  · rw [if_pos hlarge] at h
    cases h
  · rw [if_neg hlarge, hstrict] at h
    cases hparse : Syntax.parseNTriples source .rdf11 with
    | error e =>
      rw [hparse] at h
      cases h
    | ok parsed =>
      rw [hparse] at h
      simp only [Except.mapError, bind, Except.bind] at h
      cases hdom : toDOM parsed filter with
      | error e =>
        rw [hdom] at h
        cases h
      | ok rendered =>
        rw [hdom] at h
        change Except.ok (parsed, rendered) = Except.ok (graph, dom) at h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨Nat.le_of_not_gt hlarge, ?_, toDOM_graph_length_le hdom, hdom⟩
        first | rfl | exact hparse

#print axioms toDOM_graph_length_le
#print axioms parse_graph_and_caps

end L4Factoidal.Rendering.RdfView
