import L4Factoidal.RDF.Collections

namespace L4Factoidal.RDF

open L4Factoidal.RDFS

/-- Kind: resource bound.
Says: a successful walk returns strictly fewer terms than the initial
accumulator size plus fuel. Each continuation adds one term, and the
terminal node needs one unit of fuel.
Does not say: how much work or memory the two lookup functions use. -/
theorem listWalk_length_lt (firsts rests : Term → List Term)
    {fuel : Nat} {seen : List Term} {acc : Array Term} {node : Term} {items : List Term}
    (h : listWalk firsts rests fuel seen acc node = .ok items) :
    items.length < acc.size + fuel := by
  induction fuel generalizing seen acc node with
  | zero => simp [listWalk] at h
  | succ fuel ih =>
    simp only [listWalk] at h
    split at h
    · simp only [Except.ok.injEq] at h
      rw [← h, Array.length_toList]
      omega
    · split at h
      · cases h
      · split at h
        · have hb := ih (seen := _) (acc := _) (node := _) h
          simp only [Array.size_push] at hb
          omega
        · cases h
        · cases h
        · cases h

/-- Kind: resource bound.
Says: a successful collection traversal starting with an empty accumulator
returns strictly fewer terms than its supplied bound.
Does not say: how many bytes the returned terms occupy. -/
theorem listItemsBy_length_lt (firsts rests : Term → List Term)
    {bound : Nat} {head : Term} {items : List Term}
    (h : listItemsBy firsts rests bound head = .ok items) :
    items.length < bound := by
  unfold listItemsBy at h
  have hb := listWalk_length_lt firsts rests h
  simpa using hb

/-- Kind: resource bound.
Says: a successful scan-based collection traversal returns at most as many
terms as the graph has triples.
Does not say: how much scanning or cycle checking the traversal performs. -/
theorem listItems_length_le (g : Graph) {head : Term} {items : List Term}
    (h : listItems g head = .ok items) : items.length ≤ g.length := by
  unfold listItems at h
  have hb := listItemsBy_length_lt (objectsIn g rdfFirst) (objectsIn g rdfRest) h
  omega

#print axioms listWalk_length_lt
#print axioms listItemsBy_length_lt
#print axioms listItems_length_le

end L4Factoidal.RDF
