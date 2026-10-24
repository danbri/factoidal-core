/-
L4Factoidal.RDF.GraphSet — the set of triples of a graph, and the one lemma
that every set-wise producer of a graph instantiates.

RDF 1.1 Concepts and Abstract Syntax §3: "An RDF graph is a set of RDF
triples." `Graph` is `List Triple`; the set condition is `Graph.KeyNodup`
(`RDF/DatasetSet.lean`): no two triples of the list have the same
`Triple.key`, so no two are `Triple.eqb`-equal (the same RDF term: lexical
form, datatype and base direction exact, language tag without case).

The shared abstraction is `graphAddAll` (`RDF/FastGraph.lean`), the left fold
of `Graph.add`. `Graph.KeyNodup.graphAddAll` proves that it keeps a set a set.
`Graph.union`, the SPARQL CONSTRUCT collection step, the RDFS closure rounds
(`RDFS.addAll`) and the FROM merge are this fold; their theorems in
`RDF/GraphOpsSet.lean` are instances of the lemma.

`Graph.toSet g` is the fold from the empty graph: the set of triples of `g`,
each at the place of its first occurrence. The compiler runs
`Graph.toSetFast`, the same fold on the hash-indexed `FastGraph`
(`Graph.toSet_eq_fast`), linear in the length of `g`. A producer whose own
step does not keep the set (the OWL 2 RL closure adds by structural equality,
`OWL.RL.addOne`) ends with `Graph.toSet`. On a list that is already a set
`Graph.toSet` is the identity (`Graph.toSet_of_keyNodup`), so it changes no
output that was already correct.

Tracking: https://github.com/danbri/factoidal/issues/973.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.DatasetSet
import L4Factoidal.RDF.FastGraph

namespace L4Factoidal.RDF

/-! ## The shared lemma -/

/-- The left fold of `Graph.add` keeps a set a set. -/
theorem Graph.KeyNodup.graphAddAll :
    ∀ (ts : List Triple) {g : Graph}, g.KeyNodup → (graphAddAll g ts).KeyNodup
  | [], _, h => h
  | t :: ts, _, h => Graph.KeyNodup.graphAddAll ts (h.add t)

/-- `List.foldl` of `Graph.add` is `graphAddAll`. -/
theorem foldl_add_eq_graphAddAll :
    ∀ (ts : List Triple) (g : Graph), ts.foldl (fun g t => g.add t) g = graphAddAll g ts
  | [], _ => rfl
  | t :: ts, g => foldl_add_eq_graphAddAll ts (g.add t)

theorem Graph.union_eq_graphAddAll (g1 g2 : Graph) : g1.union g2 = graphAddAll g1 g2 :=
  foldl_add_eq_graphAddAll g2 g1

/-- Engine membership in the fold: in the start graph or in the list. -/
theorem Graph.mem_graphAddAll (u : Triple) :
    ∀ (ts : List Triple) (g : Graph),
      (graphAddAll g ts).mem u = true ↔ g.mem u = true ∨ Graph.mem u ts = true
  | [], g => by simp [graphAddAll, Graph.mem]
  | t :: ts, g => by
      rw [show graphAddAll g (t :: ts) = graphAddAll (g.add t) ts from rfl,
        Graph.mem_graphAddAll u ts (g.add t), Graph.mem_add_iff]
      have ht : (t.eqb u = true) ↔ u.key = t.key := by
        rw [Triple.eqb_iff_key]; exact ⟨Eq.symm, Eq.symm⟩
      simp only [Graph.mem, Bool.or_eq_true, ht]
      constructor
      · rintro ((h | h) | h)
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr h)
        · exact Or.inr h

/-- On a set, the fold appends: every triple of `ts` is new. -/
theorem graphAddAll_of_keyNodup :
    ∀ (ts acc : Graph), (acc ++ ts).KeyNodup → graphAddAll acc ts = acc ++ ts
  | [], acc, _ => by simp [graphAddAll]
  | t :: ts, acc, h => by
      have hadd : acc.add t = acc ++ [t] := by
        unfold Graph.KeyNodup at h
        rw [List.map_append, List.map_cons] at h
        have hn := List.nodup_append.mp h
        have hm : Graph.mem t acc = false := by
          cases hmm : Graph.mem t acc
          · rfl
          · exact absurd rfl
              (hn.2.2 t.key ((Graph.mem_iff_keys t acc).mp hmm) t.key (List.mem_cons_self ..))
        simp [Graph.add, hm]
      show graphAddAll (acc.add t) ts = acc ++ t :: ts
      rw [hadd, graphAddAll_of_keyNodup ts (acc ++ [t]) (by simpa using h)]
      simp

/-! ## The set of triples of a graph -/

/-- The set of triples of `g`, each at its first occurrence. -/
def Graph.toSet (g : Graph) : Graph := graphAddAll [] g

/-- `Graph.toSet` on the hash-indexed accumulator. -/
def Graph.toSetFast (g : Graph) : Graph := (FastGraph.addAll {} g).toGraph

@[csimp] theorem Graph.toSet_eq_fast : @Graph.toSet = @Graph.toSetFast := by
  funext g
  unfold Graph.toSet Graph.toSetFast
  rw [FastGraph.addAll_toGraph g {} FastGraph.inv_empty]
  rfl

theorem Graph.toSet_keyNodup (g : Graph) : g.toSet.KeyNodup :=
  Graph.KeyNodup.graphAddAll g Graph.keyNodup_nil

theorem Graph.mem_toSet (u : Triple) (g : Graph) : g.toSet.mem u = true ↔ g.mem u = true := by
  unfold Graph.toSet
  rw [Graph.mem_graphAddAll]
  simp [Graph.mem]

/-- On a set, `Graph.toSet` is the identity. -/
theorem Graph.toSet_of_keyNodup {g : Graph} (h : g.KeyNodup) : g.toSet = g := by
  unfold Graph.toSet
  exact graphAddAll_of_keyNodup g [] (by simpa using h)

/-- Every triple of `Graph.toSet g` is a triple of `g`. -/
theorem Graph.toSet_sublist (g : Graph) : ∀ t ∈ g.toSet, t ∈ g := by
  suffices h : ∀ (ts acc : Graph) (t : Triple), t ∈ graphAddAll acc ts → t ∈ acc ∨ t ∈ ts by
    intro t ht
    rcases h g [] t ht with h | h
    · cases h
    · exact h
  intro ts
  induction ts with
  | nil => intro acc t ht; exact Or.inl ht
  | cons x xs ih =>
      intro acc t ht
      rcases ih (acc.add x) t ht with h | h
      · unfold Graph.add at h
        split at h
        · exact Or.inl h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · rw [List.mem_singleton] at h; subst h; exact Or.inr List.mem_cons_self
      · exact Or.inr (List.mem_cons_of_mem _ h)

/-! ## Checks -/

private def px : WfIri := ⟨"http://e/p", by decide⟩
private def ax : WfIri := ⟨"http://e/a", by decide⟩
private def tEn : Triple := ⟨.iri ax, px, .literal (Literal.langString "v" "en")⟩
private def tEN : Triple := ⟨.iri ax, px, .literal (Literal.langString "v" "EN")⟩
private def tV : Triple := ⟨.iri ax, px, .literal (Literal.string "v")⟩

-- A repeated triple is kept once, at its first place; language tags compare
-- without case.
#guard Graph.toSet [tV, tEn, tV, tEN] == [tV, tEn]
#guard Graph.toSetFast [tV, tEn, tV, tEN] == graphAddAll [] [tV, tEn, tV, tEN]
-- A set is unchanged.
#guard Graph.toSet [tEN, tV] == [tEN, tV]

#print axioms Graph.KeyNodup.graphAddAll
#print axioms Graph.toSet_eq_fast
#print axioms Graph.toSet_keyNodup
#print axioms Graph.mem_toSet
#print axioms Graph.toSet_of_keyNodup

end L4Factoidal.RDF
