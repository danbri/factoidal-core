/-
L4Factoidal.RDF.GraphIndex — a graph with a hash set of its triples, for
adding many triples one by one in time linear in their number.

`Graph.add t g` (`RDF/Graph.lean`) is `if g.mem t then g else g ++ [t]`: a
scan of the graph and a copy of it for each triple, so a fold of `Graph.add`
over n triples takes time in n². `SPARQL.Update`'s `Dataset.insertQuads` (INSERT
DATA, https://github.com/danbri/factoidal/issues/821) and the merge of the
browser update log (`Storage.BrowserLog.merge`,
https://github.com/danbri/factoidal/issues/822) are such folds.

`GraphIx` holds the same graph as `base ++ rev.reverse` (the triples added
since the index was made are in `rev`, newest first) and the set of the KEYS of
its triples. `Graph.mem` compares with `Triple.eqb`, which is coarser than
structural equality: a language tag compares case-insensitively and an
`rdf:XMLLiteral` lexical form by its exclusive canonical form. The key of a
triple is the triple with its object replaced by `Term.joinKey` (the canonical
representative of the `Term.eqb` class, `RDF/Core.lean`), and
`Triple.eqb_iff_key` proves that two triples are `eqb`-equal exactly when
their keys are equal. So a set lookup of the key answers `Graph.mem`
(`GraphIx.contains_key`), and `GraphIx.add` is `Graph.add` with the order of
the triples unchanged (`GraphIx.toGraph_add`).
-/
import L4Factoidal.RDF.Graph
import Std.Data.HashSet

namespace L4Factoidal.RDF

/-! ## The key of a triple -/

/-- A literal's join key determines the literal up to `Literal.eqb`: the
converse of `Literal.joinKey_eq_of_eqb`. -/
theorem Literal.eqb_of_joinKey_eq {l1 l2 : Literal}
    (h : l1.joinKey = l2.joinKey) : l1.eqb l2 = true := by
  unfold Literal.joinKey at h
  simp only [Literal.mk.injEq] at h
  obtain ⟨hlex, hdt, htag, hdir⟩ := h
  unfold Literal.eqb
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨⟨hlex, hdt⟩, ?_⟩, hdir⟩
  · cases h1 : l1.langTag with
    | none =>
      cases h2 : l2.langTag with
      | none => rfl
      | some b => rw [h1, h2] at htag; simp at htag
    | some a =>
      cases h2 : l2.langTag with
      | none => rw [h1, h2] at htag; simp at htag
      | some b =>
        rw [h1, h2] at htag
        simp only [Option.map_some, Option.some.injEq] at htag
        simp [langTagOptionEq, langTagEq, htag]

/-- The converse of `Term.joinKey_eq_of_eqb`: equal join keys mean
`eqb`-equal terms. -/
theorem Term.eqb_of_joinKey_eq : ∀ {a b : Term},
    a.joinKey = b.joinKey → Term.eqb a b = true := by
  intro a
  induction a with
  | iri i => intro b h; cases b <;> simp_all [Term.eqb, Term.joinKey]
  | bnode x => intro b h; cases b <;> simp_all [Term.eqb, Term.joinKey]
  | literal l =>
      intro b h
      cases b <;> simp only [Term.joinKey, reduceCtorEq] at h
      case literal l2 =>
        simp only [Term.literal.injEq, Subtype.mk.injEq] at h
        simp only [Term.eqb]
        exact Literal.eqb_of_joinKey_eq h
  | tripleTerm s p o ih =>
      intro b h
      cases b <;> simp only [Term.joinKey, reduceCtorEq] at h
      case tripleTerm s2 p2 o2 =>
        simp only [Term.tripleTerm.injEq] at h
        obtain ⟨hs, hp, ho⟩ := h
        simp [Term.eqb, hs, hp, ih ho]

theorem Term.eqb_iff_joinKey (a b : Term) : Term.eqb a b = true ↔ a.joinKey = b.joinKey :=
  ⟨Term.joinKey_eq_of_eqb, Term.eqb_of_joinKey_eq⟩

/-- The key of a triple: its object replaced by the canonical representative
of its `Term.eqb` class. The subject and the predicate compare structurally
already. -/
def Triple.key (t : Triple) : Triple := { s := t.s, p := t.p, o := t.o.joinKey }

/-- Two triples are `eqb`-equal exactly when their keys are equal. -/
theorem Triple.eqb_iff_key (a b : Triple) : a.eqb b = true ↔ a.key = b.key := by
  obtain ⟨s1, p1, o1⟩ := a
  obtain ⟨s2, p2, o2⟩ := b
  simp only [Triple.eqb, Triple.key, Triple.mk.injEq, Bool.and_eq_true, beq_iff_eq,
    Term.eqb_iff_joinKey]
  constructor
  · rintro ⟨⟨hs, hp⟩, ho⟩; exact ⟨Subject.eqb_eq hs, hp, ho⟩
  · rintro ⟨hs, hp, ho⟩; subst hs; exact ⟨⟨Subject.eqb_refl _, hp⟩, ho⟩

/-! ## Membership through keys -/

theorem Graph.mem_iff_exists (t : Triple) (g : Graph) :
    g.mem t = true ↔ ∃ u ∈ g, u.eqb t = true := by
  induction g with
  | nil => simp [Graph.mem]
  | cons hd tl ih => simp [Graph.mem, ih]

theorem Graph.mem_iff_key (t : Triple) (g : Graph) :
    g.mem t = true ↔ ∃ u ∈ g, u.key = t.key := by
  rw [Graph.mem_iff_exists]
  simp only [Triple.eqb_iff_key]

/-! ## A graph with the set of its keys -/

/-- The graph `base ++ rev.reverse` with the set of the keys of its triples.
`keys_ok` is erased at run time. -/
structure GraphIx where
  base : Graph
  rev : List Triple
  keys : Std.HashSet Triple
  keys_ok : ∀ k, keys.contains k = true ↔ ∃ u ∈ base ++ rev.reverse, u.key = k

/-- The graph a `GraphIx` holds. -/
def GraphIx.toGraph (x : GraphIx) : Graph := x.base ++ x.rev.reverse

/-- A set lookup of the key answers `Graph.mem`. -/
theorem GraphIx.contains_key (x : GraphIx) (t : Triple) :
    x.keys.contains t.key = x.toGraph.mem t := by
  apply Bool.eq_iff_iff.mpr
  rw [x.keys_ok, GraphIx.toGraph, Graph.mem_iff_key]

/-- Insert the key of every triple of `g` into `s`. -/
def GraphIx.insertKeys (s : Std.HashSet Triple) (g : Graph) : Std.HashSet Triple :=
  g.foldl (fun acc u => acc.insert u.key) s

theorem GraphIx.contains_insertKeys (s : Std.HashSet Triple) (g : Graph) (k : Triple) :
    (GraphIx.insertKeys s g).contains k = true ↔ s.contains k = true ∨ ∃ u ∈ g, u.key = k := by
  induction g generalizing s with
  | nil => simp [GraphIx.insertKeys]
  | cons hd tl ih =>
    simp only [GraphIx.insertKeys, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq, List.mem_cons,
      exists_eq_or_imp]
    constructor
    · rintro ((h | h) | h)
      · exact Or.inr (Or.inl h)
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exact Or.inl (Or.inr h)
      · exact Or.inl (Or.inl h)
      · exact Or.inr h

/-- The index of a graph: one pass over its triples. -/
def GraphIx.ofGraph (g : Graph) : GraphIx where
  base := g
  rev := []
  keys := GraphIx.insertKeys ∅ g
  keys_ok := by
    intro k
    rw [GraphIx.contains_insertKeys]
    simp

@[simp] theorem GraphIx.toGraph_ofGraph (g : Graph) : (GraphIx.ofGraph g).toGraph = g := by
  simp [GraphIx.ofGraph, GraphIx.toGraph]

/-- `Graph.add` on the index: a set lookup, then a cons onto `rev` and a set
insert. The structure is taken apart by the match, so the set is updated in
place when the `GraphIx` is not shared. -/
def GraphIx.add (t : Triple) : GraphIx → GraphIx
  | ⟨base, rev, keys, ok⟩ =>
    if keys.contains t.key then ⟨base, rev, keys, ok⟩
    else
      ⟨base, t :: rev, keys.insert t.key, by
        intro k
        rw [Std.HashSet.contains_insert, Bool.or_eq_true, ok]
        simp only [beq_iff_eq, List.reverse_cons, ← List.append_assoc, List.mem_append,
          List.mem_singleton]
        constructor
        · rintro (h | ⟨u, hu, hk⟩)
          · exact ⟨t, Or.inr rfl, h⟩
          · exact ⟨u, Or.inl hu, hk⟩
        · rintro ⟨u, hu | rfl, hk⟩
          · exact Or.inr ⟨u, hu, hk⟩
          · exact Or.inl hk⟩

/-- `GraphIx.add` is `Graph.add`: the same triples in the same order. -/
theorem GraphIx.toGraph_add (t : Triple) (x : GraphIx) :
    (x.add t).toGraph = x.toGraph.add t := by
  have hc := GraphIx.contains_key x t
  obtain ⟨base, rev, keys, ok⟩ := x
  unfold Graph.add
  by_cases h : keys.contains t.key = true
  · have hm : Graph.mem t (GraphIx.toGraph ⟨base, rev, keys, ok⟩) = true := hc ▸ h
    rw [if_pos hm]
    simp [GraphIx.add, h]
  · have hm : ¬ Graph.mem t (GraphIx.toGraph ⟨base, rev, keys, ok⟩) = true := hc ▸ h
    rw [if_neg hm]
    simp [GraphIx.add, h, GraphIx.toGraph]

/-! ## A graph slot whose index is made on the second add

A dataset keeps each graph a plain list until triples are added to it. The
first add is `Graph.add` itself (one scan and one copy, as before), and the
second makes the index, so a request that adds one triple to a large graph
does not pay for hashing the graph, and a request that adds many pays for it
once. -/

inductive GraphSlot where
  /-- No triple added yet. -/
  | plain (g : Graph)
  /-- One triple added, with `Graph.add`. -/
  | once (g : Graph)
  | ix (x : GraphIx)

def GraphSlot.toGraph : GraphSlot → Graph
  | .plain g => g
  | .once g => g
  | .ix x => x.toGraph

def GraphSlot.add (t : Triple) : GraphSlot → GraphSlot
  | .plain g => .once (g.add t)
  | .once g => .ix ((GraphIx.ofGraph g).add t)
  | .ix x => .ix (x.add t)

@[simp] theorem GraphSlot.toGraph_add (t : Triple) (s : GraphSlot) :
    (s.add t).toGraph = s.toGraph.add t := by
  cases s <;> simp [GraphSlot.add, GraphSlot.toGraph, GraphIx.toGraph_add]

@[simp] theorem GraphSlot.toGraph_plain (g : Graph) : (GraphSlot.plain g).toGraph = g := rfl

/-! ## `Graph.union` -/

/-- `Graph.union g1 g2` (every triple of `g2` added to `g1` with `Graph.add`)
through the index. -/
def Graph.unionFast (g1 g2 : Graph) : Graph :=
  (g2.foldl (fun acc t => acc.add t) (GraphIx.ofGraph g1)).toGraph

theorem GraphIx.toGraph_foldl_add (ts : List Triple) (x : GraphIx) :
    (ts.foldl (fun acc t => acc.add t) x).toGraph = ts.foldl (fun g t => g.add t) x.toGraph := by
  induction ts generalizing x with
  | nil => rfl
  | cons t ts ih => simp only [List.foldl_cons, ih, GraphIx.toGraph_add]

theorem Graph.union_eq_unionFast : @Graph.union = @Graph.unionFast := by
  funext g1 g2
  simp [Graph.union, Graph.unionFast, GraphIx.toGraph_foldl_add]

/-! ## Checks -/

private def gx : WfIri := ⟨"http://example.org/x", by decide⟩
private def gp : WfIri := ⟨"http://example.org/p", by decide⟩
private def tEn : Triple := ⟨.iri gx, gp, .literal (Literal.langString "a" "en")⟩
private def tEN : Triple := ⟨.iri gx, gp, .literal (Literal.langString "a" "EN")⟩
private def tB : Triple := ⟨.iri gx, gp, .literal (Literal.string "b")⟩

-- Tags that differ only in case are one triple for `Graph.add` and for the index.
#guard (Graph.unionFast [] [tEn, tEN, tB, tEn]) == [tEn, tB]
#guard (Graph.unionFast [] [tEn, tEN, tB, tEn]) == Graph.union [] [tEn, tEN, tB, tEn]
#guard (Graph.unionFast [tB] [tEN, tB]) == [tB, tEN]
-- A triple that is not in the graph is added at the end.
#guard ((GraphIx.ofGraph [tB]).add tEn).toGraph == [tB, tEn]
#guard ((GraphIx.ofGraph [tB]).add tB).toGraph == [tB]
#guard tEn.key == tEN.key
#guard tEn.key != tB.key

end L4Factoidal.RDF
