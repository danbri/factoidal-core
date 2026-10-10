/-
L4Factoidal.RDF.FastGraph — a graph under construction with a hash index,
and the proof that it denotes the same graph as the list operations.

`Graph.add` (RDF/Graph.lean) is `if g.mem t then g else g ++ [t]`: a linear
`Graph.mem` scan under the engine triple equality `Triple.eqb`, then a linear
append. Folding it over n triples costs O(n^2). This module keeps the SAME
set semantics with an accumulator that costs O(1) per triple:

- `FastGraph` keeps the triples in reverse insertion order plus a hash map from
  a bucket key to the triples that carry it. The key is the subject and the
  predicate structurally and the object's `Term.joinKey`; `Term.joinKey` is
  constant on `Term.eqb` classes (`Term.joinKey_eq_of_eqb`), and `Subject.eqb`
  and `WfIri` equality are structural, so two `Triple.eqb`-equal triples always
  share a bucket. Membership is decided by `Triple.eqb` INSIDE the bucket,
  exactly as `Graph.mem` decides it over the whole graph: the key only narrows
  the candidates and never decides equality.
- `FastGraph.Inv` states that every bucket holds exactly the accumulated
  triples with that key. `FastGraph.add_toGraph` then says the indexed add
  refines `Graph.add` on the denoted graph.

The module was moved out of `Syntax/NQuadsFast.lean` and
`Syntax/NQuadsFastTheorems.lean` on 2026-10-10 so that the RDFS closure
(`RDFS/Closure.lean`) can use the same accumulator without depending on the
N-Quads lexer. The definitions and proofs of `FastGraph.add` and
`FastGraph.add_toGraph` are unchanged; `FastGraph.push`, `FastGraph.ofGraph`
and `FastGraph.addAll` are new.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.RDF.Graph
import Std.Data.HashMap

namespace L4Factoidal.RDF

/-- Bucket key: subject and predicate structurally, object by `joinKey`. -/
abbrev TripleKey := Subject × WfIri × Term

def tripleKey (t : Triple) : TripleKey := (t.s, t.p, t.o.joinKey)

/-- A graph under construction: reverse insertion order plus buckets. -/
structure FastGraph where
  rev : List Triple := []
  buckets : Std.HashMap TripleKey (List Triple) := ∅

/-- Set-semantics add with bucketed `Triple.eqb` membership — the fast twin
    of `Graph.add t` (which is `if g.mem t then g else g ++ [t]`). -/
def FastGraph.add (t : Triple) (g : FastGraph) : FastGraph :=
  let k := tripleKey t
  let bucket := g.buckets.getD k []
  if bucket.any (fun u => u.eqb t) then g
  else { rev := t :: g.rev, buckets := g.buckets.insert k (t :: bucket) }

/-- Append WITHOUT the membership test: the denotation of a list that may
    already hold duplicates, which `Graph.add` leaves in place. -/
def FastGraph.push (t : Triple) (g : FastGraph) : FastGraph :=
  let k := tripleKey t
  { rev := t :: g.rev, buckets := g.buckets.insert k (t :: g.buckets.getD k []) }

def FastGraph.toGraph (g : FastGraph) : Graph := g.rev.reverse

/-- Index a list as it stands, duplicates included. -/
def FastGraph.ofGraph (g : Graph) : FastGraph :=
  g.foldl (fun acc t => acc.push t) {}

/-- Add a list of triples set-wise, in order — the fast twin of folding
    `Graph.add` (`RDFS.addAll`). -/
def FastGraph.addAll (g : FastGraph) (ts : List Triple) : FastGraph :=
  ts.foldl (fun acc t => acc.add t) g

/-! ## Bucket keys -/

/-- `Triple.eqb`-equal triples carry the same bucket key, so a bucket
lookup never hides a match. -/
theorem tripleKey_eq_of_eqb {a b : Triple} (h : Triple.eqb a b = true) :
    tripleKey a = tripleKey b := by
  simp only [Triple.eqb, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hs, hp⟩, ho⟩ := h
  simp only [tripleKey, Prod.mk.injEq]
  exact ⟨Subject.eqb_eq hs, hp, Term.joinKey_eq_of_eqb ho⟩

/-- `Graph.mem` is the `Triple.eqb` scan of the list. -/
theorem graphMem_eq_any (t : Triple) :
    ∀ g : Graph, Graph.mem t g = g.any (fun u => u.eqb t)
  | [] => rfl
  | hd :: tl => by
      simp only [Graph.mem, List.any_cons, graphMem_eq_any t tl]

/-! ## The graph invariant -/

/-- Every bucket holds exactly the accumulated triples with that key. -/
def FastGraph.Inv (g : FastGraph) : Prop :=
  ∀ key, g.buckets.getD key [] = g.rev.filter (fun u => tripleKey u == key)

theorem FastGraph.inv_empty : FastGraph.Inv {} := by
  intro key
  simp

theorem FastGraph.add_inv {g : FastGraph} {t : Triple} (h : g.Inv) :
    (g.add t).Inv := by
  intro key
  simp only [FastGraph.add]
  split
  · exact h key
  · simp only [Std.HashMap.getD_insert, List.filter_cons]
    by_cases hk : (tripleKey t == key) = true
    · have hk' : tripleKey t = key := eq_of_beq hk
      subst hk'
      simp [h (tripleKey t)]
    · simp only [Bool.not_eq_true] at hk
      simp [hk, h key]

theorem FastGraph.push_inv {g : FastGraph} {t : Triple} (h : g.Inv) :
    (g.push t).Inv := by
  intro key
  simp only [FastGraph.push, Std.HashMap.getD_insert, List.filter_cons]
  by_cases hk : (tripleKey t == key) = true
  · have hk' : tripleKey t = key := eq_of_beq hk
    subst hk'
    simp [h (tripleKey t)]
  · simp only [Bool.not_eq_true] at hk
    simp [hk, h key]

/-- The bucket scan and the whole-graph scan answer the same membership
question. -/
theorem FastGraph.bucket_any {g : FastGraph} (t : Triple) (h : g.Inv) :
    (g.buckets.getD (tripleKey t) []).any (fun u => u.eqb t)
      = g.rev.any (fun u => u.eqb t) := by
  rw [h (tripleKey t), Bool.eq_iff_iff]
  simp only [List.any_eq_true, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨u, ⟨hu, -⟩, hp⟩
    exact ⟨u, hu, hp⟩
  · rintro ⟨u, hu, hp⟩
    exact ⟨u, ⟨hu, tripleKey_eq_of_eqb hp⟩, hp⟩

/-- The indexed add refines `Graph.add` on the denoted graph. -/
theorem FastGraph.add_toGraph {g : FastGraph} (t : Triple) (h : g.Inv) :
    (g.add t).toGraph = Graph.add t g.toGraph := by
  have hb := FastGraph.bucket_any t h
  simp only [FastGraph.add, FastGraph.toGraph, Graph.add,
    graphMem_eq_any, List.any_reverse]
  rw [hb]
  split
  · rfl
  · simp

/-! ## Building from a list, and adding a list -/

theorem FastGraph.ofGraph_foldl_inv (g : Graph) :
    ∀ acc : FastGraph, acc.Inv → (g.foldl (fun a t => a.push t) acc).Inv := by
  induction g with
  | nil => intro acc h; exact h
  | cons t ts ih =>
      intro acc h
      exact ih (acc.push t) (FastGraph.push_inv h)

theorem FastGraph.ofGraph_inv (g : Graph) : (FastGraph.ofGraph g).Inv :=
  FastGraph.ofGraph_foldl_inv g {} FastGraph.inv_empty

theorem FastGraph.ofGraph_foldl_rev (g : Graph) :
    ∀ acc : FastGraph, (g.foldl (fun a t => a.push t) acc).rev = g.reverse ++ acc.rev := by
  induction g with
  | nil => intro acc; simp
  | cons t ts ih =>
      intro acc
      rw [List.foldl_cons, ih (acc.push t)]
      simp [FastGraph.push]

/-- Indexing a list denotes the list itself, duplicates and order included. -/
theorem FastGraph.ofGraph_toGraph (g : Graph) : (FastGraph.ofGraph g).toGraph = g := by
  simp [FastGraph.ofGraph, FastGraph.toGraph, FastGraph.ofGraph_foldl_rev]

/-- The set-wise add of a list: the left fold of `Graph.add`, as
`RDFS.addAll` states it. -/
def graphAddAll (g : Graph) : List Triple → Graph
  | []      => g
  | t :: ts => graphAddAll (g.add t) ts

theorem FastGraph.addAll_inv (ts : List Triple) :
    ∀ g : FastGraph, g.Inv → (g.addAll ts).Inv := by
  induction ts with
  | nil => intro g h; exact h
  | cons t ts ih =>
      intro g h
      exact ih (g.add t) (FastGraph.add_inv h)

/-- The indexed set-wise add refines the left fold of `Graph.add`. -/
theorem FastGraph.addAll_toGraph (ts : List Triple) :
    ∀ g : FastGraph, g.Inv → (g.addAll ts).toGraph = graphAddAll g.toGraph ts := by
  induction ts with
  | nil => intro g h; rfl
  | cons t ts ih =>
      intro g h
      show (FastGraph.addAll (g.add t) ts).toGraph = graphAddAll (Graph.add t g.toGraph) ts
      rw [ih (g.add t) (FastGraph.add_inv h), FastGraph.add_toGraph t h]

end L4Factoidal.RDF
