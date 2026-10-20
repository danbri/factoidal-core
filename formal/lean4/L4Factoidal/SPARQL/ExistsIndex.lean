/-
L4Factoidal.SPARQL.ExistsIndex — `exists(pattern, μ)` (SPARQL 1.1 §18.6)
for a basic graph pattern, by index lookup instead of graph scans.

https://github.com/danbri/factoidal/issues/881. A FILTER evaluates its
condition once for each row. For `FILTER NOT EXISTS { BGP }` the
reference lowering substitutes the row into the BGP and evaluates the
result with `evalBgpIdx` from the empty binding. That evaluator keeps
its index cache for ONE call only, and a call with one row scans the
graph (`evalBgpStepCached`, the `[mu]` case). So each row read the
whole active graph: 100,000 triples took 94 to 247 s.

`ExistsIndex` holds the active graph and one LAZY index for each of
the seven non-empty position masks (`TpMask`). A `Thunk` builds an
index the first time a pattern needs that mask and keeps it, so the
indexes are built at most once for all the rows of a FILTER. The
lowering (`QueryPattern.lowerWith`, `.filter` arm) builds one
`ExistsIndex` for each active graph and gives it to each row.

The theorems:

  * `ExistsIndex.evalTP_ofGraph` : the indexed one-pattern step is
    `evalTP` (from `evalTPIdx_eq`).
  * `ExistsIndex.bgpNonempty_ofGraph` : the indexed test is
    `!(evalBgpFrom g b mu).isEmpty`, the §18.6 condition "the result is
    not the empty multiset" for the substituted BGP.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.IndexedEvalRefinement

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-- The seven position masks that key an index. The all-false mask is
not in the list: a pattern with no pinned position scans the graph. -/
def existsIndexMasks : List TpMask :=
  [ ⟨true, true, true⟩, ⟨true, true, false⟩, ⟨true, false, true⟩,
    ⟨false, true, true⟩, ⟨true, false, false⟩, ⟨false, true, false⟩,
    ⟨false, false, true⟩ ]

/-- The active graph with one lazy index for each mask of
`existsIndexMasks`. -/
structure ExistsIndex where
  graph : Graph
  table : List (TpMask × Thunk (Std.HashMap (List Term) Graph))

/-- No index is built here: each one is built when a pattern first
needs its mask, and kept for the next row. -/
def ExistsIndex.ofGraph (g : Graph) : ExistsIndex :=
  { graph := g
  , table := existsIndexMasks.map fun m =>
      (m, Thunk.mk fun _ => groupByKey (tripleKey m) g) }

/-- The positions of `tp` that μ pins: a constant, or a bound variable. -/
def tpMaskFor (tp : TriplePattern) (mu : Binding) : TpMask :=
  { s := (tp.s.resolveKey mu).isSome
  , p := (tp.p.resolveKey mu).isSome
  , o := (tp.o.resolveKey mu).isSome }

/-- All extensions of μ by `tp`: a probe of the index of μ's mask, or a
scan when no position is pinned. -/
def ExistsIndex.evalTP (ix : ExistsIndex) (tp : TriplePattern) (mu : Binding) :
    SolutionSeq :=
  let m := tpMaskFor tp mu
  match ix.table.find? (fun e => e.1 == m) with
  | some e => evalTPIdx e.1 e.2.get ix.graph tp mu
  | none => SPARQL.evalTP tp ix.graph mu

/-- Does the BGP have a solution that extends μ? Depth first; stops at
the first complete match. -/
def ExistsIndex.bgpNonempty (ix : ExistsIndex) : Bgp → Binding → Bool
  | [], _ => true
  | tp :: rest, mu => (ix.evalTP tp mu).any (fun mu2 => ix.bgpNonempty rest mu2)

theorem ExistsIndex.evalTP_ofGraph (g : Graph) (tp : TriplePattern) (mu : Binding) :
    (ExistsIndex.ofGraph g).evalTP tp mu = SPARQL.evalTP tp g mu := by
  unfold ExistsIndex.evalTP
  simp only
  split
  · rename_i e he
    have hmem := List.mem_of_find?_eq_some he
    simp only [ExistsIndex.ofGraph, List.mem_map] at hmem
    obtain ⟨m, _, hm⟩ := hmem
    subst hm
    exact evalTPIdx_eq m g tp mu
  · rfl

private theorem any_flatMap_isEmpty {α β : Type} (f : α → List β) :
    ∀ (l : List α), (l.flatMap f).isEmpty = !(l.any fun a => !(f a).isEmpty)
  | [] => rfl
  | a :: rest => by
      have ih := any_flatMap_isEmpty f rest
      rw [List.flatMap_cons, List.any_cons]
      cases h : f a with
      | nil => simpa using ih
      | cons x xs => simp

/-- The indexed test is the §18.6 condition: the BGP evaluated from μ
has at least one solution. -/
theorem ExistsIndex.bgpNonempty_ofGraph (g : Graph) :
    ∀ (b : Bgp) (mu : Binding),
      (ExistsIndex.ofGraph g).bgpNonempty b mu = !(evalBgpFrom g b mu).isEmpty
  | [], _ => rfl
  | tp :: rest, mu => by
      rw [ExistsIndex.bgpNonempty, evalBgpFrom, ExistsIndex.evalTP_ofGraph,
        any_flatMap_isEmpty]
      simp only [Bool.not_not]
      congr 1
      funext mu2
      exact ExistsIndex.bgpNonempty_ofGraph g rest mu2

#print axioms ExistsIndex.bgpNonempty_ofGraph

/-! Build-time checks, positive and negative: a bound subject with and
without a match, a repeated variable, language-tag case. -/
private def eA : WfIri := ⟨"urn:a", rfl⟩
private def eB : WfIri := ⟨"urn:b", rfl⟩
private def eP : WfIri := ⟨"urn:p", rfl⟩
private def eG : Graph :=
  [⟨.iri eA, eP, .iri eB⟩, ⟨.iri eB, eP, .iri eB⟩,
   ⟨.iri eA, eP, .literal (Literal.langString "chat" "en")⟩]
private def eIx := ExistsIndex.ofGraph eG
#guard eIx.bgpNonempty [⟨.iri eA, .iri eP, .var "o"⟩] []
#guard !eIx.bgpNonempty [⟨.iri eP, .iri eP, .var "o"⟩] []
#guard eIx.bgpNonempty [⟨.var "x", .iri eP, .var "x"⟩] []
#guard !(ExistsIndex.ofGraph [⟨.iri eA, eP, .iri eB⟩]).bgpNonempty [⟨.var "x", .iri eP, .var "x"⟩] []
#guard eIx.bgpNonempty [⟨.iri eA, .iri eP, .literal (Literal.langString "chat" "EN")⟩] []
#guard !eIx.bgpNonempty [⟨.iri eA, .iri eP, .iri eA⟩] []
#guard eIx.bgpNonempty [⟨.iri eA, .iri eP, .var "o"⟩, ⟨.var "o", .iri eP, .iri eB⟩] []
#guard !eIx.bgpNonempty [⟨.iri eB, .iri eP, .var "o"⟩, ⟨.var "o", .iri eP, .iri eA⟩] []

end L4Factoidal.SPARQL
