/-
L4Factoidal.RDFS.SemiNaive — delta evaluation for the RDFS closure.

Port of `formal/fstar/RDFS.Closure.SemiNaive.fst` (421 lines).

## What is wrong with the naive loop

`RDFS.Closure.step` re-applies all six rows to the WHOLE graph every
round. A triple derived in round 1 is re-derived and re-deduplicated in
rounds 2, 3, … r. The answer is produced r times and discarded r-1
times.

Semi-naive evaluation (Bancilhon and Ramakrishnan 1986) applies a rule
only where at least one premise is NEW. For a two-premise rule with
bodies B1 and B2, the round-k+1 work is

    Δout = (ΔB1 ⋈ B2_full) ∪ (B1_full ⋈ ΔB2)

Both terms are needed; dropping either loses derivations. The cross
term ΔB1 ⋈ ΔB2 is covered twice, harmlessly, because the full graph
contains the delta.

Every row here is `RDFS.Closure`'s own row function applied to a SUBSET
of its inputs, so this module can only derive triples the naive loop
also derives. It is sound by construction, and the only way it can be
wrong is by deriving too FEW.

## Why a hole here costs speed, never correctness

`closureSemiNaiveChecked` runs the delta loop and then applies ONE full
naive `step` to the result.

- If that step adds nothing, the result is a fixed point of the naive
  step that contains the input graph. The naive closure is the LEAST
  such fixed point, so it is contained in this one; and this one is
  contained in it by soundness. The two are equal, and the fast answer
  is returned.
- If that step adds something, the delta loop missed a derivation. The
  result is discarded and the untouched `closureFix` runs.

This is the same discipline as `RDFS.SchemaSplit`'s post-hoc check, for
the same reason: confident reasoning about this rule set has been wrong
repeatedly. Issue #340 item 4 proposed hoisting five rows out of the
loop; all five turned out to be recursive.

`RDFS.Closure` is unchanged. The naive loop stays the reference
implementation and the fallback.

## Differences from the F\*

1. The F\* module reads premises through `RDF.Indexed`'s buckets and
   needs `sorted_diff` over `graph_dedup_sort` output to compute the
   delta in one linear merge. `L4Factoidal.RDFS.Closure` states its
   rows against plain list scans (its own header records that choice),
   so the delta here is STATED as a filter against the previous round.
   Since 2026-10-12 the compiled code reads premises through
   `RDFS.Closure`'s `StepIndex` and takes the delta as the suffix the
   round appended (section "Indexed evaluation of the same rounds"),
   with proofs that both give the same lists. Measured times are in
   `docs/designissues/2026-10-12-rdfs-seminaive.md`.
2. The F\* module writes the delta term for each of the twelve rows by
   hand. Every row of `RDFS.Closure` has the shape
   `Graph → Triple → List Triple`, second premise first, so one
   combinator (`rowDelta`) states the delta term once for all six.
-/
import L4Factoidal.RDFS.Closure

namespace L4Factoidal.RDFS

open L4Factoidal.RDF

/-! ## The delta -/

/-- Triples of `newG` that `oldG` does not hold. The F\* module gets
    this from a linear merge of two sorted, deduplicated graphs; here
    it is a membership filter, which has the same answer. -/
def graphDiff (newG oldG : Graph) : Graph :=
  newG.filter (fun t => !(oldG.any (fun u => u.eqb t)))

/-! ## One delta round

Both terms of `Δout = (ΔB1 ⋈ B2_full) ∪ (B1_full ⋈ ΔB2)`. Every row of
`RDFS.Closure` takes the graph it searches for its SECOND premise
first and the triple that is its FIRST premise second, so
`delta.flatMap (row g)` is the left term and `g.flatMap (row delta)`
is the right one. -/

def rowDelta (row : Graph → Triple → List Triple) (delta g : Graph) : List Triple :=
  delta.flatMap (row g) ++ g.flatMap (row delta)

/-- Everything the six rows conclude when at least one premise is in
    `delta`. Same row order as `stepConclusions`. -/
def deltaConclusions (delta g : Graph) : List Triple :=
  rowDelta rdfs7For delta g ++
  rowDelta rdfs2For delta g ++
  rowDelta rdfs3For delta g ++
  rowDelta rdfs9For delta g ++
  rowDelta rdfs11For delta g ++
  rowDelta rdfs5For delta g

/-! ## The loop -/

/-- Fuel-bounded delta loop. `g` is everything derived so far, `delta`
    is what the previous round added. Stops when a round adds
    nothing. -/
def semiNaiveLoop (g delta : Graph) : Nat → Graph
  | 0     => g
  | n + 1 =>
      if delta.isEmpty then g
      else
        let g' := addAll g (deltaConclusions delta g)
        if g'.length = g.length then g
        else semiNaiveLoop g' (graphDiff g' g) n

/-! ## Indexed evaluation of the same rounds (2026-10-12)

`deltaConclusions` reads premises through `RDFS.Closure`'s list scans,
`addAll` tests membership with a scan of the graph, and `graphDiff`
scans the old graph once per triple of the new one. Each round
therefore costs O(|g|^2), the cost the naive loop had before
`RDFS.Closure`'s indexed section. This section computes the SAME rounds
with the same indexes and proves it, in the pattern of `closureFast`:

* `deltaConclusionsIx` reads the second premise of the left delta term
  from `StepIndex.build g` and that of the right term from
  `StepIndex.build delta`; `deltaConclusionsIx_eq` proves it equal to
  `deltaConclusions` as a LIST, from `RDFS.Closure`'s `rdfs7ForIx_eq` ..
  `rdfs5ForIx_eq`.
* `Graph.add` only appends, so the triples a round adds are the suffix of
  the new graph after the old one, and none of them is in the old graph
  up to `Triple.eqb`; `graphDiff_addAll` proves that `graphDiff` is
  that suffix (`List.drop`).
* `semiNaiveLoopFast` is `semiNaiveLoop` with those two changes and
  `FastGraph.addAll`; `semiNaiveLoopFast_eq` proves the two equal, and
  `semiNaiveLoop_eq_fast` is registered `@[csimp]`, so `semiNaive` and
  every later caller compile to the indexed loop. The definition of
  `semiNaiveLoop`, and every theorem stated about it
  (`RDFS.SemiNaiveTheorems`), is unchanged. -/

/-- `deltaConclusions` with the second premise read from indexes. -/
def deltaConclusionsIx (delta g : Graph) : List Triple :=
  let ixG := StepIndex.build g
  let ixD := StepIndex.build delta
  (delta.flatMap (rdfs7ForIx ixG) ++ g.flatMap (rdfs7ForIx ixD)) ++
  (delta.flatMap (rdfs2ForIx ixG) ++ g.flatMap (rdfs2ForIx ixD)) ++
  (delta.flatMap (rdfs3ForIx ixG) ++ g.flatMap (rdfs3ForIx ixD)) ++
  (delta.flatMap (rdfs9ForIx ixG) ++ g.flatMap (rdfs9ForIx ixD)) ++
  (delta.flatMap (rdfs11ForIx ixG) ++ g.flatMap (rdfs11ForIx ixD)) ++
  (delta.flatMap (rdfs5ForIx ixG) ++ g.flatMap (rdfs5ForIx ixD))

theorem deltaConclusionsIx_eq (delta g : Graph) :
    deltaConclusionsIx delta g = deltaConclusions delta g := by
  have h7g : rdfs7ForIx (StepIndex.build g) = rdfs7For g := funext (rdfs7ForIx_eq g)
  have h2g : rdfs2ForIx (StepIndex.build g) = rdfs2For g := funext (rdfs2ForIx_eq g)
  have h3g : rdfs3ForIx (StepIndex.build g) = rdfs3For g := funext (rdfs3ForIx_eq g)
  have h9g : rdfs9ForIx (StepIndex.build g) = rdfs9For g := funext (rdfs9ForIx_eq g)
  have h11g : rdfs11ForIx (StepIndex.build g) = rdfs11For g := funext (rdfs11ForIx_eq g)
  have h5g : rdfs5ForIx (StepIndex.build g) = rdfs5For g := funext (rdfs5ForIx_eq g)
  have h7d : rdfs7ForIx (StepIndex.build delta) = rdfs7For delta := funext (rdfs7ForIx_eq delta)
  have h2d : rdfs2ForIx (StepIndex.build delta) = rdfs2For delta := funext (rdfs2ForIx_eq delta)
  have h3d : rdfs3ForIx (StepIndex.build delta) = rdfs3For delta := funext (rdfs3ForIx_eq delta)
  have h9d : rdfs9ForIx (StepIndex.build delta) = rdfs9For delta := funext (rdfs9ForIx_eq delta)
  have h11d : rdfs11ForIx (StepIndex.build delta) = rdfs11For delta :=
    funext (rdfs11ForIx_eq delta)
  have h5d : rdfs5ForIx (StepIndex.build delta) = rdfs5For delta := funext (rdfs5ForIx_eq delta)
  simp only [deltaConclusionsIx, deltaConclusions, rowDelta]
  rw [h7g, h2g, h3g, h9g, h11g, h5g, h7d, h2d, h3d, h9d, h11d, h5d]

/-- `addAll` appends: the result is the input followed by triples the
input does not hold, up to `Triple.eqb`. -/
theorem addAll_eq_append (ts : List Triple) :
    ∀ g : Graph, ∃ suf : List Triple, addAll g ts = g ++ suf ∧
      ∀ u, u ∈ suf → Graph.mem u g = false := by
  induction ts with
  | nil => intro g; exact ⟨[], by simp [addAll], by simp⟩
  | cons t ts ih =>
    intro g
    obtain ⟨suf, he, hsuf⟩ := ih (g.add t)
    by_cases hm : Graph.mem t g = true
    · have hadd : g.add t = g := by simp [Graph.add, hm]
      refine ⟨suf, ?_, ?_⟩
      · simp only [addAll]; rw [he, hadd]
      · intro u hu; have := hsuf u hu; rwa [hadd] at this
    · have hadd : g.add t = g ++ [t] := by simp [Graph.add, hm]
      refine ⟨t :: suf, ?_, ?_⟩
      · simp only [addAll]; rw [he, hadd]; simp
      · intro u hu
        rcases List.mem_cons.mp hu with rfl | hu'
        · simpa using hm
        · have := hsuf u hu'
          rw [hadd, Graph.mem_append] at this
          simp only [Bool.or_eq_false_iff] at this
          exact this.1

/-- The delta of a round is the suffix the round appended. -/
theorem graphDiff_addAll (g : Graph) (ts : List Triple) :
    graphDiff (addAll g ts) g = (addAll g ts).drop g.length := by
  obtain ⟨suf, he, hsuf⟩ := addAll_eq_append ts g
  rw [he, List.drop_left]
  have hl : g.filter (fun t => !(g.any (fun u => u.eqb t))) = [] := by
    rw [List.filter_eq_nil_iff]
    intro t ht
    simp only [Bool.not_eq_true', Bool.not_eq_false, List.any_eq_true]
    exact ⟨t, ht, Triple.eqb_refl t⟩
  have hr : suf.filter (fun t => !(g.any (fun u => u.eqb t))) = suf := by
    rw [List.filter_eq_self]
    intro u hu
    have := hsuf u hu
    rw [graphMem_eq_any] at this
    simp [this]
  simp only [graphDiff, List.filter_append, hl, hr, List.nil_append]

/-- `semiNaiveLoop` with indexed premises, bucketed membership and the
appended suffix as the delta. -/
def semiNaiveLoopFast (g delta : Graph) : Nat → Graph
  | 0     => g
  | n + 1 =>
      if delta.isEmpty then g
      else
        let g' := ((FastGraph.ofGraph g).addAll (deltaConclusionsIx delta g)).toGraph
        if g'.length = g.length then g
        else semiNaiveLoopFast g' (g'.drop g.length) n

theorem semiNaiveLoopFast_eq (n : Nat) :
    ∀ g delta : Graph, semiNaiveLoopFast g delta n = semiNaiveLoop g delta n := by
  induction n with
  | zero => intro g delta; rfl
  | succ n ih =>
    intro g delta
    have hstep : ((FastGraph.ofGraph g).addAll (deltaConclusionsIx delta g)).toGraph
        = addAll g (deltaConclusions delta g) := by
      rw [FastGraph.addAll_toGraph _ _ (FastGraph.ofGraph_inv g), FastGraph.ofGraph_toGraph,
        deltaConclusionsIx_eq, addAll_eq_graphAddAll]
    simp only [semiNaiveLoopFast, semiNaiveLoop, hstep]
    split
    · rfl
    · split
      · rfl
      · rw [ih, graphDiff_addAll]

/-- The compiler emits `semiNaiveLoopFast` for every later call of
`semiNaiveLoop`. -/
@[csimp] theorem semiNaiveLoop_eq_fast : @semiNaiveLoop = @semiNaiveLoopFast := by
  funext g delta n
  exact (semiNaiveLoopFast_eq n g delta).symm

/-- The delta closure. The first round has no previous delta, so the
    whole graph is the delta — which makes round 1 exactly one naive
    step, as it must be. -/
def semiNaive (g : Graph) : Graph :=
  semiNaiveLoop g g (closureFuelBound g)

/-! ## The checked entry point

The only one callers should use. Its result is `closureFix g` whenever
the delta loop is not a fixed point of the naive step, so a hole in the
delta reasoning above costs a slow run, not a wrong answer. -/

/-- Does one full naive step add nothing to `h`? Decidable, and this is
    the whole safety argument. -/
def isNaiveFixpoint (h : Graph) : Bool :=
  (stepConclusions h).all (fun t => h.any (fun u => u.eqb t))

/-- `isNaiveFixpoint` with the indexed conclusions and the bucketed
membership test. -/
def isNaiveFixpointFast (h : Graph) : Bool :=
  let fg := FastGraph.ofGraph h
  (stepConclusionsIx h).all (fun t => (fg.buckets.getD (tripleKey t) []).any (fun u => u.eqb t))

theorem isNaiveFixpointFast_eq (h : Graph) : isNaiveFixpointFast h = isNaiveFixpoint h := by
  have hb : ∀ t, ((FastGraph.ofGraph h).buckets.getD (tripleKey t) []).any (fun u => u.eqb t)
      = h.any (fun u => u.eqb t) := by
    intro t
    rw [FastGraph.bucket_any t (FastGraph.ofGraph_inv h), FastGraph.ofGraph,
      FastGraph.ofGraph_foldl_rev]
    simp [List.any_reverse]
  simp only [isNaiveFixpointFast, isNaiveFixpoint, stepConclusionsIx_eq, hb]

/-- The compiler emits `isNaiveFixpointFast` for every later call of
`isNaiveFixpoint`. -/
@[csimp] theorem isNaiveFixpoint_eq_fast : @isNaiveFixpoint = @isNaiveFixpointFast := by
  funext h
  exact (isNaiveFixpointFast_eq h).symm

def closureSemiNaiveChecked (g : Graph) : Graph :=
  let fast := semiNaive g
  if isNaiveFixpoint fast then fast else closureFix g

/-! ## Build-time checks

Set equality, not list equality: the two loops add triples in different
orders, and a graph is a set (`RDF.Graph`). -/

def sameGraph (a b : Graph) : Bool :=
  a.all (fun t => b.any (fun u => u.eqb t)) &&
  b.all (fun t => a.any (fun u => u.eqb t))

private theorem exIri (s : String) : isIri ("http://e/" ++ s) = true := by
  simp [isIri, String.isEmpty]

private def i (s : String) : WfIri := ⟨"http://e/" ++ s, exIri s⟩
private def si (s : String) : Subject := .iri (i s)
private def ti (s : String) : Term := .iri (i s)
private def tr (s p o : String) : Triple := ⟨si s, i p, ti o⟩
private def typ : WfIri := rdfType
private def sco : WfIri := rdfsSubClassOf
private def spo : WfIri := rdfsSubPropertyOf

/-- A subclass chain: the case issue #340 is about, where the naive
    loop is O(n³) and re-derives every earlier round's answer. -/
def chain : Graph :=
  [ ⟨si "a", typ, ti "C1"⟩,
    ⟨si "C1", sco, ti "C2"⟩,
    ⟨si "C2", sco, ti "C3"⟩,
    ⟨si "C3", sco, ti "C4"⟩,
    ⟨si "C4", sco, ti "C5"⟩ ]

/-- A property hierarchy with a domain and a range, so rdfs7, rdfs2,
    rdfs3 and rdfs5 all fire. -/
def schema : Graph :=
  [ ⟨si "p", spo, ti "q"⟩,
    ⟨si "q", spo, ti "r"⟩,
    ⟨si "r", rdfsDomain, ti "D"⟩,
    ⟨si "r", rdfsRange, ti "R"⟩,
    ⟨si "x", i "p", ti "y"⟩,
    ⟨si "D", sco, ti "DSuper"⟩ ]

/-- A cycle, where a delta loop that stops one round early loses
    derivations. -/
def cyc : Graph :=
  [ ⟨si "A", sco, ti "B"⟩,
    ⟨si "B", sco, ti "A"⟩,
    ⟨si "z", typ, ti "A"⟩ ]

#guard sameGraph (closureSemiNaiveChecked chain) (closureFix chain)
#guard sameGraph (closureSemiNaiveChecked schema) (closureFix schema)
#guard sameGraph (closureSemiNaiveChecked cyc) (closureFix cyc)
#guard sameGraph (closureSemiNaiveChecked []) (closureFix [])

/-! The delta loop must reach the fixed point on its own on these — if
    the fallback fired, the guards above would still pass while the
    module did nothing. That is the vacuous-pass shape anti-pattern #3
    warns about, so it is checked separately. -/

#guard isNaiveFixpoint (semiNaive chain)
#guard isNaiveFixpoint (semiNaive schema)
#guard isNaiveFixpoint (semiNaive cyc)
#guard isNaiveFixpoint (semiNaive [])

/-! And the closures are not trivial: the chain must gain four
    `rdf:type` triples and six transitive `rdfs:subClassOf` triples, so
    a loop that derived nothing could not pass. -/

#guard (closureFix chain).length > chain.length
#guard (semiNaive chain).length == (closureFix chain).length
#guard (semiNaive schema).length == (closureFix schema).length
#guard (semiNaive cyc).length == (closureFix cyc).length

/-! `isNaiveFixpoint` has teeth: it must REJECT a graph that is not
    closed, or the check above proves nothing. -/

#guard !isNaiveFixpoint chain
#guard !isNaiveFixpoint schema
#guard isNaiveFixpoint []

/-! `graphDiff` is the delta, not something that happens to be
    non-empty. -/

#guard (graphDiff (step chain) chain).length > 0
#guard (graphDiff chain chain).length == 0
#guard (graphDiff chain []).length == chain.length

end L4Factoidal.RDFS
