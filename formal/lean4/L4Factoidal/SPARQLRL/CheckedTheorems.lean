/-
Actual-round preservation and fail-closed checked SPARQL-RL saturation.
Issue: https://github.com/danbri/factoidal-core/issues/745.
-/
import L4Factoidal.SPARQLRL.Checked

namespace L4Factoidal.SPARQLRL.Checked

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-- Definitional refactoring identity.
Says: extracting `generalRound` preserves the exact pre-extraction body of
one ordinary semi-naive round, including ordering and counters.
Does not say: semi-naive and naive evaluation are universally equivalent. -/
theorem generalRound_original (cx : Ctx) (pfx : String) (rules : List Rule)
    (first : Bool) (ge delta : IGraph) (ctr : Nat) :
    generalRound cx pfx rules first ge delta ctr =
      (let full : Nat → Src := fun _ => ⟨ge, none⟩
       let (out, ctr') := rules.foldl (fun (acc, c) r =>
         let sols :=
           if first then evalBody cx r ge full
           else if !r.evaldata then []
           else (List.range (countTriples r.body)).flatMap fun k =>
             evalBody cx r ge (fun i =>
               if i < k then ⟨ge, some delta⟩ else if i == k then ⟨delta, none⟩ else ⟨ge, none⟩)
         let (ts, c') := instHead r pfx c sols
         (acc ++ ts, c')) (#[], ctr)
       let delta' : IGraph := out.foldl (fun d t => if ge.contains t then d else d.insert t) {}
       (delta', ctr')) := rfl

/-- Exact explicit-fuel refinement.
Says: successful bounded progress is exactly the existing semi-naive loop
at the same supplied fuel, including insertion order and counter.
Does not say: progress success is saturation or that automatic fuel suffices. -/
theorem progress_agrees {maxTriples fuel : Nat} {cx : Ctx} {pfx : String}
    {rules : List Rule} {first : Bool} {ge delta : IGraph} {ctr : Nat}
    {out : IGraph × Nat}
    (h : progress maxTriples cx pfx rules fuel first ge delta ctr = .ok out) :
    L4Factoidal.SPARQLRL.generalLoop cx pfx rules fuel first ge delta ctr = out := by
  induction fuel generalizing first ge delta ctr with
  | zero =>
      simp only [progress] at h
      split at h
      · cases h
      · exact Except.ok.inj h
  | succ fuel ih =>
      simp only [progress] at h
      split at h
      · cases h
      · simp only [L4Factoidal.SPARQLRL.generalLoop]
        split at h
        · rename_i hzero
          simp only [hzero, ↓reduceIte]
          exact Except.ok.inj h
        · rename_i hnonzero
          simp only [hnonzero]
          split at h
          · cases h
          · exact ih h

/-- Retained-state resource invariant.
Says: successful bounded progress fits the configured triple cap.
Does not say: intermediate rule solutions or peak allocation fit that cap. -/
theorem progress_bounded {maxTriples fuel : Nat} {cx : Ctx} {pfx : String}
    {rules : List Rule} {first : Bool} {ge delta : IGraph} {ctr : Nat}
    {out : IGraph × Nat}
    (h : progress maxTriples cx pfx rules fuel first ge delta ctr = .ok out) :
    out.1.size ≤ maxTriples := by
  induction fuel generalizing first ge delta ctr with
  | zero =>
      simp only [progress] at h
      split at h
      · cases h
      · rename_i hsize
        cases h
        exact Nat.le_of_not_gt hsize
  | succ fuel ih =>
      simp only [progress] at h
      split at h
      · cases h
      · rename_i hsize
        split at h
        · cases h
          exact Nat.le_of_not_gt hsize
        · split at h
          · cases h
          · exact ih h

/-- Checked fixed-point invariant.
Says: every accepted general-layer state produces zero new triples under
the actual naive full-rule evaluation, and fits the retained triple cap.
Does not say: arbitrary policies are deterministic or the full RDF/RL
composition is one combined least fixed point. -/
theorem generalLoop_success {limits : Limits} {cx : Ctx} {pfx : String}
    {rules : List Rule} {ge : IGraph} {ctr : Nat} {out : IGraph × Nat}
    (h : generalLoop limits cx pfx rules ge ctr = .ok out) :
    Saturated cx pfx rules out ∧ out.1.size ≤ limits.maxTriples := by
  unfold generalLoop at h
  cases hfuel : limits.maxRoundsPerLayer with
  | zero => simp only [hfuel] at h; cases h
  | succ fuel =>
      simp only [hfuel] at h
      cases hp : progress limits.maxTriples cx pfx rules fuel true ge {} ctr with
      | error e => simp [hp, bind, Except.bind] at h
      | ok state =>
          simp only [hp, bind, Except.bind] at h
          split at h
          · rename_i hsat
            cases h
            exact ⟨hsat, progress_bounded hp⟩
          · cases h

/-- Exhaustion behaviour.
Says: a zero round budget never accepts a general-rule result.
Does not say: a failed computation has a normal false verdict. -/
theorem generalLoop_zero (maxTriples : Nat) (cx : Ctx) (pfx : String)
    (rules : List Rule) (ge : IGraph) (ctr : Nat) :
    generalLoop ⟨0, maxTriples⟩ cx pfx rules ge ctr = .error .exhausted := rfl

/-- Inductive preservation through an error-propagating sequence.
Says: accepted folds preserve an invariant held by each accepted step.
Does not say: failed folds return any accepted state. -/
theorem fold_preserves {α β ε : Type} (step : β → α → Except ε β)
    (P : β → Prop) (hstep : ∀ state item next,
      P state → step state item = .ok next → P next)
    (items : List α) {state out : β} (hs : P state)
    (h : items.foldlM step state = .ok out) : P out := by
  induction items generalizing state with
  | nil =>
      simp only [List.foldlM_nil, pure, Except.pure] at h
      cases h
      exact hs
  | cons item rest ih =>
      simp only [List.foldlM_cons] at h
      cases hx : step state item with
      | error e => simp [hx, bind, Except.bind] at h
      | ok next =>
          simp only [hx, bind, Except.bind] at h
          exact ih (hstep state item next hs hx) h

/-- Run-once retained-state bound.
Says: a successful run-once call returns a graph within the cap.
Does not say: the temporary rule bindings fit the same cap. -/
theorem onceRule_bounded {maxTriples : Nat} {cx : Ctx} {pfx : String}
    {rules : List Rule} {state out : IGraph × Nat} {index : Nat}
    (h : onceRule maxTriples cx pfx rules state index = .ok out) :
    out.1.size ≤ maxTriples := by
  simp only [onceRule] at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i hsize
      cases h
      exact Nat.le_of_not_gt hsize

/-- Run-once sequence resource invariant.
Says: a bounded initial graph and successful rule sequence have bounded output.
Does not say: run-once rules are fixed points or may be rerun. -/
theorem onceRules_bounded {maxTriples : Nat} {cx : Ctx} {pfx : String}
    {rules : List Rule} {state out : IGraph × Nat} {indices : List Nat}
    (hs : state.1.size ≤ maxTriples)
    (h : onceRules maxTriples cx pfx rules indices state = .ok out) :
    out.1.size ≤ maxTriples :=
  fold_preserves _ (fun x => x.1.size ≤ maxTriples)
    (fun _ _ _ _ hx => onceRule_bounded hx) indices hs h

/-- Layer resource invariant.
Says: every accepted actual run-once/general layer preserves the retained cap.
Does not say: this is a resource bound on query intermediate allocations. -/
theorem evalLayer_bounded {limits : Limits} {cx : Ctx} {pfx : String}
    {rules : List Rule} {state out : IGraph × Nat} {layer : Layer}
    (hs : state.1.size ≤ limits.maxTriples)
    (h : evalLayer limits cx pfx rules state layer = .ok out) :
    out.1.size ≤ limits.maxTriples := by
  simp only [evalLayer] at h
  cases hx : onceRules limits.maxTriples cx pfx rules layer.once state with
  | error e => simp [hx, bind, Except.bind] at h
  | ok next =>
      simp only [hx, bind, Except.bind] at h
      split at h
      · cases h
        exact onceRules_bounded hs hx
      · exact (generalLoop_success h).2

/-- Whole layer sequence resource invariant.
Says: every successful actual stratification sequence preserves the retained cap.
Does not say: one finite budget proves termination completeness for all policies. -/
theorem evalLayers_bounded {limits : Limits} {cx : Ctx} {pfx : String}
    {rules : List Rule} {state out : IGraph × Nat} {layers : List Layer}
    (hs : state.1.size ≤ limits.maxTriples)
    (h : evalLayers limits cx pfx rules layers state = .ok out) :
    out.1.size ≤ limits.maxTriples :=
  fold_preserves _ (fun x => x.1.size ≤ limits.maxTriples)
    (fun _ _ _ hx hy => evalLayer_bounded hx hy) layers hs h

/-- Exported generalized-graph resource invariant.
Says: the real checked producer's successful graph fits the retained triple cap.
Does not say: the intermediate allocation, host memory or VM-cycle cap is proved. -/
theorem evalIGraph_bounded {limits : Limits} {rs : RuleSet} {base : Graph}
    {env : EvalEnv} {out : IGraph}
    (h : evalIGraph limits rs base env = .ok out) : out.size ≤ limits.maxTriples := by
  simp only [evalIGraph] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · rename_i hsize
            simp only [bind, Except.bind] at h
            split at h
            · cases h
            · rename_i result hx
              cases h
              exact evalLayers_bounded (Nat.le_of_not_gt hsize) hx

/-- Exported RDF-result provenance and resource invariant.
Says: a successful RDF result is the exact projection of the real checked
generalized graph, and its triple count fits the configured cap.
Does not say: generalized triples are valid RDF or the result is canonicalised. -/
theorem evalGraph_success {limits : Limits} {rs : RuleSet} {base out : Graph}
    {env : EvalEnv} (h : evalGraph limits rs base env = .ok out) :
    (∃ ge, evalIGraph limits rs base env = .ok ge ∧
      ge.all.toList.filterMap t3ToTriple? = out) ∧ out.length ≤ limits.maxTriples := by
  simp only [evalGraph] at h
  cases hx : evalIGraph limits rs base env with
  | error e => simp [hx, bind, Except.bind] at h
  | ok ge =>
      simp only [hx, bind, Except.bind, pure, Except.pure] at h
      cases h
      refine ⟨⟨ge, rfl, rfl⟩, ?_⟩
      exact Nat.le_trans (List.length_filterMap_le _ _) (by
        simpa only [Array.length_toList, IGraph.size] using evalIGraph_bounded hx)

#print axioms generalRound_original
#print axioms progress_agrees
#print axioms progress_bounded
#print axioms generalLoop_success
#print axioms generalLoop_zero
#print axioms fold_preserves
#print axioms onceRule_bounded
#print axioms onceRules_bounded
#print axioms evalLayer_bounded
#print axioms evalLayers_bounded
#print axioms evalIGraph_bounded
#print axioms evalGraph_success

end L4Factoidal.SPARQLRL.Checked
