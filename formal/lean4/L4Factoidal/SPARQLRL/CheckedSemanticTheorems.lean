/-
The checked general-rule producer connected to the existing declarative
rule-body semantics and conditional least-fixed-point theorems.
Issue: https://github.com/danbri/factoidal-core/issues/745.

The actual final check discharges saturation. This module does not assume
that the ordinary automatic fuel bound always suffices, or that stratify
has already been proved to establish NegBlind for arbitrary negative rules.
-/
import L4Factoidal.SPARQLRL.CheckedTheorems
import L4Factoidal.SPARQLRL.SemiNaiveTheorems

namespace L4Factoidal.SPARQLRL.Checked

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-- Actual-step identity.
Says: the extracted round's delta is the existing new-triple construction
over the same rule-body solutions and head instances.
Does not say: the graph is already saturated. -/
theorem generalRound_delta (cx : Ctx) (pfx : String) (rules : List Rule)
    (first : Bool) (ge delta : IGraph) (ctr : Nat) :
    (generalRound cx pfx rules first ge delta ctr).1 =
      newOf ge (roundFold pfx rules (semiSols cx first ge delta) ctr).1 := rfl

/-- Index invariant.
Says: every delta constructed by the actual round has coherent indexes,
membership set and insertion-order array.
Does not say: an arbitrary externally constructed IGraph is coherent. -/
theorem generalRound_wf (cx : Ctx) (pfx : String) (rules : List Rule)
    (first : Bool) (ge delta : IGraph) (ctr : Nat) :
    (generalRound cx pfx rules first ge delta ctr).1.WF := by
  rw [generalRound_delta]
  exact wf_newOf _ _

/-- Progress index invariant.
Says: actual bounded progress preserves coherence from a coherent input.
Does not say: progress has completed its saturation check. -/
theorem progress_wf {maxTriples fuel : Nat} {cx : Ctx} {pfx : String}
    {rules : List Rule} {first : Bool} {ge delta : IGraph} {ctr : Nat}
    {out : IGraph × Nat} (hge : ge.WF)
    (h : progress maxTriples cx pfx rules fuel first ge delta ctr = .ok out) :
    out.1.WF := by
  induction fuel generalizing first ge delta ctr with
  | zero =>
      simp only [progress] at h
      split at h
      · cases h
      · cases h; exact hge
  | succ fuel ih =>
      simp only [progress] at h
      split at h
      · cases h
      · split at h
        · cases h; exact hge
        · split at h
          · cases h
          · exact ih (IGraph.wf_insertAll hge _) h

/-- Progress extensivity.
Says: bounded progress never removes a member of the input evaluation graph.
Does not say: every new member is derivable without general-rule hypotheses. -/
theorem progress_extensive {maxTriples fuel : Nat} {cx : Ctx} {pfx : String}
    {rules : List Rule} {first : Bool} {ge delta : IGraph} {ctr : Nat}
    {out : IGraph × Nat} {t : T3} (ht : ge.mem t)
    (h : progress maxTriples cx pfx rules fuel first ge delta ctr = .ok out) :
    out.1.mem t := by
  induction fuel generalizing first ge delta ctr with
  | zero =>
      simp only [progress] at h
      split at h
      · cases h
      · cases h; exact ht
  | succ fuel ih =>
      simp only [progress] at h
      split at h
      · cases h
      · split at h
        · cases h; exact ht
        · split at h
          · cases h
          · exact ih ((IGraph.mem_insertAll _ _ _).mpr (Or.inr ht)) h

/-- Producer provenance.
Says: checked general-layer success comes from its actual bounded progress
at one less than the configured round budget, reserving the final check.
Does not say: a caller-supplied result can replace that progress result. -/
theorem generalLoop_progress {limits : Limits} {cx : Ctx} {pfx : String}
    {rules : List Rule} {ge : IGraph} {ctr : Nat} {out : IGraph × Nat}
    (h : generalLoop limits cx pfx rules ge ctr = .ok out) :
    ∃ fuel, limits.maxRoundsPerLayer = fuel + 1 ∧
      progress limits.maxTriples cx pfx rules fuel true ge {} ctr = .ok out := by
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
          · cases h
            exact ⟨fuel, rfl, hp⟩
          · cases h

/-- Full-rule operational/declarative connection.
Says: the actual naive checking round adds exactly the declaratively derived
head instances that are not already members of the evaluation graph.
Does not say: arbitrary run-once rules have this general-rule semantics. -/
theorem fullRound_mem_iff (cx : Ctx) (pfx : String) (rules : List Rule)
    (hg0 : cx.g0.WF) (hgen : ∀ r ∈ rules, r.runOnce = false)
    {ge : IGraph} (hge : ge.WF) (ctr : Nat) (t : T3) :
    (generalRound cx pfx rules true ge {} ctr).1.mem t ↔
      NOut cx rules ge.mem t ∧ ¬ ge.mem t := by
  rw [generalRound_delta, mem_newOf,
    mem_roundFold pfx rules (semiSols cx true ge {})
      (fun r hr => (runOnce_false (hgen r hr)).2) ctr t]
  have hout : (∃ r ∈ rules, ∃ μ ∈ semiSols cx true ge {} r,
      ∃ tt ∈ r.head, headInst μ tt = some t) ↔ NOut cx rules ge.mem t := by
    unfold NOut semiSols
    simp only [if_true]
    constructor
    · rintro ⟨r, hr, μ, hμ, tt, htt, hi⟩
      exact ⟨r, hr, μ, (mem_evalBody_full cx hg0 hge (runOnce_false (hgen r hr)).1 μ).mp hμ,
        tt, htt, hi⟩
    · rintro ⟨r, hr, μ, hμ, tt, htt, hi⟩
      exact ⟨r, hr, μ, (mem_evalBody_full cx hg0 hge (runOnce_false (hgen r hr)).1 μ).mpr hμ,
        tt, htt, hi⟩
  rw [hout]

/-- Declarative saturation established by the actual checked producer.
Says: for general rules and coherent inputs, every declarative rule
conclusion over an accepted result is already in that result.
Does not say: arbitrary negative policies satisfy stratification's remaining
NegBlind proof obligation; this closure theorem does not need NegBlind. -/
theorem generalLoop_closed {limits : Limits} {cx : Ctx} {pfx : String}
    {rules : List Rule} {ge : IGraph} {ctr : Nat} {out : IGraph × Nat}
    (hg0 : cx.g0.WF) (hgen : ∀ r ∈ rules, r.runOnce = false) (hge : ge.WF)
    (h : generalLoop limits cx pfx rules ge ctr = .ok out) {t : T3}
    (ht : NOut cx rules out.1.mem t) : out.1.mem t := by
  obtain ⟨fuel, _, hp⟩ := generalLoop_progress h
  have hout : out.1.WF := progress_wf hge hp
  have hsat := (generalLoop_success h).1
  have hzero : ((generalRound cx pfx rules true out.1 {} out.2).1.size == 0) = true := by
    simpa only [beq_iff_eq, Saturated] using hsat
  have hempty := (size_eq_zero_iff (generalRound_wf cx pfx rules true out.1 {} out.2)).mp hzero
  by_cases hm : out.1.mem t
  · exact hm
  · exact False.elim (hempty t ((fullRound_mem_iff cx pfx rules hg0 hgen hout out.2 t).mpr ⟨ht, hm⟩))

/-- Accepted-state extensivity.
Says: every accepted checked general layer retains its input members.
Does not say: RDF serialization order or multiplicity is semantically significant. -/
theorem generalLoop_extensive {limits : Limits} {cx : Ctx} {pfx : String}
    {rules : List Rule} {ge : IGraph} {ctr : Nat} {out : IGraph × Nat}
    (h : generalLoop limits cx pfx rules ge ctr = .ok out) {t : T3}
    (ht : ge.mem t) : out.1.mem t := by
  obtain ⟨_, _, hp⟩ := generalLoop_progress h
  exact progress_extensive ht hp

/-- Conditional least-fixed-point refinement.
Says: accepted checked output is contained in every closed extension of the
input satisfying the existing general-rule/NegBlind hypotheses.
Does not say: these hypotheses have been derived from arbitrary text policies. -/
theorem generalLoop_least {limits : Limits} {cx : Ctx} {pfx : String}
    {rules : List Rule} {ge : IGraph} {ctr : Nat} {out : IGraph × Nat}
    (hg0 : cx.g0.WF) (hgen : ∀ r ∈ rules, r.runOnce = false) (hneg : NegBlind rules)
    (hge : ge.WF) (h : generalLoop limits cx pfx rules ge ctr = .ok out)
    (S : T3 → Prop) (hclosed : ∀ t, NOut cx rules S t → S t)
    (hsub : ∀ t, ge.mem t → S t) (hdiff : ∀ t, S t → ¬ ge.mem t → HeadInst rules t)
    {t : T3} (ht : out.1.mem t) : S t := by
  obtain ⟨fuel, _, hp⟩ := generalLoop_progress h
  rw [← progress_agrees hp] at ht
  exact L4Factoidal.SPARQLRL.generalLoop_least cx pfx rules hg0 hgen hneg hge fuel ctr
    S hclosed hsub hdiff t ht

/-- Run-once graph invariant and extensivity.
Says: each actual run-once call preserves coherent indexing and all old members.
Does not say: run-once semantics are equivalent to iterative general rules. -/
theorem onceRule_preserves {maxTriples : Nat} {cx : Ctx} {pfx : String}
    {rules : List Rule} {state out : IGraph × Nat} {index : Nat} (hs : state.1.WF)
    (h : onceRule maxTriples cx pfx rules state index = .ok out) :
    out.1.WF ∧ ∀ t, state.1.mem t → out.1.mem t := by
  simp only [onceRule] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      exact ⟨IGraph.wf_insertAll hs _, fun t ht => (IGraph.mem_insertAll _ _ t).mpr (Or.inr ht)⟩

/-- Run-once sequence graph invariant.
Says: the actual sequence preserves coherent indexes and all starting members.
Does not say: it satisfies a full rule saturation property. -/
theorem onceRules_preserves {maxTriples : Nat} {cx : Ctx} {pfx : String}
    {rules : List Rule} {state out : IGraph × Nat} {indices : List Nat} (hs : state.1.WF)
    (h : onceRules maxTriples cx pfx rules indices state = .ok out) :
    out.1.WF ∧ ∀ t, state.1.mem t → out.1.mem t := by
  apply fold_preserves _ (fun s => s.1.WF ∧ ∀ t, state.1.mem t → s.1.mem t) ?_
    indices (state := state) ⟨hs, fun _ ht => ht⟩ h
  intro current i next hc hn
  obtain ⟨hnwf, hnmem⟩ := onceRule_preserves hc.1 hn
  exact ⟨hnwf, fun t ht => hnmem t (hc.2 t ht)⟩

/-- Actual layer graph invariant.
Says: the run-once/general producer preserves coherent indexes and old members.
Does not say: externally constructed layer indices are a valid stratification. -/
theorem evalLayer_preserves {limits : Limits} {cx : Ctx} {pfx : String}
    {rules : List Rule} {state out : IGraph × Nat} {layer : Layer} (hs : state.1.WF)
    (h : evalLayer limits cx pfx rules state layer = .ok out) :
    out.1.WF ∧ ∀ t, state.1.mem t → out.1.mem t := by
  simp only [evalLayer] at h
  cases hx : onceRules limits.maxTriples cx pfx rules layer.once state with
  | error e => simp [hx, bind, Except.bind] at h
  | ok next =>
      have hn := onceRules_preserves hs hx
      simp only [hx, bind, Except.bind] at h
      split at h
      · cases h; exact hn
      · obtain ⟨_, _, hp⟩ := generalLoop_progress h
        exact ⟨progress_wf hn.1 hp, fun t ht => generalLoop_extensive h (hn.2 t ht)⟩

/-- Whole checked layer sequence graph invariant.
Says: successful stratified execution preserves coherent indexes and its base.
Does not say: later RDFS consequences have been recomputed after the rules. -/
theorem evalLayers_preserves {limits : Limits} {cx : Ctx} {pfx : String}
    {rules : List Rule} {state out : IGraph × Nat} {layers : List Layer} (hs : state.1.WF)
    (h : evalLayers limits cx pfx rules layers state = .ok out) :
    out.1.WF ∧ ∀ t, state.1.mem t → out.1.mem t := by
  apply fold_preserves _ (fun s => s.1.WF ∧ ∀ t, state.1.mem t → s.1.mem t) ?_
    layers (state := state) ⟨hs, fun _ ht => ht⟩ h
  intro current layer next hc hn
  obtain ⟨hnwf, hnmem⟩ := evalLayer_preserves hc.1 hn
  exact ⟨hnwf, fun t ht => hnmem t (hc.2 t ht)⟩

/-- RDF base/index bridge.
Says: constructing the actual rule index retains each input RDF triple.
Does not say: duplicate source occurrences acquire RDF multiplicity. -/
theorem ofGraph_retains {base : Graph} {t : Triple} (ht : t ∈ base) :
    (IGraph.ofGraph base).mem (tripleToT3 t) := by
  have hm : tripleToT3 t ∈ base.map tripleToT3 := List.mem_map.mpr ⟨t, ht, rfl⟩
  have hx := (IGraph.mem_foldl_insert {} (base.map tripleToT3) (tripleToT3 t)).mpr (Or.inl hm)
  simpa only [IGraph.ofGraph, List.foldl_map] using hx

/-- Actual checked producer's base and index invariant.
Says: exported successful generalized results retain all RDF input triples
and have coherent indexes; the hypotheses come from actual construction.
Does not say: arbitrary hand-constructed graph indexes are trustworthy. -/
theorem evalIGraph_preserves {limits : Limits} {rs : RuleSet} {base : Graph}
    {env : EvalEnv} {out : IGraph} (h : evalIGraph limits rs base env = .ok out) :
    out.WF ∧ ∀ t ∈ base, out.mem (tripleToT3 t) := by
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
          · simp only [bind, Except.bind] at h
            split at h
            · cases h
            · rename_i result hx
              cases h
              have hp := evalLayers_preserves (IGraph.wf_insertAll (IGraph.wf_ofGraph base) _) hx
              exact ⟨hp.1, fun t ht => hp.2 (tripleToT3 t)
                ((IGraph.mem_insertAll _ _ _).mpr (Or.inr (ofGraph_retains ht)))⟩

/-- Exact RDF/generalized triple conversion.
Says: every RDF triple survives the actual index-to-RDF projection unchanged.
Does not say: every generalized triple has an RDF projection. -/
theorem rdf_projection_roundtrip (t : Triple) : t3ToTriple? (tripleToT3 t) = some t := by
  cases t with
  | mk s p o => cases s <;> rfl

/-- Exported RDF base preservation.
Says: the real checked RDF result contains every original RDF input triple,
so an ASK sees the base as well as newly inferred triples.
Does not say: source duplicate counts must be retained. -/
theorem evalGraph_extensive {limits : Limits} {rs : RuleSet} {base out : Graph}
    {env : EvalEnv} (h : evalGraph limits rs base env = .ok out) {t : Triple}
    (ht : t ∈ base) : t ∈ out := by
  obtain ⟨⟨ge, hge, rfl⟩, _⟩ := evalGraph_success h
  have hp := evalIGraph_preserves hge
  exact List.mem_filterMap.mpr ⟨tripleToT3 t,
    Array.mem_toList_iff.mpr ((IGraph.mem_iff_all hp.1 _).mp (hp.2 t ht)),
    rdf_projection_roundtrip t⟩

#print axioms generalRound_delta
#print axioms generalRound_wf
#print axioms progress_wf
#print axioms progress_extensive
#print axioms generalLoop_progress
#print axioms fullRound_mem_iff
#print axioms generalLoop_closed
#print axioms generalLoop_extensive
#print axioms generalLoop_least
#print axioms onceRule_preserves
#print axioms onceRules_preserves
#print axioms evalLayer_preserves
#print axioms evalLayers_preserves
#print axioms ofGraph_retains
#print axioms evalIGraph_preserves
#print axioms rdf_projection_roundtrip
#print axioms evalGraph_extensive

end L4Factoidal.SPARQLRL.Checked
