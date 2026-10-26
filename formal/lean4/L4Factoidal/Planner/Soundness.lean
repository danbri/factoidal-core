/-
Capability-aware planner, KR 2.1: soundness of rewritings.

https://github.com/danbri/factoidal/issues/801.

Main results:

* `rewriting_sound`: if every `exact` source of the catalog is sound and
  `p` is a rewriting of `req` (`IsRewriting`, a Boolean check on the
  access steps plus the plan those steps denote), then every UNMARKED row
  of `p.run cat` is, as a partial function, an answer of the reference
  evaluator for `req` over the declared graph of the catalog.
* `run_unmarked_of_allExact`: with only `exact` sources, no row is marked.
* `rewriting_sound_allExact`: the two together, for every row.
* `union_sound`: soundness is closed under plan union.
* `wellFormed_no_inputFailure`: in a well-formed plan, no access finds a
  required input unbound.

The hypotheses are: soundness of the sources (a property of each
implementation against its declared extension) and the rewriting check
(a syntactic property of the steps). Neither mentions the evaluator or
the requirement's answers (CLAUDE.md anti-pattern 29).
-/
import L4Factoidal.Planner.Plan

namespace L4Factoidal.Planner

open L4Factoidal.RDF L4Factoidal.SPARQL

/-! ## Statements -/

/-- Every `exact` source returns only tuples of its extension. -/
def ExactSourcesSound (cat : Catalog) : Prop :=
  ∀ s ∈ cat, s.cap.exactness = .exact → s.sem.Sound

/-- Every unmarked row of the plan is an answer of the requirement over
the declared graph, up to equality of partial functions. -/
def SoundFor (cat : Catalog) (req : Requirement) (p : Plan) : Prop :=
  ∀ x ∈ p.run cat, x.approx = false →
    ∃ ρ ∈ req.answers (declaredGraph cat), SolEquiv x.binding ρ

/-! ## Arguments against tuples -/

/-- The arguments resolve, position by position, to the tuple. -/
def ArgsMatch (mu : Binding) : List Arg → Tuple → Prop
  | [],      []      => True
  | a :: as, t :: ts => a.resolve mu = some t ∧ ArgsMatch mu as ts
  | _,       _       => False

theorem SolLe.isSome {a b : Binding} (h : SolLe a b) {v : VarName}
    (hv : (a.lookup v).isSome = true) : (b.lookup v).isSome = true := by
  cases ha : a.lookup v with
  | none => rw [ha] at hv; cases hv
  | some t => rw [h v t ha]; rfl

theorem Arg.resolve_mono {mu nu : Binding} (h : SolLe mu nu) {a : Arg} {t : Term}
    (ha : a.resolve mu = some t) : a.resolve nu = some t := by
  cases a with
  | const c => exact ha
  | var v => exact h v t ha

theorem ArgsMatch.mono {mu nu : Binding} (h : SolLe mu nu) :
    ∀ {args : List Arg} {tup : Tuple}, ArgsMatch mu args tup → ArgsMatch nu args tup := by
  intro args
  induction args with
  | nil => intro tup hm; cases tup <;> simp_all [ArgsMatch]
  | cons a as ih =>
    intro tup hm
    cases tup with
    | nil => simp [ArgsMatch] at hm
    | cons t ts =>
      simp only [ArgsMatch] at hm ⊢
      exact ⟨Arg.resolve_mono h hm.1, ih hm.2⟩

theorem ArgsMatch.getElem {mu : Binding} :
    ∀ {args : List Arg} {tup : Tuple} {i : Nat} {a : Arg} {t : Term},
      ArgsMatch mu args tup → args[i]? = some a → tup[i]? = some t → a.resolve mu = some t := by
  intro args
  induction args with
  | nil => intro tup i a t _ ha _; simp at ha
  | cons b bs ih =>
    intro tup i a t hm ha ht
    cases tup with
    | nil => simp [ArgsMatch] at hm
    | cons u us =>
      simp only [ArgsMatch] at hm
      cases i with
      | zero =>
        simp at ha ht; subst ha; subst ht; exact hm.1
      | succ k =>
        simp at ha ht
        exact ih hm.2 ha ht

theorem ArgsMatch.var_isSome {mu : Binding} :
    ∀ {args : List Arg} {tup : Tuple} {v : VarName},
      ArgsMatch mu args tup → v ∈ args.flatMap Arg.vars → (mu.lookup v).isSome = true := by
  intro args
  induction args with
  | nil => intro tup v _ hv; simp at hv
  | cons b bs ih =>
    intro tup v hm hv
    cases tup with
    | nil => simp [ArgsMatch] at hm
    | cons u us =>
      simp only [ArgsMatch] at hm
      simp only [List.flatMap_cons, List.mem_append] at hv
      rcases hv with hv | hv
      · cases b with
        | const c => simp [Arg.vars] at hv
        | var w =>
          simp [Arg.vars] at hv; subst hv
          simp only [Arg.resolve] at hm
          rw [hm.1]; rfl
      · exact ih hm.2 hv

theorem bindArgs_spec :
    ∀ (args : List Arg) (tup : Tuple) (mu mu' : Binding),
      bindArgs args tup mu = some mu' →
      SolLe mu mu' ∧ ArgsMatch mu' args tup ∧
      ∀ w, (mu'.lookup w).isSome = true →
        (mu.lookup w).isSome = true ∨ w ∈ args.flatMap Arg.vars := by
  intro args
  induction args with
  | nil =>
    intro tup mu mu' h
    cases tup with
    | nil =>
      simp only [bindArgs, Option.some.injEq] at h; subst h
      exact ⟨SolLe.refl _, trivial, fun w hw => Or.inl hw⟩
    | cons _ _ => simp [bindArgs] at h
  | cons a as ih =>
    intro tup mu mu' h
    cases tup with
    | nil => simp [bindArgs] at h
    | cons t ts =>
      cases a with
      | const c =>
        simp only [bindArgs] at h
        by_cases hc : c = t
        · simp only [hc, if_true] at h
          obtain ⟨h1, h2, h3⟩ := ih ts mu mu' h
          refine ⟨h1, ⟨by simp [Arg.resolve, hc], h2⟩, ?_⟩
          intro w hw
          rcases h3 w hw with h | h
          · exact Or.inl h
          · right; simp only [List.flatMap_cons, List.mem_append]; exact Or.inr h
        · simp [hc] at h
      | var v =>
        simp only [bindArgs] at h
        cases hv : mu.lookup v with
        | some e =>
          rw [hv] at h
          by_cases he : e = t
          · simp only [he, if_true] at h
            obtain ⟨h1, h2, h3⟩ := ih ts mu mu' h
            refine ⟨h1, ⟨?_, h2⟩, ?_⟩
            · simp only [Arg.resolve]; exact h1 v t (he ▸ hv)
            · intro w hw
              rcases h3 w hw with h | h
              · exact Or.inl h
              · right; simp only [List.flatMap_cons, List.mem_append]; exact Or.inr h
          · simp [he] at h
        | none =>
          rw [hv] at h
          obtain ⟨h1, h2, h3⟩ := ih ts (mu.bind v t) mu' h
          have hle : SolLe mu (mu.bind v t) := SolLe.bind_of_none t hv
          refine ⟨SolLe.trans hle h1, ⟨?_, h2⟩, ?_⟩
          · simp only [Arg.resolve]
            exact h1 v t (by simp [lookup_bind])
          · intro w hw
            rcases h3 w hw with h | h
            · rw [lookup_bind] at h
              by_cases hvw : v = w
              · right; subst hvw; simp [Arg.vars]
              · left; simpa [hvw] using h
            · right; simp only [List.flatMap_cons, List.mem_append]; exact Or.inr h

/-! ## One matching step of the reference evaluator -/

/-- `mu'` extends `mu`, is contained in `row`, binds every variable of
`vs`, and binds nothing outside `mu` and `vs`. -/
def Step (mu mu' row : Binding) (vs : List VarName) : Prop :=
  SolLe mu mu' ∧ SolLe mu' row ∧ (∀ v ∈ vs, (mu'.lookup v).isSome = true) ∧
    ∀ w, (mu'.lookup w).isSome = true → (mu.lookup w).isSome = true ∨ w ∈ vs

theorem Step.refl {mu row : Binding} (h : SolLe mu row) : Step mu mu row [] :=
  ⟨SolLe.refl _, h, by simp, fun _ hw => Or.inl hw⟩

theorem Step.trans {mu mu1 mu2 row : Binding} {vs1 vs2 : List VarName}
    (h1 : Step mu mu1 row vs1) (h2 : Step mu1 mu2 row vs2) : Step mu mu2 row (vs1 ++ vs2) := by
  refine ⟨SolLe.trans h1.1 h2.1, h2.2.1, ?_, ?_⟩
  · intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · exact SolLe.isSome h2.1 (h1.2.2.1 v hv)
    · exact h2.2.2.1 v hv
  · intro w hw
    rcases h2.2.2.2 w hw with h | h
    · rcases h1.2.2.2 w h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (List.mem_append.mpr (Or.inl h'))
    · exact Or.inr (List.mem_append.mpr (Or.inr h))

theorem tryBindTerm_var {v : VarName} {x : Term} {mu row : Binding}
    (hle : SolLe mu row) (hx : row.lookup v = some x) :
    ∃ mu', tryBindTerm (.var v) x mu = some mu' ∧ Step mu mu' row [v] := by
  cases hm : mu.lookup v with
  | some e =>
    have he : e = x := by
      have := hle v e hm; rw [hx] at this; exact (Option.some.inj this).symm
    subst he
    refine ⟨mu, by simp [tryBindTerm, hm], SolLe.refl _, hle, ?_, fun w hw => Or.inl hw⟩
    intro w hw; simp at hw; subst hw; rw [hm]; rfl
  | none =>
    refine ⟨mu.bind v x, by simp [tryBindTerm, hm], SolLe.bind_of_none x hm, ?_, ?_, ?_⟩
    · intro w t hw
      rw [lookup_bind] at hw
      by_cases hvw : v = w
      · subst hvw; simp at hw; subst hw; exact hx
      · simp [hvw] at hw; exact hle w t hw
    · intro w hw; simp at hw; subst hw; simp [lookup_bind]
    · intro w hw
      rw [lookup_bind] at hw
      by_cases hvw : v = w
      · right; simp [hvw]
      · left; simpa [hvw] using hw

theorem tryBindTerm_const {c : Term} {pt : PatternTerm} (h : patternTermOfTerm c = some pt)
    (mu : Binding) : tryBindTerm pt c mu = some mu := by
  cases c <;> simp [patternTermOfTerm] at h <;> subst h <;> simp [tryBindTerm]

theorem termVars_of_const {c : Term} {pt : PatternTerm} (h : patternTermOfTerm c = some pt) :
    termVars pt = [] := by
  cases c <;> simp [patternTermOfTerm] at h <;> subst h <;> rfl

theorem subjectVars_of_const {c : Term} {ps : PatternSubject}
    (h : patternSubjectOfTerm c = some ps) : subjectVars ps = [] := by
  cases c <;> simp [patternSubjectOfTerm] at h <;> subst h <;> rfl

theorem toSubject_toTerm {x : Term} {s : Subject} (h : x.toSubject? = some s) : s.toTerm = x := by
  cases x <;> simp [Term.toSubject?] at h <;> subst h <;> rfl

theorem toPredicate_eq {x : Term} {p : WfIri} (h : Term.toPredicate? x = some p) : x = .iri p := by
  cases x <;> simp [Term.toPredicate?] at h; subst h; rfl

theorem bind_term_pos {row mu : Binding} (hle : SolLe mu row) {pt : PatternTerm} {x : Term}
    (hc : patternTermOfTerm x = some pt ∨ ∃ v, pt = .var v ∧ row.lookup v = some x) :
    ∃ mu', tryBindTerm pt x mu = some mu' ∧ Step mu mu' row (termVars pt) := by
  rcases hc with hc | ⟨v, hv, hx⟩
  · refine ⟨mu, tryBindTerm_const hc mu, ?_⟩
    rw [termVars_of_const hc]; exact Step.refl hle
  · subst hv; exact tryBindTerm_var hle hx

theorem bind_subject_pos {row mu : Binding} (hle : SolLe mu row) {ps : PatternSubject}
    {x : Term} {s : Subject} (hs : x.toSubject? = some s)
    (hc : patternSubjectOfTerm x = some ps ∨ ∃ v, ps = .var v ∧ row.lookup v = some x) :
    ∃ mu', tryBindSubject ps s mu = some mu' ∧ Step mu mu' row (subjectVars ps) := by
  rcases hc with hc | ⟨v, hv, hx⟩
  · refine ⟨mu, ?_, ?_⟩
    · cases x <;> simp [patternSubjectOfTerm] at hc <;> simp [Term.toSubject?] at hs <;>
        subst hc <;> subst hs <;> simp [tryBindSubject]
    · rw [subjectVars_of_const hc]; exact Step.refl hle
  · subst hv
    have heq : tryBindSubject (.var v) s mu = tryBindTerm (.var v) s.toTerm mu := by
      unfold tryBindSubject tryBindTerm; rfl
    rw [heq, toSubject_toTerm hs]
    exact tryBindTerm_var hle hx

theorem slot_term_cases {args : List Arg} {tup : Tuple} {row : Binding}
    (hm : ArgsMatch row args tup) {sl : Slot} {pt : PatternTerm} {x : Term}
    (hpt : sl.patternTerm args = some pt) (hx : sl.value tup = some x) :
    patternTermOfTerm x = some pt ∨ ∃ v, pt = .var v ∧ row.lookup v = some x := by
  cases sl with
  | const c =>
    simp only [Slot.value, Option.some.injEq] at hx; subst hx
    exact Or.inl hpt
  | arg i =>
    simp only [Slot.value] at hx
    simp only [Slot.patternTerm] at hpt
    cases ha : args[i]? with
    | none => rw [ha] at hpt; cases hpt
    | some a =>
      rw [ha] at hpt
      have hr := ArgsMatch.getElem hm ha hx
      cases a with
      | var v =>
        simp only [Option.some.injEq] at hpt; subst hpt
        exact Or.inr ⟨v, rfl, hr⟩
      | const c =>
        simp only [Arg.resolve, Option.some.injEq] at hr; subst hr
        exact Or.inl hpt

theorem slot_subject_cases {args : List Arg} {tup : Tuple} {row : Binding}
    (hm : ArgsMatch row args tup) {sl : Slot} {ps : PatternSubject} {x : Term}
    (hps : sl.patternSubject args = some ps) (hx : sl.value tup = some x) :
    patternSubjectOfTerm x = some ps ∨ ∃ v, ps = .var v ∧ row.lookup v = some x := by
  cases sl with
  | const c =>
    simp only [Slot.value, Option.some.injEq] at hx; subst hx
    exact Or.inl hps
  | arg i =>
    simp only [Slot.value] at hx
    simp only [Slot.patternSubject] at hps
    cases ha : args[i]? with
    | none => rw [ha] at hps; cases hps
    | some a =>
      rw [ha] at hps
      have hr := ArgsMatch.getElem hm ha hx
      cases a with
      | var v =>
        simp only [Option.some.injEq] at hps; subst hps
        exact Or.inr ⟨v, rfl, hr⟩
      | const c =>
        simp only [Arg.resolve, Option.some.injEq] at hr; subst hr
        exact Or.inl hps

/-- The template under the access arguments is a requirement triple
pattern; the template under the returned tuple is a triple. The
evaluator's `tpMatch` of that pattern against that triple succeeds from
any restriction of the plan row, and the step stays inside the row. -/
theorem tpMatch_template {args : List Arg} {tup : Tuple} {row mu : Binding}
    (hm : ArgsMatch row args tup) (hle : SolLe mu row) {tm : TripleTemplate}
    {tp : TriplePattern} {t : Triple}
    (hsub : tm.subst args = some tp) (hinst : tm.instantiate tup = some t) :
    ∃ mu', tpMatch tp t mu = some mu' ∧ Step mu mu' row (tpVars tp) := by
  unfold TripleTemplate.subst at hsub
  cases hs : tm.s.patternSubject args with
  | none => rw [hs] at hsub; cases hsub
  | some ps =>
  cases hp : tm.p.patternTerm args with
  | none => rw [hs, hp] at hsub; cases hsub
  | some pp =>
  cases ho : tm.o.patternTerm args with
  | none => rw [hs, hp, ho] at hsub; cases hsub
  | some po =>
  rw [hs, hp, ho] at hsub
  simp only [Option.some.injEq] at hsub; subst hsub
  unfold TripleTemplate.instantiate at hinst
  cases hsv : tm.s.value tup with
  | none => rw [hsv] at hinst; cases hinst
  | some sv =>
  cases hpv : tm.p.value tup with
  | none => rw [hsv, hpv] at hinst; cases hinst
  | some pv =>
  cases hov : tm.o.value tup with
  | none => rw [hsv, hpv, hov] at hinst; cases hinst
  | some ov =>
  rw [hsv, hpv, hov] at hinst
  simp only at hinst
  cases hss : sv.toSubject? with
  | none => rw [hss] at hinst; cases hinst
  | some s' =>
  cases hpp : Term.toPredicate? pv with
  | none => rw [hss, hpp] at hinst; cases hinst
  | some p' =>
  rw [hss, hpp] at hinst
  simp only [Option.some.injEq] at hinst; subst hinst
  have hpv' := toPredicate_eq hpp; subst hpv'
  obtain ⟨mu1, h1, st1⟩ := bind_subject_pos hle hss (slot_subject_cases hm hs hsv)
  obtain ⟨mu2, h2, st2⟩ := bind_term_pos st1.2.1 (slot_term_cases hm hp hpv)
  obtain ⟨mu3, h3, st3⟩ := bind_term_pos st2.2.1 (slot_term_cases hm ho hov)
  refine ⟨mu3, ?_, ?_⟩
  · simp only [tpMatch, h1, h2, h3]
  · have := Step.trans (Step.trans st1 st2) st3
    simpa [tpVars, List.append_assoc] using this

/-! ## The evaluator produces a row inside the plan row -/

theorem evalBgpFrom_row (G : Graph) (row : Binding) :
    ∀ b : Bgp,
      (∀ tp ∈ b, ∃ t ∈ G, ∀ mu, SolLe mu row →
        ∃ mu', tpMatch tp t mu = some mu' ∧ Step mu mu' row (tpVars tp)) →
      ∀ mu, SolLe mu row → ∃ ρ ∈ evalBgpFrom G b mu, Step mu ρ row (bgpVars b) := by
  intro b
  induction b with
  | nil =>
    intro _ mu hle
    exact ⟨mu, by simp [evalBgpFrom], by simpa [bgpVars] using Step.refl hle⟩
  | cons tp rest ih =>
    intro hall mu hle
    obtain ⟨t, ht, hf⟩ := hall tp (List.mem_cons_self ..)
    obtain ⟨mu', hmatch, st⟩ := hf mu hle
    obtain ⟨ρ, hρ, st'⟩ :=
      ih (fun tp' htp' => hall tp' (List.mem_cons_of_mem _ htp')) mu' st.2.1
    refine ⟨ρ, ?_, ?_⟩
    · simp only [evalBgpFrom, List.mem_flatMap]
      refine ⟨mu', ?_, hρ⟩
      simp only [evalTP, List.mem_filterMap]
      exact ⟨t, ht, hmatch⟩
    · have := Step.trans st st'
      simpa [bgpVars, List.flatMap_cons] using this

/-! ## Execution of the access chain -/

theorem mem_access_exec {cat : Catalog} {a : Access} {r y : Row}
    (hy : y ∈ (Plan.access a).exec cat r) :
    ∃ s, cat[a.src]? = some s ∧ ∃ inp, a.inputs? s.cap r.binding = some inp ∧
      ∃ tup ∈ s.sem.impl inp, s.wellTyped tup = true ∧
        bindArgs a.args tup r.binding = some y.binding ∧
        y.approx = (r.approx || s.cap.exactness.isApprox) := by
  simp only [Plan.exec] at hy
  cases hs : cat[a.src]? with
  | none => rw [hs] at hy; simp at hy
  | some s =>
    rw [hs] at hy
    simp only at hy
    cases hi : a.inputs? s.cap r.binding with
    | none => rw [hi] at hy; simp at hy
    | some inp =>
      rw [hi] at hy
      simp only [List.mem_filterMap] at hy
      obtain ⟨tup, htup, hsome⟩ := hy
      by_cases hw : s.wellTyped tup = true
      · simp only [hw, if_true] at hsome
        cases hb : bindArgs a.args tup r.binding with
        | none => rw [hb] at hsome; cases hsome
        | some b =>
          rw [hb] at hsome
          simp only [Option.map_some, Option.some.injEq] at hsome
          subst hsome
          exact ⟨s, rfl, inp, hi, tup, htup, hw, hb, rfl⟩
      · simp [hw] at hsome

theorem chainPlan_cons (a : Access) (steps : List Access) :
    chainPlan (a :: steps) = .join (.access a) (chainPlan steps) := rfl

theorem chain_exec_spec (cat : Catalog) (hsound : ExactSourcesSound cat) :
    ∀ (steps : List Access) (r x : Row), x ∈ (chainPlan steps).exec cat r → x.approx = false →
      r.approx = false ∧ SolLe r.binding x.binding ∧
      (∀ a ∈ steps, ∃ s, cat[a.src]? = some s ∧ s ∈ cat ∧
        ∃ tup ∈ s.sem.ext, s.wellTyped tup = true ∧ ArgsMatch x.binding a.args tup) ∧
      (∀ w, (x.binding.lookup w).isSome = true →
        (r.binding.lookup w).isSome = true ∨ ∃ a ∈ steps, w ∈ a.vars) := by
  intro steps
  induction steps with
  | nil =>
    intro r x hx happ
    simp only [chainPlan, List.foldr, Plan.exec, List.mem_singleton] at hx
    subst hx
    exact ⟨happ, SolLe.refl _, by simp, fun _ hw => Or.inl hw⟩
  | cons a rest ih =>
    intro r x hx happ
    rw [chainPlan_cons] at hx
    simp only [Plan.exec, List.mem_flatMap] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    obtain ⟨hyapp, hyx, hrest, hdom⟩ := ih y x hxy happ
    obtain ⟨s, hs, inp, _hinp, tup, htup, hwt, hb, hya⟩ := mem_access_exec hy
    rw [hyapp] at hya
    have hra : r.approx = false ∧ s.cap.exactness.isApprox = false :=
      Bool.or_eq_false_iff.mp hya.symm
    have hexact : s.cap.exactness = .exact := by
      cases he : s.cap.exactness with
      | exact => rfl
      | approximate => have := hra.2; rw [he] at this; cases this
    have hsmem : s ∈ cat := List.mem_of_getElem? hs
    have hext : tup ∈ s.sem.ext := hsound s hsmem hexact inp tup htup
    obtain ⟨hle, hmatch, hbdom⟩ := bindArgs_spec a.args tup r.binding y.binding hb
    refine ⟨hra.1, SolLe.trans hle hyx, ?_, ?_⟩
    · intro a' ha'
      rcases List.mem_cons.mp ha' with h | h
      · subst h
        exact ⟨s, hs, hsmem, tup, hext, hwt, ArgsMatch.mono hyx hmatch⟩
      · exact hrest a' h
    · intro w hw
      rcases hdom w hw with h | ⟨a', ha', hw'⟩
      · rcases hbdom w h with h' | h'
        · exact Or.inl h'
        · exact Or.inr ⟨a, List.mem_cons_self .., h'⟩
      · exact Or.inr ⟨a', List.mem_cons_of_mem _ ha', hw'⟩

theorem filtersPlan_exec (cat : Catalog) :
    ∀ (fs : List RowFilter) (p : Plan) (r x : Row), x ∈ (filtersPlan fs p).exec cat r →
      x ∈ p.exec cat r ∧ ∀ f ∈ fs, f.test x.binding = true := by
  intro fs
  induction fs with
  | nil => intro p r x hx; exact ⟨hx, by simp⟩
  | cons f fs ih =>
    intro p r x hx
    have hfp : filtersPlan (f :: fs) p = .filter f (filtersPlan fs p) := rfl
    rw [hfp] at hx
    simp only [Plan.exec, List.mem_filter] at hx
    obtain ⟨h1, h2⟩ := ih p r x hx.1
    refine ⟨h1, ?_⟩
    intro g hg
    rcases List.mem_cons.mp hg with h | h
    · subst h; exact hx.2
    · exact h2 g h

/-! ## The evaluator side of the filters -/

theorem mem_evalIn_filters (ds : Dataset) (G : Graph) (b : Bgp) :
    ∀ (fs : List RowFilter) (ρ : Binding), ρ ∈ evalBgp b G →
      (∀ f ∈ fs, f.test ρ = true) →
      ρ ∈ (fs.foldr (fun f p => GraphPattern.filter (fun _ => f.test) p) (.bgp b)).evalIn ds G := by
  intro fs
  induction fs with
  | nil =>
    intro ρ hρ _
    simp only [List.foldr, GraphPattern.evalIn, evalBgpIdx_eq_evalBgp]
    exact hρ
  | cons f fs ih =>
    intro ρ hρ hf
    simp only [List.foldr, GraphPattern.evalIn, filterSeq, List.mem_filter]
    exact ⟨ih ρ hρ (fun g hg => hf g (List.mem_cons_of_mem _ hg)), hf f (List.mem_cons_self ..)⟩

/-! ## Soundness -/

/-- Soundness of a rewriting: under sound exact sources, every unmarked
row of the plan is an answer of the requirement over the declared graph. -/
theorem rewriting_sound {cat : Catalog} {req : Requirement} {p : Plan}
    (hsound : ExactSourcesSound cat) (hrw : IsRewriting cat req p) : SoundFor cat req p := by
  obtain ⟨rw, hchk, hp⟩ := hrw
  subst hp
  intro x hx happ
  simp only [Rewriting.check, Bool.and_eq_true, List.all_eq_true, List.any_eq_true] at hchk
  obtain ⟨⟨hcov, hvars⟩, _⟩ := hchk
  -- Peel the projection and the filters.
  simp only [Plan.run, Rewriting.toPlan, Plan.exec, List.mem_map] at hx
  obtain ⟨x0, hx0, hxeq⟩ := hx
  subst hxeq
  obtain ⟨hx0c, hfil⟩ := filtersPlan_exec cat req.filters _ _ x0 hx0
  obtain ⟨_, _, hsteps, hdom⟩ := chain_exec_spec cat hsound rw.steps _ x0 hx0c happ
  -- The evaluator finds a row inside x0.
  have hall : ∀ tp ∈ req.bgp, ∃ t ∈ declaredGraph cat, ∀ mu, SolLe mu x0.binding →
      ∃ mu', tpMatch tp t mu = some mu' ∧ Step mu mu' x0.binding (tpVars tp) := by
    intro tp htp
    obtain ⟨a, ha, hcv⟩ := hcov tp htp
    obtain ⟨s, hs, hsmem, tup, hext, hwt, hmatch⟩ := hsteps a ha
    simp only [Access.covers, hs, List.any_eq_true, beq_iff_eq] at hcv
    obtain ⟨tm, htm, hsub⟩ := hcv
    simp only [Source.wellTyped, Bool.and_eq_true, List.all_eq_true] at hwt
    have hsome := hwt.2 tm htm
    cases hi : tm.instantiate tup with
    | none => rw [hi] at hsome; cases hsome
    | some t =>
      exact ⟨t, mem_declaredGraph hsmem hext htm hi,
        fun mu hle => tpMatch_template hmatch hle hsub hi⟩
  obtain ⟨ρ, hρ, hst⟩ :=
    evalBgpFrom_row (declaredGraph cat) x0.binding req.bgp hall [] (by intro v t h; cases h)
  -- ρ and x0 are the same partial function.
  have hequiv : SolEquiv ρ x0.binding := by
    intro v
    cases hρv : ρ.lookup v with
    | some t => exact (hst.2.1 v t hρv).symm
    | none =>
      cases hxv : x0.binding.lookup v with
      | none => rfl
      | some t =>
        exfalso
        have hsome : (x0.binding.lookup v).isSome = true := by rw [hxv]; rfl
        rcases hdom v hsome with h | ⟨a, ha, hva⟩
        · simp [Binding.lookup] at h
        · have hvb : v ∈ bgpVars req.bgp := by
            have := hvars a ha v hva
            simpa using this
          have := hst.2.2.1 v hvb
          rw [hρv] at this; cases this
  refine ⟨projectBinding req.projection ρ, ?_, ?_⟩
  · unfold Requirement.answers projectSolutions
    apply List.mem_map_of_mem
    unfold Requirement.pattern GraphPattern.eval
    apply mem_evalIn_filters
    · exact hρ
    · intro f hf
      rw [f.respects ρ x0.binding hequiv]
      exact hfil f hf
  · exact projectBinding_equiv _ hequiv.symm

/-- Soundness is closed under union of plans. -/
theorem union_sound {cat : Catalog} {req : Requirement} {p q : Plan}
    (hp : SoundFor cat req p) (hq : SoundFor cat req q) : SoundFor cat req (.union p q) := by
  intro x hx happ
  simp only [Plan.run, Plan.exec, List.mem_append] at hx
  rcases hx with hx | hx
  · exact hp x hx happ
  · exact hq x hx happ

/-! ## Approximate markers -/

/-- With only exact sources, execution never sets the marker. -/
theorem exec_approx_of_allExact {cat : Catalog}
    (hex : ∀ s ∈ cat, s.cap.exactness = .exact) :
    ∀ (p : Plan) (r x : Row), x ∈ p.exec cat r → x.approx = r.approx := by
  intro p
  induction p with
  | unit => intro r x hx; simp only [Plan.exec, List.mem_singleton] at hx; subst hx; rfl
  | access a =>
    intro r x hx
    obtain ⟨s, hs, _, _, _, _, _, _, hxa⟩ := mem_access_exec hx
    rw [hxa, hex s (List.mem_of_getElem? hs)]
    simp [Exactness.isApprox]
  | join l q ihl ihq =>
    intro r x hx
    simp only [Plan.exec, List.mem_flatMap] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    rw [ihq y x hxy, ihl r y hy]
  | filter f p ih =>
    intro r x hx
    simp only [Plan.exec, List.mem_filter] at hx
    exact ih r x hx.1
  | project vs p ih =>
    intro r x hx
    simp only [Plan.exec, List.mem_map] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    subst hxy
    exact ih r y hy
  | union l q ihl ihq =>
    intro r x hx
    simp only [Plan.exec, List.mem_append] at hx
    rcases hx with hx | hx
    · exact ihl r x hx
    · exact ihq r x hx

/-- A plan over exact sources produces no marked rows. -/
theorem run_unmarked_of_allExact {cat : Catalog}
    (hex : ∀ s ∈ cat, s.cap.exactness = .exact) (p : Plan) :
    ∀ x ∈ p.run cat, x.approx = false :=
  fun x hx => exec_approx_of_allExact hex p _ x hx

/-- With only exact, sound sources, every row of a rewriting is an
answer of the requirement over the declared graph. -/
theorem rewriting_sound_allExact {cat : Catalog} {req : Requirement} {p : Plan}
    (hex : ∀ s ∈ cat, s.cap.exactness = .exact) (hsound : ∀ s ∈ cat, s.sem.Sound)
    (hrw : IsRewriting cat req p) :
    ∀ x ∈ p.run cat, ∃ ρ ∈ req.answers (declaredGraph cat), SolEquiv x.binding ρ :=
  fun x hx =>
    rewriting_sound (fun s hs _ => hsound s hs) hrw x hx (run_unmarked_of_allExact hex p x hx)

/-! ## Well-formedness -/

theorem inputsGo_isSome (args : List Arg) (mu : Binding) :
    ∀ (is : List Nat) (acc : InputBinding),
      (∀ i ∈ is, ∃ a, args[i]? = some a ∧ (a.resolve mu).isSome = true) →
      (inputsGo args mu is acc).isSome = true := by
  intro is
  induction is with
  | nil => intro acc _; simp [inputsGo]
  | cons i is ih =>
    intro acc h
    obtain ⟨a, ha, hr⟩ := h i (List.mem_cons_self ..)
    cases hres : a.resolve mu with
    | none => rw [hres] at hr; cases hr
    | some t =>
      simp only [inputsGo, ha, hres]
      exact ih _ (fun j hj => h j (List.mem_cons_of_mem _ hj))

theorem inputs_isSome_of_bound {cap : Capability} {a : Access} {bound : List VarName}
    {mu : Binding} (hb : a.inputsBound cap bound = true)
    (hmu : ∀ v ∈ bound, (mu.lookup v).isSome = true) :
    (a.inputs? cap mu).isSome = true := by
  unfold Access.inputs?
  apply inputsGo_isSome
  intro i hi
  simp only [Access.inputsBound, List.all_eq_true] at hb
  have := hb i hi
  cases ha : a.args[i]? with
  | none => rw [ha] at this; cases this
  | some arg =>
    rw [ha] at this
    refine ⟨arg, rfl, ?_⟩
    cases arg with
    | const c => rfl
    | var v =>
      simp only [Arg.resolve]
      exact hmu v (by simpa using this)

theorem wf_domain (cat : Catalog) :
    ∀ (p : Plan) (b b' : List VarName) (r x : Row), p.wfBound cat b = some b' →
      (∀ v ∈ b, (r.binding.lookup v).isSome = true) → x ∈ p.exec cat r →
      ∀ v ∈ b', (x.binding.lookup v).isSome = true := by
  intro p
  induction p with
  | unit =>
    intro b b' r x hwf hb hx
    simp only [Plan.wfBound, Option.some.injEq] at hwf; subst hwf
    simp only [Plan.exec, List.mem_singleton] at hx; subst hx
    exact hb
  | access a =>
    intro b b' r x hwf hb hx
    obtain ⟨s, hs, _, _, tup, _, _, hbind, _⟩ := mem_access_exec hx
    simp only [Plan.wfBound, hs] at hwf
    split at hwf
    · simp only [Option.some.injEq] at hwf; subst hwf
      obtain ⟨hle, hmatch, _⟩ := bindArgs_spec a.args tup r.binding x.binding hbind
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact SolLe.isSome hle (hb v hv)
      · exact ArgsMatch.var_isSome hmatch hv
    · cases hwf
  | join l q ihl ihq =>
    intro b b' r x hwf hb hx
    simp only [Plan.wfBound] at hwf
    cases hl : l.wfBound cat b with
    | none => rw [hl] at hwf; cases hwf
    | some b1 =>
      rw [hl] at hwf
      simp only [Plan.exec, List.mem_flatMap] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      exact ihq b1 b' y x hwf (ihl b b1 r y hl hb hy) hxy
  | filter f p ih =>
    intro b b' r x hwf hb hx
    simp only [Plan.wfBound] at hwf
    simp only [Plan.exec, List.mem_filter] at hx
    exact ih b b' r x hwf hb hx.1
  | project vs p ih =>
    intro b b' r x hwf hb hx
    simp only [Plan.wfBound] at hwf
    cases hp : p.wfBound cat b with
    | none => rw [hp] at hwf; cases hwf
    | some b1 =>
      rw [hp] at hwf
      simp only [Option.map_some, Option.some.injEq] at hwf; subst hwf
      simp only [Plan.exec, List.mem_map] at hx
      obtain ⟨y, hy, hxy⟩ := hx
      subst hxy
      intro v hv
      simp only [List.mem_filter] at hv
      simp only [lookup_projectBinding]
      have hvs : vs.contains v = true := by simpa using hv.1
      rw [if_pos hvs]
      exact ih b b1 r y hp hb hy v (by simpa using hv.2)
  | union l q ihl ihq =>
    intro b b' r x hwf hb hx
    simp only [Plan.wfBound] at hwf
    cases hl : l.wfBound cat b with
    | none => rw [hl] at hwf; cases hwf
    | some b1 =>
    cases hq : q.wfBound cat b with
    | none => rw [hl, hq] at hwf; cases hwf
    | some b2 =>
      rw [hl, hq] at hwf
      simp only [Option.some.injEq] at hwf; subst hwf
      intro v hv
      simp only [List.mem_filter] at hv
      simp only [Plan.exec, List.mem_append] at hx
      rcases hx with hx | hx
      · exact ihl b b1 r x hl hb hx v hv.1
      · exact ihq b b2 r x hq hb hx v (by simpa using hv.2)

/-- The access-pattern condition holds at run time: in a well-formed
plan, no access finds a required input unbound. -/
theorem wf_no_inputFailure (cat : Catalog) :
    ∀ (p : Plan) (b b' : List VarName) (r : Row), p.wfBound cat b = some b' →
      (∀ v ∈ b, (r.binding.lookup v).isSome = true) → p.inputFailure cat r = false := by
  intro p
  induction p with
  | unit => intro _ _ _ _ _; rfl
  | access a =>
    intro b b' r hwf hb
    simp only [Plan.inputFailure]
    cases hs : cat[a.src]? with
    | none => rfl
    | some s =>
      simp only [Plan.wfBound, hs] at hwf
      split at hwf
      · rename_i hcond
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hcond
        have := inputs_isSome_of_bound hcond.2 hb (mu := r.binding)
        cases hi : a.inputs? s.cap r.binding with
        | none => rw [hi] at this; cases this
        | some _ => simp [hi]
      · cases hwf
  | join l q ihl ihq =>
    intro b b' r hwf hb
    simp only [Plan.wfBound] at hwf
    cases hl : l.wfBound cat b with
    | none => rw [hl] at hwf; cases hwf
    | some b1 =>
      rw [hl] at hwf
      simp only [Plan.inputFailure, ihl b b1 r hl hb, Bool.false_or, List.any_eq_false]
      intro y hy
      simp [ihq b1 b' y hwf (wf_domain cat l b b1 r y hl hb hy)]
  | filter f p ih =>
    intro b b' r hwf hb
    simp only [Plan.wfBound] at hwf
    exact ih b b' r hwf hb
  | project vs p ih =>
    intro b b' r hwf hb
    simp only [Plan.wfBound] at hwf
    cases hp : p.wfBound cat b with
    | none => rw [hp] at hwf; cases hwf
    | some b1 => exact ih b b1 r hp hb
  | union l q ihl ihq =>
    intro b b' r hwf hb
    simp only [Plan.wfBound] at hwf
    cases hl : l.wfBound cat b with
    | none => rw [hl] at hwf; cases hwf
    | some b1 =>
    cases hq : q.wfBound cat b with
    | none => rw [hl, hq] at hwf; cases hwf
    | some b2 =>
      simp only [Plan.inputFailure, ihl b b1 r hl hb, ihq b b2 r hq hb, Bool.or_false]

theorem wellFormed_no_inputFailure {cat : Catalog} {p : Plan} (h : p.WellFormed cat) :
    p.inputFailure cat { binding := [], approx := false } = false := by
  unfold Plan.WellFormed at h
  cases hw : p.wfBound cat [] with
  | none => rw [hw] at h; cases h
  | some b' => exact wf_no_inputFailure cat p [] b' _ hw (by simp)

end L4Factoidal.Planner
