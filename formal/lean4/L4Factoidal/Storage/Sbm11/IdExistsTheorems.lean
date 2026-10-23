/-
L4Factoidal.Storage.Sbm11.IdExistsTheorems — FILTER EXISTS and FILTER NOT
EXISTS over a basic graph pattern on the SBM11 id path
(https://github.com/danbri/factoidal/issues/956, SPARQL 1.1 section 18.6).

## What the reference computes

The reference FILTER of `EXISTS { B }` (`QueryPattern.lowerWith`,
`existsBgpRow`, `filterLowered_evalIn`) substitutes the row μ into `B`
(`substBgp`, SPARQL 1.1 section 18.6 `substitute`) and asks whether the
substituted pattern has a solution. Substitution replaces a variable that μ
binds by its value only where the value can stand: a subject position takes
an IRI or a blank node, the predicate and object positions take an IRI, a
blank node or a literal; a triple term is never substituted. A variable that
μ binds to a value that cannot stand stays a variable of the pattern, and
then the substituted pattern is NOT `B` restricted to μ.

## The id path

The id path evaluates `B` once (its rows `R`) and keeps a row of `L` when
some row of `R` is compatible with it (semi-join; NOT EXISTS: when none is,
anti-semi-join). The two agree when every variable of `B` that the row binds
is substituted at every position where it occurs (`SubstOk`); the id path
checks that per row and refuses the query otherwise (`IdQuery.semiJoinM`, an
error that starts with `refused:`).

* `exists_bgp_iff`: for a basic graph pattern with no triple-term pattern
  (`Unified.BgpTtFree`) and a row with no variable twice that is `SubstOk`,
  `evalBgp (substBgp μ B) g` is empty exactly when no solution of `evalBgp B
  g` is compatible with μ. Proved through the pivot of
  `Unified/SparqlAdequacy.lean` (`bgp_eval_sound`, `bgp_eval_complete`):
  `instTriple_subst` (substituting μ and instantiating by ν is instantiating
  by `μ ++ ν`), `instTriple_congr` (instantiation respects `Term.eqb`), and
  `evalBgpFrom_dom` (a solution binds only the seed's and the pattern's
  variables).
* `semi_decode`: decoding the id semi-join (`idSemi`) of rows of ids is the
  filter of the decoded rows by "some decoded row of `R` is compatible", when
  `Term.eqb` of decoded ids is id equality (`OptJoinTheorems.compatible_decRow`).
* `exists_decode`: the two together. When the rows of `R` decode to
  `evalBgp B g`, decoding `idSemi neg L R` is the reference FILTER of `EXISTS
  { B }` (`neg = false`) or `NOT EXISTS { B }` (`neg = true`) over the decoded
  rows of `L`: the row kept exactly when `evalBgp (substBgp row B) g` is not
  empty (EXISTS) or is empty (NOT EXISTS).
* `exists_filter_decode`: the same, stated with the reference condition the
  FILTER lowering builds (`existsBgpRow` with the condition of
  `filterLowered_evalIn`, top-level μ empty, a dataset in the environment, no
  `text:query` pattern after substitution).

Not proved here (open, as for the other operators of the id path, lemma
L5a′ of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md): that the
`Table` `IdQuery.semiJoinTable` builds (per-mask hash sets of the shared
columns) denotes `idSemi` of the denotations of its inputs, and that the rows
of the body's scans decode to `evalBgp B g`. Tested by the `#guard`s below and
by `tests/sbm11/run.sh` part (d), the `ids-exists-*` queries.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Unified.SparqlAdequacy
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.Invariants
import L4Factoidal.Storage.Sbm11.OptJoinTheorems
import L4Factoidal.Storage.Sbm11.IdQuery

set_option linter.unusedSimpArgs false

namespace L4Factoidal.Storage.Sbm11.IdExists

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Unified (BgpMatches BgpTtFree TpTtFree PatternTermTtFree PatternSubjectTtFree
  bgpVars tpVars patternSubjectVars patternTermVars bgp_eval_sound bgp_eval_complete)

/-! ## Substitutable rows -/

/-- A subject position: a variable the row binds is substituted only by an
    IRI or a blank node (`substPatternSubject`). -/
def SubjOk (mu : Binding) : PatternSubject → Prop
  | .var v =>
    match mu.lookup v with
    | none | some (.iri _) | some (.bnode _) => True
    | _ => False
  | _ => True

/-- A predicate or object position: a variable the row binds to a triple
    term is not substituted (`substPatternTerm`). -/
def TermOk (mu : Binding) : PatternTerm → Prop
  | .var v =>
    match mu.lookup v with
    | some (.tripleTerm _ _ _) => False
    | _ => True
  | _ => True

/-- Every variable of `b` that the row binds is substituted at every
    position where it occurs. -/
def SubstOk (mu : Binding) (b : Bgp) : Prop :=
  ∀ tp ∈ b, SubjOk mu tp.s ∧ TermOk mu tp.p ∧ TermOk mu tp.o

/-! ## Lookup lemmas -/

theorem lookup_append (v : VarName) :
    ∀ (a c : Binding), Binding.lookup v (a ++ c) = (Binding.lookup v a).or (Binding.lookup v c)
  | [], c => by simp [Binding.lookup]
  | (w, t) :: rest, c => by
    simp only [List.cons_append, Binding.lookup]
    by_cases h : w = v
    · simp [h]
    · simp [h, lookup_append v rest c]

/-- `compatible` read entry by entry. -/
theorem compatible_iff : ∀ (a c : Binding),
    Binding.compatible a c = true ↔
      ∀ e ∈ a, ∀ t2, Binding.lookup e.1 c = some t2 → e.2.eqb t2 = true
  | [], c => by simp [Binding.compatible]
  | (v, t) :: rest, c => by
    simp only [Binding.compatible, Bool.and_eq_true, List.mem_cons, forall_eq_or_imp]
    rw [compatible_iff rest c]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      intro t2 ht2
      simp only [ht2] at h1
      exact h1
    · rintro ⟨h1, h2⟩
      refine ⟨?_, h2⟩
      cases hl : Binding.lookup v c with
      | none => rfl
      | some t2 => exact h1 t2 hl

theorem lookup_mem : ∀ {mu : Binding} {v : VarName} {t : Term},
    mu.lookup v = some t → (v, t) ∈ mu
  | [], _, _, h => by simp [Binding.lookup] at h
  | (w, u) :: rest, v, t, h => by
    simp only [Binding.lookup] at h
    by_cases hw : w = v
    · rw [if_pos hw] at h
      cases h; subst hw; exact List.mem_cons_self ..
    · rw [if_neg hw] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

/-- With no variable twice, an entry is the lookup. -/
theorem lookup_of_mem : ∀ {mu : Binding}, (mu.map Prod.fst).Nodup →
    ∀ {v : VarName} {t : Term}, (v, t) ∈ mu → mu.lookup v = some t
  | [], _, _, _, h => by simp at h
  | (w, u) :: rest, hn, v, t, h => by
    simp only [List.map_cons, List.nodup_cons] at hn
    simp only [Binding.lookup]
    rcases List.mem_cons.mp h with he | he
    · cases he; simp
    · have hne : w ≠ v := by
        intro hwv; subst hwv
        exact hn.1 (List.mem_map.mpr ⟨(w, t), he, rfl⟩)
      rw [if_neg hne]
      exact lookup_of_mem hn.2 he

/-- A compatible row agrees by `Term.eqb` on every variable both bind. -/
theorem compatible_lookup' {a c : Binding} (h : Binding.compatible a c = true) {v : VarName}
    {t t2 : Term} (ha : a.lookup v = some t) (hc : c.lookup v = some t2) : t.eqb t2 = true :=
  (compatible_iff a c).mp h (v, t) (lookup_mem ha) t2 hc

/-! ## Substitution and instantiation -/

theorem instSubject_subst (mu nu : Binding) (ps : PatternSubject) (h : SubjOk mu ps) :
    instSubject id nu (substPatternSubject mu ps) = instSubject id (mu ++ nu) ps := by
  cases ps with
  | var v =>
    simp only [SubjOk] at h
    simp only [substPatternSubject, instSubject, lookup_append]
    cases hl : mu.lookup v with
    | none => simp [instSubject]
    | some t =>
      rw [hl] at h
      cases t with
      | iri i => simp [instSubject]
      | bnode b => simp [instSubject]
      | literal _ => exact absurd h id
      | tripleTerm _ _ _ => exact absurd h id
  | iri i => rfl
  | bnode b => rfl
  | tripleTerm _ _ _ => rfl

theorem constructPredicate_subst (mu nu : Binding) (pt : PatternTerm) (h : TermOk mu pt) :
    constructPredicate (substPatternTerm mu pt) nu = constructPredicate pt (mu ++ nu) := by
  cases pt with
  | var v =>
    simp only [TermOk] at h
    simp only [substPatternTerm, constructPredicate, lookup_append]
    cases hl : mu.lookup v with
    | none => simp [constructPredicate]
    | some t =>
      rw [hl] at h
      cases t with
      | iri i => simp [constructPredicate]
      | bnode b => simp [constructPredicate]
      | literal l => simp [constructPredicate]
      | tripleTerm _ _ _ => exact absurd h id
  | iri i => rfl
  | bnode b => rfl
  | literal l => rfl
  | tripleTerm _ _ _ => rfl

theorem instObject_subst (mu nu : Binding) (pt : PatternTerm) (h : TermOk mu pt)
    (htt : PatternTermTtFree pt) :
    instObject id nu (substPatternTerm mu pt) = instObject id (mu ++ nu) pt := by
  cases pt with
  | var v =>
    simp only [TermOk] at h
    simp only [substPatternTerm]
    cases hl : mu.lookup v with
    | none => simp [instObject, lookup_append, hl]
    | some t =>
      rw [hl] at h
      cases t with
      | iri i => simp [instObject, lookup_append, hl]
      | bnode b => simp [instObject, lookup_append, hl]
      | literal l => simp [instObject, lookup_append, hl]
      | tripleTerm _ _ _ => exact absurd h id
  | iri i => rfl
  | bnode b => rfl
  | literal l => rfl
  | tripleTerm _ _ _ => exact absurd htt id

/-- Substituting μ, then instantiating by ν, is instantiating by `μ ++ ν`. -/
theorem instTriple_subst (mu nu : Binding) (tp : TriplePattern)
    (h : SubjOk mu tp.s ∧ TermOk mu tp.p ∧ TermOk mu tp.o) (htt : TpTtFree tp) :
    instTriple id nu (substTriplePattern mu tp) = instTriple id (mu ++ nu) tp := by
  simp only [instTriple, substTriplePattern]
  rw [instSubject_subst mu nu tp.s h.1, constructPredicate_subst mu nu tp.p h.2.1,
    instObject_subst mu nu tp.o h.2.2 htt.2.2]

theorem bgpMatches_subst (mu nu : Binding) (b : Bgp) (g : Graph) (hs : SubstOk mu b)
    (hb : BgpTtFree b) :
    BgpMatches nu (substBgp mu b) g ↔ BgpMatches (mu ++ nu) b g := by
  unfold BgpMatches substBgp
  constructor
  · intro h tp htp
    have := h (substTriplePattern mu tp) (List.mem_map.mpr ⟨tp, htp, rfl⟩)
    rwa [instTriple_subst mu nu tp (hs tp htp) (hb tp htp)] at this
  · intro h tp' htp'
    obtain ⟨tp, htp, rfl⟩ := List.mem_map.mp htp'
    rw [instTriple_subst mu nu tp (hs tp htp) (hb tp htp)]
    exact h tp htp

theorem ttFree_subst (mu : Binding) (b : Bgp) (hb : BgpTtFree b) : BgpTtFree (substBgp mu b) := by
  intro tp' htp'
  obtain ⟨tp, htp, rfl⟩ := List.mem_map.mp (show tp' ∈ b.map (substTriplePattern mu) from htp')
  have h := hb tp htp
  refine ⟨?_, ?_, ?_⟩
  · simp only [substTriplePattern]
    have h1 := h.1
    cases hs : tp.s with
    | var v =>
      simp only [substPatternSubject]
      split <;> trivial
    | iri _ => trivial
    | bnode _ => trivial
    | tripleTerm _ _ _ => rw [hs] at h1; exact absurd h1 id
  · simp only [substTriplePattern]
    have h2 := h.2.1
    cases hp : tp.p with
    | var v =>
      simp only [substPatternTerm]
      split <;> trivial
    | tripleTerm _ _ _ => rw [hp] at h2; exact absurd h2 id
    | _ => trivial
  · simp only [substTriplePattern]
    have h3 := h.2.2
    cases ho : tp.o with
    | var v =>
      simp only [substPatternTerm]
      split <;> trivial
    | tripleTerm _ _ _ => rw [ho] at h3; exact absurd h3 id
    | _ => trivial

/-- An IRI or a blank node is `Term.eqb` only to itself. -/
theorem eqb_subject {t t' : Term} (h : t.eqb t' = true) (hs : t.toSubject?.isSome = true) :
    t' = t := by
  cases t <;> cases t' <;> simp_all [Term.eqb, Term.toSubject?, Subtype.ext_iff]

/-- Instantiation respects `Term.eqb`: two rows that agree by `Term.eqb` on
    the variables of a pattern with no triple-term pattern instantiate it to
    triples equal by `Triple.eqb`. -/
theorem instTriple_congr (a c : Binding) (tp : TriplePattern) (htt : TpTtFree tp)
    (hac : ∀ v ∈ tpVars tp, ∀ t, a.lookup v = some t → ∃ t', c.lookup v = some t' ∧ t.eqb t' = true)
    {w : Triple} (hw : instTriple id a tp = some w) :
    ∃ w', instTriple id c tp = some w' ∧ w.eqb w' = true := by
  simp only [instTriple] at hw
  cases hs : instSubject id a tp.s with
  | none => rw [hs] at hw; cases hw
  | some s =>
    rw [hs] at hw
    cases hp : constructPredicate tp.p a with
    | none => rw [hp] at hw; cases hw
    | some p =>
      rw [hp] at hw
      cases ho : instObject id a tp.o with
      | none => rw [ho] at hw; cases hw
      | some o =>
        rw [ho] at hw
        cases hw
        -- subject
        have hs' : instSubject id c tp.s = some s := by
          cases hts : tp.s with
          | var v =>
            rw [hts] at hs
            simp only [instSubject] at hs ⊢
            have hv : v ∈ tpVars tp := by simp [tpVars, hts, patternSubjectVars]
            cases hl : a.lookup v with
            | none => rw [hl] at hs; cases hs
            | some t =>
              obtain ⟨t', hl', he⟩ := hac v hv t hl
              rw [hl']
              rw [hl] at hs
              cases t with
              | iri i => rw [eqb_subject he rfl]; exact hs
              | bnode x => rw [eqb_subject he rfl]; exact hs
              | literal _ => simp at hs
              | tripleTerm _ _ _ => simp at hs
          | iri _ => rw [hts] at hs; exact hs
          | bnode _ => rw [hts] at hs; exact hs
          | tripleTerm _ _ _ => rw [hts] at hs; simp [instSubject] at hs
        have hp' : constructPredicate tp.p c = some p := by
          cases htp : tp.p with
          | var v =>
            rw [htp] at hp
            simp only [constructPredicate] at hp ⊢
            have hv : v ∈ tpVars tp := by simp [tpVars, htp, patternTermVars]
            cases hl : a.lookup v with
            | none => rw [hl] at hp; cases hp
            | some t =>
              obtain ⟨t', hl', he⟩ := hac v hv t hl
              rw [hl']
              rw [hl] at hp
              cases t with
              | iri i => rw [eqb_subject he rfl]; exact hp
              | bnode x => simp at hp
              | literal _ => simp at hp
              | tripleTerm _ _ _ => simp at hp
          | _ => rw [htp] at hp; simpa [constructPredicate] using hp
        cases hto : tp.o with
        | var v =>
          rw [hto] at ho
          simp only [instObject] at ho
          have hv : v ∈ tpVars tp := by simp [tpVars, hto, patternTermVars]
          obtain ⟨t', hl', he⟩ := hac v hv o ho
          refine ⟨{ s := s, p := p, o := t' }, ?_, ?_⟩
          · simp [instTriple, hs', hp', hto, instObject, hl']
          · simp [Triple.eqb, he]
        | tripleTerm _ _ _ =>
          have h3 := htt.2.2
          rw [hto] at h3
          exact absurd h3 id
        | iri i =>
          refine ⟨{ s := s, p := p, o := o }, ?_, ?_⟩
          · rw [hto] at ho
            simp [instTriple, hs', hp', hto, instObject] at ho ⊢
            exact ho
          · simp [Triple.eqb]
        | bnode x =>
          refine ⟨{ s := s, p := p, o := o }, ?_, ?_⟩
          · rw [hto] at ho
            simp [instTriple, hs', hp', hto, instObject] at ho ⊢
            exact ho
          · simp [Triple.eqb]
        | literal l =>
          refine ⟨{ s := s, p := p, o := o }, ?_, ?_⟩
          · rw [hto] at ho
            simp [instTriple, hs', hp', hto, instObject] at ho ⊢
            exact ho
          · simp [Triple.eqb]

/-! ## The variables a solution binds -/

theorem tryBindSubject_dom {ps : PatternSubject} {s : Subject} {mu mu' : Binding}
    (h : tryBindSubject ps s mu = some mu') {v : VarName} {t : Term}
    (hv : mu'.lookup v = some t) : (mu.lookup v).isSome ∨ v ∈ patternSubjectVars ps := by
  cases ps with
  | iri i =>
    cases s <;> simp only [tryBindSubject] at h
    · split at h
      · cases h; simp [hv]
      · cases h
    · cases h
  | bnode b =>
    cases s <;> simp only [tryBindSubject] at h
    · cases h
    · split at h
      · cases h; simp [hv]
      · cases h
  | tripleTerm _ _ _ => simp [tryBindSubject] at h
  | var w =>
    simp only [tryBindSubject] at h
    cases hw : mu.lookup w with
    | some ex =>
      rw [hw] at h
      simp only at h
      by_cases hc : ex.eqb s.toTerm = true
      · rw [if_pos hc] at h; cases h; simp [hv]
      · rw [if_neg hc] at h; cases h
    | none =>
      rw [hw] at h
      cases h
      simp only [Binding.bind, Binding.lookup] at hv
      by_cases hwv : w = v
      · right; simp [patternSubjectVars, hwv]
      · rw [if_neg hwv] at hv; simp [hv]

theorem tryBindTerm_dom : ∀ {pt : PatternTerm} {t : Term} {mu mu' : Binding},
    tryBindTerm pt t mu = some mu' → ∀ {v : VarName} {u : Term},
      mu'.lookup v = some u → (mu.lookup v).isSome ∨ v ∈ patternTermVars pt := by
  intro pt
  induction pt with
  | iri i =>
    intro t mu mu' h v u hv
    cases t <;> simp only [tryBindTerm] at h
    case iri i' =>
      split at h
      · cases h; simp [hv]
      · cases h
    all_goals cases h
  | bnode b =>
    intro t mu mu' h v u hv
    cases t <;> simp only [tryBindTerm] at h
    case bnode b' =>
      split at h
      · cases h; simp [hv]
      · cases h
    all_goals cases h
  | literal l =>
    intro t mu mu' h v u hv
    cases t <;> simp only [tryBindTerm] at h
    case literal l' =>
      split at h
      · cases h; simp [hv]
      · cases h
    all_goals cases h
  | var w =>
    intro t mu mu' h v u hv
    simp only [tryBindTerm] at h
    cases hw : mu.lookup w with
    | some ex =>
      rw [hw] at h
      simp only at h
      by_cases hc : ex.eqb t = true
      · rw [if_pos hc] at h; cases h; simp [hv]
      · rw [if_neg hc] at h; cases h
    | none =>
      rw [hw] at h
      cases h
      simp only [Binding.bind, Binding.lookup] at hv
      by_cases hwv : w = v
      · right; simp [patternTermVars, hwv]
      · rw [if_neg hwv] at hv; simp [hv]
  | tripleTerm ps pp po ihs ihp iho =>
    intro t mu mu' h v u hv
    cases t <;> simp only [tryBindTerm] at h
    case tripleTerm s p o =>
      cases h1 : tryBindTerm ps s.toTerm mu with
      | none => rw [h1] at h; cases h
      | some mu1 =>
        rw [h1] at h
        simp only at h
        cases h2 : tryBindTerm pp (.iri p) mu1 with
        | none => rw [h2] at h; cases h
        | some mu2 =>
          rw [h2] at h
          simp only at h
          rcases iho h hv with h3 | h3
          · obtain ⟨u2, hu2⟩ := Option.isSome_iff_exists.mp h3
            rcases ihp h2 hu2 with h4 | h4
            · obtain ⟨u1, hu1⟩ := Option.isSome_iff_exists.mp h4
              rcases ihs h1 hu1 with h5 | h5
              · exact Or.inl h5
              · right; simp [patternTermVars, h5]
            · right; simp [patternTermVars, h4]
          · right; simp [patternTermVars, h3]
    all_goals cases h

theorem tpMatch_dom {tp : TriplePattern} {t : Triple} {mu mu' : Binding}
    (h : tpMatch tp t mu = some mu') {v : VarName} {u : Term}
    (hv : mu'.lookup v = some u) : (mu.lookup v).isSome ∨ v ∈ tpVars tp := by
  simp only [tpMatch] at h
  cases h1 : tryBindSubject tp.s t.s mu with
  | none => rw [h1] at h; cases h
  | some mu1 =>
    rw [h1] at h
    simp only at h
    cases h2 : tryBindTerm tp.p (.iri t.p) mu1 with
    | none => rw [h2] at h; cases h
    | some mu2 =>
      rw [h2] at h
      simp only at h
      rcases tryBindTerm_dom h hv with h3 | h3
      · obtain ⟨u2, hu2⟩ := Option.isSome_iff_exists.mp h3
        rcases tryBindTerm_dom h2 hu2 with h4 | h4
        · obtain ⟨u1, hu1⟩ := Option.isSome_iff_exists.mp h4
          rcases tryBindSubject_dom h1 hu1 with h5 | h5
          · exact Or.inl h5
          · right; simp [tpVars, h5]
        · right; simp [tpVars, h4]
      · right; simp [tpVars, h3]

/-- A solution binds only the seed's variables and the pattern's. -/
theorem evalBgpFrom_dom (g : Graph) : ∀ (b : Bgp) {sigma nu : Binding},
    nu ∈ evalBgpFrom g b sigma → ∀ {v : VarName} {u : Term}, nu.lookup v = some u →
      (sigma.lookup v).isSome ∨ v ∈ bgpVars b
  | [], sigma, nu, h, v, u, hv => by
    simp only [evalBgpFrom, List.mem_singleton] at h
    subst h; simp [hv]
  | tp :: rest, sigma, nu, h, v, u, hv => by
    simp only [evalBgpFrom, List.mem_flatMap] at h
    obtain ⟨mu1, hmu1, hrest⟩ := h
    simp only [evalTP, List.mem_filterMap] at hmu1
    obtain ⟨t, _, hm⟩ := hmu1
    rcases evalBgpFrom_dom g rest hrest hv with h1 | h1
    · obtain ⟨u1, hu1⟩ := Option.isSome_iff_exists.mp h1
      rcases tpMatch_dom hm hu1 with h2 | h2
      · exact Or.inl h2
      · right; simp [bgpVars, List.flatMap_cons, h2]
    · right
      simp only [bgpVars, List.flatMap_cons, List.mem_append] at h1 ⊢
      exact Or.inr h1

/-! ## EXISTS by substitution is a semi-join -/

/-- **`exists(substitute(B, μ))` is "some solution of B is compatible with
    μ".** For a basic graph pattern with no triple-term pattern and a row with
    no variable twice whose bound variables of `B` are all substituted
    (`SubstOk`). -/
theorem exists_bgp_iff (g : Graph) (b : Bgp) (mu : Binding) (hb : BgpTtFree b)
    (hs : SubstOk mu b) (hk : (mu.map Prod.fst).Nodup) :
    (evalBgp (substBgp mu b) g).isEmpty = !((evalBgp b g).any (Binding.compatible mu)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.isEmpty_iff, Bool.not_eq_true', List.any_eq_false, Bool.not_eq_true]
  constructor
  · intro hnil nu hnu
    cases hc : Binding.compatible mu nu with
    | false => rfl
    | true =>
    exfalso
    -- ν is a solution of B compatible with μ: the substituted pattern has one
    have hm : BgpMatches nu b g := bgp_eval_sound hnu
    have hm' : BgpMatches (mu ++ nu) b g := by
      intro tp htp
      obtain ⟨w, hw, hg⟩ := hm tp htp
      obtain ⟨w', hw', he⟩ := instTriple_congr nu (mu ++ nu) tp (hb tp htp)
        (fun v _ t ht => by
          rw [lookup_append]
          cases hl : mu.lookup v with
          | none => exact ⟨t, by simp [ht], RDF.Term.eqb_refl t⟩
          | some t0 =>
            refine ⟨t0, by simp, ?_⟩
            rw [RDF.Term.eqb_symm]
            exact compatible_lookup' hc hl ht) hw
      exact ⟨w', hw', RDF.graphMem_of_graphMem_eqb hg he⟩
    have hsub : BgpMatches nu (substBgp mu b) g := (bgpMatches_subst mu nu b g hs hb).mpr hm'
    obtain ⟨m, hmem, _⟩ := bgp_eval_complete (ttFree_subst mu b hb) hsub
    rw [hnil] at hmem
    simp at hmem
  · intro hall
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro m hmem
    have hsub : BgpMatches m (substBgp mu b) g := bgp_eval_sound hmem
    have hm : BgpMatches (mu ++ m) b g := (bgpMatches_subst mu m b g hs hb).mp hsub
    obtain ⟨nu, hnu, hagree⟩ := bgp_eval_complete hb hm
    have hct : Binding.compatible mu nu = true := ?_
    · rw [hall nu hnu] at hct; cases hct
    apply (compatible_iff mu nu).mpr
    rintro ⟨v, t⟩ he t2 ht2
    have hmu : mu.lookup v = some t := lookup_of_mem hk he
    rcases evalBgpFrom_dom g b hnu ht2 with h0 | hvb
    · simp [Binding.empty, Binding.lookup] at h0
    obtain ⟨u, u', hu, hu', hue⟩ := hagree v hvb
    rw [lookup_append, hmu] at hu
    simp only [Option.some_or] at hu
    cases hu
    rw [hu'] at ht2
    cases ht2
    rw [RDF.Term.eqb_symm]
    exact hue

/-! ## Rows of ids -/

open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idCompatible decRow RowIds compatible_decRow)

theorem any_congr' {α : Type} {l : List α} {f g : α → Bool} (h : ∀ x ∈ l, f x = g x) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.any_cons]
    rw [h a (List.mem_cons_self ..), ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

/-- The semi-join (`neg = false`) and the anti-semi-join (`neg = true`) of
    rows of ids: a row of `L` is kept when some row of `R` is compatible with
    it (`neg = false`), or when none is (`neg = true`). -/
def idSemi (neg : Bool) (L R : List IdRow) : List IdRow :=
  L.filter fun r1 => R.any (idCompatible r1) != neg

theorem semi_decode (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (neg : Bool)
    (L R : List IdRow) (hL : ∀ r ∈ L, RowIds ok r) (hR : ∀ r ∈ R, RowIds ok r) :
    (idSemi neg L R).map (decRow dec) =
      (L.map (decRow dec)).filter fun mu => (R.map (decRow dec)).any (Binding.compatible mu) != neg := by
  unfold idSemi
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro r1 h1
  have e : (R.any fun r2 => idCompatible r1 r2) =
      (R.any fun r2 => Binding.compatible (decRow dec r1) (decRow dec r2)) :=
    any_congr' (fun r2 h2 => (compatible_decRow dec ok hdec r1 r2 (hL r1 h1) (hR r2 h2)).symm)
  simp only [Function.comp_def, List.any_map, e]

/-- **EXISTS and NOT EXISTS on ids.** When the body rows `R` decode to
    `evalBgp B g`, decoding the id semi-join (`neg = false`) or anti-semi-join
    (`neg = true`) gives the rows of `L` the reference FILTER keeps: the row
    whose substituted body has a solution (EXISTS) or has none (NOT EXISTS). -/
theorem exists_decode (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (neg : Bool)
    (g : Graph) (b : Bgp) (hb : BgpTtFree b)
    (L R : List IdRow) (hL : ∀ r ∈ L, RowIds ok r) (hR : ∀ r ∈ R, RowIds ok r)
    (hbody : R.map (decRow dec) = evalBgp b g)
    (hsub : ∀ r ∈ L, SubstOk (decRow dec r) b)
    (hkeys : ∀ r ∈ L, (r.map Prod.fst).Nodup) :
    (idSemi neg L R).map (decRow dec) =
      (L.map (decRow dec)).filter fun row => (evalBgp (substBgp row b) g).isEmpty == neg := by
  rw [semi_decode dec ok hdec neg L R hL hR, hbody, List.filter_map, List.filter_map]
  congr 1
  apply List.filter_congr
  intro r hr
  have hk : ((decRow dec r).map Prod.fst).Nodup := by
    have e : (decRow dec r).map Prod.fst = r.map Prod.fst := by
      simp [decRow, Function.comp_def]
    rw [e]; exact hkeys r hr
  simp only [Function.comp_def]
  rw [exists_bgp_iff g b (decRow dec r) hb (hsub r hr) hk]
  cases neg <;> cases ((evalBgp b g).any (Binding.compatible (decRow dec r))) <;> rfl

/-- `substBgp` reads the row through `lookup` only. -/
theorem substBgp_congr {a c : Binding} (h : ∀ v, a.lookup v = c.lookup v) (b : Bgp) :
    substBgp a b = substBgp c b := by
  unfold substBgp substTriplePattern substPatternSubject substPatternTerm
  congr 1
  funext tp
  simp only [h]

/-- **The reference FILTER of a top-level `EXISTS { B }` / `NOT EXISTS { B }`
    on ids.** The condition is the one `filterLowered_evalIn` gives the
    lowering of a FILTER at the top of the WHERE clause (μ empty), with a
    dataset in the environment and no `text:query` pattern after
    substitution. -/
theorem exists_filter_decode (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (neg : Bool)
    (env : EvalEnv) (ds : Dataset) (hds : env.dataset = some ds)
    (g : Graph) (b : Bgp) (hb : BgpTtFree b)
    (L R : List IdRow) (hL : ∀ r ∈ L, RowIds ok r) (hR : ∀ r ∈ R, RowIds ok r)
    (hbody : R.map (decRow dec) = evalBgp b g)
    (hsub : ∀ r ∈ L, SubstOk (decRow dec r) b)
    (hkeys : ∀ r ∈ L, (r.map Prod.fst).Nodup)
    (hft : ∀ r ∈ L, bgpHasFulltext (substBgp (decRow dec r) b) = false)
    (general : Graph → Binding → Bool) :
    (idSemi neg L R).map (decRow dec) =
      filterSeq (existsBgpRow env Binding.empty b neg general (ExistsIndex.ofGraph g) g)
        (L.map (decRow dec)) := by
  rw [exists_decode dec ok hdec neg g b hb L R hL hR hbody hsub hkeys]
  unfold filterSeq
  rw [List.filter_map, List.filter_map]
  congr 1
  apply List.filter_congr
  intro r hr
  have hs : substBgp (Binding.empty.merge (decRow dec r)) b = substBgp (decRow dec r) b :=
    substBgp_congr (fun v => Binding.lookup_merge_empty _ v) b
  simp only [Function.comp_def, existsBgpRow, hds, hs, hft r hr, ExistsIndex.bgpNonempty_ofGraph]
  cases neg <;> simp [evalBgp]

#print axioms exists_bgp_iff
#print axioms semi_decode
#print axioms exists_decode
#print axioms exists_filter_decode

/-! ## Checks

`IdQuery.semiMatches` on sample tables against `idSemi` on their rows
(`OptJoin.unbound`, id 0, read as absent): the table step that is tested, not
proved. -/

#guard idSemi false [[("s", 1)], [("s", 2)], [("t", 3)]] [[("s", 2), ("o", 9)]] ==
  [[("s", 2)], [("t", 3)]]
#guard idSemi true [[("s", 1)], [("s", 2)], [("t", 3)]] [[("s", 2), ("o", 9)]] == [[("s", 1)]]
#guard idSemi false [[("s", 1)]] [] == []
#guard idSemi true [[("s", 1)]] [] == [[("s", 1)]]

open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.OptJoin (unbound)

private def col (xs : List Nat) : ByteArray :=
  xs.foldl (fun b x => L4Factoidal.Qlvr.Side.put64 b x.toUInt64) ByteArray.empty

private def tab (vars : Array String) (cs : List (List Nat)) : Table :=
  { vars, cols := (cs.map col).toArray, rows := (cs.headD []).length }

private def rowsOfTable (t : Table) : List IdRow :=
  (List.range t.rows).map fun i =>
    (List.range t.vars.size).filterMap fun c =>
      let x := t.at c i
      if x == unbound then none else some (t.vars[c]!, x)

/-- `semiMatches` keeps (for `neg = false`) or drops the rows `idSemi` keeps
    or drops. -/
private def agrees (neg : Bool) (l r : Table) : Bool :=
  let hits := IdQuery.semiMatches l r
  let kept := (List.range l.rows).filter fun i => hits[i]! != neg
  kept.map (fun i => (rowsOfTable l)[i]!) == idSemi neg (rowsOfTable l) (rowsOfTable r)

private def L1 : Table := tab #["s", "a"] [[1, 1, 2, 3, 5], [10, 11, 12, 13, 14]]
private def R1 : Table := tab #["s", "o"] [[1, 3, 3], [20, 21, 22]]
private def R2 : Table := tab #["a", "s"] [[11, 13], [1, 9]]
private def R3 : Table := tab #["z"] [[7]]
private def R4 : Table := tab #["z"] [[]]
private def R5 : Table := { vars := #[], cols := #[], rows := 1 }
private def Lu : Table := tab #["s", "a"] [[1, 0, 2, 0], [0, 11, 0, 0]]
private def Ru : Table := tab #["s", "a"] [[2, 0], [11, 12]]

#guard agrees false L1 R1 && agrees true L1 R1
#guard agrees false L1 R2 && agrees true L1 R2
#guard agrees false L1 R3 && agrees true L1 R4 && agrees false L1 R5 && agrees true L1 R5
#guard agrees false Lu R1 && agrees true Lu R2 && agrees false Lu Ru && agrees true Lu Ru
#guard (IdQuery.semiMatches L1 R1).toList == [true, true, false, true, false]
#guard (IdQuery.semiMatches L1 R2).toList == [false, true, false, false, false]
#guard (IdQuery.semiMatches Lu Ru).toList == [true, true, true, true]

end L4Factoidal.Storage.Sbm11.IdExists
