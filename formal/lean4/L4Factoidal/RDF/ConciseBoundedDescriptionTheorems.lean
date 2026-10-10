/-
L4Factoidal.RDF.ConciseBoundedDescriptionTheorems — the description
`Graph.cbd` is the Concise Bounded Description: it is closed under the
two recursive clauses and it holds nothing else.

Specification: "CBD - Concise Bounded Description", W3C Member Submission,
https://www.w3.org/Submission/CBD/ , section 2. The definition and its
reading of clause 3 for RDF 1.2 are in `ConciseBoundedDescription.lean`.

Three results, for a graph `g` and starting nodes `roots`:

  * `cbd_closed_bnode` (clause 2): if a statement is in the description
    and its object is a blank node, every statement of `g` with that
    blank node as subject is in the description.
  * `cbd_closed_reifier` (clause 3, RDF 1.2 reading): if a statement is in
    the description, every `r rdf:reifies <<( s p o )>>` statement of `g`
    whose triple term is that statement is in the description.
  * `cbd_least`: a set of nodes that holds the starting nodes and is
    closed under the two clauses holds every node whose statements the
    description contains. So the description holds no statement that the
    clauses do not reach.

The first two need the walk to finish before its fuel runs out. The proof
is a potential function: the queue length plus the number of possible
candidate nodes not yet seen drops by at least one at every step, and it
starts at no more than `roots.length + g.length`.

No `sorry`, no `axiom`, no `native_decide`.
-/
import L4Factoidal.RDF.ConciseBoundedDescription

namespace L4Factoidal.RDF

/-! ## The indexes hold exactly the statements of the graph -/

/-- Folding statements into the by-subject index: a statement is under `s`
exactly when it is a statement of the folded list with subject `s`, or was
there before. -/
theorem bySubject_fold_mem (g : Graph) :
    ∀ (m : Std.HashMap Subject (List Triple)) (s : Subject) (t : Triple),
      t ∈ (g.foldl cbdSubjectStep m).getD s [] ↔
        (t ∈ g ∧ t.s = s) ∨ t ∈ m.getD s [] := by
  induction g with
  | nil => intro m s t; simp
  | cons t0 rest ih =>
      intro m s t
      simp only [List.foldl_cons, ih, cbdSubjectStep, Std.HashMap.getD_insert]
      by_cases h : (t0.s == s) = true
      · have hs : t0.s = s := by simpa using h
        subst hs
        simp only [h, if_true, List.mem_cons]
        grind
      · have hs : ¬ t0.s = s := by simpa using h
        simp only [h, if_false, List.mem_cons]
        grind

/-- One step of the reifier index. -/
theorem reifierStep_mem (m : Std.HashMap Subject (List (Subject × WfIri × Term)))
    (t0 : Triple) (ts : Subject) (e : Subject × WfIri × Term) :
    e ∈ (cbdReifierStep m t0).getD ts [] ↔
      (t0.p = L4Factoidal.RDFS.rdfReifies ∧ ∃ p o,
          t0.o = .tripleTerm ts p o ∧ e = (t0.s, p, o)) ∨ e ∈ m.getD ts [] := by
  unfold cbdReifierStep
  by_cases hp : (t0.p == L4Factoidal.RDFS.rdfReifies) = true
  · have hp' : t0.p = L4Factoidal.RDFS.rdfReifies := Subtype.ext (by simpa using hp)
    simp only [hp, if_true]
    cases ho : t0.o with
    | tripleTerm s p o =>
        simp only [Std.HashMap.getD_insert]
        by_cases hs : (s == ts) = true
        · have hs' : s = ts := by simpa using hs
          subst hs'
          simp only [hs, if_true, List.mem_cons]
          grind
        · have hs' : ¬ s = ts := by simpa using hs
          simp only [hs, if_false]
          grind
    | iri _ => grind
    | bnode _ => grind
    | literal _ => grind
  · have hp' : ¬ t0.p = L4Factoidal.RDFS.rdfReifies := fun h => hp (by simp [h])
    simp only [hp, if_false]
    grind

/-- The same for the reifier index: an entry `(r, p, o)` is under `ts` exactly
when some `rdf:reifies` statement of the folded list has subject `r` and the
triple term `<<( ts p o )>>` as its object, or the entry was there before. -/
theorem reifiers_fold_mem (g : Graph) :
    ∀ (m : Std.HashMap Subject (List (Subject × WfIri × Term))) (ts : Subject)
      (e : Subject × WfIri × Term),
      e ∈ (g.foldl cbdReifierStep m).getD ts [] ↔
        (∃ t ∈ g, t.p = L4Factoidal.RDFS.rdfReifies ∧ ∃ p o,
            t.o = .tripleTerm ts p o ∧ e = (t.s, p, o)) ∨ e ∈ m.getD ts [] := by
  induction g with
  | nil => intro m ts e; simp
  | cons t0 rest ih =>
      intro m ts e
      simp only [List.foldl_cons, ih, reifierStep_mem, List.mem_cons, exists_eq_or_imp]
      grind

/-- The statements indexed under `s` are the statements of `g` with subject `s`. -/
theorem mem_bySubject (g : Graph) (s : Subject) (t : Triple) :
    t ∈ g.cbdIndex.bySubject.getD s [] ↔ t ∈ g ∧ t.s = s := by
  unfold Graph.cbdIndex
  simp only [bySubject_fold_mem, Std.HashMap.getD_empty, List.not_mem_nil, or_false]

/-- The entries indexed under `ts` come from the `rdf:reifies` statements of
`g` whose object is a triple term with subject `ts`. -/
theorem mem_reifierEntry (g : Graph) (ts : Subject) (e : Subject × WfIri × Term) :
    e ∈ g.cbdIndex.reifiers.getD ts [] ↔
      ∃ t ∈ g, t.p = L4Factoidal.RDFS.rdfReifies ∧ ∃ p o,
        t.o = .tripleTerm ts p o ∧ e = (t.s, p, o) := by
  unfold Graph.cbdIndex
  simp only [reifiers_fold_mem, Std.HashMap.getD_empty, List.not_mem_nil, or_false]

/-- The reifiers of a statement `t`: the subjects `r` of the `rdf:reifies`
statements of `g` whose triple term is `t`, compared by IRI equality and
`Term.eqb`. -/
theorem mem_reifiersOf (g : Graph) (t : Triple) (r : Subject) :
    r ∈ g.cbdIndex.reifiersOf t ↔
      ∃ t' ∈ g, t'.p = L4Factoidal.RDFS.rdfReifies ∧ ∃ p o,
        t'.o = .tripleTerm t.s p o ∧ p = t.p ∧ o.eqb t.o = true ∧ t'.s = r := by
  unfold CbdIndex.reifiersOf
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨r', p, o⟩, hmem, hf⟩
    rw [mem_reifierEntry] at hmem
    obtain ⟨t', ht', hp, p', o', hto, he⟩ := hmem
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    by_cases hc : (p == t.p && o.eqb t.o) = true
    · simp only [hc, if_true, Option.some.injEq] at hf
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨t', ht', hp, p, o, hto, hc.1, hc.2, hf⟩
    · simp only [hc, if_false] at hf
      cases hf
  · rintro ⟨t', ht', hp, p, o, hto, hpt, heq, hs⟩
    refine ⟨(t'.s, p, o), ?_, ?_⟩
    · rw [mem_reifierEntry]
      exact ⟨t', ht', hp, p, o, hto, rfl⟩
    · simp [hpt, heq, hs]

/-- What the object of a statement contributes to the candidates. -/
theorem mem_bnodeObject (o : Term) (c : Subject) :
    c ∈ (cbdBnodeObject? o).toList ↔ ∃ b, o = .bnode b ∧ c = .bnode b := by
  cases o <;> simp [cbdBnodeObject?]

/-- The candidates of a node `s`: the blank-node objects of the statements
with subject `s` (clause 2) and the reifiers of those statements (clause 3). -/
theorem mem_candidates (g : Graph) (s c : Subject) :
    c ∈ g.cbdIndex.candidates s ↔
      ∃ t ∈ g, t.s = s ∧
        ((∃ b, t.o = .bnode b ∧ c = .bnode b) ∨ c ∈ g.cbdIndex.reifiersOf t) := by
  unfold CbdIndex.candidates
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨t, ht, hc⟩
    rw [mem_bySubject] at ht
    rw [List.mem_append, mem_bnodeObject] at hc
    exact ⟨t, ht.1, ht.2, hc⟩
  · rintro ⟨t, ht, hs, hc⟩
    refine ⟨t, (mem_bySubject g s t).mpr ⟨ht, hs⟩, ?_⟩
    rw [List.mem_append, mem_bnodeObject]
    exact hc

/-! ## The nodes a walk can ever queue, and how many are not yet seen -/

/-- The nodes some expansion can queue: the blank-node objects of the
statements of `g`, and the subjects of its `rdf:reifies` statements whose
object is a triple term. One entry at most per statement, so the list is no
longer than `g`. -/
def cbdUniverse (g : Graph) : List Subject :=
  g.filterMap fun t =>
    match t.o with
    | .bnode b          => some (Subject.bnode b)
    | .tripleTerm _ _ _ =>
        if t.p == L4Factoidal.RDFS.rdfReifies then some t.s else none
    | _                 => none

theorem cbdUniverse_length (g : Graph) : (cbdUniverse g).length ≤ g.length :=
  List.length_filterMap_le _ _

/-- Every candidate of every node is in the universe. -/
theorem candidates_mem_universe (g : Graph) (s c : Subject)
    (h : c ∈ g.cbdIndex.candidates s) : c ∈ cbdUniverse g := by
  rw [mem_candidates] at h
  obtain ⟨t, ht, -, hc⟩ := h
  unfold cbdUniverse
  rw [List.mem_filterMap]
  rcases hc with ⟨b, hb, rfl⟩ | hc
  · exact ⟨t, ht, by simp [hb]⟩
  · rw [mem_reifiersOf] at hc
    obtain ⟨t', ht', hp, p, o, hto, -, -, rfl⟩ := hc
    refine ⟨t', ht', ?_⟩
    have hp' : (t'.p == L4Factoidal.RDFS.rdfReifies) = true := by simp [hp]
    simp [hto, hp']

/-- How many members of `U` are not yet seen. -/
def cbdUnseen (U : List Subject) (seen : Std.HashSet Subject) : Nat :=
  (U.filter fun x => !seen.contains x).length

theorem cbdUnseen_le_length (U : List Subject) (seen : Std.HashSet Subject) :
    cbdUnseen U seen ≤ U.length :=
  List.length_filter_le _ _

theorem cbdUnseen_insert_le (U : List Subject) (seen : Std.HashSet Subject) (c : Subject) :
    cbdUnseen U (seen.insert c) ≤ cbdUnseen U seen := by
  induction U with
  | nil => simp [cbdUnseen]
  | cons x rest ih =>
      unfold cbdUnseen at ih ⊢
      have e : (seen.insert c).contains x = (c == x || seen.contains x) :=
        Std.HashSet.contains_insert
      by_cases h1 : seen.contains x = true
      · rw [List.filter_cons_of_neg (p := fun y => !(seen.insert c).contains y) (by simp [e, h1]),
          List.filter_cons_of_neg (p := fun y => !seen.contains y) (by simp [h1])]
        exact ih
      · by_cases h2 : (c == x) = true
        · rw [List.filter_cons_of_neg (p := fun y => !(seen.insert c).contains y) (by simp [e, h2]),
            List.filter_cons_of_pos (p := fun y => !seen.contains y) (by simp [h1]),
            List.length_cons]
          omega
        · rw [List.filter_cons_of_pos (p := fun y => !(seen.insert c).contains y)
              (by simp [e, h1, h2]),
            List.filter_cons_of_pos (p := fun y => !seen.contains y) (by simp [h1]),
            List.length_cons, List.length_cons]
          omega

/-- Seeing a new member of `U` leaves fewer members unseen. -/
theorem cbdUnseen_insert_lt (U : List Subject) (seen : Std.HashSet Subject) (c : Subject)
    (hc : c ∈ U) (hn : seen.contains c = false) :
    cbdUnseen U (seen.insert c) < cbdUnseen U seen := by
  induction U with
  | nil => cases hc
  | cons x rest ih =>
      unfold cbdUnseen at ih ⊢
      have e : (seen.insert c).contains x = (c == x || seen.contains x) :=
        Std.HashSet.contains_insert
      by_cases h1 : seen.contains x = true
      · have hxc : ¬ x = c := by rintro rfl; simp [hn] at h1
        have hc' : c ∈ rest := by
          rcases List.mem_cons.mp hc with rfl | h
          · exact absurd rfl hxc
          · exact h
        rw [List.filter_cons_of_neg (p := fun y => !(seen.insert c).contains y) (by simp [e, h1]),
          List.filter_cons_of_neg (p := fun y => !seen.contains y) (by simp [h1])]
        exact ih hc'
      · by_cases h2 : (c == x) = true
        · have hcx : c = x := by simpa using h2
          subst hcx
          have := cbdUnseen_insert_le rest seen c
          unfold cbdUnseen at this
          rw [List.filter_cons_of_neg (p := fun y => !(seen.insert c).contains y) (by simp [e, h2]),
            List.filter_cons_of_pos (p := fun y => !seen.contains y) (by simp [h1]),
            List.length_cons]
          omega
        · have hxc : ¬ c = x := by simpa using h2
          have hc' : c ∈ rest := by
            rcases List.mem_cons.mp hc with h | h
            · exact absurd h hxc
            · exact h
          rw [List.filter_cons_of_pos (p := fun y => !(seen.insert c).contains y)
              (by simp [e, h1, h2]),
            List.filter_cons_of_pos (p := fun y => !seen.contains y) (by simp [h1]),
            List.length_cons, List.length_cons]
          have := ih hc'
          omega

/-! ## What queueing candidates does -/

theorem cbdQueue_nil (work : List Subject) (seen : Std.HashSet Subject) :
    cbdQueue [] work seen = (work, seen) := rfl

/-- One candidate: skipped when seen, else queued and marked seen. -/
theorem cbdQueue_cons (c : Subject) (cs work : List Subject) (seen : Std.HashSet Subject) :
    cbdQueue (c :: cs) work seen =
      if seen.contains c = true then cbdQueue cs work seen
      else cbdQueue cs (c :: work) (seen.insert c) := by
  unfold cbdQueue
  simp only [List.foldl_cons]
  split <;> rfl

/-- Queued nodes stay queued. -/
theorem cbdQueue_work_mono (cs : List Subject) :
    ∀ (work : List Subject) (seen : Std.HashSet Subject) (x : Subject),
      x ∈ work → x ∈ (cbdQueue cs work seen).1 := by
  induction cs with
  | nil => intro work seen x hx; exact hx
  | cons c cs ih =>
      intro work seen x hx
      rw [cbdQueue_cons]
      split
      · exact ih _ _ _ hx
      · exact ih _ _ _ (List.mem_cons_of_mem _ hx)

/-- Every candidate is seen afterwards. -/
theorem cbdQueue_cands_seen (cs : List Subject) :
    ∀ (work : List Subject) (seen : Std.HashSet Subject) (c : Subject),
      c ∈ cs → (cbdQueue cs work seen).2.contains c = true := by
  induction cs with
  | nil => intro work seen c hc; cases hc
  | cons d cs ih =>
      intro work seen c hc
      rw [cbdQueue_cons]
      split
      · rename_i hd
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact cbdQueue_seen_mono cs work seen c hd
        · exact ih _ _ _ hc'
      · rename_i hd
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact cbdQueue_seen_mono cs _ _ c (by simp [Std.HashSet.contains_insert])
        · exact ih _ _ _ hc'

/-- A queued node is an old queued node or a candidate. -/
theorem cbdQueue_work_src (cs : List Subject) :
    ∀ (work : List Subject) (seen : Std.HashSet Subject) (x : Subject),
      x ∈ (cbdQueue cs work seen).1 → x ∈ work ∨ x ∈ cs := by
  induction cs with
  | nil => intro work seen x hx; exact Or.inl hx
  | cons c cs ih =>
      intro work seen x hx
      rw [cbdQueue_cons] at hx
      split at hx
      · rcases ih _ _ _ hx with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases ih _ _ _ hx with h | h
        · rcases List.mem_cons.mp h with rfl | h'
          · exact Or.inr List.mem_cons_self
          · exact Or.inl h'
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- A node seen afterwards was seen before, or is a candidate. -/
theorem cbdQueue_seen_src (cs : List Subject) :
    ∀ (work : List Subject) (seen : Std.HashSet Subject) (x : Subject),
      (cbdQueue cs work seen).2.contains x = true → seen.contains x = true ∨ x ∈ cs := by
  induction cs with
  | nil => intro work seen x hx; exact Or.inl hx
  | cons c cs ih =>
      intro work seen x hx
      rw [cbdQueue_cons] at hx
      split at hx
      · rcases ih _ _ _ hx with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · rcases ih _ _ _ hx with h | h
        · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
          rcases h with rfl | h
          · exact Or.inr List.mem_cons_self
          · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)

/-- A node newly seen is queued. -/
theorem cbdQueue_new_queued (cs : List Subject) :
    ∀ (work : List Subject) (seen : Std.HashSet Subject) (x : Subject),
      (cbdQueue cs work seen).2.contains x = true →
      seen.contains x = true ∨ x ∈ (cbdQueue cs work seen).1 := by
  induction cs with
  | nil => intro work seen x hx; exact Or.inl hx
  | cons c cs ih =>
      intro work seen x hx
      rw [cbdQueue_cons] at hx ⊢
      split at hx
      · rename_i hc
        simp only [hc, if_true]
        exact ih _ _ _ hx
      · rename_i hc
        simp only [hc, if_false]
        rcases ih _ _ _ hx with h | h
        · simp only [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] at h
          rcases h with rfl | h
          · exact Or.inr (cbdQueue_work_mono cs _ _ _ List.mem_cons_self)
          · exact Or.inl h
        · exact Or.inr h

/-- Everything queued is seen, provided everything already queued is. -/
theorem cbdQueue_queued_seen (cs : List Subject) :
    ∀ (work : List Subject) (seen : Std.HashSet Subject),
      (∀ x ∈ work, seen.contains x = true) →
      ∀ x ∈ (cbdQueue cs work seen).1, (cbdQueue cs work seen).2.contains x = true := by
  induction cs with
  | nil => intro work seen h x hx; exact h x hx
  | cons c cs ih =>
      intro work seen h x hx
      rw [cbdQueue_cons] at hx ⊢
      split at hx
      · rename_i hc
        simp only [hc, if_true]
        exact ih _ _ h x hx
      · rename_i hc
        simp only [hc, if_false]
        apply ih _ _ _ x hx
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · simp [Std.HashSet.contains_insert]
        · simp [Std.HashSet.contains_insert, h y hy']

/-- The queue grows by at most one per candidate. -/
theorem cbdQueue_length_le (cs : List Subject) :
    ∀ (work : List Subject) (seen : Std.HashSet Subject),
      (cbdQueue cs work seen).1.length ≤ work.length + cs.length := by
  induction cs with
  | nil => intro work seen; simp [cbdQueue_nil]
  | cons c cs ih =>
      intro work seen
      rw [cbdQueue_cons]
      split
      · have := ih work seen
        simp only [List.length_cons]; omega
      · have := ih (c :: work) (seen.insert c)
        simp only [List.length_cons] at this ⊢; omega

/-- The potential never rises: queue length plus members of `U` not yet seen. -/
theorem cbdQueue_potential (U : List Subject) (cs : List Subject) (hU : ∀ c ∈ cs, c ∈ U) :
    ∀ (work : List Subject) (seen : Std.HashSet Subject),
      (cbdQueue cs work seen).1.length + cbdUnseen U (cbdQueue cs work seen).2 ≤
        work.length + cbdUnseen U seen := by
  induction cs with
  | nil => intro work seen; simp [cbdQueue_nil]
  | cons c cs ih =>
      intro work seen
      have hcU : c ∈ U := hU c List.mem_cons_self
      have hrest : ∀ d ∈ cs, d ∈ U := fun d hd => hU d (List.mem_cons_of_mem _ hd)
      rw [cbdQueue_cons]
      split
      · exact ih hrest work seen
      · rename_i hc
        have hc' : seen.contains c = false := by simpa using hc
        have h1 := ih hrest (c :: work) (seen.insert c)
        have h2 := cbdUnseen_insert_lt U seen c hcU hc'
        simp only [List.length_cons] at h1
        omega

/-! ## The walk: closed when it finishes, and it finishes within its fuel -/

/-- The walk invariant: a seen node is queued, or already expanded, which
means all of its candidates are seen. -/
def CbdInv (idx : CbdIndex) (work : List Subject) (seen : Std.HashSet Subject) : Prop :=
  ∀ x, seen.contains x = true → x ∈ work ∨ ∀ c ∈ idx.candidates x, seen.contains c = true

/-- If the fuel covers the potential, the walk ends with every candidate of
every seen node seen. `U` is any list that holds every candidate of every
node (`candidates_mem_universe`). -/
theorem cbdWalk_closed (idx : CbdIndex) (U : List Subject)
    (hU : ∀ s c, c ∈ idx.candidates s → c ∈ U) :
    ∀ (fuel : Nat) (work : List Subject) (seen : Std.HashSet Subject),
      CbdInv idx work seen → work.length + cbdUnseen U seen ≤ fuel →
      ∀ x, (cbdWalk idx fuel work seen).contains x = true →
        ∀ c ∈ idx.candidates x, (cbdWalk idx fuel work seen).contains c = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro work seen hinv hfuel x hx c hc
      have hw : work = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hw
      simp only [cbdWalk] at hx ⊢
      rcases hinv x hx with h | h
      · cases h
      · exact h c hc
  | succ n ih =>
      intro work seen hinv hfuel x hx c hc
      cases work with
      | nil =>
          simp only [cbdWalk] at hx ⊢
          rcases hinv x hx with h | h
          · cases h
          · exact h c hc
      | cons s rest =>
          simp only [cbdWalk] at hx ⊢
          refine ih _ _ ?_ ?_ x hx c hc
          · intro y hy
            rcases cbdQueue_new_queued _ _ _ y hy with hseen | hq
            · rcases hinv y hseen with hmem | hall
              · rcases List.mem_cons.mp hmem with rfl | hrest
                · exact Or.inr (fun d hd => cbdQueue_cands_seen _ _ _ d hd)
                · exact Or.inl (cbdQueue_work_mono _ _ _ y hrest)
              · exact Or.inr (fun d hd => cbdQueue_seen_mono _ _ _ d (hall d hd))
            · exact Or.inl hq
          · have hpot := cbdQueue_potential U (idx.candidates s) (hU s) rest seen
            simp only [List.length_cons] at hfuel
            omega

/-- The walk adds nothing but the starting nodes and candidates of nodes it
has seen: it stays inside any set that holds the starting nodes and is
closed under candidates. -/
theorem cbdWalk_least (idx : CbdIndex) (P : Subject → Prop)
    (hP : ∀ x, P x → ∀ c ∈ idx.candidates x, P c) :
    ∀ (fuel : Nat) (work : List Subject) (seen : Std.HashSet Subject),
      (∀ x ∈ work, seen.contains x = true) → (∀ x, seen.contains x = true → P x) →
      ∀ x, (cbdWalk idx fuel work seen).contains x = true → P x := by
  intro fuel
  induction fuel with
  | zero =>
      intro work seen hwork hseen x hx
      exact hseen x (by simpa [cbdWalk] using hx)
  | succ n ih =>
      intro work seen hwork hseen x hx
      cases work with
      | nil => exact hseen x (by simpa [cbdWalk] using hx)
      | cons s rest =>
          simp only [cbdWalk] at hx
          refine ih _ _ ?_ ?_ x hx
          · exact cbdQueue_queued_seen _ _ _ (fun y hy => hwork y (List.mem_cons_of_mem _ hy))
          · intro y hy
            rcases cbdQueue_seen_src _ _ _ y hy with h | h
            · exact hseen y h
            · exact hP s (hseen s (hwork s List.mem_cons_self)) y h

/-! ## The description is closed and least -/

/-- The walk's node set is closed under candidates. -/
theorem cbdNodes_closed (g : Graph) (roots : List Subject) :
    ∀ x, (g.cbdNodes roots).contains x = true →
      ∀ c ∈ g.cbdIndex.candidates x, (g.cbdNodes roots).contains c = true := by
  unfold Graph.cbdNodes
  refine cbdWalk_closed g.cbdIndex (cbdUniverse g) (candidates_mem_universe g) _ _ _ ?_ ?_
  · intro x hx
    unfold cbdStart at hx ⊢
    rcases cbdQueue_new_queued roots [] ∅ x hx with h | h
    · simp at h
    · exact Or.inl h
  · have h1 := cbdQueue_length_le roots [] (∅ : Std.HashSet Subject)
    have h2 := cbdUnseen_le_length (cbdUniverse g) (cbdStart roots).2
    have h3 := cbdUniverse_length g
    unfold cbdStart at h2 ⊢
    simp only [List.length_nil, Nat.zero_add] at h1
    omega

/-- The walk's node set is inside every candidate-closed set that holds the
starting nodes. -/
theorem cbdNodes_least (g : Graph) (roots : List Subject) (P : Subject → Prop)
    (hroots : ∀ r ∈ roots, P r)
    (hP : ∀ x, P x → ∀ c ∈ g.cbdIndex.candidates x, P c) :
    ∀ x, (g.cbdNodes roots).contains x = true → P x := by
  unfold Graph.cbdNodes
  refine cbdWalk_least g.cbdIndex P hP _ _ _ ?_ ?_
  · unfold cbdStart
    exact cbdQueue_queued_seen roots [] ∅ (by simp)
  · intro x hx
    unfold cbdStart at hx
    rcases cbdQueue_seen_src roots [] ∅ x hx with h | h
    · simp at h
    · exact hroots x h

/-- Clause 2: a statement in the description whose object is a blank node
brings in every statement of the graph about that blank node. -/
theorem cbd_closed_bnode (g : Graph) (roots : List Subject) (t : Triple)
    (ht : t ∈ g.cbd roots) (b : BNodeId) (hb : t.o = .bnode b) :
    ∀ t' ∈ g, t'.s = .bnode b → t' ∈ g.cbd roots := by
  intro t' ht' hs
  unfold Graph.cbd at ht ⊢
  rw [List.mem_filter] at ht ⊢
  obtain ⟨htg, htn⟩ := ht
  refine ⟨ht', ?_⟩
  rw [hs]
  apply cbdNodes_closed g roots t.s htn
  rw [mem_candidates]
  exact ⟨t, htg, rfl, Or.inl ⟨b, hb, rfl⟩⟩

/-- Clause 3, in its RDF 1.2 reading: a statement in the description brings
in every `r rdf:reifies <<( s p o )>>` statement of the graph whose triple
term is that statement, and so everything about the reifier `r`. -/
theorem cbd_closed_reifier (g : Graph) (roots : List Subject) (t : Triple)
    (ht : t ∈ g.cbd roots) :
    ∀ t' ∈ g, t'.p = L4Factoidal.RDFS.rdfReifies → ∀ p o,
      t'.o = .tripleTerm t.s p o → p = t.p → o.eqb t.o = true → t' ∈ g.cbd roots := by
  intro t' ht' hp p o hto hpt heq
  unfold Graph.cbd at ht ⊢
  rw [List.mem_filter] at ht ⊢
  obtain ⟨htg, htn⟩ := ht
  refine ⟨ht', ?_⟩
  apply cbdNodes_closed g roots t.s htn
  rw [mem_candidates]
  refine ⟨t, htg, rfl, Or.inr ?_⟩
  rw [mem_reifiersOf]
  exact ⟨t', ht', hp, p, o, hto, hpt, heq, rfl⟩

/-- The description holds nothing the two clauses do not reach: a set of
nodes `P` that holds the starting nodes and is closed under the two clauses
holds the subject of every statement in the description. -/
theorem cbd_least (g : Graph) (roots : List Subject) (P : Subject → Prop)
    (hroots : ∀ r ∈ roots, P r)
    (hbnode : ∀ t ∈ g, P t.s → ∀ b, t.o = .bnode b → P (.bnode b))
    (hreif : ∀ t ∈ g, P t.s → ∀ t' ∈ g, t'.p = L4Factoidal.RDFS.rdfReifies → ∀ p o,
      t'.o = .tripleTerm t.s p o → p = t.p → o.eqb t.o = true → P t'.s) :
    ∀ t ∈ g.cbd roots, P t.s := by
  intro t ht
  unfold Graph.cbd at ht
  rw [List.mem_filter] at ht
  refine cbdNodes_least g roots P hroots ?_ t.s ht.2
  intro x hx c hc
  rw [mem_candidates] at hc
  obtain ⟨t0, ht0, rfl, hc⟩ := hc
  rcases hc with ⟨b, hb, rfl⟩ | hc
  · exact hbnode t0 ht0 hx b hb
  · rw [mem_reifiersOf] at hc
    obtain ⟨t', ht', hp, p, o, hto, hpt, heq, rfl⟩ := hc
    exact hreif t0 ht0 hx t' ht' hp p o hto hpt heq

#print axioms cbd_closed_bnode
#print axioms cbd_closed_reifier
#print axioms cbd_least

end L4Factoidal.RDF
