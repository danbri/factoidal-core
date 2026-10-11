import L4Factoidal.SPARQL.StableGrouping
import Init.Data.Array.Lemmas

namespace L4Factoidal.SPARQL.StableGrouping

theorem finishRev_addRev (same : κ → κ → Bool) (key : κ) (row : α)
    (groups : List (Group κ α)) :
    finishRev (addRev same key row groups) = add same key row (finishRev groups) := by
  have anyEq : (finishRev groups).any (fun group => same key group.key) =
      groups.any (fun group => same key group.key) := by
    simp [finishRev, List.any_map, Function.comp_def]
  simp only [addRev, add, anyEq]
  split
  · simp only [finishRev, List.map_map]
    apply List.map_congr_left
    intro group _
    dsimp only [Function.comp_def]
    by_cases h : same key group.key = true <;> simp [h]
  · simp [finishRev, List.map_append]

theorem fallback_eq_fold (same : κ → κ → Bool) (key : α → κ) (value : α → β)
    (rows : List α) (groups : List (Group κ β)) :
    fallback same key value rows groups =
      rows.foldl (fun acc row => add same (key row) (value row) acc) (finishRev groups) := by
  induction rows generalizing groups with
  | nil => rfl
  | cons row rows ih =>
      simp only [fallback, List.foldl_cons]
      change fallback same key value rows (addRev same (key row) (value row) groups) = _
      rw [ih, finishRev_addRev]

variable [BEq η] [Hashable η] [LawfulBEq η]

/-- Every group has its unique address and every address names a group with
    that encoded key. The bidirectional invariant rules out stale entries. -/
structure State.Valid (encode : κ → Option η) (state : State κ η β) : Prop where
  covered : ∀ index (bound : index < state.groups.size),
    ∃ encoded, encode (state.groups[index]'bound).key = some encoded ∧
      state.positions[encoded]? = some index
  sound : ∀ encoded index, state.positions[encoded]? = some index →
    ∃ bound : index < state.groups.size,
      encode (state.groups[index]'bound).key = some encoded

theorem State.valid_empty (encode : κ → Option η) :
    State.Valid encode (State.empty : State κ η β) := by
  constructor
  · intro index bound; simp [State.empty] at bound
  · intro encoded index found; simp [State.empty] at found

theorem State.valid_add (encode : κ → Option η) (state : State κ η β)
    (valid : State.Valid encode state) (key : κ) (encoded : η)
    (admitted : encode key = some encoded) (row : β) :
    State.Valid encode (state.add key encoded row) := by
  rcases state with ⟨groups, positions⟩
  cases found : positions[encoded]? with
  | some index =>
      simp only [State.add, found]
      constructor
      · intro j bound
        rcases valid.covered j (by simpa using bound) with ⟨code, keyCode, address⟩
        refine ⟨code, ?_, address⟩
        simp only [Array.getElem_modify]
        split <;> simpa using keyCode
      · intro code j address
        rcases valid.sound code j address with ⟨bound, keyCode⟩
        refine ⟨by simpa using bound, ?_⟩
        simp only [Array.getElem_modify]
        split <;> simpa using keyCode
  | none =>
      simp only [State.add, found]
      constructor
      · intro j bound
        by_cases old : j < groups.size
        · rcases valid.covered j old with ⟨code, keyCode, address⟩
          have distinct : encoded ≠ code := by
            intro equal; subst code
            simp [found] at address
          refine ⟨code, ?_, ?_⟩
          · simpa [Array.getElem_push, old] using keyCode
          · simp [Std.HashMap.getElem?_insert, distinct, address]
        · have equal : j = groups.size := by simp only [Array.size_push] at bound; omega
          subst j
          refine ⟨encoded, ?_, ?_⟩
          · simpa using admitted
          · simp
      · intro code j address
        rw [Std.HashMap.getElem?_insert] at address
        split at address
        · rename_i equal
          have codeEq : encoded = code := eq_of_beq equal
          simp only [Option.some.injEq] at address
          subst code; subst j
          exact ⟨by simp, by simpa using admitted⟩
        · rcases valid.sound code j address with ⟨bound, keyCode⟩
          exact ⟨by simpa using Nat.lt_trans bound (Nat.lt_succ_self _),
            by simpa [Array.getElem_push, bound] using keyCode⟩

/-- A supported key's encoded identity is exactly the grouping relation.
    Unsupported keys can still use any relation through the fallback. -/
def ExactEncoder (same : κ → κ → Bool) (encode : κ → Option η) : Prop :=
  ∀ key encoded, encode key = some encoded →
    ∀ other, same key other = true ↔ encode other = some encoded

theorem State.match_index (same : κ → κ → Bool) (encode : κ → Option η)
    (exactKey : ExactEncoder same encode) (state : State κ η β)
    (valid : State.Valid encode state) (key : κ) (encoded : η)
    (admitted : encode key = some encoded) (index : Nat)
    (found : state.positions[encoded]? = some index)
    (j : Nat) (bound : j < state.groups.size) :
    same key (state.groups[j]'bound).key = (index == j) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq]
  rw [exactKey key encoded admitted]
  constructor
  · intro keyCode
    rcases valid.covered j bound with ⟨code, oldCode, address⟩
    have codeEq : code = encoded := Option.some.inj (oldCode.symm.trans keyCode)
    subst code
    exact Option.some.inj (found.symm.trans address)
  · intro equal
    subst j
    exact (valid.sound encoded index found).choose_spec

theorem State.add_eq_addRev (same : κ → κ → Bool) (encode : κ → Option η)
    (exactKey : ExactEncoder same encode) (state : State κ η β)
    (valid : State.Valid encode state) (key : κ) (encoded : η)
    (admitted : encode key = some encoded) (row : β) :
    (state.add key encoded row).groups.toList = addRev same key row state.groups.toList := by
  rcases state with ⟨groups, positions⟩
  cases found : positions[encoded]? with
  | some index =>
      rcases valid.sound encoded index found with ⟨bound, keyCode⟩
      have anyTrue : groups.toList.any (fun group => same key group.key) = true := by
        apply List.any_eq_true.mpr
        refine ⟨groups[index]'bound, ?_, (exactKey key encoded admitted _).mpr keyCode⟩
        apply List.mem_iff_getElem.mpr
        exact ⟨index, by simpa using bound, by simp⟩
      simp only [State.add, found, addRev, anyTrue, ↓reduceIte]
      apply List.ext_getElem
      · simp
      · intro j leftBound rightBound
        have oldBound : j < groups.size := by simpa using rightBound
        have sameIndex := State.match_index same encode exactKey ⟨groups, positions⟩ valid
          key encoded admitted index found j oldBound
        simp only [List.getElem_map, Array.getElem_toList, Array.getElem_modify]
        simp only [sameIndex, beq_iff_eq]
  | none =>
      have anyFalse : groups.toList.any (fun group => same key group.key) = false := by
        apply List.any_eq_false.mpr
        intro group member
        rcases List.mem_iff_getElem.mp member with ⟨j, bound, equal⟩
        subst group
        intro matched
        have keyCode := (exactKey key encoded admitted _).mp matched
        rcases valid.covered j (by simpa using bound) with ⟨code, oldCode, address⟩
        have codeEq : code = encoded := Option.some.inj (oldCode.symm.trans keyCode)
        subst code
        simp [found] at address
      simp [State.add, found, addRev, anyFalse]

theorem hashFrom_eq_fold (same : κ → κ → Bool) (encode : κ → Option η)
    (exactKey : ExactEncoder same encode) (key : α → κ) (value : α → β)
    (rows : List α) (state : State κ η β) (valid : State.Valid encode state) :
    hashFrom same encode key value rows state =
      rows.foldl (fun acc row => add same (key row) (value row) acc)
        (finishRev state.groups.toList) := by
  induction rows generalizing state with
  | nil => rfl
  | cons row rows ih =>
      cases admitted : encode (key row) with
      | none =>
          simp only [hashFrom, admitted, fallback_eq_fold, finishRev_addRev, List.foldl_cons]
      | some encoded =>
          simp only [hashFrom, admitted, List.foldl_cons]
          rw [ih _ (State.valid_add encode state valid (key row) encoded admitted (value row)),
            State.add_eq_addRev same encode exactKey state valid (key row) encoded admitted,
            finishRev_addRev]

/-- Complete group order and row order agree for every input sequence.
    No equivalence-relation premise is imposed on unsupported keys. -/
theorem fast_eq (same : κ → κ → Bool) (encode : κ → Option η)
    (exactKey : ExactEncoder same encode) (key : α → κ) (value : α → β) (rows : List α) :
    fast same encode key value rows = reference same key value rows := by
  rw [fast, hashFrom_eq_fold same encode exactKey key value rows State.empty (State.valid_empty encode)]
  rfl

#print axioms finishRev_addRev
#print axioms State.valid_add
#print axioms fast_eq

end L4Factoidal.SPARQL.StableGrouping
