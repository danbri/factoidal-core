import Beacon.Transition

/-!
# Theorems about the beacon state transition

Each theorem is about the executable definitions in this directory; none
relates them to the consensus specification, which is checked by the
official vectors (tests, not proofs). Every theorem's comment names its
kind and states what it says and does not say.
-/

namespace Beacon

/-! ## Slots -/

/-- Kind: invariant. Says: a successful slot step raises the slot number by
    exactly one. Does not say: the caches or the epoch processing inside
    the step agree with the specification. -/
theorem slotStep_slot (c : Ctx) (x x' : BeaconState × HashCache) (h : slotStep c x = .ok x') :
    x'.1.slot = x.1.slot + 1 := by
  unfold slotStep at h
  simp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases h; rfl

/-- Kind: definitional. Says: `iterateSlots` of `n + 1` is one `slotStep`
    followed by `iterateSlots` of `n`. Does not say: anything about the
    step itself. -/
theorem iterateSlots_succ (c : Ctx) (n : Nat) (x : BeaconState × HashCache) :
    iterateSlots c (n + 1) x = (slotStep c x).bind (iterateSlots c n) := by
  simp only [iterateSlots]
  cases slotStep c x <;> rfl

/-- Kind: structural. Says: iterating `m + n` slot steps is iterating `m`
    and then `n`. Does not say: that either part succeeds. -/
theorem iterateSlots_add (c : Ctx) (m n : Nat) (x : BeaconState × HashCache) :
    iterateSlots c (m + n) x = (iterateSlots c m x).bind (iterateSlots c n) := by
  induction m generalizing x with
  | zero => simp [iterateSlots, Except.bind]
  | succ m ih =>
    rw [Nat.add_right_comm, iterateSlots_succ, iterateSlots_succ]
    cases slotStep c x with
    | error e => rfl
    | ok x1 => simpa [Except.bind] using ih x1

/-- Kind: invariant. Says: `n` successful slot steps raise the slot number
    by exactly `n`. Does not say: that they succeed. -/
theorem iterateSlots_slot (c : Ctx) (n : Nat) (x x' : BeaconState × HashCache)
    (h : iterateSlots c n x = .ok x') : x'.1.slot = x.1.slot + n := by
  induction n generalizing x with
  | zero => simp [iterateSlots] at h; subst h; rfl
  | succ n ih =>
    rw [iterateSlots_succ] at h
    cases hs : slotStep c x with
    | error e => simp [hs, Except.bind] at h
    | ok x1 =>
      simp only [hs, Except.bind] at h
      rw [ih x1 h, slotStep_slot c x x1 hs]
      omega

/-- Kind: characterisation. Says: an admitted `processSlots` call is
    exactly `target - slot` iterations of `slotStep` from an empty hashing
    cache; the iteration count is fixed before the first step. Does not
    say: the iteration succeeds. -/
theorem processSlots_eq_iterate (c : Ctx) (s : BeaconState) (target : Nat)
    (h : s.slot < target) (hl : target - s.slot ≤ maxSlotAdvance) :
    processSlots c s target = (iterateSlots c (target - s.slot) (s, {})).map (·.1) := by
  simp [processSlots, h, Nat.not_lt.mpr hl]

/-- Kind: postcondition. Says: a successful `processSlots` ends at exactly
    the requested slot. Does not say: which roots were cached on the way. -/
theorem processSlots_slot (c : Ctx) (s s' : BeaconState) (target : Nat)
    (h : processSlots c s target = .ok s') : s'.slot = target := by
  unfold processSlots at h
  split at h
  · split at h
    · cases h
    · cases hi : iterateSlots c (target - s.slot) (s, {}) with
      | error e => simp [hi, Except.map] at h
      | ok x =>
        simp only [hi, Except.map] at h
        cases h
        rw [iterateSlots_slot c _ _ x hi]
        simp only
        omega
  · cases h

/-- Kind: monotonicity. Says: a successful `processSlots` strictly raises
    the slot number. Does not say: by how much beyond `processSlots_slot`. -/
theorem processSlots_slot_lt (c : Ctx) (s s' : BeaconState) (target : Nat)
    (h : processSlots c s target = .ok s') : s.slot < s'.slot := by
  have ht := processSlots_slot c s s' target h
  unfold processSlots at h
  split at h
  · omega
  · cases h

/-- Kind: refusal. Says: a target slot that is not after the state's slot
    is refused with a fixed reason and no state. Does not say: later
    targets are accepted. -/
theorem processSlots_refuses_not_after (c : Ctx) (s : BeaconState) (target : Nat)
    (h : target ≤ s.slot) :
    processSlots c s target = .error "process_slots: target slot is not after the state's slot" := by
  simp [processSlots, Nat.not_lt.mpr h]

/-- Kind: resource bound. Says: an advance of more than `maxSlotAdvance`
    slots is refused before any step runs. Does not say: admitted advances
    finish within a time budget. -/
theorem processSlots_refuses_over_limit (c : Ctx) (s : BeaconState) (target : Nat)
    (h : target - s.slot > maxSlotAdvance) :
    processSlots c s target = .error "process_slots: advance above the resource limit" := by
  have hlt : s.slot < target := by unfold maxSlotAdvance at h; omega
  simp [processSlots, hlt, h]

/-- Kind: refusal. Says: a block whose slot is not after the state's slot
    is refused by `stateTransition`. Does not say: newer blocks are valid. -/
theorem stateTransition_refuses_old_block (c : Ctx) (s : BeaconState) (signed : SignedBeaconBlock)
    (validate : Bool) (h : signed.message.slot ≤ s.slot) :
    stateTransition c s signed validate =
      .error "process_slots: target slot is not after the state's slot" := by
  simp [stateTransition, processSlots_refuses_not_after c s _ h, bind, Except.bind]

/-- Kind: refusal. Says: `processBlockHeader` refuses a block whose slot
    differs from the state's slot. Does not say: equal slots are accepted. -/
theorem processBlockHeader_refuses_slot (p : Preset) (s : BeaconState) (block : BeaconBlock)
    (h : block.slot ≠ s.slot) :
    processBlockHeader p s block = .error "block header: slot differs from the state's slot" := by
  simp [processBlockHeader, ensure, h, bind, Except.bind]

/-! ## Effective balance hysteresis -/

/-- Kind: bound. Says: the updated effective balance never exceeds the
    validator's maximum, when the old one did not. Does not say: the old
    one is within the maximum. -/
theorem effectiveBalanceUpdate_le_max (v : Validator) (balance : Nat)
    (h : v.effectiveBalance ≤ v.maxEffectiveBalance) :
    effectiveBalanceUpdate v balance ≤ v.maxEffectiveBalance := by
  unfold effectiveBalanceUpdate
  simp only
  split
  · exact Nat.min_le_right _ _
  · exact h

/-- Kind: hysteresis band. Says: while the balance is at most 0.25 ETH
    below and at most 1.25 ETH above the effective balance, the effective
    balance does not move. Does not say: what happens outside the band. -/
theorem effectiveBalanceUpdate_stable (v : Validator) (balance : Nat)
    (hdown : v.effectiveBalance ≤ balance + 250000000)
    (hup : balance ≤ v.effectiveBalance + 1250000000) :
    effectiveBalanceUpdate v balance = v.effectiveBalance := by
  have h : ¬ (balance + effectiveBalanceIncrement / hysteresisQuotient * hysteresisDownwardMultiplier
        < v.effectiveBalance ∨
      v.effectiveBalance + effectiveBalanceIncrement / hysteresisQuotient * hysteresisUpwardMultiplier
        < balance) := by
    simp only [effectiveBalanceIncrement, hysteresisQuotient, hysteresisDownwardMultiplier,
      hysteresisUpwardMultiplier]
    omega
  exact if_neg h

/-- Kind: bound. Says: when the effective balance moves it becomes at most
    the actual balance. Does not say: it moves. -/
theorem effectiveBalanceUpdate_changed_le_balance (v : Validator) (balance : Nat)
    (h : effectiveBalanceUpdate v balance ≠ v.effectiveBalance) :
    effectiveBalanceUpdate v balance ≤ balance := by
  unfold effectiveBalanceUpdate at h ⊢
  simp only at h ⊢
  split
  · exact Nat.le_trans (Nat.min_le_left _ _) (Nat.sub_le _ _)
  · rename_i hn; simp [hn] at h

/-- Kind: granularity. Says: when the effective balance moves it becomes a
    whole number of 1 ETH increments. Does not say: it moves. -/
theorem effectiveBalanceUpdate_changed_multiple (v : Validator) (balance : Nat)
    (h : effectiveBalanceUpdate v balance ≠ v.effectiveBalance) :
    effectiveBalanceUpdate v balance % effectiveBalanceIncrement = 0 := by
  unfold effectiveBalanceUpdate at h ⊢
  simp only at h ⊢
  split
  · unfold Validator.maxEffectiveBalance
    simp only [effectiveBalanceIncrement, maxEffectiveBalanceElectra, minActivationBalance]
    split <;> omega
  · rename_i hn; simp [hn] at h

/-! ## Balances -/

/-- Kind: shape. Says: `increaseBalance` keeps the number of balances. -/
theorem increaseBalance_size (s : BeaconState) (i d : Nat) :
    (s.increaseBalance i d).balances.size = s.balances.size := by
  simp [BeaconState.increaseBalance]

/-- Kind: shape. Says: `decreaseBalance` keeps the number of balances. -/
theorem decreaseBalance_size (s : BeaconState) (i d : Nat) :
    (s.decreaseBalance i d).balances.size = s.balances.size := by
  simp [BeaconState.decreaseBalance]

/-- Kind: exact effect. Says: `increaseBalance i d` adds exactly `d` to
    balance `i` and leaves every other balance as it was. Does not say:
    the sum stays inside `uint64` (checked at run time by `inRange`). -/
theorem increaseBalance_get (s : BeaconState) (i d j : Nat) :
    (s.increaseBalance i d).balances[j]? =
      if i = j then (s.balances[j]?).map (· + d) else s.balances[j]? := by
  simp [BeaconState.increaseBalance, Array.getElem?_modify]

/-- Kind: exact effect. Says: `decreaseBalance i d` subtracts `d` from
    balance `i`, stopping at zero, and leaves every other balance as it
    was. -/
theorem decreaseBalance_get (s : BeaconState) (i d j : Nat) :
    (s.decreaseBalance i d).balances[j]? =
      if i = j then (s.balances[j]?).map (· - d) else s.balances[j]? := by
  simp [BeaconState.decreaseBalance, Array.getElem?_modify]

/-- Kind: conservation. Says: moving `amount` from balance `i` to a
    different balance `j`, when `i` holds at least `amount`, leaves the sum
    of the two unchanged (the step used by pending consolidations).
    Does not say: anything when `i = j` or the source is short. -/
theorem transfer_conserves (s : BeaconState) (i j amount a b : Nat) (hij : i ≠ j)
    (hi : s.balances[i]? = some a) (hj : s.balances[j]? = some b) (ha : amount ≤ a) :
    ∃ a' b', ((s.decreaseBalance i amount).increaseBalance j amount).balances[i]? = some a' ∧
      ((s.decreaseBalance i amount).increaseBalance j amount).balances[j]? = some b' ∧
      a' + b' = a + b := by
  refine ⟨a - amount, b + amount, ?_, ?_, by omega⟩
  · rw [increaseBalance_get, decreaseBalance_get]
    simp [Ne.symm hij, hi]
  · rw [increaseBalance_get, decreaseBalance_get]
    simp [hij, hj]

/-! ## Registry loops -/

/-- Kind: shape. Says: starting a validator's exit keeps the registry
    length. -/
theorem initiateValidatorExitWith_size (p : Preset) (churn : Nat) (s : BeaconState) (i : Nat) :
    (initiateValidatorExitWith p churn s i).validators.size = s.validators.size := by
  unfold initiateValidatorExitWith
  simp only
  split
  · rfl
  · simp [exitEpochAndUpdateChurn]

/-- Kind: shape. Says: one step of the registry update keeps the registry
    length. -/
theorem registryStep_size (p : Preset) (churn current finalized : Nat) (s : BeaconState) (i : Nat) :
    (registryStep p churn current finalized s i).validators.size = s.validators.size := by
  unfold registryStep
  simp only
  split
  · simp
  · split
    · exact initiateValidatorExitWith_size p churn s i
    · split
      · simp
      · rfl

/-- Kind: loop bound. Says: the registry update loop keeps the registry
    length, so its `count` steps, fixed at the registry length on entry,
    visit each validator once. Does not say: a time budget. -/
theorem registryLoop_size (p : Preset) (churn current finalized count i : Nat) (s : BeaconState) :
    (registryLoop p churn current finalized count i s).validators.size = s.validators.size := by
  induction count generalizing i s with
  | zero => rfl
  | succ n ih => simp [registryLoop, ih, registryStep_size]

/-- Kind: shape. Says: `processRegistryUpdates` keeps the registry length. -/
theorem processRegistryUpdates_size (p : Preset) (s : BeaconState) :
    (processRegistryUpdates p s).validators.size = s.validators.size :=
  registryLoop_size ..

/-- Kind: shape. Says: rewards and penalties keep the number of balances. -/
theorem processRewardsAndPenalties_size (p : Preset) (s : BeaconState) :
    (processRewardsAndPenalties p s).balances.size = s.balances.size := by
  unfold processRewardsAndPenalties
  split <;> simp

/-- Kind: shape. Says: the slashings step keeps the number of balances. -/
theorem processSlashings_size (p : Preset) (s : BeaconState) :
    (processSlashings p s).balances.size = s.balances.size := by
  simp [processSlashings]

/-- Kind: shape. Says: inactivity updates keep the number of scores. -/
theorem processInactivityUpdates_size (p : Preset) (s : BeaconState) :
    (processInactivityUpdates p s).inactivityScores.size = s.inactivityScores.size := by
  unfold processInactivityUpdates
  split <;> simp

/-- Kind: shape. Says: effective balance updates keep the registry length. -/
theorem processEffectiveBalanceUpdates_size (s : BeaconState) :
    (processEffectiveBalanceUpdates s).validators.size = s.validators.size := by
  simp [processEffectiveBalanceUpdates]

/-! ## Malformed input -/

/-- Kind: refusal. Says: a `uint64` wire value that is not eight bytes is
    refused. -/
theorem u64_decode_wrong_width (p : Preset) (b : ByteArray) (h : b.size ≠ 8) :
    Codec.u64.decode p b = .error "uint64: width" := by
  simp [Codec.u64, h]

/-- Kind: refusal. Says: a Boolean wire value that is not one byte is
    refused. -/
theorem bool_decode_wrong_width (p : Preset) (b : ByteArray) (h : b.size ≠ 1) :
    Codec.bool.decode p b = .error "boolean: width" := by
  simp [Codec.bool, h]

/-- Kind: refusal. Says: an empty byte string is not a bitlist (the
    delimiter bit is missing). -/
theorem bitlist_decode_empty (limit : Preset → Nat) (p : Preset) (b : ByteArray) (h : b.size = 0) :
    (Codec.bitlist limit).decode p b = .error "bitlist: empty" := by
  simp only [Codec.bitlist, if_pos h]

/-- Kind: refusal. Says: a byte vector of the wrong length is refused. -/
theorem bytesN_decode_wrong_width (n : Nat) (p : Preset) (b : ByteArray) (h : b.size ≠ n) :
    ∃ e, (Codec.bytesN n).decode p b = .error e := by
  simp [Codec.bytesN, h]

/-- Kind: refusal. Says: a list with more elements than its limit is
    refused after decoding. Does not say: memory used while decoding. -/
theorem byteList_decode_over_limit (limit : Preset → Nat) (p : Preset) (b : ByteArray)
    (h : limit p < b.size) :
    (Codec.byteList limit).decode p b = .error "byte list: over limit" := by
  simp [Codec.byteList, Nat.not_le.mpr h]

/-- Kind: refusal. Says: the actual payload transition returns no state
    when no fixture verdict is supplied. Does not say: a supplied verdict
    independently validates the execution payload. -/
theorem processExecutionPayload_without_verdict (c : Ctx) (s : BeaconState)
    (body : BeaconBlockBody) (h : c.fixtureExecutionVerdict = none) :
    processExecutionPayload c s body = .error "execution payload: execution verdict unavailable" := by
  simp only [processExecutionPayload, h]

/-- Kind: refusal. Says: a default context cannot accept an execution
    payload. Does not say: the independent EL is linked. -/
theorem processExecutionPayload_default_context (p : Preset) (s : BeaconState)
    (body : BeaconBlockBody) :
    processExecutionPayload { p := p } s body = .error "execution payload: execution verdict unavailable" := by
  rfl

#print axioms processExecutionPayload_without_verdict
#print axioms processExecutionPayload_default_context

#print axioms slotStep_slot
#print axioms iterateSlots_succ
#print axioms iterateSlots_add
#print axioms iterateSlots_slot
#print axioms processSlots_eq_iterate
#print axioms processSlots_slot
#print axioms processSlots_slot_lt
#print axioms processSlots_refuses_not_after
#print axioms processSlots_refuses_over_limit
#print axioms stateTransition_refuses_old_block
#print axioms processBlockHeader_refuses_slot
#print axioms effectiveBalanceUpdate_le_max
#print axioms effectiveBalanceUpdate_stable
#print axioms effectiveBalanceUpdate_changed_le_balance
#print axioms effectiveBalanceUpdate_changed_multiple
#print axioms increaseBalance_size
#print axioms decreaseBalance_size
#print axioms increaseBalance_get
#print axioms decreaseBalance_get
#print axioms transfer_conserves
#print axioms initiateValidatorExitWith_size
#print axioms registryStep_size
#print axioms registryLoop_size
#print axioms processRegistryUpdates_size
#print axioms processRewardsAndPenalties_size
#print axioms processSlashings_size
#print axioms processInactivityUpdates_size
#print axioms processEffectiveBalanceUpdates_size
#print axioms u64_decode_wrong_width
#print axioms bool_decode_wrong_width
#print axioms bitlist_decode_empty
#print axioms bytesN_decode_wrong_width
#print axioms byteList_decode_over_limit

end Beacon

namespace Beacon

/-! ## Fast paths -/

/-- Kind: auxiliary. Says: two folds over the same list agree when their
    step functions agree on the list's elements. -/
theorem foldl_congr_mem {α β : Type} (f g : α → β → α) (l : List β) (a : α)
    (h : ∀ a b, b ∈ l → f a b = g a b) : l.foldl f a = l.foldl g a := by
  induction l generalizing a with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [h a x (by simp)]
    exact ih _ (fun a b hb => h a b (by simp [hb]))

/-- Kind: fast path equals specification form. Says: `shuffledIndexWith`,
    given the pivots that `roundPivots` computes for the same seed, returns
    exactly `shuffledIndex` (the form written from `compute_shuffled_index`).
    Does not say: `shuffledIndex` matches the specification (tested by the
    vectors), nor anything about `shuffleList`. -/
theorem shuffledIndexWith_eq (p : Preset) (seed : ByteArray) (index count : Nat) :
    shuffledIndexWith (roundPivots p seed) index count seed = shuffledIndex p index count seed := by
  unfold shuffledIndexWith shuffledIndex
  have hsize : (roundPivots p seed).size = p.shuffleRoundCount := by simp [roundPivots]
  rw [hsize]
  apply foldl_congr_mem
  intro acc round hmem
  have hlt : round < p.shuffleRoundCount := List.mem_range.mp hmem
  have hp : (roundPivots p seed)[round]! = leNat (sha (seed.push (UInt8.ofNat round))) 0 8 := by
    simp [roundPivots, hlt]
  simp only [hp]

#print axioms foldl_congr_mem
#print axioms shuffledIndexWith_eq

end Beacon
