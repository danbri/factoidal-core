import EVMCleanroom.CallTransaction

/-! Theorems for the Prague and Osaka transaction gas rules added to the
ordinary call runner (EIP-7623 calldata floor, EIP-7825 gas cap). -/

namespace EVMCleanroom.CallTransaction

/-- Kind: preservation.
    Says: Shanghai and Cancun admission is unchanged by the later fork
    rules: the budget passes through untouched, with a zero floor.
    Does not say: that the Shanghai or Cancun rules are complete. -/
theorem forkGasRules_before_prague (fork : Fork) (tx : Envelope) (b : Budget)
    (h : fork = .shanghai ∨ fork = .cancun) : forkGasRules fork tx b = .ok b := by
  rcases h with h | h <;> subst h <;> rfl

/-- Kind: admission.
    Says: in Prague and Osaka an admitted budget's floor is the EIP-7623
    calldata floor and fits within the transaction gas limit.
    Does not say: that the floor formula is checked against EELS (tested only). -/
theorem forkGasRules_floor (fork : Fork) (tx : Envelope) (b b' : Budget)
    (hf : fork = .prague ∨ fork = .osaka) (h : forkGasRules fork tx b = .ok b') :
    b'.floor = calldataFloor tx.data ∧ b'.floor ≤ tx.gasLimit := by
  rcases hf with hf | hf <;> subst hf <;> unfold forkGasRules at h
  · by_cases hl : tx.gasLimit < calldataFloor tx.data
    · simp [hl] at h
    · simp [hl] at h; subst h; exact ⟨rfl, by simp only [calldataFloor] at hl ⊢; omega⟩
  · by_cases hc : tx.gasLimit > osakaGasCap
    · simp [hc] at h
    · by_cases hl : tx.gasLimit < calldataFloor tx.data
      · simp [hc, hl] at h
      · simp [hc, hl] at h; subst h; exact ⟨rfl, by simp only [calldataFloor] at hl ⊢; omega⟩

/-- Kind: admission.
    Says: Osaka refuses a transaction reserving more than 2^24 gas.
    Does not say: anything about block gas. -/
theorem forkGasRules_osaka_cap (tx : Envelope) (b : Budget) (h : tx.gasLimit > osakaGasCap) :
    forkGasRules .osaka tx b = .error "gas-limit-above-cap" := by
  simp [forkGasRules, h]

/-- Kind: gas accounting.
    Says: gas used is never below the floor once the floor fits the limit.
    Does not say: that the refund cap matches each fork (tested only). -/
theorem charge_used_ge_floor (b : Budget) (remaining : Nat) (counter : Int)
    (h : b.floor ≤ b.gasLimit) : b.floor ≤ (charge b remaining counter).used := by
  simp only [charge, Nat.min_eq_left h]
  exact Nat.le_max_right _ _

/-- Kind: preservation.
    Says: with a zero floor the bill is the pre-Prague one: gas consumed
    minus the capped refund.
    Does not say: which forks use a zero floor (see `forkGasRules_before_prague`). -/
theorem charge_zero_floor (b : Budget) (remaining : Nat) (counter : Int) (h : b.floor = 0) :
    (charge b remaining counter).used =
      (b.gasLimit - remaining) - min counter.toNat ((b.gasLimit - remaining) / 5) := by
  simp [charge, h]

#print axioms forkGasRules_before_prague
#print axioms forkGasRules_floor
#print axioms forkGasRules_osaka_cap
#print axioms charge_used_ge_floor
#print axioms charge_zero_floor

end EVMCleanroom.CallTransaction
