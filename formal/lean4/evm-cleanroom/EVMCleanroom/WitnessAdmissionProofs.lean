import EVMCleanroom.WitnessAdmission

namespace EVMCleanroom.WitnessAdmission

open CallTransaction

/-- Kind: resource refusal.
Says: a nonempty account suffix at the account-count boundary is refused.
Does not say: this implementation limit is an Ethereum validity rule. -/
theorem account_count_exhausted (input : AccountInput) (rest : List AccountInput) (budget : Budget) :
    scanAccounts 0 (input :: rest) budget = .error .resourceLimit := rfl

/-- Kind: resource refusal.
Says: a nonempty storage suffix at the per-account boundary is refused.
Does not say: all protocol-valid witness inventories fit this interface. -/
theorem slot_count_exhausted (input : StorageInput) (rest : List StorageInput) (budget : Budget) :
    scanSlots 0 (input :: rest) budget = .error .resourceLimit := rfl

/-- Kind: resource refusal.
Says: crossing the aggregate byte limit yields the resource constructor.
Does not say: the compiled runtime has a universal physical memory bound. -/
theorem byte_budget_refused (budget : Budget) (amount : Nat)
    (h : budget.bytes + amount > maxWitnessBytes) :
    addBytes budget amount = .error .resourceLimit := by
  simp only [addBytes, h, if_pos]

/-- Kind: resource refusal.
Says: the per-proof count guard refuses before the node scan begins.
Does not say: a larger proof is an invalid Ethereum block. -/
theorem proof_count_refused (budget : Budget) (proof : Array (Array UInt8))
    (h : proof.size > MPT.maxProofNodes) :
    scanProof budget proof = .error .resourceLimit := by
  simp only [scanProof, h, if_pos]

/-- Kind: executable composition.
Says: a failed preflight propagates without entering the account-admission loop.
Does not say: source evaluation alone proves native timing or allocation bounds. -/
theorem preflight_refused (a : Keccak.Acceptance) (root : Array UInt8)
    (inputs : List AccountInput) (error : Error)
    (h : preflight root inputs = .error error) :
    admit a root inputs = .error error := by
  simp only [admit, h]

/-- Kind: executable authentication linkage.
Says: any admitted account consumed the actual trie lookup at the hashed address
under the supplied root, and its exact lookup result fed account decoding.
Does not say: the root belongs to the canonical chain or Keccak is refined. -/
theorem account_lookup_connected (a : Keccak.Acceptance) (root : Array UInt8)
    (input : AccountInput) (witness : WitnessAccount)
    (h : admitAccount a root input = .ok witness) :
    ∃ value, MPT.lookup a root (accountKey a input.address) input.accountProof = .ok value ∧
      accountFromProof a input value = .ok witness := by
  cases hp : MPT.lookup a root (accountKey a input.address) input.accountProof with
  | error error =>
    cases error <;> simp only [admitAccount, hp, fromMPT] at h <;> cases h
  | ok value =>
    refine ⟨value, rfl, ?_⟩
    simpa only [admitAccount, hp, fromMPT] using h

/-- Kind: executable authentication linkage.
Says: each admitted slot consumed the actual lookup at its own hashed word key.
Does not say: a missing proof can establish nonmembership. -/
theorem storage_lookup_connected (a : Keccak.Acceptance) (root : Array UInt8)
    (input : StorageInput) (slot : Slot)
    (h : admitStorage a root input = .ok slot) :
    ∃ value, MPT.lookup a root (storageKey a input.key) input.proof = .ok value ∧
      storageFromProof input value = .ok slot := by
  cases hp : MPT.lookup a root (storageKey a input.key) input.proof with
  | error error =>
    cases error <;> simp only [admitStorage, hp, fromMPT] at h <;> cases h
  | ok value =>
    refine ⟨value, rfl, ?_⟩
    simpa only [admitStorage, hp, fromMPT] using h

/-- Kind: executable storage interpretation.
Says: authenticated slot absence produces the requested key with value zero.
Does not say: a failing lookup is absence. -/
theorem absent_storage_zero (input : StorageInput) :
    storageFromProof input none = .ok { key := input.key, value := 0 } := rfl

/-- Kind: executable account decoding linkage.
Says: a present lookup result must pass the actual account decoder, and that
decoded leaf is the one passed to the code/storage commitment checker.
Does not say: account RLP refinement has been established independently. -/
theorem present_account_decoded (a : Keccak.Acceptance) (input : AccountInput)
    (raw : Array UInt8) (witness : WitnessAccount)
    (h : accountFromProof a input (some raw) = .ok witness) :
    ∃ leaf, readAccount raw = .ok leaf ∧ checkedAccount a input leaf = .ok witness := by
  cases hd : readAccount raw with
  | error error => simp only [accountFromProof, hd] at h; cases h
  | ok leaf =>
    refine ⟨leaf, rfl, ?_⟩
    simpa only [accountFromProof, hd] using h

/-- Kind: executable commitment and projection linkage.
Says: a checked present account's code hashes to the proved code commitment;
its slots are admitted against that leaf's storage root; returned fields are
exactly the decoded nonce/balance and admitted code/slots.
Does not say: complete trie reconstruction or cryptographic security is proved. -/
theorem checked_account_fields (a : Keccak.Acceptance) (input : AccountInput)
    (leaf : AccountLeaf) (witness : WitnessAccount)
    (h : checkedAccount a input leaf = .ok witness) :
    MPT.hashBytes a input.code = leaf.codeHash ∧
      ∃ storage, admitStorageList a leaf.storageRoot input.storage = .ok storage ∧
        witness = accountFromLeaf input leaf storage := by
  by_cases hc : MPT.hashBytes a input.code = leaf.codeHash
  · refine ⟨hc, ?_⟩
    cases hs : admitStorageList a leaf.storageRoot input.storage with
    | error error => simp only [checkedAccount, if_pos hc, hs] at h; cases h
    | ok storage =>
      refine ⟨storage, rfl, ?_⟩
      have hw : accountFromLeaf input leaf storage = witness := by
        simpa only [checkedAccount, if_pos hc, hs, Except.ok.injEq] using h
      exact hw.symm
  · simp only [checkedAccount, if_neg hc] at h
    cases h

/-- Kind: executable storage output coverage.
Says: every new slot returned by the tail loop came from successful admission
of an input key under this same storage root.
Does not say: unrequested keys have been witnessed or can be accessed. -/
theorem storage_loop_covered (a : Keccak.Acceptance) (root : Array UInt8)
    (inputs : List StorageInput) (acc slots : List Slot)
    (h : storageLoop a root inputs acc = .ok slots) :
    ∀ slot ∈ slots, slot ∈ acc ∨
      ∃ input ∈ inputs, admitStorage a root input = .ok slot := by
  induction inputs generalizing acc slots with
  | nil =>
    have hs : acc.reverse = slots := by
      simpa only [storageLoop, Except.ok.injEq] using h
    subst slots
    intro slot hs
    exact Or.inl (List.mem_reverse.mp hs)
  | cons input rest ih =>
    cases ha : admitStorage a root input with
    | error error => simp only [storageLoop, ha] at h; cases h
    | ok value =>
      have ht : storageLoop a root rest (value :: acc) = .ok slots := by
        simpa only [storageLoop, ha] using h
      intro slot hs
      rcases ih (value :: acc) slots ht slot hs with hm | hm
      · rcases List.mem_cons.mp hm with he | he
        · subst slot
          exact Or.inr ⟨input, List.mem_cons_self, ha⟩
        · exact Or.inl he
      · rcases hm with ⟨other, ho, hr⟩
        exact Or.inr ⟨other, List.mem_cons_of_mem _ ho, hr⟩

/-- Kind: executable storage authentication linkage.
Says: every slot returned by actual list admission has an input whose hashed
key was looked up by MPT under exactly this root, and the result decoded to it.
Does not say: lookup success establishes canonical-chain membership. -/
theorem admitted_storage_connected (a : Keccak.Acceptance) (root : Array UInt8)
    (inputs : List StorageInput) (slots : List Slot)
    (h : admitStorageList a root inputs = .ok slots) :
    ∀ slot ∈ slots, ∃ input ∈ inputs, ∃ value,
      MPT.lookup a root (storageKey a input.key) input.proof = .ok value ∧
      storageFromProof input value = .ok slot := by
  intro slot hs
  have hl : storageLoop a root inputs [] = .ok slots := h
  rcases storage_loop_covered a root inputs [] slots hl slot hs with ha | ha
  · cases ha
  · rcases ha with ⟨input, hi, hadmit⟩
    exact ⟨input, hi, storage_lookup_connected a root input slot hadmit⟩

/-- Kind: executable output coverage.
Says: every new witness returned by the tail loop came from a successful
admission of an input under this same root; no unauthenticated value is added.
Does not say: the root is authenticated by a consensus client. -/
theorem account_loop_covered (a : Keccak.Acceptance) (root : Array UInt8)
    (inputs : List AccountInput) (acc witnesses : List WitnessAccount)
    (h : accountLoop a root inputs acc = .ok witnesses) :
    ∀ witness ∈ witnesses, witness ∈ acc ∨
      ∃ input ∈ inputs, admitAccount a root input = .ok witness := by
  induction inputs generalizing acc witnesses with
  | nil =>
    have hw : acc.reverse = witnesses := by
      simpa only [accountLoop, Except.ok.injEq] using h
    subst witnesses
    intro witness hw
    exact Or.inl (List.mem_reverse.mp hw)
  | cons input rest ih =>
    cases ha : admitAccount a root input with
    | error error => simp only [accountLoop, ha] at h; cases h
    | ok value =>
      have ht : accountLoop a root rest (value :: acc) = .ok witnesses := by
        simpa only [accountLoop, ha] using h
      intro witness hw
      rcases ih (value :: acc) witnesses ht witness hw with hm | hm
      · rcases List.mem_cons.mp hm with he | he
        · subst witness
          exact Or.inr ⟨input, List.mem_cons_self, ha⟩
        · exact Or.inl he
      · rcases hm with ⟨other, ho, hr⟩
        exact Or.inr ⟨other, List.mem_cons_of_mem _ ho, hr⟩

/-- Kind: public admission coverage.
Says: every witness returned by the exported admission entry has an actual
successful input admission under its supplied root, after preflight.
Does not say: a transaction signature, header or full state has been validated. -/
theorem admitted_witnesses_connected (a : Keccak.Acceptance) (root : Array UInt8)
    (inputs : List AccountInput) (witnesses : List WitnessAccount)
    (h : admit a root inputs = .ok witnesses) :
    preflight root inputs = .ok () ∧
      ∀ witness ∈ witnesses, ∃ input ∈ inputs, admitAccount a root input = .ok witness := by
  cases hp : preflight root inputs with
  | error error => simp only [admit, hp] at h; cases h
  | ok done =>
    cases done
    refine ⟨rfl, ?_⟩
    have hl : accountLoop a root inputs [] = .ok witnesses := by
      simpa only [admit, hp] using h
    intro witness hw
    rcases account_loop_covered a root inputs [] witnesses hl witness hw with ha | ha
    · cases ha
    · exact ha

/-- Kind: executable inventory preservation.
Says: successful account traversal returns exactly as many accounts as the
input list and accumulated prefix contain together.
Does not say: this count establishes account identity or complete EVM coverage. -/
theorem account_loop_length (a : Keccak.Acceptance) (root : Array UInt8)
    (inputs : List AccountInput) (acc witnesses : List WitnessAccount)
    (h : accountLoop a root inputs acc = .ok witnesses) :
    witnesses.length = inputs.length + acc.length := by
  induction inputs generalizing acc witnesses with
  | nil =>
    have hw : acc.reverse = witnesses := by
      simpa only [accountLoop, Except.ok.injEq] using h
    subst witnesses
    simp only [List.length_reverse, List.length_nil, Nat.zero_add]
  | cons input rest ih =>
    cases ha : admitAccount a root input with
    | error error => simp only [accountLoop, ha] at h; cases h
    | ok value =>
      have ht : accountLoop a root rest (value :: acc) = .ok witnesses := by
        simpa only [accountLoop, ha] using h
      have hn := ih (value :: acc) witnesses ht
      simp only [List.length_cons] at hn ⊢
      omega

/-- Kind: public inventory preservation.
Says: the actual exported admission entry returns exactly as many witnesses as
there are inputs; output authentication is established by separate linkage lemmas.
Does not say: this count alone establishes a bijection or permits unlisted accesses. -/
theorem admitted_inventory_length (a : Keccak.Acceptance) (root : Array UInt8)
    (inputs : List AccountInput) (witnesses : List WitnessAccount)
    (h : admit a root inputs = .ok witnesses) : witnesses.length = inputs.length := by
  cases hp : preflight root inputs with
  | error error => simp only [admit, hp] at h; cases h
  | ok done =>
    cases done
    have hl : accountLoop a root inputs [] = .ok witnesses := by
      simpa only [admit, hp] using h
    simpa only [List.length_nil, Nat.add_zero] using
      account_loop_length a root inputs [] witnesses hl

/-- Kind: runner refusal composition.
Says: proof-admission failure returns indeterminate and never a completed list.
Does not say: malformed witness evidence proves an Ethereum block invalid. -/
theorem authentication_refused (a : Keccak.Acceptance) (input : TransactionList.Input)
    (accounts : List AccountInput) (error : Error)
    (h : admit a (HeaderRLP.field input.parent 3) accounts = .error error) :
    runAuthenticated a input accounts = .indeterminate none error.unavailable := by
  simp only [runAuthenticated, h]

/-- Kind: actual execution authentication linkage.
Says: every accepted authenticated-list result is the existing list executor's
result on exactly the inventory admitted under field 3 of its own parent header.
Does not say: signatures, canonical-chain membership or post-state roots are checked. -/
theorem authenticated_run_accepted (a : Keccak.Acceptance) (input : TransactionList.Input)
    (accounts : List AccountInput) (result : TransactionList.Result)
    (h : runAuthenticated a input accounts = .accepted result) :
    ∃ witnesses,
      admit a (HeaderRLP.field input.parent 3) accounts = .ok witnesses ∧
      hasUnusableEmptyAccount witnesses = false ∧
      TransactionList.run a (withWitnesses input witnesses) = .accepted result := by
  cases ha : admit a (HeaderRLP.field input.parent 3) accounts with
  | error error => simp only [runAuthenticated, ha] at h; cases h
  | ok witnesses =>
    cases he : hasUnusableEmptyAccount witnesses with
    | false =>
      refine ⟨witnesses, rfl, he, ?_⟩
      simpa only [runAuthenticated, ha, he, Bool.false_eq_true, if_false] using h
    | true => simp only [runAuthenticated, ha, he, if_true] at h; cases h

#print axioms account_count_exhausted
#print axioms slot_count_exhausted
#print axioms byte_budget_refused
#print axioms proof_count_refused
#print axioms preflight_refused
#print axioms account_lookup_connected
#print axioms storage_lookup_connected
#print axioms absent_storage_zero
#print axioms present_account_decoded
#print axioms checked_account_fields
#print axioms storage_loop_covered
#print axioms admitted_storage_connected
#print axioms account_loop_covered
#print axioms admitted_witnesses_connected
#print axioms account_loop_length
#print axioms admitted_inventory_length
#print axioms authentication_refused
#print axioms authenticated_run_accepted

end EVMCleanroom.WitnessAdmission
