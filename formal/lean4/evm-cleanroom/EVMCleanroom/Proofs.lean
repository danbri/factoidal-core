import EVMCleanroom.Core
/-! Properties about the *implemented* subset, not an Ethereum consensus proof. -/

namespace EVMCleanroom

/-- Every Word value is actually below 2^256. -/
theorem word_bounded (x : Word) : x.val < modulus := x.isLt

/-- Addition is commutative modulo 2^256. -/
theorem word_add_comm (a b : Word) : a.add b = b.add a := by
  simp only [Word.add, Nat.add_comm]

/-- Each successful commit preserves the EVM's 1024-word stack limit. -/
theorem commit_stack_bounded {s out : State} {pc cost : Nat}
    {xs : List Word} {halt : Bool} {nextMemory : Option Memory} {nextStorage : Option Storage} {nextLog : Option LogEntry}
    (_h : commit s pc xs cost halt nextMemory nextStorage nextLog = .ok out) :
    out.stack.items.length ≤ 1024 := out.stack.bounded

/-- Gas never increases on a successful committed transition. -/
theorem commit_gas_nonincreasing {s out : State} {pc cost : Nat}
    {xs : List Word} {halt : Bool} {nextMemory : Option Memory} {nextStorage : Option Storage} {nextLog : Option LogEntry}
    (h : commit s pc xs cost halt nextMemory nextStorage nextLog = .ok out) : out.gas ≤ s.gas := by
  unfold commit at h
  split at h
  · split at h
    · cases h
      exact Nat.sub_le _ _
    · cases h
  · cases h

/-- A transition cannot change bytecode. -/
theorem commit_code_unchanged {s out : State} {pc cost : Nat}
    {xs : List Word} {halt : Bool} {nextMemory : Option Memory} {nextStorage : Option Storage} {nextLog : Option LogEntry}
    (h : commit s pc xs cost halt nextMemory nextStorage nextLog = .ok out) : out.code = s.code := by
  unfold commit at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h

/-- Exact successful gas accounting: the declared opcode cost is
    deducted, never rounded or silently refunded. -/
theorem commit_gas_exact {s out : State} {pc cost : Nat}
    {xs : List Word} {halt : Bool} {nextMemory : Option Memory} {nextStorage : Option Storage} {nextLog : Option LogEntry}
    (h : commit s pc xs cost halt nextMemory nextStorage nextLog = .ok out) :
    out.gas + cost = s.gas := by
  unfold commit at h
  split at h
  · split at h
    · cases h
      dsimp
      omega
    · cases h
  · cases h

/-- A successful commit cannot silently switch the active fork profile. -/
theorem commit_profile_unchanged {s out : State} {pc cost : Nat}
    {xs : List Word} {halt : Bool} {nextMemory : Option Memory} {nextStorage : Option Storage} {nextLog : Option LogEntry}
    (h : commit s pc xs cost halt nextMemory nextStorage nextLog = .ok out) :
    out.profile = s.profile := by
  unfold commit at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h

/-- The *whole* opcode dispatcher preserves bytecode, not just the
    low-level commit helper. All successful instruction execution passes
    through a single checked state-transition boundary. -/
theorem step_code_unchanged {s out : State} (h : step s = .ok out) :
    out.code = s.code := by
  cases hp : planStep s with
  | error e =>
    simp [step, hp] at h
  | ok p =>
    have hc : commit s p.nextPC p.stack p.gasCost p.halt p.nextMemory p.nextStorage p.nextLog = .ok out := by
      simpa [step, hp] using h
    exact commit_code_unchanged hc

/-- Every successful opcode step consumes a nonnegative amount of gas. -/
theorem step_gas_nonincreasing {s out : State} (h : step s = .ok out) :
    out.gas ≤ s.gas := by
  cases hp : planStep s with
  | error e =>
    simp [step, hp] at h
  | ok p =>
    have hc : commit s p.nextPC p.stack p.gasCost p.halt p.nextMemory p.nextStorage p.nextLog = .ok out := by
      simpa [step, hp] using h
    exact commit_gas_nonincreasing hc

/-- A valid opcode transition preserves the fork selector. -/
theorem step_profile_unchanged {s out : State} (h : step s = .ok out) :
    out.profile = s.profile := by
  cases hp : planStep s with
  | error e =>
    simp [step, hp] at h
  | ok p =>
    have hc : commit s p.nextPC p.stack p.gasCost p.halt p.nextMemory p.nextStorage p.nextLog = .ok out := by
      simpa [step, hp] using h
    exact commit_profile_unchanged hc

/-- A successful opcode step always has a reconstructible, exact gas bill. -/
theorem step_has_exact_bill {s out : State} (h : step s = .ok out) :
    ∃ p : Plan, planStep s = .ok p ∧ out.gas + p.gasCost = s.gas := by
  cases hp : planStep s with
  | error e =>
    simp [step, hp] at h
  | ok p =>
    have hc : commit s p.nextPC p.stack p.gasCost p.halt p.nextMemory p.nextStorage p.nextLog = .ok out := by
      simpa [step, hp] using h
    exact ⟨p, rfl, commit_gas_exact hc⟩


/-- A successful commit cannot rewrite the transaction-original slot map,
    regardless of the instruction's proposed storage update. -/
theorem commit_original_unchanged {s out : State} {pc cost : Nat}
    {xs : List Word} {halt : Bool} {nextMemory : Option Memory}
    {nextStorage : Option Storage} {nextLog : Option LogEntry}
    (h : commit s pc xs cost halt nextMemory nextStorage nextLog = .ok out)
    (key : Nat) :
    out.storage.original key = s.storage.original key := by
  unfold commit at h
  split at h
  · split at h
    · cases h
      cases nextStorage with
      | none => rfl
      | some planned => by_cases hs : s.readOnly <;> simp [hs]
    · cases h
  · cases h

/-- Even a malformed plan cannot alter current storage via a successful
    commit inside a read-only frame. Warming reads remains permissible. -/
theorem commit_static_current_unchanged {s out : State} {pc cost : Nat}
    {xs : List Word} {halt : Bool} {nextMemory : Option Memory}
    {nextStorage : Option Storage} {nextLog : Option LogEntry}
    (h : commit s pc xs cost halt nextMemory nextStorage nextLog = .ok out)
    (hs : s.readOnly = true) (key : Nat) :
    out.storage.current key = s.storage.current key := by
  unfold commit at h
  split at h
  · split at h
    · cases h
      cases nextStorage <;> simp [hs]
    · cases h
  · cases h

/-- All successful actual opcode steps preserve the transaction's
    original storage snapshot; the property does not rely on preselected
    opcode examples. -/
theorem step_original_unchanged {s out : State}
    (h : step s = .ok out) (key : Nat) :
    out.storage.original key = s.storage.original key := by
  cases hp : planStep s with
  | error e => simp [step, hp] at h
  | ok p =>
    have hc : commit s p.nextPC p.stack p.gasCost p.halt
      p.nextMemory p.nextStorage p.nextLog = .ok out := by
      simpa [step, hp] using h
    exact commit_original_unchanged hc key

/-- Arbitrarily many successful opcode steps, without a fuel assumption. -/
inductive Trace : State → State → Prop where
  | nil (s : State) : Trace s s
  | cons {s mid out : State} (h : step s = .ok mid)
      (tail : Trace mid out) : Trace s out

/-- Gas can never increase along a finite sequence of successful steps. -/
theorem Trace.gas_nonincreasing {s out : State} (h : Trace s out) :
    out.gas ≤ s.gas := by
  induction h with
  | nil _ => exact Nat.le_refl _
  | cons hs _ ih =>
    exact Nat.le_trans ih (step_gas_nonincreasing hs)

/-- Bytecode is invariant along arbitrarily long successful traces. -/
theorem Trace.code_unchanged {s out : State} (h : Trace s out) :
    out.code = s.code := by
  induction h with
  | nil _ => rfl
  | cons hs _ ih =>
    exact ih.trans (step_code_unchanged hs)


/-- The original slot map is immutable over arbitrarily long successful
    execution traces, even when many SSTOREs change the current values. -/
theorem Trace.original_unchanged {s out : State}
    (h : Trace s out) (key : Nat) :
    out.storage.original key = s.storage.original key := by
  induction h with
  | nil _ => rfl
  | cons hs _ ih =>
    exact ih.trans (step_original_unchanged hs key)

/-- An independent *billing witness* records the exact instruction plans,
    not merely the observed difference in initial/final gas. -/
inductive BilledTrace : State → Nat → State → Prop where
  | nil (s : State) : BilledTrace s 0 s
  | cons {s mid out : State} {p : Plan} {spent : Nat}
      (hp : planStep s = .ok p)
      (hc : commit s p.nextPC p.stack p.gasCost p.halt p.nextMemory p.nextStorage p.nextLog = .ok mid)
      (tail : BilledTrace mid spent out) :
      BilledTrace s (p.gasCost + spent) out

/-- Global conservation of gas on any billed execution trace. -/
theorem BilledTrace.gas_exact {s out : State} {spent : Nat}
    (h : BilledTrace s spent out) :
    out.gas + spent = s.gas := by
  induction h with
  | nil _ => simp
  | cons _ hc _ ih =>
    have hcost := commit_gas_exact hc
    omega

/-- Erasing billing evidence gives a real interpreter execution trace. -/
theorem BilledTrace.toTrace {s out : State} {spent : Nat}
    (h : BilledTrace s spent out) : Trace s out := by
  induction h with
  | nil s => exact Trace.nil s
  | cons hp hc _ ih =>
    apply Trace.cons
    · simpa [step, hp] using hc
    · exact ih

#print axioms commit_gas_exact
#print axioms step_code_unchanged
#print axioms step_gas_nonincreasing
#print axioms step_has_exact_bill
#print axioms Trace.gas_nonincreasing
#print axioms Trace.code_unchanged
#print axioms BilledTrace.gas_exact
#print axioms BilledTrace.toTrace

/-- Every *actual successful run* admits a finite sequence of
    transitions from the concrete opcode interpreter. This bridge prevents
    trace properties from applying only to fabricated abstract traces. -/
theorem run_toTrace (fuel : Nat) {s out : State}
    (h : run fuel s = .ok out) : Trace s out := by
  induction fuel generalizing s out with
  | zero =>
    simp [run] at h
  | succ n ih =>
    cases hh : s.halted with
    | true =>
      have hsout : s = out := by
        simpa [run, hh] using h
      subst out
      exact Trace.nil s
    | false =>
      simp [run, hh] at h
      cases hs : step s with
      | error e =>
        simp [hs] at h
      | ok next =>
        simp [hs] at h
        cases hn : next.halted with
        | true =>
          have hout : next = out := by
            simpa [hn] using h
          subst out
          exact Trace.cons hs (Trace.nil next)
        | false =>
          have ht : run n next = .ok out := by
            simpa [hn] using h
          exact Trace.cons hs (ih ht)

/-- Every finite interpreter trace has an exact cost-labelled witness,
    without constructing arbitrary costs post hoc. The witness is built
    from the dispatcher's Plan at each step. -/
theorem Trace.canBill {s out : State} (h : Trace s out) :
    ∃ spent : Nat, BilledTrace s spent out := by
  induction h with
  | nil s =>
    exact ⟨0, BilledTrace.nil s⟩
  | cons hs _ ih =>
    obtain ⟨amount, hbill⟩ := ih
    obtain ⟨p, hp, _⟩ := step_has_exact_bill hs
    have hc := hs
    simp [step, hp] at hc
    exact ⟨p.gasCost + amount, BilledTrace.cons hp hc hbill⟩

/-- Every successful executable run has a *certified exact gas bill*.
    This is a theorem about all accepted runs, not just a manually
    constructed billing trace. -/
theorem run_has_exact_bill (fuel : Nat) {s out : State}
    (h : run fuel s = .ok out) :
    ∃ spent : Nat, BilledTrace s spent out ∧ out.gas + spent = s.gas := by
  obtain ⟨spent, hbill⟩ := Trace.canBill (run_toTrace fuel h)
  exact ⟨spent, hbill, BilledTrace.gas_exact hbill⟩

/-- Runtime corollary: no successful execution can increase gas. -/
theorem run_gas_nonincreasing (fuel : Nat) {s out : State}
    (h : run fuel s = .ok out) : out.gas ≤ s.gas :=
  Trace.gas_nonincreasing (run_toTrace fuel h)

/-- Runtime corollary: executed bytecode remains unchanged. -/
theorem run_code_unchanged (fuel : Nat) {s out : State}
    (h : run fuel s = .ok out) : out.code = s.code :=
  Trace.code_unchanged (run_toTrace fuel h)

#print axioms run_toTrace
#print axioms Trace.canBill
#print axioms run_has_exact_bill
#print axioms run_gas_nonincreasing
#print axioms run_code_unchanged


/-- Every *successful executable run*, including runs with SSTORE, keeps
    the starting transaction-original values at every slot. -/
theorem run_original_unchanged (fuel : Nat) {s out : State}
    (h : run fuel s = .ok out) (key : Nat) :
    out.storage.original key = s.storage.original key :=
  Trace.original_unchanged (run_toTrace fuel h) key

#print axioms commit_original_unchanged
#print axioms commit_static_current_unchanged
#print axioms step_original_unchanged
#print axioms Trace.original_unchanged
#print axioms run_original_unchanged

/-- Even if a PUSH1 data byte equals the JUMPDEST opcode (0x5b),
    it is not an executable instruction boundary. This holds for every
    possible immediate byte, not just a particular example. -/
theorem push1_payload_not_jumpdest (payload : UInt8) :
    validJumpdest #[0x60, payload, 0x5b] 1 = false := by
  rfl

/-- The genuine JUMPDEST just after that immediate is executable.
    Together these are the minimal witness to PUSH-aware jump analysis. -/
theorem push1_following_jumpdest (payload : UInt8) :
    validJumpdest #[0x60, payload, 0x5b] 2 = true := by
  rfl

#print axioms push1_payload_not_jumpdest
#print axioms push1_following_jumpdest

#print axioms word_add_comm
#print axioms commit_stack_bounded
#print axioms commit_gas_nonincreasing
#print axioms commit_code_unchanged

end EVMCleanroom
