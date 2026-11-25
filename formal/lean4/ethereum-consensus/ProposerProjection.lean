import AuthenticatedProposer

/-! A two-field registry commitment projection after actual proposer authentication.
This deliberately omits initiate_validator_exit, slashings, balances and rewards.
The returned root is NOT a protocol post-state. Normative target:
consensus-specs d2021d2719235f0df4726a1d330502cb15aa8ea3, slash_validator. -/
namespace EthereumConsensus.SSZ.ProposerProjection

inductive ProjectionError where
  | authentication (reason : AuthenticatedProposer.AuthError)
  | epochOverflow
  | registry (reason : RegistryError)
  | proof (reason : ByteProofError)
  | projectedRegistryMismatch
  | projectedStateMismatch

structure ProjectionRequest where
  slot : UInt64
  first : BeaconBlockHeader
  second : BeaconBlockHeader
  context : ForkContext
  length : Nat
  validator : RegistryValidator
  member : List ByteArray
  registryRoot : ByteArray
  registrySiblings : List ByteArray
  slotSiblings : List ByteArray
  forkSiblings : List ByteArray
  genesisSiblings : List ByteArray
  stateRoot : ByteArray
  sigA : ByteArray
  sigB : ByteArray

structure PartialCommitment where
  validator : RegistryValidator
  projectedRegistryRoot : Chunk
  projectedStateRoot : Chunk

def markValidator (epoch : UInt64) (v : RegistryValidator) :
    Except ProjectionError RegistryValidator :=
  if epoch.toNat + 8192 ≥ 2 ^ 64 then .error .epochOverflow
  else .ok { v with slashed := true,
                    withdrawableEpoch := max v.withdrawableEpoch (UInt64.ofNat (epoch.toNat + 8192)) }

def authentication (q : ProjectionRequest) :
    Except AuthenticatedProposer.AuthError ProposerEvidence :=
  AuthenticatedProposer.authenticateState q.slot q.first q.second q.context
    q.length q.validator q.member q.registryRoot q.registrySiblings
    q.slotSiblings q.forkSiblings q.genesisSiblings q.stateRoot q.sigA q.sigB

/-- Private: the original membership paths have already been checked by authentication.
    This changes only two validator fields, not exit scheduling or any balances. -/
private def buildProjection (q : ProjectionRequest) : Except ProjectionError PartialCommitment := do
  let v ← markValidator (mainnetRegistryEpoch q.slot) q.validator
  let leaf ← (validatorRoot v).mapError ProjectionError.registry
  let len ← (uint64Root (UInt64.ofNat q.length)).mapError (fun _ => ProjectionError.registry .basicRoot)
  let registry ← (calculateByteBranch 41 (validatorRegistryGindex q.first.proposerIndex.toNat)
    leaf.bytes (q.member ++ [len.bytes])).mapError ProjectionError.proof
  let layout := mainnetRegistryLayout q.slot
  let state ← (calculateByteBranch (registryStateDepth layout) (registryStateGindex layout)
    registry.bytes q.registrySiblings).mapError ProjectionError.proof
  return ⟨v, registry, state⟩

/-- Re-admit the replacement witness with the existing registry verifier.
    This does not authenticate the original state or the proposed mutation. -/
def projectionRegistryCheck (q : ProjectionRequest) (p : PartialCommitment) :
    Except RegistryError ByteProofResult :=
  verifyValidatorAt q.length q.first.proposerIndex.toNat p.validator q.member
    p.projectedRegistryRoot.bytes

def projectionStateCheck (q : ProjectionRequest) (p : PartialCommitment) :
    Except RegistryError ByteProofResult :=
  verifyRegistryInState (mainnetRegistryLayout q.slot) p.projectedRegistryRoot.bytes
    q.registrySiblings p.projectedStateRoot.bytes

/-- Consistency check only. Mismatches of locally constructed roots are internal
    failures, not proof that the Ethereum input is invalid. -/
def acceptProjection (q : ProjectionRequest) (p : PartialCommitment) :
    Except ProjectionError PartialCommitment :=
  match projectionRegistryCheck q p with
  | .error e => .error (.registry e)
  | .ok r =>
    if r.matchesRoot then
      match projectionStateCheck q p with
      | .error e => .error (.registry e)
      | .ok t =>
        if t.matchesRoot then .ok p else .error .projectedStateMismatch
    else .error .projectedRegistryMismatch

private def projectChecked (q : ProjectionRequest) : Except ProjectionError PartialCommitment :=
  match buildProjection q with
  | .error e => .error e
  | .ok p => acceptProjection q p

/-- The only public authenticated commitment projection entry point
    authenticates the raw input before constructing and checking new roots. -/
def authenticateAndProject (q : ProjectionRequest) : Except ProjectionError PartialCommitment :=
  match authentication q with
  | .error e => .error (.authentication e)
  | .ok _ => projectChecked q

/-- Kind: admission. Says: uint64 overflow refuses.
Does not say: this can occur for an authenticated mainnet slot. -/
theorem mark_overflow (epoch : UInt64) (v : RegistryValidator)
    (h : epoch.toNat + 8192 ≥ 2 ^ 64) :
    markValidator epoch v = .error .epochOverflow := by
  simp only [markValidator, if_pos h]

/-- Kind: refinement. Says: on admitted arithmetic the entire returned record
is precisely the old record with two fields replaced. Does not implement exit scheduling. -/
theorem mark_checked (epoch : UInt64) (v : RegistryValidator)
    (h : ¬ epoch.toNat + 8192 ≥ 2 ^ 64) :
    markValidator epoch v = .ok { v with slashed := true, withdrawableEpoch := max v.withdrawableEpoch (UInt64.ofNat (epoch.toNat + 8192)) } := by
  simp only [markValidator, if_neg h]

/-- Kind: linkage. Says: failure of raw authentication cannot return any projection.
Does not establish the canonicality of the supplied state. -/
theorem authentication_error (q : ProjectionRequest) (e : AuthenticatedProposer.AuthError)
    (h : authentication q = .error e) :
    authenticateAndProject q = .error (.authentication e) := by
  simp only [authenticateAndProject, h]

/-- Kind: linkage. Says: the actual authenticated path delegates to the local
projection, rather than obtaining a replacement root from the host.
Does not prove that the partial root is a protocol post-state. -/
theorem authentication_success (q : ProjectionRequest) (e : ProposerEvidence)
    (h : authentication q = .ok e) :
    authenticateAndProject q = projectChecked q := by
  simp only [authenticateAndProject, h]

/-- Kind: security linkage. Says: acceptance retains the exact candidate and
both actual witness checks must succeed with matching roots.
Does not say: the old state is authentic or the mutation is protocol-complete. -/
theorem accepted_projection (q : ProjectionRequest) (p out : PartialCommitment)
    (h : acceptProjection q p = .ok out) :
    out = p ∧ ∃ r t : ByteProofResult,
      projectionRegistryCheck q p = .ok r ∧ r.matchesRoot = true ∧
      projectionStateCheck q p = .ok t ∧ t.matchesRoot = true := by
  cases hr : projectionRegistryCheck q p with
  | error e => simp [acceptProjection, hr] at h
  | ok r =>
    cases hb : r.matchesRoot with
    | false => simp [acceptProjection, hr, hb] at h
    | true =>
      cases ht : projectionStateCheck q p with
      | error e => simp [acceptProjection, hr, hb, ht] at h
      | ok t =>
        cases hc : t.matchesRoot with
        | false => simp [acceptProjection, hr, hb, ht, hc] at h
        | true =>
          have he : p = out := by simpa [acceptProjection, hr, hb, ht, hc] using h
          exact ⟨he.symm, r, t, by simp [hr], hb, by simp [ht], hc⟩

/-- Kind: linkage. Says: both real BLS verdicts are true on evidence obtained
from the raw request. Does not say: BLS is mathematically refined. -/
theorem authentication_verdicts (q : ProjectionRequest) (e : ProposerEvidence)
    (h : authentication q = .ok e) :
    AuthenticatedProposer.firstVerdict e q.sigA = .ok true ∧
    AuthenticatedProposer.secondVerdict e q.sigB = .ok true := by
  have hs := AuthenticatedProposer.state_success q.slot q.first q.second q.context
    q.length q.validator q.member q.registryRoot q.registrySiblings
    q.slotSiblings q.forkSiblings q.genesisSiblings q.stateRoot q.sigA q.sigB e h
  exact hs.2

/-- Kind: security linkage. Says: success of the exported raw-input path
requires both concrete BLS verdicts and both concrete replacement membership
verdicts on the returned roots. Does not say: a complete consensus post-state,
canonical state, collision resistance, or normative cryptographic refinement. -/
theorem successful_projection (q : ProjectionRequest) (out : PartialCommitment)
    (h : authenticateAndProject q = .ok out) :
    ∃ (e : ProposerEvidence) (r t : ByteProofResult),
      authentication q = .ok e ∧
      AuthenticatedProposer.firstVerdict e q.sigA = .ok true ∧
      AuthenticatedProposer.secondVerdict e q.sigB = .ok true ∧
      projectionRegistryCheck q out = .ok r ∧ r.matchesRoot = true ∧
      projectionStateCheck q out = .ok t ∧ t.matchesRoot = true := by
  cases ha : authentication q with
  | error e =>
    rw [authentication_error q e ha] at h
    cases h
  | ok e =>
    have hs := h
    rw [authentication_success q e ha] at hs
    cases hp : buildProjection q with
    | error reason =>
      simp only [projectChecked, hp] at hs
      cases hs
    | ok p =>
      have hc : acceptProjection q p = .ok out := by
        simpa only [projectChecked, hp] using hs
      obtain ⟨he, r, t, hr, hb, ht, hd⟩ := accepted_projection q p out hc
      obtain ⟨h1, h2⟩ := authentication_verdicts q e ha
      subst out
      exact ⟨e, r, t, by simp [ha], h1, h2, hr, hb, ht, hd⟩

#print axioms EthereumConsensus.SSZ.ProposerProjection.accepted_projection
#print axioms EthereumConsensus.SSZ.ProposerProjection.authentication_verdicts
#print axioms EthereumConsensus.SSZ.ProposerProjection.successful_projection
#print axioms EthereumConsensus.SSZ.ProposerProjection.mark_overflow
#print axioms EthereumConsensus.SSZ.ProposerProjection.mark_checked
#print axioms EthereumConsensus.SSZ.ProposerProjection.authentication_error
#print axioms EthereumConsensus.SSZ.ProposerProjection.authentication_success
end EthereumConsensus.SSZ.ProposerProjection
