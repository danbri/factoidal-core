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
private def projectChecked (q : ProjectionRequest) : Except ProjectionError PartialCommitment := do
  let v ← markValidator (mainnetRegistryEpoch q.slot) q.validator
  let leaf ← (validatorRoot v).mapError ProjectionError.registry
  let len ← (uint64Root (UInt64.ofNat q.length)).mapError (fun _ => ProjectionError.registry .basicRoot)
  let registry ← (calculateByteBranch 41 (validatorRegistryGindex q.first.proposerIndex.toNat)
    leaf.bytes (q.member ++ [len.bytes])).mapError ProjectionError.proof
  let layout := mainnetRegistryLayout q.slot
  let state ← (calculateByteBranch (registryStateDepth layout) (registryStateGindex layout)
    registry.bytes q.registrySiblings).mapError ProjectionError.proof
  return ⟨v, registry, state⟩

/-- The only public commitment projection entry point authenticates the raw input first. -/
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

#print axioms EthereumConsensus.SSZ.ProposerProjection.mark_overflow
#print axioms EthereumConsensus.SSZ.ProposerProjection.mark_checked
#print axioms EthereumConsensus.SSZ.ProposerProjection.authentication_error
#print axioms EthereumConsensus.SSZ.ProposerProjection.authentication_success
end EthereumConsensus.SSZ.ProposerProjection
