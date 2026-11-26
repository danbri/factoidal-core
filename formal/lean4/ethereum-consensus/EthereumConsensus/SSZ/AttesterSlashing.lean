import EthereumConsensus.SSZ.AttestationData
import EthereumConsensus.SSZ.ByteProofTheorems

/-! Preparatory attester-slashing evidence, not a state transition.
    Specification pin: ethereum/consensus-specs@d2021d2719235f0df4726a1d330502cb15aa8ea3,
    phase0/beacon-chain.md, is_slashable_attestation_data, is_valid_indexed_attestation,
    process_attester_slashing. Both aggregate signatures, authenticated validator
    registry and slashable-validator checks remain required before any mutation. -/
namespace EthereumConsensus.SSZ

def sameAttestationFields (a b : AttestationData) : Bool :=
  decide (a.slot = b.slot) && decide (a.committeeIndex = b.committeeIndex) &&
  (a.beaconBlockRoot.bytes == b.beaconBlockRoot.bytes) &&
  decide (a.source.epoch = b.source.epoch) &&
  (a.source.root.bytes == b.source.root.bytes) &&
  decide (a.target.epoch = b.target.epoch) &&
  (a.target.root.bytes == b.target.root.bytes)

def sameAttestationModel (a b : AttestationData) : Prop :=
  a.slot = b.slot ∧ a.committeeIndex = b.committeeIndex ∧
  a.beaconBlockRoot.bytes = b.beaconBlockRoot.bytes ∧
  a.source.epoch = b.source.epoch ∧ a.source.root.bytes = b.source.root.bytes ∧
  a.target.epoch = b.target.epoch ∧ a.target.root.bytes = b.target.root.bytes

def slashableDataModel (a b : AttestationData) : Prop :=
  (¬ sameAttestationModel a b ∧ a.target.epoch = b.target.epoch) ∨
  (a.source.epoch < b.source.epoch ∧ b.target.epoch < a.target.epoch)

/-- Direction matters for surround votes. Compare fields, not their hashes. -/
def isSlashableData (a b : AttestationData) : Bool :=
  (!sameAttestationFields a b && decide (a.target.epoch = b.target.epoch)) ||
  (decide (a.source.epoch < b.source.epoch) && decide (b.target.epoch < a.target.epoch))

inductive SlashingPreparationError where
  | resourceLimit
  | badIndices
  | notConflicting
  | noCommonIndices
  | signing (error : DomainError)

-- This is an implementation boundary, not MAX_VALIDATORS_PER_COMMITTEE.
def slashingIndexLimit : Nat := 32

def increasingAfter (previous : UInt64) : List UInt64 → Bool
  | [] => true
  | x :: xs => decide (previous < x) && increasingAfter x xs

def checkSlashingIndices (indices : List UInt64) : Except SlashingPreparationError Unit :=
  if indices.length > slashingIndexLimit then .error .resourceLimit
  else
    match indices with
    | [] => .error .badIndices
    | x :: xs => if increasingAfter x xs then .ok () else .error .badIndices

def commonSlashingIndices (left right : List UInt64) : List UInt64 :=
  left.filter (fun index => decide (index ∈ right))

structure PreparedAttesterSlashing where
  commonIndices : List UInt64
  firstSigningRoot : Chunk
  secondSigningRoot : Chunk

/-- Prepare the exact two signing messages and common candidate indices.
    No caller may use this result as evidence of signature validity. -/
def prepareAttesterSlashing (context : ForkContext) (a b : AttestationData)
    (left right : List UInt64) : Except SlashingPreparationError PreparedAttesterSlashing :=
  match checkSlashingIndices left with
  | .error e => .error e
  | .ok _ =>
    match checkSlashingIndices right with
    | .error e => .error e
    | .ok _ =>
      if isSlashableData a b then
        let common := commonSlashingIndices left right
        if common.isEmpty then .error .noCommonIndices
        else
          match attesterSigningRoot context a with
          | .error e => .error (.signing e)
          | .ok first =>
            match attesterSigningRoot context b with
            | .error e => .error (.signing e)
            | .ok second => .ok ⟨common, first.signingRoot, second.signingRoot⟩
      else .error .notConflicting

/-- Kind: refinement. Says: equality covers every field.
    Does not say: those fields describe an authentic attestation. -/
theorem sameAttestationFields_iff (a b : AttestationData) :
    sameAttestationFields a b = true ↔ sameAttestationModel a b := by
  simp [sameAttestationFields, sameAttestationModel, byteArray_beq_iff_eq, and_assoc]

/-- Kind: refinement. Says: the executable comparison is equivalent to
    the declarative double-vote or directional surround relation.
    Does not say: both attestations have valid signatures. -/
theorem isSlashableData_iff (a b : AttestationData) :
    isSlashableData a b = true ↔ slashableDataModel a b := by
  simp [isSlashableData, slashableDataModel, ← sameAttestationFields_iff]

/-- Kind: refusal. Says: data cannot conflict with itself.
    Does not say: repeating a vote is valid in every protocol context. -/
theorem isSlashableData_self (a : AttestationData) :
    isSlashableData a a = false := by
  simp [isSlashableData, sameAttestationFields, byteArray_beq_iff_eq]

/-- Kind: membership refinement. Says: common indices are exactly those
    in both lists. Does not say: any common validator is slashable. -/
theorem mem_commonSlashingIndices (index : UInt64) (left right : List UInt64) :
    index ∈ commonSlashingIndices left right ↔ index ∈ left ∧ index ∈ right := by
  simp [commonSlashingIndices]

/-- Kind: resource admission. Says: oversize lists refuse before other checks.
    Does not say: this local bound is a consensus limit. -/
theorem checkSlashingIndices_over_limit (indices : List UInt64)
    (h : indices.length > slashingIndexLimit) :
    checkSlashingIndices indices = .error .resourceLimit := by
  simp only [checkSlashingIndices, if_pos h]

/-- Kind: linkage. Says: the actual preparation propagates left admission failure.
    Does not say: right admission has already been performed. -/
theorem prepareAttesterSlashing_bad_left (context : ForkContext) (a b : AttestationData)
    (left right : List UInt64) (e : SlashingPreparationError)
    (h : checkSlashingIndices left = .error e) :
    prepareAttesterSlashing context a b left right = .error e := by
  simp only [prepareAttesterSlashing, h]

/-- Kind: linkage. Says: after left admission, right failure also propagates.
    Does not say: either aggregate signature was checked. -/
theorem prepareAttesterSlashing_bad_right (context : ForkContext) (a b : AttestationData)
    (left right : List UInt64) (e : SlashingPreparationError)
    (hl : checkSlashingIndices left = .ok ())
    (hr : checkSlashingIndices right = .error e) :
    prepareAttesterSlashing context a b left right = .error e := by
  simp only [prepareAttesterSlashing, hl, hr]

/-- Kind: linkage. Says: admitted conflicting data with a nonempty common
    set and computed signing roots yields exactly that evidence.
    Does not say: the context is authentic or a slash is authorised. -/
theorem prepareAttesterSlashing_of_ok (context : ForkContext) (a b : AttestationData)
    (left right : List UInt64) (first second : HeaderSigningResult)
    (hl : checkSlashingIndices left = .ok ())
    (hr : checkSlashingIndices right = .ok ())
    (hs : isSlashableData a b = true)
    (hc : (commonSlashingIndices left right).isEmpty = false)
    (h1 : attesterSigningRoot context a = .ok first)
    (h2 : attesterSigningRoot context b = .ok second) :
    prepareAttesterSlashing context a b left right =
      .ok ⟨commonSlashingIndices left right, first.signingRoot, second.signingRoot⟩ := by
  simp [prepareAttesterSlashing, hl, hr, hs, hc, h1, h2]

#guard increasingAfter 0 [1, 2, 18446744073709551615]
#guard !(increasingAfter 1 [1])
#guard !(increasingAfter 2 [1])
#guard commonSlashingIndices [1, 2, 3] [2, 4] == [2]
#guard (checkSlashingIndices []).toOption.isNone
#guard (checkSlashingIndices [0, 1]).toOption.isSome

#print axioms EthereumConsensus.SSZ.sameAttestationFields_iff
#print axioms EthereumConsensus.SSZ.isSlashableData_iff
#print axioms EthereumConsensus.SSZ.isSlashableData_self
#print axioms EthereumConsensus.SSZ.mem_commonSlashingIndices
#print axioms EthereumConsensus.SSZ.checkSlashingIndices_over_limit
#print axioms EthereumConsensus.SSZ.prepareAttesterSlashing_bad_left
#print axioms EthereumConsensus.SSZ.prepareAttesterSlashing_bad_right
#print axioms EthereumConsensus.SSZ.prepareAttesterSlashing_of_ok

end EthereumConsensus.SSZ
