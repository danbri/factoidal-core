import EVMCleanroom.BlobCall
import EVMCleanroom.BlobHashProofs

/-!
# Validated blob hashes at the execution boundary

The statements follow the actual admission and preparation functions. They
do not authenticate the decoded envelope, account witnesses or KZG sidecars.
-/
namespace EVMCleanroom.BlobCall

/-- Kind: admission and executable correspondence.
    Says: successful Cancun preparation has passed the nonempty, at-most-six
    and versioned-hash checks, and returns exactly the shared preparation
    result. In particular, conversion happens only after those input bounds.
    Does not say: that the signed envelope or blob commitments are authentic. -/
theorem prepareWithFees_checked (p : Input) (fees : Nat × Nat) (ready : Prepared)
    (h : prepareWithFees p fees = .ok ready) :
    ready = prepareRequest p fees ∧ p.hashes.isEmpty = false ∧
      p.hashes.size ≤ 6 ∧ p.hashes.all validHash = true := by
  unfold prepareWithFees at h
  dsimp only at h
  by_cases hKind : (p.request.tx.kind != 3) = true
  · rw [if_pos hKind] at h
    cases h
  rw [if_neg hKind] at h
  by_cases hCreate : p.request.tx.create = true
  · rw [if_pos hCreate] at h
    cases h
  rw [if_neg hCreate] at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hEmpty
  split at h
  · cases h
  rename_i hSize
  split at h
  · cases h
  rename_i hValid
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  unfold checkFunds at h
  split at h
  · cases h
  cases h
  exact ⟨rfl, by cases hBool : p.hashes.isEmpty <;> simp_all,
    Nat.le_of_not_gt hSize, by cases hBool : p.hashes.all validHash <;> simp_all⟩

/-- Kind: admission and resource boundary.
    Says: every successful checked-header entry carries exactly the ordered
    normalised input hashes, with at most six words and a nonempty, valid
    versioned-hash source list.
    Does not say: that these bytes belong to a valid KZG sidecar or chain. -/
theorem prepare_blobHashes_checked (a : Keccak.Acceptance) (p : Input) (ready : Prepared)
    (h : prepare a p = .ok ready) :
    ready.txBlobHashes = p.hashes.map hashWord ∧ ready.txBlobHashes.size ≤ 6 ∧
      p.hashes.isEmpty = false ∧ p.hashes.all validHash = true := by
  unfold prepare at h
  split at h
  · cases h
  next fees _ =>
    obtain ⟨rfl, hEmpty, hSize, hValid⟩ := prepareWithFees_checked p fees ready h
    exact ⟨rfl, by simpa [prepareRequest] using hSize, hEmpty, hValid⟩

/-- Kind: executable projection.
    Says: the exact prepared transaction context reaches the real top-level
    frame after ordinary execution-fee escrow and nonce advancement.
    Does not say: that value transfer or bytecode execution has succeeded. -/
theorem prepared_entry_blobHashes (p : Input) (fees : Nat × Nat)
    (budget : CallTransaction.Budget) :
    let ready := prepareRequest p fees
    let world := { CallTransaction.witnessWorld ready.request with
      txBlobHashes := ready.txBlobHashes }
    (CallTransaction.entryFrame ready.request
      (CallTransaction.debitSender world ready.request.tx.sender budget) budget).txBlobHashes =
      p.hashes.map hashWord := rfl

/-- Kind: executable correspondence.
    Says: after the actual successful value transfer, the actual admitted
    frame still has exactly the prepared transaction's ordered hash words.
    The premise is the real transfer result, not a context-equality assumption.
    Does not say: that execution of the entered bytecode or a sidecar succeeds. -/
theorem admitted_entry_blobHashes (ready : Prepared) (budget : CallTransaction.Budget)
    (entered : World.TxWorld)
    (hPay : World.pay
      (CallTransaction.debitSender
        { CallTransaction.witnessWorld ready.request with txBlobHashes := ready.txBlobHashes }
        ready.request.tx.sender budget)
      ready.request.tx.sender ready.request.tx.to ready.request.tx.value = .ok entered) :
    (CallTransaction.entryFrame ready.request entered budget).txBlobHashes =
      ready.txBlobHashes := by
  rw [CallTransaction.entryFrame_blobHashes, World.pay_txBlobHashes hPay]
  rfl

/-- Kind: validated-input-to-frame correspondence.
    Says: checked header and blob admission followed by the actual successful
    value transfer gives the executing frame exactly the original ordered hash
    words, with no more than six entries. Both premises are executable results.
    Does not say: that the external signature, witnesses or KZG proofs are valid. -/
theorem validated_entry_blobHashes (a : Keccak.Acceptance) (p : Input)
    (ready : Prepared) (budget : CallTransaction.Budget) (entered : World.TxWorld)
    (hReady : prepare a p = .ok ready)
    (hPay : World.pay
      (CallTransaction.debitSender
        { CallTransaction.witnessWorld ready.request with txBlobHashes := ready.txBlobHashes }
        ready.request.tx.sender budget)
      ready.request.tx.sender ready.request.tx.to ready.request.tx.value = .ok entered) :
    (CallTransaction.entryFrame ready.request entered budget).txBlobHashes = p.hashes.map hashWord ∧
      (CallTransaction.entryFrame ready.request entered budget).txBlobHashes.size ≤ 6 := by
  obtain ⟨hHashes, hSize, _, _⟩ := prepare_blobHashes_checked a p ready hReady
  rw [admitted_entry_blobHashes ready budget entered hPay]
  exact ⟨hHashes, hSize⟩

#print axioms prepareWithFees_checked
#print axioms prepare_blobHashes_checked
#print axioms prepared_entry_blobHashes
#print axioms admitted_entry_blobHashes
#print axioms validated_entry_blobHashes

end EVMCleanroom.BlobCall
