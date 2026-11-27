import EVMCleanroom.TransactionList
import EVMCleanroom.BlobCallProofs

/-!
# Ordered transaction-list execution boundaries

These statements concern the executable transaction and list functions. They
do not authenticate envelopes, initial witnesses, receipts or block membership.
-/

namespace EVMCleanroom.TransactionList

open World

/-- Kind: executable transaction boundary.
    Says: constructing the next transaction world snapshots its current
    account storage as original storage and clears the refund, log journal,
    blob hashes and effective execution price from any earlier transaction.
    Does not say: that the supplied witnesses are authenticated or complete. -/
theorem witnessWorld_fresh (p : CallTransaction.Request) :
    (CallTransaction.witnessWorld p).original =
      (fun address key => ((CallTransaction.witnessWorld p).accounts address).storage key) ∧
    (CallTransaction.witnessWorld p).refund = 0 ∧
    (CallTransaction.witnessWorld p).logsRev = [] ∧
    (CallTransaction.witnessWorld p).txBlobHashes = #[] ∧
    (CallTransaction.witnessWorld p).effectiveGasPrice = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Kind: executable transaction boundary.
    Says: initial warmth is determined only by the new transaction's sender,
    recipient, beneficiary, precompile range and access list; slot warmth is
    precisely the new access list, with no earlier world involved.
    Does not say: that the externally supplied access list is valid. -/
theorem witnessWorld_fresh_warmth (p : CallTransaction.Request) (address key : Nat) :
    (CallTransaction.witnessWorld p).warmAddresses address =
      (address == p.tx.sender || address == p.tx.to || address == p.block.coinbase ||
        decide (1 ≤ address ∧ address ≤ p.fork.precompileLimit) ||
        p.tx.accessList.any (fun entry => entry.address == address)) ∧
    (CallTransaction.witnessWorld p).warmSlots address key =
      p.tx.accessList.any (fun entry =>
        entry.address == address && entry.storageKeys.contains key) := ⟨rfl, rfl⟩

/-- Kind: executable settlement accounting.
    Says: actual successful fee settlement adds precisely this receipt's gas
    charge to the supplied prefix counter.
    Does not say: that the prefix represents an authenticated block. -/
theorem finish_cumulativeGasUsed (tx : CallTransaction.Envelope)
    (block : CallTransaction.BlockContext) (budget : CallTransaction.Budget)
    (world : TxWorld) (frame : CallTransaction.FrameStatus) (s : State)
    (success : Bool) (result : CallTransaction.Result)
    (h : CallTransaction.finish tx block budget world frame s success = .executed result) :
    result.cumulativeGasUsed = block.gasUsedBefore + result.charge.used := by
  unfold CallTransaction.finish at h
  split at h
  · cases h
  · dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        rfl

/-- Kind: executable settlement composition.
    Says: stopped, returned, reverted and exceptional frames all retain the
    exact prefix-plus-receipt gas accounting of the real settlement function.
    Does not say: that an indeterminate frame produces a receipt. -/
theorem settleFrame_cumulativeGasUsed (tx : CallTransaction.Envelope)
    (block : CallTransaction.BlockContext) (budget : CallTransaction.Budget)
    (escrow : TxWorld) (initial : State) (raw : CallOpcode.RawOutcome)
    (result : CallTransaction.Result)
    (h : CallTransaction.settleFrame tx block budget escrow initial raw = .executed result) :
    result.cumulativeGasUsed = block.gasUsedBefore + result.charge.used := by
  cases raw with
  | stopped world state =>
    obtain ⟨inner, hInner, rfl⟩ := CallTransaction.destroyAfter_executed h
    exact finish_cumulativeGasUsed _ _ _ _ _ _ _ inner hInner
  | returned world state =>
    obtain ⟨inner, hInner, rfl⟩ := CallTransaction.destroyAfter_executed h
    exact finish_cumulativeGasUsed _ _ _ _ _ _ _ inner hInner
  | reverted state => exact finish_cumulativeGasUsed _ _ _ _ _ _ _ _ h
  | exceptional reason => exact finish_cumulativeGasUsed _ _ _ _ _ _ _ _ h
  | indeterminate reason => cases h

/-- Kind: executable transaction composition.
    Says: the real admitted transaction path preserves exact cumulative gas
    accounting through escrow, value transfer, execution and settlement.
    Does not say: that this lower-level function admits the envelope itself. -/
theorem runAdmitted_cumulativeGasUsed (p : CallTransaction.Request) (world : TxWorld)
    (budget : CallTransaction.Budget) (result : CallTransaction.Result)
    (h : CallTransaction.runAdmitted p world budget = .executed result) :
    result.cumulativeGasUsed = p.block.gasUsedBefore + result.charge.used := by
  unfold CallTransaction.runAdmitted at h
  dsimp only at h
  split at h
  · unfold CallTransaction.runCreation at h
    split at h
    · exact settleFrame_cumulativeGasUsed _ _ _ _ _ _ _ h
    · split at h
      · cases h
      · exact settleFrame_cumulativeGasUsed _ _ _ _ _ _ _ h
  · split at h
    · cases h
    · exact settleFrame_cumulativeGasUsed _ _ _ _ _ _ _ h

/-- Kind: public execution accounting.
    Says: every actual result of the shared ordinary/blob execution entry
    adds exactly its own settled charge to the supplied prefix gas counter.
    Does not say: that the prefix or explicit blob context is authenticated. -/
theorem runWithBlobHashes_cumulativeGasUsed (p : CallTransaction.Request)
    (hashes : Array Word) (result : CallTransaction.Result)
    (h : CallTransaction.runWithBlobHashes p hashes = .executed result) :
    result.cumulativeGasUsed = p.block.gasUsedBefore + result.charge.used := by
  unfold CallTransaction.runWithBlobHashes at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  exact runAdmitted_cumulativeGasUsed _ _ _ _ h

/-- Kind: executable witness projection.
    Says: refresh copies the settled account's existence, balance, nonce and
    code, while retaining the supplied address and ordered storage-key list.
    Does not say: that unlisted storage has become witnessed. -/
theorem refreshWitness_projection (world : TxWorld) (w : CallTransaction.WitnessAccount) :
    (refreshWitness world w).address = w.address ∧
    (refreshWitness world w).present = CallValue.accountAlive (world.accounts w.address) ∧
    (refreshWitness world w).balance = (world.accounts w.address).balance ∧
    (refreshWitness world w).nonce = (world.accounts w.address).nonce ∧
    (refreshWitness world w).code = (world.accounts w.address).code ∧
    (refreshWitness world w).storage.map (·.key) = w.storage.map (·.key) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  simp [refreshWitness, List.map_map, Function.comp_def]

/-- Kind: executable witness projection.
    Says: every listed storage key refreshes to the settled world's exact
    value, including zero; lookup remains independent of old slot values.
    Does not say: anything about the value of an unlisted key. -/
theorem refreshWitness_listed_storage (world : TxWorld)
    (w : CallTransaction.WitnessAccount) (key : Nat)
    (hKey : w.storage.any (fun slot => slot.key == key) = true) :
    (refreshWitness world w).account.storage key = (world.accounts w.address).storage key := by
  cases hFind : w.storage.find? (fun slot => slot.key == key) with
  | none =>
    have hSome := List.isSome_find? (xs := w.storage) (f := fun slot => slot.key == key)
    simp [hFind, hKey] at hSome
  | some slot =>
    have hEqual : slot.key = key := by simpa using List.find?_some hFind
    simp [refreshWitness, CallTransaction.WitnessAccount.account, List.find?_map,
      Function.comp_def, hFind, hEqual]

/-- Kind: executable witness inventory preservation.
    Says: refreshing a settled world neither adds, removes nor reorders
    witnessed addresses.
    Does not say: that the initial witness inventory covers the whole state. -/
theorem refreshWitnesses_inventory (world : TxWorld)
    (ws : List CallTransaction.WitnessAccount) :
    (refreshWitnesses world ws).length = ws.length ∧
    (refreshWitnesses world ws).map (·.address) = ws.map (·.address) := by
  simp [refreshWitnesses, refreshWitness, List.map_map, Function.comp_def]

/-- Kind: executable lookup correspondence.
    Says: account lookup in refreshed witnesses selects the same original
    inventory entry and then refreshes its values.
    Does not say: that duplicate input addresses pass admission. -/
theorem refreshWitnesses_find (world : TxWorld)
    (ws : List CallTransaction.WitnessAccount) (address : Nat) :
    (refreshWitnesses world ws).find? (fun w => w.address == address) =
      (ws.find? (fun w => w.address == address)).map (refreshWitness world) := by
  simp [refreshWitnesses, List.find?_map, Function.comp_def, refreshWitness]

/-- Kind: executable witness coverage preservation.
    Says: the next real request's account and slot coverage is exactly the
    original inventory's coverage, despite refreshing all covered values.
    Does not say: that an unwitnessed account or slot can execute. -/
theorem refreshed_request_coverage (a : Keccak.Acceptance) (p : Input) (fees : Nat × Nat)
    (world : TxWorld) (ws : List CallTransaction.WitnessAccount) (gasUsed : Nat) (entry : Entry) :
    (CallTransaction.witnessWorld
      (requestFor a p fees (refreshWitnesses world ws) gasUsed entry)).witnessed =
    (CallTransaction.witnessWorld (requestFor a p fees ws gasUsed entry)).witnessed := by
  simp [CallTransaction.witnessWorld, requestFor, refreshWitnesses, refreshWitness,
    List.find?_map, Function.comp_def]
  funext address key
  cases ws.find? (fun item => item.address == address) <;>
    simp [refreshWitness, Function.comp_def]

/-- Kind: executable transaction-original storage.
    Says: after refresh from a previous settled world, the next request's
    original value for a covered slot is that previous post-state value.
    Does not say: that the prior transaction succeeded rather than reverted. -/
theorem refreshed_request_original (a : Keccak.Acceptance) (p : Input) (fees : Nat × Nat)
    (world : TxWorld) (ws : List CallTransaction.WitnessAccount) (gasUsed : Nat) (entry : Entry)
    (w : CallTransaction.WitnessAccount) (key : Nat)
    (hAccount : ws.find? (fun item => item.address == w.address) = some w)
    (hKey : w.storage.any (fun slot => slot.key == key) = true) :
    (CallTransaction.witnessWorld
      (requestFor a p fees (refreshWitnesses world ws) gasUsed entry)).original w.address key =
      (world.accounts w.address).storage key := by
  change ((((refreshWitnesses world ws).find? (fun item => item.address == w.address)).map
    CallTransaction.WitnessAccount.account).getD ({} : Account)).storage key = _
  rw [refreshWitnesses_find, hAccount]
  exact refreshWitness_listed_storage world w key hKey

/-- Kind: bounded-prefix resource check.
    Says: the executable bounded-prefix counter accepts exactly lists whose
    length is at most its allowance.
    Does not say: that list elements themselves satisfy any resource limit. -/
theorem countFits_iff {α : Type} (limit : Nat) (xs : List α) :
    countFits limit xs = true ↔ xs.length ≤ limit := by
  induction limit generalizing xs with
  | zero => cases xs <;> simp [countFits]
  | succ limit ih =>
    cases xs with
    | nil => simp [countFits]
    | cons x rest => simpa [countFits] using ih rest

/-- Kind: aggregate resource admission.
    Says: actual list preflight acceptance enforces the transaction count,
    total reserved instruction fuel and aggregate input-byte bounds.
    Does not say: that executing within those limits establishes consensus. -/
theorem preflight_bounded (p : Input) (h : preflight p = .ok ()) :
    p.transactions.length ≤ maxTransactions ∧
    reservedFuel p.transactions ≤ maxReservedFuel ∧ inputBytes p ≤ maxInputBytes := by
  unfold preflight at h
  split at h
  · cases h
  rename_i hCount
  split at h
  · cases h
  split at h
  · cases h
  split at h
  · cases h
  rename_i hBudget
  have hFits : countFits maxTransactions p.transactions = true := by
    cases hSize : countFits maxTransactions p.transactions <;> simp_all
  have hBounds : ¬(reservedFuel p.transactions > maxReservedFuel ∨ inputBytes p > maxInputBytes) := by
    simpa only [Bool.or_eq_true, decide_eq_true_eq] using hBudget
  exact ⟨(countFits_iff _ _).mp hFits, by omega, by omega⟩

/-- Kind: defined resource refusal.
    Says: more than 256 entries gives the resource refusal before any header
    hashing, witness refresh or entry execution.
    Does not say: that 256 entries are necessarily executable. -/
theorem preflight_too_many (p : Input) (h : maxTransactions < p.transactions.length) :
    preflight p = .error (.indeterminate (.frame .resourceLimit)) := by
  have hFits : countFits maxTransactions p.transactions = false := by
    cases hCount : countFits maxTransactions p.transactions
    · rfl
    · have := (countFits_iff _ _).mp hCount
      omega
  simp [preflight, hFits]

/-- Kind: defined aggregate resource refusal.
    Says: exceeding the total reserved-fuel or input-byte allowance produces
    the resource refusal, including when an earlier resource check also fails.
    Does not say: that per-transaction resource admission has succeeded. -/
theorem preflight_aggregate_limit (p : Input)
    (h : maxReservedFuel < reservedFuel p.transactions ∨ maxInputBytes < inputBytes p) :
    preflight p = .error (.indeterminate (.frame .resourceLimit)) := by
  unfold preflight
  split
  · rfl
  split
  · rfl
  split
  · rfl
  have hLimit : (decide (reservedFuel p.transactions > maxReservedFuel) ||
      decide (inputBytes p > maxInputBytes)) = true := by simpa using h
  simp only [hLimit, if_true]

/-- Kind: defined retained-output refusal.
    Says: the actual advance function refuses before extending the receipt
    list whenever accumulated output, log data, topics and addresses exceed
    the observation budget.
    Does not say: that the prior EVM frame allocated no temporary memory. -/
theorem advance_observation_limit (cursor : Cursor) (entry : Entry) (step : Transition)
    (h : maxObservationBytes < cursor.observationBytes + observationBytes step) :
    advance cursor entry step = .error (.indeterminate (.frame .resourceLimit)) := by
  simp [advance, h]

/-- Kind: executable prefix update.
    Says: within the retained-observation budget, advance refreshes exactly
    the settled state, adds actual gas/blob charges, prepends this receipt
    and increments the index once.
    Does not say: that the supplied transition was produced by runEntry. -/
theorem advance_exact (cursor : Cursor) (entry : Entry) (step : Transition)
    (h : cursor.observationBytes + observationBytes step ≤ maxObservationBytes) :
    advance cursor entry step = .ok {
      witnesses := refreshWitnesses step.result.world cursor.witnesses
      gasUsed := cursor.gasUsed + step.result.charge.used
      blobGasUsed := cursor.blobGasUsed + step.blobGasUsed
      receiptsRev := receiptOf entry step :: cursor.receiptsRev
      observationBytes := cursor.observationBytes + observationBytes step
      index := cursor.index + 1 } := by
  simp [advance, Nat.not_lt.mpr h]

/-- Kind: executable prefix projection.
    Says: successful advance has the exact refreshed state, counters, receipt
    order and bounded observation count shown by the implementation.
    Does not say: that arbitrary caller-created transitions are valid. -/
theorem advance_checked (cursor next : Cursor) (entry : Entry) (step : Transition)
    (h : advance cursor entry step = .ok next) :
    next.witnesses = refreshWitnesses step.result.world cursor.witnesses ∧
    next.gasUsed = cursor.gasUsed + step.result.charge.used ∧
    next.blobGasUsed = cursor.blobGasUsed + step.blobGasUsed ∧
    next.receiptsRev = receiptOf entry step :: cursor.receiptsRev ∧
    next.observationBytes = cursor.observationBytes + observationBytes step ∧
    next.observationBytes ≤ maxObservationBytes ∧ next.index = cursor.index + 1 := by
  unfold advance at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hBound
    cases h
    exact ⟨rfl, rfl, rfl, rfl, rfl, Nat.le_of_not_gt hBound, rfl⟩

/-- Kind: actual entry-to-prefix accounting.
    Says: either ordinary execution or the admitted blob path returns exactly
    prefix gas plus its real settled receipt charge, including status zero.
    Does not say: that supplied headers or decoded envelopes are authentic. -/
theorem runEntry_cumulativeGasUsed (a : Keccak.Acceptance) (p : Input) (fees : Nat × Nat)
    (ws : List CallTransaction.WitnessAccount) (gasUsed blobGasUsed : Nat)
    (entry : Entry) (step : Transition)
    (h : runEntry a p fees ws gasUsed blobGasUsed entry = .ok step) :
    step.result.cumulativeGasUsed = gasUsed + step.result.charge.used := by
  unfold runEntry at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · split at h
    · cases h
    · next blob _ =>
      split at h
      · cases h
      · next ready hReady =>
        obtain ⟨rfl, _, _, _⟩ := BlobCall.prepareWithFees_checked _ _ _ hReady
        cases hExec : CallTransaction.runWithBlobHashes
            (BlobCall.prepareRequest {
              request := requestFor a p fees ws gasUsed entry
              parent := p.parent, child := p.child, hashes := blob.hashes
              blobCap := blob.maxFeePerBlobGas, priorBlobGas := blobGasUsed } fees).request
            (BlobCall.prepareRequest {
              request := requestFor a p fees ws gasUsed entry
              parent := p.parent, child := p.child, hashes := blob.hashes
              blobCap := blob.maxFeePerBlobGas, priorBlobGas := blobGasUsed } fees).txBlobHashes with
        | rejected reason => simp [BlobCall.execute, hExec, fromTransaction] at h
        | indeterminate reason => simp [BlobCall.execute, hExec, fromTransaction] at h
        | executed result =>
          by_cases hTotal : result.cumulativeGasUsed > HeaderRLP.readNat p.child 10
          · simp only [BlobCall.execute, hExec, if_pos hTotal] at h
            cases h
          · simp only [BlobCall.execute, hExec, if_neg hTotal, fromTransaction] at h
            cases h
            have hc := runWithBlobHashes_cumulativeGasUsed _ _ _ hExec
            simpa [BlobCall.prepareRequest, BlobCall.blockContext, requestFor] using hc
  · split at h
    · cases h
    · cases hExec : CallTransaction.run (requestFor a p fees ws gasUsed entry) with
      | rejected reason => simp [hExec, fromTransaction] at h
      | indeterminate reason => simp [hExec, fromTransaction] at h
      | executed result =>
        simp only [hExec, fromTransaction] at h
        cases h
        exact runWithBlobHashes_cumulativeGasUsed _ #[] _ hExec

/-- A proof-only description of cumulative receipt gas in the loop's reverse
    accumulator. Each receipt includes all earlier receipts and its own charge. -/
def cumulativeReceipts : List Receipt → Prop
  | [] => True
  | receipt :: earlier =>
      receipt.cumulativeGasUsed =
        (earlier.map (fun r => r.charge.used)).sum + receipt.charge.used ∧
      cumulativeReceipts earlier

/-- A proof-only ordered trace. Every receipt is tied to an actual runEntry
    result and the actual advance state passed to the following entry. The
    terminal inventory is exactly the last cursor's witnesses. -/
def receiptTrace (a : Keccak.Acceptance) (p : Input) (fees : Nat × Nat) :
    Cursor → List Entry → List Receipt → List CallTransaction.WitnessAccount → Prop
  | cursor, [], receipts, finalWitnesses => receipts = [] ∧ finalWitnesses = cursor.witnesses
  | cursor, entry :: rest, receipts, finalWitnesses =>
      ∃ step next trailing,
        runEntry a p fees cursor.witnesses cursor.gasUsed cursor.blobGasUsed entry = .ok step ∧
        advance cursor entry step = .ok next ∧
        receipts = receiptOf entry step :: trailing ∧
        receiptTrace a p fees next rest trailing finalWitnesses

/-- Kind: ordered executable receipt trace.
    Says: a completed loop appends the exact receipts of successive real
    entry results in execution order, preserving all existing receipt data.
    Each successor uses the actual advance state of its predecessor, and
    the trace ends with exactly the completed loop's final witnesses.
    Does not say: that the trace's initial witnesses or envelopes are authentic. -/
theorem loop_receipt_trace (a : Keccak.Acceptance) (p : Input) (fees : Nat × Nat)
    (cursor final : Cursor) (entries : List Entry)
    (h : loop a p fees cursor entries = .ok final) :
    ∃ appended, final.receiptsRev.reverse = cursor.receiptsRev.reverse ++ appended ∧
      receiptTrace a p fees cursor entries appended final.witnesses := by
  induction entries generalizing cursor with
  | nil =>
    simp only [loop] at h
    cases h
    exact ⟨[], by simp, rfl, rfl⟩
  | cons entry rest ih =>
    simp only [loop] at h
    split at h
    · cases h
    · next step hStep =>
      split at h
      · cases h
      · next next hNext =>
        obtain ⟨appended, hAppend, hTrace⟩ := ih next h
        have hReceipts := (advance_checked cursor next entry step hNext).2.2.2.1
        refine ⟨receiptOf entry step :: appended, ?_, step, next, appended,
          hStep, hNext, rfl, hTrace⟩
        simpa [hReceipts, List.reverse_cons, List.append_assoc] using hAppend

/-- Kind: structural execution correspondence.
    Says: a completed actual loop adds one receipt and one index per input,
    preserves input kind order and the existing prefix of receipt kinds, and retains
    the same address inventory.
    Does not say: that an entry can finish when its underlying runner refuses. -/
theorem loop_order (a : Keccak.Acceptance) (p : Input) (fees : Nat × Nat)
    (cursor final : Cursor) (entries : List Entry)
    (h : loop a p fees cursor entries = .ok final) :
    final.receiptsRev.reverse.map (·.kind) =
      cursor.receiptsRev.reverse.map (·.kind) ++ entries.map (fun entry => entry.tx.kind) ∧
    final.receiptsRev.length = cursor.receiptsRev.length + entries.length ∧
    final.index = cursor.index + entries.length ∧
    final.witnesses.map (·.address) = cursor.witnesses.map (·.address) := by
  induction entries generalizing cursor with
  | nil =>
    simp only [loop] at h
    cases h
    simp
  | cons entry rest ih =>
    simp only [loop] at h
    split at h
    · cases h
    · next step _ =>
      split at h
      · cases h
      · next next hNext =>
        obtain ⟨hW, _, _, hR, _, _, hI⟩ := advance_checked cursor next entry step hNext
        obtain ⟨hKinds, hLength, hIndex, hInventory⟩ := ih next h
        refine ⟨?_, ?_, ?_, ?_⟩
        · simpa [hR, receiptOf, List.reverse_cons, List.map_append, List.append_assoc] using hKinds
        · simpa [hR, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hLength
        · simpa [hI, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hIndex
        · rw [hInventory, hW, (refreshWitnesses_inventory _ _).2]

/-- Kind: actual loop accounting invariant.
    Says: starting from balanced prefix counters and correct cumulative
    receipts, every completed loop retains exact receipt gas/blob sums,
    cumulative receipt gas and the retained-observation bound.
    Does not say: that these receipts are serialised or trie-authenticated. -/
theorem loop_accounting (a : Keccak.Acceptance) (p : Input) (fees : Nat × Nat)
    (cursor final : Cursor) (entries : List Entry)
    (hGas : cursor.gasUsed = (cursor.receiptsRev.map (fun r => r.charge.used)).sum)
    (hBlob : cursor.blobGasUsed = (cursor.receiptsRev.map (·.blobGasUsed)).sum)
    (hReceipts : cumulativeReceipts cursor.receiptsRev)
    (hObservation : cursor.observationBytes ≤ maxObservationBytes)
    (h : loop a p fees cursor entries = .ok final) :
    final.gasUsed = (final.receiptsRev.map (fun r => r.charge.used)).sum ∧
    final.blobGasUsed = (final.receiptsRev.map (·.blobGasUsed)).sum ∧
    cumulativeReceipts final.receiptsRev ∧ final.observationBytes ≤ maxObservationBytes := by
  induction entries generalizing cursor with
  | nil =>
    simp only [loop] at h
    cases h
    exact ⟨hGas, hBlob, hReceipts, hObservation⟩
  | cons entry rest ih =>
    simp only [loop] at h
    split at h
    · cases h
    · next step hStep =>
      split at h
      · cases h
      · next next hNext =>
        obtain ⟨_, hG, hB, hR, _, hO, _⟩ := advance_checked cursor next entry step hNext
        have hCumulative := runEntry_cumulativeGasUsed _ _ _ _ _ _ _ _ hStep
        apply ih next
        · simp [hG, hR, receiptOf, hGas, Nat.add_comm]
        · simp [hB, hR, receiptOf, hBlob, Nat.add_comm]
        · rw [hR]
          exact ⟨by simpa [receiptOf, hGas] using hCumulative, hReceipts⟩
        · exact hO
        · exact h

/-- Kind: indexed failure propagation.
    Says: an entry refusal stops the actual loop at the current index with
    the same reason and exposes no successful suffix or partial cursor.
    Does not say: that the failed entry is invalid when its reason is local. -/
theorem loop_entry_refused (a : Keccak.Acceptance) (p : Input) (fees : Nat × Nat)
    (cursor : Cursor) (entry : Entry) (rest : List Entry) (reason : Failure)
    (h : runEntry a p fees cursor.witnesses cursor.gasUsed cursor.blobGasUsed entry = .error reason) :
    loop a p fees cursor (entry :: rest) = .error { index := cursor.index, reason } := by
  simp [loop, h]

/-- Kind: indexed retained-output refusal.
    Says: an observation-budget refusal after a real entry stops the list at
    that entry's index and preserves the refusal instead of accepting a prefix.
    Does not say: that the preceding individual frame was not executed. -/
theorem loop_advance_refused (a : Keccak.Acceptance) (p : Input) (fees : Nat × Nat)
    (cursor : Cursor) (entry : Entry) (rest : List Entry) (step : Transition) (reason : Failure)
    (hStep : runEntry a p fees cursor.witnesses cursor.gasUsed cursor.blobGasUsed entry = .ok step)
    (hAdvance : advance cursor entry step = .error reason) :
    loop a p fees cursor (entry :: rest) = .error { index := cursor.index, reason } := by
  simp [loop, hStep, hAdvance]

/-- Kind: exact declared-total admission.
    Says: final acceptance preserves the actual loop observations and requires
    both execution-gas and blob-gas totals to equal the child header exactly.
    Does not say: that the supplied list matches the header's transaction root. -/
theorem finish_checked (p : Input) (cursor : Cursor) (result : Result)
    (h : finish p cursor = .accepted result) :
    result.receipts = cursor.receiptsRev.reverse ∧ result.finalWitnesses = cursor.witnesses ∧
    result.gasUsed = cursor.gasUsed ∧ result.blobGasUsed = cursor.blobGasUsed ∧
    result.observationBytes = cursor.observationBytes ∧
    result.gasUsed = HeaderRLP.readNat p.child 10 ∧
    result.blobGasUsed = HeaderRLP.readNat p.child 17 := by
  unfold finish at h
  split at h
  · cases h
  rename_i hGas
  split at h
  · cases h
  rename_i hBlob
  cases h
  simp only [bne_iff_ne] at hGas hBlob
  exact ⟨rfl, rfl, rfl, rfl, rfl,
    Classical.byContradiction hGas, Classical.byContradiction hBlob⟩

/-- Kind: public list execution contract.
    Says: every accepted public run has one ordered receipt per input, exact
    receipt gas/blob sums and cumulative gas, unchanged witness address
    inventory, bounded retained observations, and exact header totals.
    Does not say: that signatures, trie roots, withdrawals or chain membership
    were authenticated by this transition. -/
theorem run_accepted (a : Keccak.Acceptance) (p : Input) (result : Result)
    (h : run a p = .accepted result) :
    result.receipts.map (·.kind) = p.transactions.map (fun entry => entry.tx.kind) ∧
    result.receipts.length = p.transactions.length ∧
    result.gasUsed = (result.receipts.map (fun r => r.charge.used)).sum ∧
    result.blobGasUsed = (result.receipts.map (·.blobGasUsed)).sum ∧
    cumulativeReceipts result.receipts.reverse ∧
    result.finalWitnesses.map (·.address) = p.initialWitnesses.map (·.address) ∧
    result.observationBytes ≤ maxObservationBytes ∧
    result.gasUsed = HeaderRLP.readNat p.child 10 ∧
    result.blobGasUsed = HeaderRLP.readNat p.child 17 ∧
    p.transactions.length ≤ maxTransactions ∧
    reservedFuel p.transactions ≤ maxReservedFuel ∧ inputBytes p ≤ maxInputBytes ∧
    ∃ fees, HeaderRLP.checkedFeePair a p.parent p.child = .ok fees ∧
      receiptTrace a p fees (initial p) p.transactions result.receipts result.finalWitnesses := by
  unfold run at h
  split at h
  · next reason _ => cases reason <;> cases h
  · next hPreflight =>
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · next fees hFees =>
        split at h
        · next failure _ =>
            rcases failure with ⟨index, reason⟩
            cases reason <;> cases h
        · next cursor hLoop =>
          obtain ⟨hR, hW, hG, hB, hO, hHG, hHB⟩ := finish_checked _ _ _ h
          obtain ⟨hKinds, hLength, _, hInventory⟩ := loop_order _ _ _ _ _ _ hLoop
          obtain ⟨hGas, hBlob, hCumulative, hObservation⟩ := loop_accounting a p fees
            (initial p) cursor p.transactions rfl rfl trivial (Nat.zero_le _) hLoop
          obtain ⟨appended, hAppend, hTrace⟩ := loop_receipt_trace _ _ _ _ _ _ hLoop
          obtain ⟨hCount, hFuel, hBytes⟩ := preflight_bounded p hPreflight
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hHG, hHB, hCount, hFuel, hBytes, fees, hFees, ?_⟩
          · simpa [hR, initial] using hKinds
          · simpa [hR, initial] using hLength
          · simpa [hR, hG, List.map_reverse] using hGas
          · simpa [hR, hB, List.map_reverse] using hBlob
          · simpa [hR] using hCumulative
          · simpa [hW, initial] using hInventory
          · simpa [hO] using hObservation
          · have hSame : result.receipts = appended := by simpa [hR, initial] using hAppend
            simpa [hSame, hW] using hTrace

/-- Kind: public preflight refusal.
    Says: a failed actual preflight returns its reason before any entry or
    header processing, with no fabricated transaction index.
    Does not say: that local resource refusal establishes block invalidity. -/
theorem run_preflight_refused (a : Keccak.Acceptance) (p : Input) (reason : Failure)
    (h : preflight p = .error reason) : run a p = refusal none reason := by
  simp [run, h]

/-- Kind: list-owned refusal classification.
    Says: the blob adapter's inconsistent block-position refusal becomes a
    definite declaration rejection in the list adapter, whose public run
    derives its prefix gas and blob counters from previous executions.
    Does not say: that the standalone partial-position blob adapter changed. -/
theorem blob_position_refused :
    fromBlobRefusal (.indeterminate "inconsistent-block-position") =
      .rejected "declared-gas-total-exceeded" := rfl

#print axioms witnessWorld_fresh
#print axioms witnessWorld_fresh_warmth
#print axioms finish_cumulativeGasUsed
#print axioms settleFrame_cumulativeGasUsed
#print axioms runAdmitted_cumulativeGasUsed
#print axioms runWithBlobHashes_cumulativeGasUsed
#print axioms refreshWitness_projection
#print axioms refreshWitness_listed_storage
#print axioms refreshWitnesses_inventory
#print axioms refreshWitnesses_find
#print axioms refreshed_request_coverage
#print axioms refreshed_request_original
#print axioms countFits_iff
#print axioms preflight_bounded
#print axioms preflight_too_many
#print axioms preflight_aggregate_limit
#print axioms advance_observation_limit
#print axioms advance_exact
#print axioms advance_checked
#print axioms runEntry_cumulativeGasUsed
#print axioms loop_receipt_trace
#print axioms loop_order
#print axioms loop_accounting
#print axioms loop_entry_refused
#print axioms loop_advance_refused
#print axioms finish_checked
#print axioms run_accepted
#print axioms run_preflight_refused
#print axioms blob_position_refused

end EVMCleanroom.TransactionList
