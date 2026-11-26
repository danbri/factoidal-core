import EthereumConsensus.SSZ.ByteProof

/-! Kernel-checked properties of the concrete byte proof entry points and
    the multiproof frontier reducer. -/

namespace EthereumConsensus.SSZ

/-- Kind: invariant.
    Says: a chunk hash takes 64 bytes and returns 32 bytes.
    Does not say: SHA-256 satisfies any cryptographic assumption. -/
theorem hashPair_width (left right : Chunk) :
    (left.bytes ++ right.bytes).size = 64 ∧ (hashPair left right).bytes.size = 32 := by
  exact ⟨by simp [ByteArray.size_append, left.width, right.width], (hashPair left right).width⟩

/-- Kind: refinement.
    Says: chunk hashing applies the project SHA-256 to left bytes followed by right bytes.
    Does not say: the SHA-256 implementation is proved equivalent to FIPS 180-4. -/
theorem hashPair_ordered_sha256 (left right : Chunk) :
    (hashPair left right).bytes = L4Factoidal.Crypto.sha256 (left.bytes ++ right.bytes) := rfl

/-- Kind: admission.
    Says: the chunk constructor refuses any byte array of the wrong width.
    Does not say: a 32-byte input is an authenticated Merkle node. -/
theorem Chunk.ofBytes_refuses_wrong_width (bytes : ByteArray) (bad : bytes.size ≠ 32) :
    Chunk.ofBytes bytes = .error .chunkWidth := by
  simp [Chunk.ofBytes, bad]

/-- Kind: refinement.
    Says: successful width validation preserves the supplied bytes.
    Does not say: the bytes hold a hash from a trusted source. -/
theorem Chunk.bytes_ofBytes_ok (bytes : ByteArray) (chunk : Chunk)
    (valid : Chunk.ofBytes bytes = .ok chunk) : chunk.bytes = bytes := by
  unfold Chunk.ofBytes at valid
  split at valid
  · cases valid
    rfl
  · cases valid

/-- Kind: refinement.
    Says: the Boolean byte-array comparison is true exactly when the arrays are equal.
    Does not say: the comparison has a particular timing behaviour. -/
theorem byteArray_beq_iff_eq (left right : ByteArray) :
    (left == right) = true ↔ left = right := by
  change (left.data == right.data) = true ↔ left = right
  rw [beq_iff_eq, ByteArray.ext_iff]

/-- Kind: admission.
    Says: converting a witness list refuses a wrong width at any position.
    Does not say: any correctly sized witness is authenticated. -/
theorem mapChunks_refuses_wrong_width (bytes : List ByteArray) (b : ByteArray)
    (mem : b ∈ bytes) (bad : b.size ≠ 32) :
    bytes.mapM Chunk.ofBytes = .error .chunkWidth := by
  induction bytes with
  | nil => simp at mem
  | cons head tail ih =>
    rw [List.mapM_cons]
    rcases List.mem_cons.mp mem with rfl | memTail
    · simp [Chunk.ofBytes, bad, bind, Except.bind]
    · by_cases width : head.size = 32
      · simp [Chunk.ofBytes, width, ih memTail, bind, Except.bind]
      · simp [Chunk.ofBytes, width, bind, Except.bind]

/-- Kind: refinement.
    Says: validation recovers every chunk in order from a list of 32-byte chunks.
    Does not say: the chunks stand at the indicated indices in a particular SSZ value. -/
theorem mapChunks_of_valid (chunks : List Chunk) :
    (chunks.map Chunk.bytes).mapM Chunk.ofBytes = .ok chunks := by
  induction chunks with
  | nil => rfl
  | cons chunk chunks ih =>
    cases chunk with
    | mk bytes width => simp [Chunk.ofBytes, width, ih, bind, Except.bind, pure, Except.pure]

/-- Kind: admission.
    Says: a supported depth budget refuses a branch at index zero or one.
    Does not say: root node 1 is invalid as an SSZ node. -/
theorem calculateByteBranch_refuses_invalid_index (maxDepth index : Nat) (leaf : ByteArray)
    (proof : List ByteArray) (cap : maxDepth ≤ maxByteProofDepth) (invalid : index ≤ 1) :
    calculateByteBranch maxDepth index leaf proof = .error .invalidIndex := by
  have zeroDepth : depth index = 0 := by
    have casesIndex : index = 0 ∨ index = 1 := by omega
    rcases casesIndex with rfl | rfl <;> rfl
  simp [calculateByteBranch, branchChunks, Nat.not_lt.mpr cap, zeroDepth, invalid,
    bind, Except.bind]

/-- Kind: admission.
    Says: a branch over its selected depth budget is refused.
    Does not say: the local budget is an SSZ protocol constant. -/
theorem calculateByteBranch_refuses_over_depth (maxDepth index : Nat) (leaf : ByteArray)
    (proof : List ByteArray) (over : maxDepth < depth index) :
    calculateByteBranch maxDepth index leaf proof = .error .resourceLimit := by
  simp [calculateByteBranch, branchChunks, over, bind, Except.bind]

/-- Kind: admission.
    Says: within the budget, a branch-capable index with the wrong proof length is refused.
    Does not say: a correctly sized branch matches a trusted root. -/
theorem calculateByteBranch_refuses_wrong_length (maxDepth index : Nat) (leaf : ByteArray)
    (proof : List ByteArray) (cap : maxDepth ≤ maxByteProofDepth) (budget : depth index ≤ maxDepth)
    (validIndex : 1 < index) (wrongLength : proof.length ≠ depth index) :
    calculateByteBranch maxDepth index leaf proof = .error .proofLength := by
  simp [calculateByteBranch, branchChunks, Nat.not_lt.mpr cap, Nat.not_lt.mpr budget,
    Nat.not_le.mpr validIndex, wrongLength, bind, Except.bind]

/-- Kind: admission.
    Says: after branch budget and shape checks, any wrong-width leaf is refused.
    Does not say: a correctly sized leaf is an SSZ value of a particular type. -/
theorem calculateByteBranch_refuses_leaf_width (maxDepth index : Nat) (leaf : ByteArray)
    (proof : List ByteArray) (cap : maxDepth ≤ maxByteProofDepth) (budget : depth index ≤ maxDepth)
    (validIndex : 1 < index) (lengthEq : proof.length = depth index) (bad : leaf.size ≠ 32) :
    calculateByteBranch maxDepth index leaf proof = .error .chunkWidth := by
  simp [calculateByteBranch, branchChunks, Nat.not_lt.mpr cap, Nat.not_lt.mpr budget,
    Nat.not_le.mpr validIndex, lengthEq, Chunk.ofBytes, bad, bind, Except.bind]

/-- Kind: admission.
    Says: after branch budget and shape checks, a wrong width anywhere in the proof is refused.
    Does not say: correctly sized proof bytes match a trusted root. -/
theorem calculateByteBranch_refuses_proof_width (maxDepth index : Nat) (leaf : Chunk)
    (proof : List ByteArray) (cap : maxDepth ≤ maxByteProofDepth) (budget : depth index ≤ maxDepth)
    (validIndex : 1 < index) (lengthEq : proof.length = depth index)
    (b : ByteArray) (mem : b ∈ proof) (bad : b.size ≠ 32) :
    calculateByteBranch maxDepth index leaf.bytes proof = .error .chunkWidth := by
  simp [calculateByteBranch, branchChunks, Nat.not_lt.mpr cap, Nat.not_lt.mpr budget,
    Nat.not_le.mpr validIndex, lengthEq, Chunk.ofBytes, leaf.width,
    mapChunks_refuses_wrong_width proof b mem bad, bind, Except.bind]

/-- Kind: refinement.
    Says: admitted leaf and proof bytes reach the existing ordered fold with concrete chunk hashing.
    Does not say: this result matches the expected root or refers to a valid SSZ type path. -/
theorem calculateByteBranch_of_valid (maxDepth index : Nat) (leaf : Chunk) (proof : List Chunk)
    (cap : maxDepth ≤ maxByteProofDepth) (budget : depth index ≤ maxDepth)
    (validIndex : 1 < index) (lengthEq : proof.length = depth index) :
    calculateByteBranch maxDepth index leaf.bytes (proof.map Chunk.bytes) =
      .ok (foldProof hashPair leaf index proof) := by
  have parsed := mapChunks_of_valid proof
  rw [List.mapM_map] at parsed
  simp [calculateByteBranch, branchChunks, Nat.not_lt.mpr cap, Nat.not_lt.mpr budget,
    Nat.not_le.mpr validIndex, lengthEq, Chunk.ofBytes, leaf.width, parsed,
    bind, Except.bind, pure, Except.pure]

/-- Kind: invariant.
    Says: the terminal test yields a value exactly on the singleton root frontier.
    Does not say: that value agrees with a supplied expected root. -/
theorem frontierRoot_eq_some {α : Type} (frontier : List (Nat × α)) (root : α) :
    frontierRoot? frontier = some root ↔ frontier = [(1, root)] := by
  cases frontier with
  | nil => simp [frontierRoot?]
  | cons entry rest =>
    obtain ⟨index, value⟩ := entry
    cases rest with
    | nil =>
      cases index with
      | zero => simp [frontierRoot?]
      | succ n => cases n <;> simp [frontierRoot?]
    | cons _ _ => simp [frontierRoot?]

/-- Kind: resource bound.
    Says: zero fuel accepts the singleton root and otherwise refuses.
    Does not say: more fuel suffices on any arbitrary frontier. -/
theorem reduceFrontier_zero_fuel {α : Type} (pair : α → α → α)
    (frontier : List (Nat × α)) :
    reduceFrontier pair 0 frontier =
      match frontierRoot? frontier with
      | some root => .ok root
      | none => .error .resourceLimit := by cases h : frontierRoot? frontier <;> simp [reduceFrontier, h]

/-- Kind: invariant.
    Says: the actual successful step selects existing siblings, replaces them with
    their ordered parent, and retains the rest of the frontier.
    Does not say: a particular frontier has the required sibling entries. -/
theorem reduceFrontierStep_of_ok {α : Type} (pair : α → α → α)
    {frontier next : List (Nat × α)} (step : reduceFrontierStep pair frontier = .ok next) :
    ∃ (p : Nat) (left right : Nat × α),
      left ∈ frontier ∧ left.1 = child p false ∧
      right ∈ frontier.eraseP (fun entry => entry.1 == child p false) ∧ right.1 = child p true ∧
      next = (p, pair left.2 right.2) :: List.eraseP (fun entry => entry.1 == child p true)
        (frontier.eraseP (fun entry => entry.1 == child p false)) := by
  simp only [reduceFrontierStep] at step
  split at step
  · cases step
  split at step
  · cases step
  split at step
  · cases step
  rename_i left leftFound
  split at step
  · cases step
  rename_i right rightFound
  have leftIndex := List.find?_some leftFound
  have rightIndex := List.find?_some rightFound
  exact ⟨parent (frontier.foldl (fun acc entry => max acc entry.1) 0), left, right,
    List.mem_of_find?_eq_some leftFound, beq_iff_eq.mp leftIndex,
    List.mem_of_find?_eq_some rightFound, beq_iff_eq.mp rightIndex, (Except.ok.inj step).symm⟩

/-- Kind: resource bound.
    Says: a successful combination consumes two entries and creates one.
    Does not say: every step succeeds or the whole frontier reaches the root. -/
theorem reduceFrontierStep_length {α : Type} (pair : α → α → α)
    {frontier next : List (Nat × α)} (step : reduceFrontierStep pair frontier = .ok next) :
    next.length + 1 = frontier.length := by
  obtain ⟨p, left, right, leftMem, leftIndex, rightMem, rightIndex, rfl⟩ :=
    reduceFrontierStep_of_ok pair step
  have leftErase := List.length_eraseP_of_mem leftMem (p := fun entry => entry.1 == child p false)
    (by simp [leftIndex])
  have rightErase := List.length_eraseP_of_mem rightMem (p := fun entry => entry.1 == child p true)
    (by simp [rightIndex])
  have remaining : 0 < (frontier.eraseP (fun entry => entry.1 == child p false)).length :=
    List.length_pos_of_mem rightMem
  rw [List.length_cons, rightErase, leftErase]
  rw [leftErase] at remaining
  omega

/-- Agreement with a finite binary tree whose leaves start at `leafBase`.
    A full tree of depth `d` uses `leafBase = 2 ^ d`. -/
def FrontierAgrees {α : Type} (leafBase : Nat) (value : Nat → α)
    (frontier : List (Nat × α)) : Prop :=
  ∀ entry ∈ frontier, 1 ≤ entry.1 ∧ entry.1 < 2 * leafBase ∧ entry.2 = value entry.1

/-- Kind: preservation.
    Says: one successful step preserves agreement with the finite Merkle tree.
    Does not say: supplied hashes really agree with a trusted tree. -/
theorem reduceFrontierStep_preserves {α : Type} (pair : α → α → α) (leafBase : Nat)
    (value : Nat → α)
    (tree : ∀ p, 1 ≤ p → p < leafBase → value p = pair (value (child p false)) (value (child p true)))
    {frontier next : List (Nat × α)} (agrees : FrontierAgrees leafBase value frontier)
    (step : reduceFrontierStep pair frontier = .ok next) : FrontierAgrees leafBase value next := by
  obtain ⟨p, left, right, leftMem, leftIndex, rightMem, rightIndex, rfl⟩ :=
    reduceFrontierStep_of_ok pair step
  intro entry mem
  rcases List.mem_cons.mp mem with rfl | remaining
  · obtain ⟨leftPos, leftBound, leftValue⟩ := agrees left leftMem
    have rightValue := (agrees right (List.mem_of_mem_eraseP rightMem)).2.2
    have leftIndex' : left.1 = 2 * p := by simpa [child] using leftIndex
    have parentPos : 1 ≤ p := by omega
    have parentBound : p < leafBase := by omega
    refine ⟨parentPos, by omega, ?_⟩
    change pair left.2 right.2 = value p
    rw [leftValue, rightValue, leftIndex, rightIndex, tree p parentPos parentBound]
  · exact agrees entry (List.mem_of_mem_eraseP (List.mem_of_mem_eraseP remaining))

/-- Kind: conditional correctness.
    Says: a successful reduction of entries agreeing with a finite Merkle tree returns its root.
    Does not say: all admissible requests reduce successfully or that SHA-256 is collision resistant. -/
theorem reduceFrontier_agrees {α : Type} (pair : α → α → α) (leafBase : Nat)
    (value : Nat → α)
    (tree : ∀ p, 1 ≤ p → p < leafBase → value p = pair (value (child p false)) (value (child p true)))
    (fuel : Nat) (frontier : List (Nat × α)) (root : α)
    (agrees : FrontierAgrees leafBase value frontier)
    (result : reduceFrontier pair fuel frontier = .ok root) : root = value 1 := by
  induction fuel generalizing frontier with
  | zero =>
    cases finished : frontierRoot? frontier with
    | none => simp [reduceFrontier_zero_fuel, finished] at result
    | some found =>
      have hfrontier := (frontierRoot_eq_some frontier found).mp finished
      have rootEq : found = root := by simpa [reduceFrontier_zero_fuel, finished] using result
      subst root
      subst frontier
      exact (agrees (1, found) (by simp)).2.2
  | succ n ih =>
    cases finished : frontierRoot? frontier with
    | some found =>
      have hfrontier := (frontierRoot_eq_some frontier found).mp finished
      have rootEq : found = root := by simpa [reduceFrontier, finished] using result
      subst root
      subst frontier
      exact (agrees (1, found) (by simp)).2.2
    | none =>
      cases step : reduceFrontierStep pair frontier with
      | error err => simp [reduceFrontier, finished, step] at result
      | ok next =>
        exact ih next (reduceFrontierStep_preserves pair leafBase value tree agrees step)
          (by simpa [reduceFrontier, finished, step] using result)

/-- Kind: conditional correctness.
    Says: if the byte multiproof's admitted frontier agrees with a finite tree
    using the concrete chunk hash, a successful public calculation returns that tree's root.
    Does not say: admission by itself establishes agreement or successful reduction. -/
theorem calculateByteMulti_agrees (maxClaims maxDepth : Nat) (indices : List Nat)
    (leaves proof : List ByteArray) (leafBase : Nat) (value : Nat → Chunk)
    (tree : ∀ p, 1 ≤ p → p < leafBase → value p = hashPair (value (child p false)) (value (child p true)))
    (frontier : List (Nat × Chunk)) (root : Chunk)
    (admitted : multiFrontier maxClaims maxDepth indices leaves proof = .ok frontier)
    (agrees : FrontierAgrees leafBase value frontier)
    (result : calculateByteMulti maxClaims maxDepth indices leaves proof = .ok root) :
    root = value 1 := by
  apply reduceFrontier_agrees hashPair leafBase value tree frontier.length frontier root agrees
  simpa [calculateByteMulti, admitted, bind, Except.bind] using result

/-- Kind: admission.
    Says: the multiproof calculation refuses a request with too many claims.
    Does not say: the caller's claim cap is fixed by the protocol. -/
theorem calculateByteMulti_refuses_over_claim_cap (maxClaims maxDepth : Nat) (indices : List Nat)
    (leaves proof : List ByteArray) (over : maxClaims < indices.length) :
    calculateByteMulti maxClaims maxDepth indices leaves proof = .error .resourceLimit := by
  simp [calculateByteMulti, multiFrontier, over, bind, Except.bind]

/-- Kind: admission.
    Says: the multiproof calculation refuses out-of-budget indices.
    Does not say: the caller's depth limit is fixed by the protocol. -/
theorem calculateByteMulti_refuses_over_depth (maxClaims maxDepth : Nat) (indices : List Nat)
    (leaves proof : List ByteArray) (over : indices.all (fun index => decide (depth index ≤ maxDepth)) = false) :
    calculateByteMulti maxClaims maxDepth indices leaves proof = .error .resourceLimit := by
  simp [calculateByteMulti, multiFrontier, over, bind, Except.bind]

/-- Kind: admission.
    Says: within the resource caps, the byte API refuses claims rejected by the helper policy.
    Does not say: an admissible set of indices refers to a particular trusted SSZ value. -/
theorem calculateByteMulti_refuses_invalid_claims (maxClaims maxDepth : Nat) (indices : List Nat)
    (leaves proof : List ByteArray) (claimsCap : maxClaims ≤ maxByteProofClaims)
    (depthCap : maxDepth ≤ maxByteProofDepth) (count : indices.length ≤ maxClaims)
    (depths : indices.all (fun index => decide (depth index ≤ maxDepth)) = true)
    (invalid : helperIndices indices = none) :
    calculateByteMulti maxClaims maxDepth indices leaves proof = .error .invalidClaims := by
  simp [calculateByteMulti, multiFrontier, Nat.not_lt.mpr claimsCap, Nat.not_lt.mpr depthCap,
    Nat.not_lt.mpr count, depths, invalid, bind, Except.bind]

/-- Kind: admission.
    Says: after budget and index checks, a multiproof needs one leaf per claim.
    Does not say: a leaf of the correct width contains a particular SSZ value. -/
theorem calculateByteMulti_refuses_wrong_leaf_count (maxClaims maxDepth : Nat) (indices helpers : List Nat)
    (leaves proof : List ByteArray) (claimsCap : maxClaims ≤ maxByteProofClaims)
    (depthCap : maxDepth ≤ maxByteProofDepth) (count : indices.length ≤ maxClaims)
    (depths : indices.all (fun index => decide (depth index ≤ maxDepth)) = true)
    (validClaims : helperIndices indices = some helpers) (bad : leaves.length ≠ indices.length) :
    calculateByteMulti maxClaims maxDepth indices leaves proof = .error .leafCount := by
  simp [calculateByteMulti, multiFrontier, Nat.not_lt.mpr claimsCap, Nat.not_lt.mpr depthCap,
    Nat.not_lt.mpr count, depths, validClaims, bad, bind, Except.bind]

/-- Kind: admission.
    Says: a multiproof of admissible shape needs exactly one proof chunk per helper.
    Does not say: the supplied chunks match their tree positions. -/
theorem calculateByteMulti_refuses_wrong_proof_length (maxClaims maxDepth : Nat) (indices helpers : List Nat)
    (leaves proof : List ByteArray) (claimsCap : maxClaims ≤ maxByteProofClaims)
    (depthCap : maxDepth ≤ maxByteProofDepth) (count : indices.length ≤ maxClaims)
    (depths : indices.all (fun index => decide (depth index ≤ maxDepth)) = true)
    (validClaims : helperIndices indices = some helpers) (leafCount : leaves.length = indices.length)
    (bad : proof.length ≠ helpers.length) :
    calculateByteMulti maxClaims maxDepth indices leaves proof = .error .proofLength := by
  simp [calculateByteMulti, multiFrontier, Nat.not_lt.mpr claimsCap, Nat.not_lt.mpr depthCap,
    Nat.not_lt.mpr count, depths, validClaims, leafCount, bad, bind, Except.bind]

/-- Kind: admission.
    Says: after budget and shape checks, a wrong-width multiproof leaf is refused.
    Does not say: the other chunks are authenticated. -/
theorem calculateByteMulti_refuses_leaf_width (maxClaims maxDepth : Nat) (indices helpers : List Nat)
    (leaves proof : List ByteArray) (claimsCap : maxClaims ≤ maxByteProofClaims)
    (depthCap : maxDepth ≤ maxByteProofDepth) (count : indices.length ≤ maxClaims)
    (depths : indices.all (fun index => decide (depth index ≤ maxDepth)) = true)
    (validClaims : helperIndices indices = some helpers) (leafCount : leaves.length = indices.length)
    (proofLength : proof.length = helpers.length) (b : ByteArray) (mem : b ∈ leaves) (bad : b.size ≠ 32) :
    calculateByteMulti maxClaims maxDepth indices leaves proof = .error .chunkWidth := by
  simp [calculateByteMulti, multiFrontier, Nat.not_lt.mpr claimsCap, Nat.not_lt.mpr depthCap,
    Nat.not_lt.mpr count, depths, validClaims, leafCount, proofLength,
    mapChunks_refuses_wrong_width leaves b mem bad, bind, Except.bind]

/-- Kind: admission.
    Says: after budget, shape, and leaf checks, a wrong-width multiproof witness is refused.
    Does not say: all correctly sized witnesses match a trusted root. -/
theorem calculateByteMulti_refuses_proof_width (maxClaims maxDepth : Nat) (indices helpers : List Nat)
    (leaves : List Chunk) (proof : List ByteArray) (claimsCap : maxClaims ≤ maxByteProofClaims)
    (depthCap : maxDepth ≤ maxByteProofDepth) (count : indices.length ≤ maxClaims)
    (depths : indices.all (fun index => decide (depth index ≤ maxDepth)) = true)
    (validClaims : helperIndices indices = some helpers) (leafCount : leaves.length = indices.length)
    (proofLength : proof.length = helpers.length) (b : ByteArray) (mem : b ∈ proof) (bad : b.size ≠ 32) :
    calculateByteMulti maxClaims maxDepth indices (leaves.map Chunk.bytes) proof = .error .chunkWidth := by
  have parsed := mapChunks_of_valid leaves
  rw [List.mapM_map] at parsed
  simp [calculateByteMulti, multiFrontier, Nat.not_lt.mpr claimsCap, Nat.not_lt.mpr depthCap,
    Nat.not_lt.mpr count, depths, validClaims, leafCount, proofLength, parsed,
    mapChunks_refuses_wrong_width proof b mem bad, bind, Except.bind]

/-- Kind: refinement.
    Says: branch verification returns the calculated root, and its verdict is
    true exactly when that root's bytes equal the caller's expected bytes.
    Does not say: the caller's expected root is trusted. -/
theorem verifyByteBranch_of_ok (maxDepth index : Nat) (leaf : ByteArray)
    (proof : List ByteArray) (expectedRoot : ByteArray) (result : ByteProofResult)
    (verified : verifyByteBranch maxDepth index leaf proof expectedRoot = .ok result) :
    calculateByteBranch maxDepth index leaf proof = .ok result.root ∧
      (result.matchesRoot = true ↔ result.root.bytes = expectedRoot) := by
  cases admitted : branchChunks maxDepth index leaf proof with
  | error err => simp [verifyByteBranch, admitted, bind, Except.bind] at verified
  | ok chunks =>
    obtain ⟨checkedLeaf, checkedProof⟩ := chunks
    cases expected : Chunk.ofBytes expectedRoot with
    | error err => simp [verifyByteBranch, admitted, expected, bind, Except.bind] at verified
    | ok expectedChunk =>
      simp [verifyByteBranch, admitted, expected, bind, Except.bind, pure, Except.pure] at verified
      subst result
      constructor
      · simp [calculateByteBranch, admitted, bind, Except.bind, pure, Except.pure]
      · simpa [Chunk.bytes_ofBytes_ok expectedRoot expectedChunk expected] using
          byteArray_beq_iff_eq (foldProof hashPair checkedLeaf index checkedProof).bytes expectedChunk.bytes

/-- Kind: refinement.
    Says: multiproof verification returns the calculated root, and its verdict is
    true exactly when that root's bytes equal the caller's expected bytes.
    Does not say: the caller's expected root is trusted. -/
theorem verifyByteMulti_of_ok (maxClaims maxDepth : Nat) (indices : List Nat)
    (leaves proof : List ByteArray) (expectedRoot : ByteArray) (result : ByteProofResult)
    (verified : verifyByteMulti maxClaims maxDepth indices leaves proof expectedRoot = .ok result) :
    calculateByteMulti maxClaims maxDepth indices leaves proof = .ok result.root ∧
      (result.matchesRoot = true ↔ result.root.bytes = expectedRoot) := by
  cases admitted : multiFrontier maxClaims maxDepth indices leaves proof with
  | error err => simp [verifyByteMulti, admitted, bind, Except.bind] at verified
  | ok frontier =>
    cases expected : Chunk.ofBytes expectedRoot with
    | error err => simp [verifyByteMulti, admitted, expected, bind, Except.bind] at verified
    | ok expectedChunk =>
      cases reduced : reduceFrontier hashPair frontier.length frontier with
      | error err => simp [verifyByteMulti, admitted, expected, reduced, bind, Except.bind] at verified
      | ok root =>
        simp [verifyByteMulti, admitted, expected, reduced, bind, Except.bind, pure, Except.pure] at verified
        subst result
        constructor
        · simp [calculateByteMulti, admitted, reduced, bind, Except.bind]
        · simpa [Chunk.bytes_ofBytes_ok expectedRoot expectedChunk expected] using
            byteArray_beq_iff_eq root.bytes expectedChunk.bytes

private def zeroChunk : Chunk := ⟨⟨Array.replicate 32 0⟩, by decide⟩
private def toyPair (left right : Nat) : Nat := 100 * left + right

private def observesError (result : Except ByteProofError α) (err : ByteProofError) : Bool :=
  match result with
  | .ok _ => false
  | .error found => found == err

-- The digest of one 64-byte message of zeroes pins the concatenation boundary.
#guard L4Factoidal.Crypto.bytesToHex (hashPair zeroChunk zeroChunk).bytes ==
  "f5a5fd42d16a20302798ef6ed309979b43003d2320d9f0e8ea9831a92759fb4b"
#guard observesError (calculateByteBranch 64 1 zeroChunk.bytes []) .invalidIndex
#guard observesError (calculateByteMulti 64 64 [2, 2] [zeroChunk.bytes, zeroChunk.bytes] []) .invalidClaims
#guard observesError (calculateByteMulti 64 64 [2, 4] [zeroChunk.bytes, zeroChunk.bytes] []) .invalidClaims
#guard (calculateByteMulti 64 64 [2, 3] [zeroChunk.bytes, zeroChunk.bytes] []).toOption.any
  (fun root => root.bytes == (hashPair zeroChunk zeroChunk).bytes)
#guard observesError (reduceFrontier toyPair 0 [(2, 9), (3, 8)]) .resourceLimit
#guard (reduceFrontier toyPair 1 [(3, 8), (2, 9)]).toOption == some 908
#guard (reduceFrontier toyPair 0 [(1, 7)]).toOption == some 7
#guard observesError (reduceFrontier toyPair 2 [(1, 7), (2, 9), (3, 8)]) .conflictingNode
#guard observesError (reduceFrontier toyPair 1 [(2, 9)]) .incompleteProof

#print axioms EthereumConsensus.SSZ.hashPair_width
#print axioms EthereumConsensus.SSZ.hashPair_ordered_sha256
#print axioms EthereumConsensus.SSZ.Chunk.ofBytes_refuses_wrong_width
#print axioms EthereumConsensus.SSZ.Chunk.bytes_ofBytes_ok
#print axioms EthereumConsensus.SSZ.byteArray_beq_iff_eq
#print axioms EthereumConsensus.SSZ.mapChunks_refuses_wrong_width
#print axioms EthereumConsensus.SSZ.mapChunks_of_valid
#print axioms EthereumConsensus.SSZ.calculateByteBranch_refuses_invalid_index
#print axioms EthereumConsensus.SSZ.calculateByteBranch_refuses_over_depth
#print axioms EthereumConsensus.SSZ.calculateByteBranch_refuses_wrong_length
#print axioms EthereumConsensus.SSZ.calculateByteBranch_refuses_leaf_width
#print axioms EthereumConsensus.SSZ.calculateByteBranch_refuses_proof_width
#print axioms EthereumConsensus.SSZ.calculateByteBranch_of_valid
#print axioms EthereumConsensus.SSZ.frontierRoot_eq_some
#print axioms EthereumConsensus.SSZ.reduceFrontier_zero_fuel
#print axioms EthereumConsensus.SSZ.reduceFrontierStep_of_ok
#print axioms EthereumConsensus.SSZ.reduceFrontierStep_length
#print axioms EthereumConsensus.SSZ.reduceFrontierStep_preserves
#print axioms EthereumConsensus.SSZ.reduceFrontier_agrees
#print axioms EthereumConsensus.SSZ.calculateByteMulti_agrees
#print axioms EthereumConsensus.SSZ.calculateByteMulti_refuses_over_claim_cap
#print axioms EthereumConsensus.SSZ.calculateByteMulti_refuses_over_depth
#print axioms EthereumConsensus.SSZ.calculateByteMulti_refuses_invalid_claims
#print axioms EthereumConsensus.SSZ.calculateByteMulti_refuses_wrong_leaf_count
#print axioms EthereumConsensus.SSZ.calculateByteMulti_refuses_wrong_proof_length
#print axioms EthereumConsensus.SSZ.calculateByteMulti_refuses_leaf_width
#print axioms EthereumConsensus.SSZ.calculateByteMulti_refuses_proof_width
#print axioms EthereumConsensus.SSZ.verifyByteBranch_of_ok
#print axioms EthereumConsensus.SSZ.verifyByteMulti_of_ok

end EthereumConsensus.SSZ
