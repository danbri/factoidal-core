import EthLib.Consensus.Ssz.Merkle.Verify

/-! Isolated Lean 4.35.0 executable SSZ SHA-256 multiproof adapter. -/

namespace Factoidal.SSZ

open EthLib.Consensus.Ssz

/-- Separate local resource refusals from the upstream normative error. -/
inductive BridgeError where
  | claimLimit
  | depthLimit
  | upstream (reason : Err)
  deriving Repr, BEq, DecidableEq

/-- Preserve upstream success and error data with an explicit error tag. -/
def lift {α : Type} : Except Err α → Except BridgeError α
  | .ok value => .ok value
  | .error reason => .error (.upstream reason)

/-- Check caller-supplied budgets before enumerating upstream proof paths. -/
def checkedHelperIndices (maxClaims maxDepth : Nat) (indices : List Nat) :
    Except BridgeError (List Nat) :=
  if indices.length ≤ maxClaims then
    if indices.all (fun index => decide (Nat.log2 index ≤ maxDepth)) then
      lift (getHelperIndices indices)
    else .error .depthLimit
  else .error .claimLimit

/-- Validate budgets, cardinality and 32-byte chunk widths before SHA-256.
The hash operation and exact multiproof verdict are executed in upstream EthLib. -/
def checkedMerkleMultiproof (maxClaims maxDepth : Nat)
    (indices : List Nat) (leaves proof : List Bytes) (root : Bytes) :
    Except BridgeError Bool :=
  match checkedHelperIndices maxClaims maxDepth indices with
  | .error reason => .error reason
  | .ok helpers =>
    if leaves.length = indices.length then
      if proof.length = helpers.length then
        match checkChunks (root :: (leaves ++ proof)) with
        | .error reason => .error (.upstream reason)
        | .ok () => lift (verifyMerkleMultiproof leaves proof indices root)
      else .error (.upstream (.proofLength helpers.length proof.length))
    else .error (.upstream (.leafCount indices.length leaves.length))

/-- Says: over-budget requests refuse before path enumeration.
Does not say: the resource budget is a consensus constant. -/
theorem helper_refuses_claim_budget (cap depth : Nat) (xs : List Nat)
    (h : cap < xs.length) :
    checkedHelperIndices cap depth xs = .error .claimLimit := by
  have hn : ¬ xs.length ≤ cap := Nat.not_le.mpr h
  simp [checkedHelperIndices, hn]

/-- Says: an over-depth index refuses under an otherwise satisfied claim cap.
Does not say: index depth establishes a valid beacon container path. -/
theorem helper_refuses_depth_budget (cap depth : Nat) (xs : List Nat)
    (hsize : xs.length ≤ cap)
    (hdepth : xs.all (fun i => decide (Nat.log2 i ≤ depth)) = false) :
    checkedHelperIndices cap depth xs = .error .depthLimit := by
  simp [checkedHelperIndices, hsize, hdepth]

/-- Says: admitted requests call upstream actual helper indices, preserving errors.
Does not say: our earlier 4.33.1 helper is yet equivalent. -/
theorem helper_delegates (cap depth : Nat) (xs : List Nat)
    (hsize : xs.length ≤ cap)
    (hdepth : xs.all (fun i => decide (Nat.log2 i ≤ depth)) = true) :
    checkedHelperIndices cap depth xs = lift (getHelperIndices xs) := by
  simp [checkedHelperIndices, hsize, hdepth]

/-- Says: index admission errors cannot be converted into a Boolean verdict.
Does not say: an accepted claim authenticates any canonical beacon state. -/
theorem verifier_refuses_admission (cap depth : Nat) (xs : List Nat)
    (leaves proof : List Bytes) (root : Bytes) (err : BridgeError)
    (h : checkedHelperIndices cap depth xs = .error err) :
    checkedMerkleMultiproof cap depth xs leaves proof root = .error err := by
  simp [checkedMerkleMultiproof, h]

/-- Says: on actually admitted, width-checked input, the executable return
is exactly upstream SHA-256 multiproof verification.
Does not say: SHA-256 is collision-free or all consensus uses this adapter. -/
theorem verifier_delegates (cap depth : Nat) (xs : List Nat)
    (leaves proof : List Bytes) (root : Bytes) (helpers : List Nat)
    (hadmit : checkedHelperIndices cap depth xs = .ok helpers)
    (hleaves : leaves.length = xs.length)
    (hproof : proof.length = helpers.length)
    (hchunks : checkChunks (root :: (leaves ++ proof)) = .ok ()) :
    checkedMerkleMultiproof cap depth xs leaves proof root =
      lift (verifyMerkleMultiproof leaves proof xs root) := by
  simp [checkedMerkleMultiproof, hadmit, hleaves, hproof, hchunks]

private def zeroNode : Bytes := Array.replicate 32 0

/-- Independent FIPS-180-4 SHA-256 value for 64 zero bytes. -/
private def twoZeroRoot : Bytes :=
  #[0xf5, 0xa5, 0xfd, 0x42, 0xd1, 0x6a, 0x20, 0x30,
    0x27, 0x98, 0xef, 0x6e, 0xd3, 0x09, 0x97, 0x9b,
    0x43, 0x00, 0x3d, 0x23, 0x20, 0xd9, 0xf0, 0xe8,
    0xea, 0x98, 0x31, 0xa9, 0x27, 0x59, 0xfb, 0x4b]

#guard checkedHelperIndices 4 64 [4] == .ok [5, 3]
#guard checkedHelperIndices 4 64 [2, 3] == .ok []
#guard checkedHelperIndices 1 64 [2, 3] == .error .claimLimit
#guard checkedHelperIndices 4 1 [4] == .error .depthLimit
#guard checkedHelperIndices 4 64 [] == .error (.upstream .emptyRequest)
#guard checkedHelperIndices 4 64 [4, 4] == .error (.upstream .repeatedIndex)
#guard checkedHelperIndices 4 64 [2, 4] == .error (.upstream (.nestedIndex 4))
#guard combine zeroNode zeroNode == twoZeroRoot
#guard checkedMerkleMultiproof 4 64 [2, 3] [zeroNode, zeroNode] [] twoZeroRoot == .ok true
#guard checkedMerkleMultiproof 4 64 [2, 3] [zeroNode, zeroNode] [] zeroNode == .ok false
#guard checkedMerkleMultiproof 4 64 [2, 3] [zeroNode, zeroNode] [] (Array.replicate 31 0) ==
  .error (.upstream (.count 32 31))
#guard checkedMerkleMultiproof 4 64 [2, 3] [zeroNode] [] twoZeroRoot ==
  .error (.upstream (.leafCount 2 1))
#guard checkedMerkleMultiproof 4 64 [2, 3] [zeroNode, zeroNode] [zeroNode] twoZeroRoot ==
  .error (.upstream (.proofLength 0 1))
#guard checkedMerkleMultiproof 4 64 [4, 4] [zeroNode, zeroNode] [] twoZeroRoot ==
  .error (.upstream .repeatedIndex)

#print axioms Factoidal.SSZ.helper_refuses_claim_budget
#print axioms Factoidal.SSZ.helper_refuses_depth_budget
#print axioms Factoidal.SSZ.helper_delegates
#print axioms Factoidal.SSZ.verifier_refuses_admission
#print axioms Factoidal.SSZ.verifier_delegates

end Factoidal.SSZ
