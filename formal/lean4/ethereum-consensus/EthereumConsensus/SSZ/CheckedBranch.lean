import EthereumConsensus.SSZ.GIndex

/-!
# Checked SSZ single-branch admission

Normative positional policy: ethereum/ssz-specs at
4c2f08805080c6b4b12ede7bf48ad6a80229f4b1,
src/ssz/gindex.py: gindex_depth(1) = 0 but gindex_length(1)
rejects ROOT_HAS_NO_BRANCH; indices < 1 reject NOT_A_GINDEX.

The older generic calculate accepts a zero-length identity fold at root 1.
This module does not alter that algebraic helper. It adds the distinct
checked *proof-branch* entry point, which refuses root 1 as a branch and
checks exact witness length before invoking any supplied pair function.

This is not a cryptographic verifier: α and pair are caller supplied;
there is no fixed 32-byte SHA-256 root or SSZ type/layout validation.
-/

namespace EthereumConsensus.SSZ

/-- An admissible positive-depth branch has exactly depth index witnesses.
    The root is a node but cannot itself request a proof branch. -/
def branchLength (index : Nat) : Option Nat :=
  if index ≤ 1 then none else some (depth index)

/-- A separate identity-only node operation at root 1. This does not
    navigate the SSZ layout of a structured value. -/
def rootNodeIdentity {α : Type} (root : α) (index : Nat) : Option α :=
  if index = 1 then some root else none

/-- Checked proof-branch calculation: refuse invalid branch indices and
    witness lengths before evaluating the supplied pair hash. -/
def calculateBranch {α : Type} (pair : α → α → α)
    (leaf : α) (siblings : List α) (index : Nat) : Option α :=
  match branchLength index with
  | none => none
  | some expectedLen =>
      if siblings.length = expectedLen then
        some (foldProof pair leaf index siblings)
      else none

/-- Checked equality wrapper, still conditional on the external pair/hash. -/
def verifyBranch {α : Type} [BEq α] (pair : α → α → α)
    (leaf : α) (siblings : List α) (index : Nat)
    (expected : α) : Bool :=
  match calculateBranch pair leaf siblings index with
  | none => false
  | some calculated => calculated == expected

/-- Says: zero is not an admissible proof-branch index.
    Does not say: root node 1 is invalid as an SSZ node. -/
theorem branchLength_rejects_zero : branchLength 0 = none := by
  rfl

/-- Says: root 1 has no admitted branch.
    Does not say: root 1 lacks a valid hash_tree_root. -/
theorem branchLength_rejects_root : branchLength 1 = none := by
  rfl

/-- Says: all indices deeper than the root produce the executable depth.
    Does not say: that node exists in a concrete SSZ container layout. -/
theorem branchLength_of_valid (index : Nat) (h : 1 < index) :
    branchLength index = some (depth index) := by
  have hnot : ¬ index ≤ 1 := by omega
  simp [branchLength, hnot]

/-- Says: root-node identity and proof-branch rejection are distinct.
    Does not say: the supplied root is a trusted SHA-256 digest. -/
theorem rootNodeIdentity_at_root {α : Type} (root : α) :
    rootNodeIdentity root 1 = some root := by
  rfl

/-- Says: the real checked entry point rejects root 1.
    Does not say: node-root lookup should reject the root. -/
theorem calculateBranch_rejects_root {α : Type} (pair : α → α → α)
    (leaf : α) (siblings : List α) :
    calculateBranch pair leaf siblings 1 = none := by
  rfl

/-- Says: a branch of the wrong length is refused at the actual entry point.
    Does not say: correct-length witnesses are authenticated. -/
theorem calculateBranch_rejects_wrong_length {α : Type}
    (pair : α → α → α) (leaf : α) (siblings : List α) (index : Nat)
    (hbad : siblings.length ≠ depth index) :
    calculateBranch pair leaf siblings index = none := by
  by_cases hroot : index ≤ 1
  · simp [calculateBranch, branchLength, hroot]
  · simp [calculateBranch, branchLength, hroot, hbad]

/-- Says: a positive-depth, exact-length branch evaluates through the real
    ordered foldProof implementation. Does not say: pair is SHA-256. -/
theorem calculateBranch_of_valid {α : Type} (pair : α → α → α)
    (leaf : α) (siblings : List α) (index : Nat)
    (hindex : 1 < index) (hlen : siblings.length = depth index) :
    calculateBranch pair leaf siblings index =
      some (foldProof pair leaf index siblings) := by
  have hnot : ¬ index ≤ 1 := by omega
  simp [calculateBranch, branchLength, hnot, hlen]

/-- Says: the checked verification wrapper cannot accept the root as a
    proof-branch index, regardless of pair or expected value.
    Does not say: admitted branches have cryptographic soundness. -/
theorem verifyBranch_rejects_root {α : Type} [BEq α]
    (pair : α → α → α) (leaf : α) (siblings : List α)
    (expected : α) : verifyBranch pair leaf siblings 1 expected = false := by
  rfl

private def toyPair (a b : Nat) : Nat := 100 * a + b

#guard branchLength 0 == none
#guard branchLength 1 == none
#guard branchLength 2 == some 1
#guard branchLength 3 == some 1
#guard branchLength 9 == some 3
#guard rootNodeIdentity 37 1 == some 37
#guard rootNodeIdentity 37 0 == none
#guard calculateBranch toyPair 9 [] 0 == none
#guard calculateBranch toyPair 9 [] 1 == none
#guard calculateBranch toyPair 9 [8] 2 == some 908
#guard calculateBranch toyPair 9 [8] 3 == some 809
#guard calculateBranch toyPair 9 [8, 5, 3] 9 == some 8090503
#guard calculateBranch toyPair 9 [8, 5] 9 == none
#guard verifyBranch toyPair 9 [8] 2 908
#guard !(verifyBranch toyPair 9 [8] 2 809)
#guard !(verifyBranch toyPair 9 [] 1 9)

#print axioms EthereumConsensus.SSZ.branchLength_rejects_zero
#print axioms EthereumConsensus.SSZ.branchLength_rejects_root
#print axioms EthereumConsensus.SSZ.branchLength_of_valid
#print axioms EthereumConsensus.SSZ.rootNodeIdentity_at_root
#print axioms EthereumConsensus.SSZ.calculateBranch_rejects_root
#print axioms EthereumConsensus.SSZ.calculateBranch_rejects_wrong_length
#print axioms EthereumConsensus.SSZ.calculateBranch_of_valid
#print axioms EthereumConsensus.SSZ.verifyBranch_rejects_root

end EthereumConsensus.SSZ
