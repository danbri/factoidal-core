import EthereumConsensus.SSZ.CheckedBranch

/-!
# SSZ multiproof helper-index derivation (positional, not cryptographic)

Normative reference: ethereum/ssz-specs@
4c2f08805080c6b4b12ede7bf48ad6a80229f4b1,
src/ssz/gindex.py: get_path_indices, get_branch_indices,
_reject_related, get_helper_indices.

The upstream proof-branch API refuses index 0 and root 1. Helper indices
are the siblings of all claimed paths, less all claimed path nodes,
deduplicated and sorted from highest index to lowest. No data/root bytes
are handled here. This does not authenticate an SSZ value or implement
SHA-256, BLS, fork-choice or consensus transitions.
-/

namespace EthereumConsensus.SSZ

/-- Indices from a claimed node upwards, excluding the root. The domain
    is checked at the public multiproof entry, not in this helper. -/
def pathIndices (index : Nat) : List Nat :=
  (List.range (depth index)).map (fun shift => index / 2 ^ shift)

/-- The siblings in the proof branch, leaf-first. -/
def branchIndices (index : Nat) : List Nat :=
  (pathIndices index).map sibling

/-- Refuse repeated claims; checks are over values, not caller identities. -/
def uniqueClaims : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && uniqueClaims xs

/-- No claimed node may be a strict ancestor of another claimed node. -/
def unrelatedClaims (xs : List Nat) : Bool :=
  xs.all (fun index =>
    ((pathIndices index).drop 1).all (fun ancestor =>
      !(xs.contains ancestor)))

/-- Upstream-style multiproof input policy: nonempty, branch-capable nodes,
    distinct indices and no ancestor/descendant pair. -/
def admissibleClaims (xs : List Nat) : Bool :=
  !(xs.isEmpty) &&
    xs.all (fun index => decide (1 < index)) &&
    uniqueClaims xs && unrelatedClaims xs

/-- Actual helper-index dispatcher. Indices name the *positions* of the
    external proof nodes; no supplied hash or root is trusted or checked. -/
def helperIndices (xs : List Nat) : Option (List Nat) :=
  if admissibleClaims xs then
    let paths := (xs.map pathIndices).flatten
    let branches := (xs.map branchIndices).flatten
    let helpers := (branches.filter (fun index => !(paths.contains index))).eraseDups
    some (helpers.mergeSort (fun a b => decide (a > b)))
  else none

/-- Runtime work-budget wrapper. Caps are caller-supplied policy values,
    not SSZ protocol constants. Reject before constructing path lists.
    Capping depth bounds each branch list, and capping the claim count
    bounds the number of branch lists to be enumerated. -/
def checkedHelpers (maxClaims maxDepth : Nat) (xs : List Nat) :
    Option (List Nat) :=
  if xs.length ≤ maxClaims then
    if xs.all (fun index => decide (depth index ≤ maxDepth)) then
      helperIndices xs
    else none
  else none

/-- Says: the executable branch list is the siblings of the executable path.
    Does not say: the named nodes exist in any concrete SSZ layout. -/
theorem branchIndices_path (index : Nat) :
    branchIndices index = (pathIndices index).map sibling := by
  rfl

/-- Says: branch enumeration has precisely generalized-index depth elements.
    Does not say: any hash is computed, or that depth is cheap on unbounded Nat. -/
theorem branchIndices_length (index : Nat) :
    (branchIndices index).length = depth index := by
  simp [branchIndices, pathIndices]

/-- Says: rejecting the input policy forces the actual multiproof helper
    dispatcher to return none. Does not say: an accepted set is authenticated. -/
theorem helperIndices_refuses_invalid (xs : List Nat)
    (h : admissibleClaims xs = false) :
    helperIndices xs = none := by
  simp [helperIndices, h]

/-- Says: an admitted request reaches the actual helper enumeration.
    Does not say: the resulting indices carry valid SSZ hashes. -/
theorem helperIndices_of_admissible (xs : List Nat)
    (h : admissibleClaims xs = true) :
    ∃ helpers, helperIndices xs = some helpers := by
  let paths := (xs.map pathIndices).flatten
  let branches := (xs.map branchIndices).flatten
  let helpers := (branches.filter (fun index => !(paths.contains index))).eraseDups
  refine ⟨helpers.mergeSort (fun a b => decide (a > b)), ?_⟩
  simp [helperIndices, h, paths, branches, helpers]

/-- Says: a request beyond the explicit claim limit is refused before
    building helper paths. Does not say: the cap is a consensus constant. -/
theorem checkedHelpers_refuses_over_claim_cap
    (maxClaims maxDepth : Nat) (xs : List Nat)
    (h : maxClaims < xs.length) :
    checkedHelpers maxClaims maxDepth xs = none := by
  have hbad : ¬ xs.length ≤ maxClaims := by omega
  simp [checkedHelpers, hbad]

/-- Says: an out-of-budget depth is refused by the executable wrapper.
    Does not say: admitted indices are valid fields of SSZ container types. -/
theorem checkedHelpers_refuses_over_depth_cap
    (maxClaims maxDepth : Nat) (xs : List Nat)
    (h : xs.all (fun i => decide (depth i ≤ maxDepth)) = false) :
    checkedHelpers maxClaims maxDepth xs = none := by
  by_cases hsize : xs.length ≤ maxClaims
  · simp [checkedHelpers, hsize, h]
  · simp [checkedHelpers, hsize]

/-- Says: within the stated resource limits the wrapper delegates to the
    real helper dispatcher without changing it. No cryptographic refinement. -/
theorem checkedHelpers_within_limits
    (maxClaims maxDepth : Nat) (xs : List Nat)
    (hsize : xs.length ≤ maxClaims)
    (hdepth : xs.all (fun i => decide (depth i ≤ maxDepth)) = true) :
    checkedHelpers maxClaims maxDepth xs = helperIndices xs := by
  simp [checkedHelpers, hsize, hdepth]

/-- Says: the executable helper dispatcher refuses empty requests.
    Does not say: empty batches of other SSZ operations must be refused. -/
theorem helperIndices_empty : helperIndices [] = none := by rfl

/-- Says: multiproof proof-branch admission rejects root 1.
    Does not say: SSZ node_root(1) is invalid. -/
theorem helperIndices_root : helperIndices [1] = none := by rfl

/-- Says: two repeated node claims are refused.
    Does not say: two distinct nodes with equal *values* are invalid. -/
theorem helperIndices_duplicate : helperIndices [2, 2] = none := by rfl

/-- Says: claims at an ancestor and its child are refused by the actual
    entry. Does not say: other sets have authenticated roots. -/
theorem helperIndices_nested : helperIndices [2, 4] = none := by rfl

/-- Says: an isolated leaf needs its right sibling and its uncle.
    Does not say: these hashes are present, correct or SHA-256 digests. -/
theorem helperIndices_one_leaf : helperIndices [4] = some [5, 3] := by rfl

/-- Says: the two direct children of the root need no helper witness.
    Does not say: their claimed leaf hashes match a consensus root. -/
theorem helperIndices_root_children : helperIndices [2, 3] = some [] := by rfl

#guard helperIndices [] == none
#guard helperIndices [0] == none
#guard helperIndices [1] == none
#guard helperIndices [2, 2] == none
#guard helperIndices [2, 4] == none
#guard helperIndices [4, 5] == some [3]
#guard helperIndices [4, 6] == some [7, 5]
#guard helperIndices [4] == some [5, 3]
#guard helperIndices [2, 3] == some []
#guard checkedHelpers 1 64 [4, 5] == none
#guard checkedHelpers 4 1 [4] == none
#guard checkedHelpers 4 64 [4] == some [5, 3]
#guard checkedHelpers 4 64 [2, 3] == some []
#guard checkedHelpers 4 64 [2, 4] == none
#guard checkedHelpers 4 64 [2 ^ 65] == none

#print axioms EthereumConsensus.SSZ.branchIndices_path
#print axioms EthereumConsensus.SSZ.branchIndices_length
#print axioms EthereumConsensus.SSZ.helperIndices_refuses_invalid
#print axioms EthereumConsensus.SSZ.helperIndices_of_admissible
#print axioms EthereumConsensus.SSZ.checkedHelpers_refuses_over_claim_cap
#print axioms EthereumConsensus.SSZ.checkedHelpers_refuses_over_depth_cap
#print axioms EthereumConsensus.SSZ.checkedHelpers_within_limits
#print axioms EthereumConsensus.SSZ.helperIndices_empty
#print axioms EthereumConsensus.SSZ.helperIndices_root
#print axioms EthereumConsensus.SSZ.helperIndices_duplicate
#print axioms EthereumConsensus.SSZ.helperIndices_nested
#print axioms EthereumConsensus.SSZ.helperIndices_one_leaf
#print axioms EthereumConsensus.SSZ.helperIndices_root_children

end EthereumConsensus.SSZ
