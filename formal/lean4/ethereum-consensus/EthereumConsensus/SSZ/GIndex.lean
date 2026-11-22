import Lean

/-!
# Ethereum consensus SSZ generalized indices and proof branches

Reference: ethereum/consensus-specs, ssz/merkle-proofs.md.
Generalized indices start at root 1. A node at index i has children
2*i and 2*i+1. An odd index means the witness sibling is on the left.

This is protocol-critical *position/branch-shape* logic in Lean. The caller
supplies a pair hash: this module does NOT implement or validate SHA-256,
validate 32-byte digests, verify signed beacon data, or implement full SSZ.
In particular, a toy or compromised pair function is not cryptographic proof.
-/

namespace EthereumConsensus.SSZ

/-- Concrete generalized-index child, matching the consensus SSZ helper. -/
def child (index : Nat) (right : Bool) : Nat :=
  2 * index + if right then 1 else 0

/-- Concrete generalized-index parent. Parent of root 1 is invalid index 0. -/
def parent (index : Nat) : Nat := index / 2

/-- Concrete generalized-index sibling. Only indices >= 2 are tree children. -/
def sibling (index : Nat) : Nat :=
  if index % 2 == 0 then index + 1 else index - 1

/-- Derive a node's generalized index from a root-to-leaf path. -/
def indexForPath (path : List Bool) : Nat :=
  path.foldl child 1

/-- The number of sibling digests required by an SSZ proof. -/
def depth (index : Nat) : Nat := Nat.log2 index

/-- Structural binary-Merkle fold. The caller supplies the ordered pair hash.
    The recursion decreases the supplied sibling list, so is total. -/
def foldProof {α : Type} (pair : α → α → α)
    (leaf : α) (index : Nat) (siblings : List α) : α :=
  match siblings with
  | [] => leaf
  | peer :: rest =>
      let combined :=
        if index % 2 == 0 then pair leaf peer else pair peer leaf
      foldProof pair combined (parent index) rest

/-- Fail-closed shape admission. Index 0 and nonmatching branch length are
    rejected before any pair hash is invoked. This is not SHA-256 validation. -/
def calculate {α : Type} (pair : α → α → α)
    (leaf : α) (siblings : List α) (index : Nat) : Option α :=
  if index == 0 then none
  else if siblings.length == depth index then
    some (foldProof pair leaf index siblings)
  else none

/-- Equality check after shape admission. Trust remains in the supplied pair. -/
def verify {α : Type} [BEq α] (pair : α → α → α)
    (leaf : α) (siblings : List α) (index : Nat) (expected : α) : Bool :=
  match calculate pair leaf siblings index with
  | none => false
  | some computed => computed == expected

/-- Says: the actual parent of either generated child equals its argument.
    Does not say: zero is a valid SSZ tree index or hashes are correct. -/
theorem parent_child (n : Nat) (right : Bool) :
    parent (child n right) = n := by
  cases right <;> simp [parent, child] <;> omega

/-- Says: the actual sibling of a left child is its matching right child.
    Does not say: root 1 has a valid sibling. -/
theorem sibling_left_child (n : Nat) :
    sibling (child n false) = child n true := by
  simp [sibling, child]
  omega

/-- Says: the actual sibling of a right child is its matching left child.
    Does not say: zero is a valid generalized index. -/
theorem sibling_right_child (n : Nat) :
    sibling (child n true) = child n false := by
  simp [sibling, child]
  omega

/-- Says: a concatenated path follows the executable child function.
    Does not say: the path is a valid field path for any concrete SSZ type. -/
theorem indexForPath_append (xs ys : List Bool) :
    indexForPath (xs ++ ys) = ys.foldl child (indexForPath xs) := by
  simp [indexForPath, List.foldl_append]

/-- Says: the real calculation entry rejects generalized index zero.
    Does not say: nonzero indexes have authenticated witnesses. -/
theorem calculate_rejects_zero {α : Type} (pair : α → α → α)
    (leaf : α) (siblings : List α) :
    calculate pair leaf siblings 0 = none := by
  simp [calculate]

/-- Says: an actual calculation rejects an incorrect SSZ branch depth.
    Does not say: an admitted branch hashes to a trusted beacon root. -/
theorem calculate_rejects_wrong_depth {α : Type} (pair : α → α → α)
    (leaf : α) (siblings : List α) (index : Nat)
    (h : siblings.length ≠ depth index) :
    calculate pair leaf siblings index = none := by
  simp [calculate, h]

/-- Says: a zero-depth proof at root 1 retains the leaf.
    Does not say: this leaf is a consensus-validated root. -/
theorem calculate_root {α : Type} (pair : α → α → α) (leaf : α) :
    calculate pair leaf [] 1 = some leaf := by
  rfl

/-- Says: one left child and its right sibling use left-then-right order.
    Does not say: pair implements SHA-256. -/
theorem calculate_one_left {α : Type} (pair : α → α → α) (leaf peer : α) :
    calculate pair leaf [peer] 2 = some (pair leaf peer) := by
  rfl

/-- Says: one right child and its left sibling use left-then-right order.
    Does not say: pair implements SHA-256. -/
theorem calculate_one_right {α : Type} (pair : α → α → α) (leaf peer : α) :
    calculate pair leaf [peer] 3 = some (pair peer leaf) := by
  rfl

/-- Says: the actual verifier refuses generalized index zero.
    Does not say: positive-index proofs are cryptographically secure. -/
theorem verify_rejects_zero {α : Type} [BEq α] (pair : α → α → α)
    (leaf : α) (siblings : List α) (expected : α) :
    verify pair leaf siblings 0 expected = false := by
  simp [verify, calculate]

/- Executable vectors. The toy arithmetic pair is deliberately NOT SHA-256. -/
private def toyPair (a b : Nat) : Nat := 100 * a + b

#guard indexForPath [] == 1
#guard indexForPath [false, false] == 4
#guard indexForPath [false, true] == 5
#guard indexForPath [true, false, false] == 12
#guard parent 9 == 4
#guard sibling 9 == 8
#guard depth 9 == 3
#guard calculate toyPair 9 [8, 5, 3] 9 == some 8090503
#guard verify toyPair 9 [8, 5, 3] 9 8090503
#guard !(verify toyPair 9 [8, 5, 3] 9 8090504)
#guard calculate toyPair 9 [8, 5] 9 == none
#guard calculate toyPair 9 [] 0 == none

#print axioms EthereumConsensus.SSZ.parent_child
#print axioms EthereumConsensus.SSZ.sibling_left_child
#print axioms EthereumConsensus.SSZ.sibling_right_child
#print axioms EthereumConsensus.SSZ.indexForPath_append
#print axioms EthereumConsensus.SSZ.calculate_rejects_zero
#print axioms EthereumConsensus.SSZ.calculate_rejects_wrong_depth
#print axioms EthereumConsensus.SSZ.calculate_root
#print axioms EthereumConsensus.SSZ.calculate_one_left
#print axioms EthereumConsensus.SSZ.calculate_one_right
#print axioms EthereumConsensus.SSZ.verify_rejects_zero

end EthereumConsensus.SSZ
