import EthereumConsensus.SSZ.MultiProofHelpers
import L4Factoidal.Crypto.SHA2Theorems

/-!
# SSZ proofs over concrete 32-byte chunks

Generalised indices and helper ordering follow the SSZ proof rules used in
`CheckedBranch` and `MultiProofHelpers`. A parent is SHA-256 of the left
chunk followed by the right chunk. The expected root is supplied by the
caller. Definitions and proof obligations are recorded in factoidal-core #834.
-/

namespace EthereumConsensus.SSZ

/-- Malformed, incomplete, and out-of-budget requests are distinct from a
    computed root that differs from the expected root. -/
inductive ByteProofError where
  | resourceLimit
  | invalidIndex
  | invalidClaims
  | leafCount
  | proofLength
  | chunkWidth
  | incompleteProof
  | conflictingNode
  | parseError
  deriving BEq, DecidableEq, Repr

/-- An SSZ Merkle chunk carries its width invariant. -/
structure Chunk where
  bytes : ByteArray
  width : bytes.size = 32

/-- Check the chunk width before a byte array can be used in a proof. -/
def Chunk.ofBytes (bytes : ByteArray) : Except ByteProofError Chunk :=
  if h : bytes.size = 32 then .ok ⟨bytes, h⟩ else .error .chunkWidth

/-- SSZ's ordered hash of two chunks, using Factoidal's existing pure SHA-256. -/
def hashPair (left right : Chunk) : Chunk :=
  ⟨L4Factoidal.Crypto.sha256 (left.bytes ++ right.bytes),
   L4Factoidal.Crypto.sha256_size _⟩

/-- Maximum caller-selected proof depth and claim count. These are local
    resource limits. -/
def maxByteProofDepth : Nat := 64

def maxByteProofClaims : Nat := 64

def branchChunks (maxDepth index : Nat) (leaf : ByteArray) (proof : List ByteArray) :
    Except ByteProofError (Chunk × List Chunk) :=
  if maxByteProofDepth < maxDepth || maxDepth < depth index then
    .error .resourceLimit
  else if index ≤ 1 then .error .invalidIndex
  else if proof.length ≠ depth index then .error .proofLength
  else do
    let checkedLeaf ← Chunk.ofBytes leaf
    let checkedProof ← proof.mapM Chunk.ofBytes
    return (checkedLeaf, checkedProof)

/-- Calculate a branch root after budget, shape, and width admission. -/
def calculateByteBranch (maxDepth index : Nat) (leaf : ByteArray) (proof : List ByteArray) :
    Except ByteProofError Chunk := do
  let (checkedLeaf, checkedProof) ← branchChunks maxDepth index leaf proof
  return foldProof hashPair checkedLeaf index checkedProof

/-- A frontier is complete only when it contains exactly the root entry. -/
def frontierRoot? {α : Type} : List (Nat × α) → Option α
  | [(1, value)] => some value
  | _ => none

/-- Combine the sibling pair containing the greatest index. A successful
    step removes one entry for each child and inserts their ordered parent. -/
def reduceFrontierStep {α : Type} (pair : α → α → α) (frontier : List (Nat × α)) :
    Except ByteProofError (List (Nat × α)) :=
  let greatest := frontier.foldl (fun acc entry => max acc entry.1) 0
  let p := parent greatest
  if greatest ≤ 1 then .error .incompleteProof
  else if frontier.any (fun entry => entry.1 == p) then .error .conflictingNode
  else
    let isLeft := fun entry : Nat × α => entry.1 == child p false
    let isRight := fun entry : Nat × α => entry.1 == child p true
    match frontier.find? isLeft with
    | none => .error .incompleteProof
    | some left =>
      let rest := frontier.eraseP isLeft
      match rest.find? isRight with
      | none => .error .incompleteProof
      | some right => .ok ((p, pair left.2 right.2) :: rest.eraseP isRight)

/-- Perform at most `fuel` sibling combinations. A single entry at index 1
    is accepted even at the fuel boundary. -/
def reduceFrontier {α : Type} (pair : α → α → α) :
    Nat → List (Nat × α) → Except ByteProofError α
  | fuel, frontier =>
    match frontierRoot? frontier with
    | some root => .ok root
    | none =>
      match fuel with
      | 0 => .error .resourceLimit
      | n + 1 =>
        match reduceFrontierStep pair frontier with
        | .error err => .error err
        | .ok next => reduceFrontier pair n next

def multiFrontier (maxClaims maxDepth : Nat) (indices : List Nat)
    (leaves proof : List ByteArray) : Except ByteProofError (List (Nat × Chunk)) :=
  if maxByteProofClaims < maxClaims || maxByteProofDepth < maxDepth ||
      maxClaims < indices.length then
    .error .resourceLimit
  else if !(indices.all (fun index => decide (depth index ≤ maxDepth))) then
    .error .resourceLimit
  else
    match helperIndices indices with
    | none => .error .invalidClaims
    | some helpers =>
      if leaves.length ≠ indices.length then .error .leafCount
      else if proof.length ≠ helpers.length then .error .proofLength
      else do
        let checkedLeaves ← leaves.mapM Chunk.ofBytes
        let checkedProof ← proof.mapM Chunk.ofBytes
        return indices.zip checkedLeaves ++ helpers.zip checkedProof

/-- Calculate a multiproof root from explicit claim indices and the SSZ
    descending helper order. The checked frontier size supplies the fuel. -/
def calculateByteMulti (maxClaims maxDepth : Nat) (indices : List Nat)
    (leaves proof : List ByteArray) : Except ByteProofError Chunk := do
  let frontier ← multiFrontier maxClaims maxDepth indices leaves proof
  reduceFrontier hashPair frontier.length frontier

/-- A well-formed request yields a computed root, whether or not it matches. -/
structure ByteProofResult where
  root : Chunk
  matchesRoot : Bool

/-- Compare a computed branch root with a caller-supplied root of checked width. -/
def verifyByteBranch (maxDepth index : Nat) (leaf : ByteArray) (proof : List ByteArray)
    (expectedRoot : ByteArray) : Except ByteProofError ByteProofResult := do
  let (checkedLeaf, checkedProof) ← branchChunks maxDepth index leaf proof
  let expected ← Chunk.ofBytes expectedRoot
  let root := foldProof hashPair checkedLeaf index checkedProof
  return ⟨root, root.bytes == expected.bytes⟩

/-- Compare a computed multiproof root with a caller-supplied root of checked width. -/
def verifyByteMulti (maxClaims maxDepth : Nat) (indices : List Nat)
    (leaves proof : List ByteArray) (expectedRoot : ByteArray) :
    Except ByteProofError ByteProofResult := do
  let frontier ← multiFrontier maxClaims maxDepth indices leaves proof
  let expected ← Chunk.ofBytes expectedRoot
  let root ← reduceFrontier hashPair frontier.length frontier
  return ⟨root, root.bytes == expected.bytes⟩

end EthereumConsensus.SSZ
