import EthereumConsensus.SSZ.BasicTypes

/-!
# Fixed-length uint64 SSZ vectors

An independent Lean 4 implementation of the packed SSZ Vector[N, uint64]
profile. N is an explicit type-shape witness supplied by the caller, not the
input length inferred from unchecked bytes. The local admission cap N <= 64
bounds the amount of allocation and the number of Merkle pair operations.
Unlike SSZ List, a fixed Vector does not mix its length into its root.

Normative target: ethereum/ssz-specs@4c2f08805080c6b4b12ede7bf48ad6a80229f4b1.
Tracking: factoidal-core #842 and full-client #725. This is not a general
container/list codec, nor a claim of SHA-256 specification refinement.
-/

namespace EthereumConsensus.SSZ

inductive VectorU64Error where
  | resourceLimit
  | wrongLength
  | invalidChunk
  | incompleteTree
  deriving BEq, DecidableEq, Repr

/-- A fixed-size vector's wire data is the unmodified concatenation of
    its canonical little-endian basic-value serialisations. -/
def vectorU64Wire (values : List UInt64) : ByteArray :=
  values.foldl (fun acc value => acc ++ encodeUInt64 value) ByteArray.empty

/-- A malformed fixed-length vector must be refused rather than interpreting
    absent values as zero padding. The cap is a local resource policy. -/
def checkedVectorU64Wire (declared : Nat) (values : List UInt64) :
    Except VectorU64Error ByteArray :=
  if declared = 0 ∨ 64 < declared then .error .resourceLimit
  else if values.length ≠ declared then .error .wrongLength
  else .ok (vectorU64Wire values)

/-- A packed SSZ chunk: 32 original serialised bytes, with only the final
    incomplete chunk padded on the right with zeros. -/
def vectorU64ChunkBytes (wire : ByteArray) (index : Nat) : ByteArray :=
  (List.range 32).foldl (fun out offset =>
    let pos := index * 32 + offset
    out.push (if pos < wire.size then wire[pos]! else (0 : UInt8))) ByteArray.empty

/-- Convert the explicitly enumerated leaves to width-checked SSZ chunks. -/
def vectorU64Chunks : List Nat → ByteArray →
    Except VectorU64Error (List Chunk)
  | [], _ => .ok []
  | index :: rest, wire => do
      let chunk ← match Chunk.ofBytes (vectorU64ChunkBytes wire index) with
        | .ok checked => .ok checked
        | .error _ => .error .invalidChunk
      let tail ← vectorU64Chunks rest wire
      return chunk :: tail

/-- Pair adjacent chunks in protocol left-to-right order, never a lone node. -/
def vectorU64HashLevel : List Chunk → Except VectorU64Error (List Chunk)
  | [] => .ok []
  | [_] => .error .incompleteTree
  | left :: right :: tail => do
      let rest ← vectorU64HashLevel tail
      return hashPair left right :: rest

/-- Bounded Merkle reduction. A single leaf needs no hashing and is returned
    directly; non-singleton trees must finish before fuel is exhausted. -/
def vectorU64Reduce : Nat → List Chunk → Except VectorU64Error Chunk
  | _, [root] => .ok root
  | 0, _ => .error .resourceLimit
  | fuel + 1, leaves => do
      let next ← vectorU64HashLevel leaves
      vectorU64Reduce fuel next

/-- Width of the complete binary tree, rounded up from the packed-leaf count.
    For N in 1..64, the packed count is 1..16 and this width is at most 16. -/
def vectorU64TreeWidth (declared : Nat) : Nat :=
  let packedCount := (declared + 3) / 4
  2 ^ Nat.log2 (2 * packedCount - 1)

/-- The actual fixed-vector executable: enforce exact N before constructing
    32-byte chunks, pad the binary tree with zero chunks, and hash in Lean. -/
def checkedVectorU64 (declared : Nat) (values : List UInt64) :
    Except VectorU64Error (ByteArray × Chunk) := do
  let wire ← checkedVectorU64Wire declared values
  let packedCount := (declared + 3) / 4
  let chunks ← vectorU64Chunks (List.range packedCount) wire
  let zero ← match Chunk.ofBytes (vectorU64ChunkBytes ByteArray.empty 0) with
    | .ok chunk => .ok chunk
    | .error _ => .error .invalidChunk
  let padded := chunks ++ List.replicate (vectorU64TreeWidth declared - packedCount) zero
  let root ← vectorU64Reduce 6 padded
  return (wire, root)

/-- Kind: refusal. Says: the actual wire admission rejects a zero or
    over-cap declared length. Does not say: 64 is an SSZ protocol limit. -/
theorem checkedVectorU64Wire_refuses_cap (declared : Nat) (values : List UInt64)
    (h : declared = 0 ∨ 64 < declared) :
    checkedVectorU64Wire declared values = .error .resourceLimit := by
  simp [checkedVectorU64Wire, h]

/-- Kind: refusal. Says: after passing the declared-length cap, a wrong
    number of elements cannot be serialised as a fixed vector.
    Does not say: the caller's declared shape is authenticated. -/
theorem checkedVectorU64Wire_refuses_count (declared : Nat) (values : List UInt64)
    (cap : ¬ (declared = 0 ∨ 64 < declared))
    (wrong : values.length ≠ declared) :
    checkedVectorU64Wire declared values = .error .wrongLength := by
  simp [checkedVectorU64Wire, cap, wrong]

/-- Kind: refinement. Says: admitted wire serialization is exactly the
    concatenation of the existing executable uint64 basic encoding.
    Does not say: all uint64 inputs were authenticated by a beacon state. -/
theorem checkedVectorU64Wire_exact (declared : Nat) (values : List UInt64)
    (cap : ¬ (declared = 0 ∨ 64 < declared))
    (size : values.length = declared) :
    checkedVectorU64Wire declared values = .ok (vectorU64Wire values) := by
  simp [checkedVectorU64Wire, cap, size]

/-- Kind: refusal. Says: a zero or excessive declaration cannot reach the
    public Merkle calculation, even with apparently valid input bytes.
    Does not say: JSON parsing itself is allocation-bounded. -/
theorem checkedVectorU64_refuses_cap (declared : Nat) (values : List UInt64)
    (h : declared = 0 ∨ 64 < declared) :
    checkedVectorU64 declared values = .error .resourceLimit := by
  simp [checkedVectorU64, checkedVectorU64Wire, h]

/-- Kind: structural implementation. Says: the concrete level operation
    hashes one pair in order with our existing pure Lean SHA-256-backed hashPair.
    Does not say: SHA-256 is collision resistant. -/
theorem vectorU64HashLevel_two (left right : Chunk) :
    vectorU64HashLevel [left, right] = .ok [hashPair left right] := by
  rfl

/-- Kind: structural implementation. Says: one root chunk is accepted at
    zero fuel without calculating or inventing a parent hash.
    Does not say: this root is authenticated against a checkpoint. -/
theorem vectorU64Reduce_single (fuel : Nat) (root : Chunk) :
    vectorU64Reduce fuel [root] = .ok root := by
  cases fuel <;> rfl

/-- Kind: structural implementation. Says: a two-chunk tree is hashed in
    left/right order using exactly one round. Does not say: larger trees
    are yet proved equivalent to the normative SSZ reduction. -/
theorem vectorU64Reduce_two (left right : Chunk) :
    vectorU64Reduce 1 [left, right] = .ok (hashPair left right) := by
  rfl

/-- Kind: resource bound. Says: zero fuel on an empty frontier refuses
    rather than returning a fabricated root. Does not say: fuel six is
    sufficient for every possible number of leaves. -/
theorem vectorU64Reduce_zero_empty :
    vectorU64Reduce 0 [] = .error .resourceLimit := by
  rfl

/-- Kind: refusal. Says: if the vector length is wrong inside the admitted
    range, the public root entry refuses before merkleization.
    Does not say: a well-sized vector has a trusted root. -/
theorem checkedVectorU64_refuses_count (declared : Nat) (values : List UInt64)
    (cap : ¬ (declared = 0 ∨ 64 < declared))
    (wrong : values.length ≠ declared) :
    checkedVectorU64 declared values = .error .wrongLength := by
  simp [checkedVectorU64, checkedVectorU64Wire, cap, wrong]

private def resultError (result : Except VectorU64Error α) (error : VectorU64Error) : Bool :=
  match result with
  | .error found => found == error
  | .ok _ => false

#guard resultError (checkedVectorU64 0 []) .resourceLimit
#guard resultError (checkedVectorU64 65 (List.replicate 65 0)) .resourceLimit
#guard resultError (checkedVectorU64 4 [0, 1, 2]) .wrongLength
#guard resultError (checkedVectorU64 4 [0, 1, 2, 3, 4]) .wrongLength
#guard vectorU64TreeWidth 1 == 1
#guard vectorU64TreeWidth 4 == 1
#guard vectorU64TreeWidth 5 == 2
#guard vectorU64TreeWidth 9 == 4
#guard vectorU64TreeWidth 64 == 16
#guard (checkedVectorU64 1 [255]).toOption.map (fun r => r.2.bytes.size) == some 32
#guard (checkedVectorU64 4 [0, 1, 2, 3]).toOption.map (fun r => r.2.bytes) ==
  some (vectorU64ChunkBytes (vectorU64Wire [0, 1, 2, 3]) 0)
#guard (checkedVectorU64 5 [0, 1, 2, 3, 4]).toOption.map (fun r => r.2.bytes.size) ==
  some 32

#print axioms EthereumConsensus.SSZ.checkedVectorU64Wire_refuses_cap
#print axioms EthereumConsensus.SSZ.checkedVectorU64Wire_refuses_count
#print axioms EthereumConsensus.SSZ.checkedVectorU64Wire_exact
#print axioms EthereumConsensus.SSZ.checkedVectorU64_refuses_cap
#print axioms EthereumConsensus.SSZ.vectorU64HashLevel_two
#print axioms EthereumConsensus.SSZ.vectorU64Reduce_single
#print axioms EthereumConsensus.SSZ.vectorU64Reduce_two
#print axioms EthereumConsensus.SSZ.vectorU64Reduce_zero_empty
#print axioms EthereumConsensus.SSZ.checkedVectorU64_refuses_count

end EthereumConsensus.SSZ
