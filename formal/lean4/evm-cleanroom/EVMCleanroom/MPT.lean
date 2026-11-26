import EVMCleanroom.CanonicalRLP
import EVMCleanroom.Keccak

/-!
# Ethereum secure-trie proof paths

Independent implementation of the RLP/hex-prefix commitments described by the
Ethereum Yellow Paper, appendices B--D, and EIP-1186. Inputs are a 32-byte root,
an already hashed 32-byte key and a bounded bag of encoded proof nodes. Unused
or repeated nodes are charged to the resource budget, but are not evidence of
absence or an Ethereum-invalid block. Only a referenced node is decoded.

This checks a path relative to the supplied commitment. It does not establish
that the root belongs to the canonical chain, validate every unvisited subtree,
prove collision resistance, or replace the explicit experimental Keccak opt-in.
Issue: https://github.com/danbri/factoidal-core/issues/1043
-/

namespace EVMCleanroom.MPT

inductive Error where
  | invalidProof (reason : String)
  | resourceLimit
  deriving DecidableEq, Repr

def maxNodeBytes : Nat := 4096
def maxProofNodes : Nat := 128
def maxSteps : Nat := 65

/-- The caller must explicitly accept the existing unverified hash boundary. -/
def hashBytes (_ : Keccak.Acceptance) (bytes : Array UInt8) : Array UInt8 :=
  (Keccak.digest (ByteView.ofArray bytes)).toArray

def emptyRoot (a : Keccak.Acceptance) : Array UInt8 := hashBytes a #[0x80]

def nibbles (bytes : Array UInt8) : Array Nat :=
  bytes.foldl (fun out byte => (out.push (byte.toNat / 16)).push (byte.toNat % 16)) #[]

inductive Reference where
  | empty
  | hash (digest : Array UInt8) (isRoot : Bool := false)
  | inline (encoded : Array UInt8)
  deriving DecidableEq, Repr

/-- Actual commitment relation, including the non-root inline/hash cutoff. -/
def Matches (a : Keccak.Acceptance) : Reference → Array UInt8 → Prop
  | .empty, _ => False
  | .hash digest isRoot, bytes => hashBytes a bytes = digest ∧ (isRoot = true ∨ 32 ≤ bytes.size)
  | .inline encoded, bytes => bytes = encoded ∧ bytes.size < 32

/-- Hash equality is carried by each indexed entry; the proof is erased. -/
structure HashedNode (a : Keccak.Acceptance) where
  bytes : Array UInt8
  digest : Array UInt8
  hash_eq : hashBytes a bytes = digest

abbrev Database (a : Keccak.Acceptance) := List (HashedNode a)

def indexProof (a : Keccak.Acceptance) (proof : Array (Array UInt8)) : Database a :=
  proof.foldl (fun entries bytes =>
    { bytes, digest := hashBytes a bytes, hash_eq := rfl } :: entries) []

/-- A resolver cannot return arbitrary bytes under a hash reference. -/
structure CheckedNode (a : Keccak.Acceptance) (reference : Reference) where
  bytes : Array UInt8
  binding : Matches a reference bytes

def resolve (a : Keccak.Acceptance) (db : Database a) (reference : Reference) :
    Except Error (CheckedNode a reference) :=
  match reference with
  | .empty => .error (.invalidProof "empty-reference")
  | .inline encoded =>
    if h : encoded.size < 32 then .ok { bytes := encoded, binding := ⟨rfl, h⟩ }
    else .error (.invalidProof "oversized-inline-node")
  | .hash digest isRoot =>
    match db.find? (fun entry => entry.digest == digest) with
    | none => .error (.invalidProof "missing-referenced-node")
    | some entry =>
      -- Recheck the selected entry's equality explicitly. This supplies a
      -- closed proof even if the index lookup implementation is later changed.
      if hd : entry.digest = digest then
        if hs : isRoot = true ∨ 32 ≤ entry.bytes.size then
          .ok { bytes := entry.bytes, binding := ⟨entry.hash_eq.trans hd, hs⟩ }
        else .error (.invalidProof "hashed-short-child")
      else .error (.invalidProof "index-hash-mismatch")

private def rlpResult {α : Type} : Except CanonicalRLP.Error α → Except Error α
  | .ok value => .ok value
  | .error .resourceLimit => .error .resourceLimit
  | .error (.malformed why) => .error (.invalidProof ("rlp:" ++ why))

private def bytesOf (item : CanonicalRLP.Item) : Except Error (Array UInt8) :=
  if item.isList then .error (.invalidProof "expected-byte-string") else .ok item.payload

private def field (items : Array CanonicalRLP.Item) (i : Nat) : CanonicalRLP.Item :=
  items[i]?.getD { isList := false, payload := #[], encoded := #[0x80] }

def referenceOf (item : CanonicalRLP.Item) : Except Error Reference :=
  if item.isList then
    if item.encoded.size < 32 then .ok (.inline item.encoded)
    else .error (.invalidProof "oversized-inline-child")
  else if item.payload.isEmpty then .ok .empty
  else if item.payload.size = 32 then .ok (.hash item.payload false)
  else .error (.invalidProof "child-reference-width")

/-- Returns (isLeaf, unpacked path). Even paths have a zero padding nibble. -/
def compactPath (encoded : Array UInt8) : Except Error (Bool × Array Nat) := do
  if encoded.isEmpty then throw (.invalidProof "empty-compact-path")
  let first := encoded[0]?.getD 0
  let flag := first.toNat / 16
  if flag ≥ 4 then throw (.invalidProof "compact-path-flag")
  let odd := flag % 2 = 1
  if !odd && first.toNat % 16 != 0 then throw (.invalidProof "compact-path-padding")
  let tail := nibbles (encoded.extract 1 encoded.size)
  let path := if odd then #[first.toNat % 16] ++ tail else tail
  return (flag ≥ 2, path)

inductive Node where
  | branch (children : Array Reference) (value : Array UInt8)
  | extension (path : Array Nat) (child : Reference)
  | leaf (path : Array Nat) (value : Array UInt8)

/-- Canonical RLP plus the local branch/extension/leaf and reference shapes.
    Global trie normalisation and unvisited hashed subtrees are not checked. -/
def decodeNode (encoded : Array UInt8) : Except Error Node := do
  let item ← rlpResult (CanonicalRLP.decode encoded)
  let fields ← rlpResult (CanonicalRLP.children item)
  if fields.size = 17 then
    let mut children := #[]
    for i in [:16] do
      children := children.push (← referenceOf (field fields i))
    let value ← bytesOf (field fields 16)
    return .branch children value
  else if fields.size = 2 then
    let packed ← bytesOf (field fields 0)
    let (leaf, path) ← compactPath packed
    if leaf then
      let value ← bytesOf (field fields 1)
      if value.isEmpty then throw (.invalidProof "empty-leaf-value")
      return .leaf path value
    else
      if path.isEmpty then throw (.invalidProof "empty-extension-path")
      let child ← referenceOf (field fields 1)
      match child with
      | .empty => throw (.invalidProof "empty-extension-child")
      | _ => return .extension path child
  else throw (.invalidProof "node-arity")

inductive Action where
  | done (value : Option (Array UInt8))
  | next (child : Reference) (remaining : Array Nat)

def move (node : Node) (key : Array Nat) : Except Error Action :=
  match node with
  | .branch children value =>
    if key.isEmpty then .ok (.done (if value.isEmpty then none else some value))
    else
      let nibble := key[0]?.getD 0
      if nibble ≥ 16 then .error (.invalidProof "key-nibble")
      else match children[nibble]? with
        | none => .error (.invalidProof "branch-width")
        | some child => .ok (.next child (key.extract 1 key.size))
  | .leaf path value =>
    if path.size != key.size then .error (.invalidProof "secure-leaf-key-length")
    else .ok (.done (if path == key then some value else none))
  | .extension path child =>
    if path.size > key.size then .error (.invalidProof "extension-key-length")
    else if path == key.extract 0 path.size then
      .ok (.next child (key.extract path.size key.size))
    else .ok (.done none)

/-- A hop retains both commitment checking and actual decoding/selection
    equations, rather than accepting an unconnected caller-supplied node. -/
structure Hop (a : Keccak.Acceptance) (reference : Reference) (key : Array Nat) where
  checked : CheckedNode a reference
  node : Node
  decoded : decodeNode checked.bytes = .ok node
  action : Action
  selected : move node key = .ok action

def readHop (a : Keccak.Acceptance) (db : Database a) (reference : Reference) (key : Array Nat) :
    Except Error (Hop a reference key) :=
  match resolve a db reference with
  | .error why => .error why
  | .ok checked =>
    match hd : decodeNode checked.bytes with
    | .error why => .error why
    | .ok node =>
      match hs : move node key with
      | .error why => .error why
      | .ok action => .ok { checked, node, decoded := hd, action, selected := hs }

/-- Finite path evidence uses the checked bytes and decoded node at each hop.
    The relation is conditional on the repository's hash/decoder semantics;
    it is not a full refinement proof against an external Ethereum model. -/
inductive Path (a : Keccak.Acceptance) : Reference → Array Nat → Option (Array UInt8) → Prop where
  | empty (key) : Path a .empty key none
  | terminal {reference key value} (hop : Hop a reference key)
      (selected : hop.action = .done value) : Path a reference key value
  | descend {reference key child remaining value} (hop : Hop a reference key)
      (selected : hop.action = .next child remaining)
      (rest : Path a child remaining value) : Path a reference key value

/-- At most one branch nibble or a nonempty extension is consumed per descent;
    65 visits suffice for the fixed 64-nibble secure key. Exhaustion is explicit. -/
def walk (a : Keccak.Acceptance) (db : Database a) :
    (fuel : Nat) → (reference : Reference) → (key : Array Nat) →
    Except Error { value : Option (Array UInt8) // Path a reference key value }
  | 0, _, _ => .error .resourceLimit
  | fuel + 1, reference, key =>
    if h : reference = .empty then
      .ok ⟨none, by rw [h]; exact .empty key⟩
    else
      match readHop a db reference key with
      | .error why => .error why
      | .ok hop =>
        match hs : hop.action with
        | .done value => .ok ⟨value, .terminal hop hs⟩
        | .next child remaining =>
          match walk a db fuel child remaining with
          | .error why => .error why
          | .ok result => .ok ⟨result.val, .descend hop hs result.property⟩

def preflight (root key : Array UInt8) (proof : Array (Array UInt8)) : Except Error Unit :=
  if root.size != 32 || key.size != 32 then .error (.invalidProof "root-or-key-width")
  else if proof.size > maxProofNodes then .error .resourceLimit
  else if proof.any (fun node => node.size > maxNodeBytes) then .error .resourceLimit
  else .ok ()

/-- Full public proof lookup. Hashes are computed only after size admission.
    Nonmembership never follows from missing data or a failed decoder. -/
def lookup (a : Keccak.Acceptance) (root key : Array UInt8)
    (proof : Array (Array UInt8)) : Except Error (Option (Array UInt8)) :=
  match preflight root key proof with
  | .error why => .error why
  | .ok () =>
    if root = emptyRoot a then .ok none
    else
      match walk a (indexProof a proof) maxSteps (.hash root true) (nibbles key) with
      | .error why => .error why
      | .ok result => .ok result.val

/-- Kind: commitment boundary.
    Says: every resolved hash node's bytes have exactly the requested digest.
    Does not say: Keccak collision resistance or canonical-chain membership. -/
theorem checked_hash (a : Keccak.Acceptance) (digest : Array UInt8) (isRoot : Bool)
    (node : CheckedNode a (.hash digest isRoot)) : hashBytes a node.bytes = digest :=
  node.binding.1

/-- Kind: encoding boundary.
    Says: an embedded child is exactly the referenced bytes and shorter than 32.
    Does not say: all unvisited subtrees are normalised Ethereum tries. -/
theorem checked_inline (a : Keccak.Acceptance) (encoded : Array UInt8)
    (node : CheckedNode a (.inline encoded)) : node.bytes = encoded ∧ node.bytes.size < 32 :=
  node.binding

/-- Kind: resource refusal.
    Says: zero traversal fuel returns the explicit resource result on every input.
    Does not say: a resource refusal is an invalid Ethereum proof or transaction. -/
theorem walk_zero (a : Keccak.Acceptance) (db : Database a) (ref : Reference) (key : Array Nat) :
    walk a db 0 ref key = .error .resourceLimit := rfl

/-- Kind: executable path boundary.
    Says: any returned traversal value carries the checked root-to-result path.
    Does not say: the supplied commitment is a canonical Ethereum state root. -/
theorem walk_success (a : Keccak.Acceptance) (db : Database a) (fuel : Nat)
    (ref : Reference) (key : Array Nat)
    (out : { value : Option (Array UInt8) // Path a ref key value })
    (_h : walk a db fuel ref key = .ok out) : Path a ref key out.val := out.property

/-- Kind: public executable boundary.
    Says: successful public lookup passed size admission and either matched the
    empty-trie commitment or returned a checked path from the supplied root/key.
    Does not say: canonical-chain validity, collision resistance or full
    refinement of the decoder/trie model against the normative specification. -/
theorem lookup_success (a : Keccak.Acceptance) (root key : Array UInt8)
    (proof : Array (Array UInt8)) (value : Option (Array UInt8))
    (h : lookup a root key proof = .ok value) :
    preflight root key proof = .ok () ∧
      ((root = emptyRoot a ∧ value = none) ∨ Path a (.hash root true) (nibbles key) value) := by
  cases hp : preflight root key proof with
  | error error =>
    simp only [lookup, hp] at h
    cases h
  | ok u =>
    cases u
    refine ⟨rfl, ?_⟩
    by_cases hr : root = emptyRoot a
    · have hv : none = value := by simpa only [lookup, hp, if_pos hr, Except.ok.injEq] using h
      exact .inl ⟨hr, hv.symm⟩
    · cases hw : walk a (indexProof a proof) maxSteps (.hash root true) (nibbles key) with
      | error error =>
        simp only [lookup, hp, if_neg hr, hw] at h
        cases h
      | ok result =>
        have hv : result.val = value := by
          simpa only [lookup, hp, if_neg hr, hw, Except.ok.injEq] using h
        rw [← hv]
        exact .inr result.property

/-- Kind: public refusal boundary.
    Says: a rejected size/shape preflight cannot reach hashing or traversal in
    the public lookup definition and retains the exact refusal.
    Does not say: all resource use outside this Lean function is bounded. -/
theorem lookup_preflight_refused (a : Keccak.Acceptance) (root key : Array UInt8)
    (proof : Array (Array UInt8)) (error : Error)
    (h : preflight root key proof = .error error) : lookup a root key proof = .error error := by
  simp only [lookup, h]

#print axioms checked_hash
#print axioms checked_inline
#print axioms walk_zero
#print axioms walk_success
#print axioms lookup_success
#print axioms lookup_preflight_refused

end EVMCleanroom.MPT
