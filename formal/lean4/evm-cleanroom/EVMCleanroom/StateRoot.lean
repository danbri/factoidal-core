import EVMCleanroom.MPT

/-!
# Merkle Patricia trie roots, account encoding and logs hashes

Independent Lean construction of the commitments a state test compares:
the secure state trie root over every account, each account's storage
root, and the Keccak-256 hash of the RLP list of logs. The encodings follow
the Yellow Paper appendices B (RLP), C (hex-prefix) and D (modified Merkle
Patricia trie). No other Ethereum implementation is called.

The trie builder takes key/value pairs whose keys are already in strictly
increasing byte order and pairwise distinct; `sortEntries` establishes that
order from an arbitrary list and drops later duplicates. Recursion depth is
bounded by the key length in nibbles plus one (`trieFuel`); at the bound
the builder returns `none`, a defined refusal.

Keccak is the repository's experimental sponge, gated by the same explicit
`Keccak.Acceptance` capability as every other caller.
-/

namespace EVMCleanroom.StateRoot

/-- Big-endian bytes of `x` without leading zeros; zero is the empty array. -/
def beBytes (x : Nat) : Array UInt8 :=
  let rec go : Nat → Nat → List UInt8 → List UInt8
    | 0, _, acc => acc
    | fuel + 1, v, acc => if v = 0 then acc else go fuel (v / 256) (UInt8.ofNat (v % 256) :: acc)
  (go 64 x []).toArray

/-- Fixed-width big-endian encoding (`width` bytes, high bytes dropped). -/
def fixedBytes (width x : Nat) : Array UInt8 :=
  (List.range width).toArray.map fun i => UInt8.ofNat (x / 256 ^ (width - 1 - i) % 256)

/-- RLP length prefix with the short and long bases of a string (0x80/0xb7)
    or a list (0xc0/0xf7). -/
def lengthPrefix (shortBase longBase len : Nat) : Array UInt8 :=
  if len ≤ 55 then #[UInt8.ofNat (shortBase + len)]
  else
    let size := beBytes len
    #[UInt8.ofNat (longBase + size.size)] ++ size

/-- RLP encoding of a byte string. -/
def rlpBytes (b : Array UInt8) : Array UInt8 :=
  if b.size = 1 ∧ (b[0]?).getD 0 < 0x80 then b
  else lengthPrefix 0x80 0xb7 b.size ++ b

/-- RLP encoding of an unsigned scalar (minimal big-endian bytes). -/
def rlpScalar (x : Nat) : Array UInt8 := rlpBytes (beBytes x)

/-- RLP encoding of a list whose items are already encoded. -/
def rlpList (items : List (Array UInt8)) : Array UInt8 :=
  let payload := items.foldl (· ++ ·) #[]
  lengthPrefix 0xc0 0xf7 payload.size ++ payload

/-- Hex-prefix (compact) encoding of a nibble path with its leaf flag. -/
def hexPrefix (path : List Nat) (leaf : Bool) : Array UInt8 :=
  let flag := if leaf then 2 else 0
  let rec pairs : List Nat → List UInt8
    | a :: b :: rest => UInt8.ofNat (a * 16 + b) :: pairs rest
    | [a] => [UInt8.ofNat (a * 16)]
    | [] => []
  if path.length % 2 = 1 then
    match path with
    | n :: rest => (UInt8.ofNat ((flag + 1) * 16 + n) :: pairs rest).toArray
    | [] => #[UInt8.ofNat (flag * 16)]
  else (UInt8.ofNat (flag * 16) :: pairs path).toArray

/-- Nibbles of a byte string, high nibble first. -/
def nibbles (bytes : Array UInt8) : List Nat :=
  bytes.toList.flatMap fun b => [b.toNat / 16, b.toNat % 16]

/-- Reference to a child node: inline when its encoding is shorter than 32
    bytes, otherwise the RLP string of its Keccak-256 hash. -/
def nodeRef (a : Keccak.Acceptance) (encoded : Array UInt8) : Array UInt8 :=
  if encoded.size < 32 then encoded else rlpBytes (MPT.hashBytes a encoded)

/-- Length of the common prefix of two nibble lists. -/
def commonPrefix : List Nat → List Nat → Nat
  | a :: as, b :: bs => if a = b then commonPrefix as bs + 1 else 0
  | _, _ => 0

/-- A trie entry: remaining nibble path and the stored value bytes. -/
abbrev Entry := List Nat × Array UInt8

/-- Shared prefix length of every key in a key-sorted entry list: that of
    the first and last keys. -/
def sharedPrefix (entries : List Entry) : Nat :=
  match entries, entries.getLast? with
  | e :: _ :: _, some last => commonPrefix e.1 last.1
  | _, _ => 0

/-- Encode the trie node holding `entries` (keys relative to this node,
    sorted, distinct). `none` only when the fuel is exhausted. -/
def encodeNode (a : Keccak.Acceptance) : Nat → List Entry → Option (Array UInt8)
  | _, [] => some #[0x80]
  | _, [(path, value)] => some (rlpList [rlpBytes (hexPrefix path true), rlpBytes value])
  | 0, _ :: _ :: _ => none
  | fuel + 1, entries@(_ :: _ :: _) =>
    let shared := sharedPrefix entries
    if shared > 0 then
      let first := (entries.head?.map (·.1)).getD []
      let rest := entries.map fun e => (e.1.drop shared, e.2)
      (encodeNode a fuel rest).map fun child =>
        rlpList [rlpBytes (hexPrefix (first.take shared) false), nodeRef a child]
    else
      let terminal := (entries.find? (·.1.isEmpty)).map (·.2)
      let children := (List.range 16).mapM fun n =>
        let group := entries.filterMap fun e =>
          match e.1 with
          | m :: tail => if m = n then some (tail, e.2) else none
          | [] => none
        if group.isEmpty then some (rlpBytes #[]) else (encodeNode a fuel group).map (nodeRef a)
      children.map fun refs => rlpList (refs ++ [rlpBytes (terminal.getD #[])])

/-- Insert one pair into a byte-key-sorted list, replacing an equal key. -/
def insertSorted (key : Array UInt8) (value : Array UInt8) :
    List (Array UInt8 × Array UInt8) → List (Array UInt8 × Array UInt8)
  | [] => [(key, value)]
  | (k, v) :: rest =>
    if key.toList = k.toList then (key, value) :: rest
    else if decide (key.toList < k.toList) then (key, value) :: (k, v) :: rest
    else (k, v) :: insertSorted key value rest

/-- Sort by key bytes; for repeated keys the last value wins. -/
def sortEntries (pairs : List (Array UInt8 × Array UInt8)) : List (Array UInt8 × Array UInt8) :=
  pairs.foldl (fun acc p => insertSorted p.1 p.2 acc) []

/-- Fuel that covers the longest key: two nibbles per byte plus the leaf. -/
def trieFuel (pairs : List (Array UInt8 × Array UInt8)) : Nat :=
  2 * (pairs.foldl (fun m p => max m p.1.size) 0) + 1

/-- Root hash of the trie holding `pairs` (any order; last duplicate wins). -/
def trieRoot (a : Keccak.Acceptance) (pairs : List (Array UInt8 × Array UInt8)) :
    Option (Array UInt8) :=
  let sorted := sortEntries pairs
  (encodeNode a (trieFuel sorted) (sorted.map fun p => (nibbles p.1, p.2))).map (MPT.hashBytes a)

/-- Secure trie: keys are hashed before insertion. -/
def secureRoot (a : Keccak.Acceptance) (pairs : List (Array UInt8 × Array UInt8)) :
    Option (Array UInt8) :=
  trieRoot a (pairs.map fun p => (MPT.hashBytes a p.1, p.2))

/-- One account of a post-state: storage lists only the nonzero slots. -/
structure AccountState where
  address : Nat
  nonce : Nat
  balance : Nat
  code : Array UInt8
  storage : List (Nat × Nat)

/-- EIP-161 emptiness: such an account is absent from the state trie. -/
def AccountState.empty (s : AccountState) : Bool :=
  s.nonce == 0 && s.balance == 0 && s.code.isEmpty

def storageRoot (a : Keccak.Acceptance) (slots : List (Nat × Nat)) : Option (Array UInt8) :=
  secureRoot a ((slots.filter (·.2 != 0)).map fun (k, v) => (fixedBytes 32 k, rlpScalar v))

def accountRLP (a : Keccak.Acceptance) (s : AccountState) : Option (Array UInt8) :=
  (storageRoot a s.storage).map fun root =>
    rlpList [rlpScalar s.nonce, rlpScalar s.balance, rlpBytes root, rlpBytes (MPT.hashBytes a s.code)]

/-- State root over the nonempty accounts. Storage of an empty account is
    not consulted (it cannot be in the trie). -/
def stateRoot (a : Keccak.Acceptance) (accounts : List AccountState) : Option (Array UInt8) := do
  let live := accounts.filter (fun s => !s.empty)
  let leaves ← live.mapM fun s => (accountRLP a s).map fun v => (fixedBytes 20 s.address, v)
  secureRoot a leaves

/-- One log: emitter, topics and data bytes. -/
structure Log where
  address : Nat
  topics : List Nat
  data : Array UInt8

def logRLP (l : Log) : Array UInt8 :=
  rlpList [rlpBytes (fixedBytes 20 l.address),
    rlpList (l.topics.map fun t => rlpBytes (fixedBytes 32 t)), rlpBytes l.data]

/-- The `logs` commitment of a state test: Keccak-256 of the RLP log list. -/
def logsHash (a : Keccak.Acceptance) (logs : List Log) : Array UInt8 :=
  MPT.hashBytes a (rlpList (logs.map logRLP))

/-! ## Theorems -/

/-- Kind: executable correspondence.
    Says: the builder's empty trie hashes to the same constant that the
    independent MPT proof verifier uses as the empty root.
    Does not say: that the experimental sponge computes Keccak-256. -/
theorem trieRoot_nil (a : Keccak.Acceptance) : trieRoot a [] = some (MPT.emptyRoot a) := by
  simp [trieRoot, sortEntries, encodeNode, MPT.emptyRoot]

/-- Kind: encoding rule.
    Says: a single byte below 0x80 is its own RLP encoding.
    Does not say: anything about longer strings. -/
theorem rlpBytes_single (b : UInt8) (h : b < 0x80) : rlpBytes #[b] = #[b] := by
  simp [rlpBytes, h]

/-- Kind: encoding size.
    Says: a byte string other than a single low byte, of at most 55 bytes,
    is encoded with exactly one prefix byte.
    Does not say: the size of long-string encodings. -/
theorem rlpBytes_short_size (b : Array UInt8) (hs : b.size ≤ 55)
    (hn : ¬ (b.size = 1 ∧ (b[0]?).getD 0 < 0x80)) :
    (rlpBytes b).size = b.size + 1 := by
  simp only [rlpBytes, if_neg hn, lengthPrefix, if_pos hs, Array.size_append]
  simp; omega

/-- Kind: encoding rule.
    Says: a child node whose encoding has fewer than 32 bytes is embedded
    verbatim in its parent, and a larger one is referenced by its 32-byte
    hash string.
    Does not say: that the parent's own encoding is canonical. -/
theorem nodeRef_inline (a : Keccak.Acceptance) (e : Array UInt8) (h : e.size < 32) :
    nodeRef a e = e := by simp [nodeRef, h]

theorem nodeRef_hashed (a : Keccak.Acceptance) (e : Array UInt8) (h : ¬ e.size < 32) :
    nodeRef a e = rlpBytes (MPT.hashBytes a e) := by simp [nodeRef, h]

/-- Kind: resource bound.
    Says: with no fuel, a node of two or more entries is refused (`none`)
    rather than recursing; one or zero entries never need fuel.
    Does not say: that `trieFuel` always suffices (tested, not proved). -/
theorem encodeNode_fuel_zero (a : Keccak.Acceptance) (x y : Entry) (rest : List Entry) :
    encodeNode a 0 (x :: y :: rest) = none := rfl

/-- Kind: semantic rule (EIP-161).
    Says: empty accounts contribute nothing to the state root.
    Does not say: which accounts a transaction touches. -/
theorem stateRoot_drops_empty (a : Keccak.Acceptance) (s : AccountState)
    (accounts : List AccountState) (h : s.empty = true) :
    stateRoot a (s :: accounts) = stateRoot a accounts := by
  simp [stateRoot, h]

/-- Kind: semantic rule.
    Says: zero-valued slots do not change a storage root.
    Does not say: anything about slot ordering. -/
theorem storageRoot_drops_zero (a : Keccak.Acceptance) (k : Nat) (slots : List (Nat × Nat)) :
    storageRoot a ((k, 0) :: slots) = storageRoot a slots := by
  simp [storageRoot]

#print axioms trieRoot_nil
#print axioms rlpBytes_single
#print axioms rlpBytes_short_size
#print axioms nodeRef_inline
#print axioms nodeRef_hashed
#print axioms encodeNode_fuel_zero
#print axioms stateRoot_drops_empty
#print axioms storageRoot_drops_zero

end EVMCleanroom.StateRoot
