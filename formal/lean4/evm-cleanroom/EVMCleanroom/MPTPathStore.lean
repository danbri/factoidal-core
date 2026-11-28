import EVMCleanroom.MPT

/-! A bounded historical node bag is not a single proof. Select only the
currently reachable path and re-admit it through the existing MPT verifier.
The store is local witness material, not a canonical chain or a state database.
-/
namespace EVMCleanroom.MPTPathStore

def maxStoreNodes : Nat := 4096

structure Store (a : Keccak.Acceptance) where
  db : MPT.Database a

def valid (s : Store a) : Bool :=
  decide (s.db.length ≤ maxStoreNodes) && s.db.all (fun node => decide (node.bytes.size ≤ MPT.maxNodeBytes))

def admit (a : Keccak.Acceptance) (nodes : Array (Array UInt8)) :
    Except MPT.Error (Store a) :=
  if nodes.size > maxStoreNodes then .error .resourceLimit
  else if nodes.any (fun node => node.size > MPT.maxNodeBytes) then .error .resourceLimit
  else .ok { db := MPT.indexProof a nodes }

def extend (a : Keccak.Acceptance) (s : Store a) (nodes : Array (Array UInt8)) :
    Except MPT.Error (Store a) :=
  if s.db.length + nodes.size > maxStoreNodes then .error .resourceLimit
  else if !valid s then .error .resourceLimit
  else if nodes.any (fun node => node.size > MPT.maxNodeBytes) then .error .resourceLimit
  else .ok { db := MPT.indexProof a nodes ++ s.db }

/-- Follow authenticated hops, preserving the actual node bytes. A missing
referenced node is an error, whereas an authenticated empty child is absence.
The public caller starts with an empty accumulator and 65 visits. -/
def collect (a : Keccak.Acceptance) (db : MPT.Database a) :
    Nat → MPT.Reference → Array Nat → Array (Array UInt8) → Except MPT.Error (Array (Array UInt8))
  | 0, _, _, _ => .error .resourceLimit
  | fuel+1, ref, key, acc =>
    match ref with
    | .empty => .ok acc
    | _ =>
      match MPT.readHop a db ref key with
      | .error why => .error why
      | .ok hop =>
        let next := acc.push hop.checked.bytes
        match hop.action with
        | .done _ => .ok next
        | .next child remaining => collect a db fuel child remaining next

structure Selected (a : Keccak.Acceptance) (root key : Array UInt8) where
  proof : Array (Array UInt8)
  value : Option (Array UInt8)
  checked : MPT.lookup a root key proof = .ok value

/-- Re-admission deliberately uses the public verifier, including its original
per-proof limit, rather than widening that limit to the store capacity. -/
def select (a : Keccak.Acceptance) (s : Store a) (root key : Array UInt8) :
    Except MPT.Error (Selected a root key) := do
  MPT.preflight root key #[]
  if !valid s then throw .resourceLimit
  let proof ← if root = MPT.emptyRoot a then pure #[]
    else collect a s.db MPT.maxSteps (.hash root true) (MPT.nibbles key) #[]
  match h : MPT.lookup a root key proof with
  | .error why => throw why
  | .ok value => return { proof, value, checked := h }

/-- Kind: executable linkage.
Says: a selected result re-admits under the exact original root and key.
Does not say: the root is canonical or the bag is a complete world state. -/
theorem select_checked (a : Keccak.Acceptance) (s : Store a) (root key : Array UInt8)
    (out : Selected a root key) (_h : select a s root key = .ok out) :
    MPT.lookup a root key out.proof = .ok out.value := out.checked

/-- Kind: resource refusal.
Says: zero traversal fuel gives an explicit resource result.
Does not say: exhaustion is a protocol-invalid block. -/
theorem collect_zero (a : Keccak.Acceptance) (db : MPT.Database a)
    (ref : MPT.Reference) (key : Array Nat) (acc : Array (Array UInt8)) :
    collect a db 0 ref key acc = .error .resourceLimit := rfl

/-- Kind: pre-hashing resource guard.
Says: an oversized bag refuses before indexing.
Does not say: the host's input allocation is bounded by this check. -/
theorem admit_oversized (a : Keccak.Acceptance) (nodes : Array (Array UInt8))
    (h : nodes.size > maxStoreNodes) : admit a nodes = .error .resourceLimit := by
  simp only [admit, if_pos h]

/-- Kind: aggregate resource refusal.
Says: extension beyond the aggregate node capacity refuses before hashing new nodes.
Does not say: all host allocation or all resource use is bounded by this theorem. -/
theorem extend_oversized (a : Keccak.Acceptance) (s : Store a) (nodes : Array (Array UInt8))
    (h : s.db.length + nodes.size > maxStoreNodes) :
    extend a s nodes = .error .resourceLimit := by
  simp only [extend, if_pos h]

#print axioms extend_oversized
#print axioms select_checked
#print axioms collect_zero
#print axioms admit_oversized

end EVMCleanroom.MPTPathStore
