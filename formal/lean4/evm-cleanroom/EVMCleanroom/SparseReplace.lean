import EVMCleanroom.MPT

/-!
# Existing secure-trie leaf replacement (#1174)

This is a sparse commitment projection, not block validation. Only a present
leaf may be replaced by a nonempty value. Preserve the original canonical RLP
fields of every ancestor except its selected child, and re-admit the new path.
Unvisited siblings are commitments, not materialised state. No insertion,
deletion, collapse, global normalisation or canonical-chain selection.
-/
namespace EVMCleanroom.SparseReplace

inductive Error where
  | witness (reason : String)
  | unsupported (reason : String)
  | resourceLimit
  | internal (reason : String)
  deriving Repr, DecidableEq

def fromMPT {α : Type} : Except MPT.Error α → Except Error α
  | .ok x => .ok x
  | .error .resourceLimit => .error .resourceLimit
  | .error (.invalidProof why) => .error (.witness why)

def fromRLP {α : Type} : Except CanonicalRLP.Error α → Except Error α
  | .ok x => .ok x
  | .error .resourceLimit => .error .resourceLimit
  | .error (.malformed why) => .error (.witness why)

/-- Internal payloads are bounded by two node-size limits, hence at most
two length octets. The outer node is separately checked before hashing. -/
private def lengthPrefix (shortBase longBase n : Nat) : Array UInt8 :=
  if n ≤ 55 then #[UInt8.ofNat (shortBase + n)]
  else if n < 256 then #[UInt8.ofNat (longBase + 1), UInt8.ofNat n]
  else #[UInt8.ofNat (longBase + 2), UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]

def encodeBytes (bytes : Array UInt8) : Array UInt8 :=
  if bytes.size == 1 && (bytes[0]?).getD 0 < 128 then bytes
  else lengthPrefix 128 183 bytes.size ++ bytes

def encodeFields (fields : Array (Array UInt8)) : Except Error (Array UInt8) := do
  let n := fields.foldl (fun acc bytes => acc + bytes.size) 0
  if n > MPT.maxNodeBytes then throw .resourceLimit
  let payload := fields.foldl (fun acc bytes => acc ++ bytes) #[]
  let encoded := lengthPrefix 192 247 n ++ payload
  if encoded.size > MPT.maxNodeBytes then throw .resourceLimit
  return encoded

/-- Exact slices of the original encoded fields; no sibling decoding, hashing
or re-encoding takes place here. The caller establishes the index bound. -/
def splice (fields : Array (Array UInt8)) (i : Nat) (child : Array UInt8) :
    Array (Array UInt8) :=
  fields.extract 0 i ++ #[child] ++ fields.extract (i+1) fields.size

/-- Kind: source preservation. Says: only the selected field is replaced,
with exact original prefix and suffix slices. Does not say: arbitrary
arrays are valid trie nodes or establish global canonicality. -/
theorem splice_preserves (fields : Array (Array UInt8)) (i : Nat) (child : Array UInt8) :
    splice fields i child =
      fields.extract 0 i ++ #[child] ++ fields.extract (i+1) fields.size := rfl

def childItem (a : Keccak.Acceptance) (encoded : Array UInt8) : Array UInt8 :=
  if encoded.size < 32 then encoded else encodeBytes (MPT.hashBytes a encoded)

structure Parent where
  fields : Array (Array UInt8)
  index : Nat

structure Collected where
  leafFields : Array (Array UInt8)
  parents : List Parent

def originalFields (encoded : Array UInt8) : Except Error (Array (Array UInt8)) := do
  let item ← fromRLP (CanonicalRLP.decode encoded)
  let fields ← fromRLP (CanonicalRLP.children item)
  return fields.map (·.encoded)

/-- Follow the existing verifier's authenticated hop and selected action.
Parents are pushed in reverse order; no sibling is resolved. -/
def collect (a : Keccak.Acceptance) (db : MPT.Database a) :
    Nat → MPT.Reference → Array Nat → List Parent → Except Error Collected
  | 0, _, _, _ => .error .resourceLimit
  | fuel+1, ref, key, parents =>
    match fromMPT (MPT.readHop a db ref key) with
    | .error e => .error e
    | .ok hop =>
      match originalFields hop.checked.bytes with
      | .error e => .error e
      | .ok fields =>
        match hop.action, hop.node with
        | .done (some _), .leaf _ _ => .ok { leafFields := fields, parents }
        | .next child remaining, .branch _ _ =>
          collect a db fuel child remaining ({ fields, index := key[0]?.getD 0 } :: parents)
        | .next child remaining, .extension _ _ =>
          collect a db fuel child remaining ({ fields, index := 1 } :: parents)
        | .done none, _ => .error (.unsupported "insertion-not-yet")
        | .done (some _), _ => .error (.unsupported "non-leaf-terminal")
        | _, _ => .error (.internal "inconsistent-hop")

structure Rebuilt where
  encoded : Array UInt8
  nodes : Array (Array UInt8)

def liftParent (a : Keccak.Acceptance) (state : Rebuilt) (parent : Parent) :
    Except Error Rebuilt :=
  if parent.index ≥ parent.fields.size then .error (.internal "parent-index")
  else
    match encodeFields (splice parent.fields parent.index (childItem a state.encoded)) with
    | .error e => .error e
    | .ok encoded => .ok { encoded, nodes := state.nodes.push encoded }

/-- Kind: executable source preservation.
Says: a successful ancestor rebuild encodes the exact original prefix and
suffix, changing only the selected child; it also appends that exact node.
Does not say: every possible ancestor is globally canonical. -/
theorem liftParent_source (a : Keccak.Acceptance) (state out : Rebuilt) (parent : Parent)
    (h : liftParent a state parent = .ok out) :
    parent.index < parent.fields.size ∧
    encodeFields (parent.fields.extract 0 parent.index ++ #[childItem a state.encoded] ++
      parent.fields.extract (parent.index+1) parent.fields.size) = .ok out.encoded ∧
    out.nodes = state.nodes.push out.encoded := by
  unfold liftParent at h
  split at h
  next _ => cases h
  next hi =>
    cases enc : encodeFields (splice parent.fields parent.index (childItem a state.encoded)) with
    | error e => simp only [enc] at h; cases h
    | ok encoded =>
      simp only [enc] at h
      cases h
      exact ⟨by omega, by simpa only [splice] using enc, rfl⟩

structure Projection where
  root : Array UInt8
  nodes : Array (Array UInt8)
  deriving Repr

def rebuild (a : Keccak.Acceptance) (path : Collected) (value : Array UInt8) :
    Except Error Projection := do
  if path.leafFields.size != 2 then throw (.internal "leaf-arity")
  let leaf ← encodeFields (splice path.leafFields 1 (encodeBytes value))
  let result ← path.parents.foldlM (liftParent a) { encoded := leaf, nodes := #[leaf] }
  return { root := MPT.hashBytes a result.encoded, nodes := result.nodes }

/-- These proofs concern the actual original and generated byte paths.
They are erased by code generation. -/
structure CheckedProjection (a : Keccak.Acceptance) (root key old value : Array UInt8)
    (proof : Array (Array UInt8)) where
  projection : Projection
  oldChecked : MPT.lookup a root key proof = .ok (some old)
  newChecked : MPT.lookup a projection.root key projection.nodes = .ok (some value)

/-- Old-value and new-value lookup are actual executable checks, not host
assertions. A new proof is returned only on success. -/
def replace (a : Keccak.Acceptance) (root key old value : Array UInt8)
    (proof : Array (Array UInt8)) :
    Except Error (CheckedProjection a root key old value proof) := do
  if old.size > MPT.maxNodeBytes || value.size > MPT.maxNodeBytes then
    throw .resourceLimit
  if value.isEmpty then throw (.unsupported "deletion-not-yet")
  match h : MPT.lookup a root key proof with
  | .error .resourceLimit => throw .resourceLimit
  | .error (.invalidProof why) => throw (.witness why)
  | .ok none => throw (.unsupported "insertion-not-yet")
  | .ok (some observed) =>
    if eq : observed = old then
      let path ← collect a (MPT.indexProof a proof) MPT.maxSteps (.hash root true) (MPT.nibbles key) []
      let projected ← rebuild a path value
      match hn : MPT.lookup a projected.root key projected.nodes with
      | .ok (some observedNew) =>
        if en : observedNew = value then
          return { projection := projected, oldChecked := by simpa only [eq] using h,
            newChecked := by simpa only [en] using hn }
        else throw (.internal "new-value-mismatch")
      | .error .resourceLimit => throw .resourceLimit
      | _ => throw (.internal "new-path-refused")
    else throw (.witness "old-value-mismatch")

/-- Kind: executable linkage.
Says: success checks the actual input and output commitments against the
exact old and replacement bytes. Does not say: unseen subtrees are canonical,
Keccak is collision resistant, or the replacement is a valid Ethereum transition. -/
theorem replace_checked (a : Keccak.Acceptance) (root key old value : Array UInt8)
    (proof : Array (Array UInt8)) (out : CheckedProjection a root key old value proof)
    (_h : replace a root key old value proof = .ok out) :
    MPT.lookup a root key proof = .ok (some old) ∧
    MPT.lookup a out.projection.root key out.projection.nodes = .ok (some value) :=
  ⟨out.oldChecked, out.newChecked⟩

/-- Kind: traversal resource refusal. Says: no fuel gives a resource result.
Does not say: local resource exhaustion implies consensus invalidity. -/
theorem collect_zero (a : Keccak.Acceptance) (db : MPT.Database a)
    (ref : MPT.Reference) (key : Array Nat) (parents : List Parent) :
    collect a db 0 ref key parents = .error .resourceLimit := rfl

#print axioms splice_preserves
#print axioms liftParent_source
#print axioms replace_checked
#print axioms collect_zero

end EVMCleanroom.SparseReplace
