import EVMCleanroom.CanonicalRLP
import EVMCleanroom.MPT
import EVMCleanroom.TransactionList

/-!
# State witnesses derived from Merkle Patricia proofs

Only addresses, code bytes and requested storage keys are supplied as claims.
Nonce, balance, account presence and storage values are derived from authenticated
trie leaves. Authentication is relative to the supplied state commitment, using
the existing explicitly accepted experimental Keccak implementation. It does not
establish canonical-chain membership, transaction signatures or a post-state root.
-/
namespace EVMCleanroom.WitnessAdmission

open CallTransaction

structure StorageInput where
  key : Nat
  proof : Array (Array UInt8)
  deriving Repr

structure AccountInput where
  address : Nat
  code : Array UInt8
  accountProof : Array (Array UInt8)
  storage : List StorageInput
  deriving Repr

inductive Error where
  | invalidWitness (reason : String)
  | resourceLimit
  | unsupported (reason : String)
  deriving Repr, DecidableEq

def Error.reason : Error → String
  | .invalidWitness reason => reason
  | .resourceLimit => "state-witness-resource-limit"
  | .unsupported reason => reason

def Error.category : Error → String
  | .invalidWitness _ => "invalidWitness"
  | .resourceLimit => "resourceLimit"
  | .unsupported _ => "unsupported"

def Error.unavailable : Error → Unavailable
  | .invalidWitness reason => .unsupported ("state-witness: " ++ reason)
  | .resourceLimit => .frame .resourceLimit
  | .unsupported reason => .unsupported reason

def maxWitnessBytes : Nat := 16777216
def maxWitnessNodes : Nat := 65536
def maxWitnessSlots : Nat := 16384
def maxCodeBytes : Nat := 1048576

structure Budget where
  bytes : Nat := 0
  nodes : Nat := 0
  slots : Nat := 0
  deriving Repr, DecidableEq

/-- Byte accounting precedes any hash or RLP traversal. -/
def addBytes (budget : Budget) (amount : Nat) : Except Error Budget :=
  if budget.bytes + amount > maxWitnessBytes then .error .resourceLimit
  else .ok { budget with bytes := budget.bytes + amount }

def scanNode (budget : Budget) (node : Array UInt8) : Except Error Budget :=
  if node.size > MPT.maxNodeBytes || budget.nodes ≥ maxWitnessNodes then
    .error .resourceLimit
  else addBytes { budget with nodes := budget.nodes + 1 } node.size

def scanProof (budget : Budget) (proof : Array (Array UInt8)) : Except Error Budget :=
  if proof.size > MPT.maxProofNodes then .error .resourceLimit
  else proof.foldlM scanNode budget

/-- The local count decreases before each requested slot; the shared counter
also limits the total across all accounts. No proof hashing occurs here. -/
def scanSlots : Nat → List StorageInput → Budget → Except Error Budget
  | _, [], budget => .ok budget
  | 0, _ :: _, _ => .error .resourceLimit
  | fuel + 1, slot :: rest, budget =>
    if budget.slots ≥ maxWitnessSlots then .error .resourceLimit
    else
      match scanProof { budget with slots := budget.slots + 1 } slot.proof with
      | .error error => .error error
      | .ok next => scanSlots fuel rest next

def scanAccounts : Nat → List AccountInput → Budget → Except Error Budget
  | _, [], budget => .ok budget
  | 0, _ :: _, _ => .error .resourceLimit
  | fuel + 1, account :: rest, budget =>
    if account.code.size > maxCodeBytes then .error .resourceLimit
    else
      match addBytes budget account.code.size with
      | .error error => .error error
      | .ok withCode =>
        match scanProof withCode account.accountProof with
        | .error error => .error error
        | .ok withAccount =>
          match scanSlots maxKeysPerAccount account.storage withAccount with
          | .error error => .error error
          | .ok next => scanAccounts fuel rest next

/-- All collection and aggregate budgets pass before uniqueness checks and
before the first hash. Invalid witness data is not an Ethereum-invalid block. -/
def preflight (root : Array UInt8) (inputs : List AccountInput) : Except Error Unit :=
  match scanAccounts maxAccounts inputs {} with
  | .error error => .error error
  | .ok _ =>
    if root.size != 32 then .error (.invalidWitness "state-root-width")
    else if !(decide ((inputs.map (·.address)).Nodup)) then
      .error (.invalidWitness "duplicate-account")
    else if inputs.any (fun account => account.address ≥ World.addressBound) then
      .error (.invalidWitness "account-address-width")
    else if inputs.any (fun account => !(decide ((account.storage.map (·.key)).Nodup))) then
      .error (.invalidWitness "duplicate-storage-key")
    else if inputs.any (fun account => account.storage.any (fun slot => slot.key ≥ modulus)) then
      .error (.invalidWitness "storage-key-width")
    else .ok ()

private def bigEndianLoop : Nat → Nat → List UInt8 → List UInt8
  | 0, _, acc => acc
  | width + 1, value, acc =>
    bigEndianLoop width (value / 256) (UInt8.ofNat (value % 256) :: acc)

/-- Only the checked 20-byte address and 32-byte slot-key callers use this. -/
def fixedBytes (width value : Nat) : Array UInt8 :=
  (bigEndianLoop width value []).toArray

def accountKey (a : Keccak.Acceptance) (address : Nat) : Array UInt8 :=
  MPT.hashBytes a (fixedBytes 20 address)

def storageKey (a : Keccak.Acceptance) (key : Nat) : Array UInt8 :=
  MPT.hashBytes a (fixedBytes 32 key)

def fromRLP {α : Type} : Except CanonicalRLP.Error α → Except Error α
  | .error (.malformed reason) => .error (.invalidWitness ("account-storage-rlp: " ++ reason))
  | .error .resourceLimit => .error .resourceLimit
  | .ok value => .ok value

def fromMPT {α : Type} : Except MPT.Error α → Except Error α
  | .error (.invalidProof reason) => .error (.invalidWitness ("trie-proof: " ++ reason))
  | .error .resourceLimit => .error .resourceLimit
  | .ok value => .ok value

structure AccountLeaf where
  nonce : Nat
  balance : Nat
  storageRoot : Array UInt8
  codeHash : Array UInt8
  deriving Repr

/-- Ethereum account leaves contain exactly four byte strings. Scalar zero is
the empty string; integer widths here are the admitted execution profile's. -/
def readAccount (raw : Array UInt8) : Except Error AccountLeaf := do
  let node ← fromRLP (CanonicalRLP.decode raw)
  let fields ← fromRLP (CanonicalRLP.children node)
  match fields.toList with
  | [nonce, balance, storageRoot, codeHash] =>
    let n ← fromRLP (CanonicalRLP.scalar nonce 8)
    let b ← fromRLP (CanonicalRLP.scalar balance 32)
    if storageRoot.isList || storageRoot.payload.size != 32 then
      throw (.invalidWitness "storage-root-width")
    if codeHash.isList || codeHash.payload.size != 32 then
      throw (.invalidWitness "code-hash-width")
    return {
      nonce := n
      balance := b
      storageRoot := storageRoot.payload
      codeHash := codeHash.payload }
  | _ => throw (.invalidWitness "account-field-count")

/-- A present Ethereum storage leaf is a nonzero, minimally encoded word.
The zero value is obtained from authenticated nonmembership instead. -/
def readStorage (raw : Array UInt8) : Except Error Nat := do
  let item ← fromRLP (CanonicalRLP.decode raw)
  let value ← fromRLP (CanonicalRLP.scalar item 32)
  if value = 0 then throw (.invalidWitness "present-zero-storage")
  return value

def storageFromProof (slot : StorageInput) (value : Option (Array UInt8)) :
    Except Error Slot :=
  match value with
  | none => .ok { key := slot.key, value := 0 }
  | some raw =>
    match readStorage raw with
    | .error error => .error error
    | .ok value => .ok { key := slot.key, value }

def admitStorage (a : Keccak.Acceptance) (root : Array UInt8) (slot : StorageInput) :
    Except Error Slot :=
  match fromMPT (MPT.lookup a root (storageKey a slot.key) slot.proof) with
  | .error error => .error error
  | .ok value => storageFromProof slot value

def storageLoop (a : Keccak.Acceptance) (root : Array UInt8) :
    List StorageInput → List Slot → Except Error (List Slot)
  | [], acc => .ok acc.reverse
  | slot :: rest, acc =>
    match admitStorage a root slot with
    | .error error => .error error
    | .ok value => storageLoop a root rest (value :: acc)

def admitStorageList (a : Keccak.Acceptance) (root : Array UInt8)
    (slots : List StorageInput) : Except Error (List Slot) :=
  storageLoop a root slots []

def accountFromLeaf (input : AccountInput) (leaf : AccountLeaf)
    (storage : List Slot) : WitnessAccount :=
  { address := input.address, present := true, nonce := leaf.nonce,
    balance := leaf.balance, code := input.code, storage }

/-- Code and storage are checked against commitments from the authenticated
account leaf. No separately supplied balance, nonce or slot value is consumed. -/
def checkedAccount (a : Keccak.Acceptance) (input : AccountInput) (leaf : AccountLeaf) :
    Except Error WitnessAccount :=
  if MPT.hashBytes a input.code = leaf.codeHash then
    match admitStorageList a leaf.storageRoot input.storage with
    | .error error => .error error
    | .ok storage => .ok (accountFromLeaf input leaf storage)
  else .error (.invalidWitness "code-hash-mismatch")

def accountFromProof (a : Keccak.Acceptance) (input : AccountInput)
    (value : Option (Array UInt8)) : Except Error WitnessAccount :=
  match value with
  | none =>
    if !input.code.isEmpty then .error (.invalidWitness "absent-account-has-code")
    else if !input.storage.isEmpty then .error (.unsupported "absent-account-storage-request")
    else .ok {
      address := input.address
      present := false
      balance := 0
      nonce := 0
      code := #[]
      storage := [] }
  | some raw =>
    match readAccount raw with
    | .error error => .error error
    | .ok leaf => checkedAccount a input leaf

def admitAccount (a : Keccak.Acceptance) (root : Array UInt8) (input : AccountInput) :
    Except Error WitnessAccount :=
  match fromMPT (MPT.lookup a root (accountKey a input.address) input.accountProof) with
  | .error error => .error error
  | .ok value => accountFromProof a input value

def accountLoop (a : Keccak.Acceptance) (root : Array UInt8) :
    List AccountInput → List WitnessAccount → Except Error (List WitnessAccount)
  | [], acc => .ok acc.reverse
  | input :: rest, acc =>
    match admitAccount a root input with
    | .error error => .error error
    | .ok value => accountLoop a root rest (value :: acc)

/-- The public admission entry. Collection budgets, widths and uniqueness are
checked before any account, code or storage hash is evaluated. -/
def admit (a : Keccak.Acceptance) (root : Array UInt8) (inputs : List AccountInput) :
    Except Error (List WitnessAccount) :=
  match preflight root inputs with
  | .error error => .error error
  | .ok () => accountLoop a root inputs []

def withWitnesses (input : TransactionList.Input) (witnesses : List WitnessAccount) :
    TransactionList.Input := { input with initialWitnesses := witnesses }

/-- The older executor does not represent present-but-empty accounts. Preserve
authenticated presence and refuse that execution profile; do not invent absence. -/
def hasUnusableEmptyAccount (witnesses : List WitnessAccount) : Bool :=
  witnesses.any (fun witness => witness.present && !CallValue.accountAlive witness.account)

/-- The actual transaction-list entry obtains its only starting inventory from
proofs under field 3 of the very parent header consumed by TransactionList.run.
Its decoded transaction signatures and canonical-chain membership remain open. -/
def runAuthenticated (a : Keccak.Acceptance) (input : TransactionList.Input)
    (accounts : List AccountInput) : TransactionList.Outcome :=
  match admit a (HeaderRLP.field input.parent 3) accounts with
  | .error error => .indeterminate none error.unavailable
  | .ok witnesses =>
    if hasUnusableEmptyAccount witnesses then
      .indeterminate none (.unsupported "authenticated-empty-account-profile")
    else TransactionList.run a (withWitnesses input witnesses)

end EVMCleanroom.WitnessAdmission
