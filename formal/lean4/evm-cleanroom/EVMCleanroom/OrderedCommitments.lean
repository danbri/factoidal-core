import EVMCleanroom.SignedTransaction

/-! Ordered execution commitments for the restricted Cancun signed runner.
    Yellow Paper appendices B/D, EIP-2718, EIP-658. No secure-key hashing:
    keys are RLP(index). No state-root or full-block acceptance claim. -/
namespace EVMCleanroom.OrderedCommitments

inductive Error where
  | resourceLimit
  | observationShape
  | transactionRootMismatch
  | receiptRootMismatch
  deriving Repr, DecidableEq

def bytesRLP (b : Array UInt8) : Array UInt8 :=
  if b.size == 1 && (b[0]?.getD 0) < 128 then b
  else SignedTransaction.rlpLengthPrefix 128 183 b.size ++ b

def listRLP (items : Array (Array UInt8)) : Array UInt8 :=
  let body := items.foldl (· ++ ·) #[]
  SignedTransaction.rlpLengthPrefix 192 247 body.size ++ body

def fixed (n width : Nat) : Array UInt8 :=
  (Array.range width).map fun i => UInt8.ofNat (n / 256^(width-1-i) % 256)

def compact (leaf : Bool) (path : Array Nat) : Array UInt8 := Id.run do
  let odd := path.size % 2
  let flag := (if leaf then 2 else 0) + odd
  let mut out := #[UInt8.ofNat (16 * flag + if odd == 1 then path[0]?.getD 0 else 0)]
  for i in [:path.size / 2] do
    let j := odd + 2*i
    out := out.push (UInt8.ofNat (16 * (path[j]?.getD 0) + (path[j+1]?.getD 0)))
  return out

def childRLP (a : Keccak.Acceptance) (encoded : Array UInt8) : Array UInt8 :=
  if encoded.size < 32 then encoded else bytesRLP (MPT.hashBytes a encoded)

abbrev Entry := Array Nat × Array UInt8

def commonPath (first : Array Nat) (rows : List Entry) : Array Nat := Id.run do
  let mut n := 0
  for i in [:first.size] do
    if rows.all (fun row => row.1[i]? == first[i]?) then n := n + 1
    else break
  return first.extract 0 n

/-- Recursion is on explicit depth fuel, not input byte length or list length.
    For the bounded ordered keys each recursive descent removes a nibble
    (or a nonempty common path). Empty subtrees use the RLP empty string. -/
def build (a : Keccak.Acceptance) : Nat → List Entry → Except Error (Array UInt8)
  | 0, _ => .error .resourceLimit
  | fuel+1, rows => do
    match rows with
    | [] => return #[0x80]
    | [row] => return listRLP #[bytesRLP (compact true row.1), bytesRLP row.2]
    | first :: _ =>
      let shared := commonPath first.1 rows
      if !shared.isEmpty then
        let child ← build a fuel (rows.map fun row => (row.1.extract shared.size row.1.size, row.2))
        return listRLP #[bytesRLP (compact false shared), childRLP a child]
      else
        let mut children : Array (Array UInt8) := #[]
        for nibble in [:16] do
          let selected := rows.filter (fun row => row.1[0]? == some nibble)
          if selected.isEmpty then children := children.push #[0x80]
          else
            let child ← build a fuel (selected.map fun row => (row.1.extract 1 row.1.size, row.2))
            children := children.push (childRLP a child)
        let terminal := (rows.find? fun row => row.1.isEmpty).map Prod.snd
        return listRLP (children.push (bytesRLP (terminal.getD #[])))

def maxCommitmentBytes : Nat := 2 * TransactionList.maxObservationBytes + 1024 * TransactionList.maxTransactions

def root (a : Keccak.Acceptance) (values : List (Array UInt8)) : Except Error (Array UInt8) := do
  if !TransactionList.countFits TransactionList.maxTransactions values ||
      values.foldl (fun n v => n + v.size) 0 > maxCommitmentBytes then throw .resourceLimit
  if values.any (·.isEmpty) then throw .observationShape
  let rows := (values.toArray.mapIdx fun i value =>
    (MPT.nibbles (SignedTransaction.encodeScalar i), value)).toList
  return MPT.hashBytes a (← build a 16 rows)

def addBloom (a : Keccak.Acceptance) (bloom value : Array UInt8) : Array UInt8 := Id.run do
  let digest := MPT.hashBytes a value
  let mut result := bloom
  for j in [:3] do
    let bit := (256 * (digest[2*j]?.getD 0).toNat + (digest[2*j+1]?.getD 0).toNat) % 2048
    let i := 255 - bit / 8
    result := result.set! i ((result[i]?.getD 0) ||| UInt8.ofNat (2^(bit%8)))
  return result

def receiptBytes (a : Keccak.Acceptance) (r : TransactionList.Receipt) : Except Error (Array UInt8) := do
  if r.kind > 3 || r.cumulativeGasUsed ≥ 2^64 then throw .observationShape
  if r.logs.foldl (fun n log => n + log.data.size + 32 * log.topics.length + 20) 0 >
      TransactionList.maxObservationBytes then throw .resourceLimit
  let mut bloom : Array UInt8 := Array.replicate 256 0
  let mut logs : Array (Array UInt8) := #[]
  for log in r.logs do
    if log.address ≥ 2^160 || log.topics.length > 4 then throw .observationShape
    let address := fixed log.address 20
    bloom := addBloom a bloom address
    let topics := log.topics.toArray.map (fun topic => fixed topic.val 32)
    for topic in topics do
      bloom := addBloom a bloom topic
    let data := (Array.range log.data.size).map log.data.readByte
    logs := logs.push (listRLP #[bytesRLP address, listRLP (topics.map bytesRLP), bytesRLP data])
  let body := listRLP #[SignedTransaction.encodeScalar (if r.receiptStatus then 1 else 0),
    SignedTransaction.encodeScalar r.cumulativeGasUsed, bytesRLP bloom, listRLP logs]
  return if r.kind == 0 then body else #[UInt8.ofNat r.kind] ++ body

structure Roots where
  transactions : Array UInt8
  receipts : Array UInt8

def compute (a : Keccak.Acceptance) (entries : List SignedTransaction.RawEntry)
    (result : TransactionList.Result) : Except Error Roots := do
  if entries.length != result.receipts.length then throw .observationShape
  let txRoot ← root a (entries.map (·.raw))
  let receipts ← result.receipts.mapM (receiptBytes a)
  let receiptRoot ← root a receipts
  return ⟨txRoot, receiptRoot⟩

structure Checked (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance)
    (parent child : HeaderRLP.Fields) (accounts : List WitnessAdmission.AccountInput)
    (entries : List SignedTransaction.RawEntry) where
  execution : TransactionList.Result
  roots : Roots
  ran : SignedTransaction.run a c parent child accounts entries = .accepted execution
  computed : compute a entries execution = .ok roots
  txMatches : roots.transactions = HeaderRLP.field child 4
  receiptMatches : roots.receipts = HeaderRLP.field child 5

inductive Refusal where
  | prior (result : TransactionList.Outcome)
  | commitment (error : Error)

/-- This is a new restricted entry, not a production block/CL verdict.
    It preserves the signed runner's refusal and authenticates neither
    the parent chain nor the final state root. -/
def run (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance)
    (parent child : HeaderRLP.Fields) (accounts : List WitnessAdmission.AccountInput)
    (entries : List SignedTransaction.RawEntry) :
    Except Refusal (Checked a c parent child accounts entries) :=
  match h : SignedTransaction.run a c parent child accounts entries with
  | .accepted execution =>
    match hc : compute a entries execution with
    | .error e => .error (.commitment e)
    | .ok roots =>
      if ht : roots.transactions = HeaderRLP.field child 4 then
        if hr : roots.receipts = HeaderRLP.field child 5 then
          .ok ⟨execution, roots, h, hc, ht, hr⟩
        else .error (.commitment .receiptRootMismatch)
      else .error (.commitment .transactionRootMismatch)
  | .rejected index why => .error (.prior (.rejected index why))
  | .indeterminate index why => .error (.prior (.indeterminate index why))

/-- Kind: checked executable linkage, conditional on the independent hash and
    current restricted execution semantics; not normative MPT refinement. -/
theorem checked_source (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance)
    (parent child : HeaderRLP.Fields) (accounts : List WitnessAdmission.AccountInput)
    (entries : List SignedTransaction.RawEntry) (out : Checked a c parent child accounts entries) :
    SignedTransaction.run a c parent child accounts entries = .accepted out.execution ∧
    compute a entries out.execution = .ok out.roots ∧
    out.roots.transactions = HeaderRLP.field child 4 ∧
    out.roots.receipts = HeaderRLP.field child 5 :=
  ⟨out.ran, out.computed, out.txMatches, out.receiptMatches⟩

theorem child_inline (a : Keccak.Acceptance) (encoded : Array UInt8) (h : encoded.size < 32) :
    childRLP a encoded = encoded := by simp only [childRLP, if_pos h]

theorem child_hash (a : Keccak.Acceptance) (encoded : Array UInt8) (h : ¬ encoded.size < 32) :
    childRLP a encoded = bytesRLP (MPT.hashBytes a encoded) := by simp only [childRLP, if_neg h]

#print axioms checked_source
#print axioms child_inline
#print axioms child_hash

end EVMCleanroom.OrderedCommitments
