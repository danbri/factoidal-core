import EVMCleanroom.SecpRecovery
import EVMCleanroom.WitnessAdmission

/-!
# Raw signed Cancun transaction admission
EIP-155, EIP-2718, EIP-2930, EIP-1559, EIP-4844 and EIP-2.
Raw bytes are the sole authority for transaction fields and sender. The
parent header is still a supplied anchor, not authenticated chain membership.
Blob sidecars, transaction trie, system prelude and creation remain open.
-/
namespace EVMCleanroom.SignedTransaction

open CanonicalRLP

inductive Failure where
  | malformed (reason : String)
  | resourceLimit
  | unsupported (reason : String)
  | invalidSignature
  | arithmeticRefusal
  deriving Repr, BEq

def fromRLP {α : Type} : Except CanonicalRLP.Error α → Except Failure α
  | .ok x => .ok x
  | .error .resourceLimit => .error .resourceLimit
  | .error (.malformed why) => .error (.malformed why)

/-- Local transport policy, not a consensus transaction-size limit. -/
def maxRawBytes : Nat := CallTransaction.maxDataBytes

def decodeRoot (raw : Array UInt8) : Except Failure Item := do
  if raw.size > maxRawBytes then throw .resourceLimit
  let h ← fromRLP (readHeader raw 0 raw.size)
  if h.stop != raw.size then throw (.malformed "trailing bytes")
  fromRLP (validateSegments raw (raw.size+1) [⟨0, raw.size, 0⟩])
  return { isList := h.isList, payload := raw.extract h.payloadStart h.stop, encoded := raw }

/-- Count cap is checked before allocating further child views. Each read
uses the already checked canonical header and containing extent. -/
def childrenLoop (raw : Array UInt8) :
    Nat → Nat → Array Item → Except Failure (Array Item)
  | 0, pos, acc => if pos == raw.size then .ok acc else .error .resourceLimit
  | fuel+1, pos, acc =>
    if pos == raw.size then .ok acc
    else
      match fromRLP (readHeader raw pos raw.size) with
      | .error e => .error e
      | .ok h => childrenLoop raw fuel h.stop
          (acc.push ⟨h.isList, raw.extract h.payloadStart h.stop, raw.extract pos h.stop⟩)

def members (item : Item) (cap : Nat) : Except Failure (Array Item) :=
  if !item.isList then .error (.malformed "expected list")
  else childrenLoop item.payload cap 0 #[]

def get (items : Array Item) (i : Nat) : Except Failure Item :=
  match items[i]? with
  | none => .error (.malformed "missing field")
  | some item => .ok item

def scalarAt (items : Array Item) (i : Nat) (width : Nat := 32) : Except Failure Nat := do
  fromRLP (CanonicalRLP.scalar (← get items i) width)

def byteString (item : Item) : Except Failure (Array UInt8) :=
  if item.isList then .error (.malformed "expected byte string") else .ok item.payload

def fixedBytes (item : Item) (width : Nat) : Except Failure (Array UInt8) := do
  let b ← byteString item
  if b.size != width then throw (.malformed "fixed byte width")
  return b

def asNat (bytes : Array UInt8) : Nat :=
  bytes.foldl (fun acc b => acc*256+b.toNat) 0

def destination (item : Item) : Except Failure (Option Nat) := do
  let b ← byteString item
  if b.isEmpty then return none
  if b.size != 20 then throw (.malformed "destination width")
  return some (asNat b)

def readAccess (item : Item) : Except Failure CallTransaction.Access := do
  let pair ← members item 3
  if pair.size != 2 then throw (.malformed "access tuple width")
  let address ← fixedBytes (← get pair 0) 20
  let keys ← members (← get pair 1) CallTransaction.maxKeysPerAccount
  let slots ← keys.mapM fun key => do
    return asNat (← fixedBytes key 32)
  return { address := asNat address, storageKeys := slots.toList }

def readAccessList (item : Item) : Except Failure (List CallTransaction.Access) := do
  let entries ← members item CallTransaction.maxAccessEntries
  let accesses ← entries.mapM readAccess
  if accesses.foldl (fun acc entry => acc + entry.storageKeys.length) 0 > 16384 then
    throw .resourceLimit
  return accesses.toList

/-- Exact prefix stripping for small unsigned integers. -/
def minimalBytes (x : Nat) : Array UInt8 :=
  let bytes := (Array.range 33).map fun i => UInt8.ofNat (x / 256^(32-i) % 256)
  let start := (Array.range 33).foldl (fun i j =>
    if i == j && (bytes[j]?).getD 1 == 0 then i+1 else i) 0
  bytes.extract start bytes.size

def prefix (shortBase longBase len : Nat) : Array UInt8 :=
  if len ≤ 55 then #[UInt8.ofNat (shortBase + len)]
  else
    let size := minimalBytes len
    #[UInt8.ofNat (longBase + size.size)] ++ size

def encodeScalar (x : Nat) : Array UInt8 :=
  let bytes := minimalBytes x
  if bytes.size == 1 && (bytes[0]?).getD 0 < 128 then bytes
  else prefix 128 183 bytes.size ++ bytes

/-- Original canonical unsigned fields are kept verbatim, including nested
access lists and leading zero address bytes. Only the outer list prefix
and EIP-155 suffix are reconstructed. -/
def signingBytes (kind : Nat) (fields : Array Item) (unsignedCount : Nat)
    (chain : Option Nat) : Array UInt8 :=
  let payload := (fields.extract 0 unsignedCount).foldl (fun acc item => acc ++ item.encoded) #[]
  let payload := if kind == 0 then
      match chain with
      | none => payload
      | some id => payload ++ encodeScalar id ++ #[0x80, 0x80]
    else payload
  let encoded := prefix 192 247 payload.size ++ payload
  if kind == 0 then encoded else #[UInt8.ofNat kind] ++ encoded

def legacyDomain (v : Nat) : Except Failure (Option Nat × Nat) :=
  if v == 27 || v == 28 then .ok (none, v-27)
  else if v ≥ 35 then .ok (some ((v-35)/2), (v-35)%2)
  else .error .invalidSignature

structure Decoded where
  kind : Nat
  chain : Option Nat
  nonce : Nat
  gasLimit : Nat
  gasPriceCap : Nat
  priorityFeeCap : Nat
  to : Option Nat
  value : Nat
  data : Array UInt8
  accessList : List CallTransaction.Access
  blob : Option TransactionList.BlobFields
  signing : Array UInt8
  parity : Nat
  r : Nat
  s : Nat

def decode (raw : Array UInt8) : Except Failure Decoded := do
  if raw.size > maxRawBytes then throw .resourceLimit
  if raw.isEmpty then throw (.malformed "empty envelope")
  let tag := (raw[0]?).getD 0
  let kind := if tag ≥ 192 then 0 else tag.toNat
  if tag < 192 && (kind < 1 || kind > 3) then
    if tag < 128 then throw (.unsupported "unknown-typed-envelope")
    else throw (.malformed "legacy-envelope-not-list")
  let root ← decodeRoot (if kind == 0 then raw else raw.extract 1 raw.size)
  let fs ← members root 15
  let expected := if kind == 0 then 9 else if kind == 1 then 11 else if kind == 2 then 12 else 14
  if fs.size != expected then throw (.malformed "signed-field-count")
  let last := expected-3
  let v ← scalarAt fs last 33
  let domain ← if kind == 0 then legacyDomain v else do
    if v > 1 then throw .invalidSignature
    let chain ← scalarAt fs 0
    pure (some chain, v)
  let gasIndex := if kind == 0 then 2 else if kind == 1 then 3 else 4
  let dest ← destination (← get fs (gasIndex+1))
  if kind == 3 && dest.isNone then throw (.malformed "blob-creation")
  let access ← if kind == 0 then pure [] else readAccessList (← get fs (gasIndex+4))
  let blob ← if kind == 3 then do
      let cap ← scalarAt fs 9
      let hashes ← members (← get fs 10) 128
      let hashes ← hashes.mapM fun hash => fixedBytes hash 32
      pure (some ({ hashes, maxFeePerBlobGas := cap } : TransactionList.BlobFields))
    else pure none
  return {
    kind, chain := domain.1, parity := domain.2, to := dest,
    nonce := ← scalarAt fs (if kind == 0 then 0 else 1),
    gasLimit := ← scalarAt fs gasIndex,
    gasPriceCap := ← scalarAt fs (gasIndex-1),
    priorityFeeCap := ← (if kind ≥ 2 then scalarAt fs 2 else pure 0),
    value := ← scalarAt fs (gasIndex+2),
    data := ← byteString (← get fs (gasIndex+3)),
    accessList := access, blob,
    signing := signingBytes kind fs last domain.1,
    r := ← scalarAt fs (last+1), s := ← scalarAt fs (last+2) }

def recover (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance) (d : Decoded) :
    Except Failure Nat :=
  match SecpRecovery.recoverAddress a c
      (Keccak.experimentalDigestWord a (ByteView.ofArray d.signing)) d.parity d.r d.s with
  | .ok sender => .ok sender
  | .error .invalidSignature => .error .invalidSignature
  | .error .arithmeticRefusal => .error .arithmeticRefusal

def entryFor (d : Decoded) (sender dest fuel : Nat) : TransactionList.Entry :=
  { tx := {
      kind := d.kind, signedChainId := d.chain, sender, to := dest,
      nonce := d.nonce, value := d.value, gasLimit := d.gasLimit,
      gasPriceCap := d.gasPriceCap, priorityFeeCap := d.priorityFeeCap,
      data := d.data, accessList := d.accessList },
    fuel, blob := d.blob }

def callEntry (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance)
    (d : Decoded) (fuel : Nat) : Except Failure TransactionList.Entry :=
  match recover a c d with
  | .error e => .error e
  | .ok sender =>
    match d.to with
    | none => .error (.unsupported "contract-creation")
    | some dest => .ok (entryFor d sender dest fuel)

structure RawEntry where
  raw : Array UInt8
  fuel : Nat

def admitEntry (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance)
    (entry : RawEntry) : Except Failure TransactionList.Entry :=
  match decode entry.raw with
  | .error e => .error e
  | .ok d => callEntry a c d entry.fuel

def failure : Failure → TransactionList.Failure
  | .resourceLimit => .indeterminate (.frame .resourceLimit)
  | .arithmeticRefusal => .indeterminate (.unsupported "secp-arithmetic-refusal")
  | .unsupported why => .indeterminate (.unsupported why)
  | .invalidSignature => .rejected "invalid-signature"
  | .malformed why => .rejected ("signed-envelope: " ++ why)

def runOne (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance)
    (input : TransactionList.Input) (fees : Nat × Nat) (cursor : TransactionList.Cursor)
    (raw : RawEntry) : Except TransactionList.Failure TransactionList.Cursor :=
  match admitEntry a c raw with
  | .error why => .error (failure why)
  | .ok entry =>
    match TransactionList.runEntry a input fees cursor.witnesses cursor.gasUsed cursor.blobGasUsed entry with
    | .error e => .error e
    | .ok transition => TransactionList.advance cursor entry transition

/-- Recover signatures in execution order, not by eagerly rejecting a later
signature ahead of an earlier failing transition. -/
def loop (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance)
    (input : TransactionList.Input) (fees : Nat × Nat) :
    TransactionList.Cursor → List RawEntry → Except TransactionList.IndexedFailure TransactionList.Cursor
  | cursor, [] => .ok cursor
  | cursor, raw :: rest =>
    match runOne a c input fees cursor raw with
    | .error e => .error { index := cursor.index, reason := e }
    | .ok next => loop a c input fees next rest

/-- Neither decoded sender nor initial account values appear in the input. -/
def run (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance)
    (parent child : HeaderRLP.Fields) (accounts : List WitnessAdmission.AccountInput)
    (entries : List RawEntry) : TransactionList.Outcome :=
  if !TransactionList.countFits TransactionList.maxTransactions entries then
    .indeterminate none (.frame .resourceLimit)
  else if entries.foldl (fun acc e => acc+e.fuel) 0 > TransactionList.maxReservedFuel ||
      entries.foldl (fun acc e => acc+e.raw.size) 0 > TransactionList.maxInputBytes then
    .indeterminate none (.frame .resourceLimit)
  else
    match WitnessAdmission.admit a (HeaderRLP.field parent 3) accounts with
    | .error error => .indeterminate none error.unavailable
    | .ok witnesses =>
      if WitnessAdmission.hasUnusableEmptyAccount witnesses then
        .indeterminate none (.unsupported "authenticated-empty-account-profile")
      else
        let input : TransactionList.Input := { parent, child, initialWitnesses := witnesses, transactions := [] }
        if entries.foldl (fun acc e => acc+e.raw.size) (TransactionList.inputBytes input) >
            TransactionList.maxInputBytes then .indeterminate none (.frame .resourceLimit)
        else
          match TransactionList.preflight input with
          | .error reason => TransactionList.refusal none reason
          | .ok () =>
            let time := HeaderRLP.readNat child 11
            if time < HeaderRLP.cancunTime || time ≥ HeaderRLP.pragueTime then
              .indeterminate none (.unsupported "outside-cancun-transaction-rules")
            else
              match HeaderRLP.checkedFeePair a parent child with
              | .error _ => .indeterminate none (.unsupported "header-pair-refused")
              | .ok fees =>
                match loop a c input fees (TransactionList.initial input) entries with
                | .error fail => TransactionList.refusal (some fail.index) fail.reason
                | .ok cursor => TransactionList.finish input cursor

/-- Kind: executable linkage.
Says: successful call admission uses the actual recovery result and nonempty destination.
Does not say: the curve or RLP algorithm refines all normative semantics. -/
theorem call_entry_source (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance)
    (d : Decoded) (fuel : Nat) (entry : TransactionList.Entry)
    (h : callEntry a c d fuel = .ok entry) :
    ∃ sender dest, recover a c d = .ok sender ∧ d.to = some dest ∧
      entry = entryFor d sender dest fuel := by
  unfold callEntry at h
  cases recovered : recover a c d with
  | error e => simp only [recovered] at h; cases h
  | ok sender =>
    simp only [recovered] at h
    cases dest : d.to with
    | none => simp only [dest] at h; cases h
    | some value =>
      simp only [dest] at h
      cases h
      exact ⟨sender, value, rfl, dest, rfl⟩

/-- Kind: execution refusal.
Says: the actual raw step propagates admission failure without calling the EVM.
Does not say: failure is necessarily consensus-invalid. -/
theorem refused_entry (a : Keccak.Acceptance) (c : SecpRecovery.Acceptance)
    (input : TransactionList.Input) (fees : Nat × Nat) (cursor : TransactionList.Cursor)
    (raw : RawEntry) (error : Failure) (h : admitEntry a c raw = .error error) :
    runOne a c input fees cursor raw = .error (failure error) := by
  simp only [runOne, h]

/-- Kind: input resource contract.
Says: a raw envelope exceeding the local cap refuses before RLP processing.
Does not say: the envelope is Ethereum-invalid. -/
theorem over_limit (raw : Array UInt8) (h : raw.size > maxRawBytes) :
    decode raw = .error .resourceLimit := by
  simp [decode, h]

#print axioms call_entry_source
#print axioms refused_entry
#print axioms over_limit

end EVMCleanroom.SignedTransaction
