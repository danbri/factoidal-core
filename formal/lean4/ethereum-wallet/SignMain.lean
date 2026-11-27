import EthereumWallet.TxSign
import Lean.Data.Json.Parser
import Lean.Data.Json.FromToJson.Basic

/-!
# `eth-wallet-sign`: build and sign transactions from JSON, and run the vector suites

A development and test tool. It signs with a key given on the command line,
which is only acceptable for published test keys and keys made for a test:
the flag is called `--test-key-hex` for that reason. It never talks to a
network and never prints a key.

Signing is not constant-time, so the signing commands refuse to run without
`--dangerously-enable-variable-time-signing` (skills/lean-risk-flags); that
flag is the only place this tool accepts the risk.

    eth-wallet-sign sign --dangerously-enable-variable-time-signing --test-key-hex <64 hex> <tx.json>
    eth-wallet-sign sign-authorization --dangerously-enable-variable-time-signing --test-key-hex <64 hex> <authorization.json>
    eth-wallet-sign tx-vectors --dangerously-enable-variable-time-signing <vectors.json> [--affine N]
    eth-wallet-sign rfc6979-vectors --dangerously-enable-variable-time-signing <bitcoinjs ecdsa.json>
    eth-wallet-sign wycheproof <ecdsa_secp256k1_sha256_p1363_test.json>
    eth-wallet-sign bench --dangerously-enable-variable-time-signing [N]

JSON only carries data here: parsing uses Lean's JSON data routines, and the
executable is linked with the plain runtime initializer (see the lakefile and
docs/designissues/2026-11-25-ethereum-runtime-boundary.md).
-/

open Lean (Json)
open EVMCleanroom
open EVMCleanroom.Precompiles (natToBE toHex ofHex?)
open EthereumWallet EthereumWallet.Secp EthereumWallet.Sign EthereumWallet.Tx
open EthereumWallet.TxSign EthereumWallet.TxDecode

namespace EthereumWallet.SignCLI

/-- The comb table, built once when this tool starts. -/
def baseTable : BaseTable := BaseTable.build ()

def riskFlag : String := "--dangerously-enable-variable-time-signing"

def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def decDigit? (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat) else none

def digits? (base : Nat) (digit : Char → Option Nat) (cs : List Char) : Option Nat :=
  if cs.isEmpty then none
  else cs.foldlM (fun acc c => (digit c).map fun d => acc * base + d) 0

/-- A quantity: `0x…` hexadecimal (leading zeros allowed) or decimal digits. -/
def quantityOfString (s : String) : Except String Nat :=
  match s.toList with
  | '0' :: 'x' :: rest =>
    match digits? 16 hexDigit? rest with
    | some n => .ok n
    | none => if rest.isEmpty then .ok 0 else .error ("bad hexadecimal quantity: " ++ s)
  | cs =>
    match digits? 10 decDigit? cs with
    | some n => .ok n
    | none => .error ("bad quantity: " ++ s)

def quantity (j : Json) : Except String Nat :=
  match j with
  | .str s => quantityOfString s
  | other => other.getNat?

def stripPrefix (s : String) : String :=
  match s.toList with
  | '0' :: 'x' :: rest => String.ofList rest
  | _ => s

def bytesOfString (s : String) : Except String ByteArray :=
  match ofHex? (stripPrefix s) with
  | some b => .ok b
  | none => .error "bad hexadecimal bytes"

def bytesOf (j : Json) : Except String ByteArray := do bytesOfString (← j.getStr?)

/-- A fixed-width value (address, storage key, hash) as a number. -/
def fixedOf (width : Nat) (j : Json) : Except String Nat := do
  let b ← bytesOf j
  if b.size != width then throw s!"expected {width} bytes"
  return bytesToNat b

def field? (j : Json) (name : String) : Option Json :=
  match j.getObjVal? name with
  | .ok v => if v.isNull then none else some v
  | .error _ => none

def firstField? (j : Json) (names : List String) : Option Json := names.findSome? (field? j)

def natField (j : Json) (names : List String) (default : Option Nat := none) : Except String Nat :=
  match firstField? j names, default with
  | some v, _ => quantity v
  | none, some d => .ok d
  | none, none => .error ("missing field: " ++ names.headD "?")

def arrayField (j : Json) (name : String) : Except String (Array Json) :=
  match field? j name with
  | some v => v.getArr?
  | none => .ok #[]

def fieldsOnly (j : Json) (allowed : List String) : Except String Unit := do
  let object ← j.getObj?
  for (name, _) in object.toList do
    if !allowed.contains name then throw ("unexpected field: " ++ name)

def parseAccessEntry (j : Json) : Except String AccessEntry := do
  fieldsOnly j ["address", "storageKeys"]
  let address ← fixedOf 20 (← j.getObjVal? "address")
  let keys ← (← arrayField j "storageKeys").mapM (fixedOf 32)
  return ⟨address, keys.toList⟩

def parseAuthorization (j : Json) : Except String Authorization := do
  fieldsOnly j ["chainId", "address", "nonce", "yParity", "v", "r", "s", "signer"]
  return {
    chainId := ← natField j ["chainId"]
    address := ← fixedOf 20 (← j.getObjVal? "address")
    nonce := ← natField j ["nonce"]
    yParity := ← natField j ["yParity", "v"]
    r := ← natField j ["r"]
    s := ← natField j ["s"] }

/-- An unsigned transaction in the field names of the JSON-RPC transaction object. -/
def parseTx (j : Json) : Except String Unsigned := do
  fieldsOnly j ["type", "chainId", "nonce", "gasPrice", "maxFeePerGas", "maxPriorityFeePerGas",
    "gas", "gasLimit", "to", "value", "input", "data", "accessList", "maxFeePerBlobGas",
    "blobVersionedHashes", "authorizationList"]
  let kind ← natField j ["type"]
  let chainId ← match field? j "chainId" with
    | some v => pure (some (← quantity v))
    | none => pure none
  let to ← match field? j "to" with
    | some (.str "") => pure none
    | some (.str "0x") => pure none
    | some v => pure (some (← fixedOf 20 v))
    | none => pure none
  let data ← match firstField? j ["input", "data"] with
    | some v => bytesOf v
    | none => pure ByteArray.empty
  return {
    kind, chainId, to
    nonce := ← natField j ["nonce"]
    maxPriorityFeePerGas := ← natField j ["maxPriorityFeePerGas"] (some 0)
    maxFeePerGas := ← natField j (if kind < 2 then ["gasPrice"] else ["maxFeePerGas"])
    gasLimit := ← natField j ["gas", "gasLimit"]
    value := ← natField j ["value"] (some 0)
    data := data.data
    accessList := (← (← arrayField j "accessList").mapM parseAccessEntry).toList
    maxFeePerBlobGas := ← natField j ["maxFeePerBlobGas"] (some 0)
    blobVersionedHashes := (← (← arrayField j "blobVersionedHashes").mapM (fixedOf 32)).toList
    authorizationList := (← (← arrayField j "authorizationList").mapM parseAuthorization).toList }

def hex0x (b : ByteArray) : String := "0x" ++ toHex b

def quantityHex (n : Nat) : String :=
  let digits := toHex (minimalBE n)
  "0x" ++ (match digits.toList with
    | [] => "0"
    | '0' :: rest => String.ofList rest
    | _ => digits)

def errorText (e : Tx.Error) : String := reprStr e

/-- A key pair from 32 bytes of hexadecimal. The text is never echoed. -/
def keyPairOf (t : BaseTable) (keyHex : String) : Except String KeyPair := do
  let b ← bytesOfString keyHex
  if b.size != 32 then throw "the test key must be 32 bytes of hexadecimal"
  match KeyPair.ofSecret t (bytesToNat b) with
  | some kp => pure kp
  | none => throw "the test key is not a valid secp256k1 scalar"

def signedJson (tx : Unsigned) (kp : KeyPair) (out : Signed) : Json :=
  Json.mkObj ([
    ("raw", .str (hex0x out.raw)),
    ("hash", .str (hex0x out.hash)),
    ("signingHash", .str (hex0x out.signingHash)),
    ("from", .str (hex0x (natToBE 20 kp.address))),
    ("yParity", .str (quantityHex out.signature.yParity)),
    ("r", .str (quantityHex out.signature.r)),
    ("s", .str (quantityHex out.signature.s))] ++
    (if tx.kind = 0 then [("v", .str (quantityHex (legacyV tx.chainId out.signature.yParity)))]
     else []))

def readJson (path : String) : IO (Except String Json) := do
  try
    let text ← IO.FS.readFile path
    pure (Json.parse text)
  catch error => pure (.error error.toString)

def fail (message : String) : IO UInt32 := do
  IO.eprintln message
  return 2

def signCommand (risk : Risk.Accepted .variableTimeSigning) (keyHex path : String) :
    IO UInt32 := do
  let t := baseTable
  match (← readJson path) >>= parseTx, keyPairOf t keyHex with
  | .error why, _ => fail ("transaction: " ++ why)
  | _, .error why => fail why
  | .ok tx, .ok kp =>
    match signTransaction risk t kp tx with
    | .error e =>
      IO.println (Json.mkObj [("error", .str (errorText e))]).compress
      return 1
    | .ok out =>
      IO.println (signedJson tx kp out).compress
      return 0

def authorizationCommand (risk : Risk.Accepted .variableTimeSigning) (keyHex path : String) :
    IO UInt32 := do
  let t := baseTable
  let file ← readJson path
  let parsed : Except String (Nat × Nat × Nat) := do
    let j ← file
    fieldsOnly j ["chainId", "address", "nonce"]
    pure (← natField j ["chainId"], ← fixedOf 20 (← j.getObjVal? "address"), ← natField j ["nonce"])
  match parsed, keyPairOf t keyHex with
  | .error why, _ => fail ("authorization: " ++ why)
  | _, .error why => fail why
  | .ok (chainId, address, nonce), .ok kp =>
    match signAuthorization risk t kp chainId address nonce with
    | .error e =>
      IO.println (Json.mkObj [("error", .str (errorText e))]).compress
      return 1
    | .ok a =>
      IO.println (Json.mkObj [
        ("chainId", .str (quantityHex a.chainId)),
        ("address", .str (hex0x (natToBE 20 a.address))),
        ("nonce", .str (quantityHex a.nonce)),
        ("yParity", .str (quantityHex a.yParity)),
        ("r", .str (quantityHex a.r)),
        ("s", .str (quantityHex a.s)),
        ("signer", .str (hex0x (natToBE 20 kp.address)))]).compress
      return 0

/-! ## Transaction signing vectors -/

structure Tally where
  matched : Nat := 0
  refusedAsFixtureExpects : Nat := 0
  controls : Nat := 0
  affineChecked : Nat := 0
  failures : Array String := #[]

def Tally.fail (tally : Tally) (why : String) : Tally :=
  { tally with failures := tally.failures.push why }

def lower (s : String) : String := String.ofList (s.toList.map Char.toLower)

/-- Sender by the affine recovery of transaction admission (`SecpRecovery`), kinds 0 to 3. -/
def affineSender (raw : ByteArray) : Option Nat :=
  match SignedTransaction.decode raw.data with
  | .error _ => none
  | .ok d =>
    match SignedTransaction.recover Keccak.dangerouslyAcceptUnverified
        SecpRecovery.dangerouslyAcceptUnverified d with
    | .ok sender => some sender
    | .error _ => none

/-- Negative controls on one signed transaction: a changed hash must not verify or recover
    the signer, a changed `s` must not verify, the high-`s` twin must be refused by the
    admission rule, and a damaged raw transaction must not decode to the same transaction. -/
def controlsHold (kp : KeyPair) (tx : Unsigned) (out : Signed) : Bool :=
  let z := bytesToNat out.signingHash
  let sig := out.signature
  let n := Precompiles.Secp256k1.n
  let damaged : ByteArray := ⟨out.raw.data.modify (out.raw.size - 1) (· ^^^ 1)⟩
  verify z sig.r sig.s (kp.x, kp.y) &&
    !verify (z + 1) sig.r sig.s (kp.x, kp.y) &&
    !verify z sig.r (sig.s % (n - 1) + 1) (kp.x, kp.y) &&
    verify z sig.r (n - sig.s) (kp.x, kp.y) &&
    !SecpRecovery.signatureBounds z (1 - sig.yParity) sig.r (n - sig.s) &&
    recoverAddress (z + 1) sig != some kp.address &&
    (match decodeBack tx.kind damaged.data with
      | .ok back => back != (tx, sig, (signingPayload tx).data)
      | .error _ => true)

def runVector (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable) (affine : Bool)
    (tally : Tally) (v : Json) : Tally :=
  let name := (v.getObjValAs? String "name").toOption.getD "?"
  let parsed : Except String (Unsigned × KeyPair × String × Bool × Bool × Option Nat) := do
    let tx ← parseTx (← v.getObjVal? "tx")
    let kp ← keyPairOf t (← (← v.getObjVal? "testKey").getStr?)
    let raw ← (← v.getObjVal? "raw").getStr?
    let exception := (field? v "fixtureExpectsException").isSome
    let mismatch := (field? v "expect") == some (.str "mismatch")
    let sender ← match field? v "sender" with
      | some s => pure (some (← fixedOf 20 s))
      | none => pure none
    pure (tx, kp, lower raw, exception, mismatch, sender)
  match parsed with
  | .error why =>
    -- A fixture marked invalid may carry fields this tool's JSON reader rejects.
    if (field? v "fixtureExpectsException").isSome then
      { tally with refusedAsFixtureExpects := tally.refusedAsFixtureExpects + 1 }
    else tally.fail (name ++ ": unreadable vector: " ++ why)
  | .ok (tx, kp, raw, exception, mismatch, sender) =>
    match signTransaction risk t kp tx with
    | .error e =>
      if exception then { tally with refusedAsFixtureExpects := tally.refusedAsFixtureExpects + 1 }
      else tally.fail (name ++ ": refused: " ++ errorText e)
    | .ok out =>
      if mismatch then
        if hex0x out.raw == raw then tally.fail (name ++ ": control vector matched")
        else { tally with controls := tally.controls + 1 }
      else if hex0x out.raw != raw then tally.fail (name ++ ": raw bytes differ")
      else if sender.isSome && sender != some kp.address then
        tally.fail (name ++ ": sender address differs")
      else if !controlsHold kp tx out then tally.fail (name ++ ": a negative control did not hold")
      else if affine && tx.kind ≤ 3 then
        if affineSender out.raw == some kp.address then
          { tally with matched := tally.matched + 1, affineChecked := tally.affineChecked + 1 }
        else tally.fail (name ++ ": affine SecpRecovery gives another sender")
      else { tally with matched := tally.matched + 1 }

def vectorLoop (risk : Risk.Accepted .variableTimeSigning) (t : BaseTable) (affineBudget : Nat)
    (vectors : Array Json) : Nat → Nat → Tally → Tally
  | 0, _, tally => tally
  | fuel+1, i, tally =>
    match vectors[i]? with
    | none => tally
    | some v =>
      vectorLoop risk t affineBudget vectors fuel (i + 1)
        (runVector risk t (decide (tally.affineChecked < affineBudget)) tally v)

def txVectorsCommand (risk : Risk.Accepted .variableTimeSigning) (path : String)
    (affineBudget : Nat) : IO UInt32 := do
  match (← readJson path) >>= fun j => arrayField j "vectors" with
  | .error why => fail ("vectors: " ++ why)
  | .ok vectors =>
    let t := baseTable
    let tally := vectorLoop risk t affineBudget vectors vectors.size 0 {}
    for line in tally.failures.extract 0 20 do IO.eprintln ("FAIL " ++ line)
    IO.println (Json.mkObj [
      ("vectors", Lean.toJson vectors.size),
      ("matched", Lean.toJson tally.matched),
      ("refusedAsFixtureExpects", Lean.toJson tally.refusedAsFixtureExpects),
      ("controlVectors", Lean.toJson tally.controls),
      ("affineRecoveryChecked", Lean.toJson tally.affineChecked),
      ("failed", Lean.toJson tally.failures.size)]).compress
    return (if tally.failures.isEmpty then 0 else 1)

/-! ## RFC 6979 vectors (bitcoinjs fixture layout, and RFC 6979 A.2.5 nonces) -/

/-- A DER ECDSA signature `30 len 02 len r 02 len s`, short lengths only. -/
def derSignature (b : ByteArray) : Option (Nat × Nat) :=
  let at' (i : Nat) : Nat := (b.data.getD i 0).toNat
  if b.size < 8 ∨ at' 0 ≠ 0x30 ∨ at' 1 + 2 ≠ b.size ∨ at' 2 ≠ 2 then none
  else
    let rLen := at' 3
    if 4 + rLen + 2 > b.size ∨ at' (4 + rLen) ≠ 2 then none
    else
      let sLen := at' (5 + rLen)
      if 6 + rLen + sLen ≠ b.size then none
      else some (bytesToNat (b.extract 4 (4 + rLen)), bytesToNat (b.extract (6 + rLen) b.size))

def nthCandidate (q : Nat) : Nat → Rfc6979.State → Nat
  | 0, st => (Rfc6979.step q st).1
  | i+1, st => nthCandidate q i (Rfc6979.step q st).2

def rfc6979Command (risk : Risk.Accepted .variableTimeSigning) (path : String) : IO UInt32 := do
  let n := Precompiles.Secp256k1.n
  match (← readJson path) with
  | .error why => fail ("vectors: " ++ why)
  | .ok doc =>
    let t := baseTable
    let mut failures : Array String := #[]
    let mut signatures := 0
    let mut candidates := 0
    let mut controls := 0
    let valid := (field? doc "valid").getD .null
    for v in (arrayField valid "ecdsa").toOption.getD #[] do
      let got : Except String Bool := do
        let d ← quantityOfString ("0x" ++ (← (← v.getObjVal? "d").getStr?))
        let k ← quantityOfString ("0x" ++ (← (← v.getObjVal? "k").getStr?))
        let recid ← (← v.getObjVal? "i").getNat?
        let message ← (← v.getObjVal? "message").getStr?
        let der ← bytesOf (← v.getObjVal? "signature")
        let hash := L4Factoidal.Crypto.sha256 message.toUTF8
        let kp ← match KeyPair.ofSecret t d with
          | some kp => pure kp
          | none => throw "key"
        let sig ← match signHash risk t kp hash with
          | .ok sig => pure sig
          | .error e => throw (reprStr e)
        pure (Rfc6979.nonce n d hash == some k && derSignature der == some (sig.r, sig.s) &&
          sig.yParity == recid && verify (bytesToNat hash) sig.r sig.s (kp.x, kp.y) &&
          !verify (bytesToNat hash + 1) sig.r sig.s (kp.x, kp.y))
      match got with
      | .ok true => signatures := signatures + 1; controls := controls + 1
      | .ok false => failures := failures.push "signature vector differs"
      | .error why => failures := failures.push ("signature vector: " ++ why)
    for v in (arrayField valid "rfc6979").toOption.getD #[] do
      let got : Except String Bool := do
        let d ← quantityOfString ("0x" ++ (← (← v.getObjVal? "d").getStr?))
        let message ← (← v.getObjVal? "message").getStr?
        let hash := L4Factoidal.Crypto.sha256 message.toUTF8
        let st := Rfc6979.init n d hash
        let k0 ← quantityOfString ("0x" ++ (← (← v.getObjVal? "k0").getStr?))
        let k1 ← quantityOfString ("0x" ++ (← (← v.getObjVal? "k1").getStr?))
        let k15 ← quantityOfString ("0x" ++ (← (← v.getObjVal? "k15").getStr?))
        pure (nthCandidate n 0 st == k0 && nthCandidate n 1 st == k1 && nthCandidate n 15 st == k15)
      match got with
      | .ok true => candidates := candidates + 3
      | .ok false => failures := failures.push "nonce candidate differs"
      | .error why => failures := failures.push ("nonce vector: " ++ why)
    -- RFC 6979 appendix A.2.5: P-256 order and key, SHA-256, messages "sample" and "test".
    let q := 0xFFFFFFFF00000000FFFFFFFFFFFFFFFFBCE6FAADA7179E84F3B9CAC2FC632551
    let x := 0xC9AFA9D845BA75166B5C215767B1D6934E50C3DB36E89B127B8A622B120F6721
    let a25 := [("sample", 0xA6E3C57DD01ABE90086538398355DD4C3B17AA873382B0F24D6129493D8AAD60),
      ("test", 0xD16B6AE827F17175E040871A1C7EC3500192C4C92677336EC2537ACAEE0008E0)]
    for (message, k) in a25 do
      if Rfc6979.nonce q x (L4Factoidal.Crypto.sha256 message.toUTF8) == some k then
        candidates := candidates + 1
      else failures := failures.push ("RFC 6979 A.2.5 nonce differs: " ++ message)
      -- Control: another message must give another nonce.
      if Rfc6979.nonce q x (L4Factoidal.Crypto.sha256 (message ++ "!").toUTF8) != some k then
        controls := controls + 1
      else failures := failures.push "RFC 6979 control"
    for line in failures do IO.eprintln ("FAIL " ++ line)
    IO.println (Json.mkObj [
      ("signatureVectors", Lean.toJson signatures),
      ("nonceCandidates", Lean.toJson candidates),
      ("controls", Lean.toJson controls),
      ("failed", Lean.toJson failures.size)]).compress
    return (if failures.isEmpty then 0 else 1)

/-! ## Wycheproof ECDSA verification vectors (P1363 signatures) -/

def wycheproofCommand (path : String) : IO UInt32 := do
  match (← readJson path) with
  | .error why => fail ("vectors: " ++ why)
  | .ok doc =>
    let mut valid := 0
    let mut invalid := 0
    let mut failures : Array String := #[]
    for group in (arrayField doc "testGroups").toOption.getD #[] do
      let key : Except String (Nat × Nat) := do
        let pk ← group.getObjVal? "publicKey"
        pure (bytesToNat (← bytesOf (← pk.getObjVal? "wx")), bytesToNat (← bytesOf (← pk.getObjVal? "wy")))
      for test in (arrayField group "tests").toOption.getD #[] do
        let got : Except String (Nat × String × Bool) := do
          let q ← key
          let id ← (← test.getObjVal? "tcId").getNat?
          let expected ← (← test.getObjVal? "result").getStr?
          let msg ← bytesOf (← test.getObjVal? "msg")
          let sig ← bytesOf (← test.getObjVal? "sig")
          let z := bytesToNat (L4Factoidal.Crypto.sha256 msg)
          let ok := sig.size == 64 &&
            verify z (bytesToNat (sig.extract 0 32)) (bytesToNat (sig.extract 32 64)) q
          pure (id, expected, ok)
        match got with
        | .error why => failures := failures.push ("unreadable test: " ++ why)
        | .ok (id, expected, ok) =>
          if expected == "valid" then
            if ok then valid := valid + 1 else failures := failures.push s!"tcId {id}: valid signature refused"
          else if expected == "invalid" then
            if ok then failures := failures.push s!"tcId {id}: invalid signature accepted" else invalid := invalid + 1
          else failures := failures.push s!"tcId {id}: unknown expected result {expected}"
    for line in failures.extract 0 20 do IO.eprintln ("FAIL " ++ line)
    IO.println (Json.mkObj [
      ("validAccepted", Lean.toJson valid),
      ("invalidRefused", Lean.toJson invalid),
      ("failed", Lean.toJson failures.size)]).compress
    return (if failures.isEmpty && valid + invalid > 0 then 0 else 1)

/-! ## Timing -/

def percentile (sorted : Array Nat) (percent : Nat) : Nat :=
  sorted.getD ((sorted.size - 1) * percent / 100) 0

def summary (label : String) (samples : Array Nat) : Json :=
  let sorted := samples.qsort (· < ·)
  Json.mkObj [("what", .str label), ("runs", Lean.toJson sorted.size),
    ("p50_us", Lean.toJson (percentile sorted 50 / 1000)),
    ("p95_us", Lean.toJson (percentile sorted 95 / 1000)),
    ("p99_us", Lean.toJson (percentile sorted 99 / 1000)),
    ("max_us", Lean.toJson (percentile sorted 100 / 1000))]

/-- Time `act` on each of `runs` inputs; the result is forced by checking it. -/
def timeEach (runs : Nat) (act : Nat → Bool) : IO (Array Nat) := do
  let mut samples : Array Nat := Array.mkEmpty runs
  let mut okAll := true
  for i in [0:runs] do
    let start ← IO.monoNanosNow
    let ok := act i
    if !ok then okAll := false
    let stop ← IO.monoNanosNow
    samples := samples.push (stop - start)
  if !okAll then IO.eprintln "bench: an operation failed"
  return samples

/-- A fresh scalar for a benchmark run: SHA-256 of a counter. Never a key of any account. -/
def benchScalar (tag i : Nat) : Nat :=
  bytesToNat (L4Factoidal.Crypto.sha256 (natToBE 8 (tag * 1000003 + i))) % (Precompiles.Secp256k1.n - 1) + 1

def benchTx (i : Nat) : Unsigned :=
  { kind := 2, chainId := some 1, nonce := i, maxPriorityFeePerGas := 1000000000,
    maxFeePerGas := 30000000000, gasLimit := 21000,
    to := some 0x3535353535353535353535353535353535353535, value := 1000000000000000 + i,
    data := #[], accessList := [], maxFeePerBlobGas := 0, blobVersionedHashes := [],
    authorizationList := [] }

/-- Signing as it would be on the code that existed before this package: the affine scalar
    multiplication of `SecpRecovery` for `[k]G`, no self-check. Returns `(r, s)`. -/
def affineSign (d z k : Nat) : Option (Nat × Nat) :=
  let n := Precompiles.Secp256k1.n
  match SecpRecovery.mul k SecpRecovery.generator with
  | some (.affine x _) =>
    let r := x % n
    some (r, (normalizeS (invFixed n k * ((z + r * d) % n) % n) 0).1)
  | _ => none

/-- The same with the shared Jacobian double-and-add `mulBase` (variable schedule). -/
def jacobianSign (d z k : Nat) : Option (Nat × Nat) :=
  let n := Precompiles.Secp256k1.n
  match Precompiles.Secp256k1.mulBase k with
  | some (x, _) =>
    let r := x % n
    some (r, (normalizeS (invFixed n k * ((z + r * d) % n) % n) 0).1)
  | none => none

def benchCommand (risk : Risk.Accepted .variableTimeSigning) (runs : Nat) : IO UInt32 := do
  let n := Precompiles.Secp256k1.n
  let t := baseTable
  let kp ← match KeyPair.ofSecret t (benchScalar 1 0) with
    | some kp => pure kp
    | none => return (← fail "bench: key")
  let hashOf (i : Nat) : ByteArray := signingHash (benchTx i)
  let nonceOf (i : Nat) : Nat := (Rfc6979.nonce n kp.secret (hashOf i)).getD 1
  let rows ← (do
    let affineRuns := min runs 20
    let a ← timeEach affineRuns fun i =>
      (affineSign kp.secret (bytesToNat (hashOf i)) (nonceOf i)).isSome
    let j ← timeEach runs fun i =>
      (jacobianSign kp.secret (bytesToNat (hashOf i)) (nonceOf i)).isSome
    let full ← timeEach runs fun i =>
      match signTransaction risk t kp (benchTx i) with
      | .ok out => out.raw.size > 0
      | .error _ => false
    let hashOnly ← timeEach runs fun i =>
      match signHash risk t kp (hashOf i) with
      | .ok sig => sig.r > 0
      | .error _ => false
    let nonce ← timeEach runs fun i => nonceOf i > 0
    let comb ← timeEach runs fun i => (mulBaseSecret t (benchScalar 2 i)).isSome
    let ladder ← timeEach runs fun i => (Precompiles.Secp256k1.mulBase (benchScalar 2 i)).isSome
    let inverse ← timeEach runs fun i => invFixed n (benchScalar 3 i) > 0
    let recover ← timeEach runs fun i =>
      match signHash risk t kp (hashOf i) with
      | .ok sig => (Precompiles.Secp256k1.recover (bytesToNat (hashOf i)) sig.yParity sig.r sig.s).isSome
      | .error _ => false
    let tableBuild ← timeEach (min runs 20) fun i =>
      (combBuild 64 Precompiles.Secp256k1.generator (Array.mkEmpty (1024 + i))).size == 1024
    let encode ← timeEach runs fun i =>
      (checkedRaw (benchTx i) ⟨benchScalar 4 i, benchScalar 5 i % (n / 2) + 1, i % 2⟩).toOption.isSome
    pure [
      summary "before: sign with the affine scalar multiplication of SecpRecovery (nonce given, no self-check)" a,
      summary "before: sign with the shared Jacobian double-and-add mulBase (nonce given, no self-check)" j,
      summary "after: signTransaction, kind 2 (validate, RFC 6979, comb, self-check recovery, encode, decode back)" full,
      summary "after: signHash (RFC 6979, comb, self-check recovery)" hashOnly,
      summary "part: RFC 6979 nonce (HMAC-SHA-256)" nonce,
      summary "part: [k]G by the comb table, affine result" comb,
      summary "part: [k]G by the shared double-and-add" ladder,
      summary "part: inverse modulo n by fixed exponent" inverse,
      summary "part: signHash followed by one more recovery" recover,
      summary "part: encode and decode back (checkedRaw)" encode,
      summary "once per process: build the comb table (1024 points)" tableBuild])
  IO.println (Json.mkObj [("rows", .arr rows.toArray)]).pretty
  return 0

def usage : String :=
  "usage: eth-wallet-sign sign|sign-authorization " ++ riskFlag ++ " --test-key-hex <64 hex> <file.json>\n" ++
  "       eth-wallet-sign tx-vectors " ++ riskFlag ++ " <vectors.json> [--affine N]\n" ++
  "       eth-wallet-sign rfc6979-vectors " ++ riskFlag ++ " <ecdsa.json>\n" ++
  "       eth-wallet-sign wycheproof <p1363 vectors.json>\n" ++
  "       eth-wallet-sign bench " ++ riskFlag ++ " [runs]\n" ++
  "Signing here is not constant-time; use test keys only. Nothing is sent to any network."

/-- The one place this tool accepts the timing risk: the flag given by the person running it. -/
def withRisk (args : List String)
    (run : Risk.Accepted .variableTimeSigning → List String → IO UInt32) : IO UInt32 :=
  if args.contains riskFlag then
    run (Risk.dangerouslyAccept .variableTimeSigning) (args.filter (· != riskFlag))
  else fail ("refused: signing in this build is not constant-time; pass " ++ riskFlag ++
    " to accept that for a test key\n" ++ usage)

def run (args : List String) : IO UInt32 :=
  match args with
  | "sign" :: rest => withRisk rest fun risk rest =>
    match rest with
    | ["--test-key-hex", key, path] => do
      IO.eprintln ("warning: variable-time signing enabled (" ++ riskFlag ++ ")")
      signCommand risk key path
    | _ => fail usage
  | "sign-authorization" :: rest => withRisk rest fun risk rest =>
    match rest with
    | ["--test-key-hex", key, path] => do
      IO.eprintln ("warning: variable-time signing enabled (" ++ riskFlag ++ ")")
      authorizationCommand risk key path
    | _ => fail usage
  | "tx-vectors" :: rest => withRisk rest fun risk rest =>
    match rest with
    | [path] => txVectorsCommand risk path 0
    | [path, "--affine", count] => txVectorsCommand risk path (count.toNat?.getD 0)
    | _ => fail usage
  | "rfc6979-vectors" :: rest => withRisk rest fun risk rest =>
    match rest with
    | [path] => rfc6979Command risk path
    | _ => fail usage
  | ["wycheproof", path] => wycheproofCommand path
  | "bench" :: rest => withRisk rest fun risk rest =>
    match rest with
    | [] => benchCommand risk 200
    | [runs] => benchCommand risk (runs.toNat?.getD 200)
    | _ => fail usage
  | _ => fail usage

end EthereumWallet.SignCLI

def main (args : List String) : IO UInt32 := EthereumWallet.SignCLI.run args
