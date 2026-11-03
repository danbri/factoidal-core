/-
L4Factoidal.VC.StatusList — Bitstring Status List v1.0 (W3C Recommendation
2025-05-15, https://www.w3.org/TR/vc-bitstring-status-list/; the editor's
draft of w3c/vc-bitstring-status-list at commit 7b93711e, 2026-10-21, was
read for the algorithm text).

  * §2.1 BitstringStatusListEntry: `checkEntry` — `type`, `statusPurpose`,
    `statusListIndex` (a base-10 string of a non-negative integer),
    `statusListCredential` (a URL), `statusSize` (an integer > 0, default 1),
    `statusMessage` (2^statusSize entries when statusSize > 1).
  * §2.2 BitstringStatusListCredential: `checkListCredential` — type, the
    credential subject's type `BitstringStatusList`, its `statusPurpose` and
    `encodedList`.
  * §3.1 Generate / §3.3 Bitstring Generation: `generate` — a bitstring of at
    least 16KB (131,072 bits), GZIP (RFC 1952, `Codec.gzip`), Multibase
    base64url with no padding (`u` prefix, `JOSE.Base64Url`).
  * §3.4 Bitstring Expansion: `expand` — the reverse.
  * §3.2 Validate: `validate` — purpose match, the minimum number of entries,
    the range, the status value read at `statusListIndex * statusSize`, and
    the result map (`status`, `purpose`, `valid`, `message`).

Bit order (§3.3, "Bitstring Encoding" appendix): index 0 is the left-most bit,
the most significant bit of the first byte. A status of `statusSize` bits is
read most significant bit first.

What this module does not do: dereference the status list credential or
verify its proof. The host fetches the document (STATUS_RETRIEVAL_ERROR is
the host's), and the proof is verified by `VC/Cryptosuite.lean`
(`verifyDocument`) before `validate` runs; the Wasm op does both in order.
-/
import L4Factoidal.JSON.Value
import L4Factoidal.JOSE.Base64Url
import L4Factoidal.Codec.Archive

namespace L4Factoidal.VC.StatusList

open L4Factoidal.JSON

/-! ## Errors (§3.5 Processing Errors) -/

inductive StatusError where
  /-- STATUS_RETRIEVAL_ERROR: the list credential could not be obtained. -/
  | retrieval (detail : String)
  /-- STATUS_VERIFICATION_ERROR: a proof or the purpose did not verify. -/
  | verification (detail : String)
  /-- STATUS_LIST_LENGTH_ERROR. -/
  | listLength (entries minimum : Nat)
  /-- RANGE_ERROR. -/
  | range (position length : Nat)
  /-- MALFORMED_VALUE_ERROR. -/
  | malformed (detail : String)
  deriving Repr, DecidableEq

def StatusError.code : StatusError → String
  | .retrieval _ => "STATUS_RETRIEVAL_ERROR"
  | .verification _ => "STATUS_VERIFICATION_ERROR"
  | .listLength _ _ => "STATUS_LIST_LENGTH_ERROR"
  | .range _ _ => "RANGE_ERROR"
  | .malformed _ => "MALFORMED_VALUE_ERROR"

def StatusError.describe : StatusError → String
  | .retrieval d => s!"STATUS_RETRIEVAL_ERROR: {d}"
  | .verification d => s!"STATUS_VERIFICATION_ERROR: {d}"
  | .listLength n m => s!"STATUS_LIST_LENGTH_ERROR: {n} entries, the minimum is {m}"
  | .range p l => s!"RANGE_ERROR: position {p} is outside the bitstring of {l} bits"
  | .malformed d => s!"MALFORMED_VALUE_ERROR: {d}"

/-! ## Bits -/

/-- §3.2 |minimumNumberOfEntries|. -/
def minimumNumberOfEntries : Nat := 131072

/-- The bit at position `i` (index 0 is the most significant bit of byte 0);
`false` outside the bitstring. -/
def bitAt (b : ByteArray) (i : Nat) : Bool :=
  if h : i / 8 < b.size then
    (b.get (i / 8) h >>> (7 - (i % 8 : Nat)).toUInt8) &&& 1 == 1
  else false

/-- The bitstring with the bit at `i` set to `v` (unchanged outside it). -/
def setBit (b : ByteArray) (i : Nat) (v : Bool) : ByteArray :=
  if i / 8 < b.size then
    let mask : UInt8 := (1 : UInt8) <<< (7 - (i % 8 : Nat)).toUInt8
    let old := b.get! (i / 8)
    b.set! (i / 8) (if v then old ||| mask else old &&& ~~~mask)
  else b

/-- The status of `size` bits starting at `pos`, most significant bit first. -/
def readStatus (b : ByteArray) (pos size : Nat) : Nat :=
  (List.range size).foldl (fun acc k => 2 * acc + (if bitAt b (pos + k) then 1 else 0)) 0

/-- The bitstring with the `size`-bit status at `pos` set to `value` (its low
`size` bits, most significant first). -/
def writeStatus (b : ByteArray) (pos size value : Nat) : ByteArray :=
  (List.range size).foldl (fun acc k => setBit acc (pos + k) ((value >>> (size - 1 - k)) % 2 == 1)) b

/-- A bitstring of `n` zero bits (rounded up to whole bytes). -/
def zeros (n : Nat) : ByteArray := ByteArray.mk (Array.replicate ((n + 7) / 8) 0)

/-! ## §3.3 Bitstring Generation and §3.4 Bitstring Expansion -/

/-- GZIP, then Multibase base64url with no padding. -/
def compress (bits : ByteArray) : String :=
  "u" ++ L4Factoidal.JOSE.Base64Url.encode (L4Factoidal.Codec.gzip bits)

/-- The reverse of `compress`. -/
def expand (encoded : String) : Except StatusError ByteArray :=
  match encoded.toList with
  | 'u' :: rest =>
      match L4Factoidal.JOSE.Base64Url.decode (String.ofList rest) with
      | none => .error (.malformed "encodedList is not base64url")
      | some gz =>
          match L4Factoidal.Codec.gunzip gz with
          | .ok b => .ok b
          | .error e => .error (.malformed s!"encodedList is not GZIP data: {e}")
  | _ => .error (.malformed "encodedList is not a Multibase base64url value (prefix u)")

/-- §3.3: a bitstring of `max entries 131,072 × statusSize` bits, every status
`0` except the given `(statusListIndex, value)` pairs, compressed. -/
def generate (statusSize : Nat) (entries : Nat) (set : List (Nat × Nat)) : String :=
  let n := max entries minimumNumberOfEntries * statusSize
  compress (set.foldl (fun b (i, v) => writeStatus b (i * statusSize) statusSize v) (zeros n))

/-! ## §2.1 BitstringStatusListEntry -/

/-- A checked entry. -/
structure Entry where
  statusPurpose : String
  statusListIndex : Nat
  statusListCredential : String
  statusSize : Nat := 1
  statusMessage : Option (List Json) := none
  deriving Repr

/-- A base-10 string of a non-negative integer, no sign, no leading zero
except `"0"`. -/
def parseIndex? (s : String) : Option Nat :=
  if s.isEmpty || !s.all Char.isDigit then none
  else if s.length > 1 && s.front == '0' then none
  else s.toNat?

def isUrlLike (s : String) : Bool := s.contains ':' && !s.contains ' '

/-- §2.1: check one `credentialStatus` entry of type BitstringStatusListEntry. -/
def checkEntry (j : Json) : Except StatusError Entry := do
  match j.getString? "type" with
  | some "BitstringStatusListEntry" => pure ()
  | _ => throw (.malformed "credentialStatus.type MUST be BitstringStatusListEntry")
  let purpose ← match j.field? "statusPurpose" with
    | some (.string s) => if s.isEmpty then throw (.malformed "statusPurpose is empty") else pure s
    | _ => throw (.malformed "statusPurpose MUST be a string")
  let idx ← match j.field? "statusListIndex" with
    | some (.string s) =>
        match parseIndex? s with
        | some n => pure n
        | none => throw (.malformed "statusListIndex MUST be a non-negative integer as a base-10 string")
    | _ => throw (.malformed "statusListIndex MUST be a string")
  let slc ← match j.field? "statusListCredential" with
    | some (.string s) => if isUrlLike s then pure s else throw (.malformed "statusListCredential MUST be a URL")
    | _ => throw (.malformed "statusListCredential MUST be a URL string")
  if let some (.string idv) := j.field? "id" then
    if idv == slc then throw (.malformed "credentialStatus.id MUST NOT be the URL of the status list")
  let size ← match j.field? "statusSize" with
    | none => pure 1
    | some (.number lex) =>
        match lex.toNat? with
        | some n => if n > 0 then pure n else throw (.malformed "statusSize MUST be greater than zero")
        | none => throw (.malformed "statusSize MUST be a positive integer")
    | _ => throw (.malformed "statusSize MUST be a positive integer")
  let msgs ← match j.field? "statusMessage" with
    | none => if size > 1 then throw (.malformed "statusMessage MUST be present when statusSize > 1") else pure none
    | some (.array ms) =>
        if ms.length != 2 ^ size then
          throw (.malformed s!"statusMessage MUST have 2^statusSize = {2 ^ size} entries, has {ms.length}")
        else if !ms.all (fun m => (m.getString? "status").isSome && (m.getString? "message").isSome) then
          throw (.malformed "each statusMessage entry MUST have status and message strings")
        else pure (some ms)
    | some _ => throw (.malformed "statusMessage MUST be an array")
  pure { statusPurpose := purpose, statusListIndex := idx, statusListCredential := slc,
         statusSize := size, statusMessage := msgs }

/-- The BitstringStatusListEntry values of a credential's `credentialStatus`
(one object or an array); other entry types are not this module's. -/
def statusEntries (cred : Json) : List Json :=
  let all := match cred.field? "credentialStatus" with
    | some (.array xs) => xs
    | some x => [x]
    | none => []
  all.filter (fun e => e.getString? "type" == some "BitstringStatusListEntry")

/-! ## §2.2 BitstringStatusListCredential and §3.2 Validate -/

def typesOf (j : Json) : List String :=
  match j.field? "type" with
  | some (.string s) => [s]
  | some (.array xs) => xs.filterMap (fun x => match x with | .string s => some s | _ => none)
  | _ => []

/-- The purposes of a list credential's subject (`statusPurpose`, a string or
an array). -/
def purposesOf (subj : Json) : List String :=
  match subj.field? "statusPurpose" with
  | some (.string s) => [s]
  | some (.array xs) => xs.filterMap (fun x => match x with | .string s => some s | _ => none)
  | _ => []

/-- §2.2: the credential subject of a status list credential. -/
def checkListCredential (slc : Json) : Except StatusError Json := do
  if !(typesOf slc).contains "BitstringStatusListCredential" then
    throw (.verification "the status list credential's type does not include BitstringStatusListCredential")
  let subj ← match slc.field? "credentialSubject" with
    | some s@(.object _) => pure s
    | _ => throw (.malformed "the status list credential has no credentialSubject object")
  if subj.getString? "type" != some "BitstringStatusList" then
    throw (.malformed "the credential subject's type MUST be BitstringStatusList")
  if (subj.getString? "encodedList").isNone then
    throw (.malformed "the credential subject has no encodedList string")
  pure subj

/-- The §3.2 result map. -/
structure Result where
  status : Nat
  purpose : String
  valid : Bool
  message : Option String := none
  deriving Repr, DecidableEq

/-- §3.2 Validate, from step 3 on: the entry and the list credential whose
proofs the caller has verified. -/
def validate (entry : Entry) (slc : Json) : Except StatusError Result := do
  let subj ← checkListCredential slc
  if !(purposesOf subj).contains entry.statusPurpose then
    throw (.verification s!"the status list has no statusPurpose \"{entry.statusPurpose}\"")
  let bits ← expand ((subj.getString? "encodedList").getD "")
  let nbits := bits.size * 8
  if nbits / entry.statusSize < minimumNumberOfEntries then
    throw (.listLength (nbits / entry.statusSize) minimumNumberOfEntries)
  let pos := entry.statusListIndex * entry.statusSize
  if pos + entry.statusSize > nbits then throw (.range pos nbits)
  let status := readStatus bits pos entry.statusSize
  let message := entry.statusMessage.bind fun ms =>
    (ms.find? (fun m => m.getString? "status" == some s!"0x{(Nat.toDigits 16 status).asString}")).bind
      (·.getString? "message")
  pure { status, purpose := entry.statusPurpose, valid := status == 0, message }

/-! ## Build-time checks

Bit order: every byte value, every bit position and both values; set then
read gives the value set, and the other seven bits are unchanged. This is an
exhaustive test of `setBit`/`bitAt` on one byte (4,096 cases), not a proof:
`decide` over `UInt8` reaches the recursion limit. -/

#guard (List.range 256).all fun n => (List.range 8).all fun k => [true, false].all fun v =>
  let b := ByteArray.mk #[n.toUInt8]
  let b' := setBit b k v
  bitAt b' k == v && (List.range 8).all (fun k2 => k2 == k || bitAt b' k2 == bitAt b k2)

-- index 0 is the most significant bit of the first byte
#guard bitAt (ByteArray.mk #[0x80, 0]) 0 && !bitAt (ByteArray.mk #[0x80, 0]) 7
#guard bitAt (ByteArray.mk #[0, 1]) 15
-- a 2-bit status, most significant bit first
#guard readStatus (writeStatus (zeros 16) 6 2 2) 6 2 == 2
#guard readStatus (writeStatus (zeros 16) 6 2 3) 6 2 == 3 && readStatus (zeros 16) 6 2 == 0
-- generation and expansion are inverse on a small list
#guard (expand (compress (writeStatus (zeros 64) 5 1 1))).toOption.map (fun b => readStatus b 5 1) == some 1
#guard (expand "zabc").toOption.isNone
#guard parseIndex? "0" == some 0 && parseIndex? "94567" == some 94567
#guard parseIndex? "" == none && parseIndex? "-1" == none && parseIndex? "01" == none

end L4Factoidal.VC.StatusList
