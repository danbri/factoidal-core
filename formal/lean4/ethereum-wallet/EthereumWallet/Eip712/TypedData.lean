import EthereumWallet.Eip712.Json
import EthereumWallet.Abi.Signature

/-!
# EIP-712 typed structured data

`encodeType` (the primary type first, then the struct types it refers to,
sorted by name), `typeHash`, `encodeData`, `hashStruct`, the domain separator
and the digest `keccak256(0x19 0x01 ‖ domainSeparator ‖ hashStruct(message))`,
following EIP-712 as specification.

The walk that hashes the data also builds the `Shown` tree. A confirmation
screen that renders `Shown` therefore shows exactly the fields that went into
the digest, with the values that were hashed: there is no second reading of
the JSON.

Stricter than common wallets, each a defined refusal:

* a member of the data that no declared field covers is refused (`extraField`),
  and so is a declared field with no value (`missingField`);
* `uint` and `int` without a width, and other non-canonical type names, are
  refused (`badType`), since `encodeType` hashes the name as written;
* a JSON number must be a whole number of at most 2^53 - 1 (larger values lose
  precision in other readers; send them as strings);
* `EIP712Domain` may only have the five standard fields with their standard
  types, in the standard order, and may not be the primary type;
* at most `maxTypes` types, `maxFields` fields per type, and data nested at
  most `maxDataDepth` deep (`dataTooDeep`). Struct types may refer to
  themselves; the depth limit is on the data.
-/

namespace EthereumWallet.Eip712

open EthereumWallet.Abi

/-- Risks of the typed-data and message hashing code. -/
inductive HashRisk where
  /-- The Keccak-256 used here is pure Lean. Its running time and allocation depend on the
      bytes hashed, and its digest values are tested against vectors, not proved. Typed-data
      values and `personal_sign` messages can be private, so hashing them is a choice the
      caller makes by name. (Selectors, topics, type strings, `CREATE` preimages and addresses
      are public by the protocol's definition and need no token.) -/
  | pureKeccakOnMessages
  deriving DecidableEq, Repr

/-- Evidence that a caller accepted risk `r`; only `HashRisk.dangerouslyAccept` makes one. -/
structure HashRisk.Accepted (r : HashRisk) : Type where
  private mk ::

def HashRisk.dangerouslyAccept (r : HashRisk) : HashRisk.Accepted r := ⟨⟩

/-- The token every function that hashes message content takes. -/
abbrev MessageHashing := HashRisk.Accepted .pureKeccakOnMessages

def maxTypes : Nat := 128
def maxFields : Nat := 256
def maxDataDepth : Nat := 32
def maxTypeChars : Nat := 256

structure TypeDef where
  name : String
  /-- Field name and type string, in declaration order. -/
  fields : List (String × String)

inductive FieldType where
  /-- `uint<M>`, `int<M>`, `address`, `bool`, `bytes<M>`. -/
  | atom (t : AbiType)
  | bytes
  | string
  | struct (name : String)
  | array (elem : FieldType) (len : Option Nat)

def isIdent (s : String) : Bool := !s.isEmpty && s.toList.all isIdentChar

def elementaryOf (ident : List Char) : Option FieldType :=
  match baseOfIdent ident with
  | .ok t =>
    if t.canonical == String.ofList ident && t.wf then
      match t with
      | .bytes => some .bytes
      | .string => some .string
      | _ => some (.atom t)
    else none
  | .error _ => none

def fieldSuffixes : Nat → FieldType → List Char → Option FieldType
  | 0, _, _ => none
  | fuel + 1, t, cs =>
    match cs with
    | [] => some t
    | '[' :: ']' :: rest => fieldSuffixes fuel (.array t none) rest
    | '[' :: rest =>
      let sp := rest.span Char.isDigit
      match parseDec sp.1, sp.2 with
      | some n, ']' :: rest' => fieldSuffixes fuel (.array t (some n)) rest'
      | _, _ => none
    | _ => none

/-- A field's type string: an elementary type or a declared struct, then array suffixes.
    At most `maxDataDepth` suffixes. -/
def parseFieldType (structNames : List String) (s : String) : Except Err712 FieldType :=
  if s.length > maxTypeChars then .error (.badType s)
  else
    let sp := s.toList.span isIdentChar
    let base : Option FieldType :=
      match elementaryOf sp.1 with
      | some t => some t
      | none =>
        if structNames.contains (String.ofList sp.1) then some (.struct (String.ofList sp.1))
        else none
    match base with
    | none => .error (.badType s)
    | some b =>
      match fieldSuffixes (maxDataDepth + 1) b sp.2 with
      | some t => .ok t
      | none => .error (.badType s)

/-! ## encodeType -/

def encodeMember (f : String × String) : String := f.2 ++ " " ++ f.1

def encodeOne (td : TypeDef) : String :=
  td.name ++ "(" ++ ",".intercalate (td.fields.map encodeMember) ++ ")"

def baseIdent (typeStr : String) : String :=
  String.ofList (typeStr.toList.takeWhile isIdentChar)

/-- Names of the struct types reachable from a work list. `none` if the fuel runs out. -/
def depsLoop : Nat → List TypeDef → List String → List String → Option (List String)
  | 0, _, _, _ => none
  | _ + 1, _, [], seen => some seen
  | fuel + 1, types, n :: work, seen =>
    if seen.contains n then depsLoop fuel types work seen
    else
      match types.find? (·.name == n) with
      | none => depsLoop fuel types work seen
      | some td => depsLoop fuel types (td.fields.map (fun f => baseIdent f.2) ++ work) (n :: seen)

def totalFields (types : List TypeDef) : Nat := types.foldl (fun a td => a + td.fields.length) 0

/-- `encodeType`: the primary type, then the struct types it refers to (directly or not),
    sorted by name. -/
def encodeType (types : List TypeDef) (primary : TypeDef) : Option String :=
  match depsLoop (2 * totalFields types + types.length + 2) types
      (primary.fields.map fun f => baseIdent f.2) [primary.name] with
  | none => none
  | some seen =>
    let others := (seen.filter (· != primary.name)).mergeSort fun a b => !decide (b < a)
    some (encodeOne primary
      ++ String.join (others.filterMap fun n => (types.find? (·.name == n)).map encodeOne))

structure TypeEntry where
  name : String
  typeHash : List UInt8
  fields : List (String × FieldType)

abbrev TypeTable := List TypeEntry

def noDup : List String → Bool
  | [] => true
  | a :: rest => !rest.contains a && noDup rest

def typeDefOk (td : TypeDef) : Bool :=
  isIdent td.name && (elementaryOf td.name.toList).isNone && decide (td.fields.length ≤ maxFields)
    && td.fields.all (fun f => isIdent f.1) && noDup (td.fields.map (·.1))

/-- The only fields `EIP712Domain` may have, with their types. -/
def domainFieldOk (f : String × String) : Bool :=
  f == ("name", "string") || f == ("version", "string") || f == ("chainId", "uint256")
    || f == ("verifyingContract", "address") || f == ("salt", "bytes32")

/-- Position of a domain field in the standard order. -/
def domainRank (name : String) : Nat :=
  if name == "name" then 0 else if name == "version" then 1 else if name == "chainId" then 2
  else if name == "verifyingContract" then 3 else 4

def increasing : List Nat → Bool
  | a :: b :: rest => decide (a < b) && increasing (b :: rest)
  | _ => true

/-- `EIP712Domain` is declared, has only standard fields, and has them in the standard order
    (readers disagree on the hash of a reordered domain type). -/
def domainOk (types : List TypeDef) : Bool :=
  match types.find? (·.name == "EIP712Domain") with
  | some td => td.fields.all domainFieldOk && increasing (td.fields.map fun f => domainRank f.1)
  | none => false

def buildEntry (types : List TypeDef) (names : List String) (td : TypeDef) :
    Except Err712 TypeEntry :=
  match td.fields.mapM (fun f =>
      match parseFieldType names f.2 with
      | .ok ft => Except.ok (f.1, ft)
      | .error e => .error e) with
  | .error e => .error e
  | .ok fs =>
    match encodeType types td with
    | some enc => .ok ⟨td.name, keccak256 (utf8 enc), fs⟩
    | none => .error .tooManyTypes

/-- Check the declarations and compute each type's hash once. -/
def buildTable (types : List TypeDef) : Except Err712 TypeTable :=
  if types.length > maxTypes then .error .tooManyTypes
  else
    let names := types.map (·.name)
    if !types.all typeDefOk || !noDup names then .error (.badType "types")
    else if !domainOk types then .error (.badType "EIP712Domain")
    else types.mapM (buildEntry types names)

/-! ## Values -/

def decDigits (cs : List Char) (maxDigits : Nat) : Option Nat :=
  if cs.isEmpty || cs.length > maxDigits || !cs.all Char.isDigit then none
  else some (cs.foldl (fun a c => a * 10 + (c.toNat - 48)) 0)

def hexNatLoop : List Char → Nat → Option Nat
  | [], a => some a
  | c :: cs, a =>
    match hexVal c with
    | some v => hexNatLoop cs (a * 16 + v)
    | none => none

def hexNat (cs : List Char) : Option Nat :=
  if cs.isEmpty || cs.length > 64 then none else hexNatLoop cs 0

/-- Largest whole number a JSON number may carry here: 2^53 - 1. -/
def maxSafeInteger : Nat := 9007199254740991

def natOfJson : Json → Option Nat
  | .num raw =>
    match decDigits raw 16 with
    | some n => if n ≤ maxSafeInteger then some n else none
    | none => none
  | .str s =>
    match s.toList with
    | '0' :: 'x' :: r => hexNat r
    | cs => decDigits cs 78
  | _ => none

def intOfJson : Json → Option Int
  | .num ('-' :: raw) =>
    match decDigits raw 16 with
    | some n => if n ≤ maxSafeInteger then some (-(Int.ofNat n)) else none
    | none => none
  | .str s =>
    match s.toList with
    | '-' :: r => (decDigits r 78).map fun n => -(Int.ofNat n)
    | _ => (natOfJson (.str s)).map Int.ofNat
  | j => (natOfJson j).map Int.ofNat

/-- Bytes of a `0x` hex string with an even number of digits. -/
def hexBytes (s : String) : Option (List UInt8) :=
  match s.toList with
  | '0' :: 'x' :: r => unhexLoop r []
  | _ => none

def atomOfJson (t : AbiType) (j : Json) : Option AbiValue :=
  match t with
  | .uint _ => (natOfJson j).map .uint
  | .int _ => (intOfJson j).map .int
  | .address =>
    match j with
    | .str s =>
      match s.toList with
      | '0' :: 'x' :: r => if r.length == 40 then (hexNat r).map .address else none
      | _ => none
    | _ => none
  | .bool =>
    match j with
    | .bool b => some (.bool b)
    | _ => none
  | .fixedBytes _ =>
    match j with
    | .str s => (hexBytes s).map .bytes
    | _ => none
  | _ => none

/-- A JSON value read at an elementary type, accepted only if it has that type. -/
def parseAtom (t : AbiType) (j : Json) : Option AbiValue :=
  match atomOfJson t j with
  | some v => if t.check v then some v else none
  | none => none

/-- Kind: typing. Says: an accepted elementary value has its declared type (in range, right width).
    Does not say: that the JSON spelling was canonical. -/
theorem parseAtom_check (t : AbiType) (j : Json) (v : AbiValue) (h : parseAtom t j = some v) :
    t.check v = true := by
  simp only [parseAtom] at h
  split at h
  · split at h
    · rename_i hc
      cases h
      exact hc
    · cases h
  · cases h

/-- What was hashed, for display. -/
inductive Shown where
  | atom (type : String) (v : AbiValue)
  | bytes (b : List UInt8)
  | string (s : String)
  | struct (name : String) (fields : List (String × Shown))
  | array (items : List Shown)

instance : Inhabited Shown := ⟨.bytes []⟩

/-- `encodeData` for one field: its 32 bytes and what to show for it. The fuel is the nesting
    depth allowed; each struct or array level uses one. -/
def encodeField (risk : MessageHashing) (table : TypeTable) : Nat → FieldType → String → Json →
    Except Err712 (List UInt8 × Shown)
  | 0, _, _, _ => .error .dataTooDeep
  | fuel + 1, ft, fname, j =>
    match ft with
    | .atom t =>
      match parseAtom t j with
      | some v => .ok (t.enc v, .atom t.canonical v)
      | none => .error (.badValue fname)
    | .bytes =>
      match j with
      | .str s =>
        match hexBytes s with
        | some b => .ok (keccak256 b, .bytes b)
        | none => .error (.badValue fname)
      | _ => .error (.badValue fname)
    | .string =>
      match j with
      | .str s => .ok (keccak256 (utf8 s), .string s)
      | _ => .error (.badValue fname)
    | .array elem len =>
      match j with
      | .arr items =>
        if (match len with | some n => items.length != n | none => false) then
          .error (.badValue fname)
        else
          match items.mapM (encodeField risk table fuel elem fname) with
          | .error e => .error e
          | .ok rs => .ok (keccak256 (rs.flatMap (·.1)), .array (rs.map (·.2)))
      | _ => .error (.badValue fname)
    | .struct n =>
      match j with
      | .obj members =>
        match table.find? (·.name == n) with
        | none => .error (.badType n)
        | some te =>
          if members.length > te.fields.length then .error .extraField
          else
            match te.fields.mapM (fun (f : String × FieldType) =>
                match members.lookup f.1 with
                | none => (Except.error (Err712.missingField f.1) : Except Err712 (List UInt8 × Shown))
                | some jv => encodeField risk table fuel f.2 f.1 jv) with
            | .error e => .error e
            | .ok rs =>
              .ok (keccak256 (te.typeHash ++ rs.flatMap (·.1)),
                .struct n ((te.fields.map (·.1)).zip (rs.map (·.2))))
      | _ => .error (.badValue fname)

/-- Kind: refusal at the bound. Says: with no depth left, the walk refuses.
    Does not say: how deep a given document is. -/
theorem encodeField_depth_refused (risk : MessageHashing) (table : TypeTable) (ft : FieldType)
    (fname : String) (j : Json) :
    encodeField risk table 0 ft fname j = .error .dataTooDeep := rfl

/-! ## The request -/

structure TypedData where
  types : List TypeDef
  primaryType : String
  domain : Json
  message : Json

def fieldOfJson (f : Json) : Except Err712 (String × String) :=
  match f.get? "name", f.get? "type" with
  | some (.str n), some (.str t) => .ok (n, t)
  | _, _ => .error .badShape

def typeDefOfJson (m : String × Json) : Except Err712 TypeDef :=
  match m.2 with
  | .arr fields =>
    match fields.mapM fieldOfJson with
    | .ok fs => .ok ⟨m.1, fs⟩
    | .error e => .error e
  | _ => .error .badShape

def TypedData.ofJson (j : Json) : Except Err712 TypedData :=
  match j.get? "types", j.get? "primaryType", j.get? "domain", j.get? "message" with
  | some (.obj tms), some (.str p), some d, some m =>
    match tms.mapM typeDefOfJson with
    | .ok ts => .ok ⟨ts, p, d, m⟩
    | .error e => .error e
  | _, _, _, _ => .error .badShape

/-- What a wallet is asked to sign, and what to show for it. -/
structure SignRequest where
  primaryType : String
  domainSeparator : List UInt8
  messageHash : List UInt8
  digest : List UInt8
  domain : Shown
  message : Shown

/-- `keccak256(0x19 ‖ 0x01 ‖ domainSeparator ‖ hashStruct(message))`. -/
def typedDataDigest (domainSeparator messageHash : List UInt8) : List UInt8 :=
  keccak256 (0x19 :: 0x01 :: (domainSeparator ++ messageHash))

def finishRequest (primaryType : String) (d m : Except Err712 (List UInt8 × Shown)) :
    Except Err712 SignRequest :=
  match d, m with
  | .ok d, .ok m =>
    .ok { primaryType := primaryType, domainSeparator := d.1, messageHash := m.1,
          digest := typedDataDigest d.1 m.1, domain := d.2, message := m.2 }
  | .error e, _ => .error e
  | _, .error e => .error e

theorem finishRequest_digest (p : String) (d m : Except Err712 (List UInt8 × Shown))
    (r : SignRequest) (h : finishRequest p d m = .ok r) :
    r.digest = typedDataDigest r.domainSeparator r.messageHash := by
  cases d with
  | error e => simp [finishRequest] at h
  | ok d =>
    cases m with
    | error e => simp [finishRequest] at h
    | ok m =>
      simp only [finishRequest, Except.ok.injEq] at h
      rw [← h]

def hashTypedData (risk : MessageHashing) (td : TypedData) : Except Err712 SignRequest :=
  if td.primaryType == "EIP712Domain" then .error (.badType "EIP712Domain")
  else
    match buildTable td.types with
    | .error e => .error e
    | .ok table =>
      finishRequest td.primaryType
        (encodeField risk table (maxDataDepth + 1) (.struct "EIP712Domain") "domain" td.domain)
        (encodeField risk table (maxDataDepth + 1) (.struct td.primaryType) "message" td.message)

/-- Kind: definition check. Says: the digest of an accepted request is
    `keccak256(0x19 0x01 ‖ domainSeparator ‖ messageHash)` of the two hashes it reports.
    Does not say: that those hashes follow EIP-712 (tested against the specification's vectors
    and other implementations), or that `keccak256` is Keccak-256. -/
theorem hashTypedData_digest (risk : MessageHashing) (td : TypedData) (r : SignRequest)
    (h : hashTypedData risk td = .ok r) :
    r.digest = typedDataDigest r.domainSeparator r.messageHash := by
  simp only [hashTypedData] at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact finishRequest_digest _ _ _ r h

/-- Parse typed-data JSON and hash it. -/
def signRequestOfJson (risk : MessageHashing) (s : String) : Except Err712 SignRequest :=
  match parseJson s with
  | .error e => .error e
  | .ok j =>
    match TypedData.ofJson j with
    | .error e => .error e
    | .ok td => hashTypedData risk td

def Shown.field? (s : Shown) (name : String) : Option Shown :=
  match s with
  | .struct _ fields => fields.lookup name
  | _ => none

def Shown.addr? (s : Shown) (name : String) : Option Nat :=
  match s.field? name with
  | some (.atom _ (.address a)) => some a
  | _ => none

def Shown.uint? (s : Shown) (name : String) : Option Nat :=
  match s.field? name with
  | some (.atom _ (.uint n)) => some n
  | _ => none

def Shown.bool? (s : Shown) (name : String) : Option Bool :=
  match s.field? name with
  | some (.atom _ (.bool b)) => some b
  | _ => none

/-- The chain a request is bound to, if its domain says. -/
def SignRequest.chainId? (r : SignRequest) : Option Nat :=
  match r.domain.field? "chainId" with
  | some (.atom _ (.uint n)) => some n
  | _ => none

def SignRequest.verifyingContract? (r : SignRequest) : Option Nat :=
  match r.domain.field? "verifyingContract" with
  | some (.atom _ (.address a)) => some a
  | _ => none

/-! ## EIP-191 `personal_sign` -/

/-- `keccak256("\x19Ethereum Signed Message:\n" ‖ decimal length ‖ message)`. -/
def personalSignDigest (_ : MessageHashing) (msg : List UInt8) : List UInt8 :=
  keccak256 (0x19 :: (utf8 "Ethereum Signed Message:\n" ++ utf8 (toString msg.length) ++ msg))

/-- Kind: definition check. Says: the `personal_sign` digest is the hash of the EIP-191
    version-0x45 prefix, the decimal byte length and the message.
    Does not say: that `keccak256` is Keccak-256. -/
theorem personalSignDigest_eq (risk : MessageHashing) (msg : List UInt8) :
    personalSignDigest risk msg
      = keccak256 (0x19 :: (utf8 "Ethereum Signed Message:\n" ++ utf8 (toString msg.length) ++ msg)) :=
  rfl

end EthereumWallet.Eip712
