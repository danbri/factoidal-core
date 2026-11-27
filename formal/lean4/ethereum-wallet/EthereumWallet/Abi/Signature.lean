import EthereumWallet.Abi.Hash
import EthereumWallet.Abi.Strict

/-!
# Type strings, function signatures, selectors and calldata

The parser reads the canonical type grammar of the ABI specification:
`uint<M>`, `int<M>`, `address`, `bool`, `bytes<M>`, `bytes`, `string`,
`(T1,...,Tn)`, `T[]`, `T[k]`. It also reads `uint` and `int` as the 256-bit
types; `canonical` always prints the full name. `fixed`, `ufixed` and
`function` are refused.

Bounds on input from outside: at most `maxSigChars` characters; nesting at most
`maxTypeDepth`; array lengths of at most `maxLenDigits` digits. Past a bound
the parser returns `Err.badType`.
-/

namespace EthereumWallet.Abi

def maxSigChars : Nat := 2048
def maxLenDigits : Nat := 10

/-- A decimal number with no sign, no leading zero and at most `maxLenDigits` digits. -/
def parseDec (ds : List Char) : Option Nat :=
  if ds.isEmpty || ds.length > maxLenDigits || !ds.all Char.isDigit then none
  else if ds.head? == some '0' && ds.length > 1 then none
  else some (ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0)

def baseOfIdent (w : List Char) : Except Err AbiType :=
  let s := String.ofList w
  if s == "address" then .ok .address
  else if s == "bool" then .ok .bool
  else if s == "string" then .ok .string
  else if s == "bytes" then .ok .bytes
  else if s == "uint" then .ok (.uint 256)
  else if s == "int" then .ok (.int 256)
  else if "bytes".toList.isPrefixOf w then
    match parseDec (w.drop 5) with
    | some n => .ok (.fixedBytes n)
    | none => .error .badType
  else if "uint".toList.isPrefixOf w then
    match parseDec (w.drop 4) with
    | some n => .ok (.uint n)
    | none => .error .badType
  else if "int".toList.isPrefixOf w then
    match parseDec (w.drop 3) with
    | some n => .ok (.int n)
    | none => .error .badType
  else .error .badType

/-- Array suffixes after a base type. `depth` counts nesting so far. -/
def parseSuffixes : Nat → Nat → AbiType → List Char → Except Err (AbiType × List Char)
  | 0, _, _, _ => .error .badType
  | fuel + 1, depth, t, cs =>
    match cs with
    | '[' :: rest =>
      if depth ≥ maxTypeDepth then .error .badType
      else
        match rest with
        | ']' :: rest' => parseSuffixes fuel (depth + 1) (.array t) rest'
        | _ =>
          let sp := rest.span Char.isDigit
          match parseDec sp.1, sp.2 with
          | some n, ']' :: rest' => parseSuffixes fuel (depth + 1) (.fixedArray t n) rest'
          | _, _ => .error .badType
    | _ => .ok (t, cs)

mutual
/-- One type. `fuel` bounds the work, `depth` the nesting of tuples entered so far. -/
def parseTy : Nat → Nat → List Char → Except Err (AbiType × List Char)
  | 0, _, _ => .error .badType
  | fuel + 1, depth, cs =>
    if depth > maxTypeDepth then .error .badType
    else
      match cs with
      | '(' :: ')' :: rest => parseSuffixes (fuel + 1) depth (.tuple []) rest
      | '(' :: rest =>
        match parseItems fuel depth rest [] with
        | .error e => .error e
        | .ok r => parseSuffixes (fuel + 1) depth (.tuple r.1) r.2
      | _ =>
        let sp := cs.span Char.isAlphanum
        match baseOfIdent sp.1 with
        | .error e => .error e
        | .ok t => parseSuffixes (fuel + 1) depth t sp.2
/-- The members of a tuple after `(`, up to and including `)`. -/
def parseItems : Nat → Nat → List Char → List AbiType → Except Err (List AbiType × List Char)
  | 0, _, _, _ => .error .badType
  | fuel + 1, depth, cs, acc =>
    match parseTy fuel (depth + 1) cs with
    | .error e => .error e
    | .ok r =>
      match r.2 with
      | ',' :: rest => parseItems fuel depth rest (r.1 :: acc)
      | ')' :: rest => .ok ((r.1 :: acc).reverse, rest)
      | _ => .error .badType
end

/-- Parse one type string. The result is well formed and within the depth bound. -/
def parseType (s : String) : Except Err AbiType :=
  if s.length > maxSigChars then .error .badType
  else
    let cs := s.toList
    match parseTy (cs.length + 2) 0 cs with
    | .error e => .error e
    | .ok r =>
      if r.2.isEmpty && r.1.wf && decide (r.1.depth ≤ maxTypeDepth) then .ok r.1
      else .error .badType

/-- Kind: bound on accepted input. Says: a parsed type is well formed and nested at most
    `maxTypeDepth` deep.
    Does not say: that every well-formed type string parses (tested, not proved). -/
theorem parseType_ok (s : String) (t : AbiType) (h : parseType s = .ok t) :
    t.wf = true ∧ t.depth ≤ maxTypeDepth := by
  simp only [parseType] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · rename_i hok
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
        exact ⟨hok.1.2, hok.2⟩
      · cases h

/-- Kind: refusal at the bound. Says: a type string over `maxSigChars` characters is refused
    before it is scanned.
    Does not say: anything about shorter strings. -/
theorem parseType_too_long (s : String) (h : maxSigChars < s.length) :
    parseType s = .error .badType := by
  simp [parseType, h]

/-! ## Functions -/

structure FunctionSig where
  name : String
  inputs : List AbiType

/-- `name(type1,...,typeN)` with canonical type names and no spaces. -/
def FunctionSig.canonical (f : FunctionSig) : String :=
  f.name ++ "(" ++ canonicalL f.inputs ++ ")"

/-- The 4-byte function selector. -/
def FunctionSig.selector (f : FunctionSig) : List UInt8 :=
  (keccak256 (utf8 f.canonical)).take 4

/-- Kind: definition check. Says: the selector is the first four bytes of the Keccak-256 hash
    of the UTF-8 bytes of the canonical signature.
    Does not say: that `keccak256` is Keccak-256 (tested against published selectors). -/
theorem selector_eq (f : FunctionSig) :
    f.selector = (keccak256 (utf8 (f.name ++ "(" ++ canonicalL f.inputs ++ ")"))).take 4 := rfl

theorem selector_length (f : FunctionSig) : f.selector.length = 4 := by
  simp [FunctionSig.selector, keccak256_length]

def isIdentChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$'

/-- Parse `name(type1,...,typeN)`. -/
def parseSignature (s : String) : Except Err FunctionSig :=
  if s.length > maxSigChars then .error .badType
  else
    let sp := s.toList.span isIdentChar
    if sp.1.isEmpty then .error .badType
    else
      match parseTy (sp.2.length + 2) 0 sp.2 with
      | .error e => .error e
      | .ok r =>
        match r.1, r.2 with
        | .tuple ts, [] =>
          if typesOk ts then .ok { name := String.ofList sp.1, inputs := ts } else .error .badType
        | _, _ => .error .badType

/-- Kind: bound on accepted input. Says: a parsed signature's input types are accepted by the decoder.
    Does not say: that the name is a valid Solidity identifier beyond its character set. -/
theorem parseSignature_ok (s : String) (f : FunctionSig) (h : parseSignature s = .ok f) :
    typesOk f.inputs = true := by
  simp only [parseSignature] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · split at h
          · rename_i hok
            cases h
            exact hok
          · cases h
        · cases h

/-- Calldata: selector, then the encoded arguments. -/
def encodeCall (f : FunctionSig) (args : List AbiValue) : List UInt8 :=
  f.selector ++ encodeArgs f.inputs args

/-- Strict decoding of calldata against one known function. -/
def decodeCall (f : FunctionSig) (d : ByteArray) : Except Err (List AbiValue) :=
  if windowB d 0 f.selector then decodeArgsAt f.inputs d 4 else .error .unknownSelector

/-- Kind: round trip. Says: decoding the calldata built for a function returns its arguments.
    Does not say: that two functions never share a selector (they can). -/
theorem decodeCall_encodeCall (f : FunctionSig) (args : List AbiValue)
    (hty : typesOk f.inputs = true) (hc : checkL f.inputs args = true)
    (hl : (encodeArgs f.inputs args).length < two256) :
    decodeCall f (toBytes (encodeCall f args)) = .ok args := by
  have hw := window_toBytes (encodeCall f args)
  simp only [encodeCall] at hw ⊢
  have hsel := (windowB_iff _ 0 f.selector).mpr hw.left
  have hargs := hw.right
  rw [selector_length] at hargs
  simp only [decodeCall, hsel, if_true]
  exact decodeArgsAt_complete f.inputs _ 4 args hty hc hl (by simpa using hargs)
    (by rw [toBytes_size, List.length_append, selector_length])

/-- Kind: soundness. Says: accepted calldata is exactly the selector followed by the canonical
    encoding of the returned arguments, and nothing else.
    Does not say: that the contract at the target address implements this function. -/
theorem decodeCall_sound (f : FunctionSig) (d : ByteArray) (args : List AbiValue)
    (h : decodeCall f d = .ok args) :
    Window d 0 f.selector ∧ checkL f.inputs args = true
      ∧ Window d 4 (encodeArgs f.inputs args) ∧ 4 + (encodeArgs f.inputs args).length = d.size := by
  simp only [decodeCall] at h
  split at h
  · rename_i hsel
    have hs := decodeArgsAt_sound f.inputs d 4 args h
    exact ⟨(windowB_iff _ _ _).mp hsel, hs.2.1, hs.2.2.1, hs.2.2.2⟩
  · cases h

end EthereumWallet.Abi
