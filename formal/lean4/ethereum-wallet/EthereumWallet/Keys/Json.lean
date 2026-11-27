/-
A small JSON reader of our own, for keystore files. It imports nothing outside
`Init` (in particular not `Lean.Data.Json`, so no proof-assistant initialiser
reaches an executable through it).

Accepted: objects, arrays, strings, integers, `true`, `false`, `null`.
Refused with a defined error: input over `jsonMaxBytes`, nesting over
`jsonMaxDepth`, numbers with a fraction or exponent or more than
`jsonMaxDigits` digits or a leading zero, `\u` escapes for surrogates, raw
control characters in strings, invalid UTF-8, trailing text.

Two passes, both loops structural on a count and tail calls: bytes to tokens
(each token consumes at least one byte, so `size + 1` steps are enough), then
tokens to a value with an explicit stack whose height is checked against
`jsonMaxDepth`. Tested in `KeystoreTests`; nothing here is proved.
-/

namespace EthereumWallet.Keys

/-- A JSON value. Numbers are integers only. Object members keep their order. -/
inductive Json where
  | null
  | bool (b : Bool)
  | num (n : Int)
  | str (s : String)
  | arr (items : List Json)
  | obj (members : List (String × Json))

inductive JsonError where
  | tooLarge
  | tooDeep
  | unexpectedEnd
  | unexpectedByte (pos : Nat)
  | badString (pos : Nat)
  | unsupportedEscape (pos : Nat)
  | unsupportedNumber (pos : Nat)
  | unexpectedToken (index : Nat)
  | trailingText
  deriving Repr, BEq, DecidableEq

/-- Largest input accepted, in bytes. -/
def jsonMaxBytes : Nat := 1048576

/-- Deepest nesting of arrays and objects accepted. -/
def jsonMaxDepth : Nat := 32

/-- Most digits accepted in a number. -/
def jsonMaxDigits : Nat := 18

inductive JsonToken where
  | lbrace | rbrace | lbrack | rbrack | colon | comma
  | str (s : String)
  | num (n : Int)
  | tru | fls | nul

/-- Append the UTF-8 form of a code point below 0x10000 that is not a surrogate. -/
def pushUtf8Bmp (acc : ByteArray) (c : Nat) : ByteArray :=
  if c < 0x80 then acc.push (UInt8.ofNat c)
  else if c < 0x800 then
    (acc.push (UInt8.ofNat (0xC0 + c / 64))).push (UInt8.ofNat (0x80 + c % 64))
  else
    ((acc.push (UInt8.ofNat (0xE0 + c / 4096))).push (UInt8.ofNat (0x80 + c / 64 % 64))).push
      (UInt8.ofNat (0x80 + c % 64))

/-- The value of an ASCII hex digit. -/
def jsonHexVal? (c : UInt8) : Option Nat :=
  if 48 ≤ c && c ≤ 57 then some (c.toNat - 48)
  else if 97 ≤ c && c ≤ 102 then some (c.toNat - 87)
  else if 65 ≤ c && c ≤ 70 then some (c.toNat - 55)
  else none

/-- The four hex digits of a `\u` escape at `pos`. -/
def jsonHex4? (src : ByteArray) (pos : Nat) : Option Nat :=
  if src.size < pos + 4 then none
  else
    match jsonHexVal? (src.get! pos), jsonHexVal? (src.get! (pos + 1)),
        jsonHexVal? (src.get! (pos + 2)), jsonHexVal? (src.get! (pos + 3)) with
    | some a, some b, some c, some d => some (((a * 16 + b) * 16 + c) * 16 + d)
    | _, _, _, _ => none

/-- Read a string body from `pos` (just after the opening quote) to its closing
    quote. Gives the decoded bytes and the position after the quote. Structural
    on `fuel`; every step consumes at least one byte. -/
def lexString (src : ByteArray) : Nat → Nat → ByteArray → Except JsonError (ByteArray × Nat)
  | 0, _, _ => .error .unexpectedEnd
  | fuel + 1, pos, acc =>
    if src.size ≤ pos then .error .unexpectedEnd
    else
      let c := src.get! pos
      if c == 0x22 then .ok (acc, pos + 1)
      else if c < 0x20 then .error (.badString pos)
      else if c == 0x5C then
        if src.size ≤ pos + 1 then .error .unexpectedEnd
        else
          let e := src.get! (pos + 1)
          if e == 0x22 || e == 0x5C || e == 0x2F then lexString src fuel (pos + 2) (acc.push e)
          else if e == 0x62 then lexString src fuel (pos + 2) (acc.push 0x08)
          else if e == 0x66 then lexString src fuel (pos + 2) (acc.push 0x0C)
          else if e == 0x6E then lexString src fuel (pos + 2) (acc.push 0x0A)
          else if e == 0x72 then lexString src fuel (pos + 2) (acc.push 0x0D)
          else if e == 0x74 then lexString src fuel (pos + 2) (acc.push 0x09)
          else if e == 0x75 then
            match jsonHex4? src (pos + 2) with
            | none => .error (.badString pos)
            | some cp =>
              if 0xD800 ≤ cp && cp ≤ 0xDFFF then .error (.unsupportedEscape pos)
              else lexString src fuel (pos + 6) (pushUtf8Bmp acc cp)
          else .error (.badString pos)
      else lexString src fuel (pos + 1) (acc.push c)

/-- Read the digits of a number from `pos`. Gives the value, the digit count
    and the position after the last digit. Structural on `fuel`. -/
def lexDigits (src : ByteArray) : Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, pos, acc, count => (acc, count, pos)
  | fuel + 1, pos, acc, count =>
    if pos < src.size then
      let c := src.get! pos
      if 48 ≤ c && c ≤ 57 then lexDigits src fuel (pos + 1) (acc * 10 + (c.toNat - 48)) (count + 1)
      else (acc, count, pos)
    else (acc, count, pos)

/-- An integer at `pos`, optional minus sign first. -/
def lexNumber (src : ByteArray) (pos : Nat) : Except JsonError (Int × Nat) :=
  let neg := src.get! pos == 0x2D
  let start := if neg then pos + 1 else pos
  let (value, count, stop) := lexDigits src (jsonMaxDigits + 1) start 0 0
  if count == 0 || count > jsonMaxDigits then .error (.unsupportedNumber pos)
  else if count > 1 && src.get! start == 48 then .error (.unsupportedNumber pos)
  else
    let next := if stop < src.size then src.get! stop else 0x20
    -- A fraction, an exponent or a further digit: not an integer we take.
    if next == 0x2E || next == 0x65 || next == 0x45 || (48 ≤ next && next ≤ 57) then
      .error (.unsupportedNumber pos)
    else .ok (if neg then -(Int.ofNat value) else Int.ofNat value, stop)

/-- Whether `src` holds the ASCII text `word` at `pos`. -/
def jsonHasWord (src : ByteArray) (pos : Nat) (word : ByteArray) : Bool :=
  pos + word.size ≤ src.size && (src.extract pos (pos + word.size)).data == word.data

/-- Bytes to tokens. Structural on `fuel`, a tail call; `fuel = size + 1` is enough. -/
def lexLoop (src : ByteArray) : Nat → Nat → Array JsonToken → Except JsonError (Array JsonToken)
  | 0, _, _ => .error .unexpectedEnd
  | fuel + 1, pos, acc =>
    if src.size ≤ pos then .ok acc
    else
      let c := src.get! pos
      if c == 0x20 || c == 0x09 || c == 0x0A || c == 0x0D then lexLoop src fuel (pos + 1) acc
      else if c == 0x7B then lexLoop src fuel (pos + 1) (acc.push .lbrace)
      else if c == 0x7D then lexLoop src fuel (pos + 1) (acc.push .rbrace)
      else if c == 0x5B then lexLoop src fuel (pos + 1) (acc.push .lbrack)
      else if c == 0x5D then lexLoop src fuel (pos + 1) (acc.push .rbrack)
      else if c == 0x3A then lexLoop src fuel (pos + 1) (acc.push .colon)
      else if c == 0x2C then lexLoop src fuel (pos + 1) (acc.push .comma)
      else if c == 0x22 then
        match lexString src (src.size + 1) (pos + 1) ByteArray.empty with
        | .error e => .error e
        | .ok (bytes, next) =>
          match String.fromUTF8? bytes with
          | none => .error (.badString pos)
          | some s => lexLoop src fuel next (acc.push (.str s))
      else if c == 0x2D || (48 ≤ c && c ≤ 57) then
        match lexNumber src pos with
        | .error e => .error e
        | .ok (n, next) => lexLoop src fuel next (acc.push (.num n))
      else if jsonHasWord src pos "true".toUTF8 then lexLoop src fuel (pos + 4) (acc.push .tru)
      else if jsonHasWord src pos "false".toUTF8 then lexLoop src fuel (pos + 5) (acc.push .fls)
      else if jsonHasWord src pos "null".toUTF8 then lexLoop src fuel (pos + 4) (acc.push .nul)
      else .error (.unexpectedByte pos)

/-- An unfinished array or object waiting for the value being read. -/
inductive JsonFrame where
  | arr (done : List Json)
  | obj (done : List (String × Json)) (key : String)

/-- What the token machine expects next. -/
inductive JsonMode where
  /-- A value. -/
  | value
  /-- Just after `[`: a value or `]`. -/
  | arrStart
  /-- After an array item: `,` or `]`. -/
  | arrNext (done : List Json)
  /-- Just after `{`: a key or `}`. -/
  | objStart
  /-- After `,` in an object: a key. -/
  | objKey (done : List (String × Json))
  /-- After a key: `:`. -/
  | objColon (done : List (String × Json)) (key : String)
  /-- After an object member: `,` or `}`. -/
  | objNext (done : List (String × Json))
  /-- The whole value is read. -/
  | finished (v : Json)

/-- Hand a finished value to whatever was waiting for it. -/
def jsonGive (stack : List JsonFrame) (v : Json) : List JsonFrame × JsonMode :=
  match stack with
  | [] => ([], .finished v)
  | .arr done :: rest => (rest, .arrNext (v :: done))
  | .obj done key :: rest => (rest, .objNext ((key, v) :: done))

/-- A token where a value is expected. -/
def jsonValueStep (stack : List JsonFrame) (tok : JsonToken) (index : Nat) :
    Except JsonError (List JsonFrame × JsonMode) :=
  match tok with
  | .str s => .ok (jsonGive stack (.str s))
  | .num n => .ok (jsonGive stack (.num n))
  | .tru => .ok (jsonGive stack (.bool true))
  | .fls => .ok (jsonGive stack (.bool false))
  | .nul => .ok (jsonGive stack .null)
  | .lbrack => .ok (stack, .arrStart)
  | .lbrace => .ok (stack, .objStart)
  | _ => .error (.unexpectedToken index)

/-- Push a frame, refusing beyond `jsonMaxDepth`. -/
def jsonPush (stack : List JsonFrame) (f : JsonFrame) : Except JsonError (List JsonFrame) :=
  if jsonMaxDepth ≤ stack.length then .error .tooDeep else .ok (f :: stack)

/-- One token of the machine. -/
def jsonStep (stack : List JsonFrame) (mode : JsonMode) (tok : JsonToken) (index : Nat) :
    Except JsonError (List JsonFrame × JsonMode) :=
  match mode, tok with
  | .value, tok => jsonValueStep stack tok index
  | .arrStart, .rbrack => .ok (jsonGive stack (.arr []))
  | .arrStart, tok =>
    match jsonPush stack (.arr []) with
    | .error e => .error e
    | .ok stack => jsonValueStep stack tok index
  | .arrNext done, .comma =>
    match jsonPush stack (.arr done) with
    | .error e => .error e
    | .ok stack => .ok (stack, .value)
  | .arrNext done, .rbrack => .ok (jsonGive stack (.arr done.reverse))
  | .objStart, .rbrace => .ok (jsonGive stack (.obj []))
  | .objStart, .str key => .ok (stack, .objColon [] key)
  | .objKey done, .str key => .ok (stack, .objColon done key)
  | .objColon done key, .colon =>
    match jsonPush stack (.obj done key) with
    | .error e => .error e
    | .ok stack => .ok (stack, .value)
  | .objNext done, .comma => .ok (stack, .objKey done)
  | .objNext done, .rbrace => .ok (jsonGive stack (.obj done.reverse))
  | .finished _, _ => .error .trailingText
  | _, _ => .error (.unexpectedToken index)

/-- Run the machine over the tokens. Structural on the token list, a tail call. -/
def jsonRun : List JsonToken → Nat → List JsonFrame → JsonMode → Except JsonError Json
  | [], _, _, .finished v => .ok v
  | [], _, _, _ => .error .unexpectedEnd
  | tok :: rest, index, stack, mode =>
    match jsonStep stack mode tok index with
    | .error e => .error e
    | .ok (stack, mode) => jsonRun rest (index + 1) stack mode

/-- Read one JSON value from UTF-8 bytes. -/
def Json.parseBytes (src : ByteArray) : Except JsonError Json :=
  if jsonMaxBytes < src.size then .error .tooLarge
  else
    match lexLoop src (src.size + 1) 0 #[] with
    | .error e => .error e
    | .ok tokens => jsonRun tokens.toList 0 [] .value

/-- Read one JSON value from a string. -/
def Json.parse (s : String) : Except JsonError Json := Json.parseBytes s.toUTF8

/-- Kind: resource refusal.
    Says: input over `jsonMaxBytes` is refused before any of it is read.
    Does not say: anything about smaller input. -/
theorem Json.parseBytes_tooLarge (src : ByteArray) (h : jsonMaxBytes < src.size) :
    Json.parseBytes src = .error .tooLarge := by
  simp [Json.parseBytes, h]

/-- Kind: resource refusal.
    Says: the machine never lets the stack of open arrays and objects grow past
    `jsonMaxDepth`; a push at that height is the error `.tooDeep`.
    Does not say: that the reader accepts exactly JSON (tested). -/
theorem jsonPush_tooDeep (stack : List JsonFrame) (f : JsonFrame)
    (h : jsonMaxDepth ≤ stack.length) : jsonPush stack f = .error .tooDeep := by
  simp [jsonPush, h]

/-- The member of an object with this name, compared without regard to ASCII
    case (as Go's `encoding/json`, which geth uses, matches field names). -/
def Json.field? (j : Json) (name : String) : Option Json :=
  match j with
  | .obj members => (members.find? fun kv => kv.1.toLower == name.toLower).map (·.2)
  | _ => none

def Json.str? : Json → Option String
  | .str s => some s
  | _ => none

def Json.nat? : Json → Option Nat
  | .num (.ofNat n) => some n
  | _ => none

/-- A JSON string literal for `s`, quotes included. -/
def jsonQuote (s : String) : String :=
  let body := s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\""
    else if c == '\\' then acc ++ "\\\\"
    else if c.toNat < 0x20 then
      let n := c.toNat
      let hex := fun (d : Nat) => Char.ofNat (if d < 10 then 48 + d else 87 + d)
      ((acc ++ "\\u00").push (hex (n / 16))).push (hex (n % 16))
    else acc.push c) ""
  "\"" ++ body ++ "\""

end EthereumWallet.Keys
