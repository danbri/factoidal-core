/-!
# L4Factoidal.JS.Base64 — the base64 and hex algorithms of Uint8Array (ECMA-262 2026, §23.3.2)

`Uint8Array.fromBase64`, `fromHex`, `prototype.setFromBase64`, `setFromHex`, `toBase64` and
`toHex` (the proposal-arraybuffer-base64 algorithms FromBase64, FromHex, DecodeBase64Chunk):
pure functions on the characters of the string, so the evaluator only converts arguments and
moves bytes. Every loop is bounded by the input's length.
-/

namespace L4Factoidal.JS.Base64

def stdAlphabet : Array Char :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/".toList.toArray

/-- The value of a character of the standard base64 alphabet. -/
def val (c : Char) : Option Nat :=
  let n := c.toNat
  if 65 ≤ n && n ≤ 90 then some (n - 65)
  else if 97 ≤ n && n ≤ 122 then some (n - 71)
  else if 48 ≤ n && n ≤ 57 then some (n + 4)
  else if c == '+' then some 62 else if c == '/' then some 63 else none

/-- ASCII whitespace (U+0009, U+000A, U+000C, U+000D, U+0020). -/
def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c.toNat == 12 || c == '\r'

/-- The index of the first character at or after `i` that is not ASCII whitespace. -/
def skipWs (s : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  for _ in [i:s.size] do
    if j < s.size && isWs s[j]! then j := j + 1 else break
  return j

/-- The outcome of FromBase64 or FromHex: characters read, the bytes, and whether it ended in
an error (a SyntaxError). -/
structure Res where
  read : Nat
  bytes : Array UInt8
  err : Bool
  deriving Inhabited

/-- DecodeBase64Chunk: 2 to 4 characters' values to 1 to 3 bytes; `none` when `strict` and the
unused bits are not zero. -/
def decodeChunk (vs : Array Nat) (strict : Bool) : Option (Array UInt8) :=
  let k := vs.size
  let v := (vs ++ Array.replicate (4 - k) 0).foldl (fun a x => a * 64 + x) 0
  let b0 := (v / 65536) % 256
  let b1 := (v / 256) % 256
  let b2 := v % 256
  if k == 2 then (if strict && b1 != 0 then none else some #[b0.toUInt8])
  else if k == 3 then (if strict && b2 != 0 then none else some #[b0.toUInt8, b1.toUInt8])
  else some #[b0.toUInt8, b1.toUInt8, b2.toUInt8]

/-- FromBase64 (lastChunkHandling: 0 loose, 1 strict, 2 stop-before-partial). -/
def fromBase64 (s : Array Char) (url : Bool) (lch : Nat) (maxLength : Nat) : Res := Id.run do
  if maxLength == 0 then return { read := 0, bytes := #[], err := false }
  let len := s.size
  let mut read := 0
  let mut bytes : Array UInt8 := #[]
  let mut chunk : Array Nat := #[]
  let mut i := 0
  for _ in [0:len + 2] do
    i := skipWs s i
    if i == len then
      if chunk.size > 0 then
        if lch == 2 then return { read, bytes, err := false }
        if lch == 1 || chunk.size == 1 then return { read, bytes, err := true }
        match decodeChunk chunk false with
        | some bs => bytes := bytes ++ bs
        | none => return { read, bytes, err := true }
      return { read := len, bytes, err := false }
    let c := s[i]!
    i := i + 1
    if c == '=' then
      if chunk.size < 2 then return { read, bytes, err := true }
      i := skipWs s i
      if chunk.size == 2 then
        if i == len then
          if lch == 2 then return { read, bytes, err := false }
          return { read, bytes, err := true }
        if s[i]! == '=' then
          i := i + 1
          i := skipWs s i
      if i < len then return { read, bytes, err := true }
      match decodeChunk chunk (lch == 1) with
      | some bs => return { read := len, bytes := bytes ++ bs, err := false }
      | none => return { read, bytes, err := true }
    let c := if url then (if c == '+' || c == '/' then ' ' else if c == '-' then '+' else if c == '_' then '/' else c) else c
    let some v := val c | return { read, bytes, err := true }
    let remaining := maxLength - bytes.size
    if (remaining == 1 && chunk.size == 2) || (remaining == 2 && chunk.size == 3) then
      return { read, bytes, err := false }
    chunk := chunk.push v
    if chunk.size == 4 then
      bytes := bytes ++ ((decodeChunk chunk false).getD #[])
      chunk := #[]
      read := i
      if bytes.size == maxLength then return { read, bytes, err := false }
  return { read, bytes, err := true }

def hexVal (c : Char) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)
  else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else if 65 ≤ n && n ≤ 70 then some (n - 55) else none

/-- FromHex: pairs of hexadecimal digits, at most `maxLength` bytes. -/
def fromHex (s : Array Char) (maxLength : Nat) : Res := Id.run do
  if s.size % 2 != 0 then return { read := 0, bytes := #[], err := true }
  let mut read := 0
  let mut bytes : Array UInt8 := #[]
  for _ in [0:s.size / 2] do
    if read ≥ s.size || bytes.size ≥ maxLength then break
    match hexVal s[read]!, hexVal s[read + 1]! with
    | some a, some b => bytes := bytes.push (a * 16 + b).toUInt8; read := read + 2
    | _, _ => return { read, bytes, err := true }
  return { read, bytes, err := false }

/-- The base64 text of bytes (`url`: the base64url alphabet; `pad`: with `=`). -/
def toBase64 (bs : ByteArray) (url pad : Bool) : String := Id.run do
  let ch (v : Nat) : Char :=
    let c := stdAlphabet[v % 64]!
    if url then (if c == '+' then '-' else if c == '/' then '_' else c) else c
  let mut out := ""
  let n := bs.size
  for k in [0:(n + 2) / 3] do
    let i := 3 * k
    let b0 := bs[i]!.toNat
    let b1 := if i + 1 < n then bs[i + 1]!.toNat else 0
    let b2 := if i + 2 < n then bs[i + 2]!.toNat else 0
    let v := b0 * 65536 + b1 * 256 + b2
    out := out.push (ch (v / 262144)) |>.push (ch (v / 4096))
    if i + 1 < n then out := out.push (ch (v / 64)) else if pad then out := out.push '='
    if i + 2 < n then out := out.push (ch v) else if pad then out := out.push '='
  return out

def toHex (bs : ByteArray) : String := Id.run do
  let d := "0123456789abcdef".toList.toArray
  let mut out := ""
  for b in bs.toList do out := out.push d[b.toNat / 16]! |>.push d[b.toNat % 16]!
  return out

#guard toBase64 "hello".toUTF8 false true = "aGVsbG8=" && toBase64 "hello".toUTF8 false false = "aGVsbG8"
#guard (fromBase64 "aGVsbG8=".toList.toArray false 0 1000).bytes = "hello".toUTF8.data
#guard (fromBase64 "aGVsbG8".toList.toArray false 1 1000).err && !(fromBase64 "aGVsbG8".toList.toArray false 0 1000).err
#guard (fromHex "0aFf".toList.toArray 10).bytes = #[10, 255] && (fromHex "0g".toList.toArray 10).err
#guard toHex (ByteArray.mk #[0, 171]) = "00ab"

/-- A full chunk (four characters) is three bytes, whatever the strictness. -/
theorem decodeChunk_four (vs : Array Nat) (strict : Bool) (h : vs.size = 4) :
    (decodeChunk vs strict).map Array.size = some 3 := by
  simp [decodeChunk, h]

end L4Factoidal.JS.Base64
