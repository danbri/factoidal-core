import L4Factoidal.Paralliverse.StaticPack

/-!
# Bounded stable-pack input and output

The v1 packet contains three little-endian u32 header words (version, row count,
bank word count), followed by `(sourceStart, length)` pairs in logical row order
and then a separate word bank. Source starts are word indices relative to the
bank. The encoder stores rows in reverse physical order, with a nonzero pad
before every row. Empty rows use the same convention as other rows.
-/

namespace L4Factoidal.Paralliverse.PackWire

open StaticPack (Rows)

def version : Nat := 1
def maxRows : Nat := 128
def maxWords : Nat := 1024
def maxEditorBytes : Nat := 16 * 1024
def maxBankWords : Nat := maxRows + maxWords
def maxPacketBytes : Nat := 4 * (3 + 2 * maxRows + maxBankWords)

inductive Error where
  | invalid (message : String)
  | limit (message : String)
  deriving Repr

private inductive EditorPhase where
  | start | rowOrEnd | nextRow | wordOrEnd | nextWord
  | digits | wordDelimiter | rowDelimiter | done
  deriving BEq

private def whitespace (byte : Nat) : Bool :=
  byte == 32 || byte == 9 || byte == 10 || byte == 13

/-- Parse the editor's array of arrays of unsigned decimal u32 words. No row
or word is admitted after its limit, and each digit is checked before narrowing. -/
def parseEditor (src : ByteArray) : Except Error Rows := do
  if src.size > maxEditorBytes then
    throw (.limit "The input exceeds 16 KiB.")
  let mut phase := EditorPhase.start
  let mut rows : Rows := []
  let mut row : List UInt32 := []
  let mut rowCount := 0
  let mut wordCount := 0
  let mut value := 0
  for i in [:src.size] do
    let byte := src[i]!.toNat
    let digit := 48 ≤ byte && byte ≤ 57
    if phase == .digits then
      if digit then
        if value == 0 then
          throw (.invalid "A decimal word has a leading zero.")
        value := value * 10 + (byte - 48)
        if value ≥ UInt32.size then
          throw (.invalid "A word exceeds 4294967295.")
        continue
      row := UInt32.ofNat value :: row
      phase := .wordDelimiter
    if whitespace byte then
      continue
    match phase with
    | .start =>
      if byte != 91 then throw (.invalid "Start the outer array with '['.")
      phase := .rowOrEnd
    | .rowOrEnd | .nextRow =>
      if phase == .rowOrEnd && byte == 93 then
        phase := .done
      else
        if byte != 91 then throw (.invalid "Start each row with '['.")
        if rowCount == maxRows then throw (.limit "Use at most 128 rows.")
        rowCount := rowCount + 1
        phase := .wordOrEnd
    | .wordOrEnd | .nextWord | .wordDelimiter =>
      if phase != .nextWord && byte == 93 then
        rows := row.reverse :: rows
        row := []
        phase := .rowDelimiter
      else if phase == .wordDelimiter then
        if byte != 44 then throw (.invalid "Use a comma between words.")
        phase := .nextWord
      else
        if !digit then throw (.invalid "Use unsigned decimal words.")
        if wordCount == maxWords then throw (.limit "Use at most 1024 words.")
        wordCount := wordCount + 1
        value := byte - 48
        phase := .digits
    | .rowDelimiter =>
      if byte == 93 then phase := .done
      else if byte == 44 then phase := .nextRow
      else throw (.invalid "Use a comma between rows or close the outer array with ']'.")
    | .digits | .done => throw (.invalid "Unexpected input after the array.")
  if phase != .done then throw (.invalid "Close the rows and outer array with ']'.")
  return rows.reverse

private def pushU32 (dst : ByteArray) (word : Nat) : ByteArray :=
  let dst := dst.push (UInt8.ofNat (word % 256))
  let dst := dst.push (UInt8.ofNat ((word / 256) % 256))
  let dst := dst.push (UInt8.ofNat ((word / 65536) % 256))
  dst.push (UInt8.ofNat ((word / 16777216) % 256))

/-- Read a little-endian word. The caller checks that all four bytes are present. -/
def readU32 (src : ByteArray) (word : Nat) : Nat :=
  let i := 4 * word
  src[i]!.toNat + 256 * src[i + 1]!.toNat +
    65536 * src[i + 2]!.toNat + 16777216 * src[i + 3]!.toNat

def outputWords (words : List UInt32) : ByteArray :=
  words.foldl (fun dst word => pushU32 dst word.toNat) ByteArray.empty

def encode (rows : Rows) : Except Error ByteArray := do
  let rowCount := rows.length
  if rowCount > maxRows then throw (.limit "Use at most 128 rows.")
  let wordCount := rows.foldl (fun n row => n + row.length) 0
  if wordCount > maxWords then throw (.limit "Use at most 1024 words.")
  let bankSize := rowCount + wordCount
  let mut dst := pushU32 (pushU32 (pushU32 ByteArray.empty version) rowCount) bankSize
  let mut bankEnd := bankSize
  for row in rows do
    let len := row.length
    dst := pushU32 (pushU32 dst (bankEnd - len)) len
    bankEnd := bankEnd - len - 1
  for row in rows.reverse do
    dst := pushU32 dst 2654435769
    for word in row do
      dst := pushU32 dst word.toNat
  return dst

/-- Start and length in bank words, stored in the descriptor for logical row i. -/
def descriptorAt (src : ByteArray) (i : Nat) : Nat × Nat :=
  (readU32 src (3 + 2 * i), readU32 src (4 + 2 * i))

/-- Check the descriptors in input order and retain their spans. The range error for
a descriptor precedes its cumulative word-limit error. -/
def readSpans (src : ByteArray) (bankSize : Nat) :
    List Nat → Nat → List (Nat × Nat) → Except Error (List (Nat × Nat))
  | [], _, rev => .ok rev.reverse
  | i :: rest, used, rev =>
    let span := descriptorAt src i
    if span.1 + span.2 > bankSize then .error (.invalid "A row source range exceeds the bank.")
    else if used + span.2 > maxWords then .error (.limit "Use at most 1024 words.")
    else readSpans src bankSize rest (used + span.2) (span :: rev)

/-- Extract the words of one checked descriptor in local-index order. -/
def readSpan (src : ByteArray) (bankBase : Nat) (span : Nat × Nat) : List UInt32 :=
  (List.range span.2).map fun j => UInt32.ofNat (readU32 src (bankBase + span.1 + j))

/-- Read the physical packet. Validate every descriptor and the combined row
length before extracting words, including when descriptors share source spans. -/
def decode (src : ByteArray) : Except Error Rows :=
  if src.size > maxPacketBytes then .error (.limit "The packet exceeds its byte limit.")
  else if src.size < 12 then .error (.invalid "The packet header is truncated.")
  else if readU32 src 0 ≠ version then .error (.invalid "The packet version is unsupported.")
  else
    let rowCount := readU32 src 1
    let bankSize := readU32 src 2
    if rowCount > maxRows ∨ bankSize > maxBankWords then
      .error (.limit "The packet exceeds its row or bank limit.")
    else
      let bankBase := 3 + 2 * rowCount
      if src.size ≠ 4 * (bankBase + bankSize) then
        .error (.invalid "The packet size does not match its header.")
      else
        match readSpans src bankSize (List.range rowCount) 0 [] with
        | .error e => .error e
        | .ok spans => .ok (spans.map (readSpan src bankBase))

def prepare (src : ByteArray) : Except Error ByteArray := do
  encode (← parseEditor src)

end L4Factoidal.Paralliverse.PackWire
