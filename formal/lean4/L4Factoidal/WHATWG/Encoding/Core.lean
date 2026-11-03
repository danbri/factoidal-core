/-
L4Factoidal.WHATWG.Encoding.Core — the WHATWG Encoding Standard in Lean.

Specification: **Encoding Standard**, WHATWG Living Standard, source
https://github.com/whatwg/encoding commit `be17ac5c49881336538acfc7b40dba3c8009144b`
(2026-10-19). Section names below are the names of that text. The label table
and the indexes are generated from the same commit (`Data.lean`).

What this module defines:

  * `getEncoding` (section 4.2, "get an encoding") and `getOutputEncoding`
    (section 4.3).
  * The decoder of every encoding (sections 8 to 14) as a handler
    `Decoder.handle : Decoder → Option UInt8 → DStep`. `none` is
    end-of-queue. A handler result says which items to push, and which
    bytes to restore to the input I/O queue.
  * The encoder of every encoding that has one, as `Encoder.handle`.
  * "process a queue" for decoders and encoders, with the error modes
    "replacement" and "fatal" (decoders) and "fatal" and "html" (encoders).
  * The hooks of section 6: UTF-8 decode, UTF-8 decode without BOM,
    UTF-8 decode without BOM or fail, UTF-8 encode; the legacy hooks
    decode, BOM sniff, encode, get an encoder, encode or fail.
  * The `TextDecoder` and `TextEncoder` algorithms of section 7 as values:
    a `TextDecoder` is its whole internal state (encoding, decoder
    instance, I/O queue, ignore BOM, BOM seen, error mode, do not flush),
    and `TextDecoder.decode` returns the next state with the result.

The I/O queue is the bytes of an array from a position, after a list of
restored bytes (`Queue`). "Restore" in the specification puts items back at
the front of the queue; here it prepends to the list.

## Termination

The "process a queue" loops are tail calls with fuel. A handler that
restores bytes always restores bytes it has read before (section 4.1 and
each decoder), and it changes the decoder state so that the restored bytes
are read in a different state. No byte is read more than four times, so the
fuel `8 × (queue length + 1) + 16` is more than any run needs. If the fuel
ends the loop returns `Outcome.fuel`, which the hooks report as an error;
`tests/whatwg-encoding` has adversarial inputs for every restoring decoder.

No `partial`, no `sorry`.
-/
import Std.Data.HashMap
import L4Factoidal.WHATWG.Encoding.Data

namespace L4Factoidal.WHATWG.Encoding

/-! ## Indexes (section 5) -/

/-- The value that stands for "no code point at this pointer". -/
def nullCp : UInt32 := 0xFFFFFFFF

/-- One hexadecimal field of the generated index text. -/
def parseHexField (s : String) : UInt32 :=
  if s.isEmpty then nullCp
  else (s.foldl (fun (acc : Nat) c =>
      let d := if c ≤ '9' then c.toNat - '0'.toNat
               else if c ≤ 'F' then c.toNat - 'A'.toNat + 10
               else c.toNat - 'a'.toNat + 10
      acc * 16 + d) 0).toUInt32

/-- An index from its generated text: entry `p` is the code point of pointer
`p`, or `nullCp`. -/
def parseIndex (t : String) : Array UInt32 :=
  (t.splitOn ",").foldl (fun a f => a.push (parseHexField f)) #[]

/-- index code point (section 5): the code point of `pointer`, or `none`. -/
def indexCodePoint (idx : Array UInt32) (pointer : Nat) : Option UInt32 :=
  match idx[pointer]? with
  | some v => if v == nullCp then none else some v
  | none => none

/-- The indexes are parsed on first use, not at module initialisation. -/
def idxBig5 : Thunk (Array UInt32) := Thunk.mk fun _ => parseIndex indexText_big5
def idxEucKr : Thunk (Array UInt32) := Thunk.mk fun _ => parseIndex indexText_euc_kr
def idxGb18030 : Thunk (Array UInt32) := Thunk.mk fun _ => parseIndex indexText_gb18030
def idxJis0208 : Thunk (Array UInt32) := Thunk.mk fun _ => parseIndex indexText_jis0208
def idxJis0212 : Thunk (Array UInt32) := Thunk.mk fun _ => parseIndex indexText_jis0212
def idxIso2022JpKatakana : Thunk (Array UInt32) :=
  Thunk.mk fun _ => parseIndex indexText_iso_2022_jp_katakana

/-- index gb18030 ranges: `(pointer, code point)` pairs in increasing order. -/
def idxGb18030Ranges : Thunk (Array (Nat × Nat)) := Thunk.mk fun _ =>
  (indexText_gb18030_ranges.splitOn ",").foldl (fun a f =>
    match f.splitOn ":" with
    | [p, c] => a.push ((parseHexField p).toNat, (parseHexField c).toNat)
    | _ => a) #[]

/-- The reverse of an index: code point to its FIRST pointer ("index
pointer", section 5), over the pointers that `keep` admits. Pointers are
inserted from the last to the first, so the first one stays. -/
def reverseIndex (idx : Array UInt32) (keep : Nat → Bool) : Std.HashMap UInt32 Nat :=
  let n := idx.size
  (List.range n).foldl (fun m i =>
    let p := n - 1 - i
    let v := idx[p]!
    if v == nullCp || !keep p then m else m.insert v p) {}

def revGb18030 : Thunk (Std.HashMap UInt32 Nat) :=
  Thunk.mk fun _ => reverseIndex idxGb18030.get (fun _ => true)
def revEucKr : Thunk (Std.HashMap UInt32 Nat) :=
  Thunk.mk fun _ => reverseIndex idxEucKr.get (fun _ => true)
def revJis0208 : Thunk (Std.HashMap UInt32 Nat) :=
  Thunk.mk fun _ => reverseIndex idxJis0208.get (fun _ => true)
/-- index Shift_JIS pointer: index jis0208 without pointers 8272 to 8835. -/
def revShiftJis : Thunk (Std.HashMap UInt32 Nat) :=
  Thunk.mk fun _ => reverseIndex idxJis0208.get (fun p => p < 8272 || p > 8835)
/-- index Big5 pointer: index Big5 without pointers below (0xA1 − 0x81) × 157;
for U+2550, U+255E, U+2561, U+256A, U+5341 and U+5345 the LAST pointer. -/
def revBig5 : Thunk (Std.HashMap UInt32 Nat) := Thunk.mk fun _ =>
  let idx := idxBig5.get
  let first := reverseIndex idx (fun p => p ≥ (0xA1 - 0x81) * 157)
  let lastOf := fun (cp : UInt32) (m : Std.HashMap UInt32 Nat) =>
    let r := (List.range idx.size).foldl (fun acc p =>
      if p ≥ (0xA1 - 0x81) * 157 && idx[p]! == cp then some p else acc) none
    match r with
    | some p => m.insert cp p
    | none => m
  [0x2550, 0x255E, 0x2561, 0x256A, 0x5341, 0x5345].foldl (fun m cp => lastOf cp m) first

/-- index gb18030 ranges code point (section 5). -/
def gb18030RangesCodePoint (pointer : Nat) : Option UInt32 :=
  if (pointer > 39419 && pointer < 189000) || pointer > 1237575 then none
  else if pointer == 7457 then some 0xE7C7
  else
    let r := idxGb18030Ranges.get.foldl (fun acc (p, c) => if p ≤ pointer then (p, c) else acc) (0, 0x80)
    some (r.2 + pointer - r.1).toUInt32

/-- index gb18030 ranges pointer (section 5). -/
def gb18030RangesPointer (cp : Nat) : Nat :=
  if cp == 0xE7C7 then 7457
  else
    let r := idxGb18030Ranges.get.foldl (fun acc (p, c) => if c ≤ cp then (p, c) else acc) (0, 0x80)
    r.1 + cp - r.2

/-! ## Names and labels (section 4.2) -/

/-- ASCII whitespace (Infra): TAB, LF, FF, CR, SPACE. -/
def isAsciiWhitespace (c : Char) : Bool :=
  c == '\t' || c == '\n' || c == '\x0C' || c == '\r' || c == ' '

/-- ASCII lowercase (Infra): only A to Z change. -/
def asciiLower (s : String) : String :=
  s.map fun c => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- Remove leading and trailing ASCII whitespace (Infra "strip"). -/
def stripAsciiWhitespace (s : String) : String :=
  let cs := s.toList
  let cs := cs.dropWhile isAsciiWhitespace
  let cs := (cs.reverse.dropWhile isAsciiWhitespace).reverse
  String.ofList cs

/-- get an encoding (section 4.2). -/
def getEncoding (label : String) : Option Encoding :=
  let l := asciiLower (stripAsciiWhitespace label)
  (labelTable.find? (fun (k, _) => k == l)).map (·.2)

/-- get an output encoding (section 4.3). -/
def getOutputEncoding : Encoding → Encoding
  | .replacement | .utf_16be | .utf_16le => .utf_8
  | e => e

/-! ## Decoders -/

/-- The states of the ISO-2022-JP decoder (section 12.2.1). -/
inductive IsoState where
  | ascii | roman | katakana | leadByte | trailByte | escapeStart | escape
  deriving DecidableEq, Repr, Inhabited, BEq

/-- A decoder instance: one constructor per decoder, with that decoder's
state variables. -/
inductive Decoder where
  /-- UTF-8 code point, bytes seen, bytes needed, lower and upper boundary. -/
  | utf8 (cp : UInt32) (seen needed : Nat) (lower upper : UInt8)
  /-- The single-byte decoder over its index single-byte. -/
  | singleByte (idx : Array UInt32)
  | gb18030 (first second third : UInt8)
  | big5 (lead : UInt8)
  | eucJp (jis0212 : Bool) (lead : UInt8)
  /-- decoder state, decoder output state, leading, output. -/
  | iso2022jp (st outSt : IsoState) (lead : UInt8) (output : Bool)
  | shiftJis (lead : UInt8)
  | eucKr (lead : UInt8)
  | replacement (errorReturned : Bool)
  /-- is UTF-16BE decoder, UTF-16 leading byte, UTF-16 leading surrogate. -/
  | utf16 (be : Bool) (leadByte : Option UInt8) (leadSurrogate : Option UInt32)
  | xUserDefined
  deriving Inhabited

/-- What a decoder handler returns (section 4.1). -/
inductive DResult where
  | finished
  | items (cps : List UInt32)
  | error
  | cont
  deriving DecidableEq, Repr, Inhabited

/-- One handler run: the next decoder state, the result, and the bytes to
restore to the front of the input queue, in order. -/
structure DStep where
  dec : Decoder
  result : DResult
  restore : List UInt8 := []
  deriving Inhabited

def utf8Initial : Decoder := .utf8 0 0 0 0x80 0xBF

/-- A new instance of the decoder of an encoding. -/
def Encoding.decoder (e : Encoding) : Decoder :=
  match e with
  | .utf_8 => utf8Initial
  | .gbk | .gb18030 => .gb18030 0 0 0
  | .big5 => .big5 0
  | .euc_jp => .eucJp false 0
  | .iso_2022_jp => .iso2022jp .ascii .ascii 0 false
  | .shift_jis => .shiftJis 0
  | .euc_kr => .eucKr 0
  | .replacement => .replacement false
  | .utf_16be => .utf16 true none none
  | .utf_16le => .utf16 false none none
  | .x_user_defined => .xUserDefined
  | e => .singleByte (parseIndex (singleByteIndexText e))

@[inline] def isAscii (b : UInt8) : Bool := b ≤ 0x7F

/-- UTF-8 decoder handler (section 8.1.1). -/
def utf8Handle (cp : UInt32) (seen needed : Nat) (lower upper : UInt8) :
    Option UInt8 → DStep
  | none =>
    if needed != 0 then ⟨.utf8 cp seen 0 lower upper, .error, []⟩
    else ⟨.utf8 cp seen needed lower upper, .finished, []⟩
  | some b =>
    if needed == 0 then
      if b ≤ 0x7F then ⟨.utf8 cp seen needed lower upper, .items [b.toUInt32], []⟩
      else if 0xC2 ≤ b && b ≤ 0xDF then
        ⟨.utf8 (b &&& 0x1F).toUInt32 seen 1 lower upper, .cont, []⟩
      else if 0xE0 ≤ b && b ≤ 0xEF then
        let lower := if b == 0xE0 then 0xA0 else lower
        let upper := if b == 0xED then 0x9F else upper
        ⟨.utf8 (b &&& 0xF).toUInt32 seen 2 lower upper, .cont, []⟩
      else if 0xF0 ≤ b && b ≤ 0xF4 then
        let lower := if b == 0xF0 then 0x90 else lower
        let upper := if b == 0xF4 then 0x8F else upper
        ⟨.utf8 (b &&& 0x7).toUInt32 seen 3 lower upper, .cont, []⟩
      else ⟨.utf8 cp seen needed lower upper, .error, []⟩
    else if b < lower || b > upper then
      ⟨utf8Initial, .error, [b]⟩
    else
      let cp' := (cp <<< 6) ||| (b &&& 0x3F).toUInt32
      if seen + 1 != needed then ⟨.utf8 cp' (seen + 1) needed 0x80 0xBF, .cont, []⟩
      else ⟨.utf8 0 0 0 0x80 0xBF, .items [cp'], []⟩

/-- Restore a byte only when it is an ASCII byte (several legacy decoders). -/
@[inline] def restoreIfAscii (b : UInt8) : List UInt8 := if isAscii b then [b] else []

/-- gb18030 decoder handler (section 10.2.1). -/
def gb18030Handle (first second third : UInt8) : Option UInt8 → DStep
  | none =>
    if first == 0 && second == 0 && third == 0 then ⟨.gb18030 0 0 0, .finished, []⟩
    else ⟨.gb18030 0 0 0, .error, []⟩
  | some b =>
    if third != 0 then
      if !(0x30 ≤ b && b ≤ 0x39) then ⟨.gb18030 0 0 0, .error, [second, third, b]⟩
      else
        let p := (first.toNat - 0x81) * (10 * 126 * 10) + (second.toNat - 0x30) * (10 * 126)
          + (third.toNat - 0x81) * 10 + b.toNat - 0x30
        match gb18030RangesCodePoint p with
        | none => ⟨.gb18030 0 0 0, .error, []⟩
        | some cp => ⟨.gb18030 0 0 0, .items [cp], []⟩
    else if second != 0 then
      if 0x81 ≤ b && b ≤ 0xFE then ⟨.gb18030 first second b, .cont, []⟩
      else ⟨.gb18030 0 0 third, .error, [second, b]⟩
    else if first != 0 then
      if 0x30 ≤ b && b ≤ 0x39 then ⟨.gb18030 first b third, .cont, []⟩
      else
        let offset : Nat := if b < 0x7F then 0x40 else 0x41
        let pointer : Option Nat :=
          if (0x40 ≤ b && b ≤ 0x7E) || (0x80 ≤ b && b ≤ 0xFE) then
            some ((first.toNat - 0x81) * 190 + (b.toNat - offset))
          else none
        match pointer.bind (indexCodePoint idxGb18030.get) with
        | some cp => ⟨.gb18030 0 second third, .items [cp], []⟩
        | none => ⟨.gb18030 0 second third, .error, restoreIfAscii b⟩
    else if isAscii b then ⟨.gb18030 0 0 0, .items [b.toUInt32], []⟩
    else if b == 0x80 then ⟨.gb18030 0 0 0, .items [0x20AC], []⟩
    else if 0x81 ≤ b && b ≤ 0xFE then ⟨.gb18030 b 0 0, .cont, []⟩
    else ⟨.gb18030 0 0 0, .error, []⟩

/-- Big5 decoder handler (section 11.1.1). -/
def big5Handle (lead : UInt8) : Option UInt8 → DStep
  | none => if lead != 0 then ⟨.big5 0, .error, []⟩ else ⟨.big5 0, .finished, []⟩
  | some b =>
    if lead != 0 then
      let offset : Nat := if b < 0x7F then 0x40 else 0x62
      let pointer : Option Nat :=
        if (0x40 ≤ b && b ≤ 0x7E) || (0xA1 ≤ b && b ≤ 0xFE) then
          some ((lead.toNat - 0x81) * 157 + (b.toNat - offset))
        else none
      match pointer with
      | some 1133 => ⟨.big5 0, .items [0x00CA, 0x0304], []⟩
      | some 1135 => ⟨.big5 0, .items [0x00CA, 0x030C], []⟩
      | some 1164 => ⟨.big5 0, .items [0x00EA, 0x0304], []⟩
      | some 1166 => ⟨.big5 0, .items [0x00EA, 0x030C], []⟩
      | _ =>
        match pointer.bind (indexCodePoint idxBig5.get) with
        | some cp => ⟨.big5 0, .items [cp], []⟩
        | none => ⟨.big5 0, .error, restoreIfAscii b⟩
    else if isAscii b then ⟨.big5 0, .items [b.toUInt32], []⟩
    else if 0x81 ≤ b && b ≤ 0xFE then ⟨.big5 b, .cont, []⟩
    else ⟨.big5 0, .error, []⟩

/-- EUC-JP decoder handler (section 12.1.1). -/
def eucJpHandle (jis0212 : Bool) (lead : UInt8) : Option UInt8 → DStep
  | none =>
    if lead != 0 then ⟨.eucJp jis0212 0, .error, []⟩ else ⟨.eucJp jis0212 0, .finished, []⟩
  | some b =>
    if lead == 0x8E && 0xA1 ≤ b && b ≤ 0xDF then
      ⟨.eucJp jis0212 0, .items [0xFF61 - 0xA1 + b.toUInt32], []⟩
    else if lead == 0x8F && 0xA1 ≤ b && b ≤ 0xFE then
      ⟨.eucJp true b, .cont, []⟩
    else if lead != 0 then
      let cp : Option UInt32 :=
        if 0xA1 ≤ lead && lead ≤ 0xFE && 0xA1 ≤ b && b ≤ 0xFE then
          indexCodePoint (if jis0212 then idxJis0212.get else idxJis0208.get)
            ((lead.toNat - 0xA1) * 94 + b.toNat - 0xA1)
        else none
      match cp with
      | some c => ⟨.eucJp false 0, .items [c], []⟩
      | none => ⟨.eucJp false 0, .error, restoreIfAscii b⟩
    else if isAscii b then ⟨.eucJp jis0212 0, .items [b.toUInt32], []⟩
    else if b == 0x8E || b == 0x8F || (0xA1 ≤ b && b ≤ 0xFE) then ⟨.eucJp jis0212 b, .cont, []⟩
    else ⟨.eucJp jis0212 0, .error, []⟩

/-- ISO-2022-JP decoder handler (section 12.2.1). -/
def iso2022jpHandle (st outSt : IsoState) (lead : UInt8) (output : Bool) :
    Option UInt8 → DStep
  | item =>
    let mk (st outSt : IsoState) (lead : UInt8) (output : Bool) (r : DResult)
        (restore : List UInt8 := []) : DStep := ⟨.iso2022jp st outSt lead output, r, restore⟩
    match st with
    | .ascii =>
      match item with
      | some 0x1B => mk .escapeStart outSt lead output .cont
      | some b =>
        if b ≤ 0x7F && b != 0x0E && b != 0x0F then mk st outSt lead false (.items [b.toUInt32])
        else mk st outSt lead false .error
      | none => mk st outSt lead output .finished
    | .roman =>
      match item with
      | some 0x1B => mk .escapeStart outSt lead output .cont
      | some 0x5C => mk st outSt lead false (.items [0x00A5])
      | some 0x7E => mk st outSt lead false (.items [0x203E])
      | some b =>
        if b ≤ 0x7F && b != 0x0E && b != 0x0F then mk st outSt lead false (.items [b.toUInt32])
        else mk st outSt lead false .error
      | none => mk st outSt lead output .finished
    | .katakana =>
      match item with
      | some 0x1B => mk .escapeStart outSt lead output .cont
      | some b =>
        if 0x21 ≤ b && b ≤ 0x5F then mk st outSt lead false (.items [0xFF61 - 0x21 + b.toUInt32])
        else mk st outSt lead false .error
      | none => mk st outSt lead output .finished
    | .leadByte =>
      match item with
      | some 0x1B => mk .escapeStart outSt lead output .cont
      | some b =>
        if 0x21 ≤ b && b ≤ 0x7E then mk .trailByte outSt b false .cont
        else mk st outSt lead false .error
      | none => mk st outSt lead output .finished
    | .trailByte =>
      match item with
      | some 0x1B => mk .escapeStart outSt lead output .error
      | some b =>
        if 0x21 ≤ b && b ≤ 0x7E then
          let p := (lead.toNat - 0x21) * 94 + b.toNat - 0x21
          match indexCodePoint idxJis0208.get p with
          | some cp => mk .leadByte outSt lead output (.items [cp])
          | none => mk .leadByte outSt lead output .error
        else mk .leadByte outSt lead output .error
      | none => mk .leadByte outSt lead output .error
    | .escapeStart =>
      match item with
      | some b =>
        if b == 0x24 || b == 0x28 then mk .escape outSt b output .cont
        else mk outSt outSt lead false .error [b]
      | none => mk outSt outSt lead false .error []
    | .escape =>
      let l := lead
      let state : Option IsoState :=
        match item with
        | some 0x42 => if l == 0x28 then some .ascii else if l == 0x24 then some .leadByte else none
        | some 0x4A => if l == 0x28 then some .roman else none
        | some 0x49 => if l == 0x28 then some .katakana else none
        | some 0x40 => if l == 0x24 then some .leadByte else none
        | _ => none
      match state with
      | some s => mk s s 0 true (if output then .error else .cont)
      | none =>
        let restore := match item with | none => [l] | some b => [l, b]
        mk outSt outSt 0 false .error restore

/-- Shift_JIS decoder handler (section 12.3.1). -/
def shiftJisHandle (lead : UInt8) : Option UInt8 → DStep
  | none => if lead != 0 then ⟨.shiftJis 0, .error, []⟩ else ⟨.shiftJis 0, .finished, []⟩
  | some b =>
    if lead != 0 then
      let offset : Nat := if b < 0x7F then 0x40 else 0x41
      let leadOffset : Nat := if lead < 0xA0 then 0x81 else 0xC1
      let pointer : Option Nat :=
        if (0x40 ≤ b && b ≤ 0x7E) || (0x80 ≤ b && b ≤ 0xFC) then
          some ((lead.toNat - leadOffset) * 188 + b.toNat - offset)
        else none
      match pointer with
      | some p =>
        if 8836 ≤ p && p ≤ 10715 then ⟨.shiftJis 0, .items [(0xE000 - 8836 + p).toUInt32], []⟩
        else match indexCodePoint idxJis0208.get p with
          | some cp => ⟨.shiftJis 0, .items [cp], []⟩
          | none => ⟨.shiftJis 0, .error, restoreIfAscii b⟩
      | none => ⟨.shiftJis 0, .error, restoreIfAscii b⟩
    else if isAscii b || b == 0x80 then ⟨.shiftJis 0, .items [b.toUInt32], []⟩
    else if 0xA1 ≤ b && b ≤ 0xDF then ⟨.shiftJis 0, .items [0xFF61 - 0xA1 + b.toUInt32], []⟩
    else if (0x81 ≤ b && b ≤ 0x9F) || (0xE0 ≤ b && b ≤ 0xFC) then ⟨.shiftJis b, .cont, []⟩
    else ⟨.shiftJis 0, .error, []⟩

/-- EUC-KR decoder handler (section 13.1.1). -/
def eucKrHandle (lead : UInt8) : Option UInt8 → DStep
  | none => if lead != 0 then ⟨.eucKr 0, .error, []⟩ else ⟨.eucKr 0, .finished, []⟩
  | some b =>
    if lead != 0 then
      let pointer : Option Nat :=
        if 0x41 ≤ b && b ≤ 0xFE then some ((lead.toNat - 0x81) * 190 + (b.toNat - 0x41)) else none
      match pointer.bind (indexCodePoint idxEucKr.get) with
      | some cp => ⟨.eucKr 0, .items [cp], []⟩
      | none => ⟨.eucKr 0, .error, restoreIfAscii b⟩
    else if isAscii b then ⟨.eucKr 0, .items [b.toUInt32], []⟩
    else if 0x81 ≤ b && b ≤ 0xFE then ⟨.eucKr b, .cont, []⟩
    else ⟨.eucKr 0, .error, []⟩

/-- shared UTF-16 decoder handler (section 14.2.1). -/
def utf16Handle (be : Bool) (leadByte : Option UInt8) (leadSurrogate : Option UInt32) :
    Option UInt8 → DStep
  | none =>
    if leadByte.isSome || leadSurrogate.isSome then ⟨.utf16 be none none, .error, []⟩
    else ⟨.utf16 be none none, .finished, []⟩
  | some b =>
    match leadByte with
    | none => ⟨.utf16 be (some b) leadSurrogate, .cont, []⟩
    | some lb =>
      let cu : UInt32 :=
        if be then (lb.toUInt32 <<< 8) + b.toUInt32 else (b.toUInt32 <<< 8) + lb.toUInt32
      match leadSurrogate with
      | some ls =>
        if 0xDC00 ≤ cu && cu ≤ 0xDFFF then
          ⟨.utf16 be none none, .items [(0x10000 : UInt32) + ((ls - 0xD800) <<< 10) + (cu - 0xDC00)], []⟩
        else
          let b1 := (cu >>> 8).toUInt8
          let b2 := (cu &&& 0xFF).toUInt8
          ⟨.utf16 be none none, .error, if be then [b1, b2] else [b2, b1]⟩
      | none =>
        if 0xD800 ≤ cu && cu ≤ 0xDBFF then ⟨.utf16 be none (some cu), .cont, []⟩
        else if 0xDC00 ≤ cu && cu ≤ 0xDFFF then ⟨.utf16 be none none, .error, []⟩
        else ⟨.utf16 be none none, .items [cu], []⟩

/-- A decoder's handler, given the next item (`none` is end-of-queue). -/
def Decoder.handle : Decoder → Option UInt8 → DStep
  | .utf8 cp seen needed lower upper, i => utf8Handle cp seen needed lower upper i
  | .singleByte idx, none => ⟨.singleByte idx, .finished, []⟩
  | .singleByte idx, some b =>
    if isAscii b then ⟨.singleByte idx, .items [b.toUInt32], []⟩
    else match indexCodePoint idx (b.toNat - 0x80) with
      | some cp => ⟨.singleByte idx, .items [cp], []⟩
      | none => ⟨.singleByte idx, .error, []⟩
  | .gb18030 f s t, i => gb18030Handle f s t i
  | .big5 l, i => big5Handle l i
  | .eucJp j l, i => eucJpHandle j l i
  | .iso2022jp st o l out, i => iso2022jpHandle st o l out i
  | .shiftJis l, i => shiftJisHandle l i
  | .eucKr l, i => eucKrHandle l i
  | .replacement r, none => ⟨.replacement r, .finished, []⟩
  | .replacement r, some _ =>
    if !r then ⟨.replacement true, .error, []⟩ else ⟨.replacement r, .finished, []⟩
  | .utf16 be lb ls, i => utf16Handle be lb ls i
  | .xUserDefined, none => ⟨.xUserDefined, .finished, []⟩
  | .xUserDefined, some b =>
    if isAscii b then ⟨.xUserDefined, .items [b.toUInt32], []⟩
    else ⟨.xUserDefined, .items [0xF780 + b.toUInt32 - 0x80], []⟩

/-! ## I/O queues and "process a queue" (section 4.1) -/

/-- An I/O queue of bytes: restored bytes, then `data` from `pos`. -/
structure Queue where
  front : List UInt8 := []
  data : ByteArray := ByteArray.empty
  pos : Nat := 0
  deriving Inhabited

def Queue.ofBytes (bs : ByteArray) : Queue := { data := bs }

def Queue.length (q : Queue) : Nat := q.front.length + (q.data.size - q.pos)

/-- read an item; `none` when the queue has no more bytes. -/
@[inline] def Queue.read (q : Queue) : Option (UInt8 × Queue) :=
  match q.front with
  | b :: rest => some (b, { q with front := rest })
  | [] => if h : q.pos < q.data.size then some (q.data[q.pos], { q with pos := q.pos + 1 }) else none

/-- The bytes left in the queue, as one array. -/
def Queue.rest (q : Queue) : ByteArray :=
  ByteArray.mk q.front.toArray ++ q.data.extract q.pos q.data.size

/-- push bytes to the end of the queue. -/
def Queue.push (q : Queue) (bs : ByteArray) : Queue :=
  if q.front.isEmpty && q.pos == q.data.size then { data := bs } else { data := q.rest ++ bs }

/-- Error modes of a decoder (section 4.1). -/
inductive DecodeMode where
  | replacement | fatal
  deriving DecidableEq, Repr, Inhabited

/-- How a run of "process a queue" ended. -/
inductive Outcome where
  /-- The handler returned finished (end-of-queue was processed). -/
  | finished
  /-- The handler returned error in mode "fatal". -/
  | error
  /-- The queue had no more bytes and the caller asked not to process
  end-of-queue (`TextDecoder` with do not flush). -/
  | exhausted
  /-- The fuel ended; see "Termination" in the module header. -/
  | fuel
  deriving DecidableEq, Repr, Inhabited

@[inline] def pushItems (out : Array UInt32) : List UInt32 → Array UInt32
  | [] => out
  | c :: cs => pushItems (out.push c) cs

/-- process a queue (section 4.1) for a decoder. With `stopAtEnd` the run
stops when the queue has no more bytes, without processing end-of-queue. -/
def decodeLoop (fuel : Nat) (d : Decoder) (q : Queue) (out : Array UInt32)
    (mode : DecodeMode) (stopAtEnd : Bool) : Decoder × Queue × Array UInt32 × Outcome :=
  match fuel with
  | 0 => (d, q, out, .fuel)
  | fuel + 1 =>
    let (item, q') := match q.read with
      | some (b, q') => (some b, q')
      | none => (none, q)
    if item.isNone && stopAtEnd then (d, q, out, .exhausted)
    else
      let s := d.handle item
      let q'' := { q' with front := s.restore ++ q'.front }
      match s.result with
      | .finished => (s.dec, q'', out, .finished)
      | .items cps => decodeLoop fuel s.dec q'' (pushItems out cps) mode stopAtEnd
      | .cont => decodeLoop fuel s.dec q'' out mode stopAtEnd
      | .error =>
        match mode with
        | .replacement => decodeLoop fuel s.dec q'' (out.push 0xFFFD) mode stopAtEnd
        | .fatal => (s.dec, q'', out, .error)

def fuelFor (q : Queue) : Nat := 8 * (q.length + 1) + 16

def decodeQueue (d : Decoder) (q : Queue) (mode : DecodeMode) (stopAtEnd := false) :
    Decoder × Queue × Array UInt32 × Outcome :=
  decodeLoop (fuelFor q) d q #[] mode stopAtEnd

/-- Code points to a Lean string. Every decoder emits scalar values only. -/
def cpsToString (cps : Array UInt32) : String :=
  cps.foldl (fun s c => s.push (Char.ofNat c.toNat)) ""

/-! ## Hooks for standards (section 6) -/

/-- BOM sniff (section 6.1). -/
def bomSniff (bs : ByteArray) : Option Encoding :=
  let b (i : Nat) : Option UInt8 := bs[i]?
  if b 0 == some 0xEF && b 1 == some 0xBB && b 2 == some 0xBF then some .utf_8
  else if b 0 == some 0xFE && b 1 == some 0xFF then some .utf_16be
  else if b 0 == some 0xFF && b 1 == some 0xFE then some .utf_16le
  else none

/-- decode (section 6.1): BOM sniff, then the fallback encoding's decoder in
mode "replacement". Returns the code points. -/
def decodeCps (bs : ByteArray) (fallback : Encoding) : Array UInt32 :=
  let (enc, skip) := match bomSniff bs with
    | some .utf_8 => (Encoding.utf_8, 3)
    | some e => (e, 2)
    | none => (fallback, 0)
  let q : Queue := { data := bs, pos := skip }
  (decodeQueue enc.decoder q .replacement).2.2.1

def decode (bs : ByteArray) (fallback : Encoding) : String := cpsToString (decodeCps bs fallback)

/-- UTF-8 decode (section 6). -/
def utf8DecodeCps (bs : ByteArray) : Array UInt32 :=
  let skip := if bs[0]? == some 0xEF && bs[1]? == some 0xBB && bs[2]? == some 0xBF then 3 else 0
  (decodeQueue utf8Initial { data := bs, pos := skip } .replacement).2.2.1

def utf8Decode (bs : ByteArray) : String := cpsToString (utf8DecodeCps bs)

/-- UTF-8 decode without BOM (section 6). -/
def utf8DecodeWithoutBOM (bs : ByteArray) : String :=
  cpsToString (decodeQueue utf8Initial (Queue.ofBytes bs) .replacement).2.2.1

/-- UTF-8 decode without BOM or fail (section 6): `none` is failure. -/
def utf8DecodeWithoutBOMOrFail (bs : ByteArray) : Option String :=
  let (_, _, out, o) := decodeQueue utf8Initial (Queue.ofBytes bs) .fatal
  if o == .finished then some (cpsToString out) else none

/-! ## Encoders -/

/-- The ISO-2022-JP encoder state (section 12.2.2). -/
inductive IsoEncState where
  | ascii | roman | jis0208
  deriving DecidableEq, Repr, Inhabited, BEq

/-- An encoder instance. -/
inductive Encoder where
  | utf8
  /-- The single-byte encoder: code point to its first pointer in index single-byte. -/
  | singleByte (rev : Std.HashMap UInt32 Nat)
  | gb18030 (isGBK : Bool)
  | big5
  | eucJp
  | iso2022jp (st : IsoEncState)
  | shiftJis
  | eucKr
  | xUserDefined
  deriving Inhabited

/-- What an encoder handler returns (section 4.1). -/
inductive EResult where
  | finished
  | bytes (bs : List UInt8)
  | error (cp : UInt32)
  | cont
  deriving DecidableEq, Repr, Inhabited

structure EStep where
  enc : Encoder
  result : EResult
  restore : List UInt32 := []
  deriving Inhabited

/-- get an encoder (section 6.1): `none` for replacement and UTF-16BE/LE,
which have no encoder. -/
def getEncoder : Encoding → Option Encoder
  | .replacement | .utf_16be | .utf_16le => none
  | .utf_8 => some .utf8
  | .gbk => some (.gb18030 true)
  | .gb18030 => some (.gb18030 false)
  | .big5 => some .big5
  | .euc_jp => some .eucJp
  | .iso_2022_jp => some (.iso2022jp .ascii)
  | .shift_jis => some .shiftJis
  | .euc_kr => some .eucKr
  | .x_user_defined => some .xUserDefined
  | e => some (.singleByte (reverseIndex (parseIndex (singleByteIndexText e)) (fun _ => true)))

/-- UTF-8 encoder bytes of one code point (section 8.1.2). -/
def utf8EncodeCp (cp : UInt32) : List UInt8 :=
  if cp ≤ 0x7F then [cp.toUInt8]
  else
    let (count, offset) : Nat × UInt32 :=
      if cp ≤ 0x7FF then (1, 0xC0) else if cp ≤ 0xFFFF then (2, 0xE0) else (3, 0xF0)
    let first := ((cp >>> (6 * count).toUInt32) + offset).toUInt8
    let rest := (List.range count).reverse.map fun k =>
      (0x80 ||| ((cp >>> (6 * k).toUInt32) &&& 0x3F)).toUInt8
    first :: rest

/-- gb18030 encoder side table of section 10.2.2. -/
def gb18030EncoderTable : List (UInt32 × UInt8 × UInt8) :=
  [(0xE78D, 0xA6, 0xD9), (0xE78E, 0xA6, 0xDA), (0xE78F, 0xA6, 0xDB), (0xE790, 0xA6, 0xDC),
   (0xE791, 0xA6, 0xDD), (0xE792, 0xA6, 0xDE), (0xE793, 0xA6, 0xDF), (0xE794, 0xA6, 0xEC),
   (0xE795, 0xA6, 0xED), (0xE796, 0xA6, 0xF3), (0xE81E, 0xFE, 0x59), (0xE826, 0xFE, 0x61),
   (0xE82B, 0xFE, 0x66), (0xE82C, 0xFE, 0x67), (0xE832, 0xFE, 0x6D), (0xE843, 0xFE, 0x7E),
   (0xE854, 0xFE, 0x90), (0xE864, 0xFE, 0xA0)]

def gb18030EncHandle (isGBK : Bool) (cp : UInt32) : EResult :=
  if cp ≤ 0x7F then .bytes [cp.toUInt8]
  else if cp == 0xE5E5 then .error cp
  else if isGBK && cp == 0x20AC then .bytes [0x80]
  else match gb18030EncoderTable.find? (·.1 == cp) with
    | some (_, b1, b2) => .bytes [b1, b2]
    | none =>
      match revGb18030.get[cp]? with
      | some p =>
        let trailing := p % 190
        let offset := if trailing < 0x3F then 0x40 else 0x41
        .bytes [(p / 190 + 0x81).toUInt8, (trailing + offset).toUInt8]
      | none =>
        if isGBK then .error cp
        else
          let p := gb18030RangesPointer cp.toNat
          let b1 := p / (10 * 126 * 10)
          let p := p % (10 * 126 * 10)
          let b2 := p / (10 * 126)
          let p := p % (10 * 126)
          .bytes [(b1 + 0x81).toUInt8, (b2 + 0x30).toUInt8, (p / 10 + 0x81).toUInt8,
                  (p % 10 + 0x30).toUInt8]

def big5EncHandle (cp : UInt32) : EResult :=
  if cp ≤ 0x7F then .bytes [cp.toUInt8]
  else match revBig5.get[cp]? with
    | none => .error cp
    | some p =>
      let trailing := p % 157
      let offset := if trailing < 0x3F then 0x40 else 0x62
      .bytes [(p / 157 + 0x81).toUInt8, (trailing + offset).toUInt8]

def eucJpEncHandle (cp : UInt32) : EResult :=
  if cp ≤ 0x7F then .bytes [cp.toUInt8]
  else if cp == 0xA5 then .bytes [0x5C]
  else if cp == 0x203E then .bytes [0x7E]
  else if 0xFF61 ≤ cp && cp ≤ 0xFF9F then .bytes [0x8E, (cp - 0xFF61 + 0xA1).toUInt8]
  else
    let cp' := if cp == 0x2212 then 0xFF0D else cp
    match revJis0208.get[cp']? with
    | none => .error cp'
    | some p => .bytes [(p / 94 + 0xA1).toUInt8, (p % 94 + 0xA1).toUInt8]

def iso2022jpEncHandle (st : IsoEncState) : Option UInt32 → EStep
  | none =>
    if st != .ascii then ⟨.iso2022jp .ascii, .bytes [0x1B, 0x28, 0x42], []⟩
    else ⟨.iso2022jp st, .finished, []⟩
  | some cp =>
    let me (r : EResult) (st' := st) (restore : List UInt32 := []) : EStep :=
      ⟨.iso2022jp st', r, restore⟩
    let asciiCp := cp ≤ 0x7F
    if (st == .ascii || st == .roman) && (cp == 0x0E || cp == 0x0F || cp == 0x1B) then
      me (.error 0xFFFD)
    else if st == .ascii && asciiCp then me (.bytes [cp.toUInt8])
    else if st == .roman && ((asciiCp && cp != 0x5C && cp != 0x7E) || cp == 0xA5 || cp == 0x203E) then
      if asciiCp then me (.bytes [cp.toUInt8])
      else if cp == 0xA5 then me (.bytes [0x5C])
      else me (.bytes [0x7E])
    else if asciiCp && st != .ascii then me (.bytes [0x1B, 0x28, 0x42]) .ascii [cp]
    else if (cp == 0xA5 || cp == 0x203E) && st != .roman then
      me (.bytes [0x1B, 0x28, 0x4A]) .roman [cp]
    else
      let cp := if cp == 0x2212 then 0xFF0D else cp
      let cp := if 0xFF61 ≤ cp && cp ≤ 0xFF9F then
          (indexCodePoint idxIso2022JpKatakana.get (cp - 0xFF61).toNat).getD cp
        else cp
      match revJis0208.get[cp]? with
      | none =>
        if st == .jis0208 then me (.bytes [0x1B, 0x28, 0x42]) .ascii [cp]
        else me (.error cp)
      | some p =>
        if st != .jis0208 then me (.bytes [0x1B, 0x24, 0x42]) .jis0208 [cp]
        else me (.bytes [(p / 94 + 0x21).toUInt8, (p % 94 + 0x21).toUInt8])

def shiftJisEncHandle (cp : UInt32) : EResult :=
  if cp ≤ 0x80 then .bytes [cp.toUInt8]
  else if cp == 0xA5 then .bytes [0x5C]
  else if cp == 0x203E then .bytes [0x7E]
  else if 0xFF61 ≤ cp && cp ≤ 0xFF9F then .bytes [(cp - 0xFF61 + 0xA1).toUInt8]
  else
    let cp' := if cp == 0x2212 then 0xFF0D else cp
    match revShiftJis.get[cp']? with
    | none => .error cp'
    | some p =>
      let lead := p / 188
      let leadOffset := if lead < 0x1F then 0x81 else 0xC1
      let trailing := p % 188
      let offset := if trailing < 0x3F then 0x40 else 0x41
      .bytes [(lead + leadOffset).toUInt8, (trailing + offset).toUInt8]

def eucKrEncHandle (cp : UInt32) : EResult :=
  if cp ≤ 0x7F then .bytes [cp.toUInt8]
  else match revEucKr.get[cp]? with
    | none => .error cp
    | some p => .bytes [(p / 190 + 0x81).toUInt8, (p % 190 + 0x41).toUInt8]

/-- An encoder's handler, given the next item (`none` is end-of-queue). -/
def Encoder.handle : Encoder → Option UInt32 → EStep
  | .iso2022jp st, i => iso2022jpEncHandle st i
  | e, none => ⟨e, .finished, []⟩
  | .utf8, some cp => ⟨.utf8, .bytes (utf8EncodeCp cp), []⟩
  | .singleByte rev, some cp =>
    if cp ≤ 0x7F then ⟨.singleByte rev, .bytes [cp.toUInt8], []⟩
    else match rev[cp]? with
      | some p => ⟨.singleByte rev, .bytes [(p + 0x80).toUInt8], []⟩
      | none => ⟨.singleByte rev, .error cp, []⟩
  | .gb18030 g, some cp => ⟨.gb18030 g, gb18030EncHandle g cp, []⟩
  | .big5, some cp => ⟨.big5, big5EncHandle cp, []⟩
  | .eucJp, some cp => ⟨.eucJp, eucJpEncHandle cp, []⟩
  | .shiftJis, some cp => ⟨.shiftJis, shiftJisEncHandle cp, []⟩
  | .eucKr, some cp => ⟨.eucKr, eucKrEncHandle cp, []⟩
  | .xUserDefined, some cp =>
    if cp ≤ 0x7F then ⟨.xUserDefined, .bytes [cp.toUInt8], []⟩
    else if 0xF780 ≤ cp && cp ≤ 0xF7FF then ⟨.xUserDefined, .bytes [(cp - 0xF780 + 0x80).toUInt8], []⟩
    else ⟨.xUserDefined, .error cp, []⟩

/-- An I/O queue of scalar values. -/
structure CpQueue where
  front : List UInt32 := []
  data : Array UInt32 := #[]
  pos : Nat := 0
  deriving Inhabited

def CpQueue.length (q : CpQueue) : Nat := q.front.length + (q.data.size - q.pos)

@[inline] def CpQueue.read (q : CpQueue) : Option (UInt32 × CpQueue) :=
  match q.front with
  | c :: rest => some (c, { q with front := rest })
  | [] => if h : q.pos < q.data.size then some (q.data[q.pos], { q with pos := q.pos + 1 }) else none

/-- Error modes of an encoder (section 4.1). -/
inductive EncodeMode where
  | fatal | html
  deriving DecidableEq, Repr, Inhabited

/-- The decimal digits of `n`, as ASCII bytes. -/
def decimalBytes (n : Nat) : List UInt8 := (toString n).toList.map (·.toNat.toUInt8)

@[inline] def pushBytes (out : ByteArray) : List UInt8 → ByteArray
  | [] => out
  | b :: bs => pushBytes (out.push b) bs

/-- process a queue (section 4.1) for an encoder. The result's last
component is the code point of a fatal error, if one ended the run. -/
def encodeLoop (fuel : Nat) (e : Encoder) (q : CpQueue) (out : ByteArray) (mode : EncodeMode) :
    Encoder × CpQueue × ByteArray × Outcome × Option UInt32 :=
  match fuel with
  | 0 => (e, q, out, .fuel, none)
  | fuel + 1 =>
    let (item, q') := match q.read with
      | some (c, q') => (some c, q')
      | none => (none, q)
    let s := e.handle item
    let q'' := { q' with front := s.restore ++ q'.front }
    match s.result with
    | .finished => (s.enc, q'', out, .finished, none)
    | .bytes bs => encodeLoop fuel s.enc q'' (pushBytes out bs) mode
    | .cont => encodeLoop fuel s.enc q'' out mode
    | .error cp =>
      match mode with
      | .html => encodeLoop fuel s.enc q''
          (pushBytes out ([0x26, 0x23] ++ decimalBytes cp.toNat ++ [0x3B])) mode
      | .fatal => (s.enc, q'', out, .error, some cp)

def cpFuelFor (q : CpQueue) : Nat := 8 * (q.length + 1) + 16

/-- encode (section 6.1): the encoder in mode "html". `none` for an encoding
with no encoder (the caller is to use get an output encoding first). -/
def encode (cps : Array UInt32) (enc : Encoding) : Option ByteArray :=
  (getEncoder enc).map fun e =>
    let q : CpQueue := { data := cps }
    (encodeLoop (cpFuelFor q) e q ByteArray.empty .html).2.2.1

/-- encode or fail (section 6.1): run the encoder in mode "fatal" until it
finishes or fails; returns the encoder and queue to continue with, the
bytes, and the code point of the error (`none` when it finished). -/
def encodeOrFail (q : CpQueue) (e : Encoder) : Encoder × CpQueue × ByteArray × Option UInt32 :=
  let (e', q', out, o, err) := encodeLoop (cpFuelFor q) e q ByteArray.empty .fatal
  match o with
  | .error => (e', q', out, err)
  | .fuel => (e', q', out, some 0xFFFD)
  | _ => (e', q', out, none)

/-- UTF-8 encode (section 6). -/
def utf8Encode (cps : Array UInt32) : ByteArray :=
  cps.foldl (fun out c => pushBytes out (utf8EncodeCp c)) ByteArray.empty

/-! ## Web IDL strings and the API (section 7) -/

/-- Web IDL USVString conversion of a sequence of UTF-16 code units: a
surrogate pair becomes its scalar value, a lone surrogate becomes U+FFFD.
Also returns, for each scalar value, the number of code units it used. -/
def usvFromUtf16 (units : Array UInt16) : Array (UInt32 × Nat) := Id.run do
  let mut out : Array (UInt32 × Nat) := #[]
  let mut i := 0
  for _ in [0:units.size] do
    if h : i < units.size then
      let u := units[i].toUInt32
      if 0xD800 ≤ u && u ≤ 0xDBFF then
        match units[i + 1]? with
        | some v =>
          let v := v.toUInt32
          if 0xDC00 ≤ v && v ≤ 0xDFFF then
            out := out.push ((0x10000 : UInt32) + ((u - 0xD800) <<< 10) + (v - 0xDC00), 2)
            i := i + 2
          else
            out := out.push (0xFFFD, 1)
            i := i + 1
        | none =>
          out := out.push (0xFFFD, 1)
          i := i + 1
      else if 0xDC00 ≤ u && u ≤ 0xDFFF then
        out := out.push (0xFFFD, 1)
        i := i + 1
      else
        out := out.push (u, 1)
        i := i + 1
  return out

/-- Scalar values to UTF-16 code units (for a JavaScript string). -/
def cpsToUtf16 (cps : Array UInt32) : Array UInt16 :=
  cps.foldl (fun (out : Array UInt16) (c : UInt32) =>
    if c < 0x10000 then out.push c.toUInt16
    else
      let v := c - 0x10000
      (out.push ((0xD800 : UInt32) + (v >>> 10)).toUInt16).push ((0xDC00 : UInt32) + (v &&& 0x3FF)).toUInt16) #[]

/-- A `TextDecoder` object (sections 7.1 and 7.2): every internal slot. -/
structure TextDecoder where
  encoding : Encoding
  errorMode : DecodeMode
  ignoreBOM : Bool
  bomSeen : Bool := false
  doNotFlush : Bool := false
  decoder : Decoder
  queue : Queue := {}
  deriving Inhabited

/-- `new TextDecoder(label, options)`: `none` is a RangeError. -/
def TextDecoder.new? (label : String) (fatal ignoreBOM : Bool) : Option TextDecoder :=
  match getEncoding label with
  | none | some .replacement => none
  | some e => some { encoding := e, errorMode := if fatal then .fatal else .replacement,
                     ignoreBOM, decoder := e.decoder }

/-- The `encoding` getter: the name, ASCII lowercased. -/
def TextDecoder.encodingName (td : TextDecoder) : String := asciiLower td.encoding.name

/-- serialize I/O queue (section 7.1). -/
def TextDecoder.serialize (td : TextDecoder) (cps : Array UInt32) : TextDecoder × Array UInt32 :=
  let bomEnc := td.encoding == .utf_8 || td.encoding == .utf_16be || td.encoding == .utf_16le
  if bomEnc && !td.ignoreBOM && !td.bomSeen && cps.size > 0 then
    ({ td with bomSeen := true }, if cps[0]! == 0xFEFF then cps.extract 1 cps.size else cps)
  else (td, cps)

/-- `decode(input, options)` (section 7.2): the next state, and the output
code points or `none` for a TypeError. -/
def TextDecoder.decode (td : TextDecoder) (input : Option ByteArray) (stream : Bool) :
    TextDecoder × Option (Array UInt32) :=
  let td := if !td.doNotFlush then
      { td with decoder := td.encoding.decoder, queue := {}, bomSeen := false } else td
  let td := { td with doNotFlush := stream }
  let td := match input with
    | some bs => { td with queue := td.queue.push bs }
    | none => td
  let (d, q, out, o) := decodeQueue td.decoder td.queue td.errorMode (stopAtEnd := td.doNotFlush)
  let td := { td with decoder := d, queue := q }
  match o with
  | .finished | .exhausted =>
    let (td, cps) := td.serialize out
    (td, some cps)
  | .error | .fuel => (td, none)

/-- decode and enqueue a chunk (section 7.5, `TextDecoderStream`): push the
chunk, process items until the queue has no more bytes; the output chunk, or
`none` for a TypeError. The decoder instance is never replaced. -/
def TextDecoder.streamChunk (td : TextDecoder) (chunk : ByteArray) :
    TextDecoder × Option (Array UInt32) :=
  let td := { td with queue := td.queue.push chunk }
  let (d, q, out, o) := decodeQueue td.decoder td.queue td.errorMode (stopAtEnd := true)
  let td := { td with decoder := d, queue := q }
  match o with
  | .finished | .exhausted => let (td, cps) := td.serialize out; (td, some cps)
  | .error | .fuel => (td, none)

/-- flush and enqueue (section 7.5): process end-of-queue. -/
def TextDecoder.streamFlush (td : TextDecoder) : TextDecoder × Option (Array UInt32) :=
  let (d, q, out, o) := decodeQueue td.decoder td.queue td.errorMode
  let td := { td with decoder := d, queue := q }
  match o with
  | .finished => let (td, cps) := td.serialize out; (td, some cps)
  | _ => (td, none)

/-- A `TextEncoderStream` (section 7.6): its leading surrogate. -/
structure TextEncoderStream where
  leadingSurrogate : Option UInt32 := none
  deriving Inhabited

/-- encode and enqueue a chunk (section 7.6) with "convert code unit to scalar
value": a surrogate pair split between chunks is joined. -/
def TextEncoderStream.chunk (s : TextEncoderStream) (units : Array UInt16) :
    TextEncoderStream × ByteArray :=
  let isLead (u : UInt32) := 0xD800 ≤ u && u ≤ 0xDBFF
  let isTrail (u : UInt32) := 0xDC00 ≤ u && u ≤ 0xDFFF
  -- One code unit is read per round and at most one is restored, after which
  -- the leading surrogate is null; 2 × size + 1 rounds suffice.
  let rec go (fuel : Nat) (i : Nat) (lead : Option UInt32) (out : ByteArray) :
      Option UInt32 × ByteArray :=
    match fuel with
    | 0 => (lead, out)
    | fuel + 1 =>
      match units[i]? with
      | none => (lead, out)
      | some u =>
        let u := u.toUInt32
        match lead with
        | some l =>
          if isTrail u then
            go fuel (i + 1) none (pushBytes out (utf8EncodeCp ((0x10000 : UInt32) + ((l - 0xD800) <<< 10) + (u - 0xDC00))))
          else go fuel i none (pushBytes out (utf8EncodeCp 0xFFFD))
        | none =>
          if isLead u then go fuel (i + 1) (some u) out
          else if isTrail u then go fuel (i + 1) none (pushBytes out (utf8EncodeCp 0xFFFD))
          else go fuel (i + 1) none (pushBytes out (utf8EncodeCp u))
  let (lead, out) := go (2 * units.size + 1) 0 s.leadingSurrogate ByteArray.empty
  ({ leadingSurrogate := lead }, out)

/-- encode and flush (section 7.6). -/
def TextEncoderStream.flush (s : TextEncoderStream) : ByteArray :=
  if s.leadingSurrogate.isSome then ByteArray.mk #[0xEF, 0xBF, 0xBD] else ByteArray.empty

/-- `TextEncoder.encode(input)` (section 7.4) over UTF-16 code units. -/
def textEncoderEncode (units : Array UInt16) : ByteArray :=
  utf8Encode ((usvFromUtf16 units).map (·.1))

/-- `TextEncoder.encodeInto(source, destination)` (section 7.4): `read` in
code units, `written` in bytes, and the bytes written. -/
def textEncoderEncodeInto (units : Array UInt16) (destLength : Nat) : Nat × Nat × ByteArray :=
  (usvFromUtf16 units).foldl (fun (acc : Nat × Nat × ByteArray × Bool) (cp, n) =>
    let (read, written, out, stopped) := acc
    if stopped then acc
    else
      let bs := utf8EncodeCp cp
      if destLength - written ≥ bs.length then
        (read + n, written + bs.length, pushBytes out bs, false)
      else (read, written, out, true)) (0, 0, ByteArray.empty, false)
  |> fun (r, w, out, _) => (r, w, out)

end L4Factoidal.WHATWG.Encoding
