/-
L4Factoidal.EXPath.Binary.Text — the text encodings of EXPath Binary
4.0 §5 (bin:infer-encoding, bin:decode-string, bin:encode-string),
also used by EXPath File 4.0 (file:read-text, file:write-text).

The decoders are those of the XML parser (`L4Factoidal.XML.Encoding`):
strict UTF-8, UTF-16 with surrogate checks, ISO-8859-1 and US-ASCII.
The encoders are here. Encoding names are compared without regard to
case (Binary 4.0 §5). The supported encodings are the ones every XML
processor reads (XML 1.0 §4.3.3) plus ISO-8859-1 and US-ASCII; any
other name is `unknown-encoding`.
-/
import L4Factoidal.XML.Encoding
import L4Factoidal.XML.Document

namespace L4Factoidal.EXPath.Binary

open L4Factoidal.XML

/-- An encoding this module reads and writes. -/
inductive Enc where
  | utf8 | utf16be | utf16le | latin1 | ascii
deriving DecidableEq, Repr, Inhabited

/-- The encoding a name denotes. `UTF-16` without a byte order mark is
read and written most significant byte first (Binary 4.0
bin:encode-string). -/
def encOfName? (name : String) : Option Enc :=
  match name.toUpper with
  | "UTF-8" | "UTF8" => some .utf8
  | "UTF-16" | "UTF-16BE" | "UTF16" => some .utf16be
  | "UTF-16LE" => some .utf16le
  | "ISO-8859-1" | "LATIN1" | "ISO8859-1" | "ISO_8859-1" | "L1" => some .latin1
  | "US-ASCII" | "ASCII" => some .ascii
  | _ => none

/-- bin:infer-encoding: the effective encoding name and the offset at
which the content starts (after a byte order mark). `none`: the name
is not supported. -/
def inferEncoding (bs : List Nat) (enc : Option String) : Option (String × Nat) :=
  let e := enc.map String.toUpper
  let starts (pre : List Nat) := pre.isPrefixOf bs
  if (e == some "UTF-8" || e.isNone) && starts [0xEF, 0xBB, 0xBF] then some ("UTF-8", 3)
  else if (e == some "UTF-16" || e == some "UTF-16LE" || e.isNone) && starts [0xFF, 0xFE] then some ("UTF-16LE", 2)
  else if (e == some "UTF-16" || e == some "UTF-16BE" || e.isNone) && starts [0xFE, 0xFF] then some ("UTF-16BE", 2)
  else if e == some "UTF-16" then some ("UTF-16BE", 0)
  else match enc with
    | some n => if (encOfName? n).isSome then some (n, 0) else none
    | none => some ("UTF-8", 0)

/-- Decode octets; `none` for malformed input. -/
def decodeWith (enc : Enc) (bs : List Nat) : Option String :=
  let ba := ByteArray.mk (bs.map UInt8.ofNat).toArray
  match enc with
  | .utf8 => (decodeUtf8 ba).toOption
  | .utf16be => (decodeUtf16 ba .big 0).toOption
  | .utf16le => (decodeUtf16 ba .little 0).toOption
  | .latin1 => some (decodeLatin1 ba)
  | .ascii => (decodeAscii ba).toOption

/-- One character as UTF-16 code units. -/
def utf16Units (c : Char) : List Nat :=
  let n := c.toNat
  if n < 0x10000 then [n]
  else let m := n - 0x10000
       [0xD800 + m / 0x400, 0xDC00 + m % 0x400]

/-- Encode a string; `none` when a character cannot be represented. -/
def encodeWith (enc : Enc) (s : String) : Option (List Nat) :=
  match enc with
  | .utf8 => some (s.toUTF8.data.toList.map UInt8.toNat)
  | .utf16be => some (s.toList.flatMap (fun c => (utf16Units c).flatMap (fun u => [u / 256, u % 256])))
  | .utf16le => some (s.toList.flatMap (fun c => (utf16Units c).flatMap (fun u => [u % 256, u / 256])))
  | .latin1 => s.toList.mapM (fun c => if c.toNat < 256 then some c.toNat else none)
  | .ascii => s.toList.mapM (fun c => if c.toNat < 128 then some c.toNat else none)

#guard encodeWith .utf16be "A" == some [0, 65]
#guard encodeWith .utf16le "A" == some [65, 0]
#guard (encodeWith .utf8 "é").bind (decodeWith .utf8) == some "é"
#guard (encodeWith .utf16le "a😀").bind (decodeWith .utf16le) == some "a😀"
#guard inferEncoding [0xEF, 0xBB, 0xBF, 0x41] none == some ("UTF-8", 3)
#guard inferEncoding [0x41] (some "utf-16") == some ("UTF-16BE", 0)
#guard inferEncoding [0x41] (some "x-unknown") == none

end L4Factoidal.EXPath.Binary
