/-
L4Factoidal.XML.Encoding — from the bytes of an XML entity to its text.

Section numbers cite **Extensible Markup Language (XML) 1.0 (Fifth
Edition)**, https://www.w3.org/TR/xml/ : §4.3.3 (Character Encoding in
Entities) and Appendix F (Autodetection of Character Encodings,
non-normative).

`Parser.lean` parses a Lean `String`. An XML entity is a sequence of
BYTES, and which characters those bytes mean depends on an encoding that
the entity itself announces. This module is the step between the two.

## What `decodeXmlBytes` does

  1. **Detect the family** from the first four bytes (Appendix F.1): a
     byte order mark (`EF BB BF` UTF-8, `FE FF` or `FF FE` UTF-16), the
     bytes of `<?` in UTF-16 without a mark (`00 3C 00 3F`,
     `3C 00 3F 00`), a four-byte form (UCS-4, not implemented), EBCDIC
     (not implemented), or anything else, which is an ASCII-compatible
     8-bit family: UTF-8 unless a declaration says otherwise.
  2. **Read the encoding declaration** (`[80] EncodingDecl`, in the
     `[23] XMLDecl` of a document or the `[77] TextDecl` of an external
     entity) from the beginning of the entity. For an 8-bit family this
     reads ASCII, as Appendix F.2 describes; for UTF-16 the text is
     decoded first.
  3. **Check the declaration against the family** (§4.3.3). It is a
     fatal error for an entity that carries an encoding declaration to
     be presented in an encoding other than the one it names, for an
     entity that begins with neither a byte order mark nor an encoding
     declaration to be in anything but UTF-8, for UTF-16 to lack its
     byte order mark, and for the bytes to be illegal in the encoding
     they are in.
  4. **Decode** with the encoding the declaration names.

Encodings implemented: UTF-8, UTF-16 (little and big endian, with and
without a byte order mark), ISO-8859-1 and US-ASCII. A declaration
naming any other encoding yields `DecodeError.unsupported` with the name
as written, so a caller can report "not supported: <name>" rather than a
wrong verdict. An unsupported encoding is not a conflict and not
malformed bytes: the entity may well be fine.

## Totality

No `partial`, no `sorry`. Every loop runs over an index bounded by the
byte array's size.
-/
import L4Factoidal.XML.Parser

namespace L4Factoidal.XML

/-! ## Errors -/

/-- Why the bytes of an entity could not be turned into text. -/
inductive DecodeError where
  /-- The entity is in an encoding this decoder does not implement.
  The string is the name as the entity declares it, or a family name
  (`UCS-4`, `EBCDIC`) for an entity whose first bytes show it. The
  entity may be perfectly well-formed. -/
  | unsupported (encoding : String) : DecodeError
  /-- The bytes are not legal in the encoding the entity is in: invalid
  UTF-8 (including encoded surrogates and code points above U+10FFFF), an
  unpaired UTF-16 surrogate, an odd number of bytes in UTF-16, a byte
  above 127 in US-ASCII. §4.3.3: a fatal error. -/
  | invalid (message : String) : DecodeError
  /-- The encoding declaration disagrees with what the bytes are, or the
  entity lacks what its family requires (§4.3.3). A fatal error. -/
  | conflict (message : String) : DecodeError
deriving DecidableEq, Repr, Inhabited

/-- The text of a decoding error. -/
def DecodeError.message : DecodeError → String
  | .unsupported e => "the entity is in an encoding this processor cannot read: " ++ e
  | .invalid m => m
  | .conflict m => m

/-! ## Bytes -/

/-- Byte `i`, or 0 past the end. `ByteArray.get!` reads in constant time;
`bs.data` would copy the whole array into a boxed `Array UInt8` on every
call (measured 2026-10-10: a 200 KB UTF-16 document took minutes). -/
def byteAt (bs : ByteArray) (i : Nat) : Nat :=
  if i < bs.size then (bs.get! i).toNat else 0

/-- Whether `bs` begins with these bytes. -/
def startsWithBytes (bs : ByteArray) (pre : List Nat) : Bool :=
  bs.size ≥ pre.length && (pre.zipIdx.all fun (b, i) => byteAt bs i == b)

/-! ## Detection — Appendix F.1 -/

/-- The byte order of a UTF-16 entity. -/
inductive Endian where
  | big
  | little
deriving DecidableEq, Repr, Inhabited

/-- The family of an entity's encoding, from its first four bytes
(Appendix F.1). -/
inductive ByteFamily where
  /-- `EF BB BF`. -/
  | utf8Bom
  /-- `FE FF` (big) or `FF FE` (little), not followed by `00 00`. -/
  | utf16Bom (order : Endian)
  /-- `00 3C 00 3F` or `3C 00 3F 00`: the characters `<?` in UTF-16
  with no byte order mark. -/
  | utf16Bare (order : Endian)
  /-- Four-byte forms; the name says which. Not implemented. -/
  | ucs4 (name : String)
  /-- `4C 6F A7 94`: `<?xm` in EBCDIC. Not implemented. -/
  | ebcdic
  /-- Everything else: the bytes of `<?xm` in an ASCII-compatible
  8-bit encoding, or an entity with no declaration, which is UTF-8. -/
  | asciiCompatible
deriving DecidableEq, Repr, Inhabited

/-- Appendix F.1's table. The four-byte orders come first because a
UTF-16 byte order mark is a prefix of the UCS-4 one in little-endian
order (`FF FE 00 00`). -/
def detectFamily (bs : ByteArray) : ByteFamily :=
  if startsWithBytes bs [0x00, 0x00, 0xFE, 0xFF] then .ucs4 "UCS-4 (1234 order, with byte order mark)"
  else if startsWithBytes bs [0xFF, 0xFE, 0x00, 0x00] then .ucs4 "UCS-4 (4321 order, with byte order mark)"
  else if startsWithBytes bs [0x00, 0x00, 0xFF, 0xFE] then .ucs4 "UCS-4 (2143 order, with byte order mark)"
  else if startsWithBytes bs [0xFE, 0xFF, 0x00, 0x00] then .ucs4 "UCS-4 (3412 order, with byte order mark)"
  else if startsWithBytes bs [0xFE, 0xFF] then .utf16Bom .big
  else if startsWithBytes bs [0xFF, 0xFE] then .utf16Bom .little
  else if startsWithBytes bs [0xEF, 0xBB, 0xBF] then .utf8Bom
  else if startsWithBytes bs [0x00, 0x00, 0x00, 0x3C] then .ucs4 "UCS-4 (1234 order)"
  else if startsWithBytes bs [0x3C, 0x00, 0x00, 0x00] then .ucs4 "UCS-4 (4321 order)"
  else if startsWithBytes bs [0x00, 0x00, 0x3C, 0x00] then .ucs4 "UCS-4 (2143 order)"
  else if startsWithBytes bs [0x00, 0x3C, 0x00, 0x00] then .ucs4 "UCS-4 (3412 order)"
  else if startsWithBytes bs [0x00, 0x3C, 0x00, 0x3F] then .utf16Bare .big
  else if startsWithBytes bs [0x3C, 0x00, 0x3F, 0x00] then .utf16Bare .little
  else if startsWithBytes bs [0x4C, 0x6F, 0xA7, 0x94] then .ebcdic
  else .asciiCompatible

/-! ## Decoders -/

/-- UTF-8. `String.fromUTF8?` accepts exactly the well-formed UTF-8 of
the Unicode standard: no overlong forms, no surrogates, nothing above
U+10FFFF. -/
def decodeUtf8 (bs : ByteArray) : Except DecodeError String :=
  match String.fromUTF8? bs with
  | some s => .ok s
  | none => .error (.invalid
      "the entity is not well-formed UTF-8 (XML 1.0 section 4.3.3: illegal byte sequence)")

/-- ISO-8859-1: byte `b` is the character U+00`b`. Every byte is legal. -/
def decodeLatin1 (bs : ByteArray) : String :=
  String.ofList (bs.data.toList.map (fun b => Char.ofNat b.toNat))

/-- US-ASCII: bytes 0-127; anything above is illegal. -/
def decodeAscii (bs : ByteArray) : Except DecodeError String :=
  if bs.data.all (fun b => b.toNat < 0x80) then .ok (decodeLatin1 bs)
  else .error (.invalid "the entity declares US-ASCII but has a byte above 127 (XML 1.0 section 4.3.3)")

/-- The 16-bit code unit at byte offset `i`. -/
def utf16Unit (bs : ByteArray) (order : Endian) (i : Nat) : Nat :=
  let a := byteAt bs i
  let b := byteAt bs (i + 1)
  match order with
  | .big => a * 256 + b
  | .little => b * 256 + a

/-- The units of UTF-16 from byte offset `start` on, as characters.
A high surrogate must be followed by a low one and a low surrogate must
follow a high one; either alone is illegal (§4.3.3). `fuel` is the
number of units left. -/
def utf16Chars (bs : ByteArray) (order : Endian) (i : Nat) (acc : Array Char) :
    Nat → Except DecodeError (Array Char)
  | 0 => .ok acc
  | fuel + 1 =>
    if i + 1 ≥ bs.size then .ok acc
    else
      let u := utf16Unit bs order i
      if 0xD800 ≤ u && u ≤ 0xDBFF then
        if i + 3 < bs.size then
          let v := utf16Unit bs order (i + 2)
          if 0xDC00 ≤ v && v ≤ 0xDFFF then
            utf16Chars bs order (i + 4)
              (acc.push (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (v - 0xDC00)))) fuel
          else .error (.invalid "UTF-16: a high surrogate is not followed by a low surrogate (XML 1.0 section 4.3.3)")
        else .error (.invalid "UTF-16: a high surrogate at the end of the entity (XML 1.0 section 4.3.3)")
      else if 0xDC00 ≤ u && u ≤ 0xDFFF then
        .error (.invalid "UTF-16: a low surrogate with no high surrogate before it (XML 1.0 section 4.3.3)")
      else utf16Chars bs order (i + 2) (acc.push (Char.ofNat u)) fuel

/-- UTF-16 from byte offset `start`. An odd number of bytes is illegal. -/
def decodeUtf16 (bs : ByteArray) (order : Endian) (start : Nat) : Except DecodeError String :=
  if (bs.size - start) % 2 == 1 then
    .error (.invalid "UTF-16: an odd number of bytes (XML 1.0 section 4.3.3)")
  else
    match utf16Chars bs order start #[] ((bs.size - start) / 2 + 1) with
    | .error e => .error e
    | .ok cs => .ok (String.ofList cs.toList)

/-! ## Encoding names — §4.3.3 -/

/-- Encoding names are case-insensitive (§4.3.3). -/
def encKey (name : String) : String := name.toLower

/-- UTF-8, by the name §4.3.3 requires (`utf8` is accepted as well). -/
def isUtf8Label (name : String) : Bool := encKey name == "utf-8" || encKey name == "utf8"

/-- ISO-8859-1 under its IANA name and aliases. -/
def isLatin1Label (name : String) : Bool :=
  ["iso-8859-1", "iso_8859-1", "iso_8859-1:1987", "latin1", "l1", "iso-ir-100",
   "cp819", "ibm819", "csisolatin1"].contains (encKey name)

/-- US-ASCII under its IANA name and common aliases. -/
def isAsciiLabel (name : String) : Bool :=
  ["us-ascii", "ascii", "ansi_x3.4-1968", "iso646-us", "iso-ir-6", "us", "ibm367", "cp367",
   "csascii"].contains (encKey name)

/-- `UTF-16` with no byte order given. -/
def isUtf16Label (name : String) : Bool := encKey name == "utf-16" || encKey name == "utf16"

/-- `UTF-16LE` or `UTF-16BE`; the order the label names. -/
def utf16OrderLabel (name : String) : Option Endian :=
  if encKey name == "utf-16le" then some .little
  else if encKey name == "utf-16be" then some .big
  else none

/-! ## Reading the declaration -/

/-- The value of the `encoding` pseudo-attribute of the declaration
that opens `text`, when there is one and it is a legal `[81] EncName`.

This reads `<?xml ... ?>` the way `[23] XMLDecl` and `[77] TextDecl`
both write it, by pseudo-attribute name. A declaration that is
malformed in some other way yields whatever `encoding` value it has;
the document parser rejects the declaration itself afterwards. A value
that is not an `[81] EncName` is NOT reported: a document with
`encoding="a/b"` is not well-formed, and saying "unsupported encoding
a/b" would hide that. -/
def declaredEncoding (text : String) : Option String :=
  if !(text.startsWith "<?xml") then none
  else
    let cs := text.toList.drop 5
    match cs with
    | c :: _ =>
        if !isXmlSpace c then none
        else
          let body := cs.takeWhile (· != '?')
          match (textDeclAttrs body).find? (fun a => a.1 == "encoding") with
          | some (_, v) => if isEncName v then some v else none
          | none => none
    | [] => none

/-- The leading bytes of `bs` up to and including the first `?>`, or all
of them, read as ASCII (Appendix F.2). -/
def declarationPrefix (bs : ByteArray) : String :=
  let n := bs.size
  let stop := Id.run do
    let mut stop := n
    for i in [0:n] do
      if stop == n && byteAt bs i == 0x3F && byteAt bs (i + 1) == 0x3E then
        stop := i + 2
    pure stop
  decodeLatin1 (bs.extract 0 stop)

/-! ## `decodeXmlBytes` -/

/-- The declaration check for a UTF-16 entity (§4.3.3). With a byte order
mark the declaration may be absent, `UTF-16`, or `UTF-16LE`/`UTF-16BE`
agreeing with the mark. Without one the entity is only legal when a
declaration names the order — `UTF-16` alone is the fatal error "in UTF-16
but does not begin with a byte order mark". -/
def checkUtf16Declaration (order : Endian) (hasBom : Bool) (declared : Option String) :
    Except DecodeError Unit :=
  match declared with
  | none =>
      if hasBom then .ok ()
      else .error (.conflict
        "an entity in UTF-16 with no byte order mark and no encoding declaration (XML 1.0 section 4.3.3)")
  | some e =>
      if isUtf16Label e then
        if hasBom then .ok ()
        else .error (.conflict
          ("the entity is in UTF-16 with no byte order mark but its declaration names " ++ e ++
           ", which does not say the byte order (XML 1.0 section 4.3.3)"))
      else match utf16OrderLabel e with
        | some o =>
            if o == order then .ok ()
            else .error (.conflict
              ("the encoding declaration names " ++ e ++ " but the entity's bytes are in the other byte order (XML 1.0 section 4.3.3)"))
        | none =>
            .error (.conflict
              ("the entity is in UTF-16 but its encoding declaration names " ++ e ++
               " (XML 1.0 section 4.3.3)"))

/-- Decode the bytes of an XML entity — a document or an external parsed
entity — to its text. The leading byte order mark is consumed; the
encoding declaration is left in the text for the parser to read.

Fails with `DecodeError.unsupported` for an encoding that is not
implemented, `DecodeError.invalid` for bytes illegal in the encoding,
and `DecodeError.conflict` where §4.3.3 makes the entity a fatal error
for what its declaration says against what its bytes are. -/
def decodeXmlBytesE (bs : ByteArray) : Except DecodeError String :=
  match detectFamily bs with
  | .ucs4 name => .error (.unsupported name)
  | .ebcdic => .error (.unsupported "EBCDIC")
  | .utf8Bom =>
      match decodeUtf8 (bs.extract 3 bs.size) with
      | .error e => .error e
      | .ok text =>
          match declaredEncoding text with
          | none => .ok text
          | some e =>
              if isUtf8Label e then .ok text
              else .error (.conflict
                ("the entity begins with a UTF-8 byte order mark but its encoding declaration names " ++
                 e ++ " (XML 1.0 section 4.3.3)"))
  | .utf16Bom order =>
      match decodeUtf16 bs order 2 with
      | .error e => .error e
      | .ok text =>
          match checkUtf16Declaration order true (declaredEncoding text) with
          | .error e => .error e
          | .ok _ => .ok text
  | .utf16Bare order =>
      match decodeUtf16 bs order 0 with
      | .error e => .error e
      | .ok text =>
          match checkUtf16Declaration order false (declaredEncoding text) with
          | .error e => .error e
          | .ok _ => .ok text
  | .asciiCompatible =>
      match declaredEncoding (declarationPrefix bs) with
      | none => decodeUtf8 bs
      | some e =>
          if isUtf8Label e then decodeUtf8 bs
          else if isLatin1Label e then .ok (decodeLatin1 bs)
          else if isAsciiLabel e then decodeAscii bs
          else if isUtf16Label e || (utf16OrderLabel e).isSome then
            .error (.conflict
              ("the encoding declaration names " ++ e ++ " but the entity is not in UTF-16 " ++
               "(it begins with 8-bit characters, not a UTF-16 byte order mark; XML 1.0 section 4.3.3)"))
          else .error (.unsupported e)

/-- `decodeXmlBytesE` with the error as text: the decoder of XML 1.0
section 4.3.3 and Appendix F. Total. -/
def decodeXmlBytes (bs : ByteArray) : Except String String :=
  match decodeXmlBytesE bs with
  | .ok s => .ok s
  | .error e => .error e.message

/-! ## Parsing bytes -/

/-- Parse the bytes of a document: decode (§4.3.3 and Appendix F), then
parse the text. A decoding failure is a fatal error of the document and
is reported at position 0. -/
def parseXMLBytesWith (resolve : Resolver) (bs : ByteArray) : Except XmlError Document :=
  match decodeXmlBytesE bs with
  | .error e => .error { message := e.message, position := 0 }
  | .ok text => parseDecodedXMLWith resolve text

/-- `parseXMLBytesWith` with no external resource read. -/
def parseXMLBytes (bs : ByteArray) : Except XmlError Document :=
  parseXMLBytesWith (fun _ => none) bs

end L4Factoidal.XML
