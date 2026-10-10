/-
L4Factoidal.XML.Tests — compile-time executable checks for the XML
port.

Every `#guard` below is evaluated during `lake build`: a wrong answer
is a BUILD FAILURE, so these are unit tests with no separate runner.

The first group is the two documents hub post 25
(`docs/web/hub/25-xml-wellformedness-and-xpath.md`) uses live, with the
verdicts that post states. The rest exercise each well-formedness
constraint listed in `Parser.lean`'s header, the namespace layer, and
the round-trip and reflexivity claims from `Theorems.lean`.

Conformance discipline (iron rule #6): NOTHING here is a conformance
claim. These are hand-written fixtures. The W3C XML Conformance Test
Suite is run by `xmlconf-probe` (`ConfProbe.lean`), which reads the
vendored corpus files from disk.
-/
import L4Factoidal.XML.Theorems
import L4Factoidal.XML.Wellformedness
import L4Factoidal.XML.Encoding
import L4Factoidal.XML.Validity

namespace L4Factoidal.XML.Tests

open L4Factoidal.XML

/-! ## Hub post 25 — the two live documents

The post names one document, reuses it, then breaks it. -/

/-- The `XML` cell of hub post 25. -/
def hubXML : String :=
  "<library>\n" ++
  "  <book id=\"b1\"><title>SPARQL 1.1</title></book>\n" ++
  "  <book id=\"b2\"><title>RDF Primer</title></book>\n" ++
  "</library>"

/-- The `BAD` cell of hub post 25 — a closing tag that does not match
the element it closes. -/
def hubBAD : String := "<library><book></shelf></library>"

-- The post says `{ ok: true, wellformed: true }`.
#guard isWellFormed hubXML
-- The post says `{ ok: true, wellformed: false }`: `</shelf>` closes
-- nothing that is open.
#guard !isWellFormed hubBAD

-- The post's XPath cells select `//book/title`, so the two titles must
-- be reachable with the string-values it prints.
#guard (match parseXML hubXML with
        | .ok d => (d.root.childElements "book").map (·.textContent)
        | .error _ => []) == ["SPARQL 1.1", "RDF Primer"]

-- and `string(//book[2]/@id)` is `b2`.
#guard (match parseXML hubXML with
        | .ok d => ((d.root.childElements "book")[1]?).bind
                     (fun b => findAttr "id" b.elementAttrs)
        | .error _ => none) == some "b2"

/-! ## `[39] element` — WFC: Element Type Match -/

#guard isWellFormed "<a/>"
#guard isWellFormed "<a></a>"
#guard isWellFormed "<a><b><c/></b></a>"
-- Mismatched tags.
#guard !isWellFormed "<a></b>"
#guard !isWellFormed "<a><b></a></b>"
-- Unclosed.
#guard !isWellFormed "<a>"

/-! ## `[41] Attribute` — WFC: Unique Att Spec -/

#guard isWellFormed "<a x=\"1\" y=\"2\"/>"
-- Duplicate attribute name.
#guard !isWellFormed "<a x=\"1\" x=\"2\"/>"
-- Unescaped `<` in an attribute value ([10] AttValue excludes it).
#guard !isWellFormed "<a x=\"<\"/>"
-- Unquoted value.
#guard !isWellFormed "<a x=1/>"

/-! ## `[66] CharRef` and `[68] EntityRef` -/

#guard isWellFormed "<a>&#65;&#x41;&amp;&lt;&gt;&quot;&apos;</a>"
-- `&#RE;` — `R` is not a decimal digit.
#guard !isWellFormed "<a>&#RE;</a>"
-- `&#x4G;` — `G` is not a hexadecimal digit.
#guard !isWellFormed "<a>&#x4G;</a>"
-- Uppercase `X` is not the hexadecimal marker; it falls through to the
-- decimal path, where it is not a digit.
#guard !isWellFormed "<a>&#X41;</a>"
-- A character reference to a codepoint outside `[2] Char`.
#guard !isWellFormed "<a>&#0;</a>"
-- Not terminated by `;`.
#guard !isWellFormed "<a>&amp</a>"
-- WFC: Entity Declared.
#guard !isWellFormed "<a>&undeclared;</a>"
-- A declared internal general entity resolves.
#guard isWellFormed "<!DOCTYPE a [<!ENTITY e \"val\">]><a>&e;</a>"
#guard (match parseXML "<!DOCTYPE a [<!ENTITY e \"val\">]><a>&e;</a>" with
        | .ok d => d.root.textContent
        | .error _ => "") == "val"
-- WFC: No Recursion.
#guard !isWellFormed "<!DOCTYPE a [<!ENTITY e \"&e;\">]><a>&e;</a>"

/-! ### Entities with empty replacement text

The one place this port's VERDICT differs from `Parser.XML.fst`'s. When
an element's whole content is a reference to an entity whose
replacement text is empty, the F* parser stops collecting children at
the `&` and then rejects the document for want of an end tag. These
documents are well-formed, and the W3C conformance suite marks them
valid — `xmltest/valid/sa/023.xml`, `085.xml`, `086.xml`. See the
comment on `parseChildren`. -/

-- The body of xmltest/valid/sa/023.xml.
#guard isWellFormed "<!DOCTYPE doc [<!ELEMENT doc (#PCDATA)><!ENTITY e \"\">]><doc>&e;</doc>"
-- The body of xmltest/valid/sa/086.xml — a duplicate declaration, where
-- §4.2 says the FIRST binding wins, so `e` is still empty.
#guard isWellFormed
  "<!DOCTYPE doc [<!ELEMENT doc (#PCDATA)><!ENTITY e \"\"><!ENTITY e \"<foo>\">]><doc>&e;</doc>"
-- An expansion yielding no characters contributes no `[14] CharData`:
-- the element has no child at all, rather than an empty text node.
#guard (match parseXML "<!DOCTYPE doc [<!ENTITY e \"\">]><doc>&e;</doc>" with
        | .ok d => d.root.elementChildren.length
        | .error _ => 99) == 0
#guard roundTripsFrom "<!DOCTYPE doc [<!ENTITY e \"\">]><doc>&e;</doc>"

/-! ## `[15] Comment` -/

#guard isWellFormed "<a><!-- hi --></a>"
-- `--` may not occur inside a comment.
#guard !isWellFormed "<a><!-- a -- b --></a>"
-- ...nor may the body end in `-`.
#guard !isWellFormed "<a><!-- ---></a>"

/-! ## `[16] PI` — `[17] PITarget` -/

#guard isWellFormed "<a><?tgt data?></a>"
#guard isWellFormed "<a><?tgt?></a>"
-- The reserved target `xml`, in any case, is not a legal generic PI.
#guard !isWellFormed "<a><?xml foo?></a>"
#guard !isWellFormed "<a><?xMl foo?></a>"
-- A target is required.
#guard !isWellFormed "<a><? ?></a>"

/-! ## `[18] CDSect` and `[14] CharData` -/

#guard isWellFormed "<a><![CDATA[x < y & z]]></a>"
-- The content of a CDATA section reaches the infoset verbatim.
#guard (match parseXML "<a><![CDATA[x < y & z]]></a>" with
        | .ok d => d.root.textContent
        | .error _ => "") == "x < y & z"
-- `[14] CharData` excludes a literal `]]>`.
#guard !isWellFormed "<a>]]></a>"
-- ...but a reference may put those characters into the infoset.
#guard isWellFormed "<a>]]&gt;</a>"
-- An unterminated CDATA section.
#guard !isWellFormed "<a><![CDATA[x</a>"

/-! ## `[2] Char` -/

-- A vertical tab (#xB) is outside `[2] Char`.
#guard !isWellFormed ("<a>" ++ String.singleton (Char.ofNat 0xB) ++ "</a>")
-- Tab, LF and CR are inside it.
#guard isWellFormed "<a>\t\n</a>"

/-! ## UTF-8 — non-ASCII text and names -/

#guard isWellFormed "<a>日本語 café</a>"
#guard (match parseXML "<a>日本語 café</a>" with
        | .ok d => d.root.textContent
        | .error _ => "") == "日本語 café"
-- `[4] NameStartChar` admits these codepoints, so the element name
-- parses whole rather than being truncated mid-character.
#guard (match parseXML "<日本 x=\"1\">t</日本>" with
        | .ok d => d.root.elementTag
        | .error _ => none) == some "日本"

/-! ## `[23] XMLDecl` -/

#guard isWellFormed "<?xml version=\"1.0\"?><a/>"
#guard isWellFormed "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?><a/>"
#guard (match parseXML "<?xml version=\"1.0\" encoding=\"UTF-8\"?><a/>" with
        | .ok d => d.decl
        | .error _ => none)
       == some { version := "1.0", encoding := some "UTF-8", standalone := none }
-- `[26] VersionNum ::= '1.' [0-9]+`.
#guard !isWellFormed "<?xml version=\"2.0\"?><a/>"
-- `[32] SDDecl` is lowercase only.
#guard !isWellFormed "<?xml version=\"1.0\" standalone=\"YES\"?><a/>"
-- Out of order.
#guard !isWellFormed "<?xml version=\"1.0\" standalone=\"yes\" encoding=\"UTF-8\"?><a/>"
-- Nothing may precede the declaration.
#guard !isWellFormed " <?xml version=\"1.0\"?><a/>"

/-! ## `[1] document` — one root, and a Misc-only epilog -/

#guard isWellFormed "<!-- prolog --><a/><!-- epilog -->"
#guard isWellFormed "<?pi d?><a/><?pi d?>"
-- A second document element.
#guard !isWellFormed "<a/><b/>"
-- Stray text in the epilog.
#guard !isWellFormed "<a/>junk"
-- No document element at all.
#guard !isWellFormed "<!-- only a comment -->"

/-! ## `[28] doctypedecl` -/

#guard isWellFormed "<!DOCTYPE a><a/>"
#guard isWellFormed "<!DOCTYPE a SYSTEM \"a.dtd\"><a/>"
#guard isWellFormed "<!DOCTYPE a [<!ELEMENT a EMPTY>]><a/>"
-- The internal subset's ATTLIST ID pairs reach the infoset.
#guard (match parseXML "<!DOCTYPE a [<!ATTLIST a k ID #IMPLIED>]><a k=\"v\"/>" with
        | .ok d => (d.doctype.map (·.idAttrs)).getD []
        | .error _ => []) == [("a", "k")]
-- An unterminated internal subset.
#guard !isWellFormed "<!DOCTYPE a [<!ENTITY e \"v\"><a/>"

/-! ## §3.3.3 attribute-value normalisation -/

-- A LITERAL tab in an attribute value becomes a space...
#guard (match parseXML "<a x=\"p\tq\"/>" with
        | .ok d => findAttr "x" d.root.elementAttrs
        | .error _ => none) == some "p q"
-- ...while a CHARACTER REFERENCE to one keeps the character itself.
#guard (match parseXML "<a x=\"p&#9;q\"/>" with
        | .ok d => findAttr "x" d.root.elementAttrs
        | .error _ => none) == some "p\tq"

/-! ## §2.11 line-ending normalisation -/

#guard normalizeLineEndings "a\r\nb\rc\nd".toList == "a\nb\nc\nd".toList
#guard (match parseXML "<a>x\r\ny</a>" with
        | .ok d => d.root.textContent
        | .error _ => "") == "x\ny"

/-! ## Namespaces in XML -/

-- A declaration is in scope for the element that carries it.
#guard isNamespaceWellFormedDoc "<r xmlns:p=\"http://e/\"><p:c/></r>"
-- An undeclared prefix rejects.
#guard !isNamespaceWellFormedDoc "<r><p:c/></r>"
-- ...though it is perfectly well-formed PLAIN XML 1.0, where `:` is an
-- ordinary Name character. The two layers are separate on purpose.
#guard isWellFormed "<r><p:c/></r>"
-- The default namespace applies to unprefixed ELEMENT names (§4).
#guard isNamespaceWellFormedDoc "<r xmlns=\"http://d/\"><c/></r>"
#guard resolveElementName [("", some "http://d/")] "c"
       == some { namespace_ := some "http://d/", localPart := "c" }
-- An unprefixed ATTRIBUTE name is never in the default namespace (§6.2).
#guard resolveAttributeName [("", some "http://d/")] "c"
       == some { namespace_ := none, localPart := "c" }
-- §6.3: two attributes collide once their prefixes expand to the same
-- namespace name, even though their QNames differ.
#guard !isNamespaceWellFormedDoc
  "<r xmlns:a=\"http://e/\" xmlns:b=\"http://e/\"><c a:x=\"1\" b:x=\"2\"/></r>"
-- Reserved prefixes and namespace names.
#guard !isNamespaceWellFormedDoc "<r xmlns:xmlns=\"http://e/\"/>"
#guard !isNamespaceWellFormedDoc "<r xmlns:xml=\"http://bogus/\"/>"
#guard isNamespaceWellFormedDoc "<r xmlns:xml=\"http://www.w3.org/XML/1998/namespace\"/>"
-- `xml` is bound without being declared.
#guard isNamespaceWellFormedDoc "<r xml:lang=\"en\"/>"
-- Undeclaring a PREFIXED binding: illegal in 1.0, legal in 1.1.
#guard !isNamespaceWellFormedDoc "<r xmlns:p=\"http://e/\"><s xmlns:p=\"\"/></r>"
#guard isNamespaceWellFormedDoc
  "<?xml version=\"1.1\"?><r xmlns:p=\"http://e/\"><s xmlns:p=\"\"/></r>"
-- The default namespace may always be undeclared.
#guard isNamespaceWellFormedDoc "<r xmlns=\"http://d/\"><s xmlns=\"\"/></r>"
-- `[7] QName` syntax.
#guard splitQName "p:c" == .prefixed "p" "c"
#guard splitQName "c" == .simple "c"
#guard splitQName "a:b:c" == .malformed
#guard splitQName ":c" == .malformed
#guard splitQName "p:" == .malformed
#guard !isNamespaceWellFormedDoc "<a:b:c/>"

-- Namespaces in XML 1.0 section 6 (erratum NE08): no colon in a
-- processing instruction target, an entity name or a notation name.
-- Each is well-formed PLAIN XML, so the namespace layer alone rejects it.
#guard isWellFormed "<?a:b x?><r/>"
#guard !isNamespaceWellFormedDoc "<?a:b x?><r/>"
#guard isNamespaceWellFormedDoc "<?ab x?><r/>"
#guard !isNamespaceWellFormedDoc "<r><?a:b x?></r>"
#guard isNamespaceWellFormedDoc "<r><?ab x?></r>"
#guard isWellFormed "<!DOCTYPE r [<!ENTITY a:b \"v\">]><r/>"
#guard !isNamespaceWellFormedDoc "<!DOCTYPE r [<!ENTITY a:b \"v\">]><r/>"
#guard isNamespaceWellFormedDoc "<!DOCTYPE r [<!ENTITY ab \"v\">]><r/>"
#guard !isNamespaceWellFormedDoc "<!DOCTYPE r [<!ENTITY % a:b \"v\">]><r/>"
#guard isWellFormed "<!DOCTYPE r [<!NOTATION a:b SYSTEM \"n\">]><r/>"
#guard !isNamespaceWellFormedDoc "<!DOCTYPE r [<!NOTATION a:b SYSTEM \"n\">]><r/>"
#guard isNamespaceWellFormedDoc "<!DOCTYPE r [<!NOTATION ab SYSTEM \"n\">]><r/>"
#guard !isNamespaceWellFormedDoc "<!DOCTYPE r [<?a:b x?>]><r/>"
-- The declared names are recorded in reverse order of declaration.
#guard (match parseXML "<!DOCTYPE r [<!ENTITY e \"1\"><!NOTATION n SYSTEM \"x\"><!ENTITY f \"2\">]><r/>" with
        | .ok d => d.doctype.map (·.declared)
        | .error _ => none)
       == some { entities := ["f", "e"], notations := ["n"], piTargets := [] }

/-! ## §3.3.3 attribute-value normalisation by declared type

A processor that reads an ATTLIST must use the declared type (section
5.1). The value of an attribute whose type is not CDATA has its leading
and trailing spaces discarded and each run of spaces collapsed. -/

#guard (match parseXML "<!DOCTYPE r [<!ATTLIST r a NMTOKENS #IMPLIED>]><r a=\"  x   y  \"/>" with
        | .ok d => findAttr "a" d.root.elementAttrs
        | .error _ => none) == some "x y"
-- CDATA, declared or by default, is not collapsed.
#guard (match parseXML "<!DOCTYPE r [<!ATTLIST r a CDATA #IMPLIED>]><r a=\"  x   y  \"/>" with
        | .ok d => findAttr "a" d.root.elementAttrs
        | .error _ => none) == some "  x   y  "
#guard (match parseXML "<r a=\"  x   y  \"/>" with
        | .ok d => findAttr "a" d.root.elementAttrs
        | .error _ => none) == some "  x   y  "
-- A reference to a space is a space once expanded, so it is collapsed too.
#guard (match parseXML "<!DOCTYPE r [<!ATTLIST r a ID #IMPLIED>]><r a=\"&#32;x&#32;\"/>" with
        | .ok d => findAttr "a" d.root.elementAttrs
        | .error _ => none) == some "x"
-- The declaration is per ELEMENT: another element's attribute of the
-- same name is untouched.
#guard (match parseXML "<!DOCTYPE r [<!ATTLIST r a NMTOKEN #IMPLIED>]><r><s a=\" v \"/></r>" with
        | .ok d => ((d.root.childElements "s").head?).bind (fun s => findAttr "a" s.elementAttrs)
        | .error _ => none) == some " v "
-- Section 3.3: the FIRST declaration of an attribute is binding.
#guard (match parseXML ("<!DOCTYPE r [<!ATTLIST r a CDATA #IMPLIED>" ++
          "<!ATTLIST r a NMTOKEN #IMPLIED>]><r a=\" v \"/>") with
        | .ok d => findAttr "a" d.root.elementAttrs
        | .error _ => none) == some " v "
#guard (match parseXML ("<!DOCTYPE r [<!ATTLIST r a NMTOKEN #IMPLIED>" ++
          "<!ATTLIST r a CDATA #IMPLIED>]><r a=\" v \"/>") with
        | .ok d => findAttr "a" d.root.elementAttrs
        | .error _ => none) == some "v"
-- The normalisation can make two namespace declarations equal
-- (xmlconf rmt-ns10-012): the attributes then collide after expansion.
#guard !isNamespaceWellFormedDoc
  ("<!DOCTYPE r [<!ATTLIST r xmlns:a CDATA #IMPLIED xmlns:b NMTOKEN #IMPLIED>]>" ++
   "<r xmlns:a=\"urn:x\" xmlns:b=\" urn:x \"><c a:k=\"1\" b:k=\"2\"/></r>")
-- ...and with both declared CDATA the two names differ, so it passes.
#guard isNamespaceWellFormedDoc
  ("<!DOCTYPE r [<!ATTLIST r xmlns:a CDATA #IMPLIED xmlns:b CDATA #IMPLIED>]>" ++
   "<r xmlns:a=\"urn:x\" xmlns:b=\" urn:x \"><c a:k=\"1\" b:k=\"2\"/></r>")
-- Every attribute type is recorded.
#guard (match parseXML ("<!DOCTYPE r [<!ATTLIST r a CDATA #IMPLIED b ID #REQUIRED " ++
          "c IDREF #IMPLIED d IDREFS #IMPLIED e ENTITY #IMPLIED f ENTITIES #IMPLIED " ++
          "g NMTOKEN #IMPLIED h NMTOKENS #IMPLIED i NOTATION (n) #IMPLIED " ++
          "j (x|y) \"x\" k CDATA #FIXED \"z\">]><r b=\"b\"/>") with
        | .ok d => (d.doctype.map (fun dt => dt.attDecls.reverse.map (fun a => (a.name, a.type, a.defaultDecl)))).getD []
        | .error _ => []) ==
       [("a", .CDATA, .implied), ("b", .ID, .required), ("c", .IDREF, .implied),
        ("d", .IDREFS, .implied), ("e", .ENTITY, .implied), ("f", .ENTITIES, .implied),
        ("g", .NMTOKEN, .implied), ("h", .NMTOKENS, .implied), ("i", .NOTATION ["n"], .implied),
        ("j", .Enumeration ["x", "y"], .value "x"), ("k", .CDATA, .fixed "z")]
-- ...and re-parse unchanged after serialisation.
#guard roundTripsFrom ("<!DOCTYPE r [<!ATTLIST r a CDATA #IMPLIED b ID #REQUIRED " ++
          "c IDREF #IMPLIED d IDREFS #IMPLIED e ENTITY #IMPLIED f ENTITIES #IMPLIED " ++
          "g NMTOKEN #IMPLIED h NMTOKENS #IMPLIED i NOTATION (n) #IMPLIED " ++
          "j (x|y) \"x\" k CDATA #FIXED \"z\">]><r b=\"b\"/>")

/-! ## `[4] NCName` — Namespaces in XML §3 -/

#guard isValidNCName "abc"
#guard isValidNCName "_a-b.c1"
#guard !isValidNCName "a:b"
#guard !isValidNCName ""
#guard !isValidNCName "1abc"

/-! ## Character encodings — XML 1.0 section 4.3.3 and Appendix F

`decodeXmlBytes` turns the BYTES of an entity into text. The fixtures are
built from code units so that each one states exactly which bytes it
tests. -/

/-- UTF-16 bytes for `s`: surrogate pairs above U+FFFF, optionally a byte
order mark first. -/
def utf16Bytes (s : String) (order : Endian) (bom : Bool) : ByteArray :=
  let units : List Nat := s.toList.flatMap fun c =>
    let n := c.toNat
    if n < 0x10000 then [n]
    else [0xD800 + (n - 0x10000) / 0x400, 0xDC00 + (n - 0x10000) % 0x400]
  let units := (if bom then [0xFEFF] else []) ++ units
  ByteArray.mk ((units.flatMap fun u =>
    match order with
    | .big => [u / 256, u % 256]
    | .little => [u % 256, u / 256]).map Nat.toUInt8).toArray

/-- The bytes of a list of byte values. -/
def rawBytes (bs : List Nat) : ByteArray := ByteArray.mk (bs.map Nat.toUInt8).toArray

/-- A string's UTF-8 bytes. -/
def u8 (s : String) : ByteArray := s.toUTF8

def decoded (bs : ByteArray) : Option String := (decodeXmlBytes bs).toOption

/-- The constructor of the decoding error, or `none` when it decodes. -/
def decodeFails (bs : ByteArray) : Bool := (decodeXmlBytesE bs).toOption.isNone

-- UTF-16, both orders, with a byte order mark, including a character
-- above U+FFFF (a surrogate pair).
#guard decoded (utf16Bytes "<a>é日本😀</a>" .little true) == some "<a>é日本😀</a>"
#guard decoded (utf16Bytes "<a>é日本😀</a>" .big true) == some "<a>é日本😀</a>"
-- The byte order mark is consumed, not left as a character.
#guard (decoded (utf16Bytes "<a/>" .big true)).map (·.toList.head?) == some (some '<')
-- With a declaration, the mark and `UTF-16` agree.
#guard decoded (utf16Bytes "<?xml version=\"1.0\" encoding=\"UTF-16\"?><a/>" .little true)
       == some "<?xml version=\"1.0\" encoding=\"UTF-16\"?><a/>"
-- UTF-16 with NO byte order mark is legal only when a declaration names
-- the byte order (Appendix F.1: `3C 00 3F 00` and `00 3C 00 3F`).
#guard decoded (utf16Bytes "<?xml version=\"1.0\" encoding=\"UTF-16LE\"?><a/>" .little false)
       == some "<?xml version=\"1.0\" encoding=\"UTF-16LE\"?><a/>"
#guard decoded (utf16Bytes "<?xml version=\"1.0\" encoding=\"utf-16be\"?><a/>" .big false)
       == some "<?xml version=\"1.0\" encoding=\"utf-16be\"?><a/>"
-- ...and `UTF-16` with no mark is the fatal error of section 4.3.3.
#guard decodeFails (utf16Bytes "<?xml version=\"1.0\" encoding=\"UTF-16\"?><a/>" .little false)
-- ...as is no declaration at all (an entity with neither a mark nor a
-- declaration must be UTF-8, and these bytes are not).
#guard decodeFails (utf16Bytes "<?pi x?><a/>" .big false)
-- ...and a declaration naming the OTHER byte order.
#guard decodeFails (utf16Bytes "<?xml version=\"1.0\" encoding=\"UTF-16BE\"?><a/>" .little false)
#guard decodeFails (utf16Bytes "<?xml version=\"1.0\" encoding=\"UTF-16BE\"?><a/>" .little true)
#guard decoded (utf16Bytes "<?xml version=\"1.0\" encoding=\"UTF-16LE\"?><a/>" .little true) != none
-- The declaration must agree with the detected family (hst-lhs-008).
#guard decodeFails (utf16Bytes "<?xml version=\"1.0\" encoding=\"utf-8\"?><a/>" .big true)
#guard decodeFails (utf16Bytes "<?xml version=\"1.0\" encoding=\"ISO-8859-1\"?><a/>" .little true)
-- Illegal UTF-16: a lone surrogate of either kind, a pair in the wrong
-- order, an odd number of bytes.
#guard decodeFails (rawBytes [0xFF, 0xFE, 0x3C, 0x00, 0x00, 0xD8])
#guard decodeFails (rawBytes [0xFF, 0xFE, 0x3C, 0x00, 0x00, 0xDC, 0x3E, 0x00])
#guard decodeFails (rawBytes [0xFF, 0xFE, 0x00, 0xD8, 0x3C, 0x00])
#guard decodeFails (rawBytes [0xFF, 0xFE, 0x3C, 0x00, 0x3E])
-- UTF-8: a leading byte order mark is consumed.
#guard decoded (rawBytes [0xEF, 0xBB, 0xBF] ++ u8 "<a/>") == some "<a/>"
#guard decoded (u8 "<a>é</a>") == some "<a>é</a>"
-- A UTF-8 byte order mark with a declaration of anything else is an
-- error (hst-lhs-007); with UTF-8 it is not.
#guard decodeFails (rawBytes [0xEF, 0xBB, 0xBF] ++ u8 "<?xml version='1.0' encoding='iso-8859-1'?><x/>")
#guard decoded (rawBytes [0xEF, 0xBB, 0xBF] ++ u8 "<?xml version='1.0' encoding='UTF-8'?><x/>")
       == some "<?xml version='1.0' encoding='UTF-8'?><x/>"
-- Illegal UTF-8: encoded surrogates, an overlong form, a code point
-- above U+10FFFF, a truncated sequence, a stray continuation byte.
#guard decodeFails (u8 "<a>" ++ rawBytes [0xED, 0xA0, 0x80] ++ u8 "</a>")
#guard decodeFails (u8 "<a>" ++ rawBytes [0xED, 0xB0, 0x80] ++ u8 "</a>")
#guard decodeFails (u8 "<a>" ++ rawBytes [0xC0, 0x80] ++ u8 "</a>")
#guard decodeFails (u8 "<a>" ++ rawBytes [0xF7, 0x80, 0x80, 0x80] ++ u8 "</a>")
#guard decodeFails (u8 "<a>" ++ rawBytes [0xE2, 0x82] ++ u8 "</a>")
#guard decodeFails (u8 "<a>" ++ rawBytes [0x80] ++ u8 "</a>")
-- A declaration of UTF-16 on an entity whose bytes are 8-bit.
#guard decodeFails (u8 "<?xml version='1.0' encoding='UTF-16'?><x/>")
#guard decodeFails (u8 "<?xml version='1.0' encoding='utf-16le'?><x/>")
-- ISO-8859-1: byte 0xE9 is U+00E9, every byte is legal.
#guard decoded (u8 "<?xml version='1.0' encoding='ISO-8859-1'?><x>" ++ rawBytes [0xE9, 0xFF, 0x80] ++ u8 "</x>")
       == some "<?xml version='1.0' encoding='ISO-8859-1'?><x>éÿ\u0080</x>"
-- The same bytes with no declaration are not UTF-8.
#guard decodeFails (u8 "<x>" ++ rawBytes [0xE9] ++ u8 "</x>")
#guard decoded (u8 "<?xml version='1.0' encoding='latin1'?><x>" ++ rawBytes [0xE9] ++ u8 "</x>")
       == some "<?xml version='1.0' encoding='latin1'?><x>é</x>"
-- US-ASCII: bytes above 127 are illegal.
#guard decoded (u8 "<?xml version='1.0' encoding='US-ASCII'?><x>abc</x>")
       == some "<?xml version='1.0' encoding='US-ASCII'?><x>abc</x>"
#guard decodeFails (u8 "<?xml version='1.0' encoding='us-ascii'?><x>" ++ rawBytes [0xE9] ++ u8 "</x>")
-- Encoding names are case-insensitive.
#guard (decoded (u8 "<?xml version='1.0' encoding='iso-8859-1'?><x>" ++ rawBytes [0xE9] ++ u8 "</x>")).map
         (·.toList.contains '\u00E9') == some true
#guard (decoded (u8 "<?xml version='1.0' encoding='Iso-8859-1'?><x>" ++ rawBytes [0xE9] ++ u8 "</x>")).map
         (·.toList.contains '\u00E9') == some true
-- An encoding the decoder does not implement is reported by NAME, and
-- is neither an error of the bytes nor a verdict on the document.
#guard (decodeXmlBytesE (u8 "<?xml version='1.0' encoding='euc-jp'?><x/>")) matches .error (.unsupported "euc-jp")
#guard (decodeXmlBytesE (u8 "<?xml version='1.0' encoding='Shift_JIS'?><x/>")) matches .error (.unsupported "Shift_JIS")
#guard (decodeXmlBytesE (rawBytes [0x00, 0x00, 0x00, 0x3C, 0x00, 0x00, 0x00, 0x3F])) matches .error (.unsupported _)
#guard (decodeXmlBytesE (rawBytes [0x4C, 0x6F, 0xA7, 0x94])) matches .error (.unsupported "EBCDIC")
-- A conflict and a malformed byte sequence are NOT "unsupported".
#guard !((decodeXmlBytesE (u8 "<?xml version='1.0' encoding='UTF-16'?><x/>")) matches .error (.unsupported _))
-- An encoding name that is not an `[81] EncName` is the parser's to
-- reject, not the decoder's: the bytes decode as UTF-8.
#guard decoded (u8 "<?xml version='1.0' encoding='a/b'?><x/>") == some "<?xml version='1.0' encoding='a/b'?><x/>"
-- Autodetection (Appendix F.1).
#guard detectFamily (rawBytes [0xEF, 0xBB, 0xBF, 0x3C]) == .utf8Bom
#guard detectFamily (rawBytes [0xFE, 0xFF, 0x00, 0x3C]) == .utf16Bom .big
#guard detectFamily (rawBytes [0xFF, 0xFE, 0x3C, 0x00]) == .utf16Bom .little
#guard detectFamily (rawBytes [0x00, 0x3C, 0x00, 0x3F]) == .utf16Bare .big
#guard detectFamily (rawBytes [0x3C, 0x00, 0x3F, 0x00]) == .utf16Bare .little
#guard detectFamily (rawBytes [0x3C, 0x3F, 0x78, 0x6D]) == .asciiCompatible
#guard detectFamily (rawBytes [0x4C, 0x6F, 0xA7, 0x94]) == .ebcdic
-- `FF FE 00 00` is UCS-4, not UTF-16 followed by U+0000.
#guard (match detectFamily (rawBytes [0xFF, 0xFE, 0x00, 0x00]) with | .ucs4 _ => true | _ => false)
#guard detectFamily (rawBytes []) == .asciiCompatible
-- The empty entity decodes (to nothing); the parser rejects it.
#guard decoded (rawBytes []) == some ""
#guard (parseXMLBytes (rawBytes [])).toOption.isNone
-- End to end: a UTF-16 document with `encoding="UTF-16"` parses from
-- bytes. The same TEXT given to the String-level `parseXML` is refused,
-- because a String is taken to have been UTF-8 and UTF-16 is the
-- section 4.3.3 contradiction there.
#guard (parseXMLBytes (utf16Bytes "<?xml version=\"1.0\" encoding=\"UTF-16\"?><a x=\"é\">日本</a>" .little true)).toOption.isSome
#guard (match parseXMLBytes (utf16Bytes "<?xml version=\"1.0\" encoding=\"UTF-16\"?><a x=\"é\">日本</a>" .big true) with
        | .ok d => (findAttr "x" d.root.elementAttrs, d.root.textContent)
        | .error _ => (none, "")) == (some "é", "日本")
#guard !isWellFormed "<?xml version=\"1.0\" encoding=\"UTF-16\"?><a/>"
-- A document that does not decode is rejected, with the decoder's reason.
#guard (match parseXMLBytes (rawBytes [0xFF, 0xFE, 0x3C, 0x00, 0x3E]) with
        | .error e => e.message.startsWith "UTF-16"
        | .ok _ => false)
-- ISO-8859-1 end to end.
#guard (parseXMLBytes (u8 "<?xml version='1.0' encoding='ISO-8859-1'?><x>" ++ rawBytes [0xE9] ++ u8 "</x>")).toOption.isSome
#guard (parseXMLBytes (u8 "<?xml version='1.0'?><x>" ++ rawBytes [0xE9] ++ u8 "</x>")).toOption.isNone

/-! ## XML 1.1 — https://www.w3.org/TR/xml11/

The version comes from the XML declaration: `1.1` selects XML 1.1, anything
else (or no declaration) the XML 1.0 rules. XML 1.1 differs in `[2] Char`
(NUL is the only C0 control left out), in `[2a] RestrictedChar` (a
document may hold those controls only through a character reference), in
what a character reference may name (section 4.1), and in end-of-line
handling (section 2.11: NEL and LS join CR and LF). -/

def v11 (body : String) : String := "<?xml version=\"1.1\"?>" ++ body
def v10 (body : String) : String := "<?xml version=\"1.0\"?>" ++ body

/-- The text content of the root, or `none` when the document is refused. -/
def rootText (doc : String) : Option String :=
  match parseXML doc with
  | .ok d => some d.root.textContent
  | .error _ => none

-- Section 2.11: NEL, LS, CR NEL and a lone CR each become one LF in 1.1.
#guard rootText (v11 "<a>x\u0085y</a>") == some "x\ny"
#guard rootText (v11 "<a>x y</a>") == some "x\ny"
#guard rootText (v11 "<a>x\r\u0085y</a>") == some "x\ny"
#guard rootText (v11 "<a>x\ry</a>") == some "x\ny"
#guard rootText (v11 "<a>x\r\ny</a>") == some "x\ny"
-- ...CR LS is NOT combined: a CR becomes LF, then the LS becomes LF.
#guard rootText (v11 "<a>x\r y</a>") == some "x\n\ny"
-- In an XML 1.0 document NEL and LS are ordinary characters, left alone.
#guard rootText (v10 "<a>x\u0085y</a>") == some "x\u0085y"
#guard rootText (v10 "<a>x y</a>") == some "x y"
#guard rootText "<a>x\u0085y</a>" == some "x\u0085y"
#guard rootText (v10 "<a>x\r\u0085y</a>") == some "x\n\u0085y"
-- A version other than 1.1 is read by the 1.0 rules.
#guard rootText "<?xml version=\"1.2\"?><a>x\u0085y</a>" == some "x\u0085y"
-- NEL in an attribute value is a line end, hence a space, in 1.1.
#guard (match parseXML (v11 "<a x=\"p\u0085q\"/>") with
        | .ok d => findAttr "x" d.root.elementAttrs
        | .error _ => none) == some "p q"
#guard (match parseXML (v10 "<a x=\"p\u0085q\"/>") with
        | .ok d => findAttr "x" d.root.elementAttrs
        | .error _ => none) == some "p\u0085q"

-- Section 2.2: literal controls. #x7F-#x9F (other than NEL) and
-- #x1-#x1F (other than tab, LF, CR) are restricted in 1.1...
#guard rootText (v11 "<a>\u007F</a>") == none
#guard rootText (v11 "<a>\u0090</a>") == none
#guard rootText (v11 "<a>\u009F</a>") == none
#guard rootText (v11 "<a>\u0001</a>") == none
#guard rootText (v11 "<a>\u000C</a>") == none
-- ...in every construct, since `[1] document` excludes them wholesale.
#guard rootText (v11 "<a><!--\u0090--></a>") == none
#guard rootText (v11 "<a><?p \u0090?></a>") == none
#guard rootText (v11 "<a><![CDATA[\u0090]]></a>") == none
#guard rootText (v11 "<a x=\"\u0090\"/>") == none
#guard rootText (v11 "<!DOCTYPE a [<!-- \u0090 -->]><a/>") == none
-- XML 1.0 admits #x7F-#x9F literally and rejects #x1-#x1F.
#guard rootText (v10 "<a>\u007F</a>") == some "\u007F"
#guard rootText (v10 "<a>\u0090</a>") == some "\u0090"
#guard rootText (v10 "<a>\u0001</a>") == none
#guard rootText (v10 "<a>\u000C</a>") == none
-- NUL, the non-characters and the surrogate range are out in both.
#guard rootText (v11 "<a>\u0000</a>") == none
#guard rootText (v11 "<a>￾</a>") == none
#guard rootText (v10 "<a>￾</a>") == none
-- Section 4.1: a character reference may name any 1.1 `Char`, the
-- restricted controls included...
#guard rootText (v11 "<a>&#1;&#xC;&#x7F;&#x85;&#x9F;</a>") == some "\u0001\u000C\u007F\u0085\u009F"
-- ...which XML 1.0 refuses for #x1-#x8, #xB, #xC and #xE-#x1F,
#guard rootText (v10 "<a>&#1;</a>") == none
#guard rootText (v10 "<a>&#xC;</a>") == none
#guard rootText (v10 "<a>&#x1F;</a>") == none
-- ...and accepts for the rest.
#guard rootText (v10 "<a>&#x7F;&#x85;&#x9F;</a>") == some "\u007F\u0085\u009F"
-- Both refuse NUL and the non-characters.
#guard rootText (v11 "<a>&#0;</a>") == none
#guard rootText (v11 "<a>&#xFFFE;</a>") == none
#guard rootText (v11 "<a>&#xD800;</a>") == none
-- A character reference keeps NEL as NEL; the line-end rule is for
-- literal characters only.
#guard rootText (v11 "<a>x&#x85;y</a>") == some "x\u0085y"
-- A reference to a restricted control inside an ENTITY VALUE is legal
-- when declared, and again when the entity is used in content
-- (xmlconf rmt-054).
#guard rootText (v11 "<!DOCTYPE a [<!ENTITY e \"&#12;\">]><a>&e;</a>") == some "\u000C"
#guard rootText (v10 "<!DOCTYPE a [<!ENTITY e \"&#12;\">]><a>&e;</a>") == none
-- ...and in an attribute value.
#guard (match parseXML (v11 "<a x=\"&#1;\"/>") with
        | .ok d => findAttr "x" d.root.elementAttrs
        | .error _ => none) == some "\u0001"

-- Section 4.3.4: an entity may be 1.0 or 1.1, and the DOCUMENT's version
-- rules apply to all of it. A 1.1 document may invoke a 1.0 entity;
-- a 1.0 document may not invoke a 1.1 one.
def entRes (text : String) : Resolver := fun id => if id == "e.ent" then some text else none
def withEnt (decl : String) (ent : String) : Bool :=
  (parseXMLWith (entRes ent) (decl ++ "<!DOCTYPE a [<!ENTITY e SYSTEM \"e.ent\">]><a>&e;</a>")).toOption.isSome
#guard withEnt "<?xml version=\"1.1\"?>" "<?xml version=\"1.0\" encoding=\"UTF-8\"?>x"
#guard withEnt "<?xml version=\"1.1\"?>" "<?xml encoding=\"UTF-8\"?>x"
#guard withEnt "<?xml version=\"1.1\"?>" "<?xml version=\"1.1\" encoding=\"UTF-8\"?>x"
#guard withEnt "<?xml version=\"1.0\"?>" "<?xml version=\"1.0\" encoding=\"UTF-8\"?>x"
#guard !withEnt "<?xml version=\"1.0\"?>" "<?xml version=\"1.1\" encoding=\"UTF-8\"?>x"
#guard !withEnt "" "<?xml version=\"1.1\" encoding=\"UTF-8\"?>x"
-- An entity text with no declaration is read by the document's rules.
#guard withEnt "<?xml version=\"1.1\"?>" "x"
-- The text declaration is checked as the grammar writes it: each
-- pseudo-attribute follows whitespace, and NEL is not whitespace.
#guard !withEnt "<?xml version=\"1.1\"?>" "<?xml version=\"1.1\"\u0085encoding=\"UTF-8\"?>x"
#guard !withEnt "<?xml version=\"1.1\"?>" "<?xml version=\"1.1\" encoding=\"UTF-8\"?>x"
#guard withEnt "<?xml version=\"1.1\"?>" "<?xml version=\"1.1\" encoding=\"UTF-8\" ?>x"
#guard !withEnt "<?xml version=\"1.1\"?>" "<?xml version=\"1.1\"encoding=\"UTF-8\"?>x"
#guard !withEnt "<?xml version=\"1.1\"?>" "<?xml version=\"1.1\"?>x"
-- XML 1.0 section 2.1, third clause: the parsed entities "referenced
-- directly or indirectly within the document" are well-formed. An
-- entity that no reference names is not read, so a bad text declaration
-- in it (xmlconf `ibm-1-1-valid-P03-ibm03v09.xml`: no encoding
-- declaration) is no fault of the document; the same text IS a fault
-- where a reference includes it.
def unreferencedEnt (decl ent : String) : Bool :=
  (parseXMLWith (entRes ent) (decl ++ "<!DOCTYPE a [<!ENTITY e SYSTEM \"e.ent\">]><a>text</a>")).toOption.isSome
#guard unreferencedEnt "<?xml version=\"1.1\"?>" "<?xml version=\"1.1\"?>x"
#guard unreferencedEnt "<?xml version=\"1.0\"?>" "<?xml version=\"1.0\"?>x"
#guard unreferencedEnt "" "<?xml version=\"1.1\" encoding=\"UTF-8\"?>x"
#guard !withEnt "<?xml version=\"1.1\"?>" "<?xml version=\"1.1\"?>x"
#guard !withEnt "<?xml version=\"1.0\"?>" "<?xml version=\"1.0\"?>x"
-- The same holds of an external PARAMETER entity.
def pe (decl ent refer : String) : Bool :=
  (parseXMLWith (entRes ent) (decl ++ "<!DOCTYPE a [<!ENTITY % e SYSTEM \"e.ent\">" ++ refer ++ "]><a>text</a>")).toOption.isSome
#guard pe "" "<?xml version=\"1.0\"?>" ""
#guard !pe "" "<?xml version=\"1.0\"?>" "%e;"
#guard pe "" "<?xml version=\"1.0\" encoding=\"UTF-8\"?>" "%e;"
-- XML 1.1 §2.11 applies to external entities, and §2.2 to their text.
#guard (match parseXMLWith (entRes "<?xml encoding=\"UTF-8\"?>x\u0085y") 
          (v11 "<!DOCTYPE a [<!ENTITY e SYSTEM \"e.ent\">]><a>&e;</a>") with
        | .ok d => some d.root.textContent
        | .error _ => none) == some "x\ny"
#guard (parseXMLWith (entRes "<?xml encoding=\"UTF-8\"?>x\u0090y")
          (v11 "<!DOCTYPE a [<!ENTITY e SYSTEM \"e.ent\">]><a>&e;</a>")).toOption.isNone
#guard (parseXMLWith (entRes "<?xml encoding=\"UTF-8\"?>x\r\ny")
          (v10 "<!DOCTYPE a [<!ENTITY e SYSTEM \"e.ent\">]><a>&e;</a>")).toOption.map
          (·.root.textContent) == some "x\ny"

-- The declaration's version is recorded, and it picks the rules for
-- NEL inside the DECLARATION itself: not whitespace, so refused.
#guard (match parseXML (v11 "<a/>") with | .ok d => d.version == .v11 | .error _ => false)
#guard (match parseXML (v10 "<a/>") with | .ok d => d.version == .v10 | .error _ => false)
#guard (match parseXML "<a/>" with | .ok d => d.version == .v10 | .error _ => false)
#guard !isWellFormed "<?xml version=\"1.1\"\u0085?><a/>"
#guard !isWellFormed "<?xml version=\"1.1\" ?><a/>"

-- Names (section 2.3) are the same set in 1.1 as in the Fifth Edition
-- of 1.0: the ranges #xC0-... and #x10000-#xEFFFF, and not #xF0000.
#guard isWellFormed (v11 "<ſ/>")
#guard isWellFormed (v10 "<ſ/>")
#guard isWellFormed (v11 "<a�/>")
#guard !isWellFormed (v11 ("<a" ++ String.singleton (Char.ofNat 0xF0000) ++ "/>"))
#guard isWellFormed (v11 ("<a" ++ String.singleton (Char.ofNat 0xEFFFF) ++ "/>"))
#guard !isWellFormed (v11 "<×/>")

-- The serialiser writes the characters that would not survive a re-parse
-- as character references, so a 1.1 document round-trips.
#guard roundTripsFrom (v11 "<a>&#1;&#xC;&#x85;&#x2028;&#13;x</a>")
#guard roundTripsFrom (v11 "<a x=\"&#1;&#x85;&#x2028;&#13;&#9;\"/>")
#guard roundTripsFrom (v10 "<a>&#x7F;&#x85;&#13;x</a>")
#guard (Document.toString (match parseXML (v11 "<a>&#1;</a>") with | .ok d => d | .error _ => default))
       == v11 "<a>&#x1;</a>"
-- The tree checker is version-aware: the same tree is a well-formed 1.1
-- document and not a 1.0 one.
#guard (match parseXML (v11 "<a>&#1;</a>") with | .ok d => d.wellFormed | .error _ => false)
#guard (match parseXML (v11 "<a>&#1;</a>") with
        | .ok d => Node.wellFormed .v10 d.root | .error _ => true) == false
#guard reflexiveOn (v11 "<a x=\"&#2;\">&#3;<!-- c --></a>")
-- The namespace layer reads the version from the same declaration.
#guard isNamespaceWellFormedDoc (v11 "<r xmlns:p=\"http://e/\"><s xmlns:p=\"\"/></r>")
#guard !isNamespaceWellFormedDoc (v10 "<r xmlns:p=\"http://e/\"><s xmlns:p=\"\"/></r>")

/-! ## Validity — XML 1.0 section 3 and the validity constraints elsewhere

`validateXML` parses, then checks the constraints. `vcs` is the set of
constraint names a document violates (`none` when it is not
well-formed); `valid` is "well-formed and no violation".

Each constraint has a document that breaks it and one that does not, so a
checker that answers "valid" for everything, or "invalid" for everything,
fails the build. -/

def noFiles : Resolver := fun _ => none
def files (fs : List (String × String)) : Resolver :=
  fun id => (fs.find? (fun f => f.1 == id)).map (·.2)

def vcsWith (r : Resolver) (doc : String) : Option (List String) :=
  match validateXML r doc with
  | .ok vs => some ((vs.map (·.vc)).eraseDups)
  | .error _ => none
def vcs (doc : String) : Option (List String) := vcsWith noFiles doc
def valid (doc : String) : Bool := vcs doc == some []
def breaks (vc : String) (doc : String) : Bool :=
  match vcs doc with
  | some l => l.contains vc
  | none => false

-- A document with no document type declaration is not valid (section 2.8).
#guard !valid "<a/>"
#guard breaks "Valid Document" "<a/>"
-- ...and a minimal valid one.
#guard valid "<!DOCTYPE a [<!ELEMENT a EMPTY>]><a/>"
-- Root Element Type.
#guard breaks "Root Element Type" "<!DOCTYPE b [<!ELEMENT a EMPTY>]><a/>"
#guard !breaks "Root Element Type" "<!DOCTYPE a [<!ELEMENT a EMPTY>]><a/>"

-- Element Valid: EMPTY means no content at all.
#guard valid "<!DOCTYPE a [<!ELEMENT a EMPTY>]><a></a>"
#guard breaks "Element Valid" "<!DOCTYPE a [<!ELEMENT a EMPTY>]><a> </a>"
#guard breaks "Element Valid" "<!DOCTYPE a [<!ELEMENT a EMPTY>]><a><!-- c --></a>"
#guard breaks "Element Valid" "<!DOCTYPE a [<!ELEMENT a EMPTY>]><a><?p x?></a>"
#guard breaks "Element Valid" "<!DOCTYPE a [<!ELEMENT a EMPTY>]><a>&amp;</a>"
-- ...not even a reference to an entity whose text is empty.
#guard breaks "Element Valid" "<!DOCTYPE a [<!ELEMENT a EMPTY><!ENTITY e \"\">]><a>&e;</a>"
-- ANY: every child element must be declared.
#guard valid "<!DOCTYPE a [<!ELEMENT a ANY><!ELEMENT b EMPTY>]><a>t<b/>t<!-- c --></a>"
#guard breaks "Element Valid" "<!DOCTYPE a [<!ELEMENT a ANY>]><a><b/></a>"
-- An element with no declaration at all.
#guard breaks "Element Valid" "<!DOCTYPE a [<!ELEMENT a ANY>]><a><z/></a>"
-- Mixed content: text and only the named children.
#guard valid "<!DOCTYPE a [<!ELEMENT a (#PCDATA|b)*><!ELEMENT b EMPTY>]><a>t<b/>u<b/></a>"
#guard valid "<!DOCTYPE a [<!ELEMENT a (#PCDATA)>]><a>text</a>"
#guard valid "<!DOCTYPE a [<!ELEMENT a (#PCDATA)*>]><a>text</a>"
#guard breaks "Element Valid" "<!DOCTYPE a [<!ELEMENT a (#PCDATA|b)*><!ELEMENT b EMPTY><!ELEMENT c EMPTY>]><a><c/></a>"
#guard breaks "Element Valid" "<!DOCTYPE a [<!ELEMENT a (#PCDATA)><!ELEMENT b EMPTY>]><a><b/></a>"
-- Element content: the sequence of children matches the model.
def seqDoc (model body : String) : String :=
  "<!DOCTYPE a [<!ELEMENT a " ++ model ++ "><!ELEMENT b EMPTY><!ELEMENT c EMPTY><!ELEMENT d EMPTY>]><a>" ++ body ++ "</a>"
#guard valid (seqDoc "(b,c)" "<b/><c/>")
#guard !valid (seqDoc "(b,c)" "<b/>")
#guard !valid (seqDoc "(b,c)" "<c/><b/>")
#guard !valid (seqDoc "(b,c)" "<b/><c/><c/>")
#guard !valid (seqDoc "(b,c)" "")
#guard valid (seqDoc "(b|c)" "<c/>")
#guard !valid (seqDoc "(b|c)" "<b/><c/>")
#guard !valid (seqDoc "(b|c)" "<d/>")
#guard valid (seqDoc "(b?,c)" "<c/>")
#guard valid (seqDoc "(b?,c)" "<b/><c/>")
#guard !valid (seqDoc "(b?,c)" "<b/><b/><c/>")
#guard !valid (seqDoc "(b?,c)" "")
#guard valid (seqDoc "(b?,c?)" "")
#guard valid (seqDoc "(b|c*)" "")
#guard !valid (seqDoc "(b|c)" "")
#guard valid (seqDoc "(b*)" "")
#guard valid (seqDoc "(b*)" "<b/><b/><b/>")
#guard !valid (seqDoc "(b+)" "")
#guard valid (seqDoc "(b+)" "<b/><b/>")
#guard valid (seqDoc "(b,(c|d)*,b?)" "<b/><c/><d/><c/>")
#guard valid (seqDoc "(b,(c|d)*,b?)" "<b/><c/><b/>")
#guard !valid (seqDoc "(b,(c|d)*,b?)" "<b/><b/><b/>")
#guard valid (seqDoc "((b,c)|d)+" "<b/><c/><d/><b/><c/>")
#guard !valid (seqDoc "((b,c)|d)+" "<b/><d/>")
#guard valid (seqDoc "(b*,b)" "<b/><b/>")
#guard valid (seqDoc "( b , c )" "<b/><c/>")
#guard valid (seqDoc "(b)" "<b/>")
-- White space between children is allowed; character data, a CDATA
-- section (even an empty one) and a character reference to white space
-- are not. Comments and processing instructions are.
#guard valid (seqDoc "(b,c)" " <b/>\n<c/> ")
#guard valid (seqDoc "(b,c)" "<b/><!-- c --><?p x?><c/>")
#guard breaks "Element Valid" (seqDoc "(b,c)" "<b/>x<c/>")
#guard breaks "Element Valid" (seqDoc "(b,c)" "<b/><![CDATA[ ]]><c/>")
#guard breaks "Element Valid" (seqDoc "(b,c)" "<b/><![CDATA[]]><c/>")
#guard breaks "Element Valid" (seqDoc "(b,c)" "<b/>&#32;<c/>")
-- ...but a literal white space inside an entity's replacement text is.
#guard valid "<!DOCTYPE a [<!ELEMENT a (b)><!ELEMENT b EMPTY><!ENTITY sp \" \">]><a>&sp;<b/></a>"
#guard breaks "Element Valid" "<!DOCTYPE a [<!ELEMENT a (b)><!ELEMENT b EMPTY><!ENTITY sp \"&#38;#32;\">]><a>&sp;<b/></a>"
-- A parsed model reads back as written.
#guard (match parseContentSpecText "(b, (c | d)*, e?)" with
        | some (.children cp) => cp.matches ["b", "c", "d", "c"] && !cp.matches ["c"]
        | _ => false)
#guard (match parseContentSpecText "(#PCDATA | b | c)*" with | some (.mixed ns) => ns == ["b", "c"] | _ => false)
#guard (match parseContentSpecText "EMPTY" with | some .empty => true | _ => false)
#guard (match parseContentSpecText "ANY" with | some .any => true | _ => false)

-- Declarations. Unique Element Type Declaration; No Duplicate Types.
#guard breaks "Unique Element Type Declaration" "<!DOCTYPE a [<!ELEMENT a EMPTY><!ELEMENT a EMPTY>]><a/>"
#guard breaks "No Duplicate Types" "<!DOCTYPE a [<!ELEMENT a (#PCDATA|a|a)*>]><a/>"
#guard !breaks "No Duplicate Types" "<!DOCTYPE a [<!ELEMENT a (#PCDATA|a)*>]><a/>"

-- Attributes. Required Attribute, Attribute Value Type (declared), Fixed.
def attDoc (decl attrs : String) : String :=
  "<!DOCTYPE a [<!ELEMENT a EMPTY><!ATTLIST a " ++ decl ++ ">]><a " ++ attrs ++ "/>"
#guard valid (attDoc "x CDATA #REQUIRED" "x=\"1\"")
#guard breaks "Required Attribute" (attDoc "x CDATA #REQUIRED" "")
#guard valid (attDoc "x CDATA #IMPLIED" "")
#guard breaks "Attribute Value Type" (attDoc "x CDATA #IMPLIED" "y=\"1\"")
#guard valid (attDoc "x CDATA #FIXED \"v\"" "x=\"v\"")
#guard valid (attDoc "x CDATA #FIXED \"v\"" "")
#guard breaks "Fixed Attribute Default" (attDoc "x CDATA #FIXED \"v\"" "x=\"w\"")
-- Types: ID, IDREF(S), ENTITY/ENTITIES, NMTOKEN(S), enumerations, notations.
#guard valid (attDoc "x ID #IMPLIED" "x=\"n1\"")
#guard breaks "ID" (attDoc "x ID #IMPLIED" "x=\"1n\"")
#guard breaks "ID" (attDoc "x ID #IMPLIED y ID #IMPLIED" "x=\"n\" y=\"n\"")
#guard breaks "One ID per Element Type" (attDoc "x ID #IMPLIED y ID #IMPLIED" "")
#guard breaks "ID Attribute Default" (attDoc "x ID \"d\"" "")
#guard breaks "ID Attribute Default" (attDoc "x ID #FIXED \"d\"" "")
#guard valid (attDoc "x ID #REQUIRED" "x=\"n\"")
#guard valid (attDoc "x ID #IMPLIED y IDREF #IMPLIED" "x=\"n\" y=\"n\"")
#guard breaks "IDREF" (attDoc "x ID #IMPLIED y IDREF #IMPLIED" "x=\"n\" y=\"m\"")
#guard breaks "IDREF" (attDoc "y IDREF #IMPLIED" "y=\"1x\"")
#guard valid (attDoc "x ID #IMPLIED y IDREFS #IMPLIED" "x=\"n\" y=\"n n\"")
#guard breaks "IDREF" (attDoc "x ID #IMPLIED y IDREFS #IMPLIED" "x=\"n\" y=\"n m\"")
#guard breaks "IDREFS" (attDoc "y IDREFS #IMPLIED" "y=\"\"")
#guard valid (attDoc "x NMTOKEN #IMPLIED" "x=\"1a-b\"")
#guard breaks "Name Token" (attDoc "x NMTOKEN #IMPLIED" "x=\"a b\"")
#guard valid (attDoc "x NMTOKENS #IMPLIED" "x=\"1a b2\"")
#guard breaks "Name Token" (attDoc "x NMTOKENS #IMPLIED" "x=\"a @\"")
#guard valid (attDoc "x (p|q) #IMPLIED" "x=\"p\"")
#guard breaks "Enumeration" (attDoc "x (p|q) #IMPLIED" "x=\"r\"")
#guard breaks "No Duplicate Tokens" (attDoc "x (p|p) #IMPLIED" "")
-- An enumerated value is compared after the type's normalisation.
#guard valid (attDoc "x (p|q) #IMPLIED" "x=\" p \"")
-- The value of a tokenized attribute is normalised before it is checked.
#guard valid (attDoc "x NMTOKENS #IMPLIED" "x=\"  a   b  \"")
-- Attribute Default Legal.
#guard breaks "Attribute Default Legal" (attDoc "x NMTOKEN \"a b\"" "")
#guard valid (attDoc "x NMTOKEN \"ab\"" "")
#guard breaks "Attribute Default Legal" (attDoc "x (p|q) \"r\"" "")
#guard breaks "Attribute Default Legal" (attDoc "x IDREF \"1\"" "")
#guard breaks "Attribute Default Legal" (attDoc "x IDREFS \"a 1\"" "")
-- A default is a value the processor supplies (section 3.3.2), so the value
-- constraints of the declared type apply to it: the IDREFS default below
-- names no ID, which is a violation of IDREF. (Until defaults were
-- supplied this document was reported valid, because the checks looked
-- at the specified attributes only.)
#guard breaks "IDREF" (attDoc "x IDREFS \"a b\"" "")
#guard valid (attDoc "x IDREFS \"i i\" i ID #IMPLIED" "i=\"i\"")
-- ENTITY attributes name unparsed entities, whose notations are declared.
def entDoc (decls attrs : String) : String :=
  "<!DOCTYPE a [<!ELEMENT a ANY><!NOTATION n SYSTEM \"x\"><!ENTITY u SYSTEM \"x\" NDATA n>" ++ decls ++ "]><a " ++ attrs ++ "/>"
#guard valid (entDoc "<!ATTLIST a e ENTITY #IMPLIED>" "e=\"u\"")
#guard breaks "Entity Name" (entDoc "<!ATTLIST a e ENTITY #IMPLIED>" "e=\"v\"")
#guard breaks "Entity Name" (entDoc "<!ENTITY p \"text\"><!ATTLIST a e ENTITY #IMPLIED>" "e=\"p\"")
#guard valid (entDoc "<!ATTLIST a e ENTITIES #IMPLIED>" "e=\"u u\"")
#guard breaks "Entity Name" (entDoc "<!ATTLIST a e ENTITIES #IMPLIED>" "e=\"u v\"")
#guard breaks "Notation Declared" "<!DOCTYPE a [<!ELEMENT a EMPTY><!ENTITY u SYSTEM \"x\" NDATA zz>]><a/>"
#guard valid (entDoc "<!ATTLIST a nt NOTATION (n) #IMPLIED>" "nt=\"n\"")
#guard breaks "Notation Attributes" (entDoc "<!ATTLIST a nt NOTATION (n) #IMPLIED>" "nt=\"m\"")
#guard breaks "Notation Attributes" (entDoc "<!ATTLIST a nt NOTATION (zz) #IMPLIED>" "")
#guard breaks "One Notation Per Element Type"
  (entDoc "<!ATTLIST a nt NOTATION (n) #IMPLIED nu NOTATION (n) #IMPLIED>" "")
#guard breaks "No Notation on Empty Element"
  "<!DOCTYPE a [<!ELEMENT a EMPTY><!NOTATION n SYSTEM \"x\"><!ATTLIST a nt NOTATION (n) #IMPLIED>]><a/>"
-- xml:space, when used, must be declared as an enumeration offering one of
-- its two values (section 2.10); xml:lang must be declared like any other.
#guard valid "<!DOCTYPE a [<!ELEMENT a EMPTY><!ATTLIST a xml:space (default|preserve) #IMPLIED>]><a xml:space=\"preserve\"/>"
#guard breaks "Attribute Value Type" "<!DOCTYPE a [<!ELEMENT a EMPTY>]><a xml:space=\"preserve\"/>"
#guard breaks "Attribute Value Type" "<!DOCTYPE a [<!ELEMENT a EMPTY><!ATTLIST a xml:space CDATA #IMPLIED>]><a xml:space=\"preserve\"/>"
#guard breaks "Attribute Value Type" "<!DOCTYPE a [<!ELEMENT a EMPTY>]><a xml:lang=\"en\"/>"
-- An attribute that is only a namespace declaration is an attribute too.
#guard breaks "Attribute Value Type" "<!DOCTYPE a [<!ELEMENT a EMPTY>]><a xmlns:p=\"http://e/\"/>"
-- ID values are unique across the document.
#guard valid "<!DOCTYPE a [<!ELEMENT a (b,b)><!ELEMENT b EMPTY><!ATTLIST b i ID #REQUIRED>]><a><b i=\"x\"/><b i=\"y\"/></a>"
#guard breaks "ID" "<!DOCTYPE a [<!ELEMENT a (b,b)><!ELEMENT b EMPTY><!ATTLIST b i ID #REQUIRED>]><a><b i=\"x\"/><b i=\"x\"/></a>"

-- The first declaration of an attribute is binding (section 3.3).
#guard valid (attDoc "x CDATA #IMPLIED x ID #IMPLIED" "x=\"1 \"")
#guard breaks "ID" "<!DOCTYPE a [<!ELEMENT a EMPTY><!ATTLIST a x ID #IMPLIED x CDATA #IMPLIED>]><a x=\"1 \"/>"

-- Entity Declared (4.1): with a parameter-entity reference in the DTD an
-- undeclared general entity is a validity error, not a well-formedness one.
#guard breaks "Entity Declared"
  "<!DOCTYPE a [<!ENTITY % pe \"<!ENTITY e 't'>\">%pe;<!ELEMENT a ANY>]><a>&z;</a>"
#guard valid
  "<!DOCTYPE a [<!ENTITY % pe \"<!ENTITY e 't'>\">%pe;<!ELEMENT a ANY>]><a>&e;</a>"

-- Parameter-entity nesting (sections 2.8, 3.2.1, 3.4), in an external
-- subset.
def extDoc (dtd : String) : Option (List String) :=
  vcsWith (files [("x.dtd", dtd)]) "<!DOCTYPE a SYSTEM \"x.dtd\"><a/>"
#guard extDoc "<!ELEMENT a EMPTY>" == some []
#guard extDoc "<!ENTITY % e \"(#PCDATA\"><!ELEMENT a %e;)>" == some ["Proper Group/PE Nesting"]
#guard extDoc "<!ENTITY % e \"(b,c)?\"><!ELEMENT b EMPTY><!ELEMENT c EMPTY><!ELEMENT a %e;>" == some []
#guard extDoc "<!ENTITY % e \">\"><!ELEMENT a (#PCDATA) %e;" == some ["Proper Declaration/PE Nesting"]
#guard extDoc "<!ENTITY % e \"EMPTY\"><!ELEMENT a %e;>" == some []
#guard extDoc "<!ENTITY % e \"INCLUDE[\"><!ELEMENT a EMPTY><![ %e; <!ATTLIST a x CDATA \"v\"> ]]>"
       == some ["Proper Conditional Section/PE Nesting"]
#guard extDoc "<!ENTITY % e \"INCLUDE\"><!ELEMENT a EMPTY><![ %e; [ <!ATTLIST a x CDATA \"v\"> ]]>" == some []

-- ...and in an external parameter entity that the INTERNAL subset
-- references. WFC PEs in Internal Subset (section 2.8) keeps a reference
-- out of the markup declarations of the internal subset itself, "(This
-- does not apply to references that occur in external parameter entities
-- or to the external subset.)" The text of such an entity is read as the
-- external subset's is, and the nesting constraints apply to it.
def intDoc (ent : String) : Option (List String) :=
  vcsWith (files [("x.ent", ent)]) "<!DOCTYPE a [<!ENTITY % x SYSTEM \"x.ent\">%x;]><a/>"
#guard intDoc "<!ELEMENT a EMPTY>" == some []
#guard intDoc "<!ENTITY % e \"EMPTY\"><!ELEMENT a %e;>" == some []
#guard intDoc "<!ENTITY % e \"(b,c)?\"><!ELEMENT b EMPTY><!ELEMENT c EMPTY><!ELEMENT a %e;>" == some []
#guard intDoc "<!ENTITY % e \"(#PCDATA\"><!ELEMENT a %e;)>" == some ["Proper Group/PE Nesting"]
#guard intDoc "<!ENTITY % e \">\"><!ELEMENT a (#PCDATA) %e;" == some ["Proper Declaration/PE Nesting"]
#guard intDoc "<!ENTITY % e \"INCLUDE[\"><!ELEMENT a EMPTY><![ %e; <!ATTLIST a x CDATA \"v\"> ]]>"
       == some ["Proper Conditional Section/PE Nesting"]
#guard intDoc "<!ENTITY % e \"INCLUDE\"><!ELEMENT a EMPTY><![ %e; [ <!ATTLIST a x CDATA \"v\"> ]]>" == some []
-- An entity declared in that entity, whose replacement text holds a
-- reference written as a character reference, is included inside the
-- external context too.
#guard intDoc "<!ENTITY % c \"EMPTY\"><!ENTITY % e \"<!ELEMENT a &#37;c;>\">%e;" == some []
-- The same references inside a declaration of the internal subset are not
-- well-formed, with or without an entity between.
#guard vcs "<!DOCTYPE a [<!ENTITY % c \"EMPTY\"><!ELEMENT a %c;>]><a/>" == none
#guard vcs "<!DOCTYPE a [<!ENTITY % c \"EMPTY\"><!ENTITY % e \"<!ELEMENT a &#37;c;>\">%e;]><a/>" == none
-- A reference between declarations whose replacement text is not whole
-- declarations is not well-formed (WFC PE Between Declarations), so the
-- nesting constraint cannot be the one it breaks.
#guard vcs "<!DOCTYPE a [<!ENTITY % e \"<!ELEMENT a EMPTY\">%e;>]><a/>" == none
#guard vcs "<!DOCTYPE a [<!ENTITY % e \"<!ELEMENT a EMPTY>\">%e;]><a/>" == some []

-- Standalone Document Declaration (2.9): nothing read from outside the
-- document may decide the content of a document that says standalone=yes.
def saDoc (standalone dtd body : String) : Option (List String) :=
  vcsWith (files [("x.dtd", dtd)])
    ("<?xml version=\"1.0\" standalone=\"" ++ standalone ++ "\"?><!DOCTYPE a SYSTEM \"x.dtd\"><a>" ++ body ++ "</a>")
-- an externally declared default the element leaves out
#guard saDoc "yes" "<!ELEMENT a EMPTY><!ATTLIST a x CDATA \"d\">" "" == some ["Standalone Document Declaration"]
#guard saDoc "no" "<!ELEMENT a EMPTY><!ATTLIST a x CDATA \"d\">" "" == some []
#guard saDoc "yes" "<!ELEMENT a EMPTY><!ATTLIST a x CDATA #IMPLIED>" "" == some []
-- ...but not when the element gives the value itself
#guard vcsWith (files [("x.dtd", "<!ELEMENT a EMPTY><!ATTLIST a x CDATA \"d\">")])
  "<?xml version=\"1.0\" standalone=\"yes\"?><!DOCTYPE a SYSTEM \"x.dtd\"><a x=\"v\"/>" == some []
-- white space directly inside an externally declared element-content type
#guard saDoc "yes" "<!ELEMENT a (b)><!ELEMENT b EMPTY>" " <b/>" == some ["Standalone Document Declaration"]
#guard saDoc "yes" "<!ELEMENT a (b)><!ELEMENT b EMPTY>" "<b/>" == some []
#guard saDoc "no" "<!ELEMENT a (b)><!ELEMENT b EMPTY>" " <b/>" == some []
-- a tokenized attribute whose value normalisation would change
#guard vcsWith (files [("x.dtd", "<!ELEMENT a EMPTY><!ATTLIST a x NMTOKENS #IMPLIED>")])
  "<?xml version=\"1.0\" standalone=\"yes\"?><!DOCTYPE a SYSTEM \"x.dtd\"><a x=\" p  q \"/>"
  == some ["Standalone Document Declaration"]
#guard vcsWith (files [("x.dtd", "<!ELEMENT a EMPTY><!ATTLIST a x NMTOKENS #IMPLIED>")])
  "<?xml version=\"1.0\" standalone=\"yes\"?><!DOCTYPE a SYSTEM \"x.dtd\"><a x=\"p q\"/>" == some []
-- declared in the INTERNAL subset, the same document is standalone
#guard vcsWith noFiles
  "<?xml version=\"1.0\" standalone=\"yes\"?><!DOCTYPE a [<!ELEMENT a EMPTY><!ATTLIST a x NMTOKENS #IMPLIED>]><a x=\" p  q \"/>"
  == some []

-- A document the parser refuses has no verdict.
#guard vcs "<!DOCTYPE a [<!ELEMENT a EMPTY>]><a></b>" == none

/-! ## RDF/XML checks — `XML.Wellformedness.fst`'s other half -/

#guard isForbiddenNodeElementName "http://www.w3.org/1999/02/22-rdf-syntax-ns#li"
#guard !isForbiddenPropertyElementName "http://www.w3.org/1999/02/22-rdf-syntax-ns#li"
#guard isForbiddenPropertyElementName "http://www.w3.org/1999/02/22-rdf-syntax-ns#Description"
#guard checkConflictingAttrsNode [{ name := "rdf:ID", value := "x" },
                                  { name := "rdf:about", value := "y" }]
       == some "conflicting rdf:ID and rdf:about on a node element"
#guard checkConflictingAttrsProperty [{ name := "rdf:ID", value := "x" },
                                      { name := "rdf:about", value := "y" }] == none
#guard validateRdfIdAttr [{ name := "rdf:ID", value := "a:b" }]
       == some "Invalid rdf:ID value: a:b"

/-! ## Reflexivity of the well-formedness checker

Evidence for `ReflexiveOnParserOutput` on fixtures — NOT a proof of it.
The tag-matching component IS proved, in
`Node.serialize_element_tags_match`. -/

#guard reflexiveOn hubXML
#guard reflexiveOn "<a/>"
#guard reflexiveOn "<a x=\"1\"><b>t</b><!-- c --><![CDATA[d]]><?p e?></a>"
#guard reflexiveOn "<?xml version=\"1.0\"?><!-- p --><!DOCTYPE a><a>日本</a><!-- e -->"
-- The checker is stated on the INFOSET, so it accepts characters the
-- SYNTAX forbids but a reference legally introduces.
#guard reflexiveOn "<a x=\"&lt;\">]]&gt;</a>"

/-! ## Round-trip: `parseXML (Document.toString d) = .ok d`

Evidence for `RoundTripsOnParse` on fixtures — NOT a proof of it. The
STRING deliberately does not round-trip: `<a></a>` serialises as
`<a/>`, because the infoset is what the parser is a function into. -/

#guard roundTripsFrom hubXML
#guard roundTripsFrom "<a/>"
#guard roundTripsFrom "<a></a>"
#guard roundTripsFrom "<a x=\"1\" y=\"2\">text</a>"
#guard roundTripsFrom "<a x=\"&lt;&amp;&quot;\"/>"
-- Tab / LF / CR in an attribute value survive as character references,
-- so §3.3.3 normalisation does not flatten them on the way back in.
#guard roundTripsFrom "<a x=\"&#9;&#10;tab\"/>"
#guard roundTripsFrom "<a><!-- c --><![CDATA[x < y]]><?p d?></a>"
#guard roundTripsFrom "<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"yes\"?><a/>"
#guard roundTripsFrom "<!-- p --><?pi d?><a/><!-- e -->"
#guard roundTripsFrom "<!DOCTYPE a [<!ENTITY e \"val\"><!ENTITY f \"two\">]><a>&e;&f;</a>"
#guard roundTripsFrom "<!DOCTYPE a [<!ATTLIST a k ID #IMPLIED>]><a k=\"v\"/>"
#guard roundTripsFrom "<a>日本語 café</a>"
#guard roundTripsFrom "<日本 x=\"1\">t</日本>"
#guard roundTripsFrom "<a>]]&gt; and &lt;</a>"
#guard roundTripsFrom "<r xmlns:p=\"http://e/\" xmlns=\"http://d/\"><p:c a=\"1\"/></r>"

/-! ## Axiom audit

Every build log carries these lines. The acceptable base is exactly
Lean's standard foundations; no `sorry`, no user `axiom`, no
`native_decide`. -/

#print axioms Node.serialize_element_tags_match
#print axioms Node.wellFormedList_eq_all
#print axioms Node.wellFormed_of_mem_children
#print axioms Node.serializeList_cons
#print axioms normalizeLineEndings11TR_eq
#print axioms normalizeLineEndings11_eq_normalizeLineEndings11Impl
#print axioms parseXML
#print axioms isNamespaceWellFormed

/-! ## `[70]`–`[76]` EntityDecl, `[28]` doctypedecl, `[69]` PEReference

Each `#guard` below pins a document the parser said YES to. A
well-formedness checker that ACCEPTS malformed input reports nothing;
one that rejects valid input at least announces itself, which is why
the accept direction is the one that hides. -/

private def wf (src : String) : Bool := isWellFormed src

/-- Well-formedness with a caller that CAN read the one external
entity these cases declare. Its text is a well-formed
`[78] extParsedEnt` with a valid `[77] TextDecl`, so nothing about the
entity FILE can decide the cases below; only the constraint under test
can. -/
private def wfExt (body : String) (src : String) : Bool :=
  isWellFormedWith (fun sysId => if sysId == "e.ent" then some body else none) src

-- [75]: the PUBLIC form requires a SystemLiteral after the
-- PubidLiteral (not-wf-sa-054), and the space between them
-- (not-wf-sa-061).
#guard !(wf "<!DOCTYPE doc [\n<!ENTITY foo PUBLIC \"some public id\">\n]>\n<doc></doc>")
#guard !(wf "<!DOCTYPE doc [\n<!ENTITY e PUBLIC \"whatever\"\"e.ent\">\n]>\n<doc></doc>")
-- ...and the space after `PUBLIC` itself (o-p75fail1).
#guard !(wf "<!DOCTYPE doc [\n<!ENTITY ent PUBLIC\"PublicID\" \"nop.ent\">\n]>\n<doc/>")
#guard wf "<!DOCTYPE doc [\n<!ENTITY e PUBLIC \"whatever\" \"e.ent\">\n]>\n<doc></doc>"

-- A declaration ends at `S? '>'` and nothing else (not-wf-sa-057).
#guard !(wf "<!DOCTYPE doc [\n<!ENTITY e \"whatever\" -- a comment -->\n]>\n<doc></doc>")

-- [76] NDataDecl begins with S (not-wf-sa-069, o-p76fail1).
#guard !(wf ("<!DOCTYPE doc [\n<!NOTATION eps SYSTEM \"eps.exe\">\n" ++
             "<!ENTITY foo SYSTEM \"foo.eps\"NDATA eps>\n]>\n<doc></doc>"))
#guard wf ("<!DOCTYPE doc [\n<!NOTATION eps SYSTEM \"eps.exe\">\n" ++
           "<!ENTITY foo SYSTEM \"foo.eps\" NDATA eps>\n]>\n<doc></doc>")

-- [72] PEDecl requires the space after `%` (o-p72fail2), and [74]
-- PEDef admits no NDataDecl (o-p74fail1).
#guard !(wf "<!DOCTYPE doc [\n<!ENTITY %pe \"<!---->\">\n]>\n<doc/>")
#guard wf "<!DOCTYPE doc [\n<!ENTITY % pe \"<!---->\">\n]>\n<doc/>"
#guard !(wf ("<!DOCTYPE doc [\n<!NOTATION unknot PUBLIC \"Unknown\">\n" ++
             "<!ENTITY % pe SYSTEM \"nop.ent\" NDATA unknot>\n]>\n<doc/>"))

-- [73] EntityDef is an EntityValue or an ExternalID; `CDATA` is
-- neither (o-p73fail1).
#guard !(wf "<!DOCTYPE doc [\n<!ENTITY ge CDATA \"replacement text\">\n]>\n<doc/>")

-- [28] admits `(S ExternalID)?` between the Name and the subset, and
-- nothing else — a comment there is not part of the production
-- (not-wf-sa-056).
#guard !(wf "<!DOCTYPE doc -- a comment -- []>\n<doc></doc>")
#guard wf "<!DOCTYPE doc []>\n<doc></doc>"
#guard wf "<!DOCTYPE doc SYSTEM \"doc.dtd\">\n<doc></doc>"
#guard wf "<!DOCTYPE doc PUBLIC \"pub\" \"doc.dtd\" []>\n<doc></doc>"

-- [69] PEReference is `'%' Name ';'`: no space, and a Name is
-- required (o-p69fail2).
#guard !(wf "<!DOCTYPE doc [\n<!ENTITY % pe \"<!---->\">\n% pe;\n]>\n<doc/>")
#guard wf "<!DOCTYPE doc [\n<!ENTITY % pe \"<!---->\">\n%pe;\n]>\n<doc/>"

/-! ## §4.4.2 Included: an entity's replacement text is CONTENT

The parser used to REFUSE any entity whose replacement text held a
`<`: "entity replacement text contains markup; unsupported". That was
an honest refusal rather than a wrong splice, and it still rejected
documents the specification calls well-formed — the whole
`valid/ext-sa` family and several `valid/sa` cases.

The replacement text is now reparsed as `[43] content` and the nodes
spliced in at the reference. -/

#guard wf "<!DOCTYPE doc [<!ENTITY e \"<foo/>\">]><doc>&e;</doc>"
#guard wf "<!DOCTYPE doc [<!ENTITY e \"<foo/>\">]><doc>a&e;b</doc>"
-- WFC: Parsed Entity — the fragment must parse as content in full.
#guard !(wf "<!DOCTYPE doc [<!ENTITY e \"<foo>\">]><doc>&e;</doc>")
#guard !(wf "<!DOCTYPE doc [<!ENTITY e \"</foo>\">]><doc>&e;</doc>")

/-! ## §4.5: which references are expanded to build the replacement text

A CHARACTER reference is expanded when the replacement text is built;
a GENERAL-entity reference is bypassed and included at the reference
site instead. That difference is what decides whether a `<` in the
text is MARKUP, and collapsing the two gets one of this pair wrong
whichever way it falls. -/

-- `&#60;` is expanded here, so the replacement text IS `<foo></foo>`
-- and reparsing gives an ELEMENT (valid/sa/024).
#guard wf ("<!DOCTYPE doc [<!ELEMENT doc (foo)><!ELEMENT foo (#PCDATA)>" ++
           "<!ENTITY e \"&#60;foo></foo>\">]><doc>&e;</doc>")
-- `&lt;` is a general entity and is bypassed, so the replacement text
-- is still `&lt;foo>` and reparsing gives the TEXT `<foo>`
-- (valid/sa/088).
#guard wf ("<!DOCTYPE doc [<!ELEMENT doc (#PCDATA)>" ++
           "<!ENTITY e \"&lt;foo>\">]><doc>&e;</doc>")
-- A character reference inside markup is expanded too (valid/sa/087).
#guard wf ("<!DOCTYPE doc [<!ENTITY e \"<foo/&#62;\">" ++
           "<!ELEMENT doc (foo)><!ELEMENT foo EMPTY>]><doc>&e;</doc>")
-- CDATA inside an entity survives (valid/sa/114).
#guard wf ("<!DOCTYPE doc [<!ELEMENT doc (#PCDATA)>" ++
           "<!ENTITY e \"<![CDATA[&foo;]]>\">]><doc>&e;</doc>")

/-! ## `[9] EntityValue` is a production, not a run of characters

`normalizeEntityValue` copied every character through except a
character reference, so a bare `&` and a `%` in the internal subset
were accepted. Each of these is a document the parser said YES to. -/

-- A bare `&` must begin a Reference (not-wf-sa-113, -114). CDATA is
-- NOT recognised inside an entity value, so the `&` there is as bare
-- as any other (not-wf-sa-159).
#guard !(wf "<!DOCTYPE doc [\n<!ENTITY foo \"&\">\n]>\n<doc></doc>")
#guard !(wf "<!DOCTYPE doc [\n<!ENTITY % foo \"&\">\n]>\n<doc></doc>")
#guard !(wf ("<!DOCTYPE doc [<!ELEMENT doc (#PCDATA)>" ++
             "<!ENTITY e \"<![CDATA[Tim & Michael]]>\">]><doc>&e;</doc>"))
#guard wf "<!DOCTYPE doc [\n<!ENTITY foo \"&amp;\">\n]>\n<doc></doc>"

-- §4.4.8: a parameter-entity reference may appear in an entity value
-- only in the EXTERNAL subset (not-wf-sa-160, -162).
#guard !(wf ("<!DOCTYPE doc [<!ELEMENT doc (#PCDATA)>" ++
             "<!ENTITY % e \"\"><!ENTITY foo \"%e;\">]><doc></doc>"))
#guard !(wf ("<!DOCTYPE doc [<!ELEMENT doc (#PCDATA)>" ++
             "<!ENTITY % e1 \"\"><!ENTITY % e2 \"%e1;\">]><doc></doc>"))

/-! ## An attribute DEFAULT is an `[10] AttValue`

The well-formedness constraints on an attribute value apply to a
default value too, and none of them was checked. -/

-- WFC: Entity Declared, and "already" is the word — an entity
-- declared AFTER the ATTLIST does not count (not-wf-sa-180).
#guard !(wf ("<!DOCTYPE doc [<!ELEMENT doc (#PCDATA)>" ++
             "<!ATTLIST doc a CDATA \"&e;\"><!ENTITY e \"v\">]><doc></doc>"))
#guard wf ("<!DOCTYPE doc [<!ELEMENT doc (#PCDATA)><!ENTITY e \"v\">" ++
           "<!ATTLIST doc a CDATA \"&e;\">]><doc></doc>")
-- ...and an undeclared one is an error (not-wf-sa-078).
#guard !(wf ("<!DOCTYPE doc [<!ELEMENT doc (#PCDATA)>" ++
             "<!ATTLIST doc a CDATA \"&foo;\">]><doc></doc>"))
-- WFC: No Recursion (not-wf-sa-079, -080).
#guard !(wf ("<!DOCTYPE doc [<!ENTITY e1 \"&e2;\"><!ENTITY e2 \"&e3;\">" ++
             "<!ENTITY e3 \"&e1;\"><!ELEMENT doc (#PCDATA)>" ++
             "<!ATTLIST doc a CDATA \"&e1;\">]><doc></doc>"))

/-! ## WFC: No External Entity References (section 4.4.4)

Section 4.4.4 makes a reference to an external parsed entity
FORBIDDEN in an attribute value, directly or indirectly, and
`Included if validating` in content. The constraint is about the
DECLARATION, so it holds whether or not the entity's text can be read.

`ibm-not-wf-P41-ibm41n10.xml` and `ibm-not-wf-P41-ibm41n11.xml` name
this constraint, but their entity files independently violate `[77]`
(they open `<?xml verison="1.0"?>` — `version` misspelt, so no
`encoding` pseudo-attribute is present) and are rejected for that
before an attribute is reached. They therefore cannot witness this
constraint, and these cases do. -/

private def okEnt : String := "<?xml version=\"1.0\" encoding=\"UTF-8\"?>any"

-- Direct: the attribute value references the external entity itself.
#guard !(wfExt okEnt ("<!DOCTYPE root [<!ELEMENT root ANY>" ++
           "<!ATTLIST root a CDATA #IMPLIED>" ++
           "<!ENTITY ext SYSTEM \"e.ent\">]><root a=\"&ext;\"></root>"))
-- Indirect: through an internal entity whose replacement text
-- references it.
#guard !(wfExt okEnt ("<!DOCTYPE root [<!ELEMENT root ANY>" ++
           "<!ATTLIST root a CDATA #IMPLIED>" ++
           "<!ENTITY ext SYSTEM \"e.ent\"><!ENTITY ind \"&ext;\">" ++
           "]><root a=\"&ind;\"></root>"))
-- In an attribute DEFAULT, which is an `[10] AttValue` as well.
#guard !(wfExt okEnt ("<!DOCTYPE root [<!ELEMENT root ANY>" ++
           "<!ENTITY ext SYSTEM \"e.ent\">" ++
           "<!ATTLIST root a CDATA \"&ext;\">]><root></root>"))
-- The SAME reference in CONTENT is admitted: section 4.4.3 Included
-- if validating, not Forbidden. Without this the three above would
-- also hold of a parser that simply refused every external entity.
#guard wfExt okEnt ("<!DOCTYPE root [<!ELEMENT root ANY>" ++
           "<!ENTITY ext SYSTEM \"e.ent\">]><root>&ext;</root>")
-- And an INTERNAL entity in an attribute value is admitted, so the
-- three above turn on `external`, not on the reference itself.
#guard wfExt okEnt ("<!DOCTYPE root [<!ELEMENT root ANY>" ++
           "<!ATTLIST root a CDATA #IMPLIED>" ++
           "<!ENTITY int \"v\">]><root a=\"&int;\"></root>")

/-! ## Attribute defaults — XML 1.0 §3.3.2 and §5.1

"If the declaration is of a default value, the processor supplies the
default when the attribute is not specified" (§3.3.2), and a processor
that has read the declaration must do so even when it does not validate
(§5.1). The tree shows the supplied attributes after the specified ones,
in the order of the declarations; the parser's notes name them. -/

/-- The attributes of the root of `src`, as (name, value), or `none` when
the document is refused. -/
def rootAttrsWith (r : Resolver) (src : String) : Option (List (String × String)) :=
  match parseXMLWith r src with
  | .ok d => some (d.root.elementAttrs.map (fun a => (a.name, a.value)))
  | .error _ => none
def rootAttrs (src : String) : Option (List (String × String)) := rootAttrsWith noFiles src

-- A declared default is supplied; a specified value wins over it.
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x CDATA \"d\">]><a/>" == some [("x", "d")]
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x CDATA \"d\">]><a x=\"v\"/>" == some [("x", "v")]
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x CDATA \"d\">]><a></a>" == some [("x", "d")]
-- #FIXED supplies its value as a default too (§3.3.2).
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x CDATA #FIXED \"f\">]><a/>" == some [("x", "f")]
-- #REQUIRED and #IMPLIED supply nothing.
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x CDATA #REQUIRED>]><a/>" == some []
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x CDATA #IMPLIED>]><a/>" == some []
-- A declaration for another element type supplies nothing.
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST b x CDATA \"d\">]><a/>" == some []
-- No document type declaration: nothing to read.
#guard rootAttrs "<a/>" == some []
-- Specified attributes come first, then the defaults in declaration order.
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x CDATA \"1\" y CDATA \"2\" z CDATA \"3\">]><a y=\"s\"/>"
       == some [("y", "s"), ("x", "1"), ("z", "3")]
-- The first declaration of an attribute is binding (§3.3).
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x CDATA \"first\"><!ATTLIST a x CDATA \"second\">]><a/>"
       == some [("x", "first")]
-- Every element of the type gets it, nested ones and those that arrive in
-- an entity's replacement text.
#guard (match parseXML "<!DOCTYPE a [<!ATTLIST b x CDATA \"d\">]><a><b/><b x=\"s\"/></a>" with
        | .ok d => (d.root.elementChildren.map (fun c => c.elementAttrs.map (fun t => (t.name, t.value))))
                     == [[("x", "d")], [("x", "s")]]
        | .error _ => false)
#guard (match parseXML "<!DOCTYPE a [<!ATTLIST b x CDATA \"d\"><!ENTITY e \"<b/>\">]><a>&e;</a>" with
        | .ok d => (d.root.elementChildren.map (fun c => c.elementAttrs.map (fun t => (t.name, t.value))))
                     == [[("x", "d")]]
        | .error _ => false)
-- §3.3.3 applies to the default as to a specified value: literal white
-- space becomes a space, references are replaced, character references to
-- white space are kept, and a value of a type other than CDATA is
-- collapsed.
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x CDATA \"p\tq\">]><a/>" == some [("x", "p q")]
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x CDATA \"p&#9;q\">]><a/>" == some [("x", "p\tq")]
#guard rootAttrs "<!DOCTYPE a [<!ENTITY e \"v\"><!ATTLIST a x CDATA \"1&e;2&lt;3\">]><a/>" == some [("x", "1v2<3")]
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x NMTOKENS \"  p   q \">]><a/>" == some [("x", "p q")]
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x (p|q) \" q \">]><a/>" == some [("x", "q")]
-- ...and a specified value is still normalised by its declared type.
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x NMTOKENS \"d\">]><a x=\" p   q \"/>" == some [("x", "p q")]
-- The parser's notes name the attributes it supplied, and only those.
def definedNames (src : String) : Option (List (List String)) :=
  match parseXMLNotes noFiles false src with
  | .ok (_, n) => some (n.elems.reverse.map (·.defaulted))
  | .error _ => none
#guard definedNames "<!DOCTYPE a [<!ATTLIST a x CDATA \"1\" y CDATA \"2\">]><a y=\"s\"/>" == some [["x"]]
#guard definedNames "<!DOCTYPE a [<!ATTLIST a x CDATA \"1\">]><a x=\"s\"/>" == some [[]]
-- The external subset is read when the caller can supply it, and its
-- defaults are supplied; when it cannot be read, they are not.
#guard rootAttrsWith (files [("x.dtd", "<!ATTLIST a x CDATA \"ext\">")]) "<!DOCTYPE a SYSTEM \"x.dtd\"><a/>"
       == some [("x", "ext")]
#guard rootAttrs "<!DOCTYPE a SYSTEM \"x.dtd\"><a/>" == some []
-- A declaration made after a parameter-entity reference that was NOT read
-- is not processed (§5.1) unless the document is standalone.
#guard rootAttrs "<!DOCTYPE a [%unread;<!ATTLIST a x CDATA \"d\">]><a/>" == some []
#guard rootAttrs "<?xml version=\"1.0\" standalone=\"yes\"?><!DOCTYPE a [%unread;<!ATTLIST a x CDATA \"d\">]><a/>"
       == some [("x", "d")]
#guard rootAttrs "<!DOCTYPE a [<!ATTLIST a x CDATA \"d\">%unread;]><a/>" == some [("x", "d")]
-- A default `xmlns` declaration is a namespace declaration (Namespaces in
-- XML 1.0 §3): the document below is namespace-well-formed only because
-- the prefix is bound by the supplied attribute.
#guard (match parseXML "<!DOCTYPE p:a [<!ATTLIST p:a xmlns:p CDATA \"urn:u\">]><p:a/>" with
        | .ok d => d.namespaceWellFormed
        | .error _ => false)
#guard (match parseXML "<!DOCTYPE p:a [<!ATTLIST p:a q CDATA \"urn:u\">]><p:a/>" with
        | .ok d => !d.namespaceWellFormed
        | .error _ => false)
-- Standalone Document Declaration reads the supplied attributes: a default
-- declared outside the document breaks it, one declared inside does not.
#guard saDoc "yes" "<!ELEMENT a EMPTY><!ATTLIST a x CDATA #FIXED \"d\">" "" == some ["Standalone Document Declaration"]
#guard vcsWith noFiles
  "<?xml version=\"1.0\" standalone=\"yes\"?><!DOCTYPE a [<!ELEMENT a EMPTY><!ATTLIST a x CDATA \"d\">]><a/>" == some []
-- A supplied value is checked as a specified one is.
#guard vcsWith noFiles "<!DOCTYPE a [<!ELEMENT a EMPTY><!ATTLIST a x CDATA #FIXED \"d\">]><a/>" == some []
#guard vcsWith noFiles "<!DOCTYPE a [<!ELEMENT a EMPTY><!ATTLIST a x CDATA #FIXED \"d\">]><a x=\"e\"/>"
       == some ["Fixed Attribute Default"]

end L4Factoidal.XML.Tests
