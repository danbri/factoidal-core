/-
L4Factoidal.XML.XmlAttributes — the three attributes of the reserved
`xml` prefix that carry a value syntax: `xml:lang`, `xml:id` and
`xml:base`.

This is a CHECK over a parsed `Document`, in the namespace-aware layer:
it names the attributes by their expanded name (the `xml` prefix is bound
to `http://www.w3.org/XML/1998/namespace` and to nothing else, Namespaces
in XML 1.0 §3), and it reports what is wrong with their values. It does
not change what `parseXML` accepts. XML 1.0 §2.12, xml:id §6 and XML Base
all make a bad value an error of the application layer, not a
well-formedness error.

## The three values

* **`xml:lang`** — XML 1.0 (Fifth Edition) §2.12: "The values of the
  attribute are language identifiers as defined by [IETF BCP 47], Tags for
  the Identification of Languages; in addition, the empty string may be
  specified." BCP 47 is RFC 5646 (with RFC 4647 for matching). The check is
  RFC 5646 §2.1, `Language-Tag`: `langtag`, `privateuse` or a
  `grandfathered` tag, and it is the SYNTAX of §2.2.9 ("well-formed"). It
  does not consult the IANA language subtag registry, so a tag with a
  well-formed subtag the registry does not list is not reported.

* **`xml:id`** — xml:id Version 1.0, W3C Recommendation 9 September 2005,
  §4. After attribute-value normalisation as for type ID (§3.3.3: leading
  and trailing spaces dropped, runs of spaces made one), the value is an
  NCName. The declared type of the attribute, if the DTD declares it, is
  `ID`. The values of all attributes of type ID in the document (xml:id
  attributes, and attributes the DTD declares as ID) are unique. An
  xml:id error is not fatal (§6); here it is an item in the result.

* **`xml:base`** — XML Base (Second Edition), W3C Recommendation 28 January
  2009, §3: "The value of this attribute is interpreted as a Legacy
  Extended IRI (LEIRI)", the W3C Note of 3 November 2008. The syntax of a
  LEIRI reference is that of an IRI reference (RFC 3987) with `ucschar`
  widened to almost every character, so the constraints that remain are
  structural: a `%` starts two hexadecimal digits, a scheme is an
  ALPHA followed by ALPHA, DIGIT, `+`, `-` or `.`, there is at most one
  `#`, and `[` and `]` stand only in the host of an authority.

## What the library already does with these attributes

`xml:base` is used where the library resolves references: the RDF/XML
parser resolves `rdf:about`, `rdf:resource`, `rdf:ID` and `rdf:datatype`
against the base in force on the element (`Syntax/RdfXml.lean`,
XML Base §4). `xml:lang` is read by the RDF/XML parser for language-tagged
literals. This module adds the reporting those readers lack.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.Namespaces

namespace L4Factoidal.XML

/-! ## Characters -/

private def isAlphaC (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
private def isDigitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'
private def isAlnumC (c : Char) : Bool := isAlphaC c || isDigitC c
private def allC (p : Char → Bool) (s : String) : Bool := s.toList.all p

/-! ## `xml:lang` — BCP 47, RFC 5646 §2.1 -/

/-- The irregular `grandfathered` tags of RFC 5646 §2.1, in lower case.
The regular ones (`art-lojban`, `cel-gaulish`, `no-bok`, `no-nyn`,
`zh-guoyu`, `zh-hakka`, `zh-min`, `zh-min-nan`, `zh-xiang`) match the
`langtag` production and need no entry. -/
def irregularLanguageTags : List String :=
  [ "en-gb-oed", "i-ami", "i-bnn", "i-default", "i-enochian", "i-hak",
    "i-klingon", "i-lux", "i-mingo", "i-navajo", "i-pwn", "i-tao",
    "i-tay", "i-tsu", "sgn-be-fr", "sgn-be-nl", "sgn-ch-de" ]

/-- `extlang = 3ALPHA *2("-" 3ALPHA)`: drop up to `n` extended-language
subtags. -/
def dropExtlangs : Nat → List String → List String
  | 0, ts => ts
  | _ + 1, [] => []
  | n + 1, t :: rest =>
      if t.length == 3 && allC isAlphaC t then dropExtlangs n rest else t :: rest

/-- `script = 4ALPHA`. -/
def dropScript : List String → List String
  | [] => []
  | t :: rest => if t.length == 4 && allC isAlphaC t then rest else t :: rest

/-- `region = 2ALPHA / 3DIGIT`. -/
def dropRegion : List String → List String
  | [] => []
  | t :: rest =>
      if (t.length == 2 && allC isAlphaC t) || (t.length == 3 && allC isDigitC t)
      then rest else t :: rest

/-- `variant = 5*8alphanum / (DIGIT 3alphanum)`. -/
def isVariantSubtag (t : String) : Bool :=
  (5 ≤ t.length && t.length ≤ 8 && allC isAlnumC t) ||
  (t.length == 4 && allC isAlnumC t && (match t.toList with | c :: _ => isDigitC c | [] => false))

def dropVariants : List String → List String
  | [] => []
  | t :: rest => if isVariantSubtag t then dropVariants rest else t :: rest

/-- The subtags of one extension: `1*("-" (2*8alphanum))`. Returns how many
were taken and the rest. -/
def dropExtensionSubtags : List String → Nat × List String
  | [] => (0, [])
  | t :: rest =>
      if 2 ≤ t.length && t.length ≤ 8 && allC isAlnumC t then
        let (n, r) := dropExtensionSubtags rest
        (n + 1, r)
      else (0, t :: rest)

/-- `*("-" extension)`, `extension = singleton 1*("-" (2*8alphanum))`,
`singleton` being a digit or a letter other than `x`. `none` when a
singleton has no subtag after it. -/
def dropExtensions : Nat → List String → Option (List String)
  | 0, ts => some ts
  | _ + 1, [] => some []
  | f + 1, t :: rest =>
      if t.length == 1 && allC isAlnumC t && t.toLower != "x" then
        let (n, r) := dropExtensionSubtags rest
        if n == 0 then none else dropExtensions f r
      else some (t :: rest)

/-- `privateuse = "x" 1*("-" (1*8alphanum))`, to the end of the tag. -/
def isPrivateUseSubtags : List String → Bool
  | [] => false
  | t :: rest =>
      t.toLower == "x" && !rest.isEmpty &&
      rest.all (fun u => 1 ≤ u.length && u.length ≤ 8 && allC isAlnumC u)

/-- `langtag = language ["-" script] ["-" region] *("-" variant)
*("-" extension) ["-" privateuse]` over the subtags of a tag, with
`language = 2*3ALPHA ["-" extlang] / 4ALPHA / 5*8ALPHA`. -/
def isLangtagSubtags : List String → Bool
  | [] => false
  | l :: rest =>
      if !(allC isAlphaC l && 2 ≤ l.length && l.length ≤ 8) then false
      else
        let r1 := if l.length ≤ 3 then dropExtlangs 3 rest else rest
        let r2 := dropVariants (dropRegion (dropScript r1))
        match dropExtensions (r2.length + 1) r2 with
        | none => false
        | some r3 => r3.isEmpty || isPrivateUseSubtags r3

/-- RFC 5646 §2.1 `Language-Tag`: a `langtag`, a `privateuse` tag or a
`grandfathered` tag. Tags are ASCII and compared without regard to case
(§2.1.1). The empty string is not a tag. -/
def isLanguageTag (s : String) : Bool :=
  let subtags := s.splitOn "-"
  irregularLanguageTags.contains s.toLower ||
  isLangtagSubtags subtags || isPrivateUseSubtags subtags

/-- The value of an `xml:lang` attribute: a language tag, or the empty
string (XML 1.0 §2.12). -/
def isXmlLangValue (s : String) : Bool := s.isEmpty || isLanguageTag s

/-! ## `xml:id` -/

/-- XML 1.0 §3.3.3 for an attribute of type ID: strip leading and trailing
#x20 and make each run of #x20 one. -/
def normalizeIdValue (v : String) : String := collapseSpaces v

/-- An NCName (Namespaces in XML 1.0 §3 `[4]`): a Name with no colon. XML 1.1
has the same name characters as the Fifth Edition of XML 1.0, so the one
test serves both. -/
def isNCName (v : String) : Bool := isName v && !(v.toList.contains ':')

/-! ## `xml:base` — a LEIRI reference -/

/-- Is every `%` followed by two hexadecimal digits (RFC 3987 `pct-encoded`)? -/
def pctEncodedOk : List Char → Bool
  | [] => true
  | '%' :: a :: b :: rest => isHexDigit a && isHexDigit b && pctEncodedOk rest
  | '%' :: _ => false
  | _ :: rest => pctEncodedOk rest

/-- RFC 3986 `scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )`. -/
def isUriScheme (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => isAlphaC c && rest.all (fun d => isAlnumC d || d == '+' || d == '-' || d == '.')

/-- A LEIRI reference (XML Base §3 and the LEIRI Note §3): the structural
rules that remain once `ucschar` takes in every character but a few
non-characters. The text of the reference has at most one `#`; a `%` starts
a `pct-encoded`; a colon in the first path segment ends a `scheme`; `[` and
`]` are the delimiters of an IP literal and stand in the authority only. -/
def isLeiriReference (s : String) : Bool :=
  let cs := s.toList
  let upToDelim := cs.takeWhile (fun c => c != '/' && c != '?' && c != '#')
  let schemeOk :=
    match upToDelim.findIdx? (· == ':') with
    | some i => isUriScheme (String.ofList (upToDelim.take i))
    | none => true
  let afterScheme :=
    match upToDelim.findIdx? (· == ':') with
    | some i => cs.drop (i + 1)
    | none => cs
  -- the authority: between `//` and the next `/`, `?` or `#`
  let authority :=
    match afterScheme with
    | '/' :: '/' :: rest => rest.takeWhile (fun c => c != '/' && c != '?' && c != '#')
    | _ => []
  let outsideAuthority :=
    match afterScheme with
    | '/' :: '/' :: rest => rest.dropWhile (fun c => c != '/' && c != '?' && c != '#')
    | other => other
  let bracketsOk :=
    !(outsideAuthority.contains '[') && !(outsideAuthority.contains ']') &&
    (authority.filter (· == '[')).length == (authority.filter (· == ']')).length
  let hashes := (cs.filter (· == '#')).length
  pctEncodedOk cs && schemeOk && hashes ≤ 1 && bracketsOk

/-! ## The check -/

/-- Which attribute of the XML namespace an item is about. -/
inductive XmlAttrKind where
  | lang
  | id
  | base
deriving DecidableEq, Repr, Inhabited

def XmlAttrKind.name : XmlAttrKind → String
  | .lang => "xml:lang"
  | .id => "xml:id"
  | .base => "xml:base"

/-- One finding: the attribute, the element it is on (or, for a declaration,
the element type the declaration is for), the value, and the rule it
breaks. -/
structure XmlAttrIssue where
  kind : XmlAttrKind
  element : String
  value : String
  message : String
deriving DecidableEq, Repr, Inhabited

/-- The local part of an attribute whose name has the prefix `xml`, i.e. an
attribute in the XML namespace. -/
def xmlNamespaceLocal? (name : String) : Option String :=
  match splitQName name with
  | .prefixed "xml" l => some l
  | _ => none

mutual

/-- Every (element name, attribute) pair under a node, in document order. -/
def Node.attributePairs : Node → List (String × Attribute)
  | .element tag attrs children =>
      attrs.map (fun a => (tag, a)) ++ Node.attributePairsList children
  | _ => []

def Node.attributePairsList : List Node → List (String × Attribute)
  | [] => []
  | n :: rest => Node.attributePairs n ++ Node.attributePairsList rest

end

/-- Every problem with an `xml:lang`, `xml:id` or `xml:base` attribute of
the document, in document order, then the declarations.

`parseXML` accepts the document whatever this returns. An empty result
means every one of the three attributes that occurs has a value its
specification allows. -/
def Document.xmlAttributeIssues (d : Document) : List XmlAttrIssue :=
  let pairs := d.root.attributePairs
  let dt? := d.doctype
  -- the values of every attribute of type ID: the xml:id attributes, and the
  -- attributes the DTD declares as ID (their values the parser normalised)
  let xmlIds := pairs.filterMap fun (_, a) =>
    if xmlNamespaceLocal? a.name == some "id" then some (normalizeIdValue a.value) else none
  let dtdIds := pairs.filterMap fun (tag, a) =>
    match dt? with
    | some dt =>
        match findAttDecl dt.attDecls tag a.name with
        | some decl => if decl.type == AttType.ID && a.name != "xml:id" then some a.value else none
        | none => none
    | none => none
  let allIds := xmlIds ++ dtdIds
  let perAttribute := pairs.flatMap fun (tag, a) =>
    match xmlNamespaceLocal? a.name with
    | some "lang" =>
        if isXmlLangValue a.value then []
        else [{ kind := .lang, element := tag, value := a.value,
                message := "not a language tag (XML 1.0 section 2.12: a BCP 47 tag, RFC 5646 section 2.1, or the empty string)" }]
    | some "id" =>
        let v := normalizeIdValue a.value
        (if isNCName v then []
         else [{ kind := .id, element := tag, value := a.value,
                 message := "the normalised value is not an NCName (xml:id section 4)" }]) ++
        (if (allIds.filter (· == v)).length ≤ 1 then []
         else [{ kind := .id, element := tag, value := a.value,
                 message := "the value is not unique among the attributes of type ID (xml:id section 4)" }])
    | some "base" =>
        if isLeiriReference a.value then []
        else [{ kind := .base, element := tag, value := a.value,
                message := "not a LEIRI reference (XML Base section 3)" }]
    | _ => []
  -- a DTD that declares xml:id declares it as ID (xml:id section 4)
  let declared :=
    match dt? with
    | some dt =>
        (dt.attDecls.reverse.filter (fun decl => decl.name == "xml:id" && decl.type != AttType.ID)).map
          fun decl => { kind := .id, element := decl.element, value := "",
                        message := "xml:id is declared with a type other than ID (xml:id section 4)" }
    | none => []
  perAttribute ++ declared

/-! ## Checks -/

private def issuesOf (src : String) : Option (List (XmlAttrKind × String)) :=
  match parseXML src with
  | .ok d => some (d.xmlAttributeIssues.map (fun i => (i.kind, i.element)))
  | .error _ => none

-- xml:lang. Well-formed tags, as RFC 5646 §2.1 writes them.
#guard ["en", "en-GB", "en-US", "de", "fr-CA", "zh-Hant", "zh-Hant-TW", "zh-cmn-Hans-CN",
        "sl-rozaj", "sl-rozaj-biske", "sl-nedis", "de-CH-1901", "es-419", "en-a-bbb-x-a-ccc",
        "x-private", "en-x-private", "az-Arab-x-AZE-derbend", "qaa-Qaaa-QM-x-southern",
        "ABC", "i-klingon", "I-KLINGON", "en-GB-oed", "sgn-BE-FR", "art-lojban", "zh-min-nan",
        "de-DE-u-co-phonebk", "hy-Latn-IT-arevela", "english-US", "en-t-jp-x-a"].all isLanguageTag
-- ...and the ones it does not.
#guard !["", "e", "-en", "en-", "en--US", "en_US", "en US", "toolongsubtag-x", "luna1234",
         "a-DE", "de-419-DE", "en-a", "en-a-x-priv", "en-x", "x", "x-", "en-US-US", "i-unknown",
         "en-Latn-Latn", "123", "en-12", "zh-Hant-TW-a", "sgn-BE-DE", "en-GB-oed-x"].any isLanguageTag
-- The empty string is an xml:lang value, but not a tag.
#guard isXmlLangValue "" && !isLanguageTag ""
#guard isXmlLangValue "en-GB" && !isXmlLangValue "en_GB"

-- xml:id: an NCName after normalisation.
#guard isNCName "a1" && isNCName "_x.y-z" && isNCName "é"
#guard !isNCName "" && !isNCName "1a" && !isNCName "a:b" && !isNCName "a b" && !isNCName "-a"
#guard normalizeIdValue "  a   " == "a"

-- xml:base: a LEIRI reference.
#guard ["http://example.org/a/b?q#f", "../x", "", "/a", "a/b:c", "http://[::1]:80/x", "x#", "?q",
        "urn:isbn:0451450523", "file:///a b/c d", "http://example.org/wine/rosé",
        "mailto:a@b.example", "%41", "a%20b", "http:", "//host/x", "a<b>c", "x|y"].all isLeiriReference
#guard !["%zz", "%4", "a%", "1http://x/", "ht tp://x/", ":x", "http://a/b#c#d", "/a[b]",
         "http://[::1/x", "http://::1]/x", "x:y#a[b]"].any isLeiriReference

-- The check, on documents. A document with good values has no issue.
#guard issuesOf "<a xml:lang=\"en\" xml:id=\"i\" xml:base=\"http://e/\"><b xml:lang=\"\"/></a>" == some []
#guard issuesOf "<a/>" == some []
-- xml:lang
#guard issuesOf "<a xml:lang=\"en_US\"/>" == some [(.lang, "a")]
#guard issuesOf "<a><b xml:lang=\"x\"/><c xml:lang=\"en-GB\"/></a>" == some [(.lang, "b")]
-- xml:id: not an NCName, and not unique.
#guard issuesOf "<a xml:id=\"1\"/>" == some [(.id, "a")]
#guard issuesOf "<a xml:id=\"p:q\"/>" == some [(.id, "a")]
#guard issuesOf "<a xml:id=\"\"/>" == some [(.id, "a")]
#guard issuesOf "<a xml:id=\"a b\"/>" == some [(.id, "a")]
#guard issuesOf "<a xml:id=\"  x  \"/>" == some []
#guard issuesOf "<a><b xml:id=\"x\"/><c xml:id=\"y\"/></a>" == some []
#guard issuesOf "<a><b xml:id=\"x\"/><c xml:id=\"x\"/></a>" == some [(.id, "b"), (.id, "c")]
#guard issuesOf "<a><b xml:id=\"x\"/><c xml:id=\" x \"/></a>" == some [(.id, "b"), (.id, "c")]
-- ...unique among all IDs, the ones a DTD declares as ID included.
#guard issuesOf "<!DOCTYPE a [<!ATTLIST b i ID #IMPLIED>]><a><b i=\"x\"/><c xml:id=\"x\"/></a>"
       == some [(.id, "c")]
#guard issuesOf "<!DOCTYPE a [<!ATTLIST b i ID #IMPLIED>]><a><b i=\"x\"/><c xml:id=\"y\"/></a>" == some []
-- ...and declared as ID, if declared.
#guard issuesOf "<!DOCTYPE a [<!ATTLIST a xml:id CDATA #IMPLIED>]><a/>" == some [(.id, "a")]
#guard issuesOf "<!DOCTYPE a [<!ATTLIST a xml:id ID #IMPLIED>]><a/>" == some []
#guard issuesOf "<!DOCTYPE a [<!ATTLIST a xml:id ID #IMPLIED>]><a xml:id=\"n\"/>" == some []
-- xml:base
#guard issuesOf "<a xml:base=\"http://e/a b\"/>" == some []
#guard issuesOf "<a xml:base=\"1x:y\"/>" == some [(.base, "a")]
#guard issuesOf "<a><b xml:base=\"%zz\"/></a>" == some [(.base, "b")]
-- Only the XML namespace's attributes are read: other prefixes and
-- other names are not.
#guard issuesOf "<a xmlns:q=\"urn:q\" q:lang=\"!!\" q:id=\"1\" q:base=\"%zz\" lang=\"!!\" id=\"1\"/>" == some []
#guard issuesOf "<a xml:space=\"preserve\"/>" == some []
-- Several at once, in document order.
#guard issuesOf "<a xml:lang=\"!\" xml:id=\"1\"><b xml:base=\"%\"/></a>"
       == some [(.lang, "a"), (.id, "a"), (.base, "b")]
-- A bad value never changes what the parser accepts.
#guard (parseXML "<a xml:lang=\"!\" xml:id=\"1\" xml:base=\"%\"/>").toOption.isSome

end L4Factoidal.XML
