/-
L4Factoidal.XPath4.Html — `fn:parse-html` and `fn:html-doc` (F&O 4.0 §17.3).

The parser is `L4Factoidal.HTML` (WHATWG HTML Living Standard §13.2: the
tokenizer in `HTML/Tokenizer.lean`, tree construction in
`HTML/TreeBuilder.lean`; the module headers list what is implemented). This
file does the XDM mapping of §17.3.1 and the function wrappers:

* the HTML DOM is converted to an `L4Factoidal.XML.Node` tree and built into
  a runtime document (`Doc.ofNodes`), as `fn:parse-xml` does;
* elements are in the namespace of their DOM element: XHTML
  (`http://www.w3.org/1999/xhtml`), SVG or MathML, declared with `xmlns`
  attributes where the namespace changes; `xlink:` attributes get their
  `xmlns:xlink` declaration; `xml:` attributes use the `xml` prefix;
  namespace declarations in the HTML source are dropped (§17.3.1.1);
* the doctype is not a node of the result; comments are kept; adjacent text
  nodes are merged; the content of `template` is the content of the element;
* a name that is not a QName (an element or attribute name with a colon, such
  as `a:tag`, or an attribute `foo:bar` with an unbound prefix) is written
  with `_` in place of the colon, and is reported as a parse error, so that
  `fail-on-error` rejects it (the DOM name cannot be represented in XDM).

Options: `encoding` (xs:string) and `fail-on-error` (xs:boolean, default
false); any other key that is not a QName in a namespace is `XPTY0004`
(the option parameter conventions). `fail-on-error` raises `FODC0011` for
the first parse error, including a missing DOCTYPE. An encoding that is not
supported, or octets that cannot be decoded as the given encoding, is
`FODC0011`.

Encodings: UTF-8 (invalid octets become U+FFFD, as the WHATWG decoder does),
UTF-16LE and UTF-16BE, windows-1252 (with its aliases `latin1`,
`iso-8859-1`, `ascii`, `us-ascii`, which the Encoding Standard maps to
windows-1252) and windows-1251. A byte order mark wins over the `encoding`
option (§13.2.3.2 step 1). Without an option and without a byte order mark a
simplified prescan finds `<meta charset=...>` in the first 1024 octets;
otherwise UTF-8. The other encodings of the Encoding Standard are not
implemented.

`fn:html-doc` reads the octets of the resource that the caller supplied in
advance (`Env.resourceBytes`, or the text of `Env.resources`) and parses them;
a missing resource is `FOUT1170`.
-/
import L4Factoidal.XPath4.XmlParse
import L4Factoidal.HTML.TreeBuilder
import L4Factoidal.HTML.Tests

namespace L4Factoidal.XPath4

open L4Factoidal.XML

def nsXhtml : String := "http://www.w3.org/1999/xhtml"
def nsSvg : String := "http://www.w3.org/2000/svg"
def nsMathMl : String := "http://www.w3.org/1998/Math/MathML"

def htmlNsUri : HTML.NS → String
  | .html => nsXhtml
  | .svg => nsSvg
  | .math => nsMathMl

/-! ## Decoding -/

def windows1251High : List Nat :=
  [0x402, 0x403, 0x201A, 0x453, 0x201E, 0x2026, 0x2020, 0x2021, 0x20AC, 0x2030, 0x409, 0x2039, 0x40A, 0x40C,
   0x40B, 0x40F, 0x452, 0x2018, 0x2019, 0x201C, 0x201D, 0x2022, 0x2013, 0x2014, 0x98, 0x2122, 0x459, 0x203A,
   0x45A, 0x45C, 0x45B, 0x45F, 0xA0, 0x40E, 0x45E, 0x408, 0xA4, 0x490, 0xA6, 0xA7, 0x401, 0xA9, 0x404, 0xAB,
   0xAC, 0xAD, 0xAE, 0x407, 0xB0, 0xB1, 0x406, 0x456, 0x491, 0xB5, 0xB6, 0xB7, 0x451, 0x2116, 0x454, 0xBB,
   0x458, 0x405, 0x455, 0x457]

def decode1251 (bs : ByteArray) : String :=
  String.ofList (bs.toList.map fun b =>
    let n := b.toNat
    if n < 0x80 then Char.ofNat n
    else if n < 0xC0 then Char.ofNat (windows1251High.getD (n - 0x80) n)
    else Char.ofNat (0x410 + (n - 0xC0)))

def decode1252 (bs : ByteArray) : String :=
  String.ofList (bs.toList.map fun b =>
    let n := b.toNat
    if 0x80 ≤ n && n ≤ 0x9F then Char.ofNat (HTML.c1Table.getD (n - 0x80) n) else Char.ofNat n)

/-- The canonical name of an encoding label, if it is supported. -/
def htmlEncodingName (label : String) : Option String :=
  match (HTML.lowerStr label.trimAscii.toString) with
  | "utf-8" | "utf8" | "unicode-1-1-utf-8" => some "utf-8"
  | "utf-16le" | "utf-16" | "ucs-2" => some "utf-16le"
  | "utf-16be" => some "utf-16be"
  | "windows-1252" | "cp1252" | "latin1" | "iso-8859-1" | "iso8859-1" | "l1" | "ascii" | "us-ascii" => some "windows-1252"
  | "windows-1251" | "cp1251" => some "windows-1251"
  | _ => none

/-- The simplified prescan of §13.2.3.2: a `charset` in a `meta` element in the first 1024 octets. -/
def prescanCharset (bs : ByteArray) : Option String :=
  let head := String.ofList ((bs.extract 0 (min 1024 bs.size)).toList.map (fun b => HTML.lowerAscii (Char.ofNat b.toNat)))
  match head.splitOn "<meta" with
  | _ :: m :: _ =>
    match m.splitOn "charset" with
    | _ :: rest :: _ =>
      let r := (rest.dropWhile (fun c => HTML.isWs c)).toString
      if r.startsWith "=" then
        let r := ((r.drop 1).dropWhile (fun c => HTML.isWs c)).toString
        let r := if r.startsWith "\"" || r.startsWith "'" then (r.drop 1).toString else r
        let v := r.takeWhile (fun c => HTML.isAsciiAlnum c || c == '-' || c == '_' || c == ':' || c == '.')
        if v.isEmpty then none else some v.toString
      else none
    | _ => none
  | _ => none

def decodeHtmlBytes (bs : ByteArray) (enc : Option String) : M String := do
  let b (i : Nat) : Nat := if i < bs.size then (bs.get! i).toNat else 256
  let bad {α} (what : String) : M α := err "FODC0011" ("the HTML cannot be decoded: " ++ what)
  let (name, off) ← do
    if b 0 == 0xEF && b 1 == 0xBB && b 2 == 0xBF then pure ("utf-8", 3)
    else if b 0 == 0xFF && b 1 == 0xFE then pure ("utf-16le", 2)
    else if b 0 == 0xFE && b 1 == 0xFF then pure ("utf-16be", 2)
    else match enc with
      | some l => match htmlEncodingName l with
        | some n => pure (n, 0)
        | none => bad ("unsupported encoding " ++ l)
      | none =>
        match (prescanCharset bs).bind htmlEncodingName with
        | some n => pure (n, 0)
        | none => pure ("utf-8", 0)
  let body := bs.extract off bs.size
  match name with
  | "utf-8" => pure (utf8Lossy body)
  | "utf-16le" => match decodeUtf16 bs off false with | some t => pure t | none => bad "invalid UTF-16"
  | "utf-16be" => match decodeUtf16 bs off true with | some t => pure t | none => bad "invalid UTF-16"
  | "windows-1251" => pure (decode1251 body)
  | _ => pure (decode1252 body)

/-! ## DOM to XML nodes -/

def isXlinkName (n : String) : Bool := n.startsWith "xlink:" && n.length > 6
def isXmlName (n : String) : Bool := n.startsWith "xml:" && n.length > 4

def attrNodes (attrs : List (String × String)) : List Attribute × Bool :=
  let kept := attrs.filter (fun a => a.1 != "xmlns" && !a.1.startsWith "xmlns:")
  let mapped := kept.map fun a =>
    let nm := if isXlinkName a.1 || isXmlName a.1 then a.1 else (a.1.replace ":" "_")
    ({ name := nm, value := a.2 } : Attribute)
  (mapped, kept.any (fun a => isXlinkName a.1))

def toXml : Nat → Option HTML.NS → HTML.HNode → Node
  | 0, _, _ => .text ""
  | f + 1, parent, n =>
    match n with
    | .text s => .text s
    | .comment s => .comment s
    | .element ns name attrs kids =>
      let (ats, xl) := attrNodes attrs
      let decl : List Attribute :=
        (if parent == some ns then [] else [{ name := "xmlns", value := htmlNsUri ns }])
        ++ (if xl then [{ name := "xmlns:xlink", value := "http://www.w3.org/1999/xlink" }] else [])
      .element (name.replace ":" "_") (decl ++ ats) (kids.map (toXml f (some ns)))

/-- Names that XDM cannot represent: reported as parse errors. -/
def nameErrors : Nat → HTML.HNode → List String
  | 0, _ => []
  | f + 1, n =>
    match n with
    | .element _ name attrs kids =>
      (if name.contains ':' then ["element name is not a QName: " ++ name] else [])
      ++ (attrs.filterMap fun a =>
          if a.1.contains ':' && !isXlinkName a.1 && !isXmlName a.1 && !a.1.startsWith "xmlns" then
            some ("attribute name is not a QName: " ++ a.1) else none)
      ++ kids.flatMap (nameErrors f)
    | _ => []

/-! ## The functions -/

def htmlOptionNames : List String := ["encoding", "fail-on-error"]

/-- Parse `src` (a string, or octets with the options' encoding) into a document. -/
def parseHtmlSource (e : Env) (opts : Seq) (src : Sum String ByteArray) (base tag : String) : M Seq := do
  checkOptionKeys opts htmlOptionNames
  let enc ← match optLookup opts "encoding" with
    | none | some [] => pure none
    | some v => match ← e.coerce (parseTy "xs:string") v "encoding" with
      | [.atom x] => pure (some x.str)
      | _ => err "XPTY0004" "encoding must be xs:string"
  let failOnError ← optBool opts "fail-on-error" false
  let text ← match src with
    | .inl s => pure (if s.startsWith "﻿" then (s.drop 1).toString else s)
    | .inr bs => decodeHtmlBytes bs enc
  let r := HTML.parseHtml text
  let errs := r.errors.toList ++ r.children.flatMap (nameErrors 100000)
  if failOnError then
    match errs with
    | x :: _ => err "FODC0011" ("not a well-formed HTML document: " ++ x)
    | [] => pure ()
  let kids := r.children.map (toXml 100000 none)
  let doc := { Doc.ofNodes kids with baseUri := base }
  pure [doc.rootItem (runtimeDocId tag text)]

def parseHtmlFn : LibFn := fun _ e a => do
  match optAtom (argN a 0) with
  | none => pure []
  | some v =>
    match bytesOfAtomic v with
    | some bs => parseHtmlSource e (argN a 1) (.inr bs) e.baseUri "parse-html"
    | none => parseHtmlSource e (argN a 1) (.inl v.str) e.baseUri "parse-html"

def htmlDocFn : LibFn := fun _ e a => do
  match optAtom (argN a 0) with
  | none => pure []
  | some u =>
    if (u.str.splitOn "#").length > 1 then err "FOUT1170" "a fragment identifier is not allowed"
    let bs ← match e.resourceBin u.str with
      | some bs => pure bs
      | none =>
        match e.resource u.str with
        | some t => pure t.toUTF8
        | none => err "FOUT1170" ("resource not available: " ++ u.str)
    parseHtmlSource e (argN a 1) (.inr bs) (resolveUri e.baseUri u.str) ("html-doc" ++ u.str)

def htmlTable : List (String × LibFn) := [
  ent "parse-html" parseHtmlFn,
  ent "html-doc" htmlDocFn
]

end L4Factoidal.XPath4
