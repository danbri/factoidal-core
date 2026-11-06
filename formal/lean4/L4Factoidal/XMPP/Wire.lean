import L4Factoidal.XML.Document
import L4Factoidal.XML.Parser

/-!
XMPP wire-format glue on top of `L4Factoidal.XML` — the real, W3C-XML-1.0-
conformant, F*-ported parser (`L4Factoidal/XML/Parser.lean`,
`Document.lean`). This module does NOT reimplement XML parsing: per Iron
Rule #7 ("no hand-written reimplementations of what the formal tree
defines"), a complete element (a stanza, `<stream:features>`, a SASL
payload wrapper, etc.) is parsed via `L4Factoidal.XML.parseXML` and its
`.root`.

Two things this module DOES add, because `L4Factoidal.XML` doesn't cover
them (it's a document-oriented — prolog+root+epilog — non-validating
parser, per its own module header) and XMPP genuinely needs them:

1. `render` — serialization. `L4Factoidal.XML` is parse-only (built for
   W3C conformance testing, not round-tripping), so there's nothing to
   reuse here; this is a new concern, not a duplicate.
2. `parseOpenTag` — an XMPP stream's `<stream:stream ...>` is never
   closed until the connection ends, so it can never be a complete
   `Node` the way `parseXML` expects. This is a narrow, stated gap: the
   right long-term fix is probably a small addition to `L4Factoidal.XML`
   itself (a generic "parse one start-tag, don't require a matching
   close" mode other streaming XML protocols could reuse too), not an
   XMPP-local parser. Filed as future work, not silently worked around.
-/

namespace L4Factoidal.XMPP.Wire

open L4Factoidal.XML (Node Attribute)

/-- Replace every occurrence of `old` in `s` with `new`. `old` must be
non-empty. -/
def replaceAll (s old new : String) : String :=
  if old.isEmpty then s else String.intercalate new (s.splitOn old)

def escapeText (s : String) : String :=
  let s := replaceAll s "&" "&amp;"
  let s := replaceAll s "<" "&lt;"
  let s := replaceAll s ">" "&gt;"
  s

def escapeAttr (s : String) : String :=
  let s := escapeText s
  replaceAll s "\"" "&quot;"

mutual

/-- Render a `Node` back to XML text. `comment`/`cdata`/`pi` nodes (which
`L4Factoidal.XML` can parse but XMPP stanzas never contain) render to
their literal XML forms too, for completeness. -/
def render : Node → String
  | .text s => escapeText s
  | .comment body => s!"<!--{body}-->"
  | .cdata content => s!"<![CDATA[{content}]]>"
  | .pi target data => s!"<?{target} {data}?>"
  | .element tag attrs children =>
    let attrStr := String.join (attrs.map (fun a => s! " {a.name}=\"{escapeAttr a.value}\""))
    match children with
    | [] => s!"<{tag}{attrStr}/>"
    | _ => s!"<{tag}{attrStr}>" ++ renderList children ++ s!"</{tag}>"

def renderList : List Node → String
  | [] => ""
  | n :: ns => render n ++ renderList ns

end

/-! ## Restricted XML (RFC 6120 section 11.1)

XMPP is a restricted subset of XML: a stanza must not hold a DTD, a comment
or a processing instruction. `L4Factoidal.XML` rightly accepts all three, as a
conformant parser must, so the restriction is here, where XMPP uses it. A DTD
is refused before the parser sees the text, because declaring entities is what
gives a short input a long parse; comments and processing instructions are
refused after, and so never reach a recipient. -/

/-- What follows the first `pat` in the characters, or nothing. -/
private def dropPast (pat : List Char) : List Char → List Char
  | [] => []
  | l@(_ :: rest) => if pat.isPrefixOf l then l.drop pat.length else dropPast pat rest

/-- Does this prolog hold a `<!DOCTYPE`? A `[28] doctypedecl` can stand only
before the root element, so reading stops at the first thing that is not
whitespace, a comment or a processing instruction. `fuel` is the length: each
step consumes at least one character. -/
def prologHasDoctype : Nat → List Char → Bool
  | 0, _ => false
  | _ + 1, [] => false
  | n + 1, l@(c :: rest) =>
    if c == ' ' || c == '\t' || c == '\n' || c == '\r' then prologHasDoctype n rest
    else if "<!DOCTYPE".toList.isPrefixOf l then true
    else if "<!--".toList.isPrefixOf l then prologHasDoctype n (dropPast "-->".toList rest)
    else if "<?".toList.isPrefixOf l then prologHasDoctype n (dropPast "?>".toList rest)
    else false

/-- Is there a comment or a processing instruction in these nodes, at any
depth? A worklist, because stanzas come from the network: stack use must not
grow with their depth. `fuel` must exceed the number of nodes; running out
counts as yes, so a mistake refuses a stanza rather than passes one. -/
def holdsRestricted : Nat → List Node → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | _ + 1, .comment _ :: _ => true
  | _ + 1, .pi _ _ :: _ => true
  | n + 1, .element _ _ children :: rest => holdsRestricted n (children ++ rest)
  | n + 1, _ :: rest => holdsRestricted n rest

/-! ## The shape of a stanza

The XML parser and `render` use stack with the depth of a document, and memory
with its number of elements, and a stanza comes from the network. So its shape is
read first, in one tail-recursive pass over the characters, and a stanza over a
limit is refused, as if it did not parse. -/

/-- How deep elements may nest in a stanza. -/
def maxDepth : Nat := 64

/-- How many elements a stanza may hold, at all depths. -/
def maxElements : Nat := 8192

/-- What follows a tag whose name has begun, and whether it ended `/>`. A `>` or a
`/` in a quoted value does not count. `fuel` is at least the length. -/
def tagEnd : Nat → Option Char → Bool → List Char → List Char × Bool
  | 0, _, _, _ => ([], false)
  | _ + 1, _, _, [] => ([], false)
  | n + 1, some q, _, c :: rest =>
    if c == q then tagEnd n none false rest else tagEnd n (some q) false rest
  | n + 1, none, slash, c :: rest =>
    if c == '"' || c == '\'' then tagEnd n (some c) false rest
    else if c == '>' then (rest, slash)
    else tagEnd n none (c == '/') rest

/-- Do these characters stay inside `maxDepth` and `maxElements`? `fuel` is at
least the length, as each step consumes a character; running out counts as no, so
a mistake refuses a stanza rather than passes one. A `<` in a comment, a CDATA
section or a processing instruction opens nothing. -/
def shapeOk : Nat → Nat → Nat → List Char → Bool
  | 0, _, _, _ => false
  | _ + 1, _, _, [] => true
  | n + 1, depth, count, l@(c :: rest) =>
    if c != '<' then shapeOk n depth count rest
    else if "<!--".toList.isPrefixOf l then shapeOk n depth count (dropPast "-->".toList rest)
    else if "<![CDATA[".toList.isPrefixOf l then shapeOk n depth count (dropPast "]]>".toList rest)
    else if "<?".toList.isPrefixOf l then shapeOk n depth count (dropPast "?>".toList rest)
    else if "</".toList.isPrefixOf l then shapeOk n (depth - 1) count (dropPast ">".toList rest)
    else if depth ≥ maxDepth || count ≥ maxElements then false
    else
      let (after, selfClosing) := tagEnd n none false rest
      shapeOk n (if selfClosing then depth else depth + 1) (count + 1) after

/-- Parse a complete element (a stanza, `<stream:features>`, ...) via the
real XML parser. `L4Factoidal.XML.parseXML` accepts a document with no
XML declaration, so a bare `<message>...</message>` string parses fine —
its `.root` is exactly the element. What RFC 6120 section 11.1 forbids is
refused, as if it did not parse. -/
def parseElement (s : String) : Option Node :=
  if prologHasDoctype s.length s.toList then none
  else if !shapeOk (s.length + 1) 0 0 s.toList then none
  else match L4Factoidal.XML.parseXML s with
    | .ok doc => if holdsRestricted (s.length + 1) [doc.root] then none else some doc.root
    | .error _ => none

/-- A stanza over the shape limits is refused before the parser sees it. -/
theorem parseElement_shape (s : String) (h : shapeOk (s.length + 1) 0 0 s.toList = false) :
    parseElement s = none := by
  simp [parseElement, h]

private def nested (n : Nat) : String :=
  String.join (List.replicate n "<a>") ++ String.join (List.replicate n "</a>")

-- At the limit a stanza passes; one deeper does not, closed or not, and a
-- self-closing element at the bottom counts as a level.
#guard (parseElement (nested maxDepth)).isSome
#guard (parseElement (nested (maxDepth + 1))).isNone
#guard (parseElement (String.join (List.replicate 5000 "<a>"))).isNone
#guard (parseElement (String.join (List.replicate maxDepth "<a>") ++ "<b/>" ++ String.join (List.replicate maxDepth "</a>"))).isNone
-- Siblings do not add depth; their number is limited.
#guard (parseElement ("<m>" ++ String.join (List.replicate 100 "<a/><b></b>") ++ "</m>")).isSome
#guard (parseElement ("<m>" ++ String.join (List.replicate maxElements "<a/>") ++ "</m>")).isNone
#guard (parseElement ("<m>" ++ String.join (List.replicate (maxElements - 1) "<a/>") ++ "</m>")).isSome
-- A `<` that opens nothing does not count, and a `>` or `/>` in a value ends no tag.
#guard (parseElement ("<m><![CDATA[" ++ String.join (List.replicate 100 "<a>") ++ "]]></m>")).isSome
#guard (parseElement ("<m a=\"x>y\" b='/>'><c/></m>")).isSome
#guard shapeOk 100 0 0 "<m a='>'><c/></m>".toList

-- ## The one thing `L4Factoidal.XML` doesn't cover: an unclosed root.
-- Minimal fuel-bounded helpers, narrowly scoped to "one opening tag,"
-- not a competing element/document parser.

private def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r'

private def isNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '-' || c == '_' || c == '.' || c == ':'

private def dropSpaces : List Char → List Char
  | [] => []
  | c :: cs => if isSpace c then dropSpaces cs else c :: cs

private def spanNameGo (acc : List Char) : List Char → (List Char × List Char)
  | [] => (acc.reverse, [])
  | c :: rest => if isNameChar c then spanNameGo (c :: acc) rest else (acc.reverse, c :: rest)

private def spanName (cs : List Char) : (String × List Char) :=
  let (nameChars, rest) := spanNameGo [] cs
  (String.ofList nameChars, rest)

private def spanUntilGo (acc : List Char) (delim : Char) : List Char → (List Char × List Char)
  | [] => (acc.reverse, [])
  | c :: rest => if c == delim then (acc.reverse, c :: rest) else spanUntilGo (c :: acc) delim rest

private def spanUntil (delim : Char) (cs : List Char) : (String × List Char) :=
  let (chars, rest) := spanUntilGo [] delim cs
  (String.ofList chars, rest)

/-- Decode the five predefined entities in an attribute value. `&amp;`
decoded last, so `&amp;lt;` (the four characters `&lt;`) doesn't
double-decode into `<`. Real entity handling (numeric refs, custom
entities) belongs to `L4Factoidal.XML`; opening tags only ever carry the
five predefined ones in practice. -/
private def unescapeAttr (s : String) : String :=
  let s := replaceAll s "&lt;" "<"
  let s := replaceAll s "&gt;" ">"
  let s := replaceAll s "&apos;" "'"
  let s := replaceAll s "&quot;" "\""
  replaceAll s "&amp;" "&"

private def parseAttrs (fuel : Nat) (acc : List Attribute) (cs : List Char) :
    Option (List Attribute × List Char) :=
  match fuel with
  | 0 => none
  | fuel + 1 =>
    let cs := dropSpaces cs
    match cs with
    | [] => none
    | '>' :: _ => some (acc.reverse, cs)
    | '/' :: _ => some (acc.reverse, cs)
    | c :: _ =>
      if !isNameChar c then none else
      let (name, rest) := spanName cs
      let rest := dropSpaces rest
      match rest with
      | '=' :: rest =>
        let rest := dropSpaces rest
        match rest with
        | q :: rest =>
          if q == '"' || q == '\'' then
            let (rawValue, rest) := spanUntil q rest
            match rest with
            | _ :: rest => parseAttrs fuel (⟨name, unescapeAttr rawValue⟩ :: acc) rest
            | [] => none
          else none
        | [] => none
      | _ => none

/-- Skip an optional leading XML declaration (`<?xml ... ?>`) — real
servers (confirmed against a live ejabberd instance, 2026-09-07) send one
before `<stream:stream>`, and a naive `parseOpenTag` that doesn't expect
it fails on every real-world capture despite passing on hand-written test
strings that omitted it. Skips at most one `<? ... ?>`, XML-declaration or
not; doesn't validate its contents (that's `L4Factoidal.XML`'s job for a
document that has one as part of a full parse). -/
private def skipXmlDecl (cs : List Char) : List Char :=
  match dropSpaces cs with
  | '<' :: '?' :: rest =>
    let (_, rest) := spanUntilGo [] '>' rest
    match rest with
    | _ :: rest => rest  -- consume the '>'
    | [] => []
  | cs => cs

/-- Parse just an element's OPENING tag (name + attributes), stopping
right after `>` or `/>` — does not require or consume a matching close
tag. Returns the tag name, its attributes, whether it was self-closing,
and the unconsumed remainder. Tolerates one leading `<?xml ... ?>`. -/
def parseOpenTag (s : String) : Option (String × List Attribute × Bool × String) :=
  match dropSpaces (skipXmlDecl s.toList) with
  | '<' :: rest =>
    let rest := dropSpaces rest
    match rest with
    | [] => none
    | c :: _ =>
      if !isNameChar c then none else
      let (tag, rest) := spanName rest
      match parseAttrs (2 * rest.length + 4) [] rest with
      | none => none
      | some (attrs, rest) =>
        match dropSpaces rest with
        | '/' :: '>' :: rest' => some (tag, attrs, true, String.ofList rest')
        | '>' :: rest' => some (tag, attrs, false, String.ofList rest')
        | _ => none
  | _ => none

end L4Factoidal.XMPP.Wire
