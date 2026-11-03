/-
L4Factoidal.XPath4.XInclude — XML Inclusions (XInclude) 1.1 for the
`xinclude` option of `fn:doc` and `fn:parse-xml` (F&O 4.0 §14.6.1).

https://www.w3.org/TR/xinclude-11/ . An `xi:include` element (namespace
`http://www.w3.org/2001/XInclude`) is replaced by the resource its `href`
names, resolved against the base URI of the including document:

* `parse="xml"` (the default): the document element of the parsed
  resource, after its own inclusions, with base URI fixup (an `xml:base`
  attribute, §4.7.5) and, when the including element has a default
  namespace, `xmlns=""` so that the included names keep their namespace;
* `parse="text"`: a text node with the resource text.

A resource that cannot be read (or an `xpointer`, which `expand` does
not evaluate: https://github.com/danbri/factoidal/issues/1220; `expandX`
below does) is a resource error: the children of the
`xi:fallback` child are used, and without a fallback the error stays.
Including a resource that is already being included (a loop) is a fatal
error. The nesting is bounded by `fuel`.

The functions are pure: the caller gives the resource lookup (`fetch`)
and the XML parser (`parseRoot`).
-/
import L4Factoidal.XML.Document
import L4Factoidal.XML.Parser
import L4Factoidal.XML.Encoding
import L4Factoidal.XML.XPointer

namespace L4Factoidal.XPath4.XInclude

open L4Factoidal.XML

def xiNs : String := "http://www.w3.org/2001/XInclude"

inductive XiErr where
  /-- A resource error (XInclude 1.1 §4.4): the fallback applies. -/
  | resource (msg : String)
  /-- A fatal error. -/
  | fatal (msg : String)

def XiErr.msg : XiErr → String
  | .resource m => m
  | .fatal m => m

/-- The namespace bindings an element adds to the scope (newest first). -/
def scopeOf (sc : List (String × String)) (attrs : List Attribute) : List (String × String) :=
  attrs.foldl (fun sc a =>
    if a.name == "xmlns" then ("", a.value) :: sc
    else if a.name.startsWith "xmlns:" then ((a.name.drop 6).toString, a.value) :: sc
    else sc) sc

/-- The namespace URI and local name of an element name in a scope. -/
def nameOf (sc : List (String × String)) (tag : String) : String × String :=
  match tag.splitOn ":" with
  | [p, l] => ((sc.lookup p).getD "", l)
  | _ => ((sc.lookup "").getD "", tag)

def attrOf (attrs : List Attribute) (n : String) : Option String :=
  (attrs.find? (·.name == n)).map (·.value)

/-- A reference against the URI of the resource that holds it (its
    directory). -/
def resolveAgainst (base h : String) : String :=
  if base == "" || (h.splitOn "://").length > 1 || h.startsWith "/" then h
  else match (base.splitOn "/").dropLast with
    | [] => h
    | dirs => String.intercalate "/" dirs ++ "/" ++ h

/-- Base URI fixup and namespace fixup of an included element. -/
def fixup (href : String) (sc : List (String × String)) : Node → Node
  | .element tag attrs kids =>
    let attrs := if (attrOf attrs "xml:base").isSome then attrs
      else attrs ++ [{ name := "xml:base", value := href }]
    let attrs := if (sc.lookup "").getD "" != "" && (attrOf attrs "xmlns").isNone
      then attrs ++ [{ name := "xmlns", value := "" }] else attrs
    .element tag attrs kids
  | n => n

/-- Process the inclusions of a node: the nodes that replace it. `chain`
    holds the resources being included (for loop detection), `base` is the
    URI of the resource that holds the node, `sc` its namespace scope. -/
def expand (fetch : String → Option String) (parseRoot : String → Except String Node) :
    Nat → List String → String → List (String × String) → Node → Except XiErr (List Node)
  | 0, _, _, _, _ => .error (.fatal "XInclude nesting too deep")
  | f + 1, chain, base, sc, n =>
    match n with
    | .element tag attrs kids =>
      let sc := scopeOf sc attrs
      let (u, l) := nameOf sc tag
      if u == xiNs && l == "include" then
        let href := (attrOf attrs "href").getD ""
        let parse := (attrOf attrs "parse").getD "xml"
        let target := resolveAgainst base href
        let got : Except XiErr (List Node) :=
          if parse != "xml" && parse != "text" then .error (.fatal ("parse=\"" ++ parse ++ "\""))
          else if (attrOf attrs "xpointer").isSome then .error (.resource "xpointer is not evaluated")
          else if href == "" then .error (.fatal "an include without href")
          else if parse == "xml" && chain.contains target then .error (.fatal ("inclusion loop: " ++ target))
          else match fetch target with
            | none => .error (.resource ("cannot read " ++ target))
            | some t =>
              if parse == "text" then .ok [.text t]
              else match parseRoot t with
                | .error m => .error (.fatal (target ++ ": " ++ m))
                | .ok root => (expand fetch parseRoot f (target :: chain) target [] root).map
                    (·.map (fixup href sc))
        match got with
        | .error (.resource m) =>
          let fb := kids.find? (fun k => match k with
            | .element t _ _ => nameOf sc t == (xiNs, "fallback")
            | _ => false)
          match fb with
          | some (.element _ _ fkids) => do
            let parts ← fkids.mapM (expand fetch parseRoot f chain base sc)
            pure parts.flatten
          | _ => .error (.resource m)
        | r => r
      else if u == xiNs && l == "fallback" then
        .error (.fatal "xi:fallback is not a child of xi:include")
      else do
        let parts ← kids.mapM (expand fetch parseRoot f chain base sc)
        pure [.element tag attrs parts.flatten]
    | other => .ok [other]


/-! ## XInclude with XPointer

`expandX` is the processor of XML Inclusions (XInclude) 1.0 Second Edition
(W3C Recommendation 15 November 2006) and XInclude 1.1 (W3C Working Group
Note 2013), with the `xpointer` attribute evaluated by the XPointer
Framework (`L4Factoidal.XML.XPointer`). `expand` above stays the
processor of the `xinclude` option of `fn:doc`, which gives no pointer
evaluator: there an `xpointer` attribute is a resource error.

What `expandX` adds to `expand`:

* the `xpointer` attribute, evaluated on the acquired infoset of the
  resource (after its own inclusions); with no `href` (or an empty one)
  on the document that holds the `xi:include` (an intra-document
  reference);
* a pointer that identifies an attribute or a namespace node, or that is
  not a `Pointer` of the Framework, is a fatal error; a pointer that
  identifies no subresource is a resource error;
* an included element keeps the namespace bindings that its ancestors in
  the resource declare (namespace fixup);
* the loop rule of XInclude 1.1: a fatal error when the same resource and
  `xpointer` value are already in the inclusion chain; an intra-document
  reference to the `xi:include` element itself or to an element that
  contains it is a fatal error;
* the fatal errors on the `xi:include` element: an `href` with a fragment
  identifier; `parse="text"` with `xpointer`; no `href` and no
  `xpointer`; `accept` or `accept-language` with a character outside
  `#x20`-`#x7E`; more than one `xi:fallback` child; an `xi:include` child;
* `parse="text"` decoded by the `encoding` attribute (UTF-8 when there is
  none; a byte order mark decides UTF-16).

The caller gives the resource bytes (`Cfg.fetch`), the XML parser
(`Cfg.parseDoc`, with the URI so that a DTD can be read relative to it)
and the pointer evaluator (`Cfg.pointer`, which can add the xpointer()
scheme of the XPath engine).
-/

/-- What the processor needs from its caller. -/
structure Cfg where
  /-- The bytes of the resource at a URI. -/
  fetch : String → Option ByteArray
  /-- Parse the bytes of the resource at a URI. -/
  parseDoc : String → ByteArray → Except String Document
  /-- Resolve a pointer against a document. -/
  pointer : Option (Document → String → XPointer.Outcome) := none

/-- The text of a `parse="text"` resource: the `encoding` attribute when
it is there; else a byte order mark, or the first characters `<?` in
UTF-16 (XML 1.0 Appendix F.1); else UTF-8. A byte order mark is not part
of the text, except under a label that names the byte order (`UTF-16LE`,
`UTF-16BE`), where U+FEFF is a character. -/
def decodeText (enc : Option String) (bs : ByteArray) : Except String String :=
  let bomUtf16 : Option Endian :=
    if startsWithBytes bs [0xFE, 0xFF] then some .big
    else if startsWithBytes bs [0xFF, 0xFE] then some .little else none
  let utf8 (bs : ByteArray) : Except String String :=
    let skip := if startsWithBytes bs [0xEF, 0xBB, 0xBF] then 3 else 0
    (decodeUtf8 (bs.extract skip bs.size)).mapError (·.message)
  match enc with
  | none =>
    match detectFamily bs with
    | .utf16Bom o => (decodeUtf16 bs o 2).mapError (·.message)
    | .utf16Bare o => (decodeUtf16 bs o 0).mapError (·.message)
    | .ucs4 n => .error ("the text is in " ++ n ++ ", which is not supported")
    | .ebcdic => .error "the text is in EBCDIC, which is not supported"
    | _ => utf8 bs
  | some e =>
    if isUtf8Label e then utf8 bs
    else if isLatin1Label e then .ok (decodeLatin1 bs)
    else if isAsciiLabel e then (decodeAscii bs).mapError (·.message)
    else if isUtf16Label e then
      match bomUtf16 with
      | some o => (decodeUtf16 bs o 2).mapError (·.message)
      | none => (decodeUtf16 bs .big 0).mapError (·.message)
    else match utf16OrderLabel e with
      | some o => (decodeUtf16 bs o 0).mapError (·.message)
      | none => .error ("the encoding " ++ e ++ " is not supported")

/-- The prefix of an element or attribute name (`""` when it has none). -/
def prefixOf (n : String) : String :=
  match n.splitOn ":" with
  | [p, _] => p
  | _ => ""

/-- The prefixes that the names of an element and its descendants use
(element names, and attribute names other than namespace declarations
and `xml:`). `work` holds the nodes still to visit; a tail call per node. -/
def usedPrefixes : Nat → List Node → List String → List String
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | f + 1, n :: work, acc =>
    match n with
    | .element t as ks =>
      let ps := prefixOf t :: as.filterMap (fun a =>
        let p := prefixOf a.name
        if p == "" || p == "xmlns" || p == "xml" || a.name == "xmlns" then none else some p)
      usedPrefixes f (ks ++ work) (ps.foldl (fun acc p => if acc.contains p then acc else p :: acc) acc)
    | _ => usedPrefixes f work acc

/-- Namespace fixup of an included element: the bindings of its ancestors
in the resource (`inscope`, newest first) for the prefixes that the
element or its descendants use and that the element does not declare
itself, as attributes. -/
def nsFixupAttrs (inscope : List (String × String)) (n : Node) : List Attribute :=
  match n with
  | .element _ attrs _ =>
    let declared := attrs.filterMap (fun a =>
      if a.name == "xmlns" then some ""
      else if a.name.startsWith "xmlns:" then some (a.name.drop 6).toString else none)
    let used := usedPrefixes 1000000 [n] []
    let (out, _) := inscope.foldl (fun (acc : List (String × String) × List String) (b : String × String) =>
      if acc.2.contains b.1 || !used.contains b.1 then acc else (b :: acc.1, b.1 :: acc.2)) ([], declared)
    out.reverse.map (fun (p, u) =>
      if p == "" then { name := "xmlns", value := u } else { name := "xmlns:" ++ p, value := u })
  | _ => []

/-- The ancestors (outermost first) of the first node, in document order,
of the tree `root` that is equal to `x`. `work` holds the nodes still to
visit with their ancestors in reverse; a tail call per node. -/
def ancestorsOf (x : Node) : Nat → List (Node × List Node) → Option (List Node)
  | 0, _ => none
  | _ + 1, [] => none
  | f + 1, (n, anc) :: work =>
    if n == x then some anc.reverse
    else match n with
      | .element _ _ kids => ancestorsOf x f (kids.map (fun k => (k, n :: anc)) ++ work)
      | _ => ancestorsOf x f work

def searchDepth : Nat := 2 ^ 40

/-- The ancestors of `x` in the tree `root` (none when `x` is not in it). -/
def ancestorsIn (root x : Node) : List Node :=
  (ancestorsOf x searchDepth [(root, [])]).getD []

/-- The value of an attribute of an element. -/
def attrOfNode (n : Node) (a : String) : Option String :=
  match n with
  | .element _ as _ => attrOf as a
  | _ => none

/-- The `xml:lang` in scope at the end of a list of elements (outermost
first): the last one that carries it. `xml:lang=""` means no language
(XML 1.0 §2.12), the same as no attribute. -/
def langOf (ns : List Node) : Option String :=
  let l := ns.foldl (fun l n => match attrOfNode n "xml:lang" with | some v => some v | none => l) none
  if l == some "" then none else l

/-- The base URI after the `xml:base` attributes of a list of elements
(outermost first), from `base`. -/
def baseThrough (base : String) (ns : List Node) : String :=
  ns.foldl (fun b n => match attrOfNode n "xml:base" with | some v => resolveAgainst b v | none => b) base

/-- Base URI fixup and language fixup (XInclude 1.1 §4.5.5, §4.5.6) of an
included element. `href` is the reference as written, `anc` the element's
ancestors in its resource (outermost first), `siteLang` the language at
the `xi:include` element. The `xml:base` value is the element's base URI
relative to the including element: `href`, then the `xml:base` of each
ancestor and of the element itself. -/
def fixupX (href : String) (sc : List (String × String)) (siteLang : Option String)
    (anc : List Node) : Node → Node
  | .element tag attrs kids =>
    let own := attrs.filter (fun a => a.name != "xml:base")
    let attrs := own ++ [{ name := "xml:base", value := baseThrough href (anc ++ [.element tag attrs kids]) }]
    let lang := langOf (anc ++ [.element tag attrs kids])
    let attrs := if (attrOf attrs "xml:lang").isNone && lang != siteLang
      then attrs ++ [{ name := "xml:lang", value := lang.getD "" }] else attrs
    let attrs := if (sc.lookup "").getD "" != "" && (attrOf attrs "xmlns").isNone && prefixOf tag == ""
      then attrs ++ [{ name := "xmlns", value := "" }] else attrs
    .element tag attrs kids
  | n => n

/-- The nodes that a pointer identifies in a document, each with the
namespace bindings it needs from its ancestors. -/
def select (cfg : Cfg) (d : Document) (p : String) : Except XiErr (List Node) :=
  match cfg.pointer with
  | none => .error (.resource "xpointer is not evaluated")
  | some ev =>
    match ev d p with
    | .syntaxError m => .error (.resource ("xpointer=\"" ++ p ++ "\" is not an XPointer: " ++ m))
    | .noSubresource => .error (.resource ("xpointer=\"" ++ p ++ "\" identifies no subresource"))
    | .hits hs => hs.mapM (fun h => match h with
      | .node (.element t as ks) insc => .ok (.element t (as ++ nsFixupAttrs insc (.element t as ks)) ks)
      | .node n _ => .ok n
      | _ => .error (.fatal ("xpointer=\"" ++ p ++ "\" identifies an attribute or namespace node")))

/-- `n` is `x` or contains it (within the depth `f`). -/
def containsNode : Nat → Node → Node → Bool
  | 0, _, _ => false
  | f + 1, x, n =>
    n == x || (match n with
      | .element _ _ kids => kids.attach.any (fun ⟨k, _⟩ => containsNode f x k)
      | _ => false)

/-- A value of `accept` or `accept-language` with a character outside
`#x20`-`#x7E` (XInclude 1.1 §3.1: a fatal error). -/
def badAcceptValue (attrs : List Attribute) : Bool :=
  ["accept", "accept-language"].any (fun n => match attrOf attrs n with
    | some v => v.toList.any (fun c => c.toNat < 0x20 || c.toNat > 0x7E)
    | none => false)

def isHexDigit (c : Char) : Bool :=
  ('0' ≤ c && c ≤ '9') || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- A `%` that two hexadecimal digits do not follow (RFC 3987
`pct-encoded`): the `href` is not an IRI reference. -/
def badPercent : List Char → Bool
  | [] => false
  | '%' :: a :: b :: rest => !(isHexDigit a && isHexDigit b) || badPercent rest
  | '%' :: _ => true
  | _ :: rest => badPercent rest

/-- The checks on an `xi:include` element that do not need its resource. -/
def includeError (sc : List (String × String)) (attrs : List Attribute) (kids : List Node) :
    Option String :=
  let href := (attrOf attrs "href").getD ""
  let parse := (attrOf attrs "parse").getD "xml"
  let xp := attrOf attrs "xpointer"
  let xiKids := kids.filterMap (fun k => match k with
    | .element t _ _ => let (u, l) := nameOf sc t; if u == xiNs then some l else none
    | _ => none)
  if parse != "xml" && parse != "text" then some ("parse=\"" ++ parse ++ "\"")
  else if href == "" && xp.isNone then some "an include with no href and no xpointer"
  else if href.contains '#' then some "an href with a fragment identifier"
  else if badPercent href.toList then some ("href=\"" ++ href ++ "\" is not an IRI reference")
  else if parse == "text" && xp.isSome then some "parse=\"text\" with an xpointer"
  else if badAcceptValue attrs then some "accept or accept-language with a character outside #x20-#x7E"
  else if xiKids.any (· != "fallback") then some "an element of the XInclude namespace other than xi:fallback in xi:include"
  else if (xiKids.filter (· == "fallback")).length > 1 then some "more than one xi:fallback"
  else none

/-- The attribute declarations of a document and of every document that
it includes with `parse="xml"`, to the depth `f`: the ID-typed attributes
of the acquired infoset. `work` holds the elements still to visit with
the base URI of their document; a tail call per node. -/
def includedAttDecls (cfg : Cfg) : Nat → List (Node × String) → List AttDecl → List AttDecl
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | f + 1, (n, base) :: work, acc =>
    match n with
    | .element tag attrs kids =>
      let local_ := (tag.splitOn ":").getLast!
      let href := (attrOf attrs "href").getD ""
      let more : List (Node × String) × List AttDecl :=
        if local_ == "include" && href != "" && (attrOf attrs "parse").getD "xml" == "xml" then
          let target := resolveAgainst base href
          match (cfg.fetch target).bind (fun bs => (cfg.parseDoc target bs).toOption) with
          | some d => ([(d.root, target)], (d.doctype.map (·.attDecls)).getD [])
          | none => ([], [])
        else ([], [])
      includedAttDecls cfg f (kids.map (fun k => (k, base)) ++ more.1 ++ work) (acc ++ more.2)
    | _ => includedAttDecls cfg f work acc

/-- A document with the attribute declarations of the documents it
includes added to its DTD. -/
def withIncludedIds (cfg : Cfg) (uri : String) (d : Document) (r : Node) : Document :=
  let decls := includedAttDecls cfg 100000 [(d.root, uri)] []
  let dt := d.doctype.getD default
  { d with root := r, doctype := some { dt with attDecls := dt.attDecls ++ decls } }

/-- The top-level nodes of a document (prolog, document element, epilog). -/
def docNodes (d : Document) (r : List Node) : List Node := d.prolog ++ r ++ d.epilog

/-- Process the inclusions of a node of the document `here`: the nodes
that replace it. `chain` holds the resources (URI and pointer) being
included, `base` the URI of `here`, `sc` the namespace scope, `anc` the
ancestors of the node in `here` (innermost first). -/
def expandX (cfg : Cfg) (here : Document) :
    Nat → List String → String → List (String × String) → List Node → Node →
      Except XiErr (List Node)
  | 0, _, _, _, _, _ => .error (.fatal "XInclude nesting too deep")
  | f + 1, chain, base, sc, anc, n =>
    match n with
    | .element tag attrs kids =>
      let sc := scopeOf sc attrs
      let (u, l) := nameOf sc tag
      if u == xiNs && l == "include" then
        let href := (attrOf attrs "href").getD ""
        let parse := (attrOf attrs "parse").getD "xml"
        let xp := attrOf attrs "xpointer"
        let siteAnc := anc.reverse
        let siteLang := langOf siteAnc
        -- the reference as the include's parent reads it (the include's own xml:base)
        let hrefP := match attrOf attrs "xml:base" with
          | some b => resolveAgainst b href
          | none => href
        let got : Except XiErr (List Node) :=
          match includeError sc attrs kids with
          | some m => .error (.fatal m)
          | none =>
            if href == "" then
              -- an intra-document reference: the pointer on `here`
              match select cfg here (xp.getD "") with
              | .error e => .error e
              | .ok hits =>
                if hits.any (containsNode searchDepth n) then
                  .error (.fatal "an intra-document reference to the include element or an ancestor")
                else do
                  let parts ← hits.mapM (fun h =>
                    expandX cfg here f chain base sc (ancestorsIn here.root h).reverse h)
                  pure parts.flatten
            else
              let target := resolveAgainst (baseThrough base (siteAnc ++ [n])) href
              match cfg.fetch target with
              | none => .error (.resource ("cannot read " ++ target))
              | some bs =>
                if parse == "text" then
                  match decodeText (attrOf attrs "encoding") bs with
                  | .ok t => .ok [.text t]
                  | .error m => .error (.fatal (target ++ ": " ++ m))
                else
                  let key := target ++ "#" ++ xp.getD ""
                  if chain.contains key then .error (.fatal ("inclusion loop: " ++ key))
                  else match cfg.parseDoc target bs with
                  | .error m => .error (.fatal (target ++ ": " ++ m))
                  | .ok d => do
                    let roots ← expandX cfg d f (key :: chain) target [] [] d.root
                    match xp with
                    | none => pure ((docNodes d roots).map (fixupX hrefP sc siteLang []))
                    | some p =>
                      match roots with
                      | [r] => do
                        let hits ← select cfg (withIncludedIds cfg target d r) p
                        pure (hits.map (fun h => fixupX hrefP sc siteLang (ancestorsIn r h) h))
                      | _ => .error (.fatal (target ++ ": the document element is not one element after inclusion"))
        match got with
        | .error (.resource m) =>
          let fb := kids.find? (fun k => match k with
            | .element t _ _ => nameOf sc t == (xiNs, "fallback")
            | _ => false)
          match fb with
          | some fbn@(.element _ _ fkids) => do
            let parts ← fkids.mapM (expandX cfg here f chain base sc (fbn :: n :: anc))
            pure parts.flatten
          | _ => .error (.resource m)
        | r => r
      else if u == xiNs && l == "fallback" then
        .error (.fatal "xi:fallback is not a child of xi:include")
      else do
        let parts ← kids.mapM (expandX cfg here f chain base sc (n :: anc))
        pure [.element tag attrs parts.flatten]
    | other => .ok [other]

/-- Process a whole document at `uri`. The nodes that replace the
document element must be one element, with comments, processing
instructions and white space around it, which join the prolog and the
epilog; anything else is a fatal error (the result is not a document). -/
def processDocument (cfg : Cfg) (fuel : Nat) (uri : String) (d : Document) : Except XiErr Document :=
  match expandX cfg d fuel [uri ++ "#"] uri [] [] d.root with
  | .error e => .error e
  | .ok ns =>
    let isElem (n : Node) : Bool := match n with | .element .. => true | _ => false
    let isMisc (n : Node) : Bool := match n with
      | .comment _ | .pi .. => true
      | .text t => t.all isXmlSpace
      | _ => false
    match ns.filter isElem with
    | [r] =>
      if ns.all (fun n => isElem n || isMisc n) then
        let before := (ns.takeWhile (!isElem ·)).filter (fun n => match n with | .text _ => false | _ => true)
        let after := ((ns.dropWhile (!isElem ·)).drop 1).filter (fun n => match n with | .text _ => false | _ => true)
        .ok { d with prolog := d.prolog ++ before, root := r, epilog := after ++ d.epilog }
      else .error (.fatal "the result of inclusion at the top level is not a document")
    | _ => .error (.fatal "the result of inclusion at the top level is not one element")

/-! ## Checks -/

/-- The text of the nodes that replace the root of `src`, under a
    resource table (`#guard` helper). -/
def runText (res : List (String × String)) (src : String) : String :=
  let parseRoot (t : String) : Except String Node := match parseXML t with
    | .ok d => .ok d.root
    | .error _ => .error "not well-formed"
  match parseXML src with
  | .error _ => "not well-formed"
  | .ok d => match expand (res.lookup ·) parseRoot 16 ["main.xml"] "main.xml" [] d.root with
    | .ok ns =>
      let rec txt : Nat → Node → String
        | 0, _ => ""
        | f + 1, .element t as ks => "<" ++ t ++ String.join (as.map (fun a => " " ++ a.name ++ "=" ++ a.value)) ++ ">" ++
            String.join (ks.map (txt f)) ++ "</" ++ t ++ ">"
        | _, .text s => s
        | _, _ => ""
      String.join (ns.map (txt 50))
    | .error (.resource m) => "resource error: " ++ m
    | .error (.fatal m) => "fatal error: " ++ m

-- parse="xml": the included element, with base URI fixup
#guard runText [("dir/b.xml", "<b>x</b>")]
  "<a xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='dir/b.xml'/></a>" ==
  "<a xmlns:xi=http://www.w3.org/2001/XInclude><b xml:base=dir/b.xml>x</b></a>"
-- parse="text"
#guard runText [("t.txt", "1 < 2")]
  "<a xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='t.txt' parse='text'/></a>" ==
  "<a xmlns:xi=http://www.w3.org/2001/XInclude>1 < 2</a>"
-- a resource error uses the fallback
#guard runText []
  "<a xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='none.xml'><xi:fallback>f</xi:fallback></xi:include></a>" ==
  "<a xmlns:xi=http://www.w3.org/2001/XInclude>f</a>"
-- a resource error without a fallback
#guard runText []
  "<a xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='none.xml'/></a>" ==
  "resource error: cannot read none.xml"
-- an inclusion loop is a fatal error
#guard runText [("main.xml", "<a xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='main.xml'/></a>")]
  "<a xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='main.xml'/></a>" ==
  "fatal error: inclusion loop: main.xml"
-- EXPECTED FAILURE, https://github.com/danbri/factoidal/issues/1220: `expand`
-- (the fn:doc path) does not evaluate xpointer; `expandX` does. When the
-- fn:doc path calls `expandX`, replace this guard with the included element.
#guard runText [("b.xml", "<b id='x'/>")]
  "<a xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='b.xml' xpointer='element(/1)'/></a>" ==
  "resource error: xpointer is not evaluated"
-- an element in another namespace named include is not an inclusion
#guard runText [] "<a xmlns:xi='urn:other'><xi:include href='x'/></a>" ==
  "<a xmlns:xi=urn:other><xi:include href=x></xi:include></a>"

end L4Factoidal.XPath4.XInclude
