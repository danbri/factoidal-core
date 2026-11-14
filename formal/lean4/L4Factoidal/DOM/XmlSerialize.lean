/-
L4Factoidal.DOM.XmlSerialize — the XML serialization of a DOM node
(DOM Parsing and Serialization §3.2 "XML serialization"), as
`XMLSerializer.serializeToString` gives it (the require well-formed flag is not set).

The algorithm is the specification's, step for step, with its three pieces of state:

* the namespace prefix map (`PrefixMap`): for each namespace, the prefixes bound to it
  so far, in the order they were added ("add a prefix", "found", "retrieve a preferred
  prefix string");
* the local prefixes map of an element: the prefixes its own `xmlns:p` attributes
  declare ("recording the namespace information");
* the generated prefix index (`ns1`, `ns2`, …), one counter for the whole serialization.

Where the text of the specification and the tests of WPT
(`domparsing/XMLSerializer-serializeToString.html`) leave a choice, this module says so
at the place:

* An attribute named `xmlns` with no namespace and no prefix (`setAttribute("xmlns", …)`)
  is read as a default namespace declaration, as one in the XMLNS namespace is. The
  serialization would otherwise write two `xmlns` attributes on one start tag.
* An attribute in a namespace that no prefix in scope is bound to keeps its own prefix
  when that prefix is bound to nothing (in scope or on the element); otherwise a prefix
  is generated. (The specification's text always generates; browsers keep the prefix,
  and `xlink:href` of an SVG element stays `xlink:href`.)

Recursion: `serializeNode` follows the nesting of the tree. `fuel` is the arena's size,
which no tree of the arena is deeper than.
-/
import L4Factoidal.DOM.Arena

namespace L4Factoidal.DOM.XmlSerialize

open L4Factoidal.DOM

/-- The namespace prefix map: each namespace (`none`: no namespace) with its prefixes,
oldest first. -/
abbrev PrefixMap := List (Option String × List String)

/-- The prefixes bound to `ns`. -/
def prefixesFor (m : PrefixMap) (ns : Option String) : List String :=
  ((m.find? fun e => e.1 == ns).map (·.2)).getD []

/-- "Add a prefix to the map given a namespace": at the end of the namespace's list. -/
def addPrefix (m : PrefixMap) (ns : Option String) (p : String) : PrefixMap :=
  if m.any (fun e => e.1 == ns) then
    m.map fun e => if e.1 == ns then (e.1, e.2 ++ [p]) else e
  else m ++ [(ns, [p])]

/-- "Found": the map has `p` in the list of `ns`. -/
def found (m : PrefixMap) (ns : Option String) (p : String) : Bool :=
  (prefixesFor m ns).contains p

/-- "Retrieving a preferred prefix string" for `ns`: the preferred prefix when it is in
the namespace's list, else the last prefix of the list, else none. -/
def preferred (m : PrefixMap) (ns : Option String) (pref : Option String) : Option String :=
  let cs := prefixesFor m ns
  match pref with
  | some p => if cs.contains p then some p else cs.getLast?
  | none => cs.getLast?

/-- A prefix is bound to some namespace in the map. -/
def prefixInUse (m : PrefixMap) (p : String) : Bool :=
  m.any fun e => e.2.contains p

/-- Text of a Text node (§3.2.1.4): `&`, `<` and `>` are escaped. -/
def escText (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '&' then "&amp;" else if c == '<' then "&lt;" else if c == '>' then "&gt;"
    else String.singleton c)

/-- "Serializing an attribute value" (§3.2.1.1.3): `&`, `<`, `>` and `"` are escaped; tab,
line feed and carriage return are written as character references, so that an XML parser
reads the same value back (attribute value normalisation would make them spaces). -/
def escAttr (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '&' then "&amp;" else if c == '<' then "&lt;" else if c == '>' then "&gt;"
    else if c == '"' then "&quot;" else if c == '\t' then "&#9;" else if c == '\n' then "&#10;"
    else if c == '\r' then "&#13;" else String.singleton c)

/-- A default namespace declaration: `xmlns` with no prefix, in the XMLNS namespace or in
no namespace. -/
def isDefaultDecl (a : Attr) : Bool :=
  a.pfx.isNone && a.lname == "xmlns" && (a.ns == some xmlnsNS || a.ns.isNone)

/-- The namespace that the value of a declaration names: none for the empty string. -/
def nsOfValue (v : String) : Option String := if v == "" then none else some v

/-- "Recording the namespace information" of an element: the value of its default
namespace declaration (if it has one), the map with its prefix declarations added, and
its local prefixes map (prefix, value). -/
def record (attrs : List Attr) (m : PrefixMap) :
    Option String × PrefixMap × List (String × String) :=
  attrs.foldl (fun (acc : Option String × PrefixMap × List (String × String)) (a : Attr) =>
    if isDefaultDecl a then (some a.value, acc.2.1, acc.2.2)
    else if a.ns == some xmlnsNS && a.pfx.isSome then
      if a.value == xmlNS || found acc.2.1 (nsOfValue a.value) a.lname then acc
      else (acc.1, addPrefix acc.2.1 (nsOfValue a.value) a.lname, acc.2.2 ++ [(a.lname, a.value)])
    else acc) (none, m, [])

/-- One attribute as markup: space, name, `="`, the escaped value, `"`. -/
def attrMarkup (name value : String) : String :=
  " " ++ name ++ "=\"" ++ escAttr value ++ "\""

/-- "XML serialization of the attributes" of an element: the markup, the map and the
prefix index after it. `loc` is the element's local prefixes map; `ignoreDflt` says that
the element's default namespace declaration is not written (the start tag wrote one, or
none is needed). -/
def attrsMarkup (attrs : List Attr) (m : PrefixMap) (idx : Nat) (loc : List (String × String))
    (ignoreDflt : Bool) : String × PrefixMap × Nat :=
  attrs.foldl (fun (acc : String × PrefixMap × Nat) (a : Attr) =>
    let out := acc.1
    let m := acc.2.1
    let idx := acc.2.2
    match a.ns with
    | none =>
      if isDefaultDecl a && ignoreDflt then acc
      else (out ++ attrMarkup a.lname a.value, m, idx)
    | some ans =>
      if ans == xmlnsNS then
        let redeclared := a.pfx.isSome &&
          ((loc.find? fun x => x.1 == a.lname).map (·.2)) != some a.value &&
          found m (nsOfValue a.value) a.lname
        if a.value == xmlNS || (a.pfx.isNone && ignoreDflt) || redeclared then acc
        else if a.pfx.isSome then (out ++ attrMarkup ("xmlns:" ++ a.lname) a.value, m, idx)
        else (out ++ attrMarkup a.lname a.value, m, idx)
      else
        match preferred m (some ans) a.pfx with
        | some p => (out ++ attrMarkup (p ++ ":" ++ a.lname) a.value, m, idx)
        | none =>
          let keep := match a.pfx with
            | some p => !(loc.any fun x => x.1 == p) && !prefixInUse m p
            | none => false
          let p := if keep then a.pfx.getD "" else s!"ns{idx}"
          (out ++ attrMarkup ("xmlns:" ++ p) ans ++ attrMarkup (p ++ ":" ++ a.lname) a.value,
            addPrefix m (some ans) p, if keep then idx else idx + 1))
    ("", m, idx)

/-- The void elements of HTML, which the serialization writes as `<br />` when they have
no children (§3.2.1.1 step 14). -/
def voidElements : List String :=
  ["area", "base", "basefont", "bgsound", "br", "col", "embed", "frame", "hr", "img", "input",
   "keygen", "link", "menuitem", "meta", "param", "source", "track", "wbr"]

/-- The start tag of an element up to its attributes ("XML serializing an Element node",
steps 6 to 12): the qualified name, the namespace declaration the start tag adds (or
nothing), the inherited namespace of the children, the map, the prefix index, the local
prefixes map and the ignore namespace definition attribute flag. -/
structure Start where
  qname : String
  decl : String
  inherited : Option String
  map : PrefixMap
  idx : Nat
  loc : List (String × String)
  ignoreDflt : Bool

def elementStart (n : Node) (inherited : Option String) (m0 : PrefixMap) (idx : Nat) : Start :=
  let rec_ := record n.attrs.toList m0
  let dflt := rec_.1
  let m := rec_.2.1
  let loc := rec_.2.2
  -- the local default namespace as a namespace: none for the empty string
  let dfltNs : Option String := dflt.bind nsOfValue
  let ns := n.ns
  if inherited == ns then
    { qname := if ns == some xmlNS then "xml:" ++ n.lname else n.lname, decl := "",
      inherited := inherited, map := m, idx := idx, loc := loc, ignoreDflt := dflt.isSome }
  else
    let cand := if n.pfx == some "xmlns" then some "xmlns" else preferred m ns n.pfx
    match cand, n.pfx with
    | some p, _ =>
      { qname := p ++ ":" ++ n.lname, decl := "",
        inherited := if dflt.isSome && dflt != some xmlNS then dfltNs else inherited,
        map := m, idx := idx, loc := loc, ignoreDflt := false }
    | none, some p0 =>
      let gen := loc.any fun x => x.1 == p0
      let p := if gen then s!"ns{idx}" else p0
      { qname := p ++ ":" ++ n.lname, decl := attrMarkup ("xmlns:" ++ p) (ns.getD ""),
        inherited := if dflt.isSome then dfltNs else inherited,
        map := addPrefix m ns p, idx := if gen then idx + 1 else idx, loc := loc,
        ignoreDflt := false }
    | none, none =>
      if dflt == some (ns.getD "") then
        { qname := n.lname, decl := "", inherited := ns, map := m, idx := idx, loc := loc,
          ignoreDflt := false }
      else
        { qname := n.lname, decl := attrMarkup "xmlns" (ns.getD ""), inherited := ns, map := m,
          idx := idx, loc := loc, ignoreDflt := true }

/-- The markup of a DocumentType (§3.2.1.6). -/
def doctypeMarkup (n : Node) : String :=
  "<!DOCTYPE " ++ n.lname ++
    (if n.pubId != "" then " PUBLIC \"" ++ n.pubId ++ "\"" else "") ++
    (if n.sysId != "" && n.pubId == "" then " SYSTEM" else "") ++
    (if n.sysId != "" then " \"" ++ n.sysId ++ "\"" else "") ++ ">"

/-- The "XML serialization algorithm" on node `id` with the inherited namespace, the map
and the prefix index: the markup and the prefix index after it. -/
def serializeNode (d : Dom) : Nat → NodeId → Option String → PrefixMap → Nat → String × Nat
  | 0, _, _, _, idx => ("", idx)
  | fuel + 1, id, inherited, m, idx =>
    let n := d.get id
    match n.type with
    | .element =>
      let st := elementStart n inherited m idx
      let at_ := attrsMarkup n.attrs.toList st.map st.idx st.loc st.ignoreDflt
      let head := "<" ++ st.qname ++ st.decl ++ at_.1
      let isHtml := n.ns == some htmlNS
      let kids : List NodeId :=
        if isHtml && n.lname == "template" then
          (match n.content with
           | some c => (d.get c).kids.toList
           | none => n.kids.toList)
        else n.kids.toList
      if kids.isEmpty && isHtml && voidElements.contains n.lname then (head ++ " />", at_.2.2)
      else if kids.isEmpty && !isHtml then (head ++ "/>", at_.2.2)
      else
        let body := kids.foldl (fun (acc : String × Nat) (c : NodeId) =>
          let r := serializeNode d fuel c st.inherited at_.2.1 acc.2
          (acc.1 ++ r.1, r.2)) (head ++ ">", at_.2.2)
        (body.1 ++ "</" ++ st.qname ++ ">", body.2)
    | .document | .fragment =>
      n.kids.toList.foldl (fun (acc : String × Nat) (c : NodeId) =>
        let r := serializeNode d fuel c inherited m acc.2
        (acc.1 ++ r.1, r.2)) ("", idx)
    | .text => (escText n.data, idx)
    | .cdata => ("<![CDATA[" ++ n.data ++ "]]>", idx)
    | .comment => ("<!--" ++ n.data ++ "-->", idx)
    | .pi => ("<?" ++ n.lname ++ " " ++ n.data ++ "?>", idx)
    | .doctype => (doctypeMarkup n, idx)

/-- `XMLSerializer.serializeToString(node)`: the XML serialization of node `id`, with no
context namespace, the map that binds `xml` to the XML namespace, and prefix index 1. -/
def serialize (d : Dom) (id : NodeId) : String :=
  (serializeNode d (d.size + 1) id none [(some xmlNS, ["xml"])] 1).1

end L4Factoidal.DOM.XmlSerialize
