/-
L4Factoidal.XPath4.BaseUri — the base URI of a node (XDM 4.0 §7.6.2,
the `base-uri` accessor; XML Base 1.0 §4.2).

The root of a tree has the base URI of its document table
(`Doc.baseUri`, else `Doc.uri`). An element with an `xml:base`
attribute has the value of that attribute, resolved against the base
URI of its parent (or of the tree, for a root). Another element, and
the document node, has the base URI of its parent. An attribute, text,
comment or processing-instruction node has the base URI of its parent.
A namespace node has no base URI.
-/
import L4Factoidal.XPath4.Core
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.XPath4

/-- Is `s` an absolute IRI (a scheme, then `:`)? -/
def uriHasScheme (s : String) : Bool :=
  match s.toList with
  | c :: cs =>
    c.isAlpha &&
      (match cs.span (fun d => d.isAlphanum || d == '+' || d == '-' || d == '.') with
       | (_, ':' :: _) => true
       | _ => false)
  | [] => false

/-- Resolve `href` against `base` (RFC 3986 §5.2 when `base` is
    absolute); `href` itself when it is absolute or `base` is empty. -/
def resolveRef (base href : String) : String :=
  if uriHasScheme href || base == "" then href
  else if uriHasScheme base then L4Factoidal.Syntax.resolveIri ((base.splitOn "#").headD base) href
  else href

/-- The `xml:base` attribute of an element record, if any. -/
def Env.xmlBaseOf (e : Env) (n : NodeRef) : Option String :=
  let r := e.nrec n
  if r.kind != .element then none else
  (r.attrs.toList.find? (fun a =>
    let ra := e.nrec (n.at a)
    ra.name.uri == nsXML && ra.name.loc == "base")).map (fun a => (e.nrec (n.at a)).value)

/-- The base URI of the tree that holds `n` (of its root). -/
def Env.treeBaseUri (e : Env) (n : NodeRef) : String :=
  let d := e.doc n
  if d.baseUri != "" then d.baseUri else d.uri

/-- The base URI of a node; `none` when it has none. -/
def Env.baseUriOf (e : Env) (n : NodeRef) : Option String :=
  let r := e.nrec n
  if r.kind == .namespace then none else
  -- the element ancestors (and the node itself when it is an element),
  -- from the root down
  let chain := ((if r.kind == .element then [n] else []) ++ e.ancestors n).reverse
  let b := chain.foldl (fun cur m =>
    match e.xmlBaseOf m with
    | some v => resolveRef cur v.trimAscii.toString
    | none => cur) (e.treeBaseUri n)
  if b == "" then none else some b

end L4Factoidal.XPath4
