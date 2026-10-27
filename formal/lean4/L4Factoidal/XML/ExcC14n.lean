/-
L4Factoidal.XML.ExcC14n — Exclusive XML Canonicalization Version 1.0,
the form WITHOUT comments, of one element subtree of the parse tree of
`L4Factoidal.XML.Parser`.

Spec: Exclusive XML Canonicalization Version 1.0, W3C Recommendation
18 July 2002, https://www.w3.org/TR/2002/REC-xml-exc-c14n-20020718/
(algorithm `http://www.w3.org/2001/10/xml-exc-c14n#`). It is Canonical XML
1.0 (`L4Factoidal.XML.Canonical`, whose escaping and attribute order this
module reuses) with a different rule for namespace nodes (§3):

  * an element renders a namespace node only when the element VISIBLY
    UTILIZES its prefix (the prefix of the element's own QName, `""` for
    an unprefixed element, or of one of its attributes' QNames) and the
    nearest output ancestor did not render the same prefix with the same
    namespace name;
  * the prefixes of the InclusiveNamespaces PrefixList (§3, `#default`
    for the default namespace) are treated by the inclusive rule: an
    in-scope binding is rendered unless the nearest output ancestor
    rendered it already;
  * `xmlns=""` is rendered when the element has no default namespace and
    the nearest output ancestor rendered a non-empty one;
  * attributes in the `xml` namespace are not imported from ancestors.

The subtree is the whole node set below one element (the apex), which is
the only document subset XML Signature's same-document reference to an
element by `ID` produces after the enveloped-signature transform. The
apex has no output ancestor, so the namespace bindings its ancestors
declare are rendered on the first element that uses them.

`none` is every refusal: an element or attribute prefix that no
declaration binds (Namespaces in XML §5, "namespace constraint: prefix
declared"). A signature check must never canonicalise a document that is
not namespace-well-formed.

Comments are omitted (the "without comments" variant, the default of the
algorithm URI above). Processing instructions are kept.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XML.Canonical

namespace L4Factoidal.XML.ExcC14n

open L4Factoidal.XML
open L4Factoidal.XML.Canonical (Scope nsDecls extendScope splitQName lookup escText
  escAttr sortBy strLt pairLt isNsDeclName declText rootScope)

/-- The prefixes an element visibly utilizes (§3): its own, and those of its
attributes that are not namespace declarations. An unprefixed attribute is
in no namespace, so it utilizes nothing; the `xml` prefix is never
rendered. -/
def utilized (tag : String) (attrs : List Attribute) : List String :=
  let ps := attrs.filterMap fun a =>
    if isNsDeclName a.name then none
    else
      let p := (splitQName a.name).1
      if p == "" || p == "xml" then none else some p
  ((splitQName tag).1 :: ps).eraseDups.filter (· != "xml")

/-- A PrefixList token as a prefix: `#default` is the default namespace. -/
def prefixOfToken (t : String) : String := if t == "#default" then "" else t

/-- Record a rendered binding. Unlike `extendScope`, an empty namespace
name (`xmlns=""`) is kept, so a later element can see that the default
namespace was undeclared in the output. -/
def setRendered (r : Scope) (b : String × String) : Scope :=
  r.filter (fun x => x.1 != b.1) ++ [b]

/-- The declaration, if any, to render for prefix `p` on an element whose
bindings are `own`, below output ancestors that rendered `rendered`.
`required`: the element visibly utilizes `p`, so an unbound non-empty
prefix is a refusal (outer `none`); a PrefixList prefix that is not in
scope is simply not rendered. -/
def declFor (own rendered : Scope) (required : Bool) (p : String) :
    Option (Option (String × String)) :=
  match lookup own p with
  | some u => if lookup rendered p == some u then some none else some (some (p, u))
  | none =>
      if p == "" then
        match lookup rendered "" with
        | some u => if u.isEmpty then some none else some (some ("", ""))
        | none => some none
      else if required then none
      else some none

/-- The namespace declarations an element renders, sorted by prefix (the
default namespace, prefix `""`, first). -/
def renderDecls (incl : List String) (own rendered : Scope) (tag : String)
    (attrs : List Attribute) : Option (List (String × String)) :=
  let used := utilized tag attrs
  let extra := (incl.map prefixOfToken).eraseDups.filter (fun p => p != "xml" && !used.contains p)
  let step (req : Bool) (acc : Option (List (String × String))) (p : String) :=
    acc.bind fun ds => (declFor own rendered req p).map fun d => ds ++ d.toList
  let ds := extra.foldl (step false) (used.foldl (step true) (some []))
  ds.map (sortBy (fun a b => strLt a.1 b.1))

/-- The attributes of an element, namespace declarations removed, sorted by
namespace name and then local name (Canonical XML §2.3); `none` when an
attribute prefix is unbound. -/
def attrText (sc : Scope) (as : List Attribute) : Option String :=
  let plain := as.filter (fun a => !isNsDeclName a.name)
  let keyed := plain.map fun a =>
    let (p, l) := splitQName a.name
    if p == "" then some (("", a.name), a) else (lookup sc p).map fun u => ((u, l), a)
  if keyed.any Option.isNone then none
  else
    let ks := keyed.filterMap id
    let sorted := sortBy (fun x y => pairLt x.1 y.1) ks
    some (String.join (sorted.map (fun (_, a) => " " ++ a.name ++ "=\"" ++ escAttr a.value ++ "\"")))

mutual

/-- The canonical form of one node. `sc`: the bindings in force on its
parent; `rendered`: the bindings its output ancestors rendered. -/
def canonNode (incl : List String) (sc rendered : Scope) : Node → Option String
  | .text s     => some (escText s)
  | .cdata s    => some (escText s)
  | .comment _  => some ""
  | .pi t d     => some ("<?" ++ t ++ (if d.isEmpty then "" else " " ++ d) ++ "?>")
  | .element t attrs kids =>
      let own := extendScope sc (nsDecls attrs)
      match renderDecls incl own rendered t attrs, attrText own attrs with
      | some ds, some at_ =>
          match canonNodesAcc incl own (ds.foldl setRendered rendered) kids "" with
          | some body => some ("<" ++ t ++ declText ds ++ at_ ++ ">" ++ body ++ "</" ++ t ++ ">")
          | none => none
      | _, _ => none

/-- The canonical forms of `ns` appended to `acc`; a tail call per sibling. -/
def canonNodesAcc (incl : List String) (sc rendered : Scope) : List Node → String → Option String
  | [],      acc => some acc
  | n :: ns, acc =>
      match canonNode incl sc rendered n with
      | some s => canonNodesAcc incl sc rendered ns (acc ++ s)
      | none => none

end

/-- Exclusive XML Canonicalization 1.0, omitting comments, of the element
`n` and its subtree. `ancestors`: the namespace bindings in force on `n`'s
parent (`rootScope` for a document element). `incl`: the
InclusiveNamespaces PrefixList tokens. -/
def canonSubtree (incl : List String) (ancestors : Scope) (n : Node) : Option String :=
  canonNode incl ancestors [] n

/-- The same, for a document element given as text: a check helper. -/
def canonText? (incl : List String) (s : String) : Option String :=
  match parseXML s with
  | .ok d => canonSubtree incl rootScope d.root
  | .error _ => none

/-! ## Checks -/

-- A declaration that the element does not use is dropped; one an
-- ancestor declared is rendered where it is first used.
#guard canonText? [] "<a xmlns:p=\"u\" xmlns:q=\"v\"><p:b/></a>"
  == some "<a><p:b xmlns:p=\"u\"></p:b></a>"
-- The default namespace is visibly utilized by an unprefixed element.
#guard canonText? [] "<a xmlns=\"u\"><b/></a>" == some "<a xmlns=\"u\"><b></b></a>"
-- A binding already rendered by an output ancestor is not repeated.
#guard canonText? [] "<p:a xmlns:p=\"u\"><p:b xmlns:p=\"u\"/></p:a>"
  == some "<p:a xmlns:p=\"u\"><p:b></p:b></p:a>"
-- ... but a different namespace name for the same prefix is.
#guard canonText? [] "<p:a xmlns:p=\"u\"><p:b xmlns:p=\"v\"/></p:a>"
  == some "<p:a xmlns:p=\"u\"><p:b xmlns:p=\"v\"></p:b></p:a>"
-- `xmlns=""` only below an output ancestor with a default namespace.
#guard canonText? [] "<a xmlns=\"u\"><b xmlns=\"\"/></a>"
  == some "<a xmlns=\"u\"><b xmlns=\"\"></b></a>"
#guard canonText? [] "<a><b xmlns=\"\"/></a>" == some "<a><b></b></a>"
-- An attribute prefix is utilized; attributes sort by namespace name.
#guard canonText? [] "<a xmlns:z=\"http://a\" xmlns:y=\"http://b\" y:k=\"1\" z:k=\"2\" k=\"3\"/>"
  == some "<a xmlns:y=\"http://b\" xmlns:z=\"http://a\" k=\"3\" z:k=\"2\" y:k=\"1\"></a>"
-- An InclusiveNamespaces prefix is rendered although it is not used.
#guard canonText? ["xs"] "<a xmlns:xs=\"http://www.w3.org/2001/XMLSchema\"><b/></a>"
  == some "<a xmlns:xs=\"http://www.w3.org/2001/XMLSchema\"><b></b></a>"
#guard canonText? ["#default"] "<p:a xmlns:p=\"u\" xmlns=\"d\"/>"
  == some "<p:a xmlns=\"d\" xmlns:p=\"u\"></p:a>"
-- Comments are omitted, processing instructions kept, text escaped.
#guard canonText? [] "<a>x<!--c-->y<?t d?>&amp;&lt;&gt;\"</a>"
  == some "<a>xy<?t d?>&amp;&lt;&gt;\"</a>"
-- An unbound prefix is a refusal.
#guard canonText? [] "<p:a/>" == none
#guard canonText? [] "<a p:x=\"1\"/>" == none
-- The subtree of an element below an ancestor: the ancestor's binding is
-- rendered on the apex, its unused bindings are not.
#guard (match parseXML "<r xmlns:ds=\"D\" xmlns:s=\"S\"><ds:SignedInfo><ds:X/></ds:SignedInfo></r>" with
  | .ok { root := .element _ attrs [k], .. } =>
      canonSubtree [] (extendScope rootScope (nsDecls attrs)) k
  | _ => none)
  == some "<ds:SignedInfo xmlns:ds=\"D\"><ds:X></ds:X></ds:SignedInfo>"

end L4Factoidal.XML.ExcC14n
