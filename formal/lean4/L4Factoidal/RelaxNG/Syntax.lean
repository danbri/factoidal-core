/-
L4Factoidal.RelaxNG.Syntax — the simple syntax of RELAX NG: name classes,
patterns and the simplified grammar.

Specification: **RELAX NG Specification**, OASIS Committee Specification
3 December 2001 (https://relaxng.org/spec-20011203.html), the same text as
ISO/IEC 19757-2:2008 (Document Schema Definition Languages, Part 2,
Regular-grammar-based validation, RELAX NG).

  * §5 "Simple syntax": after the simplification of §4 a schema is a
    `grammar` with one `start` and a set of `define`s; every `define`
    holds exactly one `element` pattern, and every `ref` names such a
    `define`.
  * §6.1 "Name classes": `anyName`, `nsName`, `name` and `choice`, with
    the optional `except` of `anyName` and `nsName`. `NameClass.contains`
    is the relation `x in nc` of §6.2.

`Pattern.after` is not part of the simple syntax. It is the extra pattern
of the derivative algorithm (James Clark, "An algorithm for RELAX NG
validation", 2002, https://relaxng.org/jclark/derivative.html), which
`L4Factoidal.RelaxNG.Validate` uses; the simplifier never produces it.
-/

namespace L4Factoidal.RelaxNG

/-- The namespace name of the RELAX NG structure vocabulary (§3). -/
def rngNs : String := "http://relaxng.org/ns/structure/1.0"

/-- The datatype library URI of W3C XML Schema Part 2 datatypes, as fixed
by "Guidelines for using W3C XML Schema Datatypes with RELAX NG" (OASIS,
7 September 2001). -/
def xsdLibUri : String := "http://www.w3.org/2001/XMLSchema-datatypes"

/-- The namespace name reserved for namespace declarations (Namespaces in
XML 1.0 §3); §4.16 refuses it in an attribute name class. -/
def xmlnsUri : String := "http://www.w3.org/2000/xmlns"

/-- An expanded name: namespace URI (`""` for no namespace) and local
name. -/
structure QN where
  ns : String
  lname : String
deriving DecidableEq, Repr, Inhabited, Hashable

/-- §6.1: a name class of the simple syntax. The two `…Except` forms are
`anyName` and `nsName` with an `except` child. -/
inductive NameClass where
  | anyName
  | anyNameExcept (e : NameClass)
  | nsName (ns : String)
  | nsNameExcept (ns : String) (e : NameClass)
  | name (ns : String) (lname : String)
  | choice (a b : NameClass)
deriving DecidableEq, Repr, Inhabited

/-- §6.2 "Name classes": the relation between a name and a name class. -/
def NameClass.contains : NameClass → QN → Bool
  | .anyName, _ => true
  | .anyNameExcept e, q => !e.contains q
  | .nsName ns, q => q.ns == ns
  | .nsNameExcept ns e, q => q.ns == ns && !e.contains q
  | .name ns l, q => q.ns == ns && q.lname == l
  | .choice a b, q => a.contains q || b.contains q

/-- A datatype: the URI of its library and its local name (§4.3, §4.4). -/
structure Datatype where
  lib : String
  name : String
deriving DecidableEq, Repr, Inhabited

/-- The context of a string that a datatype reads (§6.2.8, §6.2.9): the
namespace map. The key `""` is the default namespace. For a `value`
pattern it is the in-scope prefixes of the `value` element plus its `ns`
attribute as the default namespace (§4.9); for an instance string it is the
in-scope namespaces of the element. -/
structure Context where
  ns : List (String × String)
deriving DecidableEq, Repr, Inhabited

/-- Resolve a prefix in a context (`""` gives the default namespace, which
is `""` when the context has none). -/
def Context.lookup (cx : Context) (pfx : String) : Option String :=
  match cx.ns.find? (fun b => b.1 == pfx) with
  | some (_, u) => some u
  | none => if pfx == "" then some "" else none

/-- §5: a pattern of the simple syntax, plus `after` of the derivative
algorithm. `data` without and with an `except` child are two
constructors. `params` are the `param` children of `data`, as (name,
value) pairs in document order. -/
inductive Pattern where
  | empty
  | notAllowed
  | text
  | choice (a b : Pattern)
  | interleave (a b : Pattern)
  | group (a b : Pattern)
  | oneOrMore (p : Pattern)
  | list (p : Pattern)
  | data (dt : Datatype) (params : List (String × String))
  | dataExcept (dt : Datatype) (params : List (String × String)) (e : Pattern)
  | value (dt : Datatype) (v : String) (cx : Context)
  | attribute (nc : NameClass) (p : Pattern)
  | element (nc : NameClass) (p : Pattern)
  | ref (name : String)
  | after (a b : Pattern)
deriving DecidableEq, Repr, Inhabited

/-- §5: a schema in the simple syntax. Each `defs` entry is a `define`
whose child is an `element` pattern, given by its name class and content. -/
structure Grammar where
  start : Pattern
  defs : List (String × NameClass × Pattern)
deriving Repr, Inhabited

end L4Factoidal.RelaxNG
