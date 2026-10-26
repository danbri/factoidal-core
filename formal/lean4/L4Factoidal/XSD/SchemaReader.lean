/-
L4Factoidal.XSD.SchemaReader — read the SIMPLE-TYPE part of a schema
document (XML Schema 1.1 Part 1 §3.16, the `<simpleType>` element) into
the `SimpleType` of `XSD/SimpleType.lean`.

This is NOT the Part 1 schema-document parser: it reads exactly the
subset a DATATYPE test needs — top-level `element` declarations, named
and anonymous `simpleType` definitions, `restriction` / `list` /
`union`, and the §4.3 facet elements — and it CLASSIFIES every other
schema document rather than pretending to read it. The classification
is what lets the runner report a datatype score whose denominator is
the datatype tests and not the whole suite (Part 1 Structures is
https://github.com/danbri/factoidal/issues/666, not this run).

Since 2026-10-10 it also implements the three Part 1 rules a datatype
instance test turns on, because without them the reader answered a
different question from the one the test asks:

  * §4.2.2 conditional inclusion (`vc:minVersion`, `vc:maxVersion`,
    `vc:typeAvailable`, `vc:typeUnavailable`, `vc:facetAvailable`,
    `vc:facetUnavailable`), applied to the schema document before it is
    read (`ciNode`);
  * §3.3.4.3 clause 1: an element declaration applies to an element
    with the same EXPANDED name, so a declaration is found by the
    schema's `targetNamespace` and its name, never by the local name
    alone (`elementDecl?`);
  * §3.3.4.3 clause 4 and §3.3.4.2: an `xsi:type` on the element names
    the type the element is validated against, when it resolves and is
    validly substitutable for the declared type (§3.16.6.3 Type
    Derivation OK (Simple)); an `xsi:type` that does not resolve makes
    the element invalid (G.1.12) (`governing`).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD.SimpleType
import L4Factoidal.XML.Parser

namespace L4Factoidal.XSD

open L4Factoidal.XML

/-- What a schema document contains, from the datatype runner's point
of view. -/
inductive SchemaClass where
  /-- Only simple type definitions and element declarations whose type
  is a simple type: a datatype test. -/
  | datatypeOnly
  /-- Complex types, attributes, groups, identity constraints: a Part 1
  Structures test. -/
  | structures
  /-- Both, or a construct the reader does not model (`include`,
  `import`, `redefine`, `override`). -/
  | mixed
deriving DecidableEq, Repr, Inhabited

/-! ## Names and namespaces -/

def localOf (qn : String) : String :=
  match qn.splitOn ":" with
  | [_, l] => l
  | _      => qn

def prefixOf (qn : String) : String :=
  match qn.splitOn ":" with
  | [p, _] => p
  | _      => ""

abbrev NsBindings := List (String × String)

def bindingsOf (attrs : List Attribute) : NsBindings :=
  attrs.filterMap (fun a =>
    if a.name == "xmlns" then some ("", a.value)
    else if a.name.startsWith "xmlns:"
    then some ((a.name.drop 6).toString, a.value)
    else none)

def resolvePrefix (bs : NsBindings) (p : String) : Option String :=
  (bs.find? (fun b => b.1 == p)).map (·.2)

def attrOf (name : String) : Node → Option String
  | .element _ attrs _ => (attrs.find? (fun a => a.name == name)).map (·.value)
  | _ => none

def childrenOf : Node → List Node
  | .element _ _ cs => cs
  | _ => []

def tagOf : Node → String
  | .element t _ _ => t
  | _ => ""

def elementChildren (n : Node) : List Node :=
  (childrenOf n).filter (fun c => match c with | .element _ _ _ => true | _ => false)

/-! ## Facets -/

def natOfString? (s : String) : Option Nat :=
  let cs := s.toList
  if allDigitsL cs then some (natOfDigits cs) else none

def explicitTzOf? (s : String) : Option ExplicitTz :=
  if s == "required" then some .required
  else if s == "prohibited" then some .prohibited
  else if s == "optional" then some .optional
  else none

def whiteSpaceOf? (s : String) : Option WhiteSpace :=
  if s == "preserve" then some .preserve
  else if s == "replace" then some .replace
  else if s == "collapse" then some .collapse
  else none

/-- Fold the facet children of one `restriction` into a `Facets`. The
`pattern` children of ONE restriction are alternatives, so they become
a single group (§4.3.4). -/
def facetsOfRestriction (children : List Node) : Facets :=
  let facetName (n : Node) := localOf (tagOf n)
  let valueOfFacet (n : Node) := (attrOf "value" n).getD ""
  let pats := (children.filter (fun c => facetName c == "pattern")).map valueOfFacet
  let enums := (children.filter (fun c => facetName c == "enumeration")).map valueOfFacet
  let find1 (nm : String) : Option String :=
    (children.find? (fun c => facetName c == nm)).map valueOfFacet
  { length := (find1 "length").bind natOfString?
    minLength := (find1 "minLength").bind natOfString?
    maxLength := (find1 "maxLength").bind natOfString?
    patterns := if pats.isEmpty then [] else [pats]
    enumeration := if enums.isEmpty then none else some enums
    whiteSpace := (find1 "whiteSpace").bind whiteSpaceOf?
    maxInclusive := find1 "maxInclusive"
    maxExclusive := find1 "maxExclusive"
    minInclusive := find1 "minInclusive"
    minExclusive := find1 "minExclusive"
    totalDigits := (find1 "totalDigits").bind natOfString?
    fractionDigits := (find1 "fractionDigits").bind natOfString?
    explicitTimezone := (find1 "explicitTimezone").bind explicitTzOf?
    hasAssertion := children.any (fun c =>
      facetName c == "assertion" || facetName c == "assert") }

/-! ## The schema document -/

structure SchemaDoc where
  bindings : NsBindings
  /-- `targetNamespace` of the `<schema>` element; `none` when absent.
  Every top-level declaration and named type is in it. -/
  targetNamespace : Option String := none
  /-- `blockDefault` of the `<schema>` element: the {disallowed
  substitutions} of a declaration with no `block` of its own. -/
  blockDefault : Option String := none
  /-- Named `simpleType` definitions, by name. -/
  named    : List (String × Node)
  /-- Top-level `element` declarations: name, `type` attribute, inline
  `simpleType` child, and the declaration node itself (for the Part 1
  properties a datatype validator must NOT decide — `fixed`, `default`,
  `nillable`). -/
  elements : List (String × Option String × Option Node × Node)
  klass    : SchemaClass
deriving Inhabited

/-- Is this QName the XML Schema namespace? -/
def isXsdQName (bs : NsBindings) (qn : String) : Bool :=
  resolvePrefix bs (prefixOf qn) == some xsdNamespace

/-- The built-in a QName names, if it names one that a schema document
may USE. §3.4.1: `xs:anyAtomicType` is a special type that "must not be
used as the {base type definition} of any user-defined type" and is not
available as a type reference; a schema that names it is in error, and
the suite's `simple050` and `simple053` groups say so. -/
def builtinOfQName? (bs : NsBindings) (qn : String) : Option Builtin :=
  if isXsdQName bs qn then
    match builtinOfName? (localOf qn) with
    | some .anyAtomicType => none
    | other => other
  else none

/-- Resolve a `simpleType` node into a `SimpleType`. `fuel` bounds the
chain of named-type references. -/
def readSimpleType : Nat → SchemaDoc → Node → Option SimpleType
  | 0, _, _ => none
  | fuel + 1, doc, node =>
    match (elementChildren node).find? (fun c =>
      let l := localOf (tagOf c)
      l == "restriction" || l == "list" || l == "union") with
    | none => none
    | some body =>
      let bodyKind := localOf (tagOf body)
      let kids := elementChildren body
      let inline := kids.find? (fun c => localOf (tagOf c) == "simpleType")
      if bodyKind == "restriction" then
        let f := facetsOfRestriction kids
        match attrOf "base" body with
        | some baseQn =>
            match builtinOfQName? doc.bindings baseQn with
            | some b => some (.atomic b f)
            | none =>
              match (doc.named.find? (fun p => p.1 == localOf baseQn)).map (·.2) with
              | some bn =>
                  match readSimpleType fuel doc bn with
                  | some (.atomic b bf) => some (.atomic b (Facets.merge bf f))
                  | some (.list it bf)  => some (.list it (Facets.merge bf f))
                  | some (.union ms bf) => some (.union ms (Facets.merge bf f))
                  | none => none
              | none => none
        | none =>
            match inline with
            | some st =>
                match readSimpleType fuel doc st with
                | some (.atomic b bf) => some (.atomic b (Facets.merge bf f))
                | some (.list it bf)  => some (.list it (Facets.merge bf f))
                | some (.union ms bf) => some (.union ms (Facets.merge bf f))
                | none => none
            | none => none
      else if bodyKind == "list" then
        match attrOf "itemType" body with
        | some itemQn =>
            match builtinOfQName? doc.bindings itemQn with
            | some b => some (.list (.atomic b Facets.empty) Facets.empty)
            | none =>
              match (doc.named.find? (fun p => p.1 == localOf itemQn)).map (·.2) with
              | some bn => (readSimpleType fuel doc bn).map (fun t => .list t Facets.empty)
              | none => none
        | none =>
            match inline with
            | some st => (readSimpleType fuel doc st).map (fun t => .list t Facets.empty)
            | none => none
      else
        -- union
        let named := match attrOf "memberTypes" body with
          | none => []
          | some ms => (ms.splitOn " ").filter (fun s => s != "")
        let namedTys := named.filterMap (fun qn =>
          match builtinOfQName? doc.bindings qn with
          | some b => some (SimpleType.atomic b Facets.empty)
          | none =>
            match (doc.named.find? (fun p => p.1 == localOf qn)).map (·.2) with
            | some bn => readSimpleType fuel doc bn
            | none => none)
        let inlineTys := (kids.filter (fun c => localOf (tagOf c) == "simpleType")).filterMap
          (fun c => readSimpleType fuel doc c)
        let ms := namedTys ++ inlineTys
        if ms.length == named.length
             + (kids.filter (fun c => localOf (tagOf c) == "simpleType")).length
        then some (.union ms Facets.empty) else none

/-- The Part 1 constructs that put a schema document outside the
datatype-only class. -/
def structureTags : List String :=
  ["complexType", "attribute", "attributeGroup", "group", "notation",
   "include", "import", "redefine", "override", "defaultOpenContent"]

def classifySchema (root : Node) : SchemaClass :=
  let kids := elementChildren root
  let hasStructure := kids.any (fun c => structureTags.contains (localOf (tagOf c)))
  let simpleOnly := kids.all (fun c =>
    let l := localOf (tagOf c)
    l == "simpleType" || l == "annotation" || l == "element")
  -- An element declaration with a complexType child, or with an
  -- identity constraint, is a structures test even when the schema has
  -- no top-level complexType.
  let elemComplex := kids.any (fun c =>
    localOf (tagOf c) == "element" &&
    (elementChildren c).any (fun g =>
      let gl := localOf (tagOf g)
      gl == "complexType" || gl == "key" || gl == "keyref" || gl == "unique"))
  if hasStructure || elemComplex then
    (if simpleOnly && !elemComplex then .mixed else .structures)
  else if simpleOnly then .datatypeOnly
  else .structures

/-! ## §4.2.2 Conditional inclusion -/

/-- The namespace of the `vc:` attributes. -/
def vcNamespace : String := "http://www.w3.org/2007/XMLSchema-versioning"

/-- The version of XSD this processor implements, `V` in §4.2.2, as a
scaled decimal: 11 tenths. -/
def processorVersion : Nat × Nat := (11, 1)

/-- An `xs:decimal` without a sign or exponent, as `(digits, scale)`:
`"1.10"` is `(110, 2)`. `none` for anything else. A version is never
negative. -/
def versionOf? (s : String) : Option (Nat × Nat) :=
  let cs := (s.trim).toList
  let ip := cs.takeWhile Char.isDigit
  let rest := cs.drop ip.length
  match rest with
  | [] => if ip.isEmpty then none else some (natOfDigits ip, 0)
  | '.' :: fr =>
      if (ip.isEmpty && fr.isEmpty) || !(allDigitsL fr) then none
      else some (natOfDigits (ip ++ fr), fr.length)
  | _ => none

/-- `a ≤ b` on two scaled decimals. -/
def versionLe (a b : Nat × Nat) : Bool :=
  a.1 * 10 ^ b.2 ≤ b.1 * 10 ^ a.2

/-- The facets of XSD 1.1 Part 2 §4.3, by the local name of the element
that applies each one. All are recognised; `assertion` is recognised
and its instances are counted apart by the datatype runner. -/
def knownFacets : List String :=
  ["length", "minLength", "maxLength", "pattern", "enumeration", "whiteSpace",
   "maxInclusive", "maxExclusive", "minInclusive", "minExclusive",
   "totalDigits", "fractionDigits", "assertion", "explicitTimezone"]

/-- Is this QName (resolved in `bs`) a type definition AUTOMATICALLY
KNOWN to the processor (§4.2.2)? The built-in datatypes of Part 2, plus
`xs:anyType` and `xs:error` of Part 1. A user-defined type is never
automatically known: it is defined by the schema being read. -/
def typeKnown (bs : NsBindings) (qn : String) : Bool :=
  (qn.splitOn ":").length ≤ 2 &&
  resolvePrefix bs (prefixOf qn) == some xsdNamespace &&
  ((builtinOfName? (localOf qn)).isSome || localOf qn == "anyType" || localOf qn == "error")

def facetKnown (bs : NsBindings) (qn : String) : Bool :=
  (qn.splitOn ":").length ≤ 2 &&
  resolvePrefix bs (prefixOf qn) == some xsdNamespace && knownFacets.contains (localOf qn)

/-- An `xs:QName` list (or any whitespace-separated list): the items,
with whitespace collapsed. -/
def qnameList (s : String) : List String :=
  ((String.ofList (s.toList.map (fun c =>
      if c == '\t' || c == '\n' || c == '\r' then ' ' else c))).splitOn " ").filter (· != "")

/-- §4.2.2: is an element with these attributes IGNORED, together with
its attributes and descendants? `V` is `processorVersion`. A
`vc:minVersion` or `vc:maxVersion` value that is not a decimal decides
nothing here. -/
def ciIgnored (bs : NsBindings) (attrs : List Attribute) : Bool :=
  attrs.any (fun a =>
    if prefixOf a.name == "" || resolvePrefix bs (prefixOf a.name) != some vcNamespace then false
    else
      match localOf a.name with
      | "minVersion" =>
          match versionOf? a.value with
          | some v => !(versionLe v processorVersion)
          | none   => false
      | "maxVersion" =>
          match versionOf? a.value with
          | some v => versionLe v processorVersion
          | none   => false
      | "typeAvailable"    => (qnameList a.value).any (fun q => !(typeKnown bs q))
      | "typeUnavailable"  => (qnameList a.value).all (typeKnown bs)
      | "facetAvailable"   => (qnameList a.value).any (fun q => !(facetKnown bs q))
      | "facetUnavailable" => (qnameList a.value).all (facetKnown bs)
      | _ => false)

mutual

/-- §4.2.2 `ci(S1)`: the element with every ignored descendant removed,
or `none` when the element itself is ignored. `bs` holds the bindings
in force on the parent; an element's own declarations are in force on
its own attributes, so they are added first. -/
def ciNode (bs : NsBindings) : Node → Option Node
  | .element t attrs kids =>
      let bs2 := bindingsOf attrs ++ bs
      if ciIgnored bs2 attrs then none
      else some (.element t attrs (ciNodesAcc bs2 kids []))
  | other => some other

/-- `ci` of each node of `ns` that is kept, after `acc` (earlier ones,
newest first): a tail call per sibling (https://github.com/danbri/factoidal/issues/746). -/
def ciNodesAcc (bs : NsBindings) : List Node → List Node → List Node
  | [], acc => acc.reverse
  | n :: ns, acc =>
      match ciNode bs n with
      | some m => ciNodesAcc bs ns (m :: acc)
      | none   => ciNodesAcc bs ns acc

end

/-- `ci` of each node of a list, the ignored ones dropped. -/
def ciNodes (bs : NsBindings) (ns : List Node) : List Node := ciNodesAcc bs ns []

theorem ciNodesAcc_eq (bs : NsBindings) (ns : List Node) :
    ∀ acc : List Node, ciNodesAcc bs ns acc = acc.reverse ++ ns.filterMap (ciNode bs) := by
  induction ns with
  | nil => intro acc; simp [ciNodesAcc]
  | cons n rest ih =>
      intro acc
      cases h : ciNode bs n with
      | none => simp [ciNodesAcc, h, ih]
      | some m => simp [ciNodesAcc, h, ih]

theorem ciNodes_eq (bs : NsBindings) (ns : List Node) :
    ciNodes bs ns = ns.filterMap (ciNode bs) := by
  simp [ciNodes, ciNodesAcc_eq]

/-- §4.2.2 for the `<schema>` element: when it is itself ignored, the
document keeps it with no children. -/
def conditionalInclusion (root : Node) : Node :=
  match ciNode [] root with
  | some r => r
  | none   =>
      match root with
      | .element t attrs _ => .element t attrs []
      | other              => other

/-- Read a parsed schema document, after §4.2.2 conditional inclusion. -/
def readSchema (doc : Document) : Option SchemaDoc :=
  let root := conditionalInclusion doc.root
  match root with
  | .element tag attrs _ =>
      let bs := bindingsOf attrs
      if localOf tag != "schema" then none
      else
        let kids := elementChildren root
        let named := kids.filterMap (fun c =>
          if localOf (tagOf c) == "simpleType" then
            (attrOf "name" c).map (fun n => (n, c))
          else none)
        let elems := kids.filterMap (fun c =>
          if localOf (tagOf c) == "element" then
            (attrOf "name" c).map (fun n =>
              (n, attrOf "type" c,
               (elementChildren c).find? (fun g => localOf (tagOf g) == "simpleType"),
             c))
          else none)
        some { bindings := bs, named := named, elements := elems,
               klass := classifySchema root,
               targetNamespace := (attrOf "targetNamespace" root).bind
                 (fun t => if t == "" then none else some t),
               blockDefault := attrOf "blockDefault" root }
  | _ => none

/-! ## Element declarations, by expanded name (§3.3.4.3 clause 1) -/

/-- The top-level element declaration for the expanded name
`(ns, name)`. Every top-level declaration is in the schema's
`targetNamespace`, so a namespace that differs finds nothing, whatever
the local name. -/
def elementDecl? (doc : SchemaDoc) (ns : Option String) (name : String)
    : Option (String × Option String × Option Node × Node) :=
  if doc.targetNamespace != ns then none
  else doc.elements.find? (fun e => e.1 == name)

/-- The simple type of a top-level element declaration. -/
def elementType? (doc : SchemaDoc) (ns : Option String) (name : String) : Option SimpleType :=
  match elementDecl? doc ns name with
  | none => none
  | some (_, tyQn, inline, _) =>
      match tyQn with
      | some qn =>
          match builtinOfQName? doc.bindings qn with
          | some b => some (.atomic b Facets.empty)
          | none =>
            match (doc.named.find? (fun p => p.1 == localOf qn)).map (·.2) with
            | some bn => readSimpleType 16 doc bn
            | none => none
      | none =>
          match inline with
          | some st => readSimpleType 16 doc st
          | none => none

/-- The element declaration's §3.3.1 value constraint (`fixed` or
`default`). An instance validated against a declaration that carries
one is not deciding a DATATYPE question — the outcome turns on the
Part 1 value constraint — so the runner buckets it. -/
def elementValueConstraint? (doc : SchemaDoc) (ns : Option String) (name : String)
    : Option String :=
  match elementDecl? doc ns name with
  | none => none
  | some (_, _, _, node) =>
      (attrOf "fixed" node).orElse (fun _ => attrOf "default" node)

/-! ## The instance's document element -/

def xsiNamespace : String := "http://www.w3.org/2001/XMLSchema-instance"

/-- The namespace name of a DOCUMENT element: its prefix resolved
against its own declarations, since it has no ancestors. `none` for no
namespace, including after `xmlns=""`. -/
def rootNamespace (root : Node) : Option String :=
  match root with
  | .element tag attrs _ =>
      match resolvePrefix (bindingsOf attrs) (prefixOf tag) with
      | some "" => none
      | other   => other
  | _ => none

/-- The value of an attribute in the XML Schema instance namespace on a
document element, by local name (`type`, `schemaLocation`, ...). -/
def xsiAttr? (root : Node) (local' : String) : Option String :=
  match root with
  | .element _ attrs _ =>
      let bs := bindingsOf attrs
      (attrs.find? (fun a =>
        prefixOf a.name != "" && localOf a.name == local' &&
        resolvePrefix bs (prefixOf a.name) == some xsiNamespace)).map (·.value)
  | _ => none

/-! ## Type references and Type Derivation OK (Simple) (§3.16.6.3) -/

/-- A simple type definition, by how a schema names it: a built-in, a
named `simpleType` of this schema document (by local name), or an
anonymous `simpleType` element. -/
inductive TypeRef where
  | builtin (b : Builtin)
  | named (name : String)
  | anon (node : Node)
deriving DecidableEq, Inhabited

/-- The node that defines a named type. -/
def namedNode? (doc : SchemaDoc) (name : String) : Option Node :=
  (doc.named.find? (fun p => p.1 == name)).map (·.2)

/-- A QName used INSIDE the schema document (`base`, `memberTypes`,
`type`), as a reference. Named types are found by local name, as
`readSimpleType` finds them. -/
def refOfQName? (doc : SchemaDoc) (qn : String) : Option TypeRef :=
  if isXsdQName doc.bindings qn then (builtinOfQName? doc.bindings qn).map .builtin
  else (namedNode? doc (localOf qn)).map (fun _ => .named (localOf qn))

/-- The defining node of a reference, if it has one. -/
def TypeRef.node? (doc : SchemaDoc) : TypeRef → Option Node
  | .builtin _ => none
  | .named n   => namedNode? doc n
  | .anon n    => some n

/-- The `restriction`, `list` or `union` child of a `simpleType`. -/
def bodyOf? (n : Node) : Option Node :=
  (elementChildren n).find? (fun c =>
    let l := localOf (tagOf c)
    l == "restriction" || l == "list" || l == "union")

/-- §3.16.1 {base type definition}. A `list` or a `union` has
`xs:anySimpleType`; a `restriction` has its `base` or its inline type. -/
def baseRef? (doc : SchemaDoc) (t : TypeRef) : Option TypeRef :=
  match t with
  | .builtin b => b.base?.map .builtin
  | _ =>
    match (t.node? doc).bind bodyOf? with
    | none => none
    | some body =>
        if localOf (tagOf body) == "restriction" then
          match attrOf "base" body with
          | some qn => refOfQName? doc qn
          | none => ((elementChildren body).find? (fun c =>
                      localOf (tagOf c) == "simpleType")).map .anon
        else some (.builtin .anySimpleType)

inductive Variety where
  | atomic | list | union | none
deriving DecidableEq, Inhabited

/-- §3.16.1 {variety}. A restriction has its base's variety. -/
def varietyOf : Nat → SchemaDoc → TypeRef → Variety
  | 0, _, _ => .none
  | fuel + 1, doc, t =>
    match t with
    | .builtin .anySimpleType => .none
    | .builtin .nmtokens | .builtin .idrefs | .builtin .entities => .list
    | .builtin _ => .atomic
    | _ =>
      match (t.node? doc).bind bodyOf? with
      | none => .none
      | some body =>
          let l := localOf (tagOf body)
          if l == "list" then .list
          else if l == "union" then .union
          else match baseRef? doc t with
            | some b => varietyOf fuel doc b
            | none   => .none

/-- The facet elements a `restriction` applies. -/
def facetChildren (body : Node) : List Node :=
  (elementChildren body).filter (fun c => knownFacets.contains (localOf (tagOf c)))

/-- §3.16.1 {member type definitions} of a union, and whether its
{facets} is empty: a `union` defines its members and has no facets; a
`restriction` of a union keeps the base's members and adds its own
facets. -/
def unionMembers : Nat → SchemaDoc → TypeRef → List TypeRef × Bool
  | 0, _, _ => ([], false)
  | fuel + 1, doc, t =>
    match (t.node? doc).bind bodyOf? with
    | none => ([], true)
    | some body =>
        let l := localOf (tagOf body)
        if l == "union" then
          let named := (qnameList ((attrOf "memberTypes" body).getD "")).filterMap
            (refOfQName? doc)
          let inline := ((elementChildren body).filter (fun c =>
            localOf (tagOf c) == "simpleType")).map .anon
          (named ++ inline, true)
        else if l == "restriction" then
          match baseRef? doc t with
          | some b =>
              let (ms, empty) := unionMembers fuel doc b
              (ms, empty && (facetChildren body).isEmpty)
          | none => ([], false)
        else ([], true)

/-- §3.16.6.3 Type Derivation OK (Simple): is `d` validly derived from
`b`, subject to the blocking keywords `blocked`? Clause 1: the same
type. Clause 2.1: otherwise `restriction` must not be blocked. Clause
2.2.1/2.2.2: `d`'s base is `b` or is derived from it. Clause 2.2.3: a
list or union is derived from `xs:anySimpleType`. Clause 2.2.4: `b` is a
union with no facets and `d` is derived from one of its members
(transitively, through further facet-free unions). `fuel` bounds the
chains, which a valid schema keeps finite. -/
def derivedOk : Nat → SchemaDoc → List String → TypeRef → TypeRef → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, doc, blocked, d, b =>
    if d == b then true
    else if blocked.contains "restriction" || blocked.contains "#all" then false
    else
      (match baseRef? doc d with
       | some db => db == b || derivedOk fuel doc blocked db b
       | none    => false)
      || ((varietyOf fuel doc d == .list || varietyOf fuel doc d == .union)
           && b == .builtin .anySimpleType)
      || (varietyOf fuel doc b == .union &&
          (let (ms, empty) := unionMembers fuel doc b
           empty && ms.any (fun m => derivedOk fuel doc blocked d m)))

/-- The simple type a reference names. -/
def TypeRef.resolve? (doc : SchemaDoc) : TypeRef → Option SimpleType
  | .builtin b => some (.atomic b Facets.empty)
  | .named n   => (namedNode? doc n).bind (readSimpleType 16 doc)
  | .anon n    => readSimpleType 16 doc n

/-- The declared {type definition} of an element declaration node. -/
def declaredRef? (doc : SchemaDoc) (decl : Node) : Option TypeRef :=
  match attrOf "type" decl with
  | some qn => refOfQName? doc qn
  | none => ((elementChildren decl).find? (fun g => localOf (tagOf g) == "simpleType")).map .anon

/-- §3.15.3/§3.17.6.2 QName resolution (Instance) for the document
element's `xsi:type`: the prefix (or, unprefixed, the default
namespace) resolved against the element's own declarations; the type
is a built-in when the namespace is XML Schema's, and a named type of
the schema when it is the schema's `targetNamespace`. -/
def instanceTypeRef? (doc : SchemaDoc) (root : Node) (qn : String) : Option TypeRef :=
  let q := qn.trim
  if (q.splitOn ":").length > 2 then none else
  let bs := match root with | .element _ attrs _ => bindingsOf attrs | _ => []
  let ns : Option String :=
    match resolvePrefix bs (prefixOf q) with
    | some "" => none
    | some u  => some u
    | none    => if prefixOf q == "" then none else some " unbound"
  if ns == some " unbound" then none
  else if ns == some xsdNamespace then (builtinOfName? (localOf q)).map .builtin
  else if ns == doc.targetNamespace then
    (namedNode? doc (localOf q)).map (fun _ => .named (localOf q))
  else none

/-- What decides an element's governing type (§3.3.4.3). -/
inductive Governing where
  /-- The type to validate the element against. -/
  | ok (t : TypeRef)
  /-- `xsi:type` does not resolve: the attribute is invalid (G.1.12),
  and so is the element. -/
  | unresolved (qn : String)
  /-- `xsi:type` resolves but is not validly substitutable for the
  declared type: clause 4 fails. -/
  | notSubstitutable (qn : String)
deriving Inhabited

/-- §3.3.4.3 clause 4 with §3.3.4.2: the governing type of a document
element whose declaration is `decl`. The blocking keywords are the
declaration's {disallowed substitutions}: its `block`, else the
schema's `blockDefault`. -/
def governing (doc : SchemaDoc) (decl : Node) (declared : TypeRef) (root : Node) : Governing :=
  match xsiAttr? root "type" with
  | none => .ok declared
  | some qn =>
      match instanceTypeRef? doc root qn with
      | none => .unresolved qn
      | some t =>
          let blocked := qnameList (((attrOf "block" decl).orElse (fun _ => doc.blockDefault)).getD "")
          if derivedOk 32 doc blocked t declared then .ok t else .notSubstitutable qn

/-! ## Checks -/

private def schemaOf (src : String) : Option SchemaDoc :=
  match parseXML src with
  | .ok d    => readSchema d
  | .error _ => none

private def rootOf (src : String) : Node :=
  match parseXML src with
  | .ok d    => d.root
  | .error _ => .text ""

private def xsHead (rest : String) : String :=
  "<xs:schema xmlns:xs=\"http://www.w3.org/2001/XMLSchema\" " ++ rest

-- §4.2.2: of two declarations of `e`, a 1.1 processor keeps the one
-- whose version range contains 1.1 (vc_003 in the suite).
#guard ((schemaOf (xsHead "xmlns:vc=\"http://www.w3.org/2007/XMLSchema-versioning\">"
    ++ "<xs:element name=\"e\" type=\"xs:positiveInteger\" vc:minVersion=\"1.0\" vc:maxVersion=\"1.1\"/>"
    ++ "<xs:element name=\"e\" type=\"xs:string\" vc:minVersion=\"1.1\"/></xs:schema>")).bind
    (fun s => (elementDecl? s none "e").bind (fun d => attrOf "type" d.2.2.2))) == some "xs:string"
-- maxVersion is exclusive; a typeAvailable naming an unknown type or a
-- facetUnavailable naming only known facets removes the element.
#guard ((schemaOf (xsHead "xmlns:vc=\"http://www.w3.org/2007/XMLSchema-versioning\">"
    ++ "<xs:element name=\"a\" type=\"xs:int\" vc:maxVersion=\"1.1\"/>"
    ++ "<xs:element name=\"b\" type=\"xs:int\" vc:typeAvailable=\"xs:bananaSkin\"/>"
    ++ "<xs:element name=\"c\" type=\"xs:int\" vc:facetUnavailable=\"xs:pattern\"/>"
    ++ "<xs:element name=\"d\" type=\"xs:int\" vc:typeAvailable=\"xs:int\" vc:maxVersion=\"3.2\"/>"
    ++ "</xs:schema>")).map (fun s => s.elements.map (·.1))) == some ["d"]
#guard versionOf? "1.10" == some (110, 2) && versionOf? "1.1.3" == none && versionOf? "10g" == none

-- §3.3.4.3 clause 1: the expanded name decides, not the local name.
#guard ((schemaOf (xsHead "targetNamespace=\"urn:t\"><xs:element name=\"n\" type=\"xs:decimal\"/></xs:schema>")).bind
    (fun s => elementType? s (some "urn:t") "n")).isSome
#guard ((schemaOf (xsHead "targetNamespace=\"urn:t\"><xs:element name=\"n\" type=\"xs:decimal\"/></xs:schema>")).bind
    (fun s => elementType? s (some "urn:other") "n")).isNone
#guard ((schemaOf (xsHead "targetNamespace=\"urn:t\"><xs:element name=\"n\" type=\"xs:decimal\"/></xs:schema>")).bind
    (fun s => elementType? s none "n")).isNone
#guard rootNamespace (rootOf "<p:n xmlns:p=\"urn:t\"/>") == some "urn:t"
#guard rootNamespace (rootOf "<n xmlns=\"urn:t\"/>") == some "urn:t"
#guard rootNamespace (rootOf "<n/>") == none

-- §3.3.4.3 clause 4: `xsi:type` names a restriction of the declared
-- type: it governs. A name that resolves to nothing, or to a type not
-- derived from the declared one, or one blocked by `block`, does not.
private def xsiSchema : Option SchemaDoc :=
  schemaOf (xsHead "xmlns=\"urn:t\" targetNamespace=\"urn:t\">"
    ++ "<xs:element name=\"r\" type=\"xs:boolean\"/>"
    ++ "<xs:element name=\"blk\" type=\"xs:boolean\" block=\"restriction\"/>"
    ++ "<xs:element name=\"u\"><xs:simpleType><xs:union memberTypes=\"xs:integer xs:string\"/></xs:simpleType></xs:element>"
    ++ "<xs:simpleType name=\"T\"><xs:restriction base=\"xs:boolean\"><xs:pattern value=\"true|1\"/></xs:restriction></xs:simpleType>"
    ++ "<xs:simpleType name=\"S\"><xs:restriction base=\"xs:string\"/></xs:simpleType>"
    ++ "</xs:schema>")

private def governs (decl : String) (inst : String) : String :=
  match xsiSchema with
  | none => "no schema"
  | some s =>
      match elementDecl? s (rootNamespace (rootOf inst)) decl with
      | none => "no declaration"
      | some (_, _, _, dn) =>
          match declaredRef? s dn with
          | none => "no declared type"
          | some dr =>
              match governing s dn dr (rootOf inst) with
              | .ok (.named n)   => "named " ++ n
              | .ok (.builtin b) => "builtin " ++ b.localName
              | .ok (.anon _)    => "anonymous"
              | .unresolved _    => "unresolved"
              | .notSubstitutable _ => "not substitutable"

private def xsiI (tag ty : String) : String :=
  "<t:" ++ tag ++ " xmlns:t=\"urn:t\" xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xsi:type=\"" ++ ty ++ "\">1</t:" ++ tag ++ ">"

#guard governs "r" "<t:r xmlns:t=\"urn:t\">1</t:r>" == "builtin boolean"
#guard governs "r" (xsiI "r" "t:T") == "named T"
#guard governs "r" (xsiI "r" "t:TEST") == "unresolved"
#guard governs "r" (xsiI "r" "T") == "unresolved"
#guard governs "r" (xsiI "r" "t:S") == "not substitutable"
#guard governs "blk" (xsiI "blk" "t:T") == "not substitutable"
#guard governs "blk" (xsiI "blk" "xs:boolean" |>.replace "xmlns:t=" "xmlns:xs=\"http://www.w3.org/2001/XMLSchema\" xmlns:t=") == "builtin boolean"
-- §3.16.6.3 clause 2.2.4: a member of a facet-free union is substitutable.
#guard governs "u" (xsiI "u" "t:S") == "named S"

end L4Factoidal.XSD
