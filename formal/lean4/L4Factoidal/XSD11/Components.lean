/-
L4Factoidal.XSD11.Components — the schema components of XML Schema 1.1
Part 1: Structures (W3C Recommendation, 5 April 2012).

  https://www.w3.org/TR/xmlschema11-1/#components

A schema (§3.17) is a set of components. The components refer to each
other in cycles (an element declaration names a type whose content model
contains the same declaration), so this module stores every component
in an ARRAY of its kind and every reference is an INDEX into that array.
The global (named) components are also listed by expanded name.

Simple type definitions reuse `L4Factoidal.XSD.SimpleType` (Part 2) for
their value space: the `body` of a `SimpleDef` is the Part 2 type that
decides "·locally valid·" for a literal. Part 1 adds only what Part 2
does not carry: the name, the base type definition (as an index, so the
derivation chain can be walked), `{final}`, and the variety.

Index layout of `Schema.types` (fixed, so a built-in is found without a
lookup): 0 is `xs:anyType` (§3.4.7), 1 + k is the k-th entry of
`XSD.allBuiltins` (so 1 is `xs:anySimpleType`), and user types follow.
`xs:error` (§3.16.7.3) is the last built-in.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD.SimpleType

namespace L4Factoidal.XSD11

open L4Factoidal.XSD

/-! ## Names -/

/-- An expanded name (Namespaces in XML 1.0 §2.1): the namespace name
(the empty string when the name has no namespace) and the local part. -/
structure XName where
  ns  : String
  loc : String
deriving DecidableEq, Repr, Inhabited, Hashable

def XName.show (n : XName) : String :=
  if n.ns == "" then n.loc else "{" ++ n.ns ++ "}" ++ n.loc

def xsNS  : String := "http://www.w3.org/2001/XMLSchema"
def xsiNS : String := "http://www.w3.org/2001/XMLSchema-instance"
def xmlNS : String := "http://www.w3.org/XML/1998/namespace"

def xs (l : String) : XName := ⟨xsNS, l⟩

/-- In-scope namespace bindings: prefix (empty string for the default
namespace) to namespace name. The first binding of a prefix wins. -/
abbrev NsBindings := List (String × String)

def lookupNs (bs : NsBindings) (p : String) : Option String :=
  if p == "xml" then some xmlNS else (bs.find? (fun b => b.1 == p)).map (·.2)

/-! ## Value constraints, wildcards, particles -/

inductive VCKind where
  | default | fixed
deriving DecidableEq, Repr, Inhabited

/-- §3.2.1 / §3.3.1 `{value constraint}`: the kind and the lexical form
(the value is computed against the governing type when it is used). -/
structure ValueConstraint where
  kind : VCKind
  lex  : String
deriving DecidableEq, Repr, Inhabited

/-- §3.10.1 `{namespace constraint}` `{variety}` and `{namespaces}`.
The empty string stands for ·absent· (no namespace). -/
inductive NsConstraint where
  | any
  | enum (l : List String)
  | not (l : List String)
deriving DecidableEq, Repr, Inhabited

inductive ProcessContents where
  | strict | lax | skip
deriving DecidableEq, Repr, Inhabited

/-- §3.10.1 Wildcard. `notQName` holds the `{disallowed names}` QNames;
`notDefined` and `notSibling` are the keywords `##defined` and
`##definedSibling`. -/
structure Wildcard where
  ns : NsConstraint := .any
  notQName : List XName := []
  notDefined : Bool := false
  notSibling : Bool := false
  pc : ProcessContents := .strict
deriving DecidableEq, Repr, Inhabited

/-- §3.10.4.1 Wildcard allows Namespace Name. -/
def NsConstraint.allows (c : NsConstraint) (ns : String) : Bool :=
  match c with
  | .any => true
  | .enum l => l.contains ns
  | .not l => !l.contains ns

/-- §3.10.4.2 Wildcard allows Expanded Name, clauses 1 and 2 (clause 3,
`##defined`, needs the schema and is decided by the validator). -/
def Wildcard.allowsName (w : Wildcard) (n : XName) : Bool :=
  w.ns.allows n.ns && !w.notQName.contains n

inductive Compositor where
  | seq | choice | all
deriving DecidableEq, Repr, Inhabited

/-- §3.9.1 Particle, with its `{term}` folded in: an element declaration
(index into `Schema.elems`), a wildcard, or a model group (§3.8.1).
`max = none` is `unbounded`. -/
inductive Particle where
  | elem  (min : Nat) (max : Option Nat) (decl : Nat)
  | wild  (min : Nat) (max : Option Nat) (w : Wildcard)
  | group (min : Nat) (max : Option Nat) (c : Compositor) (ps : List Particle)
deriving Repr, Inhabited

def Particle.minOcc : Particle → Nat
  | .elem m _ _ | .wild m _ _ | .group m _ _ _ => m

def Particle.maxOcc : Particle → Option Nat
  | .elem _ m _ | .wild _ m _ | .group _ m _ _ => m

def Particle.withOcc (p : Particle) (mn : Nat) (mx : Option Nat) : Particle :=
  match p with
  | .elem _ _ d => .elem mn mx d
  | .wild _ _ w => .wild mn mx w
  | .group _ _ c ps => .group mn mx c ps

/-- The empty sequence, the content model of a complex type with no
particle. -/
def Particle.emptySeq : Particle := .group 1 (some 1) .seq []

/-! ## Assertions and type alternatives -/

/-- §3.13.1 Assertion: the XPath 2.0 `{test}` with its static context. -/
structure Assertion where
  test : String
  ns : NsBindings := []
  xpathDefaultNs : String := ""
  baseUri : String := ""
deriving DecidableEq, Repr, Inhabited

/-- §3.12.1 Type Alternative. `test = none` is the default alternative. -/
structure TypeAlt where
  test : Option String
  typ : Nat
  ns : NsBindings := []
  xpathDefaultNs : String := ""
deriving DecidableEq, Repr, Inhabited

/-! ## Declarations -/

/-- `{disallowed substitutions}` / `{prohibited substitutions}` /
`{final}` members. -/
inductive DerivKw where
  | extension | restriction | substitution | list | union
deriving DecidableEq, Repr, Inhabited

/-- §3.2.1 Attribute Declaration. -/
structure AttrDecl where
  name : XName
  typ : Nat
  vc : Option ValueConstraint := none
  inheritable : Bool := false
  global : Bool := false
deriving DecidableEq, Repr, Inhabited

/-- §3.5.1 Attribute Use. -/
structure AttrUse where
  decl : Nat
  required : Bool := false
  vc : Option ValueConstraint := none
  inheritable : Bool := false
deriving DecidableEq, Repr, Inhabited

/-- §3.3.1 Element Declaration. -/
structure ElemDecl where
  name : XName
  typ : Nat
  nillable : Bool := false
  vc : Option ValueConstraint := none
  abstract : Bool := false
  /-- `{substitution group affiliations}`, as global element names. -/
  substGroups : List XName := []
  block : List DerivKw := []
  final : List DerivKw := []
  /-- `{identity-constraint definitions}`, indices into `Schema.idcs`. -/
  idcs : List Nat := []
  /-- `{type table}`: the alternatives in order, then the default. -/
  alts : List TypeAlt := []
  global : Bool := false
  /-- Set when the declaration's type was not given and must follow the
  first substitution group head (§3.3.2.3). Resolved by the reader. -/
  typeFromHead : Bool := false
deriving DecidableEq, Repr, Inhabited

inductive IdcKind where
  | key | keyref | unique
deriving DecidableEq, Repr, Inhabited

/-- §3.11.1 Identity-constraint Definition. -/
structure IDC where
  name : XName
  kind : IdcKind
  selector : String
  fields : List String
  refer : Option XName := none
  ns : NsBindings := []
  xpathDefaultNs : String := ""
deriving DecidableEq, Repr, Inhabited

/-! ## Type definitions -/

inductive Variety where
  | atomic | list | union
deriving DecidableEq, Repr, Inhabited

inductive Deriv where
  | restriction | extension
deriving DecidableEq, Repr, Inhabited

/-- §3.16.1 Simple Type Definition. `body` is the Part 2 type with the
facets of the whole derivation chain applied. -/
structure SimpleDef where
  name : Option XName
  base : Nat
  variety : Variety
  /-- For an atomic type: the built-in primitive (or ordinary built-in)
  it is ultimately derived from. -/
  builtin : Option Builtin := none
  item : Option Nat := none
  members : List Nat := []
  facets : Facets := {}
  /-- Names of facets declared `fixed="true"` at this step. -/
  fixedFacets : List String := []
  final : List DerivKw := []
  asserts : List Assertion := []
  body : SimpleType := .atomic .anySimpleType {}
deriving Repr, Inhabited

inductive OpenMode where
  | interleave | suffix
deriving DecidableEq, Repr, Inhabited

/-- §3.4.1 `{content type}`. `simple` names the simple type definition
of the content; `elems` carries `{particle}` and whether the content is
mixed. -/
inductive ContentType where
  | empty
  | simple (st : Nat)
  | elems (p : Particle) (mixed : Bool)
deriving Repr, Inhabited

/-- §3.4.1 Complex Type Definition. -/
structure ComplexDef where
  name : Option XName
  base : Nat
  deriv : Deriv := .restriction
  abstract : Bool := false
  attrUses : List AttrUse := []
  attrWild : Option Wildcard := none
  content : ContentType := .empty
  openContent : Option (OpenMode × Wildcard) := none
  final : List DerivKw := []
  block : List DerivKw := []
  asserts : List Assertion := []
  /-- Attribute names a restriction declares `use="prohibited"`. -/
  prohibited : List XName := []
deriving Repr, Inhabited

inductive TypeDef where
  | simple (s : SimpleDef)
  | complex (c : ComplexDef)
deriving Repr, Inhabited

def TypeDef.name : TypeDef → Option XName
  | .simple s => s.name
  | .complex c => c.name

def TypeDef.base : TypeDef → Nat
  | .simple s => s.base
  | .complex c => c.base

def TypeDef.isSimple : TypeDef → Bool
  | .simple _ => true
  | .complex _ => false

/-! ## The schema -/

/-- §3.17 Schema: the component arrays and the global name tables.
`errors` records every schema-level error (a violated Schema Component
Constraint or Schema Representation Constraint, or an unresolved
reference); a schema with errors is not a valid schema. -/
structure Schema where
  types : Array TypeDef := #[]
  elems : Array ElemDecl := #[]
  attrs : Array AttrDecl := #[]
  idcs  : Array IDC := #[]
  gTypes : List (XName × Nat) := []
  gElems : List (XName × Nat) := []
  gAttrs : List (XName × Nat) := []
  gIdcs  : List (XName × Nat) := []
  notations : List XName := []
  errors : List String := []
  /-- Constructs the reader does not implement; a schema that has any is
  reported as not decided, never as valid or invalid. -/
  unsupported : List String := []
deriving Inhabited

def Schema.type (s : Schema) (i : Nat) : TypeDef := s.types.getD i default
def Schema.elem (s : Schema) (i : Nat) : ElemDecl := s.elems.getD i default
def Schema.attr (s : Schema) (i : Nat) : AttrDecl := s.attrs.getD i default

def Schema.typeIdx? (s : Schema) (n : XName) : Option Nat := s.gTypes.lookup n
def Schema.elemIdx? (s : Schema) (n : XName) : Option Nat := s.gElems.lookup n
def Schema.attrIdx? (s : Schema) (n : XName) : Option Nat := s.gAttrs.lookup n

/-! ## Built-in types -/

def anyTypeIdx : Nat := 0

/-- The index of a built-in simple type. -/
def builtinIdx (b : Builtin) : Nat :=
  match allBuiltins.idxOf? b with
  | some k => k + 1
  | none => 1

def anySimpleTypeIdx : Nat := builtinIdx .anySimpleType

/-- The index of `xs:error`, right after the built-ins. -/
def errorTypeIdx : Nat := allBuiltins.length + 1

def builtinVariety (b : Builtin) : Variety :=
  match builtinListItem? b with
  | some _ => .list
  | none => .atomic

/-- §3.4.7: `xs:anyType` — mixed content, a lax wildcard with any
namespace, and a lax attribute wildcard. -/
def anyTypeDef : TypeDef :=
  .complex { name := some (xs "anyType"), base := anyTypeIdx, deriv := .restriction,
             attrWild := some { pc := .lax },
             content := .elems (.group 1 (some 1) .seq
                                  [.wild 0 none { pc := .lax }]) true }

def builtinDef (b : Builtin) : TypeDef :=
  let baseIdx := match b.base? with
    | some p => builtinIdx p
    | none => if b == .anySimpleType then anyTypeIdx else anySimpleTypeIdx
  let item := (builtinListItem? b).map builtinIdx
  .simple { name := some (xs b.localName), base := baseIdx,
            variety := builtinVariety b,
            builtin := if b == .anySimpleType then none else some b,
            item,
            -- §3.4.1: NMTOKENS, IDREFS and ENTITIES are list types, so
            -- `length` counts items (Part 2 §4.3.1).
            body := match builtinListItem? b with
              | some it => .list (.atomic it {}) {}
              | none => .atomic b {} }

/-- §3.16.7.3 `xs:error`: a union with no members, so no literal is
valid against it. -/
def errorDef : TypeDef :=
  .simple { name := some (xs "error"), base := anySimpleTypeIdx, variety := .union,
            body := .union [] {} }

/-- A schema holding only the built-in components. -/
def Schema.builtins : Schema :=
  let types := #[anyTypeDef] ++ (allBuiltins.map builtinDef).toArray ++ #[errorDef]
  let gTypes := (xs "anyType", anyTypeIdx) ::
    (allBuiltins.map (fun b => (xs b.localName, builtinIdx b))) ++ [(xs "error", errorTypeIdx)]
  -- §3.2.7: the four built-in attribute declarations of the xsi namespace.
  let attrs : Array AttrDecl := #[
    { name := ⟨xsiNS, "type"⟩, typ := builtinIdx .qname, global := true },
    { name := ⟨xsiNS, "nil"⟩, typ := builtinIdx .boolean, global := true },
    { name := ⟨xsiNS, "schemaLocation"⟩, typ := builtinIdx .anyURI, global := true },
    { name := ⟨xsiNS, "noNamespaceSchemaLocation"⟩, typ := builtinIdx .anyURI, global := true }]
  { types, gTypes, attrs,
    gAttrs := [(⟨xsiNS, "type"⟩, 0), (⟨xsiNS, "nil"⟩, 1),
               (⟨xsiNS, "schemaLocation"⟩, 2), (⟨xsiNS, "noNamespaceSchemaLocation"⟩, 3)] }

/-! ## Derivation -/

/-- The chain of base types from `t` up to `xs:anyType`, each with the
derivation method of the step that produced it. Fuel bounds the walk
(a circular definition is a schema error, §3.4.6 / §3.16.6). -/
def Schema.ancestry (s : Schema) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, t =>
    if t == anyTypeIdx then [t]
    else t :: s.ancestry f (s.type t).base

/-- `d` is `b` or is derived from it, in any number of steps
(§3.4.6.5 / §3.16.6.3, without the blocking keywords). -/
def Schema.derivesFrom (s : Schema) (d b : Nat) : Bool :=
  d == b || b == anyTypeIdx || (s.ancestry 64 d).contains b ||
  -- §3.16.6.3 clause 2.2.4: a member of a union is validly derived from
  -- the union when the union has no facets of its own.
  (match s.type b with
   | .simple sb => sb.variety == .union && sb.members.contains d
   | _ => false)

/-- The derivation methods used on the chain from `d` up to (and not
including) `b`, for the blocking checks of §3.4.6.5 clause 2.3.2 and
§3.3.4.4. -/
def Schema.methodsUpTo (s : Schema) : Nat → Nat → Nat → List DerivKw
  | 0, _, _ => []
  | f + 1, d, b =>
    if d == b || d == anyTypeIdx then []
    else
      let kw := match s.type d with
        | .complex c => if c.deriv == .extension then DerivKw.extension else .restriction
        | .simple _ => .restriction
      kw :: s.methodsUpTo f (s.type d).base b

/-- The types on the chain from `d` up to (not including) `b`. -/
def Schema.chainUpTo (s : Schema) : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | f + 1, d, b =>
    if d == b || d == anyTypeIdx then [] else d :: s.chainUpTo f (s.type d).base b

/-- The simple type definition of a simple type, or of the content of a
complex type with simple content. -/
def Schema.simpleOf? (s : Schema) (t : Nat) : Option SimpleDef :=
  match s.type t with
  | .simple sd => some sd
  | .complex c =>
    match c.content with
    | .simple st => match s.type st with
      | .simple sd => some sd
      | _ => none
    | _ => none

/-- The built-in primitive an atomic simple type is derived from (via its
Part 2 body). -/
def SimpleDef.primitive? (sd : SimpleDef) : Option Builtin :=
  match sd.body with
  | .atomic b _ => b.primitive
  | _ => none

end L4Factoidal.XSD11
