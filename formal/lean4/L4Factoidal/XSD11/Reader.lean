/-
L4Factoidal.XSD11.Reader — XML Schema 1.1 Part 1 §3 "XML
Representation" of every component and §4.2 (assembling a schema from
several schema documents): schema documents to the components of
`XSD11/Components.lean`.

  https://www.w3.org/TR/xmlschema11-1/#layer2

The reader is PURE. The schema documents a schema needs (the first one
and everything it reaches by `include`, `import`, `redefine` and
`override`) are given to it already parsed, keyed by their location;
`Harness/Xsd11Run.lean` and the XPath hook do the file reading, guided
by `refsOf`.

It works in four passes:

1. collect the top-level components of every schema document reached,
   with the context each was declared in (§4.2.3-§4.2.5, including the
   chameleon include, `redefine` and `override`);
2. give every global type, element and attribute declaration its index,
   so references in either direction resolve;
3. build each component (anonymous types, local declarations and
   identity constraints are appended as they are met);
4. finish: the type of an element declared only by its substitution
   group head (§3.3.2.3), the Part 2 `body` of every simple type, the
   effective content and attribute uses of every complex type
   (§3.4.2.3.3 extension and restriction).

Schema-level errors found here (unresolved references, duplicate names,
circular groups, malformed occurrence ranges, …) are recorded in
`Schema.errors`. The Schema Component Constraints are checked by
`XSD11/Constraints.lean`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD11.Components
import L4Factoidal.XSD.SchemaReader

namespace L4Factoidal.XSD11

open L4Factoidal.XML
open L4Factoidal.XSD (SimpleType Facets facetsOfRestriction natOfString? qnameList
  conditionalInclusion localOf prefixOf attrOf tagOf elementChildren bindingsOf childrenOf)

/-! ## Paths -/

def pathDir (p : String) : String :=
  match (p.splitOn "/").reverse with
  | _ :: rest => if rest.isEmpty then "" else String.intercalate "/" rest.reverse ++ "/"
  | []        => ""

def pathNormalize (p : String) : String :=
  let segs := p.splitOn "/"
  let out := segs.foldl (fun acc s =>
    if s == ".." then (match acc with | ".." :: _ => ".." :: acc | _ :: rest => rest | [] => if p.startsWith "/" then [] else [".."])
    else if s == "." || s == "" then acc
    else s :: acc) []
  (if p.startsWith "/" then "/" else "") ++ String.intercalate "/" out.reverse

/-- Resolve a schema location against the location of the document that
names it. An absolute URI is kept as written. -/
def resolveLoc (base rel : String) : String :=
  if rel.startsWith "/" || (rel.splitOn "://").length > 1 then rel
  else pathNormalize (pathDir base ++ rel)

/-! ## Reading context -/

structure DefaultOpen where
  mode : OpenMode
  wild : Wildcard
  appliesToEmpty : Bool
deriving Inhabited

/-- What a schema document fixes for the components declared in it. -/
structure Ctx where
  tns : String := ""
  bs : NsBindings := []
  efdQualified : Bool := false
  afdQualified : Bool := false
  blockDefault : List DerivKw := []
  finalDefault : List DerivKw := []
  xpathDefaultNs : String := ""
  defaultAttrs : Option XName := none
  defaultOpen : Option DefaultOpen := none
  loc : String := ""
  /-- Inside a `redefine`: a reference to the redefined name means the
  original component, which was renamed. -/
  renames : List (String × XName × XName) := []
deriving Inhabited

def Ctx.enter (c : Ctx) (n : Node) : Ctx :=
  match n with
  | .element _ attrs _ => { c with bs := bindingsOf attrs ++ c.bs }
  | _ => c

def isXs (n : Node) (l : String) : Bool := localOf (tagOf n) == l

/-- The element children of `n` that are not `annotation`. -/
def xsKids (n : Node) : List Node :=
  (elementChildren n).filter (fun c => !isXs c "annotation")

def xsKid? (n : Node) (l : String) : Option Node := (xsKids n).find? (fun c => isXs c l)

/-- Resolve a QName-valued attribute in the context (§3.17.6.2,
`QName resolution (Schema Document)`): an unprefixed name takes the
default namespace. -/
def Ctx.resolve? (c : Ctx) (qn : String) : Option XName :=
  let qn := (XSD.qnameList qn).headD ""
  match qn.splitOn ":" with
  | [p, l] => (lookupNs c.bs p).map (fun u => ⟨u, l⟩)
  | [l] => some ⟨(lookupNs c.bs "").getD "", l⟩
  | _ => none

/-- §3.11.2 / §3.12.2 / §3.13.2 `xpathDefaultNamespace`: the namespace
an unprefixed element name in an XPath expression stands for. -/
def Ctx.xdnOf (c : Ctx) (raw : String) : String :=
  match raw with
  | "##defaultNamespace" => (lookupNs c.bs "").getD ""
  | "##targetNamespace" => c.tns
  | "##local" => ""
  | u => u

def Ctx.renamed (c : Ctx) (kind : String) (n : XName) : XName :=
  match c.renames.find? (fun r => r.1 == kind && r.2.1 == n) with
  | some r => r.2.2
  | none => n

def derivKwsOf (s : String) : List DerivKw :=
  let ws := XSD.qnameList s
  if ws.contains "#all" then [.extension, .restriction, .substitution, .list, .union]
  else ws.filterMap (fun w =>
    match w with
    | "extension" => some .extension
    | "restriction" => some .restriction
    | "substitution" => some .substitution
    | "list" => some .list
    | "union" => some .union
    | _ => none)

/-! ## Pass 1: collect the top-level components -/

inductive TopKind where
  | simpleType | complexType | element | attribute | group | attributeGroup | notation
deriving DecidableEq, Repr, Inhabited

def TopKind.ofTag : String → Option TopKind
  | "simpleType" => some .simpleType
  | "complexType" => some .complexType
  | "element" => some .element
  | "attribute" => some .attribute
  | "group" => some .group
  | "attributeGroup" => some .attributeGroup
  | "notation" => some .notation
  | _ => none

def TopKind.isType : TopKind → Bool
  | .simpleType | .complexType => true
  | _ => false

/-- The kind name used for renames and overrides: type definitions share
one symbol space (§3.17.3). -/
def TopKind.space : TopKind → String
  | .simpleType | .complexType => "type"
  | .element => "element"
  | .attribute => "attribute"
  | .group => "group"
  | .attributeGroup => "attributeGroup"
  | .notation => "notation"

structure Top where
  kind : TopKind
  name : XName
  node : Node
  ctx : Ctx
deriving Inhabited

/-- A loaded schema document. -/
structure LoadedDoc where
  loc : String
  doc : Document
deriving Inhabited

structure Collect where
  tops : Array Top := #[]
  seen : List (String × String) := []
  errors : List String := []
  unsupported : List String := []
deriving Inhabited

def openModeOf (s : String) : Option OpenMode :=
  match s with
  | "interleave" => some .interleave
  | "suffix" => some .suffix
  | _ => none

/-- §3.10.2: the namespace constraint and process contents of an `any`
or `anyAttribute` element. -/
def readWildcard (c : Ctx) (n : Node) : Wildcard :=
  let pc := match attrOf "processContents" n with
    | some "lax" => ProcessContents.lax
    | some "skip" => .skip
    | _ => .strict
  let tok (t : String) : String :=
    if t == "##targetNamespace" then c.tns else if t == "##local" then "" else t
  let nsc : NsConstraint :=
    match attrOf "namespace" n, attrOf "notNamespace" n with
    | some v, _ =>
      let ws := XSD.qnameList v
      if ws == ["##any"] || ws.isEmpty && v == "##any" then .any
      else if ws == ["##other"] then .not ["", c.tns].eraseDups
      else .enum (ws.map tok)
    | none, some v => .not ((XSD.qnameList v).map tok)
    | none, none => .any
  let notQ := match attrOf "notQName" n with
    | some v => XSD.qnameList v
    | none => []
  { ns := nsc, pc,
    notQName := notQ.filterMap (fun q =>
      if q.startsWith "##" then none else c.resolve? q),
    notDefined := notQ.contains "##defined",
    notSibling := notQ.contains "##definedSibling" }

/-- The `<schema>` element's own properties as a context. -/
def schemaCtx (loc : String) (root : Node) (tnsOverride : Option String) : Ctx :=
  let c0 : Ctx := { loc }
  let c := c0.enter root
  let tns := tnsOverride.getD ((attrOf "targetNamespace" root).getD "")
  let c := { c with
    tns := tns,
    efdQualified := attrOf "elementFormDefault" root == some "qualified",
    afdQualified := attrOf "attributeFormDefault" root == some "qualified",
    blockDefault := derivKwsOf ((attrOf "blockDefault" root).getD ""),
    finalDefault := derivKwsOf ((attrOf "finalDefault" root).getD ""),
    xpathDefaultNs := "" }
  let c := { c with xpathDefaultNs := c.xdnOf ((attrOf "xpathDefaultNamespace" root).getD "##local") }
  let c := { c with defaultAttrs := (attrOf "defaultAttributes" root).bind c.resolve? }
  let dOpen := (xsKids root).find? (fun k => isXs k "defaultOpenContent")
  let c := match dOpen with
    | some d =>
      let mode := (attrOf "mode" d).bind openModeOf |>.getD .interleave
      let w := (xsKid? d "any").map (readWildcard (c.enter d)) |>.getD {}
      let dop : DefaultOpen := { mode, wild := w, appliesToEmpty := attrOf "appliesToEmpty" d == some "true" }
      { c with defaultOpen := some dop }
    | none => c
  -- A chameleon include (§4.2.3 clause 2.3): unprefixed references to
  -- no-namespace names in the included document are taken as references
  -- to the including document's target namespace.
  match tnsOverride with
  | some t =>
    if (attrOf "targetNamespace" root).isNone && (lookupNs c.bs "").isNone
    then { c with bs := ("", t) :: c.bs } else c
  | none => c

/-- The schema document for the XML namespace (`xml:lang`, `xml:space`,
`xml:base`, `xml:id` and the attribute group `xml:specialAttrs`), as the
W3C publishes it at `http://www.w3.org/2001/xml.xsd`, reduced to its
components. It is used when a schema imports the XML namespace and the
document named by `schemaLocation` is not available (no I/O here). -/
def xmlNsSchemaText : String :=
  "<xs:schema xmlns:xs='http://www.w3.org/2001/XMLSchema' targetNamespace='http://www.w3.org/XML/1998/namespace' xmlns:xml='http://www.w3.org/XML/1998/namespace'>" ++
  "<xs:attribute name='lang'><xs:simpleType><xs:union memberTypes='xs:language'><xs:simpleType><xs:restriction base='xs:string'><xs:enumeration value=''/></xs:restriction></xs:simpleType></xs:union></xs:simpleType></xs:attribute>" ++
  "<xs:attribute name='space'><xs:simpleType><xs:restriction base='xs:NCName'><xs:enumeration value='default'/><xs:enumeration value='preserve'/></xs:restriction></xs:simpleType></xs:attribute>" ++
  "<xs:attribute name='base' type='xs:anyURI'/>" ++
  "<xs:attribute name='id' type='xs:ID'/>" ++
  "<xs:attributeGroup name='specialAttrs'><xs:attribute ref='xml:base'/><xs:attribute ref='xml:lang'/><xs:attribute ref='xml:space'/><xs:attribute ref='xml:id'/></xs:attributeGroup>" ++
  "</xs:schema>"

def xmlNsSchemaLoc : String := "\u0000builtin:xml.xsd"

def xmlNsDoc? : Option LoadedDoc :=
  match parseXML xmlNsSchemaText with
  | .ok d => some { loc := xmlNsSchemaLoc, doc := d }
  | .error _ => none

/-- The locations a schema document names (for the harness's loader). -/
def refsOf (loc : String) (d : Document) : List String :=
  (xsKids (conditionalInclusion d.root)).filterMap (fun k =>
    if isXs k "include" || isXs k "import" || isXs k "redefine" || isXs k "override" then
      (attrOf "schemaLocation" k).map (resolveLoc loc)
    else none)

def findDoc (docs : List LoadedDoc) (loc : String) : Option Document :=
  match (docs.find? (fun d => d.loc == loc)).map (·.doc) with
  | some d => some d
  | none => if loc == xmlNsSchemaLoc then xmlNsDoc?.map (·.doc) else none

/-- Collect the top-level components of one schema document and of the
documents it reaches. `overrides` lists the `(space, name)` pairs that an
enclosing `override` replaces; `redef` carries the renames a `redefine`
asks for (the original of a redefined component gets a hidden name). -/
def collectDoc (docs : List LoadedDoc) : Nat → String → Option String →
    List (String × XName) → List (String × XName × XName) → Collect → Collect
  | 0, loc, _, _, _, st => { st with errors := s!"include depth exceeded at {loc}" :: st.errors }
  | f + 1, loc, tnsOverride, overrides, redef, st =>
    let key := (loc, tnsOverride.getD "\u0000")
    if st.seen.contains key then st
    else
    match findDoc docs loc with
    | none => st
    | some d =>
      let root := conditionalInclusion d.root
      if !isXs root "schema" then
        { st with errors := s!"{loc}: document element is not xs:schema" :: st.errors }
      else
      let ctx := schemaCtx loc root tnsOverride
      let st := { st with seen := key :: st.seen }
      (xsKids root).foldl (fun st k =>
        let kc := ctx.enter k
        let tag := localOf (tagOf k)
        if tag == "include" then
          match attrOf "schemaLocation" k with
          | some sl =>
            let l := resolveLoc loc sl
            match findDoc docs l with
            | some inc =>
              let itns := attrOf "targetNamespace" (conditionalInclusion inc.root)
              if itns.isSome && itns != some ctx.tns then
                { st with errors := s!"{loc}: included {l} has a different targetNamespace" :: st.errors }
              else collectDoc docs f l (if itns.isNone then some ctx.tns else none) overrides redef st
            | none => st
          | none => { st with errors := s!"{loc}: include without schemaLocation" :: st.errors }
        else if tag == "import" then
          let ins := attrOf "namespace" k
          if ins == some ctx.tns || (ins.isNone && ctx.tns == "") then
            { st with errors := s!"{loc}: import of its own target namespace" :: st.errors }
          else
          let sl? := match attrOf "schemaLocation" k with
            | some sl => if (findDoc docs (resolveLoc loc sl)).isNone && ins == some xmlNS then some xmlNsSchemaLoc else some sl
            | none => if ins == some xmlNS then some xmlNsSchemaLoc else none
          match sl? with
          | some sl =>
            let l := if sl == xmlNsSchemaLoc then sl else resolveLoc loc sl
            match findDoc docs l with
            | some imp =>
              let itns := (attrOf "targetNamespace" (conditionalInclusion imp.root)).getD ""
              if itns != ins.getD "" then
                { st with errors := s!"{loc}: imported {l} has targetNamespace {itns}" :: st.errors }
              else collectDoc docs f l none [] [] st
            | none => st
          | none => st
        else if tag == "redefine" || tag == "override" then
          match attrOf "schemaLocation" k with
          | none => { st with errors := s!"{loc}: {tag} without schemaLocation" :: st.errors }
          | some sl =>
            let l := resolveLoc loc sl
            let members := (xsKids k).filterMap (fun m =>
              match TopKind.ofTag (localOf (tagOf m)), attrOf "name" m with
              | some tk, some nm => some (tk, ⟨ctx.tns, nm⟩, m)
              | _, _ => none)
            match findDoc docs l with
            | none =>
              if tag == "redefine" && !members.isEmpty then
                { st with errors := s!"{loc}: redefined document {l} not found" :: st.errors }
              else
                -- §4.2.5: an override whose target is missing still
                -- contributes its own components.
                members.foldl (fun st (tk, nm, m) =>
                  { st with tops := st.tops.push { kind := tk, name := nm, node := m, ctx := kc.enter m } }) st
            | some rd =>
              let rtns := attrOf "targetNamespace" (conditionalInclusion rd.root)
              if rtns.isSome && rtns != some ctx.tns then
                { st with errors := s!"{loc}: {tag} target {l} has a different targetNamespace" :: st.errors }
              else
              let tnsO := if rtns.isNone then some ctx.tns else none
              if tag == "override" then
                let ovs := members.map (fun (tk, nm, _) => (tk.space, nm))
                let st := collectDoc docs f l tnsO (ovs ++ overrides) redef st
                members.foldl (fun st (tk, nm, m) =>
                  if overrides.contains (tk.space, nm) then st
                  else { st with tops := st.tops.push { kind := tk, name := nm, node := m, ctx := kc.enter m } }) st
              else
                -- redefine: rename the originals, then add the redefinitions
                -- whose self-reference resolves to the renamed original.
                let rn := members.map (fun (tk, nm, _) =>
                  (tk.space, nm, ({ nm with loc := nm.loc ++ "\u0000redefined" } : XName)))
                let st := collectDoc docs f l tnsO overrides (rn ++ redef) st
                members.foldl (fun st (tk, nm, m) =>
                  if tk == .simpleType || tk == .complexType || tk == .group || tk == .attributeGroup then
                    let mc := kc.enter m
                    let top : Top := { kind := tk, name := nm, node := m, ctx := { mc with renames := rn.filter (fun r => r.2.1 == nm) ++ mc.renames } }
                    { st with tops := st.tops.push top }
                  else { st with errors := s!"{loc}: {localOf (tagOf m)} not allowed in redefine" :: st.errors }) st
        else
          match TopKind.ofTag tag with
          | some tk =>
            match attrOf "name" k with
            | some nm =>
              let xn : XName := ⟨ctx.tns, nm⟩
              if overrides.contains (tk.space, xn) then st
              else
                let xn := match redef.find? (fun r => r.1 == tk.space && r.2.1 == xn) with
                  | some r => r.2.2
                  | none => xn
                { st with tops := st.tops.push { kind := tk, name := xn, node := k, ctx := kc } }
            | none => { st with errors := s!"{loc}: top-level {tag} without a name" :: st.errors }
          | none =>
            if tag == "defaultOpenContent" || tag == "annotation" then st
            else { st with errors := s!"{loc}: unexpected top-level element {tag}" :: st.errors }) st

/-! ## Passes 2 and 3: build the components -/

structure RS where
  sch : Schema
  tops : Array Top
  /-- Group and attribute-group references being expanded (circularity). -/
  visiting : List (String × XName) := []
deriving Inhabited

abbrev RM := StateM RS

def addErr (e : String) : RM Unit :=
  modify (fun s => { s with sch := { s.sch with errors := e :: s.sch.errors } })

def addUnsupported (e : String) : RM Unit :=
  modify (fun s => { s with sch := { s.sch with unsupported := e :: s.sch.unsupported } })

def pushType (t : TypeDef) : RM Nat := do
  let s ← get
  set { s with sch := { s.sch with types := s.sch.types.push t } }
  pure s.sch.types.size

def setType (i : Nat) (t : TypeDef) : RM Unit :=
  modify (fun s => { s with sch := { s.sch with types := s.sch.types.set! i t } })

def pushElem (e : ElemDecl) : RM Nat := do
  let s ← get
  set { s with sch := { s.sch with elems := s.sch.elems.push e } }
  pure s.sch.elems.size

def setElem (i : Nat) (e : ElemDecl) : RM Unit :=
  modify (fun s => { s with sch := { s.sch with elems := s.sch.elems.set! i e } })

def pushAttr (a : AttrDecl) : RM Nat := do
  let s ← get
  set { s with sch := { s.sch with attrs := s.sch.attrs.push a } }
  pure s.sch.attrs.size

def setAttr (i : Nat) (a : AttrDecl) : RM Unit :=
  modify (fun s => { s with sch := { s.sch with attrs := s.sch.attrs.set! i a } })

def pushIdc (d : IDC) : RM Nat := do
  let s ← get
  set { s with sch := { s.sch with idcs := s.sch.idcs.push d } }
  pure s.sch.idcs.size

def findTop (kind : TopKind → Bool) (n : XName) : RM (Option Top) := do
  let s ← get
  pure (s.tops.find? (fun t => kind t.kind && t.name == n))

/-- Resolve a type reference (`type`, `base`, `itemType`, `memberTypes`
entry). `xs:anyAtomicType` may not be named in a schema document
(Part 2 §3.2.2). -/
def typeRef (c : Ctx) (qn : String) : RM Nat := do
  match c.resolve? qn with
  | none => addErr s!"cannot resolve type QName {qn}"; pure anyTypeIdx
  | some n =>
    let n := c.renamed "type" n
    match (← get).sch.typeIdx? n with
    | some i => pure i
    | none => addErr s!"unresolved type {n.show}"; pure anyTypeIdx

def occursOf (n : Node) : RM (Nat × Option Nat) := do
  let mn ← match attrOf "minOccurs" n with
    | none => pure 1
    | some v => match natOfString? (XSD.applyWhiteSpace .collapse v) with
      | some k => pure k
      | none => addErr s!"bad minOccurs {v}"; pure 1
  let mx ← match attrOf "maxOccurs" n with
    | none => pure (some 1)
    | some v =>
      let v := XSD.applyWhiteSpace .collapse v
      if v == "unbounded" then pure none
      else match natOfString? v with
        | some k => pure (some k)
        | none => addErr s!"bad maxOccurs {v}"; pure (some 1)
  match mx with
  | some k => if k < mn then addErr s!"maxOccurs {k} < minOccurs {mn}"
  | none => pure ()
  pure (mn, mx)

def vcOf (n : Node) : RM (Option ValueConstraint) := do
  match attrOf "default" n, attrOf "fixed" n with
  | some _, some _ => addErr "both default and fixed"; pure none
  | some d, none => pure (some { kind := .default, lex := d })
  | none, some f => pure (some { kind := .fixed, lex := f })
  | none, none => pure none

def assertsOf (c : Ctx) (tag : String) (n : Node) : List Assertion :=
  ((xsKids n).filter (fun k => isXs k tag)).filterMap (fun k =>
    let kc := c.enter k
    (attrOf "test" k).map (fun t =>
      { test := t, ns := kc.bs,
        xpathDefaultNs := ((attrOf "xpathDefaultNamespace" k).map (c.enter k).xdnOf).getD c.xpathDefaultNs,
        baseUri := c.loc }))

/-- The facets of a `restriction` step, and the names of those declared
`fixed`. -/
def facetsOf (n : Node) : Facets × List String :=
  let kids := xsKids n
  let f := facetsOfRestriction kids
  let fixedNames := (kids.filter (fun k => attrOf "fixed" k == some "true")).map (fun k => localOf (tagOf k))
  (f, fixedNames)

def facetTags : List String :=
  ["length", "minLength", "maxLength", "pattern", "enumeration", "whiteSpace",
   "maxInclusive", "maxExclusive", "minInclusive", "minExclusive",
   "totalDigits", "fractionDigits", "assertion", "explicitTimezone"]

/-- §3.10.2 Schema Representation Constraints on `any` / `anyAttribute`:
the `##` keywords allowed in `namespace`, `notNamespace` and `notQName`,
and `namespace` with `notNamespace` not both given. -/
def wildReprErrors (n : Node) : List String :=
  let ns := (attrOf "namespace" n).map XSD.qnameList |>.getD []
  let nn := (attrOf "notNamespace" n).map XSD.qnameList |>.getD []
  let nq := (attrOf "notQName" n).map XSD.qnameList |>.getD []
  let badKw (allowed : List String) (l : List String) :=
    l.filter (fun t => t.startsWith "##" && !allowed.contains t)
  (if (attrOf "namespace" n).isSome && (attrOf "notNamespace" n).isSome then ["wildcard with both namespace and notNamespace"] else []) ++
  (badKw ["##any", "##other", "##targetNamespace", "##local"] ns).map (fun t => s!"wildcard namespace {t} is not allowed") ++
  (if (ns.contains "##any" || ns.contains "##other") && ns.length > 1 then ["##any or ##other with other namespaces"] else []) ++
  (badKw ["##targetNamespace", "##local"] nn).map (fun t => s!"wildcard notNamespace {t} is not allowed") ++
  (badKw ["##defined", "##definedSibling"] nq).map (fun t => s!"wildcard notQName {t} is not allowed")

/-- §3.10.6.4 (attribute) wildcard intersection, for the namespace
constraints; the other properties come from the first. -/
def wildIntersect (a b : Wildcard) : Wildcard :=
  let ns := match a.ns, b.ns with
    | .any, x => x
    | x, .any => x
    | .enum l, .enum m => .enum (l.filter m.contains)
    | .enum l, .not m => .enum (l.filter (fun x => !m.contains x))
    | .not m, .enum l => .enum (l.filter (fun x => !m.contains x))
    | .not l, .not m => .not (l ++ m).eraseDups
  { a with ns, notQName := (a.notQName ++ b.notQName).eraseDups,
           notDefined := a.notDefined || b.notDefined }

def wildUnion (a b : Wildcard) : Wildcard :=
  let ns := match a.ns, b.ns with
    | .any, _ => .any
    | _, .any => .any
    | .enum l, .enum m => .enum (l ++ m).eraseDups
    | .enum l, .not m => .not (m.filter (fun x => !l.contains x))
    | .not m, .enum l => .not (m.filter (fun x => !l.contains x))
    | .not l, .not m => if (l.filter m.contains).isEmpty then .any else .not (l.filter m.contains)
  { a with ns, notQName := a.notQName.filter b.notQName.contains }

/-- §3.4.2.5: the local attribute wildcard and the default attribute
group's, combined (union, §3.10.6.3). -/
def wildUnionOpt (a b : Option Wildcard) : Option Wildcard :=
  match a, b with
  | none, x => x
  | x, none => x
  | some x, some y => some (wildUnion x y)

/-- §3.4.2.3.3 the explicit content: empty when there is no particle or
the particle is an empty `all`/`sequence` (or an empty `choice` with
minOccurs 0, or maxOccurs 0); then `mixed` decides between empty content
and mixed content with an empty sequence. -/
def explicitContent (p : Option Particle) (mixed : Bool) : ContentType :=
  let isEmpty : Bool := match p with
    | none => true
    | some (.group _ mx c ps) =>
      mx == some 0 || (ps.isEmpty && (c == .seq || c == .all)) ||
      (ps.isEmpty && c == .choice && (p.map (·.minOcc)) == some 0)
    | some q => q.maxOcc == some 0
  if isEmpty then
    if mixed then .elems Particle.emptySeq true else .empty
  else .elems p.get! mixed

/-- §3.4.2.3.3: the open content of a complex type: its own
`openContent`, else the schema's `defaultOpenContent`. -/
def openContentOf (c : Ctx) (n : Node) : RM (Option (OpenMode × Wildcard)) := do
  match xsKid? n "openContent" with
  | some oc =>
    let mode := (attrOf "mode" oc).getD "interleave"
    if mode == "none" then pure none
    else
      let w := (xsKid? oc "any").map (readWildcard (c.enter oc)) |>.getD {}
      pure ((openModeOf mode).map (fun m => (m, w)))
  | none =>
    match c.defaultOpen with
    | some d => pure (some (d.mode, d.wild))
    | none => pure none

mutual

/-- §3.16.2 a `simpleType` element (named or anonymous). -/
def readSimpleType (fuel : Nat) (c : Ctx) (n : Node) (name : Option XName) : RM SimpleDef := do
  match fuel with
  | 0 => addErr "simple type nesting too deep"; pure default
  | f + 1 =>
  let c := c.enter n
  let final := match attrOf "final" n with
    | some v => derivKwsOf v
    | none => c.finalDefault.filter (fun k => k != .extension && k != .substitution)
  let body? := (xsKids n).find? (fun k => isXs k "restriction" || isXs k "list" || isXs k "union")
  match body? with
  | none => addErr "simpleType without restriction, list or union"; pure { name, base := anySimpleTypeIdx, variety := .atomic, final }
  | some b =>
    let bc := c.enter b
    if isXs b "restriction" then
      let inline := xsKid? b "simpleType"
      let baseIdx ← match attrOf "base" b, inline with
        | some q, none => typeRef bc q
        | none, some st => do
            let sd ← readSimpleType f bc st none
            pushType (.simple sd)
        | some _, some _ => do addErr "restriction with both base and simpleType"; pure anySimpleTypeIdx
        | none, none => do addErr "restriction without base"; pure anySimpleTypeIdx
      let (facets, fixedFacets) := facetsOf b
      let unknown := (xsKids b).filter (fun k => !(facetTags.contains (localOf (tagOf k))) && !isXs k "simpleType")
      if !unknown.isEmpty then addErr s!"unexpected {localOf (tagOf unknown.head!)} in simple restriction"
      let bt := (← get).sch.type baseIdx
      let (variety, item, members, builtin) := match bt with
        | .simple sd => (sd.variety, sd.item, sd.members, sd.builtin)
        | .complex _ => (Variety.atomic, none, [], none)
      if !bt.isSimple then addErr "simple type restricts a complex type"
      if baseIdx == anySimpleTypeIdx then addErr "simple type may not restrict xs:anySimpleType directly"
      if baseIdx == builtinIdx .anyAtomicType then addErr "simple type may not restrict xs:anyAtomicType (Part 2 §3.2.2)"
      -- §4.3: a facet other than pattern, enumeration and assertion appears at most once
      let fnames := (xsKids b).filterMap (fun k =>
        let l := localOf (tagOf k)
        if facetTags.contains l && l != "pattern" && l != "enumeration" && l != "assertion" then some l else none)
      if fnames.length != fnames.eraseDups.length then addErr "a facet is given twice in one restriction"
      pure { name, base := baseIdx, variety, item, members, builtin, facets, fixedFacets, final,
             asserts := assertsOf bc "assertion" b }
    else if isXs b "list" then
      let inline := xsKid? b "simpleType"
      let itemIdx ← match attrOf "itemType" b, inline with
        | some q, none => typeRef bc q
        | none, some st => do
            let sd ← readSimpleType f bc st none
            pushType (.simple sd)
        | _, _ => do addErr "list needs exactly one of itemType and simpleType"; pure anySimpleTypeIdx
      pure { name, base := anySimpleTypeIdx, variety := .list, item := some itemIdx, final }
    else
      let named := (XSD.qnameList ((attrOf "memberTypes" b).getD ""))
      let mutual_ ← named.mapM (typeRef bc)
      let inl := (xsKids b).filter (fun k => isXs k "simpleType")
      let inlIdx ← inl.mapM (fun st => do
        let sd ← readSimpleType f bc st none
        pushType (.simple sd))
      let ms := mutual_ ++ inlIdx
      if ms.isEmpty then addErr "union with no member types"
      pure { name, base := anySimpleTypeIdx, variety := .union, members := ms, final }

/-- §3.10.2 / §3.8.2 / §3.9.2: a particle element (`element`, `group`
reference, `sequence`, `choice`, `all`, `any`). -/
def readParticle (fuel : Nat) (c : Ctx) (n : Node) : RM (Option Particle) := do
  match fuel with
  | 0 => addErr "particle nesting too deep"; pure none
  | f + 1 =>
  let c := c.enter n
  let (mn, mx) ← occursOf n
  let tag := localOf (tagOf n)
  if tag == "element" then
    match attrOf "ref" n with
    | some r =>
      match c.resolve? r with
      | none => addErr s!"cannot resolve element ref {r}"; pure none
      | some rn =>
        match (← get).sch.elemIdx? rn with
        | some i =>
          if (attrOf "name" n).isSome || (attrOf "type" n).isSome then addErr "element ref with name or type"
          pure (some (.elem mn mx i))
        | none => addErr s!"unresolved element {rn.show}"; pure none
    | none =>
      let i ← readElement f c n false
      pure (some (.elem mn mx i))
  else if tag == "any" then
    wildReprErrors n |>.forM addErr
    pure (some (.wild mn mx (readWildcard c n)))
  else if tag == "group" then
    match attrOf "ref" n with
    | none => addErr "local group without ref"; pure none
    | some r =>
      match c.resolve? r with
      | none => addErr s!"cannot resolve group ref {r}"; pure none
      | some gn =>
        let gn := c.renamed "group" gn
        if (← get).visiting.contains ("group", gn) then
          addErr s!"circular group {gn.show}"; pure none
        else
        match ← findTop (· == .group) gn with
        | none => addErr s!"unresolved group {gn.show}"; pure none
        | some t =>
          match (xsKids t.node).find? (fun k => isXs k "sequence" || isXs k "choice" || isXs k "all") with
          | none => addErr s!"group {gn.show} has no model group"; pure none
          | some mg =>
            modify (fun s => { s with visiting := ("group", gn) :: s.visiting })
            let gctx := t.ctx.enter t.node
            let p ← readParticle f gctx mg
            modify (fun s => { s with visiting := s.visiting.erase ("group", gn) })
            if (attrOf "minOccurs" mg).isSome || (attrOf "maxOccurs" mg).isSome then
              addErr "model group in a named group may not carry minOccurs or maxOccurs"
            pure (p.map (·.withOcc mn mx))
  else if tag == "sequence" || tag == "choice" || tag == "all" then
    let comp := if tag == "sequence" then Compositor.seq else if tag == "choice" then .choice else .all
    let kids := xsKids n
    let mut ps : Array Particle := #[]
    for k in kids do
      let kt := localOf (tagOf k)
      if comp == .all && !(kt == "element" || kt == "any" || kt == "group") then
        addErr s!"{kt} not allowed in xs:all"
      else if !(kt == "element" || kt == "any" || kt == "group" || kt == "sequence" || kt == "choice") then
        addErr s!"{kt} not allowed in a model group"
      else
        match ← readParticle f c k with
        | some p => ps := ps.push p
        | none => pure ()
    if comp == .all then
      if mx != some 1 && mx != some 0 then addErr "xs:all with maxOccurs other than 0 or 1"
      if mn > 1 then addErr "xs:all with minOccurs greater than 1"
    pure (some (.group mn mx comp ps.toList))
  else
    addErr s!"unexpected particle {tag}"; pure none

/-- §3.3.2 an `element` element: a top-level declaration (index already
assigned) or a local one (appended). Returns the declaration's index. -/
def readElement (fuel : Nat) (c : Ctx) (n : Node) (global : Bool) (gIdx : Option Nat := none) : RM Nat := do
  match fuel with
  | 0 => addErr "element nesting too deep"; pure 0
  | f + 1 =>
  let c := c.enter n
  let nm := (attrOf "name" n).getD ""
  if nm == "" then addErr "element declaration without a name"
  let qualified :=
    match attrOf "form" n with
    | some "qualified" => true
    | some "unqualified" => false
    | _ => c.efdQualified
  if !global && (attrOf "form" n).isSome && (attrOf "targetNamespace" n).isSome then
    addErr "element with both form and targetNamespace"
  let ns := if global then c.tns
    else match attrOf "targetNamespace" n with
      | some t => t
      | none => if qualified then c.tns else ""
  let xn : XName := ⟨ns, nm⟩
  let inlineS := xsKid? n "simpleType"
  let inlineC := xsKid? n "complexType"
  let sgs := ((XSD.qnameList ((attrOf "substitutionGroup" n).getD "")).filterMap c.resolve?)
  if !global && (attrOf "substitutionGroup" n).isSome then addErr "local element with substitutionGroup"
  if !global && ((attrOf "abstract" n).isSome || (attrOf "final" n).isSome) then
    addErr "local element with abstract or final"
  let (typ, fromHead) ← match attrOf "type" n, inlineS, inlineC with
    | some q, none, none => do pure ((← typeRef c q), false)
    | none, some st, none => do
        let sd ← readSimpleType f c st none
        pure ((← pushType (.simple sd)), false)
    | none, none, some ct => do
        let cd ← readComplexType f c ct none
        pure ((← pushType (.complex cd)), false)
    | none, none, none => pure (anyTypeIdx, !sgs.isEmpty)
    | _, _, _ => do addErr s!"element {nm} has more than one type"; pure (anyTypeIdx, false)
  let vc ← vcOf n
  let block := match attrOf "block" n with
    | some v => derivKwsOf v
    | none => c.blockDefault.filter (fun k => k == .extension || k == .restriction || k == .substitution)
  let final := match attrOf "final" n with
    | some v => derivKwsOf v
    | none => c.finalDefault.filter (fun k => k == .extension || k == .restriction)
  -- Placeholder index, so the identity constraints can be read after.
  let decl : ElemDecl := {
    name := xn, typ, nillable := attrOf "nillable" n == some "true",
    vc, abstract := attrOf "abstract" n == some "true", substGroups := sgs, block, final,
    global, typeFromHead := fromHead }
  let idx ← match gIdx with
    | some i => do setElem i decl; pure i
    | none => pushElem decl
  -- identity constraints
  let idcNodes := (xsKids n).filter (fun k => isXs k "unique" || isXs k "key" || isXs k "keyref")
  let mut idcIdx : Array Nat := #[]
  for k in idcNodes do
    let kc := c.enter k
    let kind := if isXs k "unique" then IdcKind.unique else if isXs k "key" then .key else .keyref
    match attrOf "ref" k with
    | some r =>
      -- §3.11.2 (1.1): a reference to an identity constraint defined elsewhere.
      match kc.resolve? r with
      | some rn =>
        match (← get).sch.gIdcs.lookup rn with
        | some j => idcIdx := idcIdx.push j
        | none =>
          -- resolved after all elements are read
          let j ← pushIdc { name := rn, kind, selector := "\u0000ref", fields := [] }
          idcIdx := idcIdx.push j
      | none => addErr s!"cannot resolve identity constraint ref {r}"
    | none =>
    let iname : XName := ⟨c.tns, (attrOf "name" k).getD ""⟩
    let sel := ((xsKid? k "selector").bind (attrOf "xpath")).getD ""
    let fields := ((xsKids k).filter (fun x => isXs x "field")).map (fun x => (attrOf "xpath" x).getD "")
    if (xsKid? k "selector").isNone || fields.isEmpty then addErr s!"identity constraint {iname.show} needs a selector and a field"
    let xdn := ((attrOf "xpathDefaultNamespace" k).map (c.enter k).xdnOf).getD c.xpathDefaultNs
    let refer := if kind == .keyref then (attrOf "refer" k).bind kc.resolve? else none
    if kind == .keyref && refer.isNone then addErr "keyref without refer"
    if (← get).sch.gIdcs.lookup iname |>.isSome then addErr s!"duplicate identity constraint {iname.show}"
    let j ← pushIdc { name := iname, kind, selector := sel, fields, refer, ns := kc.bs, xpathDefaultNs := xdn }
    modify (fun s => { s with sch := { s.sch with gIdcs := (iname, j) :: s.sch.gIdcs } })
    idcIdx := idcIdx.push j
  -- type alternatives (§3.12.2)
  let altNodes := (xsKids n).filter (fun k => isXs k "alternative")
  let mut alts : Array TypeAlt := #[]
  for k in altNodes do
    let kc := c.enter k
    let ty ← match attrOf "type" k, xsKid? k "simpleType", xsKid? k "complexType" with
      | some q, none, none => typeRef kc q
      | none, some st, none => do
          let sd ← readSimpleType f kc st none
          pushType (.simple sd)
      | none, none, some ct => do
          let cd ← readComplexType f kc ct none
          pushType (.complex cd)
      | none, none, none => do addErr "alternative without a type"; pure anyTypeIdx
      | _, _, _ => do addErr "alternative with more than one type"; pure anyTypeIdx
    alts := alts.push { test := attrOf "test" k, typ := ty, ns := kc.bs,
                        xpathDefaultNs := ((attrOf "xpathDefaultNamespace" k).map (c.enter k).xdnOf).getD c.xpathDefaultNs }
  let decl := { decl with idcs := idcIdx.toList, alts := alts.toList }
  setElem idx decl
  pure idx

/-- §3.2.2 an `attribute` element inside a type or attribute group: the
attribute use, or `none` for a prohibited one (whose name is returned
in the second component). -/
def readAttrUse (fuel : Nat) (c : Ctx) (n : Node) : RM (Option AttrUse × Option XName) := do
  match fuel with
  | 0 => addErr "attribute nesting too deep"; pure (none, none)
  | f + 1 =>
  let c := c.enter n
  let use := (attrOf "use" n).getD "optional"
  let vc ← vcOf n
  if use == "required" && (vc.map (·.kind)) == some .default then addErr "required attribute with a default"
  if use == "prohibited" && (vc.map (·.kind)) == some .default then addErr "prohibited attribute with a default"
  let inh := (attrOf "inheritable" n).map (· == "true")
  match attrOf "ref" n with
  | some r =>
    match c.resolve? r with
    | none => addErr s!"cannot resolve attribute ref {r}"; pure (none, none)
    | some rn =>
      match (← get).sch.attrIdx? rn with
      | none => addErr s!"unresolved attribute {rn.show}"; pure (none, none)
      | some i =>
        if (attrOf "type" n).isSome || (xsKid? n "simpleType").isSome || (attrOf "form" n).isSome then
          addErr "attribute ref with type or form"
        if use == "prohibited" then pure (none, some rn)
        else
          let d := (← get).sch.attr i
          pure (some { decl := i, required := use == "required", vc,
                       inheritable := inh.getD d.inheritable }, none)
  | none =>
    let nm := (attrOf "name" n).getD ""
    if nm == "" then addErr "attribute without a name"
    if nm == "xmlns" then addErr "attribute named xmlns"
    let qualified := match attrOf "form" n with
      | some "qualified" => true
      | some "unqualified" => false
      | _ => c.afdQualified
    let ns := match attrOf "targetNamespace" n with
      | some t => t
      | none => if qualified then c.tns else ""
    if ns == xsiNS then addErr "attribute in the xsi namespace"
    let typ ← match attrOf "type" n, xsKid? n "simpleType" with
      | some q, none => typeRef c q
      | none, some st => do
          let sd ← readSimpleType f c st none
          pushType (.simple sd)
      | none, none => pure anySimpleTypeIdx
      | some _, some _ => do addErr "attribute with both type and simpleType"; pure anySimpleTypeIdx
    let i ← pushAttr { name := ⟨ns, nm⟩, typ, vc := none, inheritable := inh.getD false }
    if use == "prohibited" then pure (none, some ⟨ns, nm⟩)
    else pure (some { decl := i, required := use == "required", vc, inheritable := inh.getD false }, none)

/-- The attribute uses, prohibited names, attribute wildcard and
attribute-group references of a sequence of attribute children (a type
definition or an attribute group). -/
def readAttrs (fuel : Nat) (c : Ctx) (kids : List Node)
    : RM (List AttrUse × List XName × Option Wildcard) := do
  match fuel with
  | 0 => addErr "attribute group nesting too deep"; pure ([], [], none)
  | f + 1 =>
  let mut uses : Array AttrUse := #[]
  let mut prohib : Array XName := #[]
  let mut wild : Option Wildcard := none
  let mut groupWilds : Array Wildcard := #[]
  for k in kids do
    if isXs k "attribute" then
      let (u, p) ← readAttrUse f c k
      if let some u := u then uses := uses.push u
      if let some p := p then prohib := prohib.push p
    else if isXs k "attributeGroup" then
      match attrOf "ref" k with
      | none => addErr "local attributeGroup without ref"
      | some r =>
        match (c.enter k).resolve? r with
        | none => addErr s!"cannot resolve attributeGroup ref {r}"
        | some gn =>
          let gn := c.renamed "attributeGroup" gn
          if (← get).visiting.contains ("attributeGroup", gn) then
            addErr s!"circular attribute group {gn.show}"
          else
          match ← findTop (· == .attributeGroup) gn with
          | none => addErr s!"unresolved attributeGroup {gn.show}"
          | some t =>
            modify (fun s => { s with visiting := ("attributeGroup", gn) :: s.visiting })
            let (us, ps, w) ← readAttrs f (t.ctx.enter t.node) (xsKids t.node)
            modify (fun s => { s with visiting := s.visiting.erase ("attributeGroup", gn) })
            uses := uses ++ us.toArray
            prohib := prohib ++ ps.toArray
            if let some w := w then groupWilds := groupWilds.push w
    else if isXs k "anyAttribute" then
      if wild.isSome then addErr "more than one anyAttribute"
      wildReprErrors k |>.forM addErr
      wild := some (readWildcard (c.enter k) k)
    else if isXs k "assert" || isXs k "openContent" then
      pure ()
  -- §3.6.2.2: the wildcard is the intersection of the local one and the
  -- attribute groups' ones.
  let w := groupWilds.foldl (fun acc g =>
    match acc with
    | none => some g
    | some a => some (wildIntersect a g)) wild
  pure (uses.toList, prohib.toList, w)

/-- §3.4.2 a `complexType` element (named or anonymous). The content and
attribute uses recorded here are the LOCAL ones; `finishComplex` adds
what the base type contributes. -/
def readComplexType (fuel : Nat) (c : Ctx) (n : Node) (name : Option XName) : RM ComplexDef := do
  match fuel with
  | 0 => addErr "complex type nesting too deep"; pure { name, base := anyTypeIdx }
  | f + 1 =>
  let c := c.enter n
  let block := match attrOf "block" n with
    | some v => derivKwsOf v
    | none => c.blockDefault.filter (fun k => k == .extension || k == .restriction)
  let final := match attrOf "final" n with
    | some v => derivKwsOf v
    | none => c.finalDefault.filter (fun k => k == .extension || k == .restriction)
  let abstract := attrOf "abstract" n == some "true"
  let kids := xsKids n
  let applyDefaultAttrs := attrOf "defaultAttributesApply" n != some "false"
  let defaultUses ← match c.defaultAttrs, applyDefaultAttrs with
    | some ga, true => do
      match ← findTop (· == .attributeGroup) ga with
      | some t => readAttrs f (t.ctx.enter t.node) (xsKids t.node)
      | none => addErr s!"unresolved defaultAttributes {ga.show}"; pure ([], [], none)
    | _, _ => pure ([], [], none)
  let base : ComplexDef := { name, base := anyTypeIdx, abstract, block, final }
  match kids.find? (fun k => isXs k "simpleContent" || isXs k "complexContent") with
  | some sc =>
    let scc := c.enter sc
    let mixedCC := match attrOf "mixed" sc with
      | some v => some (v == "true")
      | none => none
    match (xsKids sc).find? (fun k => isXs k "restriction" || isXs k "extension") with
    | none => addErr "simpleContent/complexContent without restriction or extension"; pure base
    | some d =>
      let dc := scc.enter d
      let baseIdx ← match attrOf "base" d with
        | some q => typeRef dc q
        | none => do addErr "derivation without base"; pure anyTypeIdx
      let deriv := if isXs d "extension" then Deriv.extension else .restriction
      let dk := xsKids d
      let attrKids := dk.filter (fun k => isXs k "attribute" || isXs k "attributeGroup" || isXs k "anyAttribute")
      let (uses, prohib, wild) ← readAttrs f dc attrKids
      let (du, dp, dw) := defaultUses
      let asserts := assertsOf dc "assert" d
      if isXs sc "simpleContent" then
        -- §3.4.2.2: simple content
        let content ← if deriv == .restriction then do
            let inline := xsKid? d "simpleType"
            let baseContent : Nat := match (← get).sch.type baseIdx with
              | .complex bc => match bc.content with
                | .simple st => st
                | .elems _ true => anySimpleTypeIdx
                | _ => anySimpleTypeIdx
              | .simple _ => baseIdx
            let stBase ← match inline with
              | some st => do
                  let sd ← readSimpleType f dc st none
                  pushType (.simple sd)
              | none => pure baseContent
            let (facets, fixedFacets) := facetsOf d
            let hasFacets := (dk.any (fun k => facetTags.contains (localOf (tagOf k)))) || inline.isSome
            if hasFacets then
              let bt := (← get).sch.type stBase
              let (variety, item, members, builtin) := match bt with
                | .simple sd => (sd.variety, sd.item, sd.members, sd.builtin)
                | .complex _ => (Variety.atomic, none, [], none)
              let i ← pushType (.simple { name := none, base := stBase, variety, item, members, builtin,
                                          facets, fixedFacets, asserts := assertsOf dc "assertion" d })
              pure (ContentType.simple i)
            else pure (ContentType.simple stBase)
          else do
            match (← get).sch.type baseIdx with
            | .simple _ => pure (ContentType.simple baseIdx)
            | .complex bc => match bc.content with
              | .simple st => pure (ContentType.simple st)
              | _ => pure (ContentType.simple anySimpleTypeIdx)
        pure { base with base := baseIdx, deriv, content, attrUses := uses ++ du,
                         prohibited := prohib ++ dp,
                         attrWild := wildUnionOpt wild dw, asserts,
                         openContent := none }
      else
        -- §3.4.2.3: complex content
        let mixed := mixedCC.getD (attrOf "mixed" n == some "true")
        let pnode := dk.find? (fun k => isXs k "sequence" || isXs k "choice" || isXs k "all" || isXs k "group")
        let p ← match pnode with
          | some pn => readParticle f dc pn
          | none => pure none
        let oc ← openContentOf dc d
        pure { base with base := baseIdx, deriv, prohibited := prohib ++ dp,
                         content := explicitContent p mixed,
                         attrUses := uses ++ du, attrWild := wildUnionOpt wild dw, asserts,
                         openContent := oc }
  | none =>
    -- §3.4.2.3.3 shorthand: a restriction of xs:anyType
    let mixed := attrOf "mixed" n == some "true"
    let pnode := kids.find? (fun k => isXs k "sequence" || isXs k "choice" || isXs k "all" || isXs k "group")
    let p ← match pnode with
      | some pn => readParticle f c pn
      | none => pure none
    let attrKids := kids.filter (fun k => isXs k "attribute" || isXs k "attributeGroup" || isXs k "anyAttribute")
    let (uses, _, wild) ← readAttrs f c attrKids
    let (du, _, dw) := defaultUses
    let oc ← openContentOf c n
    pure { base with base := anyTypeIdx, deriv := .restriction,
                     content := explicitContent p mixed,
                     attrUses := uses ++ du, attrWild := wildUnionOpt wild dw,
                     asserts := assertsOf c "assert" n, openContent := oc }


end

/-! ## Pass 4: finish -/

/-- The Part 2 type of a simple type definition, built along its base
chain (the same construction as `XSD.readSimpleType`). -/
def bodyOf (s : Schema) : Nat → Nat → SimpleType
  | 0, _ => .atomic .anySimpleType {}
  | f + 1, i =>
    match s.type i with
    | .complex _ => .atomic .anySimpleType {}
    | .simple sd => if i ≤ errorTypeIdx then sd.body else go f sd
where
  go (f : Nat) (sd : SimpleDef) : SimpleType :=
    match sd.variety, sd.item with
    | .list, some it =>
      if sd.base == anySimpleTypeIdx then .list (bodyOf s f it) {}
      else match bodyOf s f sd.base with
        | .list itb bf => .list itb (Facets.merge bf sd.facets)
        | other => other
    | .union, _ =>
      if sd.base == anySimpleTypeIdx then .union (sd.members.map (bodyOf s f)) {}
      else match bodyOf s f sd.base with
        | .union ms bf => .union ms (Facets.merge bf sd.facets)
        | other => other
    | _, _ =>
      match bodyOf s f sd.base with
      | .atomic b bf => .atomic b (Facets.merge bf sd.facets)
      | .list it bf => .list it (Facets.merge bf sd.facets)
      | .union ms bf => .union ms (Facets.merge bf sd.facets)

/-- The variety, item and members of a simple type, inherited along the
restriction chain (pass 3 reads them from a base that may not be built
yet). -/
def inheritVariety (s : Schema) : Nat → Nat → (Variety × Option Nat × List Nat × Option XSD.Builtin)
  | 0, _ => (.atomic, none, [], none)
  | f + 1, i =>
    match s.type i with
    | .complex _ => (.atomic, none, [], none)
    | .simple sd =>
      if sd.base == anySimpleTypeIdx || sd.base == anyTypeIdx || i ≤ errorTypeIdx then
        (sd.variety, sd.item, sd.members, sd.builtin)
      else inheritVariety s f sd.base

/-- §3.4.2.3.3 / §3.4.2.5: the effective content and attribute uses of a
complex type, from its local ones and its base's effective ones. -/
def effComplex (s : Schema) : Nat → Nat → ComplexDef
  | 0, _ => default
  | f + 1, i =>
    match s.type i with
    | .simple _ => default
    | .complex c =>
      if i == anyTypeIdx then c else
      match s.type c.base with
      | .simple _ => c
      | .complex _ =>
        let b := if c.base == anyTypeIdx then (match anyTypeDef with
            | .complex a => a | _ => default) else effComplex s f c.base
        let localNames := c.attrUses.map (fun u => (s.attr u.decl).name)
        if c.deriv == .extension then
          let inherited := b.attrUses.filter (fun u => !localNames.contains (s.attr u.decl).name)
          let content := match b.content, c.content with
            | .elems bp bm, .empty => ContentType.elems bp bm
            | .elems bp bm, .elems (.group 1 (some 1) .seq []) _ =>
              -- §3.4.2.3.3 clause 4.2.1 note: base element content with an
              -- explicit empty mixed content keeps the base particle.
              .elems bp bm
            | .elems bp bm, .elems cp cm =>
              match bp, cp with
              | .group 1 (some 1) .all bps, .group 1 (some 1) .all cps =>
                .elems (.group 1 (some 1) .all (bps ++ cps)) (bm || cm)
              | _, _ => .elems (.group 1 (some 1) .seq [bp, cp]) (bm || cm)
            | .simple st, _ => .simple st
            | .empty, x => x
            | .elems bp bm, .simple _ => .elems bp bm
          let oc := match c.openContent with
            | some x => some x
            | none => b.openContent
          { c with attrUses := inherited ++ c.attrUses,
                   attrWild := wildUnionOpt c.attrWild b.attrWild,
                   content, openContent := oc,
                   asserts := b.asserts ++ c.asserts }
        else
          -- restriction: base uses not redeclared and not prohibited remain
          let inherited := b.attrUses.filter (fun u =>
            !localNames.contains (s.attr u.decl).name && !c.prohibited.contains (s.attr u.decl).name)
          { c with attrUses := inherited ++ c.attrUses,
                   asserts := b.asserts ++ c.asserts }

/-- Record the prohibited names of each complex restriction so the
effective uses drop them: pass 3 returns them separately. -/
structure Prohibitions where
  byType : List (Nat × List XName) := []
deriving Inhabited

/-- §3.3.2.3: the type of a declaration given only by its substitution
group head is the head's type. -/
def headType (s : Schema) : Nat → Nat → Nat
  | 0, i => (s.elem i).typ
  | f + 1, i =>
    let e := s.elem i
    if !e.typeFromHead then e.typ
    else match e.substGroups.head? >>= s.elemIdx? with
      | some h => if h == i then e.typ else headType s f h
      | none => e.typ

/-! ## Entry point -/

/-- Read a schema from its first document and the documents it reaches
(`docs`, keyed by location). Additional `extra` locations are read as
further top-level documents (an instance's schema location hints). -/
def readSchemaDocs (docs : List LoadedDoc) (roots : List String) : Schema :=
  let col := roots.foldl (fun st r => collectDoc docs 32 r none [] [] st) ({} : Collect)
  let base := Schema.builtins
  let tops := col.tops
  -- pass 2: indices
  -- The schema for schema documents defines `xs:anyType` and may define
  -- other built-ins again; the built-in components are kept (§3.4.7).
  let typeTops := tops.toList.filter (fun t => t.kind.isType && !(t.name.ns == xsNS && (base.gTypes.lookup t.name).isSome))
  let elemTops := tops.toList.filter (·.kind == .element)
  let attrTops := tops.toList.filter (·.kind == .attribute)
  let t0 := base.types.size
  let types := base.types ++ (typeTops.map (fun _ => (default : TypeDef))).toArray
  let gTypesNew := typeTops.zipIdx.map (fun (t, k) => (t.name, t0 + k))
  let e0 := base.elems.size
  let elems := base.elems ++ (elemTops.map (fun t => ({ name := t.name, typ := anyTypeIdx, global := true } : ElemDecl))).toArray
  let gElems := elemTops.zipIdx.map (fun (t, k) => (t.name, e0 + k))
  let a0 := base.attrs.size
  let attrs := base.attrs ++ (attrTops.map (fun t => ({ name := t.name, typ := anySimpleTypeIdx, global := true } : AttrDecl))).toArray
  let gAttrsNew := attrTops.zipIdx.map (fun (t, k) => (t.name, a0 + k))
  let dupErrs (l : List XName) (what : String) : List String :=
    let rec go : List XName → List XName → List String
      | [], _ => []
      | x :: xs, seen => (if seen.contains x then [s!"duplicate {what} {x.show}"] else []) ++ go xs (x :: seen)
    go l []
  let gTypeNames := gTypesNew.map (·.1)
  let builtinClash := gTypeNames.filter (fun n => n.ns == xsNS && (base.gTypes.lookup n).isSome)
  let errs0 := col.errors ++ dupErrs gTypeNames "type" ++ dupErrs (gElems.map (·.1)) "element" ++
    dupErrs (gAttrsNew.map (·.1)) "attribute" ++
    dupErrs ((tops.toList.filter (·.kind == .group)).map (·.name)) "group" ++
    dupErrs ((tops.toList.filter (·.kind == .attributeGroup)).map (·.name)) "attribute group" ++
    builtinClash.map (fun n => s!"redefinition of built-in {n.show}")
  let notations := (tops.toList.filter (·.kind == .notation)).map (·.name)
  let sch : Schema := { base with
    types, elems, attrs,
    gTypes := base.gTypes ++ gTypesNew, gElems,
    gAttrs := base.gAttrs ++ gAttrsNew, notations,
    errors := errs0, unsupported := col.unsupported }
  -- pass 3: build
  let build : RM Unit := do
    for (t, k) in typeTops.zipIdx do
      if t.kind == .simpleType then
        let sd ← readSimpleType 64 t.ctx t.node (some t.name)
        setType (t0 + k) (.simple sd)
      else
        let cd ← readComplexType 64 t.ctx t.node (some t.name)
        setType (t0 + k) (.complex cd)
    for (t, k) in elemTops.zipIdx do
      let _ ← readElement 64 t.ctx t.node true (some (e0 + k))
    for (t, k) in attrTops.zipIdx do
      let (u, _) ← readAttrUse 64 t.ctx t.node
      match u with
      | some u =>
        let d := (← get).sch.attr u.decl
        let c := t.ctx.enter t.node
        if (attrOf "ref" t.node).isSome then addErr "top-level attribute with ref"
        if (attrOf "use" t.node).isSome then addErr "top-level attribute with use"
        if (attrOf "form" t.node).isSome then addErr "top-level attribute with form"
        setAttr (a0 + k) { d with name := ⟨c.tns, (attrOf "name" t.node).getD ""⟩, vc := u.vc,
                                  global := true }
      | none => pure ()
  let ((), rs) := build.run { sch, tops }
  let sch := rs.sch
  -- pass 4: finish
  let sch := { sch with elems := sch.elems.mapIdx (fun i (e : ElemDecl) =>
    if e.typeFromHead then { e with typ := headType sch 64 i } else e) }
  -- identity-constraint references resolved now that every one is read
  let sch := { sch with idcs := sch.idcs.map (fun (d : IDC) =>
    if d.selector == "\u0000ref" then
      match sch.gIdcs.lookup d.name with
      | some j => let r := sch.idcs.getD j default
                  { r with kind := d.kind }
      | none => d
    else d) }
  let refErrs := (sch.idcs.toList.filter (fun (d : IDC) => d.selector == "\u0000ref")).map
    (fun d => s!"unresolved identity constraint ref {d.name.show}")
  let sch := { sch with errors := refErrs ++ sch.errors }
  let sch := { sch with types := sch.types.mapIdx (fun i (t : TypeDef) =>
    match t with
    | .simple sd =>
      if i ≤ errorTypeIdx then t
      else
        let (v, it, ms, b) := inheritVariety sch 64 i
        .simple { sd with variety := v, item := it, members := ms, builtin := b }
    | other => other) }
  let sch := { sch with types := sch.types.mapIdx (fun i (t : TypeDef) =>
    match t with
    | .simple sd =>
      if i ≤ errorTypeIdx then t else .simple { sd with body := bodyOf sch 64 i }
    | other => other) }
  let sch := { sch with types := sch.types.mapIdx (fun i (t : TypeDef) =>
    match t with
    | .complex _ => if i == anyTypeIdx then t else .complex (effComplex sch 64 i)
    | other => other) }
  sch

/-- Read a schema from one parsed document with no other documents. -/
def readSchemaDoc (d : Document) (loc : String := "schema.xsd") : Schema :=
  readSchemaDocs [{ loc, doc := d }] [loc]

end L4Factoidal.XSD11
