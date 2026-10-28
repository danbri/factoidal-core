/-
L4Factoidal.XSD11.Validate — schema-validity assessment of an XML tree
(XML Schema 1.1 Part 1 §3.3.4 Element Declaration validation rules,
§3.4.4 Complex Type Definition validation rules, §3.2.4 / §3.5.4
attributes, §3.16.4 simple types, §3.17.4 ID/IDREF) and the
post-schema-validation infoset (PSVI) it produces.

  https://www.w3.org/TR/xmlschema11-1/#cvc-elt
  https://www.w3.org/TR/xmlschema11-1/#cvc-complex-type

## The PSVI is the input plus annotations

`PNode` mirrors `XML.Node`: every element keeps its tag, its attributes
and its children, and gains a `PInfo` (validity, governing type and
declaration, `nil`, the schema-normalized value and the typed value);
every attribute keeps its name and value and gains a `PInfo`. The two
PSVI additions that are new information items — attributes supplied by
a `default` or `fixed` value constraint, and the text of an element
supplied by its value constraint — are held in separate fields
(`defaults`, `defaultText`) so that erasing the annotations
(`PNode.erase`) gives back exactly the input. `XSD11/Theorems.lean`
proves that (`assess_erase`).

## XPath

Type alternatives (§3.12.4) and assertions (§3.13.4) need XPath 2.0.
This module does not import an XPath engine: it takes a `Hooks` value
whose functions evaluate a test. `XSD11/XPathHooks.lean` supplies one
built on `L4Factoidal.XPath4`. With `Hooks.none` a test is not
evaluated and the outcome is recorded in `unsupported`, never guessed.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD11.ContentModel
import L4Factoidal.XSD11.Reader
import L4Factoidal.XSD11.Pattern

namespace L4Factoidal.XSD11

open L4Factoidal.XML
open L4Factoidal.XSD (localOf prefixOf bindingsOf)

/-! ## The PSVI -/

inductive Validity where
  | valid | invalid | notKnown
deriving DecidableEq, Repr, Inhabited

/-- The PSVI properties of an element or attribute information item
(§3.3.5, §3.2.5): `[validity]`, `[type definition]`, `[element
declaration]` / `[attribute declaration]`, `[nil]`, `[schema normalized
value]`, and the typed value (`[schema actual value]`). -/
structure PInfo where
  validity : Validity := .notKnown
  typ : Option Nat := none
  decl : Option Nat := none
  nilled : Bool := false
  normalized : Option String := none
  value : Option XSD.Val := none
  /-- For a union type: the member type the value was validated by. -/
  memberType : Option Nat := none
deriving Repr, Inhabited

/-- An attribute with its PSVI properties. -/
structure PAttr where
  attr : Attribute
  name : XName
  info : PInfo := {}
deriving Repr, Inhabited

/-- A node of the PSVI. -/
inductive PNode where
  | elem (tag : String) (attrs : List PAttr) (kids : List PNode) (name : XName)
      (info : PInfo) (defaults : List PAttr) (defaultText : Option String)
  | text (s : String)
  | cdata (s : String)
  | comment (s : String)
  | pi (t d : String)
deriving Repr, Inhabited

mutual
/-- Erase the annotations: the input tree. -/
def PNode.erase : PNode → Node
  | .elem tag attrs kids _ _ _ _ => .element tag (attrs.map (·.attr)) (PNode.eraseList kids)
  | .text s => .text s
  | .cdata s => .cdata s
  | .comment s => .comment s
  | .pi t d => .pi t d

def PNode.eraseList : List PNode → List Node
  | [] => []
  | p :: ps => p.erase :: PNode.eraseList ps
end

def PNode.info? : PNode → Option PInfo
  | .elem _ _ _ _ i _ _ => some i
  | _ => none

def PNode.kids : PNode → List PNode
  | .elem _ _ k _ _ _ _ => k
  | _ => []

def PNode.attrs : PNode → List PAttr
  | .elem _ a _ _ _ d _ => a ++ d
  | _ => []

def PNode.name? : PNode → Option XName
  | .elem _ _ _ n _ _ _ => some n
  | _ => none

/-! ## Names in an instance -/

def instBindings (bs : NsBindings) (attrs : List Attribute) : NsBindings :=
  bindingsOf attrs ++ bs

/-- The expanded name of an element tag (unprefixed: the default
namespace). -/
def elemXName (bs : NsBindings) (tag : String) : XName :=
  match tag.splitOn ":" with
  | [p, l] => ⟨(lookupNs bs p).getD "", l⟩
  | _ => ⟨(lookupNs bs "").getD "", tag⟩

/-- The expanded name of an attribute (unprefixed: no namespace). -/
def attrXName (bs : NsBindings) (nm : String) : XName :=
  match nm.splitOn ":" with
  | [p, l] => ⟨(lookupNs bs p).getD "", l⟩
  | _ => ⟨"", nm⟩

def isNsDecl (a : Attribute) : Bool := a.name == "xmlns" || a.name.startsWith "xmlns:"

/-- A QName in instance content (an `xsi:type` value, a QName-typed
value): `none` when its prefix is not declared. -/
def resolveInstQName (bs : NsBindings) (s : String) : Option XName :=
  let s := XSD.applyWhiteSpace .collapse s
  match s.splitOn ":" with
  | [p, l] => (lookupNs bs p).map (fun u => ⟨u, l⟩)
  | [l] => some ⟨(lookupNs bs "").getD "", l⟩
  | _ => none

/-! ## Hooks for XPath -/

/-- The XPath evaluations validation needs. `test sch e ns xdns n`
evaluates the boolean test `e` with `n` as the context node (a type
alternative or an assertion); `testValue sch e ns xdns t v` evaluates an
assertion facet with `$value` bound to the literal `v` typed by simple
type `t`. `none` means "cannot evaluate". -/
structure Hooks where
  test : Schema → String → NsBindings → String → PNode → Option Bool
  testValue : Schema → String → NsBindings → String → Nat → String → Option Bool

def Hooks.none : Hooks := ⟨fun _ _ _ _ _ => Option.none, fun _ _ _ _ _ _ => Option.none⟩

/-! ## Simple values -/

/-- Replace the prefix of a QName value by its namespace name, so values
compare by expanded name (Part 2 §3.3.18: the value space of `QName` is
the set of expanded names). -/
def resolveQNameVal (bs : NsBindings) : XSD.Val → Option XSD.Val
  | .qname p l nt => if p == "" then some (.qname ((lookupNs bs "").getD "") l nt)
                     else (lookupNs bs p).map (fun u => .qname u l nt)
  | .seq vs =>
    let rs := vs.map (resolveQNameVal' bs)
    if rs.all Option.isSome then some (.seq (rs.filterMap id)) else none
  | v => some v
where
  resolveQNameVal' (bs : NsBindings) : XSD.Val → Option XSD.Val
    | .qname p l nt => if p == "" then some (.qname ((lookupNs bs "").getD "") l nt)
                       else (lookupNs bs p).map (fun u => .qname u l nt)
    | v => some v

/-- The assertions on a simple type's derivation chain. -/
def Schema.simpleAsserts (s : Schema) : Nat → Nat → List Assertion
  | 0, _ => []
  | f + 1, t =>
    match s.type t with
    | .simple sd => if t ≤ errorTypeIdx then [] else sd.asserts ++ s.simpleAsserts f sd.base
    | _ => []

/-- The `pattern` facets of a Part 2 type at every level (the list
level on the whole literal, the item type on each item, a union's member
on the value), decided by `XSD11.Pattern` (the shared XSD profile, then
the F&O 4.0 parser for the XSD 1.1 syntax the profile refuses). -/
def bodyPatternsOk : Nat → XSD.SimpleType → String → Bool
  | 0, _, _ => true
  | f + 1, t, lit =>
    let norm := XSD.applyWhiteSpace t.whiteSpaceOf lit
    patternOk11 t.facets.patterns norm &&
    (match t with
     | .atomic _ _ => true
     | .list it _ => ((norm.splitOn " ").filter (· != "")).all (bodyPatternsOk f it)
     | .union ms _ => ms.any (fun m => (XSD.valueOf m norm).isSome && bodyPatternsOk f m norm))

/-- The enumeration in force on a simple type and the bindings of the
step that declared it. -/
def Schema.enumOf (s : Schema) : Nat → Nat → Option (List String × NsBindings)
  | 0, _ => none
  | f + 1, t =>
    match s.type t with
    | .simple sd =>
      if t ≤ errorTypeIdx then none
      else match sd.facets.enumeration with
        | some vs => some (vs, sd.facetNs)
        | none => s.enumOf f sd.base
    | _ => none

def clearEnum : XSD.SimpleType → XSD.SimpleType
  | .atomic b f => .atomic b { f with enumeration := none }
  | other => other

/-- §3.16.4 String Valid: the literal against simple type `t`. Returns
the schema-normalized value and the typed value, or the error. -/
def validateSimple (s : Schema) (h : Hooks) (bs : NsBindings) (t : Nat) (lit : String)
    (unsup : List String) : Except String (String × XSD.Val) × List String :=
  match s.simpleOf? t with
  | none => (.error "not a simple type", unsup)
  | some sd =>
    let norm := XSD.applyWhiteSpace sd.body.whiteSpaceOf lit
    -- QName and NOTATION enumerations compare expanded names (Part 2
    -- §3.3.18): the facet values with the schema's bindings, below
    let qEnum : Bool := match sd.body with
      | .atomic b f => (b.primitive == some .qname || b.primitive == some .notation) && f.enumeration.isSome
      | _ => false
    let body := if qEnum then clearEnum sd.body else sd.body
    match (XSD.valueOf body lit).filter (fun _ => bodyPatternsOk 16 sd.body lit) with
    | none => (.error s!"'{lit}' is not valid for {(sd.name.map XName.show).getD "an anonymous type"}", unsup)
    | some v =>
      -- QName and NOTATION values need their prefixes declared.
      let isQ : Bool := match sd.body with
        | .atomic b _ => (b.primitive == some .qname || b.primitive == some .notation)
        | .list (.atomic b _) _ => (b.primitive == some .qname || b.primitive == some .notation)
        | _ => false
      let isNotation : Bool := match sd.body with
        | .atomic b _ => b.primitive == some .notation
        | _ => false
      let v' := if isQ then resolveQNameVal bs v else some v
      match v' with
      | none => (.error s!"undeclared prefix in QName '{lit}'", unsup)
      | some v =>
        let notationOk := !isNotation || (match v with
          | .qname u l _ => s.notations.contains ⟨u, l⟩
          | _ => false)
        let enumOk := !qEnum || (match s.enumOf 64 t with
          | some (vs, ens) => vs.any (fun ev =>
              match resolveInstQName ens ev with
              | some n => (match v with
                | .qname u l _ => n.ns == u && n.loc == l
                | _ => false)
              | none => false)
          | none => true)
        if !notationOk then (.error s!"'{lit}' does not name a declared notation", unsup)
        else if !enumOk then (.error s!"'{lit}' is not in the enumeration", unsup)
        else
        let asserts := s.simpleAsserts 64 t
        let (ok, unsup) := asserts.foldl (fun (ok, un) a =>
          match h.testValue s a.test a.ns a.xpathDefaultNs t norm with
          | some b => (ok && b, un)
          | none => (ok, s!"assertion facet {a.test}" :: un)) (true, unsup)
        if ok then (.ok (norm, v), unsup) else (.error s!"assertion facet fails for '{lit}'", unsup)

/-- Is the type derived from `xs:ID` / `xs:IDREF` / `xs:IDREFS`? -/
def Schema.idKind (s : Schema) (t : Nat) : Option XSD.Builtin :=
  match s.simpleOf? t with
  | some sd =>
    match sd.body with
    | .atomic b _ =>
      if XSD.derivedFrom b .id then some .id
      else if XSD.derivedFrom b .idref then some .idref
      else if b == .idrefs then some .idrefs
      else none
    | .list (.atomic b _) _ => if XSD.derivedFrom b .idref then some .idrefs else none
    | _ => none
  | none => none

/-! ## Accumulated document-level state -/

structure VAcc where
  ids : List String := []
  idrefs : List String := []
  errors : List String := []
  unsupported : List String := []
deriving Inhabited

def VAcc.err (a : VAcc) (e : String) : VAcc := { a with errors := e :: a.errors }

/-- Record ID / IDREF values of a validated simple value (§3.17.4). -/
def VAcc.noteIds (a : VAcc) (s : Schema) (t : Nat) (v : XSD.Val) : VAcc :=
  match s.idKind t, v with
  | some .id, .str _ x =>
    if a.ids.contains x then { a with errors := s!"duplicate ID {x}" :: a.errors }
    else { a with ids := x :: a.ids }
  | some .idref, .str _ x => { a with idrefs := x :: a.idrefs }
  | some .idrefs, .seq vs => { a with idrefs := (vs.filterMap (fun v => match v with
      | .str _ x => some x | _ => none)) ++ a.idrefs }
  | _, _ => a

/-! ## Substitution groups and derivation -/

/-- §3.3.6.3 Substitution Group OK (Transitive), clause 2: `member` is
in the substitution group of `head` (by its affiliations), and neither
the head's `{disallowed substitutions}` nor the derivation methods
block it. -/
def Schema.substOk (s : Schema) (head member : Nat) : Bool :=
  let hd := s.elem head
  let rec reaches : Nat → Nat → Bool
    | 0, _ => false
    | f + 1, m =>
      let me := s.elem m
      me.substGroups.any (fun g => match s.elemIdx? g with
        | some gi => gi == head || reaches f gi
        | none => false)
  if hd.block.contains .substitution then false
  else if !(reaches 32 member) then false
  else
    let mt := (s.elem member).typ
    let methods := s.methodsUpTo 64 mt hd.typ
    let typeBlock := match s.type hd.typ with
      | .complex c => c.block
      | _ => []
    s.derivesFrom mt hd.typ && !methods.any (fun m => hd.block.contains m || typeBlock.contains m)

/-- The declaration an element named `n` is validated against when it
matches the particle of declaration `d`. -/
def Schema.declFor (s : Schema) (d : Nat) (n : XName) : Option Nat :=
  if (s.elem d).name == n then some d
  else if !(s.elem d).global then none
  else (s.gElems.find? (fun (gn, gi) => gn == n && s.substOk d gi)).map (·.2)

/-- The element names of the element particles of a content model (for
`##definedSibling`). -/
def Particle.elemNames (s : Schema) : Nat → Particle → List XName
  | 0, _ => []
  | f + 1, p =>
    match p with
    | .elem _ _ d => [(s.elem d).name]
    | .wild _ _ _ => []
    | .group _ _ _ ps => ps.flatMap (Particle.elemNames s f)

def Schema.matchCtx (s : Schema) (siblings : List XName) : MatchCtx :=
  { declFor := s.declFor,
    wildOk := fun w n => w.allowsName n &&
      !(w.notDefined && (s.elemIdx? n).isSome) &&
      !(w.notSibling && siblings.contains n) }

/-- §3.4.6.5 Type Derivation OK (Complex) / §3.16.6.3 (Simple), with the
blocking set: `d` may stand for `b` when it is derived from it and no
method on the chain is in `blocked`. -/
def Schema.derivOkBlocked (s : Schema) (d b : Nat) (blocked : List DerivKw) : Bool :=
  s.derivesFrom d b && !((s.methodsUpTo 64 d b).any (fun m => blocked.contains m)) &&
  -- the prohibited substitutions of each type on the chain
  !((s.chainUpTo 64 d b).any (fun t =>
      match s.type t with
      | .complex _ => false
      | _ => false))

/-! ## Element validation -/

/-- How an element is to be validated. -/
inductive How where
  /-- Against this element declaration. -/
  | decl (d : Nat)
  /-- Matched by a wildcard with these process contents (§3.10.4). -/
  | wild (pc : ProcessContents)
  /-- Against a type with no declaration (`xsi:type` at the root, or a
  validation request with a type). -/
  | typ (t : Nat)
deriving Inhabited

mutual
/-- A node with no annotations. -/
def PNode.ofNode : Node → PNode
  | .element tag attrs kids => .elem tag (attrs.map (fun a => ⟨a, ⟨"", a.name⟩, {}⟩))
      (PNode.ofNodeList kids) ⟨"", tag⟩ {} [] none
  | .text s => .text s
  | .cdata s => .cdata s
  | .comment s => .comment s
  | .pi t d => .pi t d

def PNode.ofNodeList : List Node → List PNode
  | [] => []
  | n :: ns => PNode.ofNode n :: PNode.ofNodeList ns
end

def isWs (s : String) : Bool := s.all XML.isXmlSpace

def leafText : Node → String
  | .text s | .cdata s => s
  | _ => ""

def PNode.ofLeaf : Node → PNode
  | .text s => .text s
  | .cdata s => .cdata s
  | .comment s => .comment s
  | .pi t d => .pi t d
  | .element tag attrs _ => .elem tag (attrs.map (fun a => ⟨a, ⟨"", a.name⟩, {}⟩)) [] ⟨"", tag⟩ {} [] none

def xsiAttrVal (bs : NsBindings) (attrs : List Attribute) (l : String) : Option String :=
  (attrs.find? (fun a => !isNsDecl a && attrXName bs a.name == ⟨xsiNS, l⟩)).map (·.value)

/-- Validate one attribute against its declaration (with the use's value
constraint, if any). -/
def validateAttrValue (s : Schema) (h : Hooks) (bs : NsBindings) (d : Nat)
    (vc : Option ValueConstraint) (a : Attribute) (acc : VAcc) : PInfo × VAcc :=
  let ad := s.attr d
  let (r, un) := validateSimple s h bs ad.typ a.value acc.unsupported
  let acc := { acc with unsupported := un }
  match r with
  | .error e => ({ validity := .invalid, typ := some ad.typ, decl := some d },
                 acc.err s!"attribute {a.name}: {e}")
  | .ok (norm, v) =>
    let vc := vc.orElse (fun _ => ad.vc)
    let fixedOk := match vc with
      | some ⟨.fixed, lex⟩ =>
        match (validateSimple s h bs ad.typ lex []).1 with
        | .ok (_, fv) => XSD.valEqualOrIdentical v fv
        | .error _ => false
      | _ => true
    let acc := acc.noteIds s ad.typ v
    if fixedOk then ({ validity := .valid, typ := some ad.typ, decl := some d, normalized := some norm, value := some v }, acc)
    else ({ validity := .invalid, typ := some ad.typ, decl := some d, normalized := some norm, value := some v },
          acc.err s!"attribute {a.name}: value does not match fixed value")

/-- The xsi attributes, checked against their built-in declarations. -/
def xsiAttrInfo (s : Schema) (h : Hooks) (bs : NsBindings) (n : XName) (a : Attribute) (acc : VAcc) : PInfo × VAcc :=
  -- §3.2.7: `xsi:schemaLocation` is a list of URI pairs and is a hint
  -- only (§4.3.2); its value is not checked here.
  if n.loc == "schemaLocation" || n.loc == "noNamespaceSchemaLocation" then ({ validity := .valid }, acc) else
  match s.attrIdx? n with
  | some d => validateAttrValue s h bs d none a acc
  | none => ({ validity := .invalid }, acc.err s!"unknown xsi attribute {a.name}")

/-- Attributes of an element whose type is `t` (§3.4.4.2 clauses 2-4):
each attribute's PSVI info, the defaulted attributes, and whether all
are valid. -/
def validateAttrs (s : Schema) (h : Hooks) (bs : NsBindings) (t : Nat) (attrs : List Attribute)
    (acc : VAcc) : List PInfo × List PAttr × Bool × VAcc :=
  let (uses, wild) := match s.type t with
    | .complex c => (c.attrUses, c.attrWild)
    | .simple _ => ([], none)
  let step := fun (st : Array PInfo × Bool × VAcc) (a : Attribute) =>
    let (out, ok, acc) := st
    if isNsDecl a then (out.push { validity := .valid }, ok, acc)
    else
    let n := attrXName bs a.name
    if n.ns == xsiNS then
      let (i, acc) := xsiAttrInfo s h bs n a acc
      (out.push i, ok && i.validity != .invalid, acc)
    else
    match uses.find? (fun u => (s.attr u.decl).name == n) with
    | some u =>
      let (i, acc) := validateAttrValue s h bs u.decl u.vc a acc
      (out.push i, ok && i.validity == .valid, acc)
    | none =>
      match wild with
      | some w =>
        if w.allowsName n && !(w.notDefined && (s.attrIdx? n).isSome) then
          match w.pc with
          | .skip => (out.push {}, ok, acc)
          | pc =>
            match s.attrIdx? n with
            | some d =>
              let (i, acc) := validateAttrValue s h bs d none a acc
              (out.push i, ok && i.validity == .valid, acc)
            | none =>
              if pc == .strict then (out.push { validity := .invalid }, false, acc.err s!"no declaration for attribute {n.show}")
              else (out.push {}, ok, acc)
        else (out.push { validity := .invalid }, false, acc.err s!"attribute {n.show} not allowed")
      | none => (out.push { validity := .invalid }, false, acc.err s!"attribute {n.show} not allowed")
  let (infos, ok, acc) := attrs.foldl step (#[], true, acc)
  let present := attrs.filter (fun a => !isNsDecl a) |>.map (fun a => attrXName bs a.name)
  -- required attributes (§3.4.4.2 clause 3)
  let missing := uses.filter (fun u => u.required && !present.contains (s.attr u.decl).name)
  let acc := missing.foldl (fun acc u => acc.err s!"required attribute {(s.attr u.decl).name.show} missing") acc
  -- defaulted attributes (§3.4.5.2 / §3.2.5)
  let defaults := uses.filterMap (fun u =>
    let ad := s.attr u.decl
    if present.contains ad.name then none
    else match u.vc.orElse (fun _ => ad.vc) with
      | some vc =>
        let pfx := ""
        let nm := if ad.name.ns == "" then ad.name.loc else pfx ++ ad.name.loc
        some ({ attr := ⟨nm, vc.lex⟩, name := ad.name,
                info := { validity := .valid, typ := some ad.typ, decl := some u.decl,
                          normalized := some vc.lex,
                          value := match (validateSimple s h bs ad.typ vc.lex []).1 with
                            | .ok (_, v) => some v | .error _ => none } } : PAttr)
      | none => none)
  (infos.toList, defaults, ok && missing.isEmpty, acc)

/-- The text content of the children (character data only). -/
def textContent (kids : List Node) : String :=
  String.join (kids.map leafText)

def hasElementKid (kids : List Node) : Bool :=
  kids.any (fun k => match k with | .element _ _ _ => true | _ => false)

/-- Choose the governing type of an element with declaration `d` from
its type table (§3.12.4 Type Alternative Satisfied). -/
def selectType (s : Schema) (h : Hooks) (d : Nat) (probe : PNode) (acc : VAcc) : Nat × VAcc :=
  let e := s.elem d
  let rec go : List TypeAlt → VAcc → Nat × VAcc
    | [], acc => (e.typ, acc)
    | a :: rest, acc =>
      match a.test with
      | none => (a.typ, acc)
      | some t =>
        match h.test s t a.ns a.xpathDefaultNs probe with
        | some true => (a.typ, acc)
        | some false => go rest acc
        | none => go rest { acc with unsupported := s!"type alternative test {t}" :: acc.unsupported }
  go e.alts acc

/-- The assertions of a complex type (§3.13.4.1). -/
def checkAsserts (s : Schema) (h : Hooks) (t : Nat) (pn : PNode) (acc : VAcc) : Bool × VAcc :=
  match s.type t with
  | .complex c =>
    c.asserts.foldl (fun (ok, acc) a =>
      match h.test s a.test a.ns a.xpathDefaultNs pn with
      | some b => (ok && b, if b then acc else acc.err s!"assertion {a.test} fails")
      | none => (ok, { acc with unsupported := s!"assertion {a.test}" :: acc.unsupported })) (true, acc)
  | .simple _ => (true, acc)

/-! ## Children -/

/-- How the children of an element are assessed. -/
inductive KidMode where
  /-- Every element child is skipped (the parent is skipped or nilled). -/
  | skip
  /-- Every element child is assessed laxly (§3.10.4.1, lax). -/
  | lax
  /-- Simple content: an element child is an error. -/
  | simple
  /-- Element or mixed content: the children follow the content model. -/
  | content (m : MatchCtx) (oc : Option (OpenMode × Wildcard)) (mixed : Bool)

/-- The state carried across the children. -/
structure KState where
  cm : Option CMState := none
  ok : Bool := true
  acc : VAcc := {}

def kidBindings (bs : NsBindings) : Node → NsBindings
  | .element _ kattrs _ => instBindings bs kattrs
  | _ => bs

def kidTag : Node → String
  | .element t _ _ => t
  | _ => ""

/-- How an element child is validated, and the state after the content
model consumed it. -/
def KidMode.decide (mode : KidMode) (bs : NsBindings) (parent : XName) (st : KState) (k : Node) : How × KState :=
  match mode with
  | .skip => (.wild .skip, { st with ok := false })
  | .lax => (.wild .lax, st)
  | .simple =>
    let acc := st.acc.err s!"element {parent.show}: element child in simple content"
    (.wild .skip, { st with ok := false, acc := acc })
  | .content m oc _ =>
    let kname := elemXName (kidBindings bs k) (kidTag k)
    match st.cm.bind (fun c => c.step m oc kname) with
    | some (c', .decl d) => (.decl d, { st with cm := some c' })
    | some (c', .wild w) => (.wild w.pc, { st with cm := some c' })
    | none =>
      let acc := st.acc.err s!"element {parent.show}: child {kname.show} not allowed here"
      (.wild .skip, { st with cm := none, ok := false, acc := acc })

/-- The state after an element child was validated: its validity counts. -/
def KidMode.after (mode : KidMode) (how : How) (st : KState) (pk : PNode) : KState :=
  let kv := (pk.info?.map (·.validity)).getD .notKnown
  let kok := match mode, how with
    | .skip, _ | .simple, _ => true
    | .lax, _ => kv != .invalid
    | .content .., .decl _ => kv == .valid
    | .content .., .wild .strict => kv == .valid
    | .content .., .wild .skip => true
    | .content .., _ => kv != .invalid
  { st with ok := st.ok && kok }

/-- The state after a character, comment or processing-instruction child. -/
def KidMode.leaf (mode : KidMode) (parent : XName) (st : KState) (k : Node) : KState :=
  match mode with
  | .content _ _ mixed =>
    let x := leafText k
    if mixed || isWs x then st
    else { st with ok := false, acc := st.acc.err s!"element {parent.show}: character data not allowed" }
  | _ => st

/-- One child: an element is validated by `rec` as the mode decides; any
other node is copied. -/
def kidStep (rec : NsBindings → How → Node → VAcc → PNode × VAcc) (mode : KidMode)
    (bs : NsBindings) (parent : XName) (st : KState) (k : Node) : PNode × KState :=
  match k with
  | .element .. =>
    let (how, st) := mode.decide bs parent st k
    let (pk, acc) := rec bs how k st.acc
    (pk, mode.after how { st with acc } pk)
  | other => (PNode.ofLeaf other, mode.leaf parent st other)

/-- The children, one step each, with the state threaded through (a tail
call per child). -/
def foldKids (step : KState → Node → PNode × KState) : List Node → KState → List PNode → List PNode × KState
  | [], st, out => (out.reverse, st)
  | k :: ks, st, out =>
    let r := step st k
    foldKids step ks r.2 (r.1 :: out)

/-- Pair the attributes with their PSVI information, in order. -/
def mkPAttrs (nm : String → XName) : List Attribute → List PInfo → List PAttr
  | [], _ => []
  | a :: as, i :: is => ⟨a, nm a.name, i⟩ :: mkPAttrs nm as is
  | a :: as, [] => ⟨a, nm a.name, {}⟩ :: mkPAttrs nm as []

/-- The attributes of an element that has no type (lax assessment): an
attribute with a global declaration is validated against it. -/
def laxAttrs (s : Schema) (h : Hooks) (bs : NsBindings) (attrs : List Attribute) (acc : VAcc)
    : List PInfo × Bool × VAcc :=
  let (ainfos, aok, acc) := attrs.foldl (fun (st : Array PInfo × Bool × VAcc) a =>
    let (out, ok, acc) := st
    if isNsDecl a then (out.push {}, ok, acc)
    else
    match s.attrIdx? (attrXName bs a.name) with
    | some d =>
      let (i, acc) := validateAttrValue s h bs d none a acc
      (out.push i, ok && i.validity != .invalid, acc)
    | none => (out.push {}, ok, acc)) (#[], true, acc)
  (ainfos.toList, aok, acc)

/-! ## Element validation -/

/-- What is known about an element before its children are read. -/
structure Head where
  declOpt : Option Nat
  typ : Option Nat
  skip : Bool
  /-- `xsi:type`, abstractness and `xsi:nil` are acceptable. -/
  headOk : Bool
  nilled : Bool
  ainfos : List PInfo
  defaults : List PAttr
  aok : Bool
  mode : KidMode
  st0 : KState

/-- §3.3.4.3 clauses 1-4 and §3.4.4.2 clauses 2-4: the declaration, the
governing type (type table, `xsi:type`), `xsi:nil`, the attributes, and
how the children are to be read. -/
def elemHead (s : Schema) (h : Hooks) (bs : NsBindings) (how : How) (tag : String)
    (attrs : List Attribute) (kids : List Node) (acc : VAcc) : Head :=
  let name := elemXName bs tag
  let probe := PNode.elem tag (attrs.map (fun a => ⟨a, attrXName bs a.name, {}⟩)) [] name {} [] none
  let declOpt : Option Nat := match how with
    | .decl d => some d
    | .wild .skip => none
    | .wild _ => s.elemIdx? name
    | .typ _ => none
  let skip := match how with | .wild .skip => true | _ => false
  let declInvalid := match declOpt with
    | some d => (s.elem d).abstract
    | none => false
  let acc := if declInvalid then acc.err s!"element {name.show}: declaration is abstract" else acc
  let (declType, acc) : Option Nat × VAcc := match declOpt, how with
    | some d, _ => let (t, a) := selectType s h d probe acc; (some t, a)
    | none, .typ t => (some t, acc)
    | none, _ => (none, acc)
  let xsiType := if skip then none else xsiAttrVal bs attrs "type"
  let (typ, typOk, acc) : Option Nat × Bool × VAcc := match xsiType with
    | none => (declType, true, acc)
    | some q =>
      match (resolveInstQName bs q).bind s.typeIdx? with
      | none => (declType, false, acc.err s!"element {name.show}: xsi:type {q} does not resolve")
      | some xt =>
        match declType with
        | none => (some xt, true, acc)
        | some dt =>
          let blocked := (declOpt.map (fun d => (s.elem d).block)).getD [] ++
            (match s.type dt with | .complex c => c.block | _ => [])
          if s.derivOkBlocked xt dt blocked then (some xt, true, acc)
          else (declType, false, acc.err s!"element {name.show}: xsi:type {q} is not validly derived")
  let typAbstract := match typ.map s.type with
    | some (.complex c) => c.abstract
    | _ => false
  let acc := if typAbstract then acc.err s!"element {name.show}: type is abstract" else acc
  match typ with
  | none =>
    if skip then
      { declOpt, typ, skip, headOk := true, nilled := false, ainfos := [], defaults := [],
        aok := true, mode := .skip, st0 := { acc } }
    else
      let (ainfos, aok, acc) := laxAttrs s h bs attrs acc
      { declOpt, typ, skip, headOk := typOk, nilled := false, ainfos, defaults := [], aok,
        mode := .lax, st0 := { acc } }
  | some t =>
    let nilAttr := xsiAttrVal bs attrs "nil"
    let nillable := (declOpt.map (fun d => (s.elem d).nillable)).getD false
    let nilled := nilAttr.map (fun v => XSD.applyWhiteSpace .collapse v == "true" ||
      XSD.applyWhiteSpace .collapse v == "1") |>.getD false
    let nilOk := !nilAttr.isSome || nillable
    let acc := if !nilOk then acc.err s!"element {name.show}: xsi:nil on a non-nillable declaration" else acc
    let (ainfos, defaults, aok, acc) := validateAttrs s h bs t attrs acc
    let vc := declOpt.bind (fun d => (s.elem d).vc)
    let txt := textContent kids
    let nilContentOk := !nilled || (!hasElementKid kids && txt.all XML.isXmlSpace && (vc.map (·.kind)) != some .fixed)
    let acc := if !nilContentOk then acc.err s!"element {name.show}: nilled element has content" else acc
    let headOk := typOk && nilOk && nilContentOk && !declInvalid && !typAbstract
    let isSimple : Bool := (s.simpleOf? t).isSome
    let (mode, cm) : KidMode × Option CMState :=
      if nilled then (.skip, none)
      else if isSimple then (.simple, none)
      else match s.type t with
        | .complex c => match c.content with
          | .elems p m => (.content (s.matchCtx (Particle.elemNames s 64 p)) c.openContent m, some (CMState.init p))
          | _ => (.content (s.matchCtx []) c.openContent false, some { res := [.eps] })
        | _ => (.content (s.matchCtx []) none false, some { res := [.eps] })
    -- a nilled element's children are an error already counted above
    let st0 : KState := { cm, acc }
    { declOpt, typ, skip, headOk, nilled := nilled && nilOk, ainfos, defaults, aok, mode, st0 }

/-- §3.3.4.3 clause 5 and §3.4.4.2 clause 1: the PSVI information of the
element once its children are read, and the default text. -/
def elemFinish (s : Schema) (h : Hooks) (bs : NsBindings) (tag : String) (attrs : List Attribute)
    (kids : List Node) (hd : Head) (outs : List PNode) (kst : KState) : PInfo × Option String × VAcc :=
  let name := elemXName bs tag
  let acc := kst.acc
  match hd.typ with
  | none =>
    let v := if hd.skip then Validity.notKnown
      else if kst.ok && hd.aok && hd.headOk then .notKnown else .invalid
    ({ validity := v }, none, acc)
  | some t =>
    let pattrs := mkPAttrs (attrXName bs) attrs hd.ainfos
    let base := hd.headOk && hd.aok && kst.ok
    if hd.nilled then
      ({ validity := if base then .valid else .invalid, typ := some t, decl := hd.declOpt, nilled := true }, none, acc)
    else
    match s.simpleOf? t with
    | some sd =>
      let st := match s.type t with
        | .complex c => match c.content with
          | .simple x => x
          | _ => t
        | _ => t
      let _ := sd
      let vc := hd.declOpt.bind (fun d => (s.elem d).vc)
      let txt := textContent kids
      let noContent := !hasElementKid kids && txt == ""
      let (lit, defText) := if noContent then
          match vc with
          | some v => (v.lex, some v.lex)
          | none => (txt, none)
        else (txt, none)
      let (r, un) := validateSimple s h bs st lit acc.unsupported
      let acc := { acc with unsupported := un }
      let (sok, norm, val, acc) := match r with
        | .ok (norm, v) => (true, some norm, some v, acc.noteIds s st v)
        | .error e => (false, none, none, acc.err s!"element {name.show}: {e}")
      let fixedOk := match vc, val with
        | some ⟨.fixed, lex⟩, some v =>
          match (validateSimple s h bs st lex []).1 with
          | .ok (_, fv) => XSD.valEqualOrIdentical v fv
          | .error _ => false
        | _, _ => true
      let acc := if !fixedOk then acc.err s!"element {name.show}: value does not match fixed value" else acc
      let info : PInfo := { validity := .notKnown, typ := some t, decl := hd.declOpt, normalized := norm, value := val }
      let (asOk, acc) := checkAsserts s h t (PNode.elem tag pattrs outs name info hd.defaults defText) acc
      ({ info with validity := if base && sok && fixedOk && asOk then .valid else .invalid }, defText, acc)
    | none =>
      let endOk := (kst.cm.map CMState.nullable).getD false
      let acc := if endOk then acc else acc.err s!"element {name.show}: content incomplete"
      let info : PInfo := { validity := .notKnown, typ := some t, decl := hd.declOpt }
      let (asOk, acc) := checkAsserts s h t (PNode.elem tag pattrs outs name info hd.defaults none) acc
      ({ info with validity := if base && endOk && asOk then .valid else .invalid }, none, acc)

/-- Validate an element (§3.3.4.3 Element Locally Valid (Element) and
§3.4.4.2 Element Locally Valid (Complex Type)). `bs0` holds the bindings
in scope on the parent. The output element is built in one place from
the input's tag, attributes and children, which is what makes
`Theorems.validateElement_erase` a short induction. -/
def validateElement (s : Schema) (h : Hooks) : Nat → NsBindings → How → Node → VAcc → PNode × VAcc
  | 0, _, _, n, acc => (PNode.ofNode n, acc.err "element nesting too deep")
  | f + 1, bs0, how, n, acc =>
    match n with
    | .element tag attrs kids =>
      let bs := instBindings bs0 attrs
      let name := elemXName bs tag
      let hd := elemHead s h bs how tag attrs kids acc
      let (outs, kst) := foldKids (kidStep (validateElement s h f) hd.mode bs name) kids hd.st0 []
      let (info, defText, acc) := elemFinish s h bs tag attrs kids hd outs kst
      (.elem tag (mkPAttrs (attrXName bs) attrs hd.ainfos) outs name info hd.defaults defText, acc)
    | other => (PNode.ofLeaf other, acc)

/-! ## Assessment of a document -/

structure Assessment where
  root : PNode
  valid : Bool
  errors : List String
  unsupported : List String
deriving Inhabited

/-- How the document element is validated: by its global declaration,
else by its `xsi:type`; `none` when it has neither. -/
def rootHow (s : Schema) (root : Node) (bs : NsBindings) : Option How :=
  match root with
  | .element tag attrs _ =>
    let rbs := instBindings bs attrs
    match s.elemIdx? (elemXName rbs tag) with
    | some d => some (.decl d)
    | none =>
      match (xsiAttrVal rbs attrs "type").bind (resolveInstQName rbs) |>.bind s.typeIdx? with
      | some t => some (.typ t)
      | none => none
  | _ => none

/-- §5.2 assessment starting from the document element, strictly: the
element must have a global declaration (or an `xsi:type`) and be valid,
and every IDREF must name an ID (§3.17.4). Identity constraints are
checked by `XSD11/Identity.lean` through `assessDoc`. -/
def assessRoot (s : Schema) (h : Hooks) (root : Node) (bs : NsBindings := []) : Assessment :=
  match rootHow s root bs with
  | none =>
    let r := validateElement s h 10000 bs (.wild .lax) root {}
    { root := r.1, valid := false, errors := "no declaration for the document element" :: r.2.errors,
      unsupported := r.2.unsupported }
  | some how =>
    let r := validateElement s h 10000 bs how root {}
    let acc := r.2
    let dangling := acc.idrefs.filter (fun x => !acc.ids.contains x)
    let errs := dangling.map (fun x => s!"IDREF {x} has no matching ID") ++ acc.errors
    let dupIds := acc.errors.filter (fun e => e.startsWith "duplicate ID")
    { root := r.1, valid := (r.1.info?.map (·.validity)) == some .valid && dangling.isEmpty && dupIds.isEmpty,
      errors := errs, unsupported := acc.unsupported }

end L4Factoidal.XSD11
