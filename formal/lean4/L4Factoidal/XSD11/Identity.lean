/-
L4Factoidal.XSD11.Identity — identity constraints: XML Schema 1.1 Part 1
§3.11.4 (Identity-constraint Satisfied) over the PSVI, with the
restricted XPath of §3.11.6.2 for `selector` and `field`.

  https://www.w3.org/TR/xmlschema11-1/#cvc-identity-constraint

A selector selects descendant elements of the element that carries the
constraint (the target node set); each field selects at most one element
or attribute of a target node, whose typed value is one key component.
Key sequences are compared by the value equality of Part 2 (`XSD.Val`,
`valEqualOrIdentical`), so `1` and `1.0` of type `xs:decimal` are the
same key, and a string and a decimal never are.

`keyref` is checked against the union of the node tables of the
referenced `key`/`unique` constraints declared on the element and its
descendants (§3.11.5, the propagation of node tables); the conflict
rule of §3.11.5 clause 2.1 (a key that occurs in two descendant tables
is dropped) is not modelled.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD11.Validate

namespace L4Factoidal.XSD11

/-! ## The restricted XPath -/

inductive NameTest where
  | any
  | nsAny (ns : String)
  | name (n : XName)
deriving DecidableEq, Repr, Inhabited

inductive Step where
  | self
  | child (t : NameTest)
  | attr (t : NameTest)
deriving DecidableEq, Repr, Inhabited

/-- One `Path`: whether it starts with `.//`, and its steps. -/
structure RPath where
  desc : Bool
  steps : List Step
deriving Repr, Inhabited

def stripWs (s : String) : String := String.ofList (s.toList.filter (fun c => !XML.isXmlSpace c))

def parseNameTest (bs : NsBindings) (xdn : String) (t : String) : Option NameTest :=
  if t == "*" then some .any
  else match t.splitOn ":" with
    | [p, "*"] => (lookupNs bs p).map NameTest.nsAny
    | [p, l] => (lookupNs bs p).map (fun u => .name ⟨u, l⟩)
    | [l] => if l == "" then none else some (.name ⟨xdn, l⟩)
    | _ => none

def parseStep (bs : NsBindings) (xdn : String) (s : String) : Option Step :=
  if s == "." then some .self
  else if s.startsWith "@" then (parseNameTest bs "" (s.drop 1).toString).map Step.attr
  else if s.startsWith "attribute::" then (parseNameTest bs "" (s.drop 11).toString).map Step.attr
  else if s.startsWith "child::" then (parseNameTest bs xdn (s.drop 7).toString).map Step.child
  else (parseNameTest bs xdn s).map Step.child

/-- Parse a selector or field expression (`|`-separated paths). `field`
allows a final attribute step. -/
def parseRPaths (bs : NsBindings) (xdn : String) (field : Bool) (src : String) : Option (List RPath) :=
  let src := stripWs src
  if src == "" then none else
  let alts := src.splitOn "|"
  let paths := alts.map (fun a =>
    let (desc, rest) := if a.startsWith ".//" then (true, (a.drop 3).toString) else (false, a)
    let segs := rest.splitOn "/"
    if segs.any (· == "") then none
    else
      let steps := segs.map (parseStep bs xdn)
      if steps.any Option.isNone then none
      else
        let steps := steps.filterMap id
        -- an attribute step may only be the last step of a field
        let bad := steps.zipIdx.any (fun (st, i) => match st with
          | .attr _ => !field || i + 1 != steps.length
          | _ => false)
        if bad then none else some { desc, steps : RPath })
  if paths.any Option.isNone then none else some (paths.filterMap id)

/-! ## Evaluation over the PSVI -/

def NameTest.matches (t : NameTest) (n : XName) : Bool :=
  match t with
  | .any => true
  | .nsAny u => n.ns == u
  | .name m => n == m

/-- A selected item: an element or an attribute, with its PSVI info. -/
inductive Sel where
  | el (p : PNode)
  | at (a : PAttr)
deriving Inhabited

def descendantsOrSelf : Nat → PNode → List PNode
  | 0, _ => []
  | f + 1, p =>
    match p with
    | .elem .. => p :: p.kids.flatMap (descendantsOrSelf f)
    | _ => []

def elemKids (p : PNode) : List PNode :=
  p.kids.filter (fun k => match k with | .elem .. => true | _ => false)

def evalSteps : List Step → List Sel → List Sel
  | [], cur => cur
  | st :: rest, cur =>
    let next := cur.flatMap (fun c =>
      match c, st with
      | .el p, .self => [Sel.el p]
      | .el p, .child t => (elemKids p).filterMap (fun k =>
          match k.name? with
          | some n => if t.matches n then some (Sel.el k) else none
          | none => none)
      | .el p, .attr t => (p.attrs.filter (fun a => t.matches a.name && a.name.ns != xsiNS)).map Sel.at
      | .at _, _ => [])
    evalSteps rest next

def evalRPath (p : PNode) (rp : RPath) : List Sel :=
  let starts := if rp.desc then descendantsOrSelf 10000 p else [p]
  evalSteps rp.steps (starts.map Sel.el)

def evalRPaths (p : PNode) (rps : List RPath) : List Sel := rps.flatMap (evalRPath p)

def Sel.value? (s : Schema) : Sel → Option XSD.Val
  | .el p => match p.info? with
    | some i => if i.nilled then none else
        -- only simple values are key components (§3.11.4 clause 3)
        match i.typ with
        | some t => if (s.simpleOf? t).isSome then i.value else none
        | none => none
    | none => none
  | .at a => a.info.value

/-- A key sequence: `none` when a field selects nothing; an error when a
field selects more than one node or a node with no simple value. -/
def keySeq (s : Schema) (fields : List (List RPath)) (target : PNode) : Except String (Option (List XSD.Val)) :=
  fields.foldlM (fun acc f =>
    match acc with
    | none => pure none
    | some vs =>
      match evalRPaths target f with
      | [] => pure none
      | [x] => match x.value? s with
        | some v => pure (some (vs ++ [v]))
        | none => .error "a field selects a node with no simple typed value"
      | _ => .error "a field selects more than one node") (some [])

def keyEq (a b : List XSD.Val) : Bool := XSD.valsEqualOrIdentical a b

/-- The key sequences of an identity constraint on element `p` (the
`qualified node set` of §3.11.4), with the errors found. -/
def idcTable (s : Schema) (d : IDC) (p : PNode) : List (List XSD.Val) × List String :=
  match parseRPaths d.ns d.xpathDefaultNs false d.selector,
        d.fields.mapM (parseRPaths d.ns d.xpathDefaultNs true) with
  | some sel, some fs =>
    let targets := (evalRPaths p sel).filterMap (fun x => match x with | .el e => some e | _ => none)
    targets.foldl (fun (tbl, errs) t =>
      match keySeq s fs t with
      | .error e => (tbl, s!"{d.name.show}: {e}" :: errs)
      | .ok none =>
        if d.kind == .key then (tbl, s!"key {d.name.show}: a field selects nothing" :: errs)
        else (tbl, errs)
      | .ok (some ks) =>
        if d.kind != .keyref && tbl.any (keyEq ks) then
          (tbl, s!"{d.name.show}: duplicate key" :: errs)
        else (tbl ++ [ks], errs)) ([], [])
  | _, _ => ([], [s!"{d.name.show}: selector or field is not in the restricted XPath subset"])

/-- Check every identity constraint in the PSVI tree. -/
def checkIdcs (s : Schema) (root : PNode) : List String :=
  let all := descendantsOrSelf 10000 root
  all.flatMap (fun p =>
    match p.info? with
    | some i =>
      match i.decl with
      | some di =>
        (s.elem di).idcs.flatMap (fun j =>
          let d := s.idcs.getD j default
          let (tbl, errs) := idcTable s d p
          if d.kind == .keyref then
            match d.refer >>= (fun r => s.gIdcs.lookup r) with
            | none => errs
            | some rj =>
              let rd := s.idcs.getD rj default
              -- the referenced tables on this element and its descendants
              let refTbl := (descendantsOrSelf 10000 p).flatMap (fun q =>
                match q.info? >>= (·.decl) with
                | some qd => if (s.elem qd).idcs.contains rj then (idcTable s rd q).1 else []
                | none => [])
              errs ++ (tbl.filter (fun ks => !refTbl.any (keyEq ks))).map
                (fun _ => s!"keyref {d.name.show}: no matching key")
          else errs)
      | none => []
    | none => [])

/-! ## Assessment with identity constraints -/

/-- The schema location hints of an instance's document element. -/
def schemaHints (root : XML.Node) : List String :=
  match root with
  | .element _ attrs _ =>
    let bs := instBindings [] attrs
    let sl := (xsiAttrVal bs attrs "schemaLocation").map XSD.qnameList |>.getD []
    let rec pairs : List String → List String
      | _ :: loc :: rest => loc :: pairs rest
      | _ => []
    pairs sl ++ ((xsiAttrVal bs attrs "noNamespaceSchemaLocation").map XSD.qnameList |>.getD [])
  | _ => []

/-- Assess a document: `assessRoot`, then the identity constraints. -/
def assessDoc (s : Schema) (h : Hooks) (d : XML.Document) : Assessment :=
  let a := assessRoot s h d.root
  let errs := checkIdcs s a.root
  { a with valid := a.valid && errs.isEmpty, errors := errs ++ a.errors }

end L4Factoidal.XSD11
