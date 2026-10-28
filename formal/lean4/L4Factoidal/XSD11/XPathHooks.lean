/-
L4Factoidal.XSD11.XPathHooks — the bridge between XML Schema 1.1
validation and `L4Factoidal.XPath4` (XDM 4.0, XPath 4.0):

  * `psviDoc`: the XDM 4.0 document of a PSVI tree (XDM 4.0 §3.3,
    "Construction from a PSVI"): element and attribute nodes carry the
    type annotation (`NRec.tann`) and the typed value (`NRec.tval`) that
    validation gave them; attributes supplied by a default are present;
  * `xpathHooks`: type alternatives (§3.12.4) and assertions (§3.13.4)
    evaluated by the XPath 4.0 evaluator. XPath 4.0 is a superset of the
    XPath 2.0 that Part 1 names for these tests.

The typed values are built by `XPath4.castFromString` from the
schema-normalized value and the built-in type the simple type is
derived from (for a list, item by item; for a union, the first member
type that accepts the value, §3.16.4 clause 3). `XSD11/Theorems.lean`
states the agreement with the XSD value (`atomsOf_valid`).

Known differences, each a qt4tests or xsdtests case that does not pass:
an assertion's context element has a document node as parent (Part 1
§3.13.4.1 asks for a parentless element).

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD11.SchemaForSchemas
import L4Factoidal.XPath4.Eval

namespace L4Factoidal.XSD11

open L4Factoidal.XPath4 (Atomic AType QN Doc NRec Env Item NodeRef castFromString)

/-! ## Typed values -/

/-- The XDM atomic values of a schema-normalized literal of simple type
`body` (a Part 2 type). `none` when the literal is not valid. -/
def atomsOfBody (ns : String → Option String) : Nat → XSD.SimpleType → String → Option (List Atomic)
  | 0, _, _ => none
  | f + 1, t, lit =>
    match t with
    | .atomic b _ =>
      if b == .anySimpleType || b == .anyAtomicType then some [Atomic.untypedOf lit]
      else match castFromString lit (.b b) ns with
        | .ok a => some [a]
        | .error _ => none
    | .list item _ =>
      let toks := (lit.splitOn " ").filter (· != "")
      let rs := toks.map (atomsOfBody ns f item)
      if rs.all Option.isSome then some (rs.filterMap id).flatten else none
    | .union ms _ =>
      (ms.find? (fun m => (XSD.valueOf m lit).isSome)).bind (fun m => atomsOfBody ns f m lit)

/-- The typed value of a node of simple type (or simple content) `t`. -/
def atomsOf (s : Schema) (ns : String → Option String) (t : Nat) (norm : String) : Option (List Atomic) :=
  match s.simpleOf? t with
  | some sd => atomsOfBody ns 16 sd.body norm
  | none => none

def xnameQN (n : XName) : QN := { uri := n.ns, loc := n.loc }

/-- The type annotation of a type definition (an anonymous type gets a
name in no namespace that no schema document can write). -/
def Schema.typeQN (s : Schema) (t : Nat) : QN :=
  match (s.type t).name with
  | some n => xnameQN n
  | none => { uri := "", loc := s!"#anonymous-{t}" }

/-! ## The XDM document of a PSVI -/

mutual
/-- The tree XDM is constructed from: the input with the defaulted
attributes and the default text added. -/
def PNode.toXdm : PNode → XML.Node
  | .elem tag attrs kids _ _ defs dt =>
    .element tag (attrs.map (·.attr) ++ defs.map (·.attr))
      (match dt with
       | some t => [.text t]
       | none => PNode.toXdmList kids)
  | .text s => .text s
  | .cdata s => .cdata s
  | .comment s => .comment s
  | .pi t d => .pi t d

def PNode.toXdmList : List PNode → List XML.Node
  | [] => []
  | p :: ps => p.toXdm :: PNode.toXdmList ps
end

def isElemP : PNode → Bool
  | .elem .. => true
  | _ => false

def annotRec (s : Schema) (r : NRec) (i : PInfo) : NRec :=
  let nsr := fun (p : String) => r.inscope.lookup p
  match i.typ with
  | none => r
  | some t =>
    let tval := match i.normalized with
      | some norm => if i.nilled then some [] else atomsOf s nsr t norm
      | none => if i.nilled then some [] else none
    let elemOnly : Bool := match s.type t with
      | .complex c => match c.content with
        | .elems _ false => true
        | .empty => false
        | _ => false
      | _ => false
    { r with tann := some (s.typeQN t), tval, nilled := i.nilled,
             noTypedValue := elemOnly && r.kind == .element }

/-- Copy the PSVI annotations onto the node records of `d`, starting at
record `idx` for the PSVI node `p`. -/
def annotate (s : Schema) : Nat → Array NRec → Nat → PNode → Array NRec
  | 0, a, _, _ => a
  | f + 1, a, idx, p =>
    match p with
    | .elem _ attrs kids _ info defs _ =>
      if h : idx < a.size then
        let r := a[idx]
        let inscope := r.inscope
        let a := a.set idx (annotRec s r info)
        -- attributes: the record order is the non-namespace attributes in order
        let pas := (attrs ++ defs).filter (fun x => !isNsDecl x.attr)
        let a := (r.attrs.toList.zip pas).foldl (fun a (j, pa) =>
          if hj : j < a.size then a.set j (annotRec s { a[j] with inscope := inscope } pa.info) else a) a
        let kidRecs := r.children.toList.filter (fun j => (a.getD j default).kind == .element)
        (kidRecs.zip (kids.filter isElemP)).foldl (fun a (j, k) => annotate s f a j k) a
      else a
    | _ => a

/-- The XDM 4.0 document of a PSVI tree, with type annotations and typed
values. Record 1 is the element (record 0 is the document node). -/
def psviDoc (s : Schema) (p : PNode) (uri : String := "") : Doc :=
  let d := Doc.ofNodes [p.toXdm] uri
  { d with nodes := annotate s 100000 d.nodes 1 p }

/-! ## The hooks -/

/-- The static namespaces of an XPath test: the in-scope prefixes of the
schema document, and `xpathDefaultNamespace` as the default element
namespace (§3.13.2, §3.12.2). -/
def nsForXPath (bs : NsBindings) (xdn : String := "") : List (String × String) :=
  (if xdn == "" then [] else [("", xdn)]) ++ (bs.filter (fun b => b.1 != "")).eraseDups

def evalTest (env : Env) (expr : String) : Option Bool :=
  match L4Factoidal.XPath4.evalString expr env with
  | .ok seq => match L4Factoidal.XPath4.ebv seq with
    | .ok b => some b
    | .error _ => some false
  | .error e =>
    -- a dynamic error in an assertion or alternative test is "false"
    -- (§3.13.4.1 clause 2, §3.12.4); a static error is not decided here.
    if e.code.startsWith "XPST" then none else some false

def xpathHooks : Hooks :=
  { test := fun s expr bs xdn p =>
      let d := psviDoc s p
      let value : List Item := match p.info? with
        | some i => match i.typ, i.normalized with
          | some t, some norm => ((atomsOf s (fun pr => lookupNs bs pr) t norm).getD []).map Item.atom
          | _, _ => []
        | none => []
      let env : Env := { docs := #[d], ctx := some [.node ⟨0, 1, none⟩], pos := 1, size := 1,
                         ns := nsForXPath bs xdn, vars := [({ uri := "", loc := "value" }, value)] }
      evalTest env expr,
    testValue := fun s expr bs xdn t norm =>
      let value : List Item := ((atomsOf s (fun pr => lookupNs bs pr) t norm).getD []).map Item.atom
      let env : Env := { ns := nsForXPath bs xdn, vars := [({ uri := "", loc := "value" }, value)] }
      evalTest env expr }

end L4Factoidal.XSD11
