/-
L4Factoidal.XPath4.Doc — XDM 4.0 NODES over the project's XML parse
tree (`L4Factoidal.XML.Document`).

A document is flattened into a TABLE of node records in document order
(XDM 4.0 §2.5: an element, then its namespace and attribute nodes, then
its children). A node is `(document, index)`; document order is index
order; a subtree is the index range `[i, last i]`. The axes are then
index arithmetic and parent links, with no re-walking of the tree.

Names are expanded with the in-scope namespace declarations (Namespaces
in XML 1.0 §6). Adjacent text and CDATA nodes are merged into one text
node (XDM 4.0 §6.7.1: no two adjacent text nodes).

Not modelled: namespace nodes as items on the `namespace` axis (the
axis returns the in-scope bindings as records), type annotations from
schema validation, `is-id`/`is-idrefs`, base URIs other than the
document URI.
-/
import L4Factoidal.XPath4.Syntax
import L4Factoidal.XML.Parser

namespace L4Factoidal.XPath4

open L4Factoidal.XML

def splitName (n : String) : String × String :=
  match n.splitOn ":" with
  | [p, l] => (p, l)
  | _ => ("", n)

/-- Merge adjacent text/CDATA children, and drop empty text. -/
def mergeText : List Node → List Node
  | [] => []
  | n :: rest =>
    let rest' := mergeText rest
    match n with
    | .text a | .cdata a =>
      match rest' with
      | .text b :: r => .text (a ++ b) :: r
      | r => if a == "" then r else .text a :: r
    | other => other :: rest'

abbrev B := StateM (Array NRec)

def pushRec (r : NRec) : B Nat := do
  let a ← get
  set (a.push r)
  pure a.size

def setRec (i : Nat) (f : NRec → NRec) : B Unit :=
  modify (fun a => if h : i < a.size then a.set i (f a[i]) else a)

def buildNode : Nat → Option Nat → List (String × String) → Node → B (Option Nat)
  | 0, _, _, _ => pure none
  | f + 1, par, scope, n =>
    match n with
    | .text s | .cdata s => do
        let i ← pushRec { kind := .text, value := s, parent := par }
        setRec i (fun r => { r with last := i })
        pure (some i)
    | .comment b => do
        let i ← pushRec { kind := .comment, value := b, parent := par }
        setRec i (fun r => { r with last := i })
        pure (some i)
    | .pi t d => do
        let i ← pushRec { kind := .pi, name := { uri := "", loc := t }, value := d, parent := par }
        setRec i (fun r => { r with last := i })
        pure (some i)
    | .element tag attrs kids => do
        -- namespace declarations first
        let scope := attrs.foldl (fun sc a =>
          if a.name == "xmlns" then ("", a.value) :: sc
          else if a.name.startsWith "xmlns:" then
            ((splitName a.name).2, a.value) :: sc
          else sc) scope
        let (p, l) := splitName tag
        let uri := (scope.lookup p).getD (if p == "xml" then nsXML else "")
        let i ← pushRec { kind := .element, name := { uri, loc := l, pfx := p }, parent := par,
                          inscope := scope }
        let mut ats : Array Nat := #[]
        for a in attrs do
          if a.name == "xmlns" || a.name.startsWith "xmlns:" then continue
          let (ap, al) := splitName a.name
          let auri := if ap == "" then "" else if ap == "xml" then nsXML else (scope.lookup ap).getD ""
          let j ← pushRec { kind := .attribute, name := { uri := auri, loc := al, pfx := ap },
                            value := a.value, parent := some i }
          setRec j (fun r => { r with last := j })
          ats := ats.push j
        let mut cs : Array Nat := #[]
        for k in mergeText kids do
          match ← buildNode f (some i) scope k with
          | some j => cs := cs.push j
          | none => pure ()
        let sz := (← get).size
        setRec i (fun r => { r with children := cs, attrs := ats, last := sz - 1 })
        pure (some i)

/-- A document node whose children are `ns` (a document's prolog, element
    and epilog, or the content of a parsed fragment). -/
def Doc.ofNodes (ns : List Node) (uri : String := "") : Doc :=
  let act : B Unit := do
    let i ← pushRec { kind := .document }
    let mut cs : Array Nat := #[]
    for k in mergeText ns do
      match ← buildNode 100000 (some i) [("xml", nsXML)] k with
      | some j => cs := cs.push j
      | none => pure ()
    let sz := (← get).size
    setRec i (fun r => { r with children := cs, last := sz - 1 })
  let ((), a) := act.run #[]
  { nodes := a, uri }

def Doc.ofDocument (d : Document) (uri : String := "") : Doc :=
  let base := Doc.ofNodes d.children uri
  match d.doctype with
  | some dt =>
    { base with idAttrs := dt.idAttrs,
                idrefAttrs := (dt.attDecls.filter (fun a => a.type == AttType.IDREF || a.type == AttType.IDREFS)).map
                  (fun a => (a.element, a.name)) }
  | none => base

def Doc.ofString (s : String) (uri : String := "") : Except String Doc :=
  match parseXML s with
  | .ok d => .ok (Doc.ofDocument d uri)
  | .error e => .error (reprStr e)

def Doc.get (d : Doc) (i : Nat) : NRec := d.nodes.getD i default

def Doc.textFrom (d : Doc) (last : Nat) : Nat → Nat → String → String
  | 0, _, acc => acc
  | f + 1, j, acc =>
    if j > last then acc
    else
      let x := d.get j
      d.textFrom last f (j + 1) (if x.kind == .text then acc ++ x.value else acc)

/-- The string value (XDM 4.0 §5.13). -/
def Doc.stringValue (d : Doc) (i : Nat) : String :=
  let r := d.get i
  match r.kind with
  | .element | .document => d.textFrom r.last (r.last - i) (i + 1) ""
  | _ => r.value

end L4Factoidal.XPath4
