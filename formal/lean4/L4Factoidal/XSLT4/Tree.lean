/-
L4Factoidal.XSLT4.Tree — the result of a sequence constructor, and the
construction of new XDM nodes from it.

Spec: XSLT 4.0 editor's draft (https://qt4cg.org/specifications/xslt-40/Overview.html,
read 2026-10-28), §5.7 "Sequence Constructors", §5.7.1 "Constructing
Complex Content", §5.7.2 "Constructing Simple Content"; XDM 4.0 §2.

A sequence constructor gives a list of `Out`: existing items (atomic
values, nodes of a source or temporary tree, maps, arrays, functions)
and nodes that are still being built (`Out.elem` and the others). A
node that is being built is turned into an XDM node only when a value
is needed (a variable, a function result, the final result); a child
element is never copied into its parent, it is written into the
parent's node table once. A constructed node is a new runtime document
(`NodeRef.rt`) of `XPath4.Doc` form: the node, then its attributes,
then its children, in document order.
-/
import L4Factoidal.XPath4.Eval

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

/-- An item of the result of a sequence constructor. -/
inductive Out where
  /-- An existing item. -/
  | item (i : Item)
  /-- An element to build: name, namespace bindings it declares
      (prefix, URI), content. -/
  | elem (name : QN) (decls : List (String × String)) (content : List Out)
  | attr (name : QN) (value : String)
  | text (s : String)
  | comment (s : String)
  | pi (target value : String)
  | nsN (pfx uri : String)
  /-- A document node to build: content, document URI. -/
  | doc (content : List Out) (uri : String)
deriving Inhabited

def Out.ofSeq (s : Seq) : List Out := s.map Out.item

/-! ## Normalised content (§5.7.1) -/

/-- A child of a node that is being built. -/
inductive Kid where
  | text (s : String)
  /-- A node to copy (element, text, comment, processing instruction). -/
  | node (n : NodeRef)
  /-- An element, comment or processing instruction to build. -/
  | out (o : Out)
deriving Inhabited

structure Norm where
  attrs : Array (QN × String) := #[]
  nss : List (String × String) := []
  kids : Array Kid := #[]
  /-- The last thing added was an atomic value (for the space between
      adjacent atomic values). -/
  lastAtom : Bool := false
deriving Inhabited

def Norm.pushText (nm : Norm) (s : String) : Norm :=
  if s == "" then nm
  else match nm.kids.back? with
    | some (.text t) => { nm with kids := nm.kids.pop.push (.text (t ++ s)) }
    | _ => { nm with kids := nm.kids.push (.text s) }

def Norm.addAttr (nm : Norm) (q : QN) (v : String) : M Norm :=
  if !nm.kids.isEmpty then
    err "XTDE0410" "an attribute node was added to an element after a child node"
  else
    let as := nm.attrs.filter (fun (x, _) => !(x == q))
    pure { nm with attrs := as.push (q, v), lastAtom := false }

def Norm.addNs (nm : Norm) (p u : String) : M Norm :=
  if !nm.kids.isEmpty then
    err "XTDE0410" "a namespace node was added to an element after a child node"
  else match nm.nss.lookup p with
    | some u' => if u' == u then pure nm
                 else err "XTDE0430" ("two namespace nodes bind prefix '" ++ p ++ "' to different URIs")
    | none => pure { nm with nss := nm.nss ++ [(p, u)], lastAtom := false }

/-- Add one item of content. -/
def normItem (env : Env) : Nat → Norm → Item → M Norm
  | 0, _, _ => err "FOER0000" "content too deep"
  | f + 1, nm, i =>
    match i with
    | .atom a =>
        let nm := if nm.lastAtom then nm.pushText " " else nm
        pure { (nm.pushText a.str) with lastAtom := true }
    | .node n =>
      let r := env.nrec n
      match r.kind with
      | .document => do
          let mut nm := { nm with lastAtom := false }
          for c in r.children.toList do
            nm ← normItem env f nm (.node (n.at c))
          pure nm
      | .attribute => nm.addAttr r.name r.value
      | .namespace => nm.addNs r.name.loc r.value
      | .text => pure { (nm.pushText r.value) with lastAtom := false }
      | _ => pure { nm with kids := nm.kids.push (.node n), lastAtom := false }
    | .arr ms => do
        let mut nm := nm
        for m in ms do
          for x in m do nm ← normItem env f nm x
        pure nm
    | .jnode _ _ v _ => do
        -- a JNode stands for its ·jvalue·
        let mut nm := nm
        for x in v do nm ← normItem env f nm x
        pure nm
    | .map _ => err "XTDE0450" "a map cannot be added to the content of a node"
    | .fn _ => err "XTDE0450" "a function item cannot be added to the content of a node"

def normOut (env : Env) : Nat → Norm → Out → M Norm
  | 0, _, _ => err "FOER0000" "content too deep"
  | f + 1, nm, o =>
    match o with
    | .item i => normItem env 10000 nm i
    | .attr q v => nm.addAttr q v
    | .nsN p u => nm.addNs p u
    | .text s => pure { (nm.pushText s) with lastAtom := false }
    | .doc cs _ => do
        let mut nm := { nm with lastAtom := false }
        for c in cs do nm ← normOut env f nm c
        pure nm
    | other => pure { nm with kids := nm.kids.push (.out other), lastAtom := false }

def normContent (env : Env) (cs : List Out) : M Norm := do
  let mut nm : Norm := {}
  for c in cs do nm ← normOut env 100000 nm c
  pure nm

/-! ## Building node tables -/

abbrev TB := StateT (Array NRec) M

def tPush (r : NRec) : TB Nat := do
  let a ← get
  set (a.push r)
  pure a.size

def tSet (i : Nat) (f : NRec → NRec) : TB Unit :=
  modify (fun a => if h : i < a.size then a.set i (f a[i]) else a)

/-- The namespace bindings a node needs for its own name and the names
    of its attributes (for `copy-namespaces="no"`). -/
def neededNs (d : Doc) (r : NRec) : List (String × String) :=
  let own := if r.name.uri != "" || r.name.pfx != "" then [(r.name.pfx, r.name.uri)] else []
  own ++ r.attrs.toList.filterMap (fun a =>
    let ar := d.get a
    if ar.name.uri != "" && ar.name.pfx != "" then some (ar.name.pfx, ar.name.uri) else none)

/-- Copy the subtree of `src` (one loop over its index range) under
    `par`; `pscope` is the namespace scope of the new parent. Returns
    the index of the copy. -/
def copyTree (env : Env) (src : NodeRef) (par : Option Nat) (pscope : List (String × String))
    (copyNs : Bool) : TB Nat := do
  let d := env.doc src
  let r := d.get src.idx
  let lo := src.idx
  let hi := if r.kind == .element || r.kind == .document then max r.last lo else lo
  let base := (← get).size
  let shift (j : Nat) : Nat := j - lo + base
  for i in [lo:hi+1] do
    let x := d.get i
    let par' := if i == lo then par else x.parent.map shift
    let sc := if x.kind == .element then
        (if copyNs then x.inscope ++ pscope else neededNs d x ++ pscope) else []
    let newPar := par'
    let rec' : NRec := { x with parent := newPar, children := x.children.map shift, attrs := x.attrs.map shift, last := shift (max x.last i), inscope := sc }
    let _ ← tPush rec'
  pure base

/-- A prefix for namespace `uri` that is free in `scope` (`ns0`,
    `ns1`, ...), unless `scope` already binds a non-empty prefix to it. -/
def freePrefix (scope : List (String × String)) (uri : String) (want : String) : String := Id.run do
  if want != "" && want != "xmlns" then
    match scope.lookup want with
    | none => return want
    | some u => if u == uri then return want
  match scope.find? (fun (p, u) => u == uri && p != "" && scope.lookup p == some u) with
  | some (p, _) => return p
  | none =>
    for k in [0:10000] do
      let p := "ns" ++ toString k
      if (scope.lookup p).isNone then return p
    return "ns"

/-- Namespace fixup (XSLT 4.0 §5.7.3) for an element name: the scope
    gets a binding for the element's prefix. -/
def fixElemName (q : QN) (scope : List (String × String)) : QN × List (String × String) :=
  if q.pfx == "xml" then (q, scope) else
  match scope.lookup q.pfx with
  | some u =>
      if u == q.uri then (q, scope)
      else if q.pfx == "" then (q, ("", q.uri) :: scope)
      else (q, (q.pfx, q.uri) :: scope)
  | none =>
      if q.uri == "" && q.pfx == "" then (q, scope)
      else (q, (q.pfx, q.uri) :: scope)

/-- Namespace fixup for an attribute name: a namespaced attribute needs
    a non-empty prefix bound to its URI. -/
def fixAttrName (q : QN) (scope : List (String × String)) : QN × List (String × String) :=
  if q.uri == "" then ({ q with pfx := "" }, scope)
  else if q.uri == nsXML then ({ q with pfx := "xml" }, scope)
  else
    let p := freePrefix scope q.uri q.pfx
    let q' := { q with pfx := p }
    if scope.lookup p == some q.uri then (q', scope) else (q', (p, q.uri) :: scope)

mutual
/-- Build an element under `par`. -/
def buildElem (env : Env) : Nat → Option Nat → List (String × String) → QN →
    List (String × String) → List Out → TB Nat
  | 0, _, _, _, _, _ => throw { code := "FOER0000", msg := "result tree too deep" }
  | f + 1, par, pscope, name, decls, content => do
    let nm ← normContent env content
    let scope0 := (decls ++ nm.nss).reverse ++ pscope
    let (name, scope1) := fixElemName name scope0
    let mut scope := scope1
    let mut ats : Array (QN × String) := #[]
    for (q, v) in nm.attrs.toList do
      let (q', sc') := fixAttrName q scope
      scope := sc'
      ats := ats.push (q', v)
    let i ← tPush { kind := .element, name, parent := par, inscope := scope }
    let mut aIdx : Array Nat := #[]
    for (q, v) in ats.toList do
      let j ← tPush { kind := .attribute, name := q, value := v, parent := some i }
      tSet j (fun r => { r with last := j })
      aIdx := aIdx.push j
    let mut cs : Array Nat := #[]
    for k in nm.kids.toList do
      match k with
      | .text s =>
          let j ← tPush { kind := .text, value := s, parent := some i }
          tSet j (fun r => { r with last := j })
          cs := cs.push j
      | .node n => cs := cs.push (← copyTree env n (some i) scope true)
      | .out o =>
          match ← buildKid env f (some i) scope o with
          | some j => cs := cs.push j
          | none => pure ()
    let sz := (← get).size
    tSet i (fun r => { r with attrs := aIdx, children := cs, last := sz - 1 })
    pure i

/-- Build one child that `normContent` left as `Kid.out`. -/
def buildKid (env : Env) : Nat → Option Nat → List (String × String) → Out → TB (Option Nat)
  | 0, _, _, _ => throw { code := "FOER0000", msg := "result tree too deep" }
  | f + 1, par, scope, o =>
    match o with
    | .elem q ds cs => some <$> buildElem env f par scope q ds cs
    | .comment s => do
        let j ← tPush { kind := .comment, value := s, parent := par }
        tSet j (fun r => { r with last := j }); pure (some j)
    | .pi t v => do
        let j ← tPush { kind := .pi, name := { uri := "", loc := t }, value := v, parent := par }
        tSet j (fun r => { r with last := j }); pure (some j)
    | .text s => do
        if s == "" then pure none else
        let j ← tPush { kind := .text, value := s, parent := par }
        tSet j (fun r => { r with last := j }); pure (some j)
    | _ => pure none
end

/-- Build a document node with content `cs`. -/
def buildDoc (env : Env) (cs : List Out) : TB Unit := do
  let nm ← normContent env cs
  if !nm.attrs.isEmpty then
    throw { code := "XTDE0420", msg := "an attribute node cannot be a child of a document node" }
  if !nm.nss.isEmpty then
    throw { code := "XTDE0420", msg := "a namespace node cannot be a child of a document node" }
  let i ← tPush { kind := .document }
  let scope := [("xml", nsXML)]
  let mut kids : Array Nat := #[]
  for k in nm.kids.toList do
    match k with
    | .text s =>
        let j ← tPush { kind := .text, value := s, parent := some i }
        tSet j (fun r => { r with last := j })
        kids := kids.push j
    | .node n => kids := kids.push (← copyTree env n (some i) scope true)
    | .out o =>
        match ← buildKid env 100000 (some i) scope o with
        | some j => kids := kids.push j
        | none => pure ()
  let sz := (← get).size
  tSet i (fun r => { r with children := kids, last := sz - 1 })

/-- The XDM item for one `Out`, as a new tree with document number
    `id` when it is a node that is being built. -/
def materialize (env : Env) (id : Nat) (o : Out) : M Item := do
  let mkItem (act : TB Unit) (uri : String := "") : M Item := do
    let ((), a) ← act.run #[]
    pure (.node { doc := id, idx := 0, rt := some { nodes := a, uri } })
  match o with
  | .item i => pure i
  | .elem q ds cs => mkItem (do let _ ← buildElem env 100000 none [("xml", nsXML)] q ds cs)
  | .doc cs uri => mkItem (buildDoc env cs) uri
  | .attr q v =>
      let (q', _) := fixAttrName q []
      mkItem (do let j ← tPush { kind := .attribute, name := q', value := v }; tSet j (fun r => { r with last := j }))
  | .text s => mkItem (do let j ← tPush { kind := .text, value := s }; tSet j (fun r => { r with last := j }))
  | .comment s => mkItem (do let j ← tPush { kind := .comment, value := s }; tSet j (fun r => { r with last := j }))
  | .pi t v => mkItem (do
      let j ← tPush { kind := .pi, name := { uri := "", loc := t }, value := v }
      tSet j (fun r => { r with last := j }))
  | .nsN p u => mkItem (do
      let j ← tPush { kind := .namespace, name := { uri := "", loc := p }, value := u }
      tSet j (fun r => { r with last := j }))

/-- A deep copy of an existing node as a new tree (`xsl:copy-of`,
    `fn:copy-of`). -/
def copyAsTree (env : Env) (id : Nat) (n : NodeRef) (copyNs : Bool := true) : M Item := do
  let act : TB Unit := do let _ ← copyTree env n none [("xml", nsXML)] copyNs
  let ((), a) ← act.run #[]
  let d := env.doc n
  pure (.node { doc := id, idx := 0, rt := some { nodes := a, uri := if n.idx == 0 then d.uri else "" } })

/-- The ancestors of node `i` of `d`, outermost first. -/
def ancestorsOf (d : Doc) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | f + 1, i, acc =>
    match (d.get i).parent with
    | some p => ancestorsOf d f p (p :: acc)
    | none => acc

/-- `fn:snapshot` (XSLT 4.0 §20.3.2): a copy of the node with its
    subtree, inside copies of its ancestors that keep their names,
    attributes and in-scope namespaces but no other children. The item is
    the copy of the node itself (for an attribute, the copy of the
    attribute on the copy of its parent). -/
def snapshotAsTree (env : Env) (id : Nat) (n : NodeRef) : M Item := do
  let d := env.doc n
  let r := d.get n.idx
  let isAttr := r.kind == .attribute || r.kind == .namespace
  let chain : List Nat :=
    if isAttr then match r.parent with
      | some p => ancestorsOf d 100000 p [] ++ [p]
      | none => []
    else ancestorsOf d 100000 n.idx []
  let act : TB Nat := do
    let mut prev : Option Nat := none
    let mut newChain : List Nat := []
    let mut attrOf : List (Nat × Nat) := []
    for a in chain do
      let ra := d.get a
      let j ← tPush { ra with parent := prev, children := #[], attrs := #[] }
      if let some p := prev then tSet p (fun x => { x with children := #[j] })
      let mut ats : Array Nat := #[]
      for ax in ra.attrs.toList do
        let k ← tPush { d.get ax with parent := some j, children := #[], attrs := #[] }
        tSet k (fun x => { x with last := k })
        ats := ats.push k
        attrOf := (ax, k) :: attrOf
      tSet j (fun x => { x with attrs := ats })
      newChain := newChain ++ [j]
      prev := some j
    let target ← if isAttr then pure ((attrOf.lookup n.idx).getD 0)
      else do
        let t ← copyTree env n prev [("xml", nsXML)] true
        if let some p := prev then tSet p (fun x => { x with children := #[t] })
        pure t
    let sz := (← get).size
    for j in newChain do tSet j (fun x => { x with last := sz - 1 })
    pure target
  let (t, a) ← act.run #[]
  pure (.node { doc := id, idx := t, rt := some { nodes := a, uri := d.uri } })

end L4Factoidal.XSLT4
