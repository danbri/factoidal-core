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
import L4Factoidal.XPath4.BaseUri

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

/-- The name of a content attribute that is not an attribute: the first
    item of the content of an `Out.elem` that keeps the base URI of the
    node it copies (`xsl:copy`, §11.9.1). `buildElem` drops it; it sets
    the base URI of the tree when the element is the root. -/
def baseMarkQ : QN := { uri := "urn:x-factoidal:internal", loc := "base-uri" }

/-- The name of a content attribute that is not an attribute: the
    children of the element do not inherit the namespaces it declares
    (`inherit-namespaces="no"`, §11.9.1). `buildElem` drops it. -/
def noInheritQ : QN := { uri := "urn:x-factoidal:internal", loc := "no-inherit" }

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
  /-- The type annotations of attributes added as nodes (§25.1.1): the
      record of the attribute node, by name. -/
  attrAnn : List (QN × NRec) := []
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
      | .attribute => do
          let nm' ← nm.addAttr r.name r.value
          let ann := nm'.attrAnn.filter (fun (q, _) => !(q == r.name))
          pure { nm' with attrAnn := if r.tann.isSome then (r.name, r) :: ann else ann }
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

/-- The record of a node without its schema type annotation
    (`validation="strip"`, §25.1.1): `xs:untyped` or `xs:untypedAtomic`,
    the typed value is the string value, not nilled. -/
def _root_.L4Factoidal.XPath4.NRec.untyped (r : NRec) : NRec :=
  { r with tann := none, tval := none, nilled := false, noTypedValue := false }

/-- Copy the subtree of `src` (one loop over its index range) under
    `par`; `pscope` is the namespace scope of the new parent. Returns
    the index of the copy. `keep`: the copies keep their type
    annotations (`validation="preserve"`); otherwise they are untyped
    (`validation="strip"`, §25.1.1). -/
def copyTree (env : Env) (src : NodeRef) (par : Option Nat) (pscope : List (String × String))
    (copyNs : Bool) (keep : Bool := true) : TB Nat := do
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
    -- namespace fixup (§5.7.3): an element in no namespace does not
    -- inherit a default namespace from its new parent
    let sc := if x.kind == .element && x.name.uri == "" && (sc.lookup "").getD "" != "" then ("", "") :: sc else sc
    let newPar := par'
    let rec' : NRec := { x with parent := newPar, children := x.children.map shift, attrs := x.attrs.map shift, last := shift (max x.last i), inscope := sc }
    let _ ← tPush (if keep then rec' else rec'.untyped)
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
/-- Build an element under `par`. `keep`: the nodes copied into it keep
    their type annotations (`validation="preserve"`, §25.1.1); the
    elements built inside it are built with `keep` false. -/
def buildElem (env : Env) (keep : Bool) : Nat → Option Nat → List (String × String) → QN →
    List (String × String) → List Out → TB Nat
  | 0, _, _, _, _, _ => throw { code := "FOER0000", msg := "result tree too deep" }
  | f + 1, par, pscope, name, decls, content => do
    let nm ← normContent env content
    let noInherit := nm.attrs.any (fun (q, _) => q == noInheritQ)
    let nm := { nm with attrs := nm.attrs.filter (fun (q, _) => !(q == baseMarkQ) && !(q == noInheritQ)) }
    -- §5.7.1: two namespace nodes that bind one prefix to two URIs
    for (p, u) in nm.nss do
      match decls.lookup p with
      | some u' => if u' != u then
          throw { code := "XTDE0430", msg := "two namespace nodes bind prefix '" ++ p ++ "' to different URIs" }
      | none => pure ()
    let scope0 := (decls ++ nm.nss).reverse ++ pscope
    -- a namespace node of the element that binds the prefix of its name
    -- to another URI: the element gets another prefix (§5.7.3)
    let name := match nm.nss.lookup name.pfx with
      | some u => if u != name.uri && name.uri != "" && name.pfx != "xml" then
          { name with pfx := freePrefix scope0 name.uri "" } else name
      | none => name
    let (name, scope1) := fixElemName name scope0
    let mut scope := scope1
    let mut ats : Array (QN × String) := #[]
    for (q, v) in nm.attrs.toList do
      let (q', sc') := fixAttrName q scope
      scope := sc'
      ats := ats.push (q', v)
    let i ← tPush { kind := .element, name, parent := par, inscope := scope }
    -- the scope the children start from: with inherit-namespaces="no"
    -- they do not get the bindings of this element, only those that it
    -- inherits itself (as when the element is copied into its parent)
    let kscope := if noInherit then pscope else scope
    let mut aIdx : Array Nat := #[]
    for (q, v) in ats.toList do
      let j ← tPush { kind := .attribute, name := q, value := v, parent := some i }
      tSet j (fun r => { r with last := j })
      if keep then
        if let some (_, ar) := nm.attrAnn.find? (fun (x, _) => x == q) then
          tSet j (fun r => { r with tann := ar.tann, tval := ar.tval })
      aIdx := aIdx.push j
    let mut cs : Array Nat := #[]
    for k in nm.kids.toList do
      match k with
      | .text s =>
          let j ← tPush { kind := .text, value := s, parent := some i }
          tSet j (fun r => { r with last := j })
          cs := cs.push j
      | .node n => cs := cs.push (← copyTree env n (some i) kscope true keep)
      | .out o =>
          match ← buildKid env f (some i) kscope o with
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
    | .elem q ds cs => some <$> buildElem env false f par scope q ds cs
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

/-- Build a document node with content `cs` (`keep` as for `buildElem`). -/
def buildDoc (env : Env) (cs : List Out) (keep : Bool := false) : TB Unit := do
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
    | .node n => kids := kids.push (← copyTree env n (some i) scope true keep)
    | .out o =>
        match ← buildKid env 100000 (some i) scope o with
        | some j => kids := kids.push j
        | none => pure ()
  let sz := (← get).size
  tSet i (fun r => { r with children := kids, last := sz - 1 })

/-- The XDM item for one `Out`, as a new tree with document number
    `id` when it is a node that is being built. `keep`: the nodes copied
    into the new node keep their type annotations (§25.1.1). -/
def materializeK (keep : Bool) (env : Env) (id : Nat) (o : Out) : M Item := do
  -- the base URI of a new tree is the static base URI where it is made
  -- (§5.7.1, §9.4), unless the node keeps that of the node it copies
  let mkItem (act : TB Unit) (uri : String := "") (base : String := env.baseUri) : M Item := do
    let ((), a) ← act.run #[]
    pure (.node { doc := id, idx := 0, rt := some { nodes := a, uri, baseUri := (if uri != "" then "" else base) } })
  match o with
  | .item i => pure i
  | .elem q ds cs =>
      let base := match cs with
        | .attr bq v :: _ => if bq == baseMarkQ then v else env.baseUri
        | _ => env.baseUri
      mkItem (do let _ ← buildElem env keep 100000 none [("xml", nsXML)] q ds cs) "" base
  | .doc cs uri => mkItem (buildDoc env cs keep) uri
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

/-- `materializeK`: the nodes copied into a new node are untyped
    (`validation="strip"`, the default). -/
def materialize (env : Env) (id : Nat) (o : Out) : M Item := materializeK false env id o

/-- A deep copy of an existing node as a new tree (`xsl:copy-of`,
    `fn:copy-of`); `keep` false: the copy is untyped. -/
def copyAsTree (env : Env) (id : Nat) (n : NodeRef) (copyNs : Bool := true) (keep : Bool := true) : M Item := do
  let act : TB Unit := do let _ ← copyTree env n none [("xml", nsXML)] copyNs keep
  let ((), a) ← act.run #[]
  let d := env.doc n
  -- §11.9.2: the copy has the base URI of the node, except that its
  -- `xml:base` attribute (copied with it) is resolved against the
  -- static base URI
  let base := if (env.xmlBaseOf n).isSome && env.baseUri != "" then env.baseUri
    else (env.baseUriOf n).getD ""
  let uri := if n.idx == 0 then d.uri else ""
  pure (.node { doc := id, idx := 0, rt := some { nodes := a, uri, baseUri := base } })

/-- `fn:snapshot` (XSLT 4.0 §20.6.2): a deep copy of `n` in a new tree
    that also holds copies of its ancestors, each with its attributes
    and namespaces but with no other children. The result is the copy
    of `n` (the root of the new tree is a copy of the root of the old
    one, a document node or not). -/
def snapshotAsTree (env : Env) (id : Nat) (n : NodeRef) : M Item := do
  let d := env.doc n
  let r := d.get n.idx
  let anc := (env.ancestors n).reverse
  let act : TB Nat := do
    let mut par : Option Nat := none
    let mut scope : List (String × String) := [("xml", nsXML)]
    let mut target : Option Nat := none
    let mut made : Array Nat := #[]
    for a in anc do
      let ra := d.get a.idx
      let i ← tPush { ra with parent := par, children := #[], attrs := #[], last := 0 }
      made := made.push i
      let mut ats : Array Nat := #[]
      for x in ra.attrs.toList do
        let j ← tPush { d.get x with parent := some i, children := #[], attrs := #[] }
        tSet j (fun y => { y with last := j })
        ats := ats.push j
        if x == n.idx then target := some j
      tSet i (fun y => { y with attrs := ats })
      if let some p := par then tSet p (fun y => { y with children := y.children.push i })
      par := some i
      if ra.kind == .element then scope := ra.inscope ++ scope
    -- the node itself: an attribute is copied with its parent; a
    -- namespace node is one of the namespace nodes of the copied parent
    let tgt ← match target, r.kind, par with
      | some j, _, _ => pure j
      | none, .namespace, some p => pure (nsNodeIdx p ((n.idx - nsBase) % nsSlot))
      | none, _, _ => do
          let j ← copyTree env n par scope true
          if let some p := par then tSet p (fun y => { y with children := y.children.push j })
          pure j
    let sz := (← get).size
    for i in made do tSet i (fun y => { y with last := sz - 1 })
    pure tgt
  let (tgt, a) ← act.run #[]
  let root := (anc.head?).getD n
  let base := env.treeBaseUri root
  pure (.node { doc := id, idx := tgt, rt := some { nodes := a, baseUri := base } })

/-- The top level of a raw result before it becomes a result tree
    (XSLT 4.0 §26.1, Serialization 4.0 §2 steps 1 to 4): arrays are
    flattened, a map or function item is an error (SENR0001), and with an
    `item-separator` the separator stands between the items, each atomic
    value as text. -/
def Out.normalizeTop (sep : Option String) (os : List Out) : M (List Out) := do
  let mut flat : Array Out := #[]
  let mut todo : List Out := os
  for _ in [0:10000000] do
    match todo with
    | [] => break
    | o :: rest =>
      todo := rest
      match o with
      | .item (.arr ms) => todo := ms.flatten.map Out.item ++ todo
      | .item (.map _) => err "SENR0001" "a map cannot be serialized by this method"
      | .item (.fn _) => err "SENR0001" "a function item cannot be serialized by this method"
      | o => flat := flat.push o
  match sep with
  | none => pure flat.toList
  | some s =>
    pure (flat.toList.zipIdx.flatMap (fun (o, i) =>
      (if i == 0 then [] else [Out.text s]) ++
      [match o with
        | .item (.atom a) => Out.text a.str
        | o => o]))

end L4Factoidal.XSLT4
