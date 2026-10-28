/-
L4Factoidal.XPath4.Update — `fn:update` (F&O 4.0 §12.5.1, new in 4.0):
a copy of a tree in which the selected nodes are replaced.

Spec: F&O 4.0 editor's draft §12.5.1 (Issue 2873, PR 2881), XDM 4.0
§8.5 (JNodes); the QT4 tests `fn/update.xml` decide where the draft is
not explicit.

The origin is `$value` if it is a node, else `fn:jtree($value)`. The
selected nodes are found with ONE call of `$select`, by node identity
(XNodes: the document and the index; JNodes: the step positions below
the root, `jposPath`). Every node of the origin's tree is then
processed once, bottom-up: its attributes and children first, then the
node itself, which is replaced by its substitution sequence when it is
selected.

XNodes are rebuilt as an `XT` tree (records of `NRec`) and flattened
into a new document table with a parentless root at index 0. JNodes are
rebuilt as values: a map, an array or a sequence from the contributions
of the children (`JC`), and a selected JNode `C` is passed to
`$replacement` as a parentless JNode that keeps its ·jkey·.

Not modelled: a fresh node identity per call. The evaluator is pure, so
two calls with the same arguments give nodes with the same identity
(tests `fn-update-xnode-115` and `-116` expect distinct nodes). Type
annotations are not kept (every XNode is untyped, as no schema
validation exists here).
-/
import L4Factoidal.XPath4.XmlParse
import Std.Data.HashSet

namespace L4Factoidal.XPath4

/-! ## XNodes -/

/-- An XNode under construction: an element or a document node with its
    attributes and children, or a leaf (attribute, text, comment,
    processing instruction). -/
inductive XT where
  | el (r : NRec) (attrs : List NRec) (kids : List XT)
  | lf (r : NRec)

instance : Inhabited XT := ⟨.lf default⟩

/-- Element and document content: adjacent text nodes are merged and
    an empty text node is dropped (XDM 4.0 §6.7.1). -/
def mergeKids (ks : List XT) : List XT :=
  ks.foldr (fun k acc =>
    match k with
    | .lf r =>
      if r.kind == .text then
        match acc with
        | .lf r2 :: rest =>
          if r2.kind == .text then .lf { r with value := r.value ++ r2.value } :: rest
          else if r.value == "" then acc else k :: acc
        | _ => if r.value == "" then acc else k :: acc
      else k :: acc
    | _ => k :: acc) []

/-- A copy of a node of a document (with its subtree). -/
def Env.readXT (e : Env) : Nat → NodeRef → XT
  | 0, n => .lf (e.nrec n)
  | f + 1, n =>
    let r := e.nrec n
    match r.kind with
    | .element | .document =>
      .el r (r.attrs.toList.map (fun a => e.nrec (n.at a)))
        (r.children.toList.map (fun c => e.readXT f (n.at c)))
    | _ => .lf r

/-- The in-scope namespaces of an element placed under a parent with the
    bindings `parent` (namespace inheritance): its own bindings, its
    name's binding, then the parent's bindings for other prefixes. -/
def scopeMerge (r : NRec) (parent : List (String × String)) : List (String × String) :=
  let own := if r.name.pfx == "xml" || r.inscope.lookup r.name.pfx == some r.name.uri then r.inscope
    else (r.name.pfx, r.name.uri) :: r.inscope
  own ++ parent.filter (fun (p, _) => !own.any (·.1 == p))

/-- Flatten an `XT` into the document table (document order: a node,
    its attributes, then its children). -/
def flatXT : Nat → Option Nat → List (String × String) → XT → B Unit
  | 0, _, _, _ => pure ()
  | f + 1, par, psc, t =>
    match t with
    | .lf r => do
        let i ← pushRec { r with parent := par, children := #[], attrs := #[] }
        setRec i (fun x => { x with last := i })
    | .el r ats kids => do
        let sc := if r.kind == .element then scopeMerge r psc else r.inscope
        let i ← pushRec { r with parent := par, inscope := sc, children := #[], attrs := #[] }
        let mut aidx : Array Nat := #[]
        for a in ats do
          let j ← pushRec { a with parent := some i, children := #[], attrs := #[] }
          setRec j (fun x => { x with last := j })
          aidx := aidx.push j
        let mut cidx : Array Nat := #[]
        for k in mergeKids kids do
          let j := (← get).size
          flatXT f (some i) sc k
          cidx := cidx.push j
        let sz := (← get).size
        setRec i (fun x => { x with children := cidx, attrs := aidx, last := sz - 1 })

def nrecHash (h : UInt64) (r : NRec) : UInt64 :=
  let h := hMix h (match r.kind with
    | .document => 1 | .element => 2 | .attribute => 3 | .text => 4
    | .comment => 5 | .pi => 6 | .namespace => 7)
  let h := hMix (hMix (hMix h (hStr r.name.uri)) (hStr r.name.loc)) (hStr r.value)
  hMix (hMix h r.last.toUInt64) ((r.parent.getD 0) + 1).toUInt64

/-- A new XNode tree: the root at index 0, with no parent. -/
def mkXNode (tag key : String) (t : XT) : Item :=
  let ((), arr) := (flatXT 100000 none [] t).run #[]
  let h := arr.foldl nrecHash 0xcbf29ce484222325
  .node { doc := runtimeDocId tag (key ++ "/" ++ toString h), idx := 0, rt := some { nodes := arr } }

/-- A prefix for `u` that `sc` does not bind to another URI. -/
def fixPrefix (sc : List (String × String)) (p u : String) : String :=
  match (List.range 1000).find? (fun i =>
      match sc.lookup (p ++ "_" ++ toString (i + 1)) with
      | none => true
      | some v => v == u) with
  | some i => p ++ "_" ++ toString (i + 1)
  | none => p ++ "_x"

/-- An element C with new attributes: no two with the same name
    (FOUP0004), and namespace fixup for the attribute names. -/
def finishEl (r : NRec) (ats : List NRec) (kids : List XT) : M XT := do
  let mut seen : List (String × String) := []
  for a in ats do
    if seen.contains (a.name.uri, a.name.loc) then
      err "FOUP0004" ("fn:update: two attributes named " ++ a.name.loc)
    seen := (a.name.uri, a.name.loc) :: seen
  if r.kind != .element then return .el r ats kids
  let mut sc := r.inscope
  let mut out : Array NRec := #[]
  for a in ats do
    let p := a.name.pfx
    if a.name.uri == "" || p == "" || p == "xml" then
      out := out.push a
    else
      match sc.lookup p with
      | none => sc := (p, a.name.uri) :: sc; out := out.push a
      | some v =>
        if v == a.name.uri then out := out.push a
        else
          let p' := fixPrefix sc p a.name.uri
          if sc.lookup p' != some a.name.uri then sc := (p', a.name.uri) :: sc
          out := out.push { a with name := { a.name with pfx := p' } }
  pure (.el { r with inscope := sc } out.toList kids)

/-- `C` with its value replaced by the string `s`. -/
def setValue (c : XT) (s : String) : M XT :=
  match c with
  | .el r ats _ => pure (.el r ats [.lf { kind := .text, value := s }])
  | .lf r =>
    match r.kind with
    | .comment =>
      if (s.splitOn "--").length > 1 || s.endsWith "-" then
        err "XQDY0072" "fn:update: a comment may not contain '--' or end with '-'"
      else pure (.lf { r with value := s })
    | .pi =>
      let s := String.ofList (s.toList.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r'))
      if (s.splitOn "?>").length > 1 then
        err "XQDY0026" "fn:update: a processing instruction may not contain '?>'"
      else pure (.lf { r with value := s })
    | _ => pure (.lf { r with value := s })

structure XU where
  e : Env
  h : Hooks
  sel : Std.HashSet Nat
  repl : Seq
  /-- `$replacement` when it is a single function item to call. -/
  callRepl : Option Item
  key : String

def xtIsAttr : XT → Bool
  | .lf r => r.kind == .attribute
  | _ => false

def xtIsNs : XT → Bool
  | .lf r => r.kind == .namespace
  | _ => false

/-- The substitution sequence for a selected XNode `C`. -/
def XU.subst (u : XU) (c : XT) (idx : Nat) (isAttr : Bool) : M (List XT) := do
  let items ← match u.callRepl with
    | some fi => u.h.callN fi [[mkXNode "update-node" (u.key ++ "#" ++ toString idx) c]]
    | none => pure u.repl
  let mut out : Array XT := #[]
  let mut nval := 0
  for j in items do
    match j with
    | .node m =>
      let mr := u.e.nrec m
      if mr.kind == .document then
        for k in mr.children do out := out.push (u.e.readXT 100000 (m.at k))
      else out := out.push (u.e.readXT 100000 m)
    | .atom a =>
      nval := nval + 1
      if nval > 1 then err "FOUP0004" "fn:update: more than one item replaces the value of a selected node"
      out := out.push (← setValue c a.str)
    | _ => err "FOUP0004" "fn:update: a replacement for an XNode must be an XNode or an atomic item"
  for t in out do
    if xtIsNs t || xtIsAttr t != isAttr then
      err "FOUP0004" (if isAttr then "fn:update: an attribute must be replaced by attributes"
        else "fn:update: a child must be replaced by nodes that are not attributes")
  pure out.toList

/-- Process an XNode of the origin's tree: the nodes that take its place. -/
def XU.proc (u : XU) : Nat → NodeRef → M (List XT)
  | 0, _ => err "FOER0000" "fn:update: tree too deep"
  | f + 1, n => do
    let r := u.e.nrec n
    let c ← match r.kind with
      | .element | .document => do
        let mut ats : Array NRec := #[]
        for a in r.attrs do
          for t in ← u.proc f (n.at a) do
            match t with
            | .lf ar => ats := ats.push ar
            | _ => pure ()
        let mut ks : Array XT := #[]
        for k in r.children do
          for t in ← u.proc f (n.at k) do ks := ks.push t
        finishEl r ats.toList (mergeKids ks.toList)
      | _ => pure (XT.lf r)
    if u.sel.contains n.idx then u.subst c n.idx (r.kind == .attribute) else pure [c]

/-! ## JNodes -/

/-- The kind of a JNode by its ·jvalue· (XDM 4.0 §8.5). -/
inductive JK where
  | map | arr | seq | leaf
deriving DecidableEq

def jkindOf (v : Seq) : JK :=
  match v with
  | [.map _] => .map
  | [.arr _] => .arr
  | _ :: _ :: _ => .seq
  | _ => .leaf

/-- A contribution to the ·jvalue· of a parent: a key (for a map), a
    value, and where it comes from: 0 any position (the node itself, a
    replaced value, a JNode with no parent), 1 a map entry, 2 an array
    member, 3 an item of a sequence or a leaf. -/
structure JC where
  key : Option Atomic
  val : Seq
  src : Nat

def srcOfKind : JK → Nat
  | .map => 1
  | .arr => 2
  | _ => 3

/-- The ·jvalue· of a JNode of kind `k` rebuilt from the contributions of
    its children. -/
def rebuildJ (k : JK) (cs : List JC) : M Seq := do
  match k with
  | .map =>
    let mut mb : MB := {}
    for c in cs do
      if c.src == 2 || c.src == 3 then
        err "FOUP0004" "fn:update: a map entry must be replaced by map entries"
      match c.key with
      | none => err "FOUP0004" "fn:update: a map entry needs a key"
      | some key =>
        if (mb.find? key).isSome then
          err "FOUP0004" ("fn:update: two entries with the key " ++ key.str)
        mb := mb.set key c.val
    pure [.map mb.toList]
  | .arr =>
    let mut ms : Array Seq := #[]
    for c in cs do
      if c.src == 1 || c.src == 3 then
        err "FOUP0004" "fn:update: an array member must be replaced by array members"
      ms := ms.push c.val
    pure [.arr ms.toList]
  | _ => pure (cs.flatMap (·.val))

structure JU where
  h : Hooks
  sel : Std.HashSet (List Nat)
  repl : Seq
  callRepl : Option Item
  salt : UInt64

/-- The substitution sequence for a selected JNode with key `key` and
    rebuilt value `v`, whose parent is of kind `pk`. -/
def JU.substJ (u : JU) (key : Atomic) (v : Seq) (pk : JK) (path : List Nat) : M (List JC) := do
  let cnode : Item := .jnode (hMix (hMix u.salt (hash path)) v.length.toUInt64) [⟨key, 1⟩] v []
  let items ← match u.callRepl with
    | some fi => u.h.callN fi [[cnode]]
    | none => pure u.repl
  let mut out : Array JC := #[]
  let mut nval := 0
  for j in items do
    let valueRepl : Bool := match j with
      | .jnode .. | .node _ => false
      | .map _ => pk != .map
      | .arr _ => pk != .arr
      | _ => true
    if valueRepl then
      nval := nval + 1
      if nval > 1 then err "FOUP0004" "fn:update: more than one item replaces the value of a selected node"
      out := out.push ⟨some key, [j], 0⟩
    else
      match j with
      | .jnode _ st2 v2 up2 =>
        match st2, up2 with
        | [], _ =>
          for ch in jchildren j do
            out := out.push ⟨jkeyOf ch, jvalOf ch, srcOfKind (jkindOf v2)⟩
        | s :: _, [] => out := out.push ⟨some s.key, v2, 0⟩
        | s :: _, p :: _ =>
          out := out.push ⟨some s.key, v2, if s.pos == 0 then 3 else srcOfKind (jkindOf p)⟩
      | .map kvs => for (k, x) in kvs do out := out.push ⟨some k, x, 1⟩
      | .arr ms => for m in ms do out := out.push ⟨none, m, 2⟩
      | _ => err "FOUP0004" "fn:update: an XNode cannot replace a JNode"
  pure out.toList

/-- Process a JNode of the origin's tree, whose parent is of kind `pk`:
    its rebuilt value and the contributions that take its place. -/
def JU.procJ (u : JU) : Nat → Item → JK → M (Seq × List JC)
  | 0, _, _ => err "FOER0000" "fn:update: tree too deep"
  | f + 1, nd, pk => do
    let v := jvalOf nd
    let k := jkindOf v
    let newv ← match k with
      | .leaf => pure v
      | _ => do
        let mut cs : Array JC := #[]
        for ch in jchildren nd do
          for c in (← u.procJ f ch k).2 do cs := cs.push c
        rebuildJ k cs.toList
    let path := jposPath nd
    match jkeyOf nd with
    | some key =>
      if u.sel.contains path then pure (newv, ← u.substJ key newv pk path)
      else pure (newv, [⟨some key, newv, 0⟩])
    | none => pure (newv, [⟨none, newv, 0⟩])

/-! ## The function -/

/-- Is the JNode `j` reached from the JNode `o` by one or more child
    steps (not item-axis steps)? -/
def jbelow (o j : Item) : Bool :=
  match o, j with
  | .jnode r0 st0 _ _, .jnode r st _ _ =>
    r == r0 && st.length > st0.length &&
    let extra := st.take (st.length - st0.length)
    let rest := st.drop (st.length - st0.length)
    extra.all (·.pos != 0) && (rest.zip st0).all (fun (a, b) => a.pos == b.pos)
  | _, _ => false

def updateFn : LibFn := fun h e a => do
  let value := argN a 0
  let repl := argN a 2
  let callRepl : Option Item := match repl with
    | [i@(.fn _)] => some i
    | _ => none
  if let some fi := callRepl then
    if (fi.fnArity.getD 0) > 1 then
      err "XPTY0004" "fn:update: $replacement must accept one argument"
  let origin : Item ← match value with
    | [i@(.node _)] | [i@(.jnode ..)] => pure i
    | [i@(.map _)] | [i@(.arr _)] => pure (mkJRoot 0 [i])
    | _ => err "XPTY0004" "fn:update: $value must be a node, a map or an array"
  let selFn ← match argN a 1 with
    | [f] => pure f
    | _ => err "XPTY0004" "fn:update: $select must be a function item"
  let sel ← h.callN selFn [[origin]]
  if !sel.all Item.isGNode then
    err "XPTY0004" "fn:update: $select must return nodes"
  match origin with
  | .node o =>
    let orec := e.nrec o
    let mut s : Std.HashSet Nat := {}
    for i in sel do
      match i with
      | .node m =>
        if m.doc == o.doc && o.idx < m.idx && m.idx ≤ orec.last && (e.nrec m).kind != .namespace then
          s := s.insert m.idx
        else err "FOUP0003" "fn:update: a selected node is not below the origin node"
      | _ => err "FOUP0003" "fn:update: a selected node is not below the origin node"
    let key := toString o.doc ++ ":" ++ toString o.idx
    let u : XU := { e, h, sel := s, repl, callRepl, key }
    match ← u.proc 100000 o with
    | [t] => pure [mkXNode "update" (key ++ ":" ++ toString s.size) t]
    | _ => err "FOER0000" "fn:update: the origin node was replaced"
  | o@(.jnode r0 st0 v0 _) =>
    let mut s : Std.HashSet (List Nat) := {}
    for i in sel do
      if jbelow o i then s := s.insert (jposPath i)
      else err "FOUP0003" "fn:update: a selected node is not below the origin node"
    let salt := hMix (hMix r0 (hashSeq v0)) 0x7570646174650000
    let u : JU := { h, sel := s, repl, callRepl, salt }
    let (newv, _) ← u.procJ 10000 o .leaf
    match value with
    | [.jnode ..] =>
      let rid := hMix (hMix (hashSeq newv) salt) (s.size.toUInt64)
      let steps : List JStep := match st0 with
        | [] => []
        | st :: _ => [⟨st.key, 1⟩]
      pure [.jnode rid steps newv []]
    | _ => pure newv
  | _ => err "XPTY0004" "fn:update: $value must be a node, a map or an array"

def updateTable : List (String × LibFn) := [("update", updateFn)]

end L4Factoidal.XPath4
