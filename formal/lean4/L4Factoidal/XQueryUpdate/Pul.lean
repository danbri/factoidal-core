/-
L4Factoidal.XQueryUpdate.Pul — pending update lists and `upd:applyUpdates`
(XQuery Update Facility 3.0, W3C Recommendation 2017-01-24,
https://www.w3.org/TR/xquery-update-30/, §2.1, §8).

An updating expression returns an XDM instance and a pending update
list. Here an update primitive (§8.1) is an item of a reserved kind in
the result sequence: a function item `upd:<kind>` (namespace `#upd`,
which no query can write) partially applied to its operands. So the
comma operator, FLWOR, `if`, `typeswitch` and function calls merge
pending update lists by sequence concatenation, which is
`upd:mergeUpdates` (§8.2.2: the union of the two lists), and no shared
XDM type changes. `splitPul` takes the XDM instance and the list apart.

`applyUpdates` (§8.2.3) runs `compatibilityCheck` (§8.2.1), then
rebuilds every document that a primitive targets, from the state of the
snapshot: every operand node is read before any document changes, so
the result does not depend on the order of the primitives. The order of
§8.2.3 rule 2 is kept where it matters: `replaceElementContent`
replaces the children that the insertions made, a replaced node takes
its replacement and not its deletion, and insertions before or after a
deleted or replaced node stay. Adjacent text nodes are merged and empty
text nodes are removed (rule 3, `mergeKids`). Duplicate attribute names
on one element are `XUDY0021` (rule 4).

Not modelled: node identity across a snapshot — a rebuilt document gets
new indices, so a node reference taken before `applyUpdates` must not
be used after it (the runner starts every later query from the
documents). Revalidation is `revalidate` (strict and lax through the
schema hook; `skip` removes types, §8.2.5).
-/
import L4Factoidal.XPath4.Ext
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.XQueryUpdate

open L4Factoidal.XPath4

/-- The namespace of the reserved function items that carry update
    primitives. A query cannot name it (`#` is not a URI character an
    `EQName` can produce here). -/
def nsUPD : String := "#upd"

/-- The update primitives of §8.1. -/
inductive PKind where
  | insertBefore | insertAfter | insertInto | insertIntoAsFirst | insertIntoAsLast
  | insertAttributes | delete | replaceNode | replaceValue | replaceElementContent
  | rename | put
deriving DecidableEq, Repr, Inhabited

def PKind.all : List PKind :=
  [.insertBefore, .insertAfter, .insertInto, .insertIntoAsFirst, .insertIntoAsLast,
   .insertAttributes, .delete, .replaceNode, .replaceValue, .replaceElementContent,
   .rename, .put]

def PKind.name : PKind → String
  | .insertBefore => "insertBefore" | .insertAfter => "insertAfter"
  | .insertInto => "insertInto" | .insertIntoAsFirst => "insertIntoAsFirst"
  | .insertIntoAsLast => "insertIntoAsLast" | .insertAttributes => "insertAttributes"
  | .delete => "delete" | .replaceNode => "replaceNode" | .replaceValue => "replaceValue"
  | .replaceElementContent => "replaceElementContent" | .rename => "rename" | .put => "put"

def PKind.ofName? (s : String) : Option PKind := PKind.all.find? (·.name == s)

/-- An update primitive. `content` holds the nodes of the insertion or
    replacement sequence (an atomic item stands for a text node with its
    string, §5.1 "as though it were an enclosed expression"); `str` the
    string of `replaceValue`, the text of `replaceElementContent` (`some`
    in `content` as one atom) and the URI of `put`; `name` the new name
    of `rename`. -/
structure Prim where
  kind : PKind
  target : NodeRef
  content : Seq := []
  str : String := ""
  name : QN := default
deriving Inhabited

/-- The item that carries a primitive. -/
def Prim.toItem (p : Prim) : Item :=
  .fn (.papp (.fn (.builtin { uri := nsUPD, loc := p.kind.name } 0))
    [some [.node p.target], some p.content, some [.atom (Atomic.ofStr p.str)],
     some [.atom (Atomic.ofQN p.name)]])

/-- The primitive an item carries, if it carries one. -/
def Prim.ofItem? : Item → Option Prim
  | .fn (.papp (.fn (.builtin q 0)) [some [.node t], some c, some [.atom s], some [.atom n]]) =>
    if q.uri != nsUPD then none else
    match PKind.ofName? q.loc with
    | some k =>
      let nm := match n.v with | .qn x => x | _ => default
      some { kind := k, target := t, content := c, str := s.str, name := nm }
    | none => none
  | _ => none

def isPulItem (i : Item) : Bool := (Prim.ofItem? i).isSome

/-- The XDM instance and the pending update list of a result. -/
def splitPul (s : Seq) : Seq × List Prim :=
  let (ps, xs) := s.partition isPulItem
  (xs, ps.filterMap Prim.ofItem?)

def pulOf (s : Seq) : List Prim := (splitPul s).2

/-! ## Compatibility (§8.2.1) -/

def nodeKey (n : NodeRef) : Nat × Nat := (n.doc, n.idx)

/-- The namespace bindings a primitive creates (§8.2.1, last rule):
    `(element, prefix, uri)`. -/
def Prim.nsBindings (env : Env) (p : Prim) : List ((Nat × Nat) × String × String) :=
  let attrBind (owner : NodeRef) (s : Seq) := s.filterMap (fun i => match i with
    | .node m =>
      let r := env.nrec m
      if r.kind == .attribute && r.name.uri != "" && r.name.pfx != "" then
        some (nodeKey owner, r.name.pfx, r.name.uri) else none
    | _ => none)
  match p.kind with
  | .insertAttributes => attrBind p.target p.content
  | .replaceNode =>
    let r := env.nrec p.target
    if r.kind == .attribute then
      match r.parent with
      | some par => attrBind (p.target.at par) p.content
      | none => []
    else []
  | .rename =>
    let r := env.nrec p.target
    if r.kind == .element then
      (if p.name.uri == "" && p.name.pfx == "" then [] else [(nodeKey p.target, p.name.pfx, p.name.uri)])
    else if r.kind == .attribute && p.name.uri != "" && p.name.pfx != "" then
      match r.parent with
      | some par => [(nodeKey (p.target.at par), p.name.pfx, p.name.uri)]
      | none => []
    else []
  | _ => []

/-- `upd:compatibilityCheck`: XUDY0015, XUDY0016, XUDY0017, XUDY0031,
    XUDY0024. -/
def compatibilityCheck (env : Env) (pul : List Prim) : M Unit := do
  let mut ren : Std.HashSet (Nat × Nat) := {}
  let mut rep : Std.HashSet (Nat × Nat) := {}
  let mut val : Std.HashSet (Nat × Nat) := {}
  let mut uris : Std.HashSet String := {}
  let mut binds : Std.HashMap ((Nat × Nat) × String) String := {}
  for p in pul do
    let k := nodeKey p.target
    match p.kind with
    | .rename =>
      if ren.contains k then err "XUDY0015" "a node is the target of two rename expressions"
      ren := ren.insert k
    | .replaceNode =>
      if rep.contains k then err "XUDY0016" "a node is the target of two replace expressions"
      rep := rep.insert k
    | .replaceValue | .replaceElementContent =>
      if val.contains k then err "XUDY0017" "a node is the target of two replace value of expressions"
      val := val.insert k
    | .put =>
      if uris.contains p.str then err "XUDY0031" ("two fn:put calls with the URI " ++ p.str)
      uris := uris.insert p.str
    | _ => pure ()
    for (el, pf, u) in p.nsBindings env do
      match binds.get? (el, pf) with
      | some u2 => if u2 != u then err "XUDY0024" ("conflicting namespace bindings for the prefix " ++ pf)
      | none => binds := binds.insert (el, pf) u
  pure ()

/-! ## The rebuilt tree -/

/-- Types after an update (§8.2.5 `upd:removeType`, §8.2.6
    `upd:setToUntyped`): an untyped record. -/
def _root_.L4Factoidal.XPath4.NRec.untype (r : NRec) : NRec := { r with tann := none, tval := none, nilled := false, noTypedValue := false }

/-- `upd:setToUntyped` on a whole inserted tree. -/
def untypeXT : Nat → XT → XT
  | 0, t => t
  | f + 1, .el r ats ks => .el r.untype (ats.map NRec.untype) (ks.map (untypeXT f))
  | _, .lf r => .lf r.untype

/-- `upd:removeType` on one record: an element loses its type to
    `xs:anyType` when it had one, an attribute becomes untyped. -/
def _root_.L4Factoidal.XPath4.NRec.removeType (r : NRec) : NRec :=
  if r.kind == .element then
    match r.tann with
    | some q =>
      if q.loc == "untyped" && q.uri == nsXS then r.untype
      else { r with tann := some { uri := nsXS, loc := "anyType", pfx := "xs" }, tval := none,
                    nilled := false, noTypedValue := false }
    | none => r.untype
  else r.untype

/-- The operations on each node of one document, by node index. -/
structure Ops where
  before : Std.HashMap Nat (Array XT) := {}
  after : Std.HashMap Nat (Array XT) := {}
  into : Std.HashMap Nat (Array XT) := {}
  first : Std.HashMap Nat (Array XT) := {}
  last : Std.HashMap Nat (Array XT) := {}
  attrs : Std.HashMap Nat (Array NRec) := {}
  del : Std.HashSet Nat := {}
  repl : Std.HashMap Nat (Array XT) := {}
  val : Std.HashMap Nat String := {}
  content : Std.HashMap Nat (Option String) := {}
  ren : Std.HashMap Nat QN := {}
  /-- Nodes whose name or content changes: `upd:removeType` applies to
      them and their ancestors. -/
  touched : Std.HashSet Nat := {}
deriving Inhabited

def addTo (m : Std.HashMap Nat (Array XT)) (k : Nat) (xs : List XT) : Std.HashMap Nat (Array XT) :=
  m.insert k ((m.getD k #[]) ++ xs.toArray)

/-- The trees of an insertion or replacement sequence, read in the
    snapshot (`env` before any change). An atomic item is a text node. -/
def contentXT (env : Env) (s : Seq) : List XT :=
  s.filterMap (fun i => match i with
    | .node m => some (env.readXT 100000 m)
    | .atom a => some (.lf { kind := .text, value := a.str })
    | _ => none)

/-- Is the element (or document) record untyped (`xs:untyped`)? -/
def _root_.L4Factoidal.XPath4.NRec.isUntyped (r : NRec) : Bool :=
  match r.tann with
  | none => true
  | some q => q.uri == nsXS && q.loc == "untyped"

/-- Does a content sequence hold an element or a text node (an atomic
    item is a text node)? -/
def hasElemOrText (env : Env) (s : Seq) : Bool :=
  s.any (fun i => match i with
    | .node m => let k := (env.nrec m).kind; k == .element || k == .text
    | .atom _ => true
    | _ => false)

/-- The flags of a primitive (`Prim.str` of the content primitives):
    `noinherit` (copy-namespaces no-inherit), `strip` (construction strip). -/
def Prim.flag (p : Prim) (f : String) : Bool := (p.str.splitOn ",").contains f

/-- Record the primitives of one document in `Ops`. `env` is the
    snapshot. The nodes marked in `touched` are those §8.1 passes to
    `upd:removeType`. -/
def collectOps (env : Env) (d : Doc) (ps : List Prim) : Ops := Id.run do
  let mut o : Ops := {}
  for p in ps do
    let i := p.target.idx
    let r := d.get i
    let parIdx := r.parent.getD i
    let par := d.get parIdx
    -- §8.1.1 rule 1b: content inserted under an untyped parent is untyped;
    -- construction strip copies the content untyped (XQuery 3.0 §3.9.1.3)
    let cx (owner : NRec) : List XT :=
      let xs := contentXT env p.content
      if owner.isUntyped || p.flag "strip" then xs.map (untypeXT 100000) else xs
    let et := hasElemOrText env p.content
    let touch (o : Ops) (b : Bool) (k : Nat) : Ops := if b then { o with touched := o.touched.insert k } else o
    match p.kind with
    | .insertBefore => o := touch { o with before := addTo o.before i (cx par) } et parIdx
    | .insertAfter => o := touch { o with after := addTo o.after i (cx par) } et parIdx
    | .insertInto => o := touch { o with into := addTo o.into i (cx r) } et i
    | .insertIntoAsFirst => o := touch { o with first := addTo o.first i (cx r) } et i
    | .insertIntoAsLast => o := touch { o with last := addTo o.last i (cx r) } et i
    | .insertAttributes =>
      let ats := (cx r).filterMap (fun t => match t with | .lf a => some a | _ => none)
      o := touch { o with attrs := o.attrs.insert i ((o.attrs.getD i #[]) ++ ats.toArray) } true i
    | .delete =>
      let b := (r.kind == .element || r.kind == .attribute || r.kind == .text) && par.kind == .element
      o := touch { o with del := o.del.insert i } b parIdx
    | .replaceNode =>
      let b := r.kind == .element || r.kind == .attribute || r.kind == .text || et ||
        p.content.any (fun x => match x with | .node m => (env.nrec m).kind == .attribute | _ => false)
      o := touch { o with repl := o.repl.insert i (cx par).toArray } b parIdx
    | .replaceValue =>
      o := { o with val := o.val.insert i p.str }
      if r.kind == .attribute then o := touch o true i
      else if r.kind == .text && r.parent.isSome then o := touch o true parIdx
    | .replaceElementContent =>
      let t := match p.content with
        | [.atom a] => some a.str
        | _ => none
      o := touch { o with content := o.content.insert i t } true i
    | .rename =>
      o := touch { o with ren := o.ren.insert i p.name } (r.kind == .element || r.kind == .attribute) i
    | .put => pure ()
  return o

/-- Add a binding to an element's in-scope namespaces, unless the prefix
    is bound to that URI already. -/
def addBinding (sc : List (String × String)) (p u : String) : List (String × String) :=
  if p == "xml" then sc
  else if sc.lookup p == some u then sc else (p, u) :: sc

/-- A renamed node (§8.1.11). -/
def renamed (r : NRec) (q : QN) : NRec :=
  match r.kind with
  | .element =>
    let sc := if q.uri == "" && q.pfx == "" then
        (if (r.inscope.lookup "").getD "" != "" then ("", "") :: r.inscope else r.inscope)
      else addBinding r.inscope q.pfx q.uri
    { r with name := q, inscope := sc }
  | .pi => { r with name := { uri := "", loc := q.loc } }
  | _ => { r with name := q }

/-- The touched nodes and their ancestors (`upd:removeType` climbs). -/
def withAncestors (d : Doc) (t : Std.HashSet Nat) : Std.HashSet Nat := Id.run do
  let mut out := t
  for i in t.toList do
    let mut j := i
    for _ in [0:100000] do
      match (d.get j).parent with
      | some p =>
        if out.contains p && p != i then break
        out := out.insert p
        j := p
      | none => break
  return out

/-- Rebuild the node at `i`: the nodes that take its place among its
    parent's attributes or children (its replacement, nothing when it is
    deleted, else itself with its changes). The caller adds the
    insertions before and after it. -/
def rebuild (d : Doc) (o : Ops) (typeGone : Std.HashSet Nat) : Nat → Nat → M (List XT)
  | 0, _ => err "XUDY0021" "document too deep"
  | f + 1, i => do
    -- a deleted or replaced node is still checked (§8.2.3 rule 4: a
    -- detached node must satisfy the XDM constraints too)
    if let some rs := o.repl.get? i then
      let _ ← rebuild d { o with repl := o.repl.erase i } typeGone f i
      return rs.toList
    if o.del.contains i then
      let _ ← rebuild d { o with del := o.del.erase i } typeGone f i
      return []
    let r0 := d.get i
    let r := match o.ren.get? i with
      | some q => renamed r0 q
      | none => r0
    let r := match o.val.get? i with
      | some s => { r with value := s }
      | none => r
    let r := if typeGone.contains i then r.removeType else r
    match r.kind with
    | .element | .document =>
      -- attributes
      let mut ats : Array NRec := #[]
      for a in r.attrs do
        if let some rs := o.repl.get? a then
          for t in rs do
            match t with
            | .lf ar => ats := ats.push ar
            | _ => pure ()
          continue
        if o.del.contains a then continue
        let ar0 := d.get a
        let ar := match o.ren.get? a with
          | some q => renamed ar0 q
          | none => ar0
        let ar := match o.val.get? a with
          | some s => { ar with value := s }
          | none => ar
        let ar := if typeGone.contains a then ar.removeType else ar
        ats := ats.push ar
      ats := ats ++ (o.attrs.getD i #[])
      -- XDM: no two attributes with the same expanded name (§8.2.3 rule 4)
      let mut seen : Std.HashSet (String × String) := {}
      for a in ats do
        if seen.contains (a.name.uri, a.name.loc) then
          err "XUDY0021" ("two attributes named " ++ a.name.show ++ " after the updates")
        seen := seen.insert (a.name.uri, a.name.loc)
      -- the namespace bindings of the attribute names (§8.1.6, §8.1.8, §8.1.11)
      let mut sc := r.inscope
      if r.kind == .element then
        for a in ats do
          if a.name.uri != "" && a.name.pfx != "" && a.name.pfx != "xml" then
            match sc.lookup a.name.pfx with
            | some u =>
              if u != a.name.uri then
                err "XUDY0021" ("the prefix " ++ a.name.pfx ++ " is bound to two namespaces")
            | none => sc := (a.name.pfx, a.name.uri) :: sc
        if r.name.pfx != "xml" && r.name.uri != "" then
          match sc.lookup r.name.pfx with
          | some u => if u != r.name.uri then err "XUDY0021" ("the prefix " ++ r.name.pfx ++ " is bound to two namespaces")
          | none => sc := (r.name.pfx, r.name.uri) :: sc
      -- children
      let mut ks : Array XT := (o.first.getD i #[])
      for c in r.children do
        ks := ks ++ (o.before.getD c #[])
        ks := ks ++ (← rebuild d o typeGone f c).toArray
        ks := ks ++ (o.after.getD c #[])
      ks := ks ++ (o.into.getD i #[]) ++ (o.last.getD i #[])
      if let some t := o.content.get? i then
        ks := match t with
          | some s => #[.lf { kind := .text, value := s }]
          | none => #[]
      pure [.el { r with inscope := sc } ats.toList ks.toList]
    | _ => pure [.lf r]

/-- Flatten an `XT` into a document table, as `XPath4.flatXT`, with the
    namespace inheritance of the snapshot: with `inherit` (copy-namespaces
    inherit, §8.2.3 rule 5 and §8.2.7 `upd:propagateNamespace`) an element
    also has the bindings of its parent for the prefixes it does not bind;
    with no-inherit it keeps its own in-scope namespaces only. -/
def flatU (inherit : Bool) : Nat → Option Nat → List (String × String) → XT → B Unit
  | 0, _, _, _ => pure ()
  | f + 1, par, psc, t =>
    match t with
    | .lf r => do
        let i ← pushRec { r with parent := par, children := #[], attrs := #[] }
        setRec i (fun x => { x with last := i })
    | .el r ats kids => do
        let sc := if r.kind == .element then (if inherit then scopeMerge r psc else r.inscope) else r.inscope
        let i ← pushRec { r with parent := par, inscope := sc, children := #[], attrs := #[] }
        let mut aidx : Array Nat := #[]
        for a in ats do
          let j ← pushRec { a with parent := some i, children := #[], attrs := #[] }
          setRec j (fun x => { x with last := j })
          aidx := aidx.push j
        let mut cidx : Array Nat := #[]
        for k in mergeKids kids do
          let j := (← get).size
          flatU inherit f (some i) sc k
          cidx := cidx.push j
        let sz := (← get).size
        setRec i (fun x => { x with children := cidx, attrs := aidx, last := sz - 1 })

/-- A document rebuilt from an `XT` whose root is at index 0. -/
def docOfXT (base : Doc) (t : XT) (inherit : Bool := true) : Doc :=
  let ((), arr) := (flatU inherit 100000 none [] t).run #[]
  { base with nodes := arr, origin := none }

/-- Apply the primitives of one document (all with the same document
    number) to it. -/
def applyDoc (env : Env) (d : Doc) (ps : List Prim) : M Doc := do
  let o := collectOps env d ps
  let typeGone := withAncestors d o.touched
  -- the copy-namespaces inherit mode of the expressions (`Prim.str`)
  let inherit := !ps.any (fun p => p.flag "noinherit" &&
    [PKind.insertBefore, .insertAfter, .insertInto, .insertIntoAsFirst, .insertIntoAsLast,
     .insertAttributes, .replaceNode, .rename].contains p.kind)
  match ← rebuild d o typeGone 100000 0 with
  | [t] => pure (docOfXT d t inherit)
  | _ => err "XUDY0021" "the root of a document was removed"

/-! ## upd:applyUpdates (§8.2.3) -/

/-- The result of `applyUpdates`: the new dynamic context (source
    documents replaced), the rebuilt run-time documents by document
    number, and the documents `fn:put` stored (URI, node). -/
structure Applied where
  env : Env
  rt : List (Nat × Doc) := []
  puts : List (String × NodeRef) := []
  /-- The numbers of the source documents (`Env.docs`) that changed. -/
  changed : List Nat := []
deriving Inhabited

/-- `upd:applyUpdates`, without revalidation (`Revalidate` adds it):
    check, then rebuild each targeted document from the snapshot. -/
def applyUpdates (env : Env) (pul : List Prim) : M Applied := do
  compatibilityCheck env pul
  let mut docNums : List Nat := []
  for p in pul do
    if p.kind != .put && !docNums.contains p.target.doc then docNums := docNums ++ [p.target.doc]
  let mut out : Applied := { env }
  for dn in docNums do
    let ps := pul.filter (fun p => p.kind != .put && p.target.doc == dn)
    let some p0 := ps.head? | continue
    let d := env.doc p0.target
    let nd ← applyDoc env d ps
    match p0.target.rt with
    | some _ => out := { out with rt := (dn, nd) :: out.rt }
    | none => out := { out with env := { out.env with docs := out.env.docs.set! dn nd },
                                changed := out.changed ++ [dn] }
  -- fn:put runs last, on the updated nodes (§6.1 note)
  for p in pul do
    if p.kind == .put then
      let t := match p.target.rt with
        | some _ => match out.rt.lookup p.target.doc with
          | some nd => { p.target with rt := some nd }
          | none => p.target
        | none => p.target
      out := { out with puts := out.puts ++ [(p.str, t)] }
  pure out

/-- A node after `applyUpdates`: the same index in the rebuilt run-time
    document (used for a copy's root, index 0). -/
def Applied.refresh (a : Applied) (n : NodeRef) : NodeRef :=
  match n.rt with
  | some _ => match a.rt.lookup n.doc with
    | some nd => { n with rt := some nd }
    | none => n
  | none => n

end L4Factoidal.XQueryUpdate
