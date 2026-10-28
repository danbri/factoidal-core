/-
L4Factoidal.XQueryUpdate.Expr — the evaluation of the XQuery Update
Facility 3.0 expressions (https://www.w3.org/TR/xquery-update-30/ §5,
§6.1): insert, delete, replace, replace value of, rename, copy modify,
transform with, dynamic updating function invocation, `fn:put`.

The grammar (`XQueryUpdate.Grammar`) writes each expression as an
`Expr.ext` node with a tag that starts with `upd-`; the XQuery 4.0
dispatcher (`XQuery4.Runtime.evalExt`) gives such a node to `evalUpd`
with callbacks into the evaluator. Each expression checks its operands
in the order of the specification and returns the update primitives of
`XQueryUpdate.Pul` (with the pending update lists of its operands).

Copy modify (§5.6) is `let $v := upd-copy(E) ... return upd-modify(M, R)`:
`upd-copy` makes a new tree (new node identity, types removed, §5.6
step 1), `upd-modify` evaluates M, refuses a primitive whose target is
not in a copy (XUDY0014) or a `put` (XUDY0037), applies the list to the
copies (`applyUpdates`) and evaluates R with the variables bound to the
changed copies.
-/
import L4Factoidal.XQueryUpdate.Pul

namespace L4Factoidal.XQueryUpdate

open L4Factoidal.XPath4

/-- The callbacks into the XQuery 4.0 evaluator. -/
structure UCb where
  eval : Env → Expr → M Seq
  apply : Env → Item → List Seq → M Seq
  /-- The name of a computed element (`false`) or attribute (`true`)
      constructor from a value, with the static namespaces. -/
  nameOf : Env → Seq → List (String × String) → Bool → M QN
  /-- A new document number for a node built at run time. -/
  newId : String → Env → String → Nat

/-- The binding that marks a function item as an updating function
    (§2.3): it is in the closure of the inline function item. -/
def updFnKey : QN := { uri := "#upd", loc := "updating-function" }

/-- Is a function item an updating function? -/
def isUpdatingFn : Item → Bool
  | .fn (.inline _ _ _ _ cl) => cl.any (fun (q, _) => q == updFnKey)
  | .fn (.papp f _) => isUpdatingFn f
  | .fn (.builtin q _) => q.uri == nsFN && q.loc == "put"
  | _ => false
termination_by i => sizeOf i
decreasing_by all_goals simp_wf; all_goals omega

/-- Mark a function item as updating. -/
def markUpdating : Item → Item
  | .fn (.inline ps ret body focus cl) => .fn (.inline ps ret body focus ((updFnKey, []) :: cl))
  | i => i

/-- The binding that holds the revalidation mode of the module (§3.1). -/
def revalKey : QN := { uri := "#upd", loc := "revalidation" }

/-- The revalidation mode (§3.1). Its default is implementation-defined
    ("Overwritable"); here it is `skip`, so a module without `declare
    revalidation` does not validate. -/
def revalMode (env : Env) : String :=
  match env.vars.lookup revalKey with
  | some [.atom a] => a.str
  | _ => "skip"

/-! ## The insertion sequence -/

/-- An insertion or replacement sequence (§5.1, "as though it were an
    enclosed expression in an element constructor", XQuery 3.0 §3.9.1.3
    rule 1e): adjacent atomic values become one text node (an `.atom`
    here) with their strings joined by a space, a document node gives
    its children, and attributes come before other nodes (XUTY0004).
    Returns the attributes and the other nodes, in order. -/
def insertionSeq (env : Env) (s : Seq) (attrCode : String := "XUTY0004") : M (List Item × List Item) := do
  let mut attrs : Array Item := #[]
  let mut others : Array Item := #[]
  let mut atoms : Option String := none
  let flat : Seq := s.flatMap (fun i => match i with
    | .arr ms => ms.flatten
    | x => [x])
  for i in flat do
    match i with
    | .atom a => atoms := some (match atoms with | some t => t ++ " " ++ a.str | none => a.str)
    | .node n =>
      if let some t := atoms then
        others := others.push (.atom (Atomic.ofStr t)); atoms := none
      let r := env.nrec n
      match r.kind with
      | .attribute =>
        if !others.isEmpty then err attrCode "an attribute node after a node that is not an attribute"
        attrs := attrs.push i
      | .document =>
        for c in r.children do others := others.push (.node (n.at c))
      | .namespace => err "XQTY0105" "a namespace node in an insertion sequence"
      | _ => others := others.push i
    | .map _ | .fn _ => err "XQTY0105" "a map or function item in an insertion sequence"
    | .jnode .. => err "XQTY0105" "a JNode in an insertion sequence"
    | .arr _ => err "XQTY0105" "an array in an insertion sequence"
  if let some t := atoms then others := others.push (.atom (Atomic.ofStr t))
  pure (attrs.toList, others.toList)

/-- The attribute names of an insertion: their implied namespace
    bindings must not conflict with `scope` (XUDY0023) or with each
    other (XUDY0024). -/
def checkAttrNs (env : Env) (scope : List (String × String)) (attrs : List Item) : M Unit := do
  let mut seen : List (String × String) := []
  for a in attrs do
    match a with
    | .node n =>
      let q := (env.nrec n).name
      if q.pfx != "" && q.uri != "" && q.pfx != "xml" then
        match scope.lookup q.pfx with
        | some u => if u != q.uri then err "XUDY0023" ("the prefix " ++ q.pfx ++ " is bound to another namespace")
        | none => pure ()
        match seen.lookup q.pfx with
        | some u => if u != q.uri then err "XUDY0024" ("two attributes bind the prefix " ++ q.pfx ++ " to different namespaces")
        | none => seen := (q.pfx, q.uri) :: seen
    | _ => pure ()

def kindIn (env : Env) (n : NodeRef) (ks : List NKind) : Bool := ks.contains (env.nrec n).kind

/-- The single node of a target expression, after its pending update
    list is taken off: `none` when empty (XUDY0027 is the caller's). -/
def oneNode? (s : Seq) : Option (Option NodeRef) :=
  match s with
  | [] => some none
  | [.node n] => some (some n)
  | _ => none

/-! ## The expressions -/

/-- The construction mode of the static context (XQuery 3.0 §4.6):
    `declare construction strip` is the binding `XQuery4.constructionStripKey`. -/
def constructionStrip (env : Env) : Bool :=
  env.vars.any (fun (q, _) => q.uri == "#xq" && q.loc == "construction-strip")

/-- The flags a content primitive carries in `Prim.str`. -/
def contentFlags (env : Env) (inh : String) : String :=
  inh ++ (if constructionStrip env then ",strip" else "")

/-- `insert node(s) S (as first|as last)? into|after|before T` (§5.1). -/
def evalInsert (cb : UCb) (env : Env) (src tgt : Expr) (mode : String) (inh0 : String := "inherit") : M Seq := do
  let inh := contentFlags env inh0
  let (sv, p1) := splitPul (← cb.eval env src)
  let (alist, clist) ← insertionSeq env sv
  let (tv, p2) := splitPul (← cb.eval env tgt)
  let into := mode == "into" || mode == "first" || mode == "last"
  let target ← match oneNode? tv with
    | some (some n) =>
      if into && !kindIn env n [.element, .document] then
        err "XUTY0005" "the target of insert into is not a single element or document node"
      if !into && !kindIn env n [.element, .text, .comment, .pi] then
        err "XUTY0006" "the target of insert before or after is not a single element, text, comment or processing-instruction node"
      pure n
    | some none => err "XUDY0027" "the target of an insert expression is empty"
    | none => err (if into then "XUTY0005" else "XUTY0006") "the target of an insert expression is not a single node"
  let r := env.nrec target
  let parent? := r.parent.map (target.at ·)
  if !into && parent?.isNone then err "XUDY0029" "the target of insert before or after has no parent"
  let mut prims : List Prim := []
  if !alist.isEmpty then
    if into then
      if r.kind != .element then err "XUTY0022" "attributes inserted into a document node"
      checkAttrNs env r.inscope alist
      prims := prims ++ [{ kind := .insertAttributes, target, content := alist, str := inh }]
    else
      match parent? with
      | some par =>
        let pr := env.nrec par
        if pr.kind != .element then err "XUDY0030" "attributes inserted before or after a child of a document node"
        checkAttrNs env pr.inscope alist
        prims := prims ++ [{ kind := .insertAttributes, target := par, content := alist, str := inh }]
      | none => pure ()
  if !clist.isEmpty then
    let k : PKind := match mode with
      | "first" => .insertIntoAsFirst
      | "last" => .insertIntoAsLast
      | "before" => .insertBefore
      | "after" => .insertAfter
      | _ => .insertInto
    prims := prims ++ [{ kind := k, target, content := clist, str := inh }]
  pure ((p1 ++ p2 ++ prims).map Prim.toItem)

/-- `delete node(s) T` (§5.2). -/
def evalDelete (cb : UCb) (env : Env) (tgt : Expr) : M Seq := do
  let (tv, p1) := splitPul (← cb.eval env tgt)
  let mut prims : List Prim := []
  for i in tv do
    match i with
    | .node n =>
      if (env.nrec n).parent.isSome then prims := prims ++ [{ kind := .delete, target := n }]
    | _ => err "XUTY0007" "the target of a delete expression is not a sequence of nodes"
  pure ((p1 ++ prims).map Prim.toItem)

/-- The single target of a replace expression (§5.3): XUDY0027, XUTY0008. -/
def replaceTarget (env : Env) (tv : Seq) : M NodeRef :=
  match oneNode? tv with
  | some (some n) =>
    if kindIn env n [.element, .attribute, .text, .comment, .pi] then pure n
    else err "XUTY0008" "the target of a replace expression is not a single element, attribute, text, comment or processing-instruction node"
  | some none => err "XUDY0027" "the target of a replace expression is empty"
  | none => err "XUTY0008" "the target of a replace expression is not a single node"

/-- `replace node T with E` (§5.3.1). -/
def evalReplace (cb : UCb) (env : Env) (tgt wth : Expr) (inh0 : String := "inherit") : M Seq := do
  let inh := contentFlags env inh0
  let (wv, p1) := splitPul (← cb.eval env wth)
  let (tv, p2) := splitPul (← cb.eval env tgt)
  let target ← replaceTarget env tv
  let r := env.nrec target
  let some par := r.parent | err "XUDY0009" "the target of a replace expression has no parent"
  let (alist, clist) ← insertionSeq env wv (if r.kind == .attribute then "XUTY0011" else "XUTY0010")
  if r.kind == .attribute then
    if !clist.isEmpty then err "XUTY0011" "an attribute is replaced by a node that is not an attribute"
    checkAttrNs env (env.nrec (target.at par)).inscope alist
  else if !alist.isEmpty then err "XUTY0010" "a node is replaced by an attribute node"
  pure ((p1 ++ p2 ++ [({ kind := .replaceNode, target, content := alist ++ clist, str := inh } : Prim)]).map Prim.toItem)

/-- `replace value of node T with E` (§5.3.2). -/
def evalReplaceValue (cb : UCb) (env : Env) (tgt wth : Expr) : M Seq := do
  let (wv, p1) := splitPul (← cb.eval env wth)
  -- the content of a text node constructor (XQuery 3.0 §3.9.3.4)
  let atoms ← env.atomize wv
  let text? : Option String := if atoms.isEmpty then none
    else some (String.intercalate " " (atoms.map (·.str)))
  let (tv, p2) := splitPul (← cb.eval env tgt)
  let target ← replaceTarget env tv
  let r := env.nrec target
  let prim : Prim ← if r.kind == .element then
      pure { kind := .replaceElementContent, target, content := (text?.map (fun s => [Item.atom (Atomic.ofStr s)])).getD [] }
    else
      let s := text?.getD ""
      if r.kind == .comment && ((s.splitOn "--").length > 1 || s.endsWith "-") then
        err "XQDY0072" "a comment may not contain '--' or end with '-'"
      if r.kind == .pi && (s.splitOn "?>").length > 1 then
        err "XQDY0026" "a processing instruction may not contain '?>'"
      let s := if r.kind == .pi then String.ofList (s.toList.dropWhile (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')) else s
      pure { kind := .replaceValue, target, str := s }
  pure ((p1 ++ p2 ++ [prim]).map Prim.toItem)

/-- `rename node T as N` (§5.4); `sns` are the static namespaces. -/
def evalRename (cb : UCb) (env : Env) (tgt nm : Expr) (sns : List (String × String)) (inh : String := "inherit") : M Seq := do
  let (tv, p1) := splitPul (← cb.eval env tgt)
  let target ← match oneNode? tv with
    | some (some n) =>
      if kindIn env n [.element, .attribute, .pi] then pure n
      else err "XUTY0012" "the target of a rename expression is not a single element, attribute or processing-instruction node"
    | some none => err "XUDY0027" "the target of a rename expression is empty"
    | none => err "XUTY0012" "the target of a rename expression is not a single node"
  let (nv, p2) := splitPul (← cb.eval env nm)
  let r := env.nrec target
  let q ← match r.kind with
    | .element =>
      let q ← cb.nameOf env nv sns false
      let q := if q.uri == nsXML && q.pfx == "" then { q with pfx := "xml" } else q
      if q.pfx == "xmlns" || q.uri == "http://www.w3.org/2000/xmlns/" then err "XQDY0096" "an element name in the xmlns namespace"
      if !(q.uri == "" && q.pfx == "") && q.pfx != "xml" then
        match r.inscope.lookup q.pfx with
        | some u => if u != q.uri && !(q.pfx == "" && u == "") then
            err "XUDY0023" ("the prefix " ++ (if q.pfx == "" then "(default)" else q.pfx) ++ " is bound to another namespace")
        | none => pure ()
      pure q
    | .attribute =>
      let q ← cb.nameOf env nv sns true
      let q := if q.uri == nsXML && q.pfx == "" then { q with pfx := "xml" } else q
      if q.pfx == "xmlns" || (q.pfx == "" && q.loc == "xmlns") || q.uri == "http://www.w3.org/2000/xmlns/" then
        err "XQDY0044" "an attribute name xmlns"
      if q.uri != "" && q.pfx != "xml" then
        match r.parent with
        | some par =>
          match (env.nrec (target.at par)).inscope.lookup q.pfx with
          | some u => if u != q.uri then err "XUDY0023" ("the prefix " ++ q.pfx ++ " is bound to another namespace")
          | none => pure ()
        | none => pure ()
      pure q
    | _ =>
      -- a processing instruction: the name expression of a computed PI constructor
      let as ← env.atomize nv
      match as with
      | [a] =>
        if !(a.isStringLike || a.ty == .untyped) then err "XPTY0004" "a processing-instruction name must be a string"
        let s := a.str.trimAscii.toString
        if !L4Factoidal.XSD.isNCName s then err "XQDY0041" ("invalid processing-instruction name " ++ s)
        if s.toLower == "xml" then err "XQDY0064" "a processing-instruction name xml"
        pure { uri := "", loc := s }
      | _ => err "XPTY0004" "a processing-instruction name must be one string"
  pure ((p1 ++ p2 ++ [({ kind := .rename, target, name := q, str := inh } : Prim)]).map Prim.toItem)

/-- copy-namespaces no-preserve (XQuery 3.0 §4.9): an element keeps only
    the namespace bindings its name and its attributes' names use. -/
def noPreserveXT : Nat → XT → XT
  | 0, t => t
  | f + 1, .el r ats ks =>
    let r := if r.kind != .element then r else
      let used := (if r.name.uri != "" || r.name.pfx == "" then [(r.name.pfx, r.name.uri)] else []) ++
        ats.filterMap (fun a => if a.name.uri != "" && a.name.pfx != "" then some (a.name.pfx, a.name.uri) else none)
      { r with inscope := used.eraseDups ++ [("xml", nsXML)] }
    .el r ats (ks.map (noPreserveXT f))
  | _, .lf r => .lf r

/-- The copy of a node for copy modify (§5.6 step 1): a new tree with a
    new identity; types removed (`xs:untyped`, `xs:untypedAtomic`), and
    no document URI. -/
def copyNode (cb : UCb) (env : Env) (n : NodeRef) (salt : String) (preserve : Bool := true) : Item :=
  let t := untypeXT 100000 (env.readXT 100000 n)
  let t := if preserve then t else noPreserveXT 100000 t
  let ((), arr) := (flatXT 100000 none [] t).run #[]
  let d : Doc := { nodes := arr }
  let id := cb.newId "upd-copy" env (salt ++ "/" ++ toString n.doc ++ "/" ++ toString n.idx)
  .node { doc := id, idx := 0, rt := some d }

/-- `upd-copy`: one copy clause of copy modify (XUTY0013). -/
def evalCopy (cb : UCb) (env : Env) (src : Expr) (salt : String) (preserve : Bool := true) : M Seq := do
  let (sv, p1) := splitPul (← cb.eval env src)
  match sv with
  | [.node n] => pure (copyNode cb env n salt preserve :: p1.map Prim.toItem)
  | _ => err "XUTY0013" "a copy clause does not give a single node"

/-- The revalidation hook: applied to every document `applyUpdates`
    changed (`XQueryUpdate.Revalidate`). -/
abbrev RevalFn := Env → String → Applied → M Applied

/-- `upd-modify`: the modify and return clauses of copy modify (§5.6
    steps 2 to 4). `vs` are the copy variables. -/
def evalModify (cb : UCb) (reval : RevalFn) (env : Env) (m r : Expr) (vs : List QN) (mode : String := "") : M Seq := do
  -- the copies' pending update lists are on the variables' values
  let mut copies : List Nat := []
  let mut copyPul : List Prim := []
  for v in vs do
    match env.vars.lookup v with
    | some s =>
      let (xs, ps) := splitPul s
      copyPul := copyPul ++ ps
      for x in xs do
        match x with
        | .node n => copies := n.doc :: copies
        | _ => pure ()
    | none => pure ()
  -- bind the variables to the copies only (their lists stay with the result)
  let env1 := { env with vars := env.vars.map (fun (q, s) => if vs.contains q then (q, (splitPul s).1) else (q, s)) }
  let (_, pul) := splitPul (← cb.eval env1 m)
  for p in pul do
    if p.kind == .put then err "XUDY0037" "fn:put in the modify clause of a copy modify expression"
    if !copies.contains p.target.doc then
      err "XUDY0014" "the modify clause changes a node that the copy clause did not create"
  let a ← applyUpdates env1 pul
  let a ← reval env1 (if mode == "" then revalMode env1 else mode) a
  let env2 := { env1 with vars := env1.vars.map (fun (q, s) =>
    if vs.contains q then (q, s.map (fun i => match i with | .node n => .node (a.refresh n) | x => x)) else (q, s)) }
  let res ← cb.eval env2 r
  pure (res ++ copyPul.map Prim.toItem)

/-- `invoke updating F(args)` (§5.5). -/
def evalInvoke (cb : UCb) (env : Env) (f : Expr) (args : List Expr) : M Seq := do
  let (fv, p1) := splitPul (← cb.eval env f)
  let mut avs : List Seq := []
  let mut ps : List Prim := p1
  for a in args do
    let (v, p) := splitPul (← cb.eval env a)
    avs := avs ++ [v]; ps := ps ++ p
  match fv with
  | [fi] => pure ((← cb.apply env fi avs) ++ ps.map Prim.toItem)
  | _ => err "XPTY0004" "the function of invoke updating is not a single function item"

/-- `fn:put($node, $uri, $params?)` (§6.1). -/
def evalPut (env : Env) (args : List Seq) : M Seq := do
  let (nodeArg, uriArg) := (args.headD [], args.getD 1 [])
  let n ← match nodeArg with
    | [.node n] =>
      if kindIn env n [.document, .element] then pure n
      else err "FOUP0001" "fn:put of a node that is not a document or element node"
    | [_] => err "XPTY0004" "the first argument of fn:put is not a node"
    | _ => err "XPTY0004" "the first argument of fn:put is not a single node"
  let u ← match ← env.atomize uriArg with
    | [a] => pure a.str
    | _ => err "XPTY0004" "the second argument of fn:put is not a single string"
  let u := u.trimAscii.toString
  if u.any (fun c => c == ' ' || c == '<' || c == '>' || c == '"' || c == '{' || c == '}' || c == '|' || c == '\\' || c == '^' || c == '`')
     || (u.splitOn ":").head? == some "" || u.startsWith ":" then
    err "FOUP0002" ("fn:put: not a valid URI " ++ u)
  let base := env.baseUri
  let u := if (u.splitOn ":").length > 1 || base == "" then u
    else resolveUri base u
  pure [Prim.toItem { kind := .put, target := n, str := u }]

/-- The `upd-` constructs. -/
def evalUpd (cb : UCb) (reval : RevalFn) (env : Env) (tag : String) (es : List Expr) (_ts : List IType)
    (qs : List QN) (ss : List String) : M Seq := do
  match tag, es with
  | "upd-insert", [s, t] => evalInsert cb env s t (ss.headD "into") (ss.getD 1 "inherit")
  | "upd-delete", [t] => evalDelete cb env t
  | "upd-replace", [t, w] => evalReplace cb env t w (ss.headD "inherit")
  | "upd-replace-value", [t, w] => evalReplaceValue cb env t w
  | "upd-rename", [t, n] => evalRename cb env t n (qs.map (fun q => (q.pfx, q.uri))) (ss.headD "inherit")
  | "upd-copy", [s] => evalCopy cb env s (ss.headD "") (ss.getD 1 "preserve" != "no-preserve")
  | "upd-modify", [m, r] => evalModify cb reval env m r qs (ss.getD 1 "")
  | "upd-invoke", f :: args => evalInvoke cb env f args
  | "upd-fn", [e] =>
    let v ← cb.eval env e
    pure (if ss.headD "" == "updating" then v.map markUpdating else v)
  | _, _ => err "XPST0003" ("unknown update construct " ++ tag)

end L4Factoidal.XQueryUpdate
