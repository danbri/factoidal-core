/-
L4Factoidal.XSLT4.Transform — run a compiled stylesheet: whitespace
stripping of the source documents (§4.3), the global variables and
parameters (§9.5), the host functions that XPath expressions call
(stylesheet functions §10.3 and the XSLT functions of §20–21), the
initial invocation (§2.3), and the serialization of the results
(§26) through `XPath4.Serialize`.

Spec: XSLT 4.0 editor's draft (https://qt4cg.org/specifications/xslt-40/Overview.html,
read 2026-10-28).
-/
import L4Factoidal.XSLT4.Interp

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

-- Whitespace stripping (§4.3): `XSLT4.Strip` (`filterDoc`, `stripsUnder`,
-- `stripDoc`), which `Interp` also uses for `xsl:source-document`.

/-! ## Keys (§20.2) -/

abbrev KeyIndex := Std.HashMap String (Array Nat)

/-! ## Options and results -/

structure TOpts where
  /-- The initial named template (`none`: apply templates, or
      `xsl:initial-template` when there is no source). -/
  initialTemplate : Option QN := none
  /-- The initial mode key (`none`: the default mode). -/
  initialMode : Option String := none
  /-- The initial match selection (`none`: the global context item). -/
  initialSelect : Option Seq := none
  /-- The initial function and its arguments. -/
  initialFunction : Option (QN × List Seq) := none
  globalCtx : Option Item := none
  params : List (QN × Seq) := []
  /-- The documents of the dynamic context (source documents first). -/
  env : Env := {}
  /-- The base output URI (`current-output-uri`, relative `href`s). -/
  outUri : String := ""
deriving Inhabited

structure TResult where
  /-- The raw principal result. -/
  raw : Seq
  /-- The output definition of the principal result and the
      serialization attributes of the `xsl:result-document` that wrote
      it (none: the unnamed output definition). -/
  principalFormat : String × List (String × String) := ("", [])
  /-- Secondary results: absolute href, value, output definition, the
      instruction's serialization attributes. -/
  secondary : List (String × Seq × String × List (String × String))
  msgs : List String
deriving Inhabited

/-! ## The host functions -/

def XFunction.minArity (f : XFunction) : Nat :=
  (f.params.filter (fun p => p.sel.isNone && p.body.isEmpty)).length

def XFunction.accepts (f : XFunction) (k : Nat) : Bool :=
  f.minArity ≤ k && k ≤ f.params.length

def userFnAvail (S : Sheet) (q : QN) (k : Option Nat) : Bool :=
  S.functions.any (fun f => f.name == q && (match k with | some n => f.accepts n | none => true))

def lookupV (vs : List (QN × Seq)) (q : QN) : Option Seq :=
  (vs.find? (fun (v, _) => v == q)).map (·.2)

def seedOf (c : HostCall) : Nat :=
  match lookupV c.vars vSeed with
  | some [.atom ⟨_, .int i⟩] => i.toNat
  | _ => 0

/-- Run XSLT code from a host function: a fresh state whose document
    numbers derive from the call. -/
def runFresh {α} (c : HostCall) (tag : String) (args : List Seq) (act : XM α) : M α := do
  let h := hash (tag ++ "\x00" ++ toString (seedOf c) ++ "\x00" ++ toString (args.map showSeq))
  let (v, _) ← act.run { base := (h.toNat % 1000000007) + 1 }
  pure v

/-- The key index of `kd` over document `doc` (number `di`). -/
def buildKeyIndex (S : Sheet) (env : Env) (kd : KeyDef) (root : NodeRef) : M KeyIndex := do
  let d := env.doc root
  let mut idx : KeyIndex := {}
  let lo := root.idx
  let hi := (d.get root.idx).last
  for i in [lo:hi+1] do
    let nd := root.at i
    if !(kd.pat.matches env (.node nd)) then continue
    let cx : Ctx := { env := env.focus (.node nd) 1 1 }
    let v ← match kd.use with
      | some e => (·.1) <$> (evalX cx e).run {}
      | none => do
        let (os, _) ← (run 100000 S cx kd.body).run {}
        let (v, _) ← (materializeAll env os).run {}
        pure v
    let as ← env.atomize v
    let ks := if kd.composite then [String.intercalate "\x00" (as.map groupKeyStr)] else as.map groupKeyStr
    for k in ks.eraseDups do
      idx := idx.insert k ((idx.getD k #[]).push i)
  pure idx

/-- The values of an accumulator before and after each node of the
    tree at `root` (§18.2), by one walk in document order. -/
def accumulatorValues (S : Sheet) (env : Env) (acc : Accumulator) (root : NodeRef) :
    M (Std.HashMap Nat (Seq × Seq)) := do
  let d := env.doc root
  let hi := (d.get root.idx).last
  let rootItem : Item := .node root
  let cx0 : Ctx := { env := env.focus rootItem 1 1 }
  let (init, _) ← (evalX cx0 acc.init).run {}
  let applyRules (isEnd : Bool) (nd : NodeRef) (v : Seq) : M Seq := do
    let mut v := v
    let rules := acc.rules.filter (fun r => r.isEnd == isEnd && r.pat.matches env (.node nd))
    match rules.getLast? with
    | none => pure v
    | some r =>
      let cx := (({ env := env.focus (.node nd) 1 1 } : Ctx)).bind { uri := "", loc := "value" } v
      let nv ← match r.sel with
        | some e => (·.1) <$> (evalX cx e).run {}
        | none => do
          let (os, _) ← (run 100000 S cx r.body).run {}
          let (x, _) ← (materializeAll env os).run {}
          pure x
      v := nv
      match acc.ty with
      | some t => env.coerce t v ("accumulator " ++ acc.name.show)
      | none => pure v
  let mut out : Std.HashMap Nat (Seq × Seq) := {}
  let mut cur := init
  let mut openStack : List Nat := []
  for i in [root.idx:hi+1] do
    let r := d.get i
    if r.kind == .attribute || r.kind == .namespace then continue
    -- close the nodes that end before i
    for _ in [0:openStack.length] do
      match openStack with
      | j :: rest =>
        if (d.get j).last < i then
          cur ← applyRules true (root.at j) cur
          out := out.insert j ((out.getD j ([], [])).1, cur)
          openStack := rest
        else break
      | [] => break
    cur ← applyRules false (root.at i) cur
    out := out.insert i (cur, cur)
    openStack := i :: openStack
  for j in openStack do
    cur ← applyRules true (root.at j) cur
    out := out.insert j ((out.getD j ([], [])).1, cur)
  pure out

/-- Remove `.` and `..` segments from the path of a URI (RFC 3986
    §5.2.4). -/
def removeDots (u : String) : String := Id.run do
  let (pre, path) := match u.splitOn "://" with
    | [s, rest] =>
      match rest.splitOn "/" with
      | auth :: segs => (s ++ "://" ++ auth, segs)
      | [] => (u, [])
    | _ => ("", u.splitOn "/")
  let mut out : List String := []
  for seg in path do
    if seg == "." then continue
    if seg == ".." then out := out.dropLast
    else out := out ++ [seg]
  return if pre == "" then String.intercalate "/" out else pre ++ "/" ++ String.intercalate "/" out

/-- The host function table over the dynamic context `base` (global
    variables bound), with `f` levels of nested stylesheet function
    calls. -/
def mkHost (S : Sheet) (base : Env) (keyCache : List ((String × Nat) × Thunk (M KeyIndex)))
    (accCache : List ((String × Nat) × Thunk (M (Std.HashMap Nat (Seq × Seq))))) :
    Nat → QN → Nat → Option HostFn
  | 0, _, _ => none
  | f + 1, q, k =>
    let env : Env := { base with host := mkHost S base keyCache accCache f }
    let ctxNode (c : HostCall) (what : String) : M NodeRef :=
      match c.ctx with
      | some [.node nd] => pure nd
      | some _ => err "XTTE1020" (what ++ " needs a node as context item")
      | none => err "XTDE1270" (what ++ " needs a context item")
    -- stylesheet functions (highest import precedence); an unprefixed
    -- call also finds a function in no namespace (4.0)
    let q := if q.uri == nsFN && q.pfx == "" && S.functions.any (fun g => g.name.uri == "" && g.name.loc == q.loc)
      then { q with uri := "" } else q
    let fns := S.functions.filter (fun g => g.name == q && g.accepts k)
    match fns.foldl (fun (b : Option XFunction) g => match b with
        | none => some g
        | some x => if g.prec > x.prec then some g else some x) none with
    | some fn => some fun c args => runFresh c fn.name.eqn args (do
        let mut cx : Ctx := { env := { env with ctx := none, pos := 0, size := 0, ns := c.ns, vars := env.vars }, inFn := true, tempOut := true }
        let mut i := 0
        for p in fn.params do
          let v ← match args[i]? with
            | some a => match p.ty with
              | some t => liftX (env.coerce t a ("$" ++ p.name.show ++ " of " ++ fn.name.show))
              | none => pure a
            | none =>
              -- a default value, in the focus of the call
              let dcx : Ctx := { cx with env := { cx.env with ctx := c.ctx, pos := c.pos, size := c.size } }
              bindValue 100000 S dcx p.sel p.body p.ty ("$" ++ p.name.show)
          cx := cx.bind p.name v
          i := i + 1
        let os ← run 1000000 S cx fn.body
        let v ← materializeAll env os
        match fn.ty with
        | some t => liftX (env.coerce t v ("the result of " ++ fn.name.show))
        | none => pure v)
    | none =>
    if q.uri != nsFN then none else
    match stdHost (userFnAvail S) q k with
    | some h => some h
    | none =>
    match q.loc, k with
    | "current", 0 => some fun c _ =>
        match lookupV c.vars vCurrent with
        | some v => pure v
        | none => err "XTDE1360" "current() is used where there is no current item"
    | "current-group", 0 => some fun c _ =>
        match lookupV c.vars vGroup with
        | some v => pure v
        | none => err "XTDE1061" "there is no current group"
    | "current-grouping-key", 0 => some fun c _ =>
        match lookupV c.vars vGroupKey with
        | some v => pure v
        | none => err "XTDE1071" "there is no current grouping key"
    | "current-merge-group", 0 => some fun c _ =>
        match lookupV c.vars vGroup, lookupV c.vars vMergeGroup with
        | some v, some _ => pure v
        | _, _ => err "XTDE3480" "there is no current merge group"
    | "current-merge-group", 1 => some fun c a => do
        let nm := strArg (a.getD 0 [])
        match lookupV c.vars vMergeGroup with
        | some rows => pure (rows.filterMap (fun r => match r with
            | .arr [[.atom s], [it]] => if s.str == nm then some it else none
            | _ => none))
        | none => err "XTDE3480" "there is no current merge group"
    | "current-merge-key", 0 => some fun c _ =>
        match lookupV c.vars vMergeKey with
        | some v => pure v
        | none => err "XTDE3510" "there is no current merge key"
    | "current-merge-key-array", 0 => some fun c _ =>
        match lookupV c.vars vMergeKey with
        | some v => pure [.arr (v.map (fun i => [i]))]
        | none => err "XTDE3510" "there is no current merge key"
    | "regex-group", 1 => some fun c a => do
        let i : Int := match a.getD 0 [] with
          | [.atom ⟨_, .int i⟩] => i
          | _ => -1
        match lookupV c.vars vRegex with
        | some [.arr gs] =>
            if i < 0 then pure (sStr "") else
            pure ((gs.getD i.toNat []).take 1 |>.map id |> fun x => if x.isEmpty then sStr "" else x)
        | _ => pure (sStr "")
    | "current-output-uri", 0 => some fun c _ =>
        match lookupV c.vars vOutUri with
        | some v => pure v
        | none => pure []
    | "unparsed-entity-uri", _ => some fun _ _ => pure (sStr "")
    | "unparsed-entity-public-id", _ => some fun _ _ => pure (sStr "")
    | "stream-available", 1 => some fun _ _ => pure (sBool false)
    | "copy-of", _ | "snapshot", _ => some fun c a => do
        let s ← match k, c.ctx with
          | 0, some s => pure s
          | 0, none => err "XPDY0002" "copy-of() needs a context item"
          | _, _ => pure (a.getD 0 [])
        let mut out : Array Item := #[]
        let mut j := 0
        for it in s do
          match it with
          | .node nd =>
            let id := (2 : Nat) ^ 43 + (hash (toString (seedOf c) ++ ":" ++ toString j)).toNat % 1000000000000
            out := out.push (← copyAsTree env id nd)
          | other => out := out.push other
          j := j + 1
        pure out.toList
    | "key", _ => if k != 2 && k != 3 then none else some fun c a => do
        let nm ← lexQName c.ns (strArg (a.getD 0 [])) false "XTDE1260"
        let kds := S.keys.filter (fun kd => kd.name == nm)
        if kds.isEmpty then err "XTDE1260" ("no key named " ++ nm.show)
        let root ← match a.getD 2 [] with
          | [.node t] => pure t
          | [] => if k == 3 then err "XTDE1270" "key() needs a node" else do
              let nd ← ctxNode c "key()"
              pure (env.treeRoot nd)
          | _ => err "XPTY0004" "the third argument of key() must be a node"
        let rootN := if k == 3 then root else root
        if k == 2 && (env.nrec (env.treeRoot rootN)).kind != .document then
          err "XTDE1270" "key() with two arguments needs a context node in a document"
        let vals ← env.atomize (a.getD 1 [])
        let comp := kds.any (·.composite)
        let wanted := if comp then [String.intercalate "\x00" (vals.map groupKeyStr)] else vals.map groupKeyStr
        let mut hits : Array NodeRef := #[]
        for kd in kds do
          let idx ← match rootN.rt, keyCache.lookup (kd.name.eqn, rootN.doc) with
            | none, some th => if rootN.idx == 0 then th.get else buildKeyIndex S env kd rootN
            | _, _ => buildKeyIndex S env kd rootN
          for w in wanted do
            for i in idx.getD w #[] do
              let nd := rootN.at i
              -- with a third argument: only nodes in its subtree
              if k == 3 && (i < rootN.idx || i > (env.nrec rootN).last) then continue
              hits := hits.push nd
        pure ((sortNodes hits.toList).map Item.node)
    | "document", _ => if k != 1 && k != 2 then none else some fun c a => do
        let base := match a.getD 1 [] with
          | [.node b] =>
              let d := env.doc b
              if d.baseUri != "" then d.baseUri else d.uri
          | _ => ""
        let mut out : Array NodeRef := #[]
        for it in a.getD 0 [] do
          let (u, b) := match it with
            | .node nd =>
                let d := env.doc nd
                (env.nodeString nd, if base != "" then base else (if d.baseUri != "" then d.baseUri else d.uri))
            | .atom x => (x.str, if base != "" then base else S.baseUri)
            | _ => ("", S.baseUri)
          let b := if b == "" then S.baseUri else b
          let abs := if u == "" then b else resolveUri b u
          let abs := match abs.splitOn "#" with
            | p :: _ => p
            | [] => abs
          let abs := removeDots abs
          match callFn 100000 env { uri := nsFN, loc := "doc" } [sStr abs] with
          | .ok [.node d] => out := out.push d
          | .ok _ => pure ()
          | .error e =>
              match callFn 100000 env { uri := nsFN, loc := "doc" } [sStr u] with
              | .ok [.node d] => out := out.push d
              | _ => throw { e with code := if e.code == "FODC0002" then "FODC0002" else e.code }
        let _ := c
        pure ((sortNodes out.toList).map Item.node)
    | "accumulator-before", 1 | "accumulator-after", 1 => some fun c a => do
        let nm ← lexQName c.ns (strArg (a.getD 0 [])) false "XTDE3340"
        let some acc := S.accumulators.find? (·.name == nm) | err "XTDE3340" ("no accumulator named " ++ nm.show)
        let nd ← ctxNode c q.loc
        let r := env.nrec nd
        if r.kind == .attribute || r.kind == .namespace then err "XTTE3360" "accumulators are not defined on attribute and namespace nodes"
        let root := env.treeRoot nd
        let vals ← match nd.rt, accCache.lookup (acc.name.eqn, nd.doc) with
          | none, some th => th.get
          | _, _ => accumulatorValues S env acc root
        match vals.get? nd.idx with
        | some (b, af) => pure (if q.loc == "accumulator-before" then b else af)
        | none => pure []
    | _, _ => none

/-! ## The transformation -/

def xslGlobals : QN := xv "globals"

/-- Evaluate the global variables and parameters (§9.5): repeated
    passes, each evaluating the declarations whose references are
    already bound. -/
def evalGlobals (S : Sheet) (o : TOpts) (env0 : Env) : M Env := do
  -- the declaration of each name with the highest precedence
  let mut decls : List Global := []
  for g in S.globals do
    match decls.find? (·.name == g.name) with
    | some h => if g.prec > h.prec then decls := (decls.filter (·.name != g.name)) ++ [g]
    | none => decls := decls ++ [g]
  let staticNames := S.statics.map (·.1)
  let mut env := env0
  let mut pending := decls.filter (fun g => !(g.isStatic && staticNames.contains g.name))
  for _ in [0:decls.length + 1] do
    if pending.isEmpty then break
    let mut next : List Global := []
    let mut progress := false
    let mut lastErr : Option Err := none
    for g in pending do
      let host := mkHost S env [] [] 100000
      let one := if o.globalCtx.isSome then 1 else 0
      let genv : Env := { env with host, ctx := o.globalCtx.map (fun i => [i]), pos := one, size := one }
      let supplied := if g.isParam then lookupV o.params g.name else none
      let act : XM Seq := match supplied with
        | some v => match g.ty with
          | some t => liftX (genv.coerce t v ("$" ++ g.name.show))
          | none => pure v
        | none =>
          if g.required then xerr "XTDE0050" ("no value given for the required parameter $" ++ g.name.show)
          else bindValue 100000 S { env := genv } g.sel g.body g.ty ("$" ++ g.name.show)
      match act.run { base := (hash g.name.eqn).toNat % 100000 + 7 } with
      | .ok (v, _) =>
          env := { env with vars := env.vars ++ [(g.name, v)] }
          progress := true
      | .error e =>
          if e.code == "XPST0008" then next := next ++ [g]; lastErr := some e
          else throw e
    pending := next
    if !progress then
      match lastErr with
      | some e => throw (if pending.length > 0 && pending.any (fun g => e.msg.contains g.name.show) then
          { code := "XTDE0640", msg := "circular definition of global variables: " ++ e.msg } else e)
      | none => break
  pure env

/-- Run a stylesheet. -/
def transform (S : Sheet) (o : TOpts) : M TResult := do
  let docs := o.env.docs.map (stripDoc S)
  let dfs := S.decimalFormats ++ o.env.decimalFormats
  let ns0 := S.ns.filter (·.1 != "")
  let vars0 := [(xslGlobals, [])] ++ S.statics.reverse
  let env0 : Env := { o.env with docs, decimalFormats := dfs, baseUri := S.baseUri, ns := ns0, vars := vars0 }
  if S.globalCtxUse == "required" && o.globalCtx.isNone then
    err "XTDE3086" "the stylesheet requires a global context item"
  let globalCtx := if S.globalCtxUse == "absent" then none else o.globalCtx
  let o := { o with globalCtx }
  let env ← evalGlobals S o env0
  -- key and accumulator caches over the documents of the context
  let keyCache : List ((String × Nat) × Thunk (M KeyIndex)) :=
    (List.range docs.size).flatMap (fun di => S.keys.map (fun kd =>
      ((kd.name.eqn, di), Thunk.mk (fun _ => buildKeyIndex S { env with host := mkHost S env [] [] 100000 } kd (NodeRef.mk' di 0)))))
  let accCache : List ((String × Nat) × Thunk (M (Std.HashMap Nat (Seq × Seq)))) :=
    (List.range docs.size).flatMap (fun di => S.accumulators.map (fun acc =>
      ((acc.name.eqn, di), Thunk.mk (fun _ => accumulatorValues S { env with host := mkHost S env [] [] 100000 } acc (NodeRef.mk' di 0)))))
  let host := mkHost S env keyCache accCache 100000
  let env := { env with host, vars := env.vars ++ [(vOutUri, if o.outUri == "" then [] else [.atom (Atomic.ofUri o.outUri)])] }
  let focusEnv := match o.globalCtx with
    | some i => env.focus i 1 1
    | none => env
  let cx : Ctx := { env := focusEnv, mode := S.defaultMode, backCompat := ({ version := S.version } : SCx).backCompat }
  let act : XM (List Out) := do
    match o.initialFunction with
    | some (fq, args) =>
      match host fq args.length with
      | some h => do pure (Out.ofSeq (← liftX (h { vars := env.vars, ns := env.ns } args)))
      | none => xerr "XTDE0041" ("no stylesheet function " ++ fq.show ++ "#" ++ toString args.length)
    | none =>
    let initT := match o.initialTemplate with
      | some t => some t
      | none => if o.initialMode.isNone && o.initialSelect.isNone && o.globalCtx.isNone then
          some { uri := nsXSL, loc := "initial-template" } else none
    match initT with
    | some tn =>
      let cands := S.templates.toList.filter (fun t => t.name == some tn)
      match cands.foldl (fun (b : Option Tmpl) t => match b with
          | none => some t
          | some x => if t.prec > x.prec then some t else some x) none with
      | none => xerr "XTDE0040" ("no template named " ++ tn.show)
      | some t =>
        for p in t.params do
          if p.required && !p.tunnel then
            xerr "XTDE0700" ("no value for the required parameter $" ++ p.name.show ++ " of the initial template")
        let cx' := if t.ctxAbsent then cx.noFocus else cx
        invoke 1000000 S cx' t [] []
    | none =>
      let mode := o.initialMode.getD S.defaultMode
      let mode := if mode == "#default" then S.defaultMode else mode
      if mode != "#unnamed" && mode != S.defaultMode && !(S.modes.any (·.name == mode)) &&
          !(S.templates.any (fun t => t.modes.contains mode || t.modes.contains "#all")) then
        xerr "XTDE0045" ("the initial mode " ++ mode ++ " is not declared")
      let sel := match o.initialSelect with
        | some s => s
        | none => match o.globalCtx with | some i => [i] | none => []
      applyT 1000000 S { cx with mode } sel mode [] [] none
  let (os, st) ← act.run { base := 1 }
  let (raw, st) ← (materializeAll env os).run st
  let abs (h : String) : String := if o.outUri == "" then h else resolveUri o.outUri h
  -- §25.1: a result document with no href (or the base output URI) is
  -- the principal result
  let isPrincipal (h : String) : Bool := h == "" || (o.outUri != "" && abs h == o.outUri)
  let (raw, pf) ← match st.results.toList.find? (fun (h, _, _, _) => isPrincipal h) with
    | some (_, v, f, sp) =>
        if !raw.isEmpty then err "XTDE1490" "the principal result is written twice"
        else pure (v, (f, sp))
    | none => pure (raw, ("", []))
  let secs := st.results.toList.filter (fun (h, _, _, _) => !isPrincipal h)
  pure { raw, principalFormat := pf, secondary := secs.map (fun (h, v, f, sp) => (abs h, v, f, sp)), msgs := st.msgs.toList }

/-! ## Serialization (§26) -/

def serKinds : List String :=
  ["allow-duplicate-names", "build-tree", "byte-order-mark", "canonical", "cdata-section-elements",
   "csv-header", "csv-quote-character", "csv-separator", "doctype-public", "doctype-system", "encoding",
   "escape-solidus", "escape-uri-attributes", "html-version", "include-content-type", "indent",
   "indent-unit", "item-separator", "json-lines", "json-node-output-method", "line-ending", "media-type",
   "method", "normalization-form", "omit-xml-declaration", "standalone", "suppress-indentation",
   "undeclare-prefixes", "use-character-maps", "version"]

/-- The characters a named character map maps, with the maps it uses
    first (§26.1). -/
def Sheet.charMapOf (S : Sheet) : Nat → String → M (List (Char × String))
  | 0, _ => err "XTSE1600" "character maps use each other in a cycle"
  | f + 1, key => do
    -- the declaration with the highest import precedence (the last)
    match S.charMaps.reverse.find? (·.1 == key) with
    | none => err "XTSE1590" ("unknown character map " ++ key)
    | some (_, uses, own) =>
      let mut out : List (Char × String) := []
      for u in uses do out := out ++ (← S.charMapOf f u)
      pure (out ++ own)

/-- Serialization parameters from `xsl:output` properties. -/
def serParamsOfProps (S : Sheet) (props : List (String × String)) : M SerParams := do
  let mut p : SerParams := {}
  for (name0, v) in props do
    let name := if name0 == "output-version" then "version" else name0
    if name == "build-tree" || name == "parameter-document" || name == "indent-attributes" then continue
    if name == "use-character-maps" then
      let mut cm : List (Char × String) := []
      for t in (v.split (· == ' ')).toList.map (·.toString) |>.filter (· != "") do
        let key ← match lexQName S.ns t false "XTSE1590" with
          | .ok q => pure q.eqn
          | .error _ => pure t
        cm := cm ++ (← S.charMapOf 20 key)
      p ← p.set "use-character-maps" (.cm cm)
      continue
    let some kind := paramKinds.lookup name | continue
    let pv ← match kind with
      | .bool => pure (PVal.b (← parseYesNo name v))
      | .boolOpt =>
        match trimWs v with
        | "omit" => pure (PVal.ob none)
        | x => pure (PVal.ob (some (← parseYesNo name x)))
      | .qnames =>
        let toks := (trimWs v).splitOn " " |>.filter (· != "")
        pure (PVal.qs (← toks.mapM (resolveLexQN S.ns)))
      | .method =>
        let x := trimWs v
        if x.startsWith "Q{" then pure (PVal.s x)
        else if serMethods.contains x then pure (PVal.s x)
        else err "SEPM0016" ("unknown method " ++ x)
      | _ => pure (PVal.s v)
    p ← p.set name pv
  p.check

/-- The output definition properties for `key` (`""`: the unnamed
    one), with the instruction's own properties after them. -/
def Sheet.outputProps (S : Sheet) (key : String) (extra : List (String × String) := []) :
    M (List (String × String)) := do
  let base ← match S.outputs.lookup key with
    | some ps => pure ps
    | none => if key == "" then pure [] else err "XTDE1460" ("no output definition named " ++ key)
  pure ((base.filter (fun (k, _) => !(extra.any (·.1 == k)))) ++ extra)

/-- The default output method (§26.1): `html` when the result's first
    element is `html` in no namespace, `xhtml` when it is in the XHTML
    namespace, else `xml`. -/
def defaultMethod (env : Env) (s : Seq) : String :=
  let firstElem : Option NodeRef := s.findSome? (fun i => match i with
    | .node n =>
      let r := env.nrec n
      if r.kind == .element then some n
      else if r.kind == .document then
        -- no text before the element
        let kids := r.children.toList.map (n.at ·)
        let before := kids.takeWhile (fun c => (env.nrec c).kind != .element)
        if before.any (fun c => (env.nrec c).kind == .text && !(env.nrec c).value.toList.all Char.isWhitespace) then none
        else kids.find? (fun c => (env.nrec c).kind == .element)
      else none
    | _ => none)
  match firstElem with
  | some n =>
    let q := (env.nrec n).name
    if q.uri == "" && q.loc.toLower == "html" then "html"
    else if q.uri == nsXHTML && q.loc == "html" then "xhtml"
    else "xml"
  | none => "xml"

/-- Serialize a result with the output definition `props`. -/
def serializeResult (S : Sheet) (env : Env) (props : List (String × String)) (s : Seq) : M String := do
  let props := if props.any (·.1 == "method") then props else props ++ [("method", defaultMethod env s)]
  -- XSLT's default: the XML declaration is written (§26)
  let m := (props.lookup "method").getD "xml"
  let props := if (m == "xml" || m == "xhtml") && !(props.any (·.1 == "omit-xml-declaration")) then
      props ++ [("omit-xml-declaration", "no")] else props
  let p ← serParamsOfProps S props
  let out ← env.serializeWith p s
  let bom := match props.lookup "byte-order-mark" with
    | some v => ["yes", "true", "1"].contains v.trimAscii.toString
    | none => false
  pure (if bom then "\uFEFF" ++ out else out)

end L4Factoidal.XSLT4
