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
import L4Factoidal.XSLT4.Package

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

/-! ## Whitespace stripping (§4.3) -/

/-- A copy of `d` with only the nodes `keep` admits (indices remapped,
    document order kept). -/
def filterDoc (d : Doc) (keep : Nat → Bool) : Doc := Id.run do
  let sz := d.nodes.size
  let mut newIdx : Array (Option Nat) := Array.replicate sz none
  let mut pre : Array Nat := Array.replicate (sz + 1) 0
  let mut k := 0
  for i in [0:sz] do
    if keep i then
      newIdx := newIdx.set! i (some k)
      k := k + 1
    pre := pre.set! (i + 1) k
  let mut out : Array NRec := #[]
  for i in [0:sz] do
    if keep i then
      let r := d.get i
      let mp (j : Nat) : Option Nat := newIdx.getD j none
      let lastNew := pre.getD (r.last + 1) k
      let nl := if lastNew == 0 then 0 else lastNew - 1
      out := out.push { r with parent := r.parent.bind mp, children := r.children.filterMap mp, attrs := r.attrs.filterMap mp, last := nl }
  return { d with nodes := out }

def nameTestPrio : NameTest → Float
  | .name _ => 0
  | .ns _ | .loc _ => -0.25
  | .any => -0.5

/-- Is a whitespace text node with parent element `p` stripped? -/
def stripsUnder (S : Sheet) (d : Doc) (p : Nat) : Bool := Id.run do
  let r := d.get p
  if r.kind != .element then return false
  -- xml:space on the element or its nearest ancestor that has one
  let mut cur : Option Nat := some p
  for _ in [0:100000] do
    match cur with
    | none => break
    | some j =>
      let x := d.get j
      for a in x.attrs.toList do
        let ar := d.get a
        if ar.name.uri == nsXML && ar.name.loc == "space" then
          if ar.value.trimAscii.toString == "preserve" then return false
          if ar.value.trimAscii.toString == "default" then cur := none
      if cur.isNone then break
      cur := x.parent
  let mut best : Option (Nat × Float × Bool) := none
  for (t, strip, prec) in S.space do
    if !(nameTestMatches t r.name) then continue
    let pr := nameTestPrio t
    match best with
    | none => best := some (prec, pr, strip)
    | some (bp, bpr, _) =>
      if prec > bp || (prec == bp && pr ≥ bpr) then best := some (prec, pr, strip)
  match best with
  | some (_, _, s) => return s
  | none => return false

def stripDoc (S : Sheet) (d : Doc) : Doc :=
  if S.space.isEmpty || !(S.space.any (·.2.1)) then d else
  filterDoc d (fun i =>
    let r := d.get i
    if r.kind != .text || !(r.value.toList.all (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')) then true
    else match r.parent with
      | some p => !(stripsUnder S d p)
      | none => true)

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
  /-- Parameters of the initial template (non-tunnel and tunnel). -/
  templateParams : List (QN × Seq) := []
  tunnelParams : List (QN × Seq) := []
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
  /-- The messages as document nodes. -/
  msgDocs : List Item := []
deriving Inhabited

/-! ## The host functions -/

def XFunction.minArity (f : XFunction) : Nat :=
  (f.params.filter (fun p => p.required)).length

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

/-- The index string of a key value: with a collation other than the
    codepoint collation, strings are indexed by their collation key. -/
def keyStrOf (env : Env) (coll : String) (a : Atomic) : String :=
  match (if coll == "" then none else (collationOf env.baseUri coll).toOption) with
  | some c =>
    if (a.ty == .untyped || a.isStringLike) && !c.isCodepoint then
      "s:" ++ String.intercalate "," ((c.key a.str).map toString)
    else groupKeyStr a
  | none => groupKeyStr a

/-- The entries of a key over the subtree at `root` (for
    `fn:map-for-key`): each distinct key value (by its index string),
    one representative value, and the node indexes in document order. -/
def keyEntries (S : Sheet) (env : Env) (kd : KeyDef) (root : NodeRef) : M (List (String × Atomic × Array Nat)) := do
  let d := env.doc root
  let mut keys : Array (String × Atomic) := #[]
  let mut idx : Std.HashMap String (Array Nat) := {}
  for i in [root.idx:(d.get root.idx).last+1] do
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
    for a in as do
      let k := groupKeyStr a
      match idx.get? k with
      | some ns => if ns.back? != some i then idx := idx.insert k (ns.push i)
      | none => keys := keys.push (k, a); idx := idx.insert k #[i]
  pure (keys.toList.map (fun (k, a) => (k, a, idx.getD k #[])))

/-- The key index of `kd` over document `doc` (number `di`). -/
def buildKeyIndex (S : Sheet) (env : Env) (kd : KeyDef) (root : NodeRef) : M KeyIndex := do
  let d := env.doc root
  let mut idx : KeyIndex := {}
  let lo := root.idx
  let hi := (d.get root.idx).last
  -- namespace nodes are visited only for a pattern that can match them
  let withNs := (kd.pat.src.splitOn "namespace").length > 1
  let mut ids : Array Nat := #[]
  for i in [lo:hi+1] do
    ids := ids.push i
    if withNs then
      for k in [0:(nsNodesOf (d.get i)).length] do ids := ids.push (nsNodeIdx i k)
  for i in ids do
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
    let kstr := keyStrOf env kd.collation
    let ks := if kd.composite then [String.intercalate "\x00" (as.map kstr)] else as.map kstr
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
    let q := if q.uri == nsFN && q.pfx == "" && S.functions.any (fun g => g.name.uri == "" && g.name.loc == q.loc && g.accepts k)
      then { q with uri := "" } else q
    let fns := S.functions.filter (fun g => g.name == q && g.accepts k)
    match fns.foldl (fun (b : Option XFunction) g => match b with
        | none => some g
        | some x => if g.prec > x.prec then some g else some x) none with
    | some fn => some fun c args => runFresh c fn.name.eqn args (do
        if let [.staticErr "XTDE3052" msg] := fn.body then xerr "XTDE3052" msg
        let mut cx : Ctx := { env := { env with ctx := none, pos := 0, size := 0, ns := c.ns, vars := env.vars }, inFn := true, tempOut := true }
        -- the defaults see none of the parameters (XPST0008)
        let cx0 := cx
        let mut i := 0
        for p in fn.params do
          let v ← match args[i]? with
            | some a => match p.ty with
              | some t => liftX (env.coerce t a ("$" ++ p.name.show ++ " of " ++ fn.name.show))
              | none => pure a
            | none =>
              -- a default value, in the focus of the call
              let dcx : Ctx := { cx0 with env := { cx0.env with ctx := c.ctx, pos := c.pos, size := c.size } }
              -- with no select and no content the default is the empty
              -- sequence (§10.3.2)
              if p.sel.isNone && p.body.isEmpty then
                match p.ty with
                | some t => liftX (env.coerce t [] ("$" ++ p.name.show ++ " of " ++ fn.name.show))
                | none => pure []
              else bindValue 100000 S dcx p.sel p.body p.ty ("$" ++ p.name.show) "XTTE0600"
          cx := cx.bind p.name v
          i := i + 1
        let os ← run 1000000 S cx fn.body
        let v ← materializeAll env os
        match fn.ty with
        | some t => liftX (typeErrAs "XTTE0780" (env.coerce t v ("the result of " ++ fn.name.show)))
        | none => pure v)
    | none =>
    if q.uri != nsFN then none else
    match S.extraHost env q k with
    | some h => some h
    | none =>
    match stdHost (userFnAvail S) q k with
    | some h => some h
    | none =>
    match q.loc, k with
    | "function-lookup", 2 => some fun _ a => do
        -- a stylesheet function is found too (F&O 4.0 §16.1.2)
        match a.getD 0 [], a.getD 1 [] with
        | [.atom ⟨_, .qn fq⟩], [.atom ⟨_, .int ar⟩] =>
          if ar ≥ 0 && userFnAvail S fq (some ar.toNat) then pure [.fn (.builtin fq ar.toNat)]
          else callFn 100000 env q a
        | _, _ => callFn 100000 env q a
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
        | some v => if showSeq v == showSeq noGroupKey then err "XTDE1071" "there is no current grouping key" else pure v
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
    | "regex-groups", 0 => some fun c _ =>
        -- fn:regex-groups (§17.2.1): the current captured groups
        match lookupV c.vars vRegex with
        | some v => pure v
        | none => pure [.map []]
    | "regex-group", 1 => some fun c a => do
        -- fn:regex-group(G) is regex-groups()?G?value otherwise "" (§17.2.2)
        let key ← match a.getD 0 [] with
          | [.atom k] => pure k
          | _ => err "XPTY0004" "regex-group() needs an integer or a string"
        let key := if key.ty == .untyped then Atomic.ofStr key.str else key
        match lookupV c.vars vRegex with
        | some [.map gs] =>
          -- a named group is keyed by its name; its number is in `nr`
          let byNr := gs.find? (fun (_, r) => match r with
            | [.map rec] => rec.any (fun (k1, v) => k1.str == "nr" && (match v with | [.atom a] => atomicEqual a key | _ => false))
            | _ => false)
          match gs.find? (fun (k0, _) => atomicEqual k0 key) |>.orElse (fun _ => byNr) with
          | some (_, [.map rec]) => pure ((rec.find? (fun (k1, _) => k1.str == "value")).map (·.2) |>.getD (sStr ""))
          | _ => pure (sStr "")
        | _ => pure (sStr "")
    | "current-output-uri", 0 => some fun c _ =>
        match lookupV c.vars vOutUri with
        | some v => pure v
        | none => pure []
    | "unparsed-entity-uri", _ => some fun _ _ => pure (sStr "")
    | "unparsed-entity-public-id", _ => some fun _ _ => pure (sStr "")
    | "stream-available", 1 => some fun _ _ => pure (sBool false)
    | "apply-templates", _ => if k != 1 && k != 2 then none else some fun c a => do
        -- fn:apply-templates (§6.9.3.1): the effect of xsl:apply-templates
        let opts := match a.getD 1 [] with
          | [.map kvs] => kvs
          | _ => []
        let opt (key : String) : Option Seq := (opts.find? (fun (k0, _) => k0.str == key)).map (·.2)
        let qmap (key : String) : M (List (QN × Seq)) :=
          match opt key with
          | some [.map kvs] => kvs.mapM (fun (k0, v) => (match k0.v with
              | .qn q => pure (q, v)
              | _ => err "XPTY0004" ("the keys of " ++ key ++ " must be QNames")))
          | some [] | none => pure []
          | _ => err "XPTY0004" (key ++ " must be a map")
        let ps ← qmap "params"
        let tps ← qmap "tunnel-params"
        let cur := match lookupV c.vars vMode with
          | some [.atom m] => m.str
          | _ => "#unnamed"
        let named (q : QN) : M String :=
          -- a named mode must be declared and not private (XTDE0565)
          match S.modes.find? (·.name == q.eqn) with
          | some md => if md.vis == "private" then err "XTDE0565" ("mode " ++ q.show ++ " is private") else pure q.eqn
          | none => err "XTDE0565" ("mode " ++ q.show ++ " is not declared")
        let mode ← match opt "mode" with
          | none | some [] => pure "#unnamed"
          | some [.atom m] =>
            (match m.v with
            | .qn q => named q
            | _ => if m.str == "#current" then pure cur else if m.str == "#unnamed" then pure "#unnamed"
              else err "XPTY0004" ("invalid mode " ++ m.str))
          | _ => err "XPTY0004" "invalid mode option"
        runFresh c "apply-templates" a (do
          let cx : Ctx := { env := { env with ctx := c.ctx, pos := c.pos, size := c.size, ns := c.ns, vars := env.vars } }
          -- the tunnel parameters in force are passed on (§10.1.3)
          let inForce : List (QN × Seq) := match lookupV c.vars vTunnel with
            | some [.map kvs] => kvs.filterMap (fun (k0, v) => match k0.v with
                | .qn q => some (q, v)
                | _ => none)
            | _ => []
          let tun := tps ++ inForce.filter (fun (q, _) => !tps.any (·.1 == q))
          let os ← applyT 100000 S cx (a.getD 0 []) mode ps tun none
          materializeAll env os)
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
            let cenv := if c.baseUri != "" then { env with baseUri := c.baseUri } else env
            out := out.push (← if q.loc == "snapshot" then snapshotAsTree cenv id nd else copyAsTree cenv id nd)
          | other => out := out.push other
          j := j + 1
        pure out.toList
    | "map-for-key", _ => if k != 1 && k != 2 then none else some fun c a => do
        -- fn:map-for-key (§20.2.3)
        let nm ← match a.getD 0 [] with
          | [.atom x] => match x.v with
            | .qn q => pure q
            | _ => lexQName c.ns x.str false "XTDE1260"
          | _ => err "XPTY0004" "the key name must be a string or a QName"
        let kds := S.keys.filter (fun kd => kd.name == nm)
        if kds.isEmpty then err "XTDE1260" ("no key named " ++ nm.show)
        if kds.any (fun kd => kd.composite || !(kd.collation == "" || kd.collation == codepointCollation)) then
          err "XTDE1262" ("the key " ++ nm.show ++ " is composite or has a collation other than the codepoint collation")
        let root ← match a.getD 1 [] with
          | [.node t] => pure t
          | [] => do pure (env.treeRoot (← ctxNode c "map-for-key()"))
          | _ => err "XPTY0004" "the second argument of map-for-key() must be a node"
        if (env.nrec (env.treeRoot root)).kind != .document then
          err "XTDE1270" "map-for-key() needs a node in a tree whose root is a document node"
        let mut order : Array String := #[]
        let mut vals : Std.HashMap String (Atomic × Array Nat) := {}
        for kd in kds do
          for (ks, av, ns) in ← keyEntries S env kd root do
            match vals.get? ks with
            | some (a0, old) => vals := vals.insert ks (a0, (old ++ ns))
            | none => order := order.push ks; vals := vals.insert ks (av, ns)
        let entries := order.toList.filterMap (fun ks => (vals.get? ks).map (fun (av, ns) =>
          (av, (sortNodes (ns.toList.eraseDups.map root.at)).map Item.node)))
        pure [.map entries]
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
        let rootN := root
        if (env.nrec (env.treeRoot rootN)).kind != .document then
          err "XTDE1270" "key() needs a node in a tree whose root is a document node"
        let vals ← env.atomize (a.getD 1 [])
        let comp := kds.any (·.composite)
        let ks := keyStrOf env (kds.head?.map (·.collation) |>.getD "")
        let wanted := if comp then [String.intercalate "\x00" (vals.map ks)] else vals.map ks
        let mut hits : Array NodeRef := #[]
        for (kd, j) in S.keys.zipIdx do
          if kd.name != nm then continue
          let idx ← match rootN.rt, keyCache.lookup (kd.name.eqn ++ "#" ++ toString j, rootN.doc) with
            | none, some th => if rootN.idx == 0 then th.get else buildKeyIndex S env kd rootN
            | _, _ => buildKeyIndex S env kd rootN
          for w in wanted do
            for i in idx.getD w #[] do
              let nd := rootN.at i
              -- with a third argument: only nodes in its subtree
              if k == 3 && (i < rootN.idx || i > (env.nrec rootN).last) then continue
              hits := hits.push nd
        pure ((sortNodes hits.toList).map Item.node)
    | "doc", _ | "doc-available", _ => if k != 1 && k != 2 then none else some fun c a => do
        -- a relative reference is resolved against the static base URI of
        -- the call (F&O 4.0 §14.6.1), which differs between stylesheet
        -- modules and under `xml:base`
        let plain : Env := { env with host := fun _ _ => none }
        let fq : QN := { uri := nsFN, loc := q.loc }
        let b := if c.baseUri != "" then c.baseUri else S.baseUri
        -- §4.3: xsl:strip-space applies to the documents that fn:doc reads
        -- (unless the call gives its own strip-space option)
        let own := match a.getD 1 [] with
          | [.map kvs] => kvs.any (fun (k, _) => k.str == "strip-space")
          | _ => false
        let strip (v : Seq) : Seq := if own then v else v.map (fun it => match it with
          | .node nd => match nd.rt with
            | some d => .node { nd with rt := some (stripDoc S d) }
            | none => it
          | _ => it)
        strip <$> match a.getD 0 [] with
        | [.atom x] =>
          let u := x.str
          if (u.splitOn "#").length > 1 || uriHasScheme u || b == "" then callFn 100000 plain fq a
          else
            match callFn 100000 plain fq ([sStr (resolveRef b u)] ++ a.drop 1) with
            | .ok v =>
                let no := match v with
                  | [.atom y] => (match y.v with | .bool false => true | _ => false)
                  | _ => false
                if no then callFn 100000 plain fq a else pure v
            | .error e => match callFn 100000 plain fq a with
              | .ok v => pure v
              | .error _ => throw e
        | _ => callFn 100000 plain fq a
    | "document", _ => if k != 1 && k != 2 then none else some fun c a => do
        -- §20.1: the base URI is that of the second argument (a node, or
        -- the `base-uri` option), else the base URI of a node item, else
        -- the static base URI of the call
        let staticBase := if c.baseUri != "" then c.baseUri else S.baseUri
        let base? : Option (Option String) ← match a.getD 1 [] with
          | [.node b] => pure (some (env.baseUriOf b))
          | [.map kvs] => pure ((kvs.find? (fun (k, _) => k.str == "base-uri")).map (fun (_, v) =>
              match v with
              | [.atom x] => some x.str
              | _ => none))
          | [] => pure none
          | _ => err "XPTY0004" "the second argument of document() must be a node or a map"
        let mut refs : Array (String × Option String) := #[]
        for it in a.getD 0 [] do
          match it with
          | .node nd =>
              for x in ← env.atomize [.node nd] do
                refs := refs.push (x.str, base?.getD (env.baseUriOf nd))
          | .atom x =>
              if !(x.isStringLike || x.is .anyURI) then
                err "XPTY0004" "document() expects strings, URIs or nodes"
              refs := refs.push (x.str, base?.getD (if staticBase == "" then none else some staticBase))
          | _ => err "XPTY0004" "document() expects strings, URIs or nodes"
        let mut out : Array NodeRef := #[]
        for (u0, b?) in refs do
          let u := u0.trimAscii.toString
          let abs ← if uriHasScheme u then pure u else match b? with
            | some b => pure (resolveRef b u)
            | none => err "XTDE1162" ("no base URI to resolve the relative reference '" ++ u ++ "'")
          let (abs, frag) := match abs.splitOn "#" with
            | p :: f :: _ => (p, some f)
            | _ => (abs, none)
          let abs := removeDots abs
          -- §20.1: a fragment identifier this processor does not recognize
          -- (only a shorthand pointer, an NCName, is)
          if let some f := frag then
            if !isNCName f then err "XTDE1160" ("fragment identifier '" ++ f ++ "' is not recognized")
          -- the options of the call go to fn:doc; a document read with
          -- options is another document than one read without them
          let opts : List Seq := match a.getD 1 [] with
            | [.map kvs] => [[.map kvs]]
            | _ => []
          let plain : Env := { env with host := fun _ _ => none }
          let d ← match callFn 100000 plain { uri := nsFN, loc := "doc" } ([sStr abs] ++ opts) with
            | .ok [.node d] => pure (some d)
            | .ok _ => pure none
            | .error e =>
                match callFn 100000 plain { uri := nsFN, loc := "doc" } ([sStr u] ++ opts) with
                | .ok [.node d] => pure (some d)
                | _ => throw e
          let own := match opts with
            | [[.map kvs]] => kvs.any (fun (k, _) => k.str == "strip-space")
            | _ => false
          let d := if own then d else d.map (fun nd => match nd.rt with
            | some x => { nd with rt := some (stripDoc S x) }
            | none => nd)
          let d := match d, opts with
            | some nd, [o] => if nd.rt.isSome then
                some { nd with doc := (2 : Nat) ^ 44 + (hash (abs ++ "|" ++ showSeq o)).toNat % 1000000000000 }
              else some nd
            | _, _ => d
          match d, frag with
          | some d, none => out := out.push d
          | some d, some f =>
              -- a shorthand pointer (XPointer Framework §3.2): the element
              -- with that ID
              match callFn 100000 env { uri := nsFN, loc := "id" } [sStr f, [.node d]] with
              | .ok ns => for x in ns do
                  match x with
                  | .node m => out := out.push m
                  | _ => pure ()
              | .error e => throw e
          | none, _ => pure ()
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
      let gctx := if g.noCtx then none else o.globalCtx
      let one := if gctx.isSome then 1 else 0
      let gbase := if g.base != "" then g.base else env.baseUri
      let genv : Env := { env with host, ctx := gctx.map (fun i => [i]), pos := one, size := one, baseUri := gbase }
      let supplied := if g.isParam then lookupV o.params g.name else none
      let act : XM Seq := match supplied with
        | some v => match g.ty with
          | some t => liftX (typeErrAs "XTTE0590" (genv.coerce t v ("$" ++ g.name.show)))
          | none => pure v
        | none =>
          if g.required then xerr "XTDE0050" ("no value given for the required parameter $" ++ g.name.show)
          else bindValue 100000 S { env := genv, backCompat := ({ version := S.version } : SCx).backCompat } g.sel g.body g.ty ("$" ++ g.name.show) (if g.isParam then "XTTE0590" else "XTTE0570")
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
  let env0 := if S.defaultCollation != "" then { env0 with defaultCollation := S.defaultCollation } else env0
  if S.globalCtxUse == "required" && o.globalCtx.isNone then
    err "XTDE3086" "the stylesheet requires a global context item"
  let globalCtx := if S.globalCtxUse == "absent" then none else o.globalCtx
  let o := { o with globalCtx }
  let env ← evalGlobals S o env0
  -- key and accumulator caches over the documents of the context
  let keyCache : List ((String × Nat) × Thunk (M KeyIndex)) :=
    (List.range docs.size).flatMap (fun di => S.keys.zipIdx.map (fun (kd, j) =>
      ((kd.name.eqn ++ "#" ++ toString j, di), Thunk.mk (fun _ => buildKeyIndex S { env with host := mkHost S env [] [] 100000 } kd (NodeRef.mk' di 0)))))
  let accCache : List ((String × Nat) × Thunk (M (Std.HashMap Nat (Seq × Seq)))) :=
    (List.range docs.size).flatMap (fun di => S.accumulators.map (fun acc =>
      ((acc.name.eqn, di), Thunk.mk (fun _ => accumulatorValues S { env with host := mkHost S env [] [] 100000 } acc (NodeRef.mk' di 0)))))
  let host := mkHost S env keyCache accCache 100000
  let hostParams (q : QN) (k : Nat) : Option (List String) :=
    let q := if q.uri == nsFN && q.pfx == "" && S.functions.any (fun g => g.name.uri == "" && g.name.loc == q.loc && g.accepts k)
      then { q with uri := "" } else q
    (S.functions.find? (fun f => f.name == q && f.accepts k)).map (·.params.map (·.name.loc))
  let env := { env with host, hostParams, vars := env.vars ++ [(vOutUri, if o.outUri == "" then [] else [.atom (Atomic.ofUri o.outUri)])] }
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
        if S.privTemplates.contains tn then
          xerr "XTDE0040" ("the template " ++ tn.show ++ " is not public, so it cannot be the initial template")
        for p in t.params do
          if p.required && !p.tunnel && !o.templateParams.any (·.1 == p.name) then
            xerr "XTDE0700" ("no value for the required parameter $" ++ p.name.show ++ " of the initial template")
        let cx' := if t.ctxAbsent then cx.noFocus else cx
        invoke 1000000 S cx' t o.templateParams o.tunnelParams
    | none =>
      let mode := o.initialMode.getD S.defaultMode
      let mode := if mode == "#default" then S.defaultMode else mode
      if S.isPackage && o.initialMode.isSome && o.initialSelect.isNone && o.globalCtx.isNone then
        xerr "XTDE0044" "an initial mode is given and there is no initial match selection"
      if let some ok := S.initModes then
        if o.initialMode.isSome && !ok.contains mode then
          xerr "XTDE0045" ("the mode " ++ mode ++ " is not eligible as an initial mode")
      if mode != "#unnamed" && mode != S.defaultMode && !(S.modes.any (·.name == mode)) &&
          !(S.templates.any (fun t => t.modes.contains mode || t.modes.contains "#all")) then
        xerr "XTDE0045" ("the initial mode " ++ mode ++ " is not declared")
      let sel := match o.initialSelect with
        | some s => s
        | none => match o.globalCtx with | some i => [i] | none => []
      applyT 1000000 S { cx with mode } sel mode o.templateParams o.tunnelParams none
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
  pure { raw, principalFormat := pf, secondary := secs.map (fun (h, v, f, sp) => (abs h, v, f, sp)), msgs := st.msgs.toList, msgDocs := st.msgDocs.toList }

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
