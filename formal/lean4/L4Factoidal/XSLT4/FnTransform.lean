/-
L4Factoidal.XSLT4.FnTransform — `fn:transform` (F&O 4.0 §18.3): a
transformation with a stylesheet that the call names, compiled and run by
this processor.

The stylesheet comes from `stylesheet-location` (and the modules it
includes or imports), `stylesheet-text` or `stylesheet-node`. The texts
are the resources of the dynamic context (`Env.resources`): the function
does no I/O. The invocation follows the rules of §18.3: call-function
with `initial-function`, call-template with `initial-template`,
apply-templates with `source-node` or `initial-match-selection`, else the
template `xsl:initial-template`. The result is a map: the principal
result under `output` (or the base output URI) and each secondary result
under its absolute URI, delivered as a document node, raw, or serialized.

A nested `fn:transform` is available with one less unit of fuel.
-/
import L4Factoidal.XSLT4.Transform

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

/-- The text of a resource of the dynamic context: by its URI, or by the
    relative reference it was read under. -/
def resourceText (res : List (String × String)) (u : String) : Option String :=
  match res.lookup u with
  | some t => some t
  | none => (res.find? (fun (k, _) => u.endsWith ("/" ++ k) || k.endsWith ("/" ++ u))).map (·.2)

/-- A stylesheet module and the modules it includes or imports, from the
    resources (breadth first; `fuel` bounds the number of modules). -/
def moduleClosure (res : List (String × String)) : Nat → List String → List (String × String) → List (String × String)
  | 0, _, acc => acc
  | _ + 1, [], acc => acc
  | f + 1, u :: rest, acc =>
    if acc.any (·.1 == u) then moduleClosure res f rest acc else
    match resourceText res u with
    | some t => moduleClosure res f (rest ++ moduleRefs u t ++ packageRefs u t) (acc ++ [(u, t)])
    | none => moduleClosure res f rest acc

/-- The QName-keyed entries of an option map. -/
def qnEntries (v : Option Seq) (what : String) : M (List (QN × Seq)) :=
  match v with
  | none | some [] => pure []
  | some [.map kvs] => kvs.mapM (fun (k, x) => match k.v with
      | .qn q => pure (q, x)
      | _ => err "XPTY0004" ("the keys of " ++ what ++ " must be QNames"))
  | some _ => err "XPTY0004" (what ++ " must be a map")

mutual

/-- `fn:transform` with `fuel` levels of nesting, and the packages the
    run knows (for `package-name` and for `xsl:use-package`). -/
def fnTransformHost : Nat → List PkgEntry → Env → QN → Nat → Option HostFn
  | 0, _, _, _, _ => none
  | f + 1, lib, env, q, k =>
    if q.uri == nsFN && q.loc == "transform" && k == 1 then
      some (fun c a => fnTransform f lib env c a)
    else none

def fnTransform : Nat → List PkgEntry → Env → HostCall → List Seq → M Seq
  | 0, _, _, _, _ => err "FOXT0001" "fn:transform is nested too deeply"
  | f + 1, lib, env, c, a => do
    let opts ← match a.getD 0 [] with
      | [.map kvs] => pure kvs
      | _ => err "XPTY0004" "the argument of fn:transform must be a map"
    let opt (key : String) : Option Seq := (opts.find? (fun (k0, _) => k0.str == key)).map (·.2)
    let str (key : String) : M (Option String) := do
      match opt key with
      | none | some [] => pure none
      | some v => match ← env.atomize v with
        | [x] => pure (some x.str)
        | _ => err "XPTY0004" ("the option " ++ key ++ " must be a single string")
    let base := env.baseUri
    -- the stylesheet: exactly one of its three forms (FOXT0002)
    let given := ["stylesheet-location", "stylesheet-text", "stylesheet-node",
      "package-location", "package-text", "package-node", "package-name"].filter (fun k => (opt k).isSome)
    if given.length != 1 then
      err "FOXT0002" "fn:transform needs exactly one of stylesheet-location, stylesheet-text and stylesheet-node"
    let sbase ← str "stylesheet-base-uri"
    let (principal, texts) ← match given with
      | ["stylesheet-location"] | ["package-location"] => do
        let some loc ← str given.head! | err "FOXT0002" "empty stylesheet location"
        let u := resolveUri base loc
        let texts := moduleClosure env.resources 1000 [u] []
        if texts.isEmpty then err "FOXT0002" ("the stylesheet " ++ loc ++ " is not available")
        pure (u, texts)
      | ["package-name"] => do
        -- the package of that name in the run's library; with
        -- package-version, the highest version in the range (§3.4.1)
        let some nm ← str "package-name" | err "FOXT0002" "empty package name"
        let rng ← match ← str "package-version" with
          | some v => match parseRange v with
            | some r => pure r
            | none => err "FOXT0002" ("invalid package-version " ++ v)
          | none => pure [VRange.any]
        let lib' := lib.map (pkgHeader env.resources)
        let cands := lib'.filter (fun e => e.name == nm &&
          (match parseVersion e.version with
            | some v => rng.any (·.matches v)
            | none => false))
        let best := cands.foldl (fun (b : Option PkgEntry) e => match b, parseVersion e.version with
          | some x, some v => (match parseVersion x.version with
              | some xv => if cmpVersion v xv == .gt then some e else some x
              | none => some e)
          | none, _ => some e
          | b, none => b) none
        let some e := best | err "XTSE3000" ("no package " ++ nm ++ " in the requested version")
        let texts := moduleClosure env.resources 1000 [e.uri] []
        if texts.isEmpty then err "FOXT0002" ("the package " ++ nm ++ " is not available")
        pure (e.uri, texts)
      | ["stylesheet-text"] | ["package-text"] => do
        let some t ← str given.head! | err "FOXT0002" "empty stylesheet text"
        let u := match sbase with | some b => resolveUri base b | none => base
        let u := if u == "" then "file:///stylesheet.xsl" else u
        pure (u, moduleClosure env.resources 1000 (moduleRefs u t) [(u, t)])
      | _ => do
        let node ← match opt given.head! with
          | some [.node n] => pure n
          | _ => err "XPTY0004" "stylesheet-node must be a node"
        let t ← match ← callFn 100000 env { uri := nsFN, loc := "serialize" } [[.node node]] with
          | [.atom x] => pure x.str
          | _ => err "FOXT0002" "the stylesheet node cannot be serialized"
        let d := env.doc node
        let u := match sbase with
          | some b => resolveUri base b
          | none => if d.baseUri != "" then d.baseUri else if d.uri != "" then d.uri else base
        pure (u, moduleClosure env.resources 1000 (moduleRefs u t) [(u, t)])
    let statics ← qnEntries (opt "static-params") "static-params"
    -- the library packages' modules join the texts (xsl:use-package)
    let libTexts := moduleClosure env.resources 1000 (lib.map (·.uri)) []
    let texts := texts ++ libTexts.filter (fun (u, _) => !texts.any (·.1 == u))
    let S ← compileStylesheet principal texts statics lib
    let S := { S with extraHost := fnTransformHost f lib }
    let params ← qnEntries (opt "stylesheet-params") "stylesheet-params"
    let tparams ← qnEntries (opt "template-params") "template-params"
    let tunnel ← qnEntries (opt "tunnel-params") "tunnel-params"
    -- the invocation (§18.3)
    let qnOpt (key : String) : M (Option QN) := match opt key with
      | none | some [] => pure none
      | some [.atom x] => match x.v with
        | .qn q => pure (some q)
        | _ => err "XPTY0004" ("the option " ++ key ++ " must be a QName")
      | some _ => err "XPTY0004" ("the option " ++ key ++ " must be a QName")
    let ifn ← qnOpt "initial-function"
    let itmpl ← qnOpt "initial-template"
    let imode ← qnOpt "initial-mode"
    let src := match opt "source-node" with
      | some [i] => some i
      | _ => none
    let sel : Option Seq := match opt "initial-match-selection" with
      | some v => some v
      | none => src.map (fun i => [i])
    let gctx : Option Item := match opt "global-context-item" with
      | some [i] => some i
      | _ => match src with
        | some (.node n) => some (.node (env.treeRoot n))
        | other => other
    let fargs : List Seq ← match opt "function-params" with
      | none | some [] => pure []
      | some [.arr ms] => pure ms
      | some _ => err "XPTY0004" "function-params must be an array"
    let outUri := (← str "base-output-uri").map (resolveUri base) |>.getD ""
    let topts : TOpts := {
      initialFunction := ifn.map (fun q => (q, fargs)),
      initialTemplate := if ifn.isSome then none else itmpl,
      initialMode := imode.map (·.eqn),
      initialSelect := if ifn.isSome || itmpl.isSome then none else sel,
      globalCtx := gctx, params, env := { env with vars := [] }, outUri,
      templateParams := tparams, tunnelParams := tunnel }
    let r ← transform S topts
    -- delivery (document, raw or serialized)
    let fmt := (← str "delivery-format").getD "document"
    if !["document", "raw", "serialized", "file"].contains fmt then
      err "FOXT0002" ("invalid delivery-format " ++ fmt)
    let sparams := match opt "serialization-params" with
      | some [.map kvs] => kvs.filterMap (fun (k0, v) => match v with
          | [.atom x] => some (k0.str, x.str)
          | _ => none)
      | _ => []
    let wrap (v : Seq) : M Seq := do
      let isDoc : Bool := match v with
        | [.node n] => (env.nrec n).kind == .document
        | _ => false
      if isDoc then pure v else pure [← materialize env (2 ^ 42 + 7) (.doc (Out.ofSeq v) "")]
    let deliver (v : Seq) (f : String) (sp : List (String × String)) : M Seq := do
      if fmt == "raw" then return v
      if fmt == "serialized" || fmt == "file" then
        let props ← S.outputProps f (sp ++ sparams)
        return sStr (← serializeResult S env props v)
      wrap v
    let key := if outUri == "" then "output" else outUri
    let principalV ← deliver r.raw r.principalFormat.1 r.principalFormat.2
    let mut entries : List (Atomic × Seq) := [(Atomic.ofStr key, principalV)]
    for (h, v, fm, sp) in r.secondary do
      entries := entries ++ [(Atomic.ofStr h, ← deliver v fm sp)]
    pure [.map entries]

end

end L4Factoidal.XSLT4
