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
import L4Factoidal.XSLT4.Streaming.Check

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

/-! ## `fn:transform` for the qt4tests host (from PR 205)

The entry used by `l4qt4` (`transformHost`): the option names and types
of F&O 4.0 §18.3 are checked first, the requested properties are compared
with `systemProperty`, and a request for `xsl:supports-streaming` runs the
XSLT Streaming 4.0 analysis. `fnTransformHost` above is the entry of the
XSLT 4.0 runner (packages, nested transformations). The two are to become
one function: https://github.com/danbri/factoidal/issues/1101. -/

def transformOptionNames : List String :=
  ["base-output-uri", "cache", "delivery-format", "enable-assertions", "enable-messages",
   "enable-trace", "function-params", "global-context-item", "initial-function",
   "initial-match-selection", "initial-mode", "initial-template", "package-name",
   "package-location", "package-node", "package-text", "package-version", "post-process",
   "requested-properties", "serialization-params", "source-location", "source-node",
   "static-params", "stylesheet-base-uri", "stylesheet-location", "stylesheet-node",
   "stylesheet-params", "stylesheet-text", "template-params", "tunnel-params", "trusted",
   "vendor-options", "xslt-version"]

/-- The declared types of the options (F&O 4.0 §17.5.2, the option table). -/
def transformOptionTypes : List (String × String) :=
  [("base-output-uri", "xs:string"), ("cache", "xs:boolean"), ("delivery-format", "xs:string"),
   ("enable-assertions", "xs:boolean"), ("enable-messages", "xs:boolean"),
   ("enable-trace", "xs:boolean"), ("function-params", "array(item()*)"),
   ("global-context-item", "item()"), ("initial-function", "xs:QName"),
   ("initial-match-selection", "item()*"), ("initial-mode", "xs:QName"),
   ("initial-template", "xs:QName"), ("post-process", "fn(xs:string, item()*) as item()*"),
   ("requested-properties", "map(xs:QName, xs:anyAtomicType)"),
   ("serialization-params", "map(xs:anyAtomicType, item()*)"),
   ("source-location", "xs:string"), ("static-params", "map(xs:QName, item()*)"),
   ("stylesheet-base-uri", "xs:string"), ("stylesheet-location", "xs:string"),
   ("stylesheet-params", "map(xs:QName, item()*)"), ("stylesheet-text", "xs:string"),
   ("trusted", "xs:boolean"), ("xslt-version", "xs:decimal"),
   ("template-params", "map(xs:QName, item()*)"), ("tunnel-params", "map(xs:QName, item()*)")]

/-- A map of QName keys as a list of bindings. -/
def qnameBindings (s : Option Seq) : List (QN × Seq) :=
  match s with
  | some [.map kvs] => kvs.filterMap (fun (k, v) => match k.v with | .qn q => some (q, v) | _ => none)
  | _ => []

/-- A serialization parameter value as the string of an output definition. -/
def propString (e : Env) (v : Seq) : String :=
  match v with
  | [.atom ⟨_, .bool b⟩] => if b then "yes" else "no"
  | [.atom ⟨_, .qn q⟩] => q.eqn
  | _ => String.intercalate " " ((e.atomize v).toOption.getD [] |>.map Atomic.str)

/-- `fn:transform($options)`. `apply` calls a function item (for
    `post-process`). -/
def fnTransformQ (env : Env) (applyF : Item → List Seq → M Seq) (args : List Seq) : M Seq := do
  let opts0 := args.headD []
  checkOptionKeys opts0 transformOptionNames
  let opts ← match opts0 with
    | [.map kvs] => do
      let mut out : List (Atomic × Seq) := []
      for (k, v) in kvs do
        match transformOptionTypes.lookup k.str with
        | some t => out := out ++ [(k, ← env.coerce (parseTy t) v ("option " ++ k.str))]
        | none => out := out ++ [(k, v)]
      pure [Item.map out]
    | _ => err "XPTY0004" "fn:transform: the options must be a map"
  let get (k : String) : Option Seq := optLookup opts k
  let str? (k : String) : Option String := match get k with
    | some [.atom a] => some a.str
    | _ => none
  -- unsupported requests (FOXT0001)
  for k in ["package-name", "package-location", "package-node", "package-text", "package-version"] do
    if (get k).isSome then err "FOXT0001" ("fn:transform: the option " ++ k ++ " is not supported")
  match get "xslt-version" with
  | some [.atom v] =>
    match v.num? with
    | some x => if x.toFloat > 4.0 then err "FOXT0001" ("no XSLT " ++ v.str ++ " processor is available")
    | none => pure ()
  | _ => pure ()
  -- requested properties (F&O 4.0 §17.5.2): a request that the processor's
  -- system-property value does not meet is FOXT0001; xsl:version is ignored
  for (q, v) in qnameBindings (get "requested-properties") do
    if q.uri != nsXSL || q.loc == "version" then continue
    let want := propString env v
    let actual := systemProperty q.loc
    let norm (s : String) : String := match s.trimAscii.toString.toLower with
      | "true" | "yes" | "1" => "yes"
      | "false" | "no" | "0" => "no"
      | x => x
    if actual != "" && norm want != norm actual then
      err "FOXT0001" ("no XSLT processor with " ++ q.loc ++ " = " ++ want ++ " is available")
  let delivery := (str? "delivery-format").getD "document"
  if !["document", "serialized", "raw"].contains delivery then
    if delivery == "file" then err "FOXT0001" "the delivery format file is not supported"
    else err "FOXT0002" ("unknown delivery format " ++ delivery)
  -- the stylesheet: exactly one of location, node, text
  let given := ["stylesheet-location", "stylesheet-node", "stylesheet-text"].filter (fun k => (get k).isSome)
  if given.length != 1 then
    err "FOXT0002" "fn:transform needs exactly one of stylesheet-location, stylesheet-node, stylesheet-text"
  let base := match str? "stylesheet-base-uri" with
    | some b => resolveUri env.baseUri b
    | none => env.baseUri
  let (pUri, pText) ← match str? "stylesheet-location", get "stylesheet-node", str? "stylesheet-text" with
    | some loc, _, _ =>
      let abs := resolveUri env.baseUri loc
      match env.resource loc with
      | some t => pure (abs, t)
      | none =>
        match env.docUris.lookup loc |>.orElse (fun _ => env.docUris.lookup abs) with
        | some di => pure (abs, ← env.serializeWith { method := "xml" } [.node (NodeRef.mk' di 0)])
        | none => err "FODC0002" ("stylesheet not available: " ++ loc)
    | none, some [.node n], _ =>
      let d := env.doc n
      let u := if d.baseUri != "" then d.baseUri else if d.uri != "" then d.uri else base
      pure (u, ← env.serializeWith { method := "xml" } [.node n])
    | none, some _, _ => err "XPTY0004" "stylesheet-node must be a node"
    | none, none, some t => pure (base, t)
    | none, none, none => err "FOXT0002" "no stylesheet"
  -- the modules: the principal one and the caller's resources
  let texts : List (String × String) := (pUri, pText) ::
    env.resources.flatMap (fun (k, v) => if k.startsWith "#" then [] else [(resolveUri pUri k, v), (k, v)])
  let S ← compileStylesheet pUri texts (qnameBindings (get "static-params"))
  -- a request for a streaming processor (xsl:supports-streaming): the
  -- streamability analysis of XSLT Streaming 4.0 §3.1 runs, and a
  -- construct declared streamable that is not guaranteed streamable is
  -- XTSE3430 (`XSLT4.Streaming.analyzeModules`, as in l4xslt4)
  let wantsStreaming := (qnameBindings (get "requested-properties")).any (fun (q, v) =>
    q.uri == nsXSL && q.loc == "supports-streaming" &&
      ["true", "yes", "1"].contains (propString env v).trimAscii.toString.toLower)
  if wantsStreaming then
    if let some e := L4Factoidal.XSLT4.Streaming.analyzeModules texts (qnameBindings (get "static-params")) then
      throw e
  -- the invocation
  let srcNode : Option Item ← match get "source-node", str? "source-location" with
    | some [i@(.node _)], _ => pure (some i)
    | some _, _ => err "XPTY0004" "source-node must be a node"
    | none, some loc =>
      match env.docUris.lookup loc |>.orElse (fun _ => env.docUris.lookup (resolveUri env.baseUri loc)) with
      | some di => pure (some (.node (NodeRef.mk' di 0)))
      | none => match env.resource loc with
        | some t => match Doc.ofString t (resolveUri env.baseUri loc) with
          | .ok d => pure (some (Doc.rootItem d (runtimeDocId "transform-source" t)))
          | .error m => err "FODC0002" ("source not well-formed: " ++ m)
        | none => err "FODC0002" ("source not available: " ++ loc)
    | none, none => pure none
  let rootOf (i : Item) : Item := match i with
    | .node n => .node { n with idx := 0 }
    | x => x
  let globalCtx : Option Item := match get "global-context-item" with
    | some [i] => some i
    | _ => srcNode.map rootOf
  let qn? (k : String) : Option QN := match get k with
    | some [.atom ⟨_, .qn q⟩] => some q
    | _ => none
  let initialFunction : Option (QN × List Seq) := (qn? "initial-function").map (fun q =>
    (q, match get "function-params" with
      | some [.arr ms] => ms
      | _ => []))
  let initialTemplate := qn? "initial-template"
  let initialSelect : Option Seq := match get "initial-match-selection" with
    | some s => some s
    | none => if initialTemplate.isNone then srcNode.map (fun i => [i]) else none
  -- xsl:unnamed and xsl:default name the unnamed and the default mode
  let initialMode := (qn? "initial-mode").map (fun q =>
    if q.uri == nsXSL && q.loc == "unnamed" then "#unnamed"
    else if q.uri == nsXSL && q.loc == "default" then "#default" else q.eqn)
  -- the invocation options that exclude each other (FOXT0002)
  if initialFunction.isSome && (initialTemplate.isSome || (get "initial-mode").isSome) then
    err "FOXT0002" "initial-function excludes initial-template and initial-mode"
  if initialTemplate.isSome && ((get "initial-mode").isSome || (get "initial-match-selection").isSome) then
    err "FOXT0002" "initial-template excludes initial-mode and initial-match-selection"
  if initialFunction.isSome && (get "function-params").isNone then
    err "FOXT0002" "initial-function needs function-params"
  if ([(get "source-node").isSome, (get "source-location").isSome, (get "initial-match-selection").isSome].filter id).length > 1 then
    err "FOXT0002" "at most one of source-node, source-location and initial-match-selection"
  let outUri := match str? "base-output-uri" with
    | some u => resolveUri env.baseUri u
    | none => ""
  let topts : TOpts := { initialTemplate, initialMode, initialSelect, initialFunction, globalCtx,
                         params := qnameBindings (get "stylesheet-params"), env, outUri,
                         templateParams := qnameBindings (get "template-params"),
                         tunnelParams := qnameBindings (get "tunnel-params") }
  let r ← transform S topts
  -- the results
  let serProps : List (String × String) := match get "serialization-params" with
    | some [.map kvs] => kvs.filterMap (fun (k, v) => if v.isEmpty then none else some (k.str, propString env v))
    | _ => []
  let deliver (fmt : String) (sp : List (String × String)) (extra : List (String × String)) (v : Seq) : M Seq := do
    match delivery with
    | "raw" => pure v
    | "serialized" =>
      let props ← S.outputProps fmt (sp ++ extra)
      pure (sStr (← serializeResult S env props v))
    | _ =>
      let isDoc : Bool := match v with
        | [.node n] => (env.nrec n).kind == .document
        | _ => false
      if isDoc then pure v
      else pure [← materialize env (2 ^ 45) (.doc (Out.ofSeq v) outUri)]
  let post (key : String) (v : Seq) : M Seq := do
    match get "post-process" with
    | some [f] => applyF f [sStr key, v]
    | _ => pure v
  let pKey := match str? "base-output-uri" with
    | some u => u
    | none => "output"
  let mut kvs : List (Atomic × Seq) := []
  let pv ← deliver r.principalFormat.1 r.principalFormat.2 serProps r.raw
  kvs := kvs ++ [(Atomic.ofStr pKey, ← post pKey pv)]
  for (h, v, f, sp) in r.secondary do
    let sv ← deliver f sp [] v
    kvs := kvs ++ [(Atomic.ofStr h, ← post h sv)]
  pure [.map kvs]

/-- An `Env.host` hook that adds `fn:transform#1` over `base`; `env`
    gives the documents and resources, `applyF` calls function items. -/
def transformHost (env : Env) (applyF : Item → List Seq → M Seq)
    (base : QN → Nat → Option HostFn) : QN → Nat → Option HostFn :=
  fun q k =>
    if q.uri == nsFN && q.loc == "transform" && k == 1 then
      some (fun _ args => fnTransformQ env applyF args)
    else base q k

end L4Factoidal.XSLT4
