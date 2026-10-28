/-
L4Factoidal.XSLT4.FnTransform — `fn:transform` (F&O 4.0 §17.5.2) for an
XPath or XQuery host, with the XSLT 4.0 processor of this tree
(`XSLT4.compileStylesheet`, `XSLT4.transform`).

The stylesheet is exactly one of `stylesheet-location` (read from the
caller's resources and documents), `stylesheet-node` (serialized and read
again) and `stylesheet-text`; the modules it includes or imports come from
the caller's resources. The invocation is the first of: `initial-function`
with `function-params`; `initial-template`; apply-templates to
`source-node`, `source-location` or `initial-match-selection`; the template
`xsl:initial-template`. `source-node` also gives the global context item
(the root of its tree), unless `global-context-item` is given.

The result map has one entry for the principal result (key: the
`base-output-uri`, or `"output"`) and one for each secondary result (key:
its absolute URI). The value is a document node (`delivery-format`
`document`, the default), a string (`serialized`, with the stylesheet's
output definition and `serialization-params`), or the raw value (`raw`);
`post-process` is applied to each. XSLT errors keep their codes.

Not supported, FOXT0001 (F&O 4.0: "the XSLT processor API does not
support some requested feature"): packages (`package-*`), delivery format
`file`, an `xslt-version` above 4.0, and
the request `xsl:is-schema-aware` true. `trusted`, `cache`,
`enable-assertions`, `enable-messages`, `enable-trace` and `vendor-options`
are accepted with no effect.
-/
import L4Factoidal.XSLT4.Transform
import L4Factoidal.XSLT4.Streaming.Check

namespace L4Factoidal.XSLT4

open L4Factoidal.XPath4

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
def fnTransform (env : Env) (applyF : Item → List Seq → M Seq) (args : List Seq) : M Seq := do
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
      some (fun _ args => fnTransform env applyF args)
    else base q k

end L4Factoidal.XSLT4
