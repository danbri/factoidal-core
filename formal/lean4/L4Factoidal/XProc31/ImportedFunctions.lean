import L4Factoidal.XProc31.Loading
import L4Factoidal.XSLT4.Package
import L4Factoidal.XSLT4.Transform
import L4Factoidal.XQuery4.LoadModule
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.XProc31.ImportedFunctions
open XPath4

/-- Each exported function retains its library's lexical environment. -/
structure Export where
  source : String
  name : QN
  arity : Nat
  call : HostFn

/-- Capture caller-owned node trees before entering a library environment. -/
def freeze (caller : Env) : Nat → Seq → Seq
  | 0, xs => xs
  | fuel+1, xs => xs.map fun item => match item with
    | .node n => .node (if n.rt.isSome then n else {n with rt := some (caller.doc n)})
    | .map kvs => .map (kvs.map fun (k,v) => (k, freeze caller fuel v))
    | .arr xs => .arr (xs.map (freeze caller fuel))
    | other => other

def host (exports : List Export) (caller : Env) (name : QN) (arity : Nat) : Option HostFn :=
  (exports.find? (fun e => e.name == name && e.arity == arity)).map fun e =>
    fun c args => e.call c (args.map (freeze caller 256))

/-- Same source imports are idempotent; distinct sources cannot contribute the
same signature in a single lexical scope. Outer scopes are merged separately. -/
def merge (left right : List Export) : Result (List Export) := do
  let mut out := left
  for entry in right do
    match out.find? (fun old => old.name == entry.name && old.arity == entry.arity) with
    | none => out := out ++ [entry]
    | some old =>
      if old.source != entry.source then
        return ← error "XS0105" ("duplicate imported function " ++ entry.name.eqn ++ "#" ++ toString entry.arity)
  return out

def importable (contentType : String) : Bool :=
  ["application/xslt+xml", "application/xquery"].contains contentType

private def compileError (e : XPath4.Err) : ProcError :=
  ⟨"XS0106", e.code ++ ": " ++ e.msg, false, [], none⟩

private def readSource (uri : String) : IO (Result String) := do
  let path ← match documentFilePath uri with
    | .ok p => pure p
    | .error e => return .error e
  try return .ok (← IO.FS.readFile path)
  catch e => return error "XS0106" ("cannot load function library " ++ uri ++ ": " ++ e.toString)

/-- Preload local dependencies. The host evaluators themselves remain pure. -/
private def collect (kind : String) : Nat → List String → List (String × String) →
    IO (Result (List (String × String)))
  | 0, _, _ => pure (error "XS0106" "function library dependency depth exceeded")
  | _, [], texts => pure (.ok texts)
  | fuel+1, uri::rest, texts => do
    if texts.any (fun p => p.1 == uri) then return ← collect kind fuel rest texts
    let source ← match ← readSource uri with
      | .ok s => pure s
      | .error e => return .error e
    let refs ← if kind == "application/xslt+xml" then pure (XSLT4.packageRefs uri source)
      else match XQuery4.parseModule source with
        | .error e => return .error (compileError e)
        | .ok m => pure (m.imports.flatMap fun (_,_,locations) =>
            locations.map (Syntax.resolveIri uri))
    collect kind fuel (rest ++ refs) (texts ++ [(uri,source)])

private def xqueryExports (uri source : String) (texts : List (String × String)) : XPath4.M (List Export) := do
  let mut resources := texts
  for (_, text) in texts do
    let m ← XQuery4.parseModule text
    if let some (_, namespaceUri) := m.libNs then
      resources := resources ++ [("#module " ++ namespaceUri, text)]
  let m ← XQuery4.parseModule source
  let m := {m with baseUri := m.baseUri.orElse (fun _ => some uri)}
  let env := XQuery4.moduleEnv {resources, baseUri := uri} m
  let (libs, _) ← XQuery4.loadImports env 128 ((m.libNs.map (·.2)).toList) m
  XQuery4.checkModules env (libs ++ [m])
  let bound ← XQuery4.bindModules 100000 env (libs ++ [m])
  let bound := XQuery4.markStatic bound
  let mut out : List Export := []
  for decl in m.decls do
    if let .fn f := decl then
      if m.privates.contains f.name || f.body.isNone then continue
      if f.updating then err "XUST0001" "updating functions cannot be imported into XPath"
      let lo := (f.params.takeWhile (fun (_,_,defaultValue) => defaultValue.isNone)).length
      for arity in [lo:f.params.length+1] do
        if let some action := XQuery4.refUser? (fun fn args => XPath4.apply 100000 bound fn args) bound f.name arity then
          let values ← action
          let [fn] := values | err "XPTY0004" "function reference did not return one item"
          out := out ++ [{source := uri, name := f.name, arity, call := fun _ args => XPath4.apply 100000 bound fn args}]
  return out

private def xsltExports (uri : String) (texts : List (String × String)) : XPath4.M (List Export) := do
  let sheet ← XSLT4.compileStylesheet uri texts
  if sheet.globalCtxUse == "required" then err "XTDE3086" "function library requires a global context item"
  let env : Env := {resources := texts, baseUri := sheet.baseUri, ns := sheet.ns.filter (·.1 != ""), schema := sheet.schema, decimalFormats := sheet.decimalFormats, vars := [(XSLT4.xslGlobals, [])] ++ sheet.statics.reverse}
  let env := if sheet.defaultCollation != "" then {env with defaultCollation := sheet.defaultCollation} else env
  let bound ← XSLT4.evalGlobals sheet {} env
  let table := XSLT4.mkHost sheet bound [] [] 100000
  let mut out : List Export := []
  for f in sheet.functions do
    if !(["public", "final"].contains f.vis) then continue
    for arity in [f.minArity:f.params.length+1] do
      if out.any (fun e => e.name == f.name && e.arity == arity) then continue
      if let some call := table f.name arity then
        out := out ++ [{source := uri, name := f.name, arity, call}]
  return out

/-- Load and compile a local library, without running an XQuery main body or
an XSLT initial template. `namespaces = []` imports all public namespaces. -/
def load (uri contentType : String) (namespaces : List String := []) : IO (Result (List Export)) := do
  if !importable contentType then return error "XS0106" ("unsupported function library media type " ++ contentType)
  let texts ← match ← collect contentType 512 [uri] [] with
    | .ok texts => pure texts
    | .error e => return .error e
  let source := (texts.lookup uri).getD ""
  let compiled := if contentType == "application/xquery" then xqueryExports uri source texts else xsltExports uri texts
  return (compiled.mapError compileError).map fun exports =>
    exports.filter (fun e => namespaces.isEmpty || namespaces.contains e.name.uri)

#guard importable "application/xquery"
#guard !importable "not a media type"

/-- Real fixture libraries exercise both language adapters and declaration-only
loading of XQuery main modules. No fixture result is used by the evaluator. -/
def fixtureRegression (documents : System.FilePath) : IO (Result Unit) := do
  let namespaceUri := "http://xproc.org/ns/testsuite/3.0/function-test"
  for (file, media) in [("xslt-functions.xsl", "application/xslt+xml"),
      ("xquery-functions.xq", "application/xquery"), ("xquery-library.xq", "application/xquery")] do
    let uri := "file://" ++ (documents / file).toString
    let exports ← match ← load uri media with
      | .error e => return .error e
      | .ok es => pure es
    let q : QN := {uri := namespaceUri, loc := "function2"}
    let some invoke := host exports {} q 1 | return error "regression" (file ++ ": missing function2#1")
    let values ← match invoke {} [[.atom (Atomic.ofStr "argument")]] with
      | .error e => return .error (compileError e)
      | .ok values => pure values
    if seqString {} values != "argument" then return error "regression" (file ++ ": wrong argument/result")
    if (host exports {} q 0).isSome then return error "regression" (file ++ ": wrong arity exported")
    if (host exports {} {uri := namespaceUri, loc := "private-function"} 0).isSome then
      return error "regression" (file ++ ": private function exported")
    match merge exports exports with
    | .error e => return .error e
    | .ok both => if both.length != exports.length then return error "regression" "duplicate source was not deduplicated"
    let other := exports.map (fun e => {e with source := e.source ++ "/different"})
    match merge exports other with
    | .error e => if e.code != "XS0105" then return error "regression" "wrong duplicate signature error"
    | .ok _ => return error "regression" "distinct-source signature collision accepted"
  return .ok ()

end L4Factoidal.XProc31.ImportedFunctions
