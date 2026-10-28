/-
L4Factoidal.XQuery4.LoadModule — `fn:load-xquery-module` (F&O 4.0
§17.4.1) for an XPath or XQuery host: the public functions and global
variables of an XQuery 4.0 library module, loaded with the module loader
of `XQuery4.Module` (`parseModule`, `loadImports`, `checkModules`,
`bindModules`).

The module text is the `content` option, or the texts the caller gave
under `#module <uri>` in `Env.resources` (the same resources that
`import module` reads). The result is a `load-xquery-module-record`:
`variables` maps each public global variable of the loaded module (not of
the modules it imports) to its value; `functions` maps each public
function name to a map from each permitted arity to a function item. A
lower arity fixes the optional parameters to their defaults, evaluated
with the module's global context value.

Errors: FOQM0001 (zero-length URI), FOQM0002 (no library module with the
namespace), FOQM0003 (a static error in the module), FOQM0005 (a supplied
context value or external variable value that does not match its
declared type, or both `context-value` and `context-item`), FOQM0006 (an
XQuery version above 4.0). Dynamic errors in the module are returned as
they are. The options `trusted`, `location-hints` and `vendor-options`
are accepted and have no effect.

`loadModuleHost` adds the function to an `Env.host` hook, so that an
XPath host that has this module offers it (the XPath library alone gives
FOQM0006, `XPath4.Collections`).
-/
import L4Factoidal.XQuery4.Module

namespace L4Factoidal.XQuery4

open L4Factoidal.XPath4

def loadOptionNames : List String :=
  ["xquery-version", "trusted", "location-hints", "content", "context-value", "context-item",
   "variables", "vendor-options"]

/-- Is the code that of a static error (FOQM0003 covers them)? -/
def isStaticCode (c : String) : Bool :=
  c.startsWith "XPST" || c.startsWith "XQST"

/-- A module whose function bodies run as untrusted code. -/
def Module.untrustedBodies (m : Module) : Module :=
  { m with decls := m.decls.map (fun d => match d with
    | .fn fd => .fn { fd with body := fd.body.map (fun b => .ext "untrusted" [b] [] [] []) }
    | other => other) }

/-- `fn:load-xquery-module($module-uri, $options)`; `depth` bounds the
    nesting of loads made by loaded modules. -/
def loadXQueryModule : Nat → Nat → Env → List Seq → M Seq
  | _, 0, _, _ => err "FOQM0006" "fn:load-xquery-module: modules loaded too deeply"
  | fuel, depth + 1, env, args => do
  let uri ← match args.headD [] with
    | [.atom a] => pure a.str
    | [] => err "XPTY0004" "fn:load-xquery-module: $module-uri must be a string"
    | _ => err "XPTY0004" "fn:load-xquery-module: $module-uri must be one string"
  if uri == "" then err "FOQM0001" "fn:load-xquery-module: the module URI is a zero-length string"
  let opts0 := args.getD 1 []
  checkOptionKeys opts0 loadOptionNames
  -- each option value is coerced to its declared type (the option
  -- parameter conventions, F&O 4.0 §1.7.4)
  let optTypes : List (String × String) :=
    [("xquery-version", "xs:decimal"), ("trusted", "xs:boolean"), ("location-hints", "xs:string*"),
     ("content", "xs:string"), ("context-value", "item()*"), ("context-item", "item()?"),
     ("variables", "map(xs:QName, item()*)"), ("vendor-options", "map(xs:QName, item()*)")]
  let opts ← match opts0 with
    | [.map kvs] => do
      let mut out : List (Atomic × Seq) := []
      for (k, v) in kvs do
        match optTypes.lookup k.str with
        | some t => out := out ++ [(k, ← env.coerce (parseTy t) v ("option " ++ k.str))]
        | none => out := out ++ [(k, v)]
      pure [Item.map out]
    | other => pure other
  -- the XQuery version: this processor is XQuery 4.0
  match optLookup opts "xquery-version" with
  | some [.atom v] =>
    match v.num? with
    | some x => if x.toFloat > 4.0 then err "FOQM0006" ("no XQuery " ++ v.str ++ " processor is available")
    | none => err "XPTY0004" "xquery-version must be a decimal"
  | some [] | none => pure ()
  | some _ => err "XPTY0004" "xquery-version must be one decimal"
  -- the context value
  let cv := optLookup opts "context-value"
  let ci := optLookup opts "context-item"
  if cv.isSome && ci.isSome then err "FOQM0005" "both context-value and context-item are given"
  let ctxv : Option Seq ← match cv, ci with
    | some s, _ => pure (some s)
    | none, some [] => pure none
    | none, some [i] => pure (some [i])
    | none, some _ => err "XPTY0004" "context-item must be at most one item"
    | none, none => pure none
  -- the values of external variables
  let mut extVars : List (QN × Seq) := []
  match optLookup opts "variables" with
  | some [.map kvs] =>
    for (k, v) in kvs do
      match k.v with
      | .qn q => extVars := extVars ++ [(q, v)]
      | _ => err "XPTY0004" "the keys of the variables option must be QNames"
  | some [] | none => pure ()
  | some _ => err "XPTY0004" "the variables option must be a map"
  -- trust (F&O 4.0 §17.4.1): untrusted code reads no external resource
  let trusted ← match optLookup opts "trusted" with
    | some [.atom ⟨_, .bool b⟩] => pure b
    | some [] | none => pure false
    | some _ => err "XPTY0004" "trusted must be a boolean"
  let untrusted := env.untrusted || !trusted
  -- the module texts
  let content : String := match optLookup opts "content" with
    | some [.atom a] => a.str
    | _ => ""
  let texts := if content != "" then [content] else moduleTexts env uri
  if texts.isEmpty then err "FOQM0002" ("no library module with the namespace " ++ uri)
  let mut mods : List Module := []
  for t in texts do
    match parseModule t [] (typeLoader env 8 [uri]) with
    | .error ex =>
      if isStaticCode ex.code then err "FOQM0003" ("a static error in the module: " ++ ex.code ++ " " ++ ex.msg)
      else throw ex
    | .ok lm =>
      if (lm.libNs.map (·.2)) != some uri then
        err "FOQM0002" ("the module text is not a library module for " ++ uri)
      mods := mods ++ [if untrusted then lm.untrustedBodies else lm]
  -- one environment: the caller's documents and resources, the supplied
  -- variables and context value, none of the caller's bindings
  -- the loaded code may itself call fn:load-xquery-module
  let host : QN → Nat → Option HostFn := fun q k =>
    if q.uri == nsFN && q.loc == "load-xquery-module" && (k == 1 || k == 2) then
      some (fun c a => loadXQueryModule fuel depth { env with untrusted := untrusted || c.untrusted } a)
    else env.host q k
  let env0 : Env := { env with vars := extVars, ctx := ctxv, pos := if ctxv.isSome then 1 else 0,
                               size := if ctxv.isSome then 1 else 0, untrusted, host }
  let mut libs : List Module := []
  let mut seen : List String := [uri]
  for lm in mods do
    let (ls, s') ← loadImports (moduleEnv env0 lm) 50 seen lm
    libs := libs ++ (if untrusted then ls.map Module.untrustedBodies else ls); seen := s'
  let all := libs ++ mods
  let envm := match mods.head? with | some lm => moduleEnv env0 lm | none => env0
  match checkModules envm all with
  | .error ex =>
    if isStaticCode ex.code then err "FOQM0003" ("a static error in the module: " ++ ex.code ++ " " ++ ex.msg)
    else throw ex
  | .ok _ => pure ()
  -- the supplied values must match the declared types (FOQM0005)
  for m in all do
    for d in m.decls do
      match d with
      | .var v ty _ true =>
        match extVars.find? (fun (q, _) => q == v) with
        | some (_, s) =>
          match envm.coerce ty s ("$" ++ v.show) with
          | .ok _ => pure ()
          | .error _ => err "FOQM0005" ("the value of $" ++ v.show ++ " does not match its declared type")
        | none => pure ()
      | .ctx ty _ _ =>
        match ctxv with
        | some s => if !(envm.seqMatches s ty) then err "FOQM0005" "the context value does not match its declared type"
        | none => pure ()
      | _ => pure ()
  let envb ← bindModules fuel envm all
  -- the public variables and functions of the loaded module itself
  let mut varKvs : List (Atomic × Seq) := []
  let mut fnKvs : List (Atomic × Seq) := []
  for lm in mods do
    for d in lm.decls do
      match d with
      | .var v .. =>
        if lm.privates.any (· == v) then continue
        let val := (envb.vars.find? (fun (q, _) => q == v)).map (·.2) |>.getD []
        varKvs := varKvs ++ [(Atomic.ofQN v, val)]
      | .fn fd =>
        if lm.privates.any (· == fd.name) || fd.body.isNone then continue
        let lo := (fd.params.takeWhile (fun (_, _, x) => x.isNone)).length
        let mut byArity : List (Atomic × Seq) := []
        for k in [lo:fd.params.length + 1] do
          match refUser? (fun f as => apply fuel (markStatic envb) f as) (markStatic envb) fd.name k with
          | some r => byArity := byArity ++ [(Atomic.ofInt k, ← r)]
          | none => pure ()
        -- one entry per name: the arities of all its declarations
        let key := Atomic.ofQN fd.name
        match fnKvs.find? (fun (k, _) => atomicEqual k key) with
        | some (_, [.map old]) =>
          fnKvs := fnKvs.map (fun (k, v) => if atomicEqual k key then (k, [.map (old ++ byArity)]) else (k, v))
        | _ => fnKvs := fnKvs ++ [(key, [.map byArity])]
      | _ => pure ()
  pure [.map [(Atomic.ofStr "variables", [.map varKvs]), (Atomic.ofStr "functions", [.map fnKvs])]]

/-- An `Env.host` hook that adds `fn:load-xquery-module#1` and `#2` over
    `base`; `env` gives the documents and module texts. -/
def loadModuleHost (env : Env) (base : QN → Nat → Option HostFn) : QN → Nat → Option HostFn :=
  fun q k =>
    if q.uri == nsFN && q.loc == "load-xquery-module" && (k == 1 || k == 2) then
      some (fun c args => loadXQueryModule 20000 20 { env with untrusted := env.untrusted || c.untrusted } args)
    else base q k

end L4Factoidal.XQuery4
