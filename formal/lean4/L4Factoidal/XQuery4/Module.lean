/-
L4Factoidal.XQuery4.Module — XQuery 4.0 modules (XQuery 4.0 §5): the
version declaration, the prolog, main and library modules, and their
evaluation over `XPath4.eval`.

Prolog declarations read: `declare namespace`, `declare default
element namespace`, `declare default function namespace` (only the
`fn` namespace), `declare boundary-space`, `declare default
collation`, `declare base-uri`, `declare construction`, `declare
ordering`, `declare default order empty`, `declare copy-namespaces`,
`declare (default) decimal-format`, `declare option`, `declare
variable` (with `external` and a default), `declare context item`/
`value`, `declare function` (with annotations, default parameter values
of 4.0, and `external` refused with XPST0017 at the call), `import
module` (from the module texts the caller gives in `Env.resources`
under `#module <uri>`). `import schema` raises `XQST0009` (no schema
support); `declare type` and `declare record` raise `XPST0003`.

A main module is evaluated as follows: the functions are bound
(`Runtime.fnKey`), then each global variable in order, each with the
marker `Runtime.staticKey` on top of the bindings, then the query body.
-/
import L4Factoidal.XQuery4.Grammar
import L4Factoidal.XQuery4.Static
import L4Factoidal.XPath4.Eval

namespace L4Factoidal.XQuery4

open L4Factoidal.XPath4

/-- A function declaration. -/
structure FnDecl where
  name : QN
  params : List (QN × IType × Option Expr)
  ret : IType
  body : Option Expr
deriving Inhabited

inductive Decl where
  | var (name : QN) (ty : IType) (init : Option Expr) (external : Bool)
  | fn (d : FnDecl)
  | ctx (ty : IType) (init : Option Expr) (external : Bool)
deriving Inhabited

structure Module where
  /-- The static namespace bindings after the prolog. -/
  ns : List (String × String) := []
  decls : List Decl := []
  /-- `import module`: prefix, target namespace, location hints. -/
  imports : List (String × String × List String) := []
  /-- The query body; `none` in a library module. -/
  body : Option Expr := none
  /-- A library module's namespace. -/
  libNs : Option (String × String) := none
  defaultCollation : Option String := none
  baseUri : Option String := none
  emptyGreatest : Bool := false
deriving Inhabited

def qerr {α} (code msg : String) : P α := throw { code, msg }

def withXq {α} (cfg : Cfg) (ns : List (String × String)) (p : P α) : P α :=
  withReader (fun c => { c with ns, ext := some (grammar cfg) }) p

def reservedFnNs : List String :=
  [nsFN, nsXS, nsMATH, nsMAP, nsARR, "http://www.w3.org/XML/1998/namespace",
   "http://www.w3.org/2001/XMLSchema-instance"]

/-- The word after `declare` that starts a prolog declaration. -/
def declWords : List String :=
  ["namespace", "default", "boundary-space", "base-uri", "construction", "ordering",
   "copy-namespaces", "decimal-format", "variable", "function", "option", "context",
   "record", "type", "revalidation", "updating", "fixed"]

/-- Is a `declare`/`import` keyword followed by a declaration word? -/
def atDecl : P (Option String) := do
  ws
  let c ← read
  let i ← get
  match ncnameAt c.s i with
  | some ("declare", e) =>
    let j := skipWsF c.s (c.s.size + 1) 0 e
    if chAt c.s j == '%' then return some "declare"
    match ncnameAt c.s j with
    | some (w, _) => pure (if declWords.contains w then some "declare" else none)
    | none => pure none
  | some ("import", e) =>
    let j := skipWsF c.s (c.s.size + 1) 0 e
    match ncnameAt c.s j with
    | some (w, _) => pure (if w == "module" || w == "schema" then some "import" else none)
    | none => pure none
  | _ => pure none

def pNCName : P String := do
  ws
  let c ← read
  match ncnameAt c.s (← get) with
  | some (n, e) => set e; pure n
  | none => synErr "expected an NCName"

def pUriLit : P String := do
  let u ← pStringLit
  expandRefs u |> fun r => match r with | .ok v => pure (normSpace v) | .error e => throw e

/-- Skip annotations `%name` or `%name(literals)`. -/
def pAnnotations : P (List String) := do
  let mut out : List String := []
  for _ in [0:1000] do
    ws
    if (← peekAt 0) != '%' then break
    adv 1
    match ← peekQName with
    | some (p, u, l, e) =>
      set e
      let q ← resolve p u l "http://www.w3.org/2012/xquery"
      if q.uri == "http://www.w3.org/2012/xquery" && !(l == "public" || l == "private") then
        qerr "XQST0045" ("reserved annotation %" ++ l)
      if [nsFN, nsXS, nsMATH, nsMAP, nsARR, "http://www.w3.org/XML/1998/namespace",
          "http://www.w3.org/2001/XMLSchema-instance"].contains q.uri then
        qerr "XQST0045" ("annotation in a reserved namespace " ++ l)
      out := out ++ [l]
      if ← eatS "(" then
        for _ in [0:1000] do
          ws
          let ch ← peekAt 0
          if ch == '"' || ch == '\'' then let _ ← pStringLit
          else
            let _ ← pExpr 100
          if !(← eatS ",") then break
        expectS ")"
    | none => synErr "bad annotation"
  pure out

/-- Parse a module (main or library). -/
def pModule : P Module := do
  let mut m : Module := {}
  let mut cfg : Cfg := {}
  let c0 ← read
  let mut ns : List (String × String) := c0.ns
  -- the version declaration
  if ← kwThenKw "xquery" "version" then
    expectKw "xquery"; expectKw "version"
    let v ← pStringLit
    if !["1.0", "3.0", "3.1", "4.0"].contains v then qerr "XQST0031" ("XQuery version " ++ v ++ " is not supported")
    if ← eatKw "encoding" then
      let enc ← pStringLit
      let ok := match enc.toList with
        | c :: rest => c.isAlpha && rest.all (fun x => x.isAlphanum || x == '.' || x == '_' || x == '-')
        | [] => false
      if !ok then qerr "XQST0087" ("invalid encoding " ++ enc)
    expectS ";"
  else if ← kwThenKw "xquery" "encoding" then
    expectKw "xquery"; expectKw "encoding"
    let enc ← pStringLit
    let ok := match enc.toList with
      | c :: rest => c.isAlpha && rest.all (fun x => x.isAlphanum || x == '.' || x == '_' || x == '-')
      | [] => false
    if !ok then qerr "XQST0087" ("invalid encoding " ++ enc)
    expectS ";"
  -- a library module
  if ← kwThenKw "module" "namespace" then
    expectKw "module"; expectKw "namespace"
    let p ← pNCName
    expectS "="
    let u ← pUriLit
    if u == "" then qerr "XQST0088" "an empty module namespace"
    if p == "xml" || p == "xmlns" then qerr "XQST0070" "module prefix xml or xmlns"
    expectS ";"
    m := { m with libNs := some (p, u) }
    ns := (p, u) :: ns
  let mut seenNs : List String := []
  let mut seen : List String := []
  let mut fnSigs : List (QN × Nat × Nat) := []
  let mut varNames : List QN := []
  let mut ctxSeen := false
  for _ in [0:100000] do
    let some kw ← atDecl | break
    if kw == "import" then
      expectKw "import"
      if ← eatKw "schema" then qerr "XQST0009" "schema import is not supported"
      expectKw "module"
      let mut pfx := ""
      if ← eatKw "namespace" then
        pfx ← pNCName
        expectS "="
      let u ← pUriLit
      if u == "" then qerr "XQST0088" "an empty module namespace"
      let mut locs : List String := []
      if ← eatKw "at" then
        for _ in [0:1000] do
          locs := locs ++ [← pUriLit]
          if !(← eatS ",") then break
      expectS ";"
      if pfx == "xml" || pfx == "xmlns" then qerr "XQST0070" "import prefix xml or xmlns"
      if m.imports.any (fun (_, u', _) => u' == u) then qerr "XQST0047" "the same module imported twice"
      if (m.libNs.map (·.2)) == some u then qerr "XQST0047" "a module imports itself"
      if pfx != "" then
        if seenNs.contains pfx then qerr "XQST0033" ("prefix " ++ pfx ++ " declared twice")
        seenNs := pfx :: seenNs
        ns := (pfx, u) :: ns.filter (·.1 != pfx)
      m := { m with imports := m.imports ++ [(pfx, u, locs)] }
      continue
    expectKw "declare"
    let annots ← withXq cfg ns pAnnotations
    let w ← pNCName
    match w with
    | "namespace" =>
      let p ← pNCName
      expectS "="
      let u ← pUriLit
      expectS ";"
      if p == "xml" || p == "xmlns" then qerr "XQST0070" ("prefix " ++ p ++ " cannot be declared")
      if u == nsXML || u == "http://www.w3.org/2000/xmlns/" then qerr "XQST0070" "a reserved namespace"
      if seenNs.contains p then qerr "XQST0033" ("prefix " ++ p ++ " declared twice")
      seenNs := p :: seenNs
      ns := if u == "" then ns.filter (·.1 != p) else (p, u) :: ns.filter (·.1 != p)
    | "default" =>
      if ← eatKw "element" then
        expectKw "namespace"
        let u ← pUriLit
        expectS ";"
        if seen.contains "defelem" then qerr "XQST0066" "two default element namespace declarations"
        seen := "defelem" :: seen
        if u == nsXML || u == "http://www.w3.org/2000/xmlns/" then qerr "XQST0070" "a reserved namespace"
        ns := ("", u) :: ns.filter (·.1 != "")
      else if ← eatKw "function" then
        expectKw "namespace"
        let u ← pUriLit
        expectS ";"
        if seen.contains "deffn" then qerr "XQST0066" "two default function namespace declarations"
        seen := "deffn" :: seen
        if u == nsXML || u == "http://www.w3.org/2000/xmlns/" then qerr "XQST0070" "a reserved namespace"
        ns := ("#fn", u) :: ns.filter (·.1 != "#fn")
      else if ← eatKw "collation" then
        let u ← pUriLit
        expectS ";"
        if seen.contains "coll" then qerr "XQST0038" "two default collation declarations"
        seen := "coll" :: seen
        if u != "http://www.w3.org/2005/xpath-functions/collation/codepoint" then
          qerr "XQST0038" ("unknown collation " ++ u)
        m := { m with defaultCollation := some u }
      else if ← eatKw "order" then
        expectKw "empty"
        let g ← if ← eatKw "greatest" then pure true else expectKw "least"; pure false
        expectS ";"
        if seen.contains "order" then qerr "XQST0069" "two empty order declarations"
        seen := "order" :: seen
        m := { m with emptyGreatest := g }
      else if ← eatKw "decimal-format" then
        for _ in [0:100] do
          ws
          if (← peekAt 0) == ';' then break
          let _ ← pNCName; expectS "="; let _ ← pStringLit
        expectS ";"
      else synErr "bad default declaration"
    | "boundary-space" =>
      let pres ← if ← eatKw "preserve" then pure true else expectKw "strip"; pure false
      expectS ";"
      if seen.contains "bs" then qerr "XQST0068" "two boundary-space declarations"
      seen := "bs" :: seen
      cfg := { cfg with boundaryPreserve := pres }
    | "base-uri" =>
      let u ← pUriLit
      expectS ";"
      if seen.contains "base" then qerr "XQST0032" "two base-uri declarations"
      seen := "base" :: seen
      m := { m with baseUri := some u }
    | "construction" =>
      if !(← eatKw "strip") then expectKw "preserve"
      expectS ";"
      if seen.contains "constr" then qerr "XQST0067" "two construction declarations"
      seen := "constr" :: seen
    | "ordering" =>
      if !(← eatKw "ordered") then expectKw "unordered"
      expectS ";"
      if seen.contains "ordering" then qerr "XQST0065" "two ordering declarations"
      seen := "ordering" :: seen
    | "copy-namespaces" =>
      if !(← eatKw "preserve") then expectKw "no-preserve"
      expectS ","
      if !(← eatKw "inherit") then expectKw "no-inherit"
      expectS ";"
      if seen.contains "copyns" then qerr "XQST0055" "two copy-namespaces declarations"
      seen := "copyns" :: seen
    | "decimal-format" =>
      let _ ← peekQName >>= fun r => match r with | some (_, _, _, e) => set e | none => pure ()
      for _ in [0:100] do
        ws
        if (← peekAt 0) == ';' then break
        let _ ← pNCName; expectS "="; let _ ← pStringLit
      expectS ";"
    | "option" =>
      match ← peekQName with
      | some (p, u, l, e) =>
        set e
        let _ ← withXq cfg ns (resolve p u l "http://www.w3.org/2012/xquery")
      | none => synErr "bad option name"
      let _ ← pStringLit
      expectS ";"
    | "context" =>
      if !(← eatKw "item") then expectKw "value"
      if ctxSeen then qerr "XQST0099" "two context item declarations"
      ctxSeen := true
      let ty ← if ← eatKw "as" then withXq cfg ns (pSeqType 1000) else pure (.seq .item .star)
      if ← eatS ":=" then
        let e ← withXq cfg ns (pExprSingle 100000)
        expectS ";"
        m := { m with decls := m.decls ++ [.ctx ty (some e) false] }
      else
        expectKw "external"
        let d ← if ← eatS ":=" then pure (some (← withXq cfg ns (pExprSingle 100000))) else pure none
        expectS ";"
        m := { m with decls := m.decls ++ [.ctx ty d true] }
    | "variable" =>
      let v ← withXq cfg ns pVar
      if varNames.any (· == v) then qerr "XQST0049" ("variable $" ++ v.show ++ " declared twice")
      varNames := v :: varNames
      if let some (_, u) := m.libNs then
        if v.uri != u then qerr "XQST0048" "a library module variable outside the module namespace"
      let ty ← if ← eatKw "as" then withXq cfg ns (pSeqType 1000) else pure (.seq .item .star)
      if ← eatS ":=" then
        let e ← withXq cfg ns (pExprSingle 100000)
        expectS ";"
        m := { m with decls := m.decls ++ [.var v ty (some e) false] }
      else
        expectKw "external"
        let d ← if ← eatS ":=" then pure (some (← withXq cfg ns (pExprSingle 100000))) else pure none
        expectS ";"
        m := { m with decls := m.decls ++ [.var v ty d true] }
    | "function" =>
      let _ := annots
      let q ← match ← peekQName with
        | some (p, u, l, e) =>
          set e
          withXq cfg ns (resolve p u l ((ns.lookup "#fn").getD nsFN))
        | none => synErr "expected a function name"
      if reservedFnNs.contains q.uri then qerr "XQST0045" ("function " ++ q.show ++ " in a reserved namespace")
      if q.uri == "" then qerr "XQST0060" ("function " ++ q.show ++ " in no namespace")
      if let some (_, u) := m.libNs then
        if q.uri != u then qerr "XQST0048" "a library module function outside the module namespace"
      expectS "("
      let mut ps : Array (QN × IType × Option Expr) := #[]
      if !(← eatS ")") then
        for _ in [0:10000] do
          let v ← withXq cfg ns pVar
          if ps.any (fun (x, _, _) => x == v) then qerr "XQST0039" ("parameter $" ++ v.show ++ " twice")
          let t ← if ← eatKw "as" then withXq cfg ns (pSeqType 1000) else pure (.seq .item .star)
          let d ← if ← eatS ":=" then pure (some (← withXq cfg ns (pExprSingle 100000))) else pure none
          ps := ps.push (v, t, d)
          if !(← eatS ",") then break
        expectS ")"
      let ret ← if ← eatKw "as" then withXq cfg ns (pSeqType 1000) else pure (.seq .item .star)
      let body ← if ← eatKw "external" then pure none
        else pure (some (← withXq cfg ns (pEnclosed 100000)))
      expectS ";"
      let maxA := ps.size
      let minA := (ps.toList.takeWhile (fun (_, _, d) => d.isNone)).length
      if fnSigs.any (fun (q2, lo, hi) => q2 == q && !(hi < minA || maxA < lo)) then
        qerr "XQST0034" ("function " ++ q.show ++ " declared twice")
      fnSigs := (q, minA, maxA) :: fnSigs
      m := { m with decls := m.decls ++ [.fn { name := q, params := ps.toList, ret, body }] }
    | "record" | "type" => synErr ("declare " ++ w ++ " is not implemented")
    | "revalidation" => qerr "XQST0075" "revalidation is not supported"
    | "updating" => qerr "XUST0001" "updating functions are not supported"
    | _ => synErr ("unknown declaration " ++ w)
  m := { m with ns }
  if m.libNs.isNone then
    ws
    let c ← read
    let i ← get
    if i ≥ c.s.size then synErr "a main module needs a query body"
    let b ← withXq cfg ns (pExpr 100000)
    m := { m with body := some b }
  ws
  let c ← read
  let i ← get
  if i < c.s.size then synErr ("unexpected text at offset " ++ toString i ++ ": '" ++
     String.ofList ((List.range (min 20 (c.s.size - i))).map (fun k => chAt c.s (i + k))) ++ "'")
  pure m

/-- Parse an XQuery 4.0 module, with the namespace bindings of the
    environment. -/
def parseModule (src : String) (ns : List (String × String) := []) : M Module :=
  match (pModule.run { s := src.toList.toArray, ns }).run 0 with
  | .ok (m, _) => .ok m
  | .error e => .error e

/-! ## Evaluation -/

def markStatic (e : Env) : Env := e.bind staticKey []

/-- The function items of a declaration: one per arity it accepts
    (4.0 default parameter values), the defaults bound by `let`. -/
def fnBindings (d : FnDecl) : List (QN × Seq) :=
  match d.body with
  | none => []
  | some body =>
    let ps := d.params
    let minA := (ps.takeWhile (fun (_, _, x) => x.isNone)).length
    (List.range (ps.length + 1 - minA)).map (fun j =>
      let k := minA + j
      let given := ps.take k
      let rest := ps.drop k
      let body' := rest.foldr (fun (v, t, x) acc => Expr.letE v t (x.getD (.seq [])) acc) body
      (fnKey d.name k, [.fn (.inline (given.map (fun (v, t, _) => (v, t))) d.ret body' false [])]))

/-- The module texts the caller gave for a namespace. -/
def moduleTexts (env : Env) (uri : String) : List String :=
  env.resources.filterMap (fun (k, v) => if k == "#module " ++ uri then some v else none)

/-- The library modules a module imports, transitively (imported
    modules first), to depth `d`. -/
def loadImports (env : Env) : Nat → Module → M (List Module)
  | 0, _ => err "XQST0093" "module imports nested too deeply"
  | d + 1, m => do
    let mut out : List Module := []
    for (_, u, _) in m.imports do
      let texts := moduleTexts env u
      if texts.isEmpty then err "XQST0059" ("no module found for namespace " ++ u)
      for t in texts do
        let lm ← parseModule t
        if (lm.libNs.map (·.2)) != some u then err "XQST0059" ("the module text is not a module for " ++ u)
        let sub ← loadImports env d lm
        out := out ++ sub ++ [lm]
    pure out

def Module.globals (m : Module) : List QN :=
  m.decls.filterMap (fun d => match d with | .var v .. => some v | _ => none)

def Module.fnArities (m : Module) : List (QN × Nat × Nat) :=
  m.decls.filterMap (fun d => match d with
    | .fn fd =>
      let minA := (fd.params.takeWhile (fun (_, _, x) => x.isNone)).length
      some (fd.name, minA, fd.params.length)
    | _ => none)

/-- The static checks of `Static.staticErr` over every module: the
    initializers, the function bodies, the query body. -/
def checkModules (env : Env) (ms : List Module) : M Unit := do
  let globals := ms.flatMap Module.globals
  let fns := ms.flatMap Module.fnArities
  let known (q : QN) (k : Nat) : Bool :=
    (findSigAny q).isSome || (q.uri == nsFN && q.loc == "concat") ||
    fns.any (fun (q2, lo, hi) => q2 == q && lo ≤ k && k ≤ hi)
  let base : SCtx := { vars := env.vars.map (·.1) ++ globals, knownFn := known }
  for m in ms do
    for d in m.decls do
      let r := match d with
        | .var _ _ (some e) _ => staticErr 100000 base e
        | .ctx _ (some e) _ => staticErr 100000 base e
        | .fn fd => match fd.body with
          | some b =>
            -- defaults see the earlier parameters; the body sees all of them
            staticErr 100000 (base.add (fd.params.map (·.1))) b
          | none => none
        | _ => none
      if let some e := r then throw e
    if let some b := m.body then
      if let some e := staticErr 100000 base b then throw e

/-- Bind the functions of the modules, then their global variables and
    context value. A variable whose initializer reads a global that is
    not bound yet is tried again after the others (XQuery 4.0 §5.16:
    order by dependency); a round with no progress is `XQDY0054`. -/
def bindModules (fuel : Nat) (env : Env) (ms : List Module) : M Env := do
  let mut env := env
  for m in ms do
    for dcl in m.decls do
      if let .fn fd := dcl then
        for b in fnBindings fd do env := { env with vars := b :: env.vars }
  let globals := ms.flatMap Module.globals
  let mut pending : List Decl := ms.flatMap (fun m => m.decls.filter (fun d => match d with | .fn _ => false | _ => true))
  for _ in [0:pending.length + 1] do
    if pending.isEmpty then break
    let mut later : List Decl := []
    let mut lastErr : Option Err := none
    for dcl in pending do
      match dcl with
      | .var v ty init external =>
        let env1 := markStatic env
        let r : M Seq := if external then
            match env.vars.find? (fun (q, _) => q == v) with
            | some (_, s) => pure s
            | none => match init with
              | some e => eval fuel env1 e
              | none => err "XPDY0002" ("no value for the external variable $" ++ v.show)
          else eval fuel env1 (init.getD (.seq []))
        match r with
        | .ok val =>
          let val ← env.coerce ty val ("$" ++ v.show)
          env := env.bind v val
        | .error e =>
          if e.code == "XPST0008" && globals.any (fun g => e.msg.endsWith ("$" ++ g.show)) then
            later := later ++ [dcl]; lastErr := some e
          else throw e
      | .ctx ty init external =>
        let env1 := markStatic env
        let val ← if external then
            match env.ctx with
            | some s => pure s
            | none => match init with
              | some e => eval fuel env1 e
              | none => pure []
          else eval fuel env1 (init.getD (.seq []))
        if !val.isEmpty || !external then
          if !(env.seqMatches val ty) then err "XPTY0004" "the context value does not match its declared type"
          env := { env with ctx := some val, pos := 1, size := 1 }
      | .fn _ => pure ()
    if later.length == pending.length then
      match lastErr with
      | some e => throw { e with code := "XQDY0054", msg := "circular variable dependency: " ++ e.msg }
      | none => break
    pending := later
  pure env

/-- Evaluate a main module. -/
def evalModule (fuel : Nat) (env : Env) (m : Module) : M Seq := do
  let env := { env with ns := m.ns }
  let env := match m.defaultCollation with | some c => { env with defaultCollation := c } | none => env
  let env := match m.baseUri with | some b => { env with baseUri := b } | none => env
  let libs ← loadImports env 20 m
  checkModules env (libs ++ [m])
  let env ← bindModules fuel env (libs ++ [m])
  match m.body with
  | some b => eval fuel (markStatic env) b
  | none => err "XPST0003" "a library module has no query body"

/-- Parse and evaluate an XQuery 4.0 main module. -/
def evalQuery (src : String) (env : Env := {}) (fuel : Nat := 100000) : M Seq := do
  let m ← parseModule src env.ns
  evalModule fuel env m

def evalQShow (src : String) : String :=
  match evalQuery src with
  | .ok s => showSeq s
  | .error e => "error " ++ e.code ++ ": " ++ e.msg

#guard evalQShow "1 + 2" == "3"
#guard evalQShow "for $x in 1 to 3 where $x > 1 return $x * 10" == "20 30"
#guard evalQShow "declare function local:f($n) { if ($n le 1) then 1 else $n * local:f($n - 1) }; local:f(5)" == "120"
#guard evalQShow "declare variable $x := 4; $x + 1" == "5"
#guard evalQShow "for $x in (3, 1, 2) order by $x descending return $x" == "3 2 1"
#guard evalQShow "string(<a b='1'>x{1 + 1}y</a>)" == "x2y"
#guard evalQShow "<a b='1'/>/@b = 1" == "true"
#guard evalQShow "count(<a><b/><b/></a>/b)" == "2"
#guard evalQShow "try { 1 div 0 } catch * { $err:code }" == "err:FOAR0001"
#guard evalQShow "typeswitch (1) case xs:string return 'a' case xs:integer return 'b' default return 'c'" == "b"
#guard evalQShow "switch (2) case 1 return 'a' case 2 return 'b' default return 'c'" == "b"
#guard evalQShow "for $x in 1 to 6 group by $k := $x mod 2 order by $k return sum($x)" == "12 9"
#guard evalQShow "for tumbling window $w in 1 to 5 start at $s when true() end at $e when $e - $s eq 1 return count($w)" == "2 2 1"
#guard evalQShow "for $x in 1 to 3 count $c return $c" == "1 2 3"
#guard evalQShow "name(element foo { 'x' })" == "foo"
#guard evalQShow "string(text { 1, 2 })" == "1 2"
#guard evalQShow "'&lt;'" == "<"

end L4Factoidal.XQuery4
