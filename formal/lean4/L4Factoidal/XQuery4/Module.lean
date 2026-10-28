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
under `#module <uri>`). `import schema` binds its prefix; the schema itself is the host's (no schema
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
  /-- The annotations (`fn:function-annotations`). -/
  annots : List (QN × List Atomic) := []
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
  /-- Named item types (`declare type`, `declare record`) in scope after
      the prolog: this module's and the public ones it imports. -/
  types : List (QN × IType) := []
  /-- The item types this module declares, with `true` for `%private`. -/
  ownTypes : List (QN × IType × Bool) := []
  /-- `import schema`: the target namespaces (XQuery 4.0 §5.11). -/
  schemaImports : List String := []
  /-- `declare construction strip` (§5.6); the default is `preserve`. -/
  constructionStrip : Bool := false
  /-- Variables and functions declared `%private` (§5.15): not seen
      by an importing module. -/
  privates : List QN := []
  /-- Decimal formats (`declare decimal-format`), as `Env.decimalFormats`. -/
  decimalFormats : List (String × List (String × String)) := []
  /-- Output declarations (`declare option output:name "value"`, §5.20.2):
      local name and value, in order (`XPath4.declParams` reads them). -/
  outputDecls : List (String × String) := []
deriving Inhabited

def qerr {α} (code msg : String) : P α := throw { code, msg }

def withXq {α} (cfg : Cfg) (ns : List (String × String)) (p : P α) : P α :=
  withReader (fun c => { c with ns, ext := some (grammar cfg), types := cfg.types,
                                lenientTypes := cfg.lenient }) p

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

/-- Annotations `%name` or `%name(literals)` (XQuery 4.0 §5.18, [32]): the
    expanded name and the values. An unprefixed name is in the
    `http://www.w3.org/2012/xquery` namespace (the `xq` prefix); a name in
    a reserved namespace is XQST0045. -/
def pAnnotations : P (List (QN × List Atomic)) := do
  let mut out : List (QN × List Atomic) := []
  for _ in [0:1000] do
    ws
    if (← peekAt 0) != '%' then break
    adv 1
    match ← peekQName with
    | some (p, u, l, e) =>
      set e
      let q ← resolve p u l "http://www.w3.org/2012/xquery"
      if q.uri == "http://www.w3.org/2012/xquery" && !(["public", "private", "constructor"].contains l) then
        qerr "XQST0045" ("reserved annotation %" ++ l)
      if [nsFN, nsXS, nsMATH, nsMAP, nsARR, "http://www.w3.org/XML/1998/namespace",
          "http://www.w3.org/2001/XMLSchema-instance"].contains q.uri then
        qerr "XQST0045" ("annotation in a reserved namespace " ++ l)
      let mut vals : List Atomic := []
      if ← eatS "(" then
        -- AnnotationValue: a string literal, a numeric literal with an
        -- optional minus, a QName literal `#name`, `true()` or `false()`
        for _ in [0:1000] do
          ws
          let ch ← peekAt 0
          if ch == '"' || ch == '\'' then vals := vals ++ [Atomic.ofStr (← pStringLit)]
          else if ch == '#' then
            adv 1
            match ← peekQName with
            | some (p2, u2, l2, e2) =>
              set e2
              vals := vals ++ [Atomic.ofQN (← resolve p2 u2 l2 "")]
            | none => synErr "bad QName literal"
          else if ch == '-' || ch == '+' || ch.isDigit || ch == '.' then
            let neg ← eatS "-"
            if !neg then let _ ← eatS "+"
            ws
            let ch2 ← peekAt 0
            if !(ch2.isDigit || ch2 == '.') then synErr "an annotation value must be a literal"
            match ← pNumber with
            | .lit a =>
              vals := vals ++ [if !neg then a else
                match a.num? with
                | some v => (numNeg v).atomic
                | none => a]
            | _ => synErr "an annotation value must be a literal"
          else if (← kwThen "true" '(') || (← kwThen "false" '(') then
            let n ← pNCName; expectS "("; expectS ")"
            vals := vals ++ [Atomic.ofBool (n == "true")]
          else synErr "an annotation value must be a literal"
          if !(← eatS ",") then break
        expectS ")"
      out := out ++ [(q, vals)]
    | none => synErr "bad annotation"
  pure out

/-- Does the annotation list hold `%public` or `%private` more than once
    or both (XQuery 4.0 §5.15, §5.18; `code` is XQST0106 or XQST0116)? -/
def checkVisibility (annots : List (QN × List Atomic)) (code : String) : P Unit := do
  let nPub := (annots.filter (fun (q, _) => q.uri == "http://www.w3.org/2012/xquery" && q.loc == "public")).length
  let nPriv := (annots.filter (fun (q, _) => q.uri == "http://www.w3.org/2012/xquery" && q.loc == "private")).length
  if nPub > 1 || nPriv > 1 || (nPub > 0 && nPriv > 0) then
    qerr code "both %public and %private, or one of them twice"

def isPrivateAnn (annots : List (QN × List Atomic)) : Bool :=
  annots.any (fun (q, _) => q.uri == "http://www.w3.org/2012/xquery" && q.loc == "private")

/-- A record field name: an NCName or a string literal. -/
def pFieldName : P String := do
  ws
  let ch ← peekAt 0
  if ch == '"' || ch == '\'' then pStringLit else pNCName

/-- Is the item type a generalized atomic type (an atomic type, an
    enumeration or a union of those)? -/
def isGenAtomic : IType → Bool
  | .atomic _ => true
  | .enum _ => true
  | .choice ts => !ts.isEmpty && ts.all (fun t => match t with | .atomic _ => true | .enum _ => true | _ => false)
  | _ => false

/-- Checks on the name of a declared item type (§5.19, §5.20): a public
    type of a library module is in the module namespace (XQST0048); any
    other name is not in a reserved namespace (XQST0045). -/
def checkTypeName (lib : Option (String × String)) (annots : List (QN × List Atomic)) (q : QN) : P Unit := do
  match lib with
  | some (_, u) =>
    if !isPrivateAnn annots then
      if q.uri != u then qerr "XQST0048" ("public type " ++ q.show ++ " outside the module namespace")
    else if reservedFnNs.contains q.uri then qerr "XQST0045" ("type " ++ q.show ++ " in a reserved namespace")
  | none =>
    if reservedFnNs.contains q.uri then qerr "XQST0045" ("type " ++ q.show ++ " in a reserved namespace")

/-- The names in the source text `s[st, en)` of an item type that may
    refer to a named item type (used for the cycle check of §5.19): QNames
    not followed by `(`, with prefixes resolved by `ns`; string literals
    are skipped. -/
def typeRefs (s : Array Char) (st en : Nat) (ns : List (String × String)) : List QN := Id.run do
  let mut out : List QN := []
  let mut i := st
  for _ in [0:en - st + 1] do
    if i ≥ en then break
    let ch := chAt s i
    if ch == '\'' || ch == '"' then
      let mut j := i + 1
      for _ in [0:en - i + 1] do
        if j ≥ en || chAt s j == ch then break
        j := j + 1
      i := j + 1
    else if ch == 'Q' && chAt s (i + 1) == '{' then
      let mut j := i + 2
      for _ in [0:en - i + 1] do
        if j ≥ en || chAt s j == '}' then break
        j := j + 1
      let uri := String.ofList ((List.range (j - i - 2)).map (fun k => chAt s (i + 2 + k)))
      match ncnameAt s (j + 1) with
      | some (l, e) =>
        if chAt s e != '(' then out := { uri, loc := l } :: out
        i := e
      | none => i := j + 1
    else
      match ncnameAt s i with
      | some (n, e) =>
        if chAt s e == ':' then
          match ncnameAt s (e + 1) with
          | some (l, e2) =>
            if chAt s e2 != '(' then
              match (ns.lookup n).orElse (fun _ => defaultNs.lookup n) with
              | some u => out := { uri := u, loc := l, pfx := n } :: out
              | none => pure ()
            i := e2
          | none => i := e
        else
          if chAt s e != '(' then out := { uri := (ns.lookup "").getD "", loc := n } :: out
          i := e
      | none => i := i + 1
  return out

/-- Parse a module (main or library). `types0` are named types from a
    first pass; `lenient` makes that first pass. -/
def pModule (types0 : List (QN × IType) := []) (lenient : Bool := false)
    (loader : String → Except Err (List (QN × IType)) := fun _ => .ok []) : P Module := do
  let mut m : Module := {}
  let mut cfg : Cfg := { types := types0, lenient }
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
  -- the item types declared in this module, and the imported ones
  let mut declared : List QN := []
  let mut importedTy : List QN := []
  let mut typeDeps : List (QN × List QN) := []
  for _ in [0:100000] do
    let some kw ← atDecl | break
    if kw == "import" then
      expectKw "import"
      if ← eatKw "schema" then
        -- XQuery 4.0 §5.11: the in-scope schema definitions come from the
        -- host (`XPath4.SchemaHook`); the import binds the prefix
        let mut pfx : Option String := none
        if ← eatKw "namespace" then
          pfx := some (← pNCName)
          expectS "="
        else if ← eatKw "fixed" then
          expectKw "default"; expectKw "element"; expectKw "namespace"; pfx := some ""
        else if ← eatKw "default" then
          expectKw "element"; expectKw "namespace"; pfx := some ""
        let u ← pUriLit
        if ← eatKw "at" then
          for _ in [0:1000] do
            let _ ← pUriLit
            if !(← eatS ",") then break
        expectS ";"
        if u == "" && (pfx.map (· != "")).getD false then qerr "XQST0057" "a schema import with a prefix and an empty namespace"
        if m.schemaImports.contains u then qerr "XQST0058" "the same schema namespace imported twice"
        m := { m with schemaImports := m.schemaImports ++ [u] }
        match pfx with
        | some "xml" | some "xmlns" => qerr "XQST0070" "import prefix xml or xmlns"
        | some p =>
          if p != "" && seenNs.contains p then qerr "XQST0033" ("prefix " ++ p ++ " declared twice")
          if p != "" then seenNs := p :: seenNs
          ns := (p, u) :: ns.filter (·.1 != p)
        | none => pure ()
        continue
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
      -- the public item types of the imported module (§5.19)
      match loader u with
      | .error e => throw e
      | .ok tys =>
        for (tq, tt) in tys do
          importedTy := tq :: importedTy
          cfg := { cfg with types := (tq, tt) :: cfg.types.filter (fun (n, _) => !(n == tq)) }
      continue
    expectKw "declare"
    let annots ← withXq cfg ns pAnnotations
    let w ← pNCName
    -- 4.0: `declare fixed default ... namespace` (fixed for the module)
    let w ← if w == "fixed" then pNCName else pure w
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
        let mut props : List (String × String) := []
        for _ in [0:100] do
          ws
          if (← peekAt 0) == ';' then break
          let pn ← pNCName; expectS "="
          let pv ← pStringLit
          if props.any (·.1 == pn) then qerr "XQST0114" ("decimal format property " ++ pn ++ " twice")
          props := props ++ [(pn, pv)]
        expectS ";"
        if m.decimalFormats.any (·.1 == "") then qerr "XQST0111" "two default decimal formats"
        m := { m with decimalFormats := m.decimalFormats ++ [("", props)] }
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
      let strip ← if ← eatKw "strip" then pure true else expectKw "preserve"; pure false
      expectS ";"
      if seen.contains "constr" then qerr "XQST0067" "two construction declarations"
      seen := "constr" :: seen
      m := { m with constructionStrip := strip }
    | "ordering" =>
      if !(← eatKw "ordered") then expectKw "unordered"
      expectS ";"
      if seen.contains "ordering" then qerr "XQST0065" "two ordering declarations"
      seen := "ordering" :: seen
    | "copy-namespaces" =>
      let pres ← if ← eatKw "preserve" then pure true else expectKw "no-preserve"; pure false
      expectS ","
      let inh ← if ← eatKw "inherit" then pure true else expectKw "no-inherit"; pure false
      expectS ";"
      cfg := { cfg with copyPreserve := pres, copyInherit := inh }
      if seen.contains "copyns" then qerr "XQST0055" "two copy-namespaces declarations"
      seen := "copyns" :: seen
    | "decimal-format" =>
      let key ← match ← peekQName with
        | some (p, u, l, e) =>
          set e
          let q ← withXq cfg ns (resolve p u l "")
          pure q.eqn
        | none => synErr "expected a decimal format name"
      let mut props : List (String × String) := []
      for _ in [0:100] do
        ws
        if (← peekAt 0) == ';' then break
        let pn ← pNCName; expectS "="
        let pv ← pStringLit
        if props.any (·.1 == pn) then qerr "XQST0114" ("decimal format property " ++ pn ++ " twice")
        props := props ++ [(pn, pv)]
      expectS ";"
      if m.decimalFormats.any (·.1 == key) then qerr "XQST0111" "two decimal formats with one name"
      m := { m with decimalFormats := m.decimalFormats ++ [(key, props)] }
    | "option" =>
      let oq ← match ← peekQName with
      | some (p, u, l, e) =>
        set e
        withXq cfg ns (resolve p u l "http://www.w3.org/2012/xquery")
      | none => synErr "bad option name"
      -- an XQuery string literal: references expanded (§4.2.1)
      let ov ← match expandRefs (← pStringLit) with
        | .ok t => pure t
        | .error ex => throw ex
      expectS ";"
      -- output declarations (§5.20.2): XQST0108, XQST0109, XQST0110
      if oq.uri == nsOUTPUT then
        if m.libNs.isSome then qerr "XQST0108" "an output declaration in a library module"
        if ((paramKinds.lookup oq.loc).isNone && oq.loc != "parameter-document") || oq.loc == "use-character-maps" then
          qerr "XQST0109" ("unknown serialization parameter output:" ++ oq.loc)
        if m.outputDecls.any (·.1 == oq.loc) then qerr "XQST0110" ("output:" ++ oq.loc ++ " declared twice")
        m := { m with outputDecls := m.outputDecls ++ [(oq.loc, ov)] }
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
      checkVisibility annots "XQST0116"
      let v ← withXq cfg ns pVar
      if varNames.any (· == v) then qerr "XQST0049" ("variable $" ++ v.show ++ " declared twice")
      varNames := v :: varNames
      if let some (_, u) := m.libNs then
        if v.uri != u && !isPrivateAnn annots then qerr "XQST0048" "a library module variable outside the module namespace"
      let ty ← if ← eatKw "as" then withXq cfg ns (pSeqType 1000) else pure (.seq .item .star)
      if ← eatS ":=" then
        let e ← withXq cfg ns (pExprSingle 100000)
        expectS ";"
        m := { m with decls := m.decls ++ [.var v ty (some e) false] }
        if isPrivateAnn annots then m := { m with privates := v :: m.privates }
      else
        expectKw "external"
        let d ← if ← eatS ":=" then pure (some (← withXq cfg ns (pExprSingle 100000))) else pure none
        expectS ";"
        m := { m with decls := m.decls ++ [.var v ty d true] }
        if isPrivateAnn annots then m := { m with privates := v :: m.privates }
    | "function" =>
      checkVisibility annots "XQST0106"
      let q ← match ← peekQName with
        | some (p, u, l, e) =>
          if p.isNone && u.isNone && reservedFnNames.contains l then
            synErr ("reserved function name " ++ l)
          set e
          let q ← withXq cfg ns (resolve p u l ((ns.lookup "#fn").getD nsFN))
          -- 4.0: an unprefixed name with the default function namespace
          -- fn is a name in no namespace (§5.18.1)
          pure (if p.isNone && u.isNone && q.uri == nsFN then { q with uri := "" } else q)
        | none => synErr "expected a function name"
      if reservedFnNs.contains q.uri then qerr "XQST0045" ("function " ++ q.show ++ " in a reserved namespace")
      if let some (_, u) := m.libNs then
        if q.uri != u && !isPrivateAnn annots then qerr "XQST0048" "a library module function outside the module namespace"
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
      m := { m with decls := m.decls ++ [.fn { name := q, params := ps.toList, ret, body, annots }] }
      if isPrivateAnn annots then m := { m with privates := q :: m.privates }
    | "type" =>
      checkVisibility annots "XQST0106"
      let q ← match ← peekQName with
        | some (p, u, l, e) => set e; withXq cfg ns (resolve p u l ((ns.lookup "").getD ""))
        | none => synErr "expected a type name"
      checkTypeName m.libNs annots q
      expectKw "as"
      let st ← get
      let t ← withXq cfg ns (pItemType 1000)
      let en ← get
      expectS ";"
      if !lenient && (declared.contains q || importedTy.contains q) then
        qerr "XQST0146" ("type " ++ q.show ++ " declared twice")
      declared := q :: declared
      typeDeps := typeDeps ++ [(q, typeRefs (← read).s st en ns)]
      m := { m with ownTypes := m.ownTypes ++ [(q, t, isPrivateAnn annots)] }
      cfg := { cfg with types := (q, t) :: cfg.types.filter (fun (n, _) => !(n == q)) }
      -- the constructor function of a generalized atomic type (§5.19,
      -- §4.21.5): `$arg cast as T?`
      if isGenAtomic t then
        let a : QN := { uri := "", loc := "arg" }
        let body : Expr := .cast (.var a) t true
        let pt : IType := .seq (.atomic (.b .anyAtomicType)) .opt
        if fnSigs.any (fun (q2, lo, hi) => q2 == q && !(hi < 1 || 1 < lo)) then
          qerr "XQST0034" ("function " ++ q.show ++ " declared twice")
        fnSigs := (q, 1, 1) :: fnSigs
        m := { m with decls := m.decls ++ [.fn { name := q, params := [(a, pt, none)], ret := .seq t .opt,
                                                 body := some body, annots }] }
        if isPrivateAnn annots then m := { m with privates := q :: m.privates }
    | "record" =>
      checkVisibility annots "XQST0106"
      let q ← match ← peekQName with
        | some (p, u, l, e) => set e; withXq cfg ns (resolve p u l ((ns.lookup "").getD ""))
        | none => synErr "expected a record type name"
      checkTypeName m.libNs annots q
      expectS "("
      let mut fs : Array (String × Bool × IType × Option Expr) := #[]
      let mut ext := false
      if !(← eatS ")") then
        for _ in [0:10000] do
          if ← eatS "*" then
            if fs.isEmpty then synErr "a record type with only '*'"
            ext := true; break
          ws
          let quoted := (← peekAt 0) == '"' || (← peekAt 0) == '\''
          let f ← pFieldName
          -- §5.20.2: the field names are NCNames, not string literals
          if quoted then synErr "a record field name written as a string literal"
          let opt ← eatS "?"
          let ft ← if ← eatKw "as" then withXq cfg ns (pSeqType 1000) else pure (.seq .item .star)
          let d ← if ← eatS ":=" then pure (some (← withXq cfg ns (pExprSingle 100000))) else pure none
          if fs.any (·.1 == f) then qerr "XPST0021" ("record field " ++ f ++ " twice")
          fs := fs.push (f, opt, ft, d)
          if !(← eatS ",") then break
        expectS ")"
      expectS ";"
      if !lenient && (declared.contains q || importedTy.contains q) then
        qerr "XQST0146" ("type " ++ q.show ++ " declared twice")
      declared := q :: declared
      let rt : IType := .record (fs.toList.map (fun (f, o, t, _) => (f, o, t))) ext
      m := { m with ownTypes := m.ownTypes ++ [(q, rt, isPrivateAnn annots)] }
      cfg := { cfg with types := (q, rt) :: cfg.types.filter (fun (n, _) => !(n == q)) }
      -- the record constructor function (§5.20.2): one parameter per
      -- field; an optional field defaults to the empty sequence and an
      -- empty optional field gives no entry
      let pv (f : String) : QN := { uri := "", loc := f }
      let params := fs.toList.map (fun (f, o, t, d) =>
        (pv f, t, if d.isSome then d else if o then some (Expr.seq []) else none))
      let entry (f : String) (o : Bool) : Expr :=
        let e : Expr := .call { uri := nsMAP, loc := "entry" } [some (.lit (Atomic.ofStr f)), some (.var (pv f))] []
        if o then .ifE (.call { uri := nsFN, loc := "empty" } [some (.var (pv f))] []) (.seq []) e else e
      let body : Expr := .call { uri := nsMAP, loc := "merge" }
        [some (.seq (fs.toList.map (fun (f, o, _, _) => entry f o)))] []
      let lo := (params.takeWhile (fun (_, _, x) => x.isNone)).length
      if params.drop lo |>.any (fun (_, _, x) => x.isNone) then
        qerr "XQST0148" "a required record field after an optional one"
      if fnSigs.any (fun (q2, lo2, hi2) => q2 == q && !(hi2 < lo || params.length < lo2)) then
        qerr "XQST0034" ("function " ++ q.show ++ " declared twice")
      fnSigs := (q, lo, params.length) :: fnSigs
      m := { m with decls := m.decls ++ [.fn { name := q, params, ret := rt, body := some body, annots }] }
      if isPrivateAnn annots then m := { m with privates := q :: m.privates }
    | "revalidation" => qerr "XQST0075" "revalidation is not supported"
    | "updating" => qerr "XUST0001" "updating functions are not supported"
    | _ => synErr ("unknown declaration " ++ w)
  -- §5.19: a cyclic or self-referential `declare type` is XQST0140
  if !lenient then
    let names := typeDeps.map (·.1)
    for (q, ds) in typeDeps do
      let mut reach : List QN := ds.filter (names.contains ·)
      for _ in [0:names.length + 1] do
        reach := reach ++ (reach.flatMap (fun r => (typeDeps.find? (·.1 == r)).map (·.2) |>.getD []))
        reach := (reach.filter (names.contains ·)).eraseDups
      if reach.contains q then qerr "XQST0140" ("item type " ++ q.show ++ " refers to itself")
  m := { m with ns, types := cfg.types }
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
def parseModule (src : String) (ns : List (String × String) := [])
    (loader : String → Except Err (List (QN × IType)) := fun _ => .ok []) : M Module :=
  let s := src.toList.toArray
  -- first pass: the named types, with forward references read as item()
  let types0 := match ((pModule [] true loader).run { s, ns }).run 0 with
    | .ok (m, _) => m.types
    | .error _ => []
  match ((pModule types0 false loader).run { s, ns }).run 0 with
  | .ok (m, _) => .ok m
  | .error e => .error e

/-! ## Evaluation -/

def markStatic (e : Env) : Env := e.bind staticKey []

/-- The binding of a declaration: the function item of the full arity
    and, for each optional parameter, a focus function computing its
    default value in the focus of the call (XQuery 4.0 §5.18.2). -/
def fnBinding (d : FnDecl) : Option (QN × Seq) :=
  match d.body with
  | none => none
  | some body =>
    let ps := d.params
    let lo := (ps.takeWhile (fun (_, _, x) => x.isNone)).length
    let full : Item := .fn (.inline (ps.map (fun (v, t, _) => (v, t))) d.ret body false [])
    let dflts : List Item := (ps.drop lo).map (fun (_, t, x) =>
      .fn (.inline [] t (x.getD (.seq [])) true []))
    some (fnKey d.name lo ps.length, full :: dflts)

/-- The module texts the caller gave for a namespace. -/
def moduleTexts (env : Env) (uri : String) : List String :=
  env.resources.filterMap (fun (k, v) => if k == "#module " ++ uri then some v else none)

/-- The public item types of the library modules for namespace `uri`
    (§5.19: public types are visible after `import module`); `seen` ends
    cyclic imports and `d` bounds the nesting. -/
def typeLoader (env : Env) : Nat → List String → String → Except Err (List (QN × IType))
  | 0, _, _ => .ok []
  | d + 1, seen, uri =>
    if seen.contains uri then .ok [] else
    (moduleTexts env uri).foldlM (fun acc t => do
      let lm ← parseModule t [] (typeLoader env d (uri :: seen))
      if (lm.libNs.map (·.2)) != some uri then pure acc
      else pure (acc ++ lm.ownTypes.filterMap (fun (q, ty, priv) => if priv then none else some (q, ty)))) []

/-- The library modules a module imports, transitively (imported
    modules first), to depth `d`; a namespace already loaded (`seen`)
    is not loaded again, so cyclic imports end (XQuery 4.0 §5.12). -/
def loadImports (env : Env) : Nat → List String → Module → M (List Module × List String)
  | 0, _, _ => err "XQST0093" "module imports nested too deeply"
  | d + 1, seen, m => do
    let mut out : List Module := []
    let mut seen := seen
    for (_, u, _) in m.imports do
      if seen.contains u then continue
      seen := u :: seen
      let texts := moduleTexts env u
      if texts.isEmpty then err "XQST0059" ("no module found for namespace " ++ u)
      for t in texts do
        let lm ← parseModule t [] (typeLoader env 8 seen)
        if (lm.libNs.map (·.2)) != some u then err "XQST0059" ("the module text is not a module for " ++ u)
        let (sub, seen') ← loadImports env d seen lm
        seen := seen'
        out := out ++ sub ++ [lm]
    pure (out, seen)

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
    fns.any (fun (q2, lo, hi) => (q2 == q || (q.uri == nsFN && q.pfx == "" && q2 == { q with uri := "" }))
      && lo ≤ k && k ≤ hi)
  if globals.length != globals.eraseDups.length then
    err "XQST0049" "a global variable declared in two modules"
  for (q, lo, hi) in fns do
    if (fns.filter (fun (q2, lo2, hi2) => q2 == q && !(hi < lo2 || hi2 < lo))).length > 1 then
      err "XQST0034" ("function " ++ q.show ++ " declared twice")
  for m in ms do
    -- a module sees its own declarations and the public ones of the others
    -- (XQuery 4.0 §5.12: only the modules it imports directly, not
    -- those they import)
    let vis (m2 : Module) (q : QN) : Bool :=
      m2.libNs == m.libNs ||
      (m.imports.any (fun (_, u, _) => some u == m2.libNs.map (·.2)) && !m2.privates.any (· == q))
    let globalsM := ms.flatMap (fun m2 => m2.globals.filter (vis m2))
    let fnsM := ms.flatMap (fun m2 => m2.fnArities.filter (fun (q, _, _) => vis m2 q))
    let knownM (q : QN) (k : Nat) : Bool :=
      (findSigAny q).isSome || (q.uri == nsFN && q.loc == "concat") ||
      fnsM.any (fun (q2, lo, hi) => (q2 == q || (q.uri == nsFN && q.pfx == "" && q2 == { q with uri := "" }))
        && lo ≤ k && k ≤ hi)
    let _ := known
    let base : SCtx := { vars := env.vars.map (·.1) ++ globalsM, knownFn := knownM }
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
def bindFns (env : Env) (ms : List Module) : Env :=
  ms.foldl (fun e m => m.decls.foldl (fun e d => match d with
    | .fn fd => match fnBinding fd with
      | some b => { e with vars := b :: e.vars }
      | none => e
    | _ => e) e) env

/-- Bind one global variable or the context value; `none` when the
    initializer reads a global not bound yet (try again later). -/
def bindOne (fuel : Nat) (globals : List QN) (env : Env) : Decl → M (Option Env × Option Err)
  | .var v ty init external => do
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
      pure (some (env.bind v val), none)
    | .error e =>
      if e.code == "XPST0008" && globals.any (fun g => e.msg.endsWith ("$" ++ g.show)) then
        pure (none, some e)
      else throw e
  | .ctx ty init external => do
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
      pure (some { env with ctx := some val, pos := 1, size := 1 }, none)
    else pure (some env, none)
  | .fn _ => pure (some env, none)

/-- One round over the pending declarations: the bound environment,
    the declarations to try again, the last postponement. -/
def bindRound (fuel : Nat) (globals : List QN) : Env → List Decl → M (Env × List Decl × Option Err)
  | env, [] => pure (env, [], none)
  | env, d :: ds => do
    match ← bindOne fuel globals env d with
    | (some env', _) => bindRound fuel globals env' ds
    | (none, e) =>
      let (env', later, e') ← bindRound fuel globals env ds
      pure (env', d :: later, e'.orElse (fun _ => e))

/-- Rounds until every declaration is bound; a round with no progress
    is `XQDY0054` (XQuery 4.0 §5.16: variables bound in dependency
    order, a cycle is an error). -/
def bindRounds (fuel : Nat) (globals : List QN) : Nat → Env → List Decl → M Env
  | _, env, [] => pure env
  | 0, env, _ => pure env
  | k + 1, env, pending@(_ :: _) => do
    let (env', later, lastErr) ← bindRound fuel globals env pending
    if later.length == pending.length then
      match lastErr with
      | some e => throw { e with code := "XQDY0054", msg := "circular variable dependency: " ++ e.msg }
      | none => pure env'
    else bindRounds fuel globals k env' later

def bindModules (fuel : Nat) (env : Env) (ms : List Module) : M Env :=
  let pending := ms.flatMap (fun m => m.decls.filter (fun d => match d with | .fn _ => false | _ => true))
  bindRounds fuel (ms.flatMap Module.globals) (pending.length + 1) (bindFns env ms) pending

/-- The dynamic context of a module before its declarations are bound:
    the prolog's namespaces, collation, base URI and decimal formats. -/
def moduleEnv (env : Env) (m : Module) : Env :=
  let env := { env with ns := m.ns }
  let env := match m.defaultCollation with | some c => { env with defaultCollation := c } | none => env
  let env := match m.baseUri with | some b => { env with baseUri := b } | none => env
  let env := { env with decimalFormats := m.decimalFormats ++ env.decimalFormats }
  if m.constructionStrip then env.bind constructionStripKey [] else env

/-- Evaluate a main module. -/
def evalModule (fuel : Nat) (env : Env) (m : Module) : M Seq := do
  -- XQuery 4.0 §5.11: an imported schema namespace must be one the in-scope
  -- schema definitions (`XPath4.SchemaHook`) have components for
  for u in m.schemaImports do
    if !env.schema.targetNamespaces.contains u then
      err "XQST0059" ("no schema for the imported namespace " ++ u)
  let env := moduleEnv env m
  let (libs, _) ← loadImports env 50 ((m.libNs.map (·.2)).toList) m
  checkModules env (libs ++ [m])
  let env ← bindModules fuel env (libs ++ [m])
  match m.body with
  | some b => eval fuel (markStatic env) b
  | none => err "XPST0003" "a library module has no query body"

/-- Parse and evaluate an XQuery 4.0 main module. -/
def evalQuery (src : String) (env : Env := {}) (fuel : Nat := 100000) : M Seq := do
  let m ← parseModule src env.ns (typeLoader env 8 [])
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
