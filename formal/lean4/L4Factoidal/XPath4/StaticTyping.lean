/-
Static sequence-type analysis shared by XPath and XQuery. The traversal is
independent of evaluation: both conditional branches and function bodies are
checked. Core supplies the sequence types, subtype relation and function catalog.
Exhausted analysis budgets report FOER0000. Expression forms without a rule
still have type item()*; this approximation does not establish whole-language
static-typing completeness.
-/
import L4Factoidal.XPath4.Core
import L4Factoidal.XQueryUpdate.TypeRules

namespace L4Factoidal.XPath4.StaticTyping

structure Ctx where
  vars : List (QN × IType) := []
  focus : IType := .item
  funcs : QN → Nat → Option IType := fun _ _ => none

def top : IType := .seq .item .star

def isTop : IType → Bool
  | .seq .item .star => true
  | _ => false

def itemType : IType → IType
  | .seq t _ => t
  | t => t

def allowsZero : IType → Bool
  | .empty | .seq _ .opt | .seq _ .star => true
  | _ => false

def allowsMany : IType → Bool
  | .seq _ .star | .seq _ .plus => true
  | _ => false

def withOcc (t : IType) (zero many : Bool) : IType :=
  if many then .seq t (if zero then .star else .plus)
  else if zero then .seq t .opt else t

/-- A union of branch types, including the union of their cardinalities. -/
def join (a b : IType) : IType :=
  match a, b with
  | .empty, .empty => .empty
  | .empty, t | t, .empty => withOcc (itemType t) true (allowsMany t)
  | _, _ => withOcc (.choice [itemType a, itemType b])
      (allowsZero a || allowsZero b) (allowsMany a || allowsMany b)

/-- Concatenation sums occurrences rather than taking their union. -/
def concat (a b : IType) : IType :=
  match a, b with
  | .empty, t | t, .empty => t
  | _, _ => withOcc (.choice [itemType a, itemType b])
      (allowsZero a && allowsZero b) true

def optional (t : IType) : IType :=
  match t with
  | .empty => .empty
  | _ => withOcc (itemType t) true (allowsMany t)

def repeated (t : IType) : IType :=
  match t with
  | .empty => .empty
  | _ => .seq (itemType t) .star

/-- Composition of sequence cardinalities for a path or simple map. -/
def composed (src dst : IType) : IType :=
  match src, dst with
  | .empty, _ | _, .empty => .empty
  | _, _ => withOcc (itemType dst) (allowsZero src || allowsZero dst)
      (allowsMany src || allowsMany dst)

def booleanT : IType := .atomic (.b .boolean)
def integerT : IType := .atomic (.b .integer)
def numericT : IType := .choice [.atomic (.b .decimal), .atomic (.b .float), .atomic (.b .double)]

/-- Function conversion for known atomic/node types. Unknown item types are
    admitted so that an unmodelled form cannot manufacture a type error. -/
def convertible : Nat → IType → IType → M Bool
  | 0, _, _ => err "FOER0000" "incomplete static analysis: type conversion budget exhausted"
  | f + 1, a, b =>
    if subtype a b then pure true else
    match a, b with
    | .item, _ => pure true
    | .seq .item .star, _ => pure true
    | .choice ts, _ => ts.allM (fun t => convertible f t b)
    | .seq t o, .seq u p => if occLe o p then convertible f t u else pure false
    | .seq t .one, u => convertible f t u
    | _, .seq u p => if occLe .one p then convertible f a u else pure false
    | .atomic .untyped, .atomic _ => pure true
    | .atomic (.b .anyURI), .atomic (.b .string) => pure true
    | .atomic t, .atomic u => pure (
      (t.derives (.b .decimal) && (u == .b .float || u == .b .double)) ||
      (t == .b .float && u == .b .double))
    | t, .atomic _ => pure (subtype t .anyNode)
    | _, .choice ts => ts.anyM (fun t => convertible f a t)
    | _, _ => pure false

def require (a b : IType) (what : String) : M Unit := do
  if ← convertible 100 a b then pure ()
  else err "XPTY0004" ("static type does not match " ++ what)

/-- Declaration matching retains named PI types, which Core's approximate
    subtype relation does not compare for equality. -/
def declaredSubtype : Nat → IType → IType → M Bool
  | 0, _, _ => err "FOER0000" "incomplete static analysis: subtype budget exhausted"
  | f + 1, a, b =>
    if subtype a b then pure true else
    match a, b with
    | .pi (some x), .pi (some y) => pure (x == y)
    | .seq t o, .seq u p => if occLe o p then declaredSubtype f t u else pure false
    | .seq t .one, u => declaredSubtype f t u
    | t, .seq u p => if occLe .one p then declaredSubtype f t u else pure false
    | .choice ts, u => ts.allM (fun t => declaredSubtype f t u)
    | _, _ => pure false

def bindType (actual declared : IType) : M IType := do
  if isTop declared then return actual
  if !(← declaredSubtype 100 actual declared) && !(← convertible 100 actual declared) then
    err "XPTY0004" "binding expression does not match its declared static type"
  else pure declared

/-- EBV requires homogeneous nodes or at most one EBV-capable atomic value.
    A mixed node/atomic sequence is rejected even when its first item is a node. -/
def checkEBV (t : IType) : M Unit := do
  if isTop t then return ()
  let it := itemType t
  if subtype it .anyNode then return ()
  if allowsMany t then err "FORG0006" "static sequence type has no effective boolean value"
  else if ← convertible 100 t (.seq (.choice [booleanT, numericT, .atomic (.b .string),
      .atomic (.b .anyURI), .atomic .untyped]) .opt) then pure ()
  else err "FORG0006" "static item type has no effective boolean value"

/-- Node-test union nesting has an explicit limit, separate from the
    expression traversal budget. Exhaustion is an error, not acceptance. -/
def testType (ax : Axis) : Nat → NodeTest → M IType
  | 0, _ => err "FOER0000" "static node-test nesting limit"
  | f + 1, .name n | f + 1, .ncname n _ =>
      pure (if ax == .attribute then .attr (some n) else .elem (some n))
  | _ + 1, .kind t => pure t
  | f + 1, .union ts => .choice <$> ts.mapM (testType ax f)

def nodeKind : IType → Nat
  | .elem _ | .elemT .. | .schemaElem _ => 1
  | .attr _ | .attrT .. | .schemaAttr _ => 2
  | .text => 3 | .comment => 4 | .pi _ => 5 | .doc _ => 6 | .nsNode => 7
  | _ => 0

def nameDisjoint : NameTest → NameTest → Bool
  | .name a, .name b => !(a == b)
  | .name a, .ns u | .ns u, .name a => a.uri != u
  | .name a, .loc l | .loc l, .name a => a.loc != l
  | .ns a, .ns b | .loc a, .loc b => a != b
  | _, _ => false

def disjoint (a b : IType) : Bool :=
  if nodeKind a != 0 && nodeKind b != 0 && nodeKind a != nodeKind b then true else
  match a, b with
  | .elem (some x), .elem (some y) | .attr (some x), .attr (some y) => nameDisjoint x y
  | .pi (some x), .pi (some y) => x != y
  | _, _ => false

def emptyStep (focus : IType) (ax : Axis) (out : IType) : Bool :=
  let k := nodeKind focus
  let leaf := k != 0 && k != 1 && k != 6
  match ax with
  | .self => disjoint focus out
  | .descendantOrSelf => leaf && disjoint focus out
  | .child | .descendant => leaf
  | .attribute => k != 0 && k != 1
  | .parent | .ancestor => k == 6
  | _ => false

def fnType (ctx : Ctx) (q : QN) (arity : Nat) : IType :=
  match ctx.funcs q arity with
  | some t => t
  | none => match findSig q arity with
    | some s => .fnT ((s.ps.take arity).map (·.ty)) s.ret
    | none => .anyFn

/-- Primitive atomic families present in a union; unknown node atomization
    and unconstrained items supply no evidence of an incompatibility. -/
def hasAtomicFamily : Nat → IType → String → M Bool
  | 0, _, _ => err "FOER0000" "incomplete static analysis: atomic family budget exhausted"
  | f + 1, .seq t _, family => hasAtomicFamily f t family
  | f + 1, .choice ts, family => ts.anyM (fun t => hasAtomicFamily f t family)
  | _ + 1, .atomic a, family => pure (a.prim == family)
  | _ + 1, _, _ => pure false

/-- A complex mixed annotation can have an element-only restriction. Static
    atomization must therefore account for an absent typed value even when
    a particular dynamic node happens to have mixed content. -/
def checkAtomizable (env : Env) : Nat → IType → M Unit
  | 0, _ => err "FOER0000" "incomplete static analysis: atomization budget exhausted"
  | f + 1, t =>
    match t with
    | .seq t _ => checkAtomizable env f t
    | .choice ts => ts.forM (checkAtomizable env f)
    | .elemT _ ty _ =>
      match env.schema.typeInfo ty with
      | some info =>
        if !info.simple && (info.variety == "mixed" || info.variety == "element-only") then
          err "FOTY0012" "the static element type can have no typed value"
        else pure ()
      | none => pure ()
    | _ => pure ()

def checkFilter : Nat → IType → IType → M Unit
  | 0, _, _ => err "FOER0000" "incomplete static analysis: filter type budget exhausted"
  | f + 1, input, cb =>
    match cb with
    | .choice ts => ts.forM (checkFilter f input)
    | .fnT ps r => do
      if ps.length != 1 && ps.length != 2 then
        err "XPTY0004" "filter predicate requires one or two parameters"
      let inputItem : IType := match input with | .empty => .choice [] | _ => itemType input
      require inputItem (ps.headD .item) "filter predicate argument"
      if ps.length == 2 then require integerT (ps.getD 1 integerT) "filter position argument"
      if !(← declaredSubtype 100 r booleanT) then
        err "XPTY0004" "filter predicate must return exactly one boolean"
    | .item => pure ()
    | _ => err "XPTY0004" "filter predicate must be exactly one function"

/-- Infer an expression's sequence type. The fuel makes nested extension and
    clause traversals total without depending on the evaluator's recursion. -/
def infer : Nat → Env → Ctx → Expr → M IType
  | 0, _, _, _ => err "FOER0000" "incomplete static analysis: expression budget exhausted"
  | fuel + 1, env, ctx, e => do
    let go := infer fuel env
    let all (es : List Expr) (c : Ctx) : M (List IType) := es.mapM (go c)
    match e with
    | .lit a => pure (.atomic a.ty)
    | .seq es => return (← all es ctx).foldl concat .empty
    | .var q => pure ((ctx.vars.find? (·.1 == q)).map (·.2) |>.getD top)
    | .ctx => pure ctx.focus
    | .root => pure (.doc none)
    | .slash a b | .smap a b =>
      let ta ← go ctx a
      let tb ← go { ctx with focus := itemType ta } b
      pure (composed ta tb)
    | .pipe a b =>
      let ta ← go ctx a
      go { ctx with focus := ta } b
    | .step ax nt ps =>
      let out ← testType ax 1000 nt
      if emptyStep (itemType ctx.focus) ax out then
        err "XPST0005" "axis step has the empty static type"
      let _ ← all ps { ctx with focus := out }
      let positional := ps.any (fun p => match p with | .lit a => a.isNumeric | _ => false)
      -- XML attributes with an expanded name are unique on their element.
      let namedAttribute := ax == .attribute && (match nt with
        | .name (.name _) | .ncname (.name _) _ => true | _ => false)
      pure (.seq out (if positional || namedAttribute || ax == .self || ax == .parent then .opt else .star))
    | .dstep _ e ps =>
      let _ ← go ctx e
      let _ ← all ps ctx
      pure (.seq .anyNode .star)
    | .filter a p =>
      let ta ← go ctx a
      let tp ← go { ctx with focus := itemType ta } p
      let positional := match p with | .lit a => a.isNumeric | _ => false
      if positional then pure (.seq (itemType ta) .opt)
      else do checkEBV tp; pure (optional ta)
    | .ifE c a b =>
      checkEBV (← go ctx c)
      let ta ← go ctx a
      let tb ← go ctx b
      pure (join ta tb)
    | .inline ps ret body focus =>
      let c := { ctx with vars := ps ++ ctx.vars }
      let r ← go c body
      let r ← bindType r ret
      pure (.fnT (if focus then [.item] else ps.map (·.2)) r)
    | .fref q n => pure (fnType ctx q n)
    | .call q args kw =>
      let positional ← match q.uri == nsFN && q.loc == "filter", args with
        | true, [some input, some (.inline ps ret body focus)] => do
          let inputT ← go ctx input
          -- Filter supplies one item per invocation, even when its input
          -- sequence is empty or has several items. Specialize unconstrained
          -- inline parameters at this call before inferring its result.
          let inputItem : IType := match inputT with | .empty => .choice [] | _ => itemType inputT
          let ps := ps.zipIdx |>.map (fun ((v,t), i) =>
            (v, if isTop t then (if i == 0 then inputItem else integerT) else t))
          let predT ← go ctx (.inline ps ret body focus)
          pure [inputT, predT]
        | _, _ => args.mapM (fun a => match a with
          | some x => go ctx x | none => pure top)
      let named ← kw.mapM (fun (n, x) => do
        let t ← match x with | some e => go ctx e | none => pure top
        pure (n, t))
      if args.any Option.isNone || kw.any (fun p => p.2.isNone) then return .anyFn
      if q.uri == nsXS then
        match atypeOfName? q.loc with
        | some t => return .seq (.atomic t) .opt
        | none => return top
      if q.uri == nsFN && q.loc == "filter" && positional.length == 2 then
        checkFilter 100 (positional.getD 0 top) (positional.getD 1 top)
        return optional (positional.getD 0 top)
      if q.uri == nsFN && q.loc == "data" then
        checkAtomizable env 100 (positional.headD ctx.focus)
      if q.uri == nsFN && (q.loc == "boolean" || q.loc == "not") then
        checkEBV (positional.headD ctx.focus)
      if q.uri == nsFN && ["avg", "sum", "min", "max"].contains q.loc then
        let t := itemType (positional.headD top)
        if (← hasAtomicFamily 100 t "numeric") && (← hasAtomicFamily 100 t "string") then
          err "FORG0006" "aggregate inputs have incompatible static types"
      match ctx.funcs q (args.length + kw.length) with
      | some (.fnT ps r) =>
        for (t, p) in positional.zip ps do require t p "function parameter"
        return r
      | _ => pure ()
      match findSig q (args.length + kw.length) with
      | none => pure top
      | some s =>
        for (t, p) in positional.zip s.ps do require t p.ty (q.show ++ " parameter " ++ p.name)
        for (n, t) in named do
          if let some p := s.ps.find? (·.name == n) then require t p.ty (q.show ++ " parameter " ++ n)
        if positional.isEmpty && named.isEmpty && q.uri == nsFN && q.loc == "has-children" then
          require ctx.focus (.seq .anyNode .opt) "has-children context"
        -- These F&O parameters are optional by arity, but a supplied encoding
        -- is a required singleton string (the catalog's options union is wider).
        if q.uri == nsFN && ["unparsed-text", "unparsed-text-lines", "unparsed-text-available"].contains q.loc && positional.length == 2 then
          require (positional.getD 1 top) (.choice [.atomic (.b .string), .anyMap]) "text encoding/options"
        pure s.ret
    | .dyn f args =>
      let tf ← go ctx f
      let ts ← all (args.filterMap id) ctx
      match tf with
      | .fnT ps r =>
        for (t, p) in ts.zip ps do require t p "dynamic function parameter"
        pure r
      | _ => pure top
    | .letE v vt a b =>
      let actual ← go ctx a
      let t := if isTop vt then actual else vt
      let r ← go { ctx with vars := (v, t) :: ctx.vars } b
      let _ ← bindType actual vt
      pure r
    | .forE _ v v2 pv vt src body =>
      let ts ← go ctx src
      let t ← bindType (itemType ts) vt
      let vs := (v, t) :: (v2.toList ++ pv.toList).map (fun q => (q, integerT)) ++ ctx.vars
      pure (composed ts (← go { ctx with vars := vs } body))
    | .quant _ v vt src sat =>
      let t ← bindType (itemType (← go ctx src)) vt
      checkEBV (← go { ctx with vars := (v, t) :: ctx.vars } sat)
      pure booleanT
    | .bin op a b =>
      let ta ← go ctx a
      let tb ← go ctx b
      match op with
      | .or | .and => checkEBV ta; checkEBV tb; pure booleanT
      | .add | .sub | .mul | .div | .idiv | .mod =>
        let arithmetic : IType := .seq (.choice [numericT, .atomic (.b .duration),
          .atomic (.b .dateTime), .atomic (.b .date), .atomic (.b .time)]) .opt
        require ta arithmetic "arithmetic operand"
        require tb arithmetic "arithmetic operand"
        if (← convertible 100 ta (.seq numericT .opt)) && (← convertible 100 tb (.seq numericT .opt)) then
          pure (withOcc numericT (allowsZero ta || allowsZero tb) false)
        else pure top
      | .to =>
        require ta (.seq integerT .opt) "range operand"
        require tb (.seq integerT .opt) "range operand"
        pure (.seq integerT .star)
      | .veq | .vne | .vlt | .vle | .vgt | .vge =>
        require ta (.seq (.atomic (.b .anyAtomicType)) .opt) "value comparison operand"
        require tb (.seq (.atomic (.b .anyAtomicType)) .opt) "value comparison operand"
        pure (withOcc booleanT (allowsZero ta || allowsZero tb) false)
      | .concat => pure (.atomic (.b .string))
      | .otherwise => pure (join ta tb)
      | .union | .intersect | .except => pure (.seq .anyNode .star)
      | _ => pure booleanT
    | .neg a | .plus a =>
      let t ← go ctx a
      require t (.seq numericT .opt) "unary numeric operand"
      pure (.seq numericT .opt)
    | .instOf a _ | .castable a _ _ => let _ ← go ctx a; pure booleanT
    | .treat a t => let _ ← go ctx a; pure t
    | .cast a t opt => let _ ← go ctx a; pure (if opt then optional t else t)
    | .mapC es => let _ ← all (es.flatMap (fun (a,b) => [a,b])) ctx; pure .anyMap
    | .arrS es => let _ ← all es ctx; pure .anyArr
    | .arrC a => pure (.arrT (← go ctx a))
    | .lookup a k =>
      let _ ← go ctx a
      let _ ← all k.toList ctx
      pure top
    | .ulookup k => let _ ← all k.toList ctx; pure top
    | .mapArrow a f args =>
      let _ ← go ctx a
      let _ ← go ctx f
      let _ ← all (args.filterMap id) ctx
      pure top
    | .tmpl es => let _ ← all es ctx; pure (.atomic (.b .string))
    | .ext "flwor" es _ _ _ => do
      -- Iterate over clauses. Deferred actions retain the old recursive
      -- unwind order: let validation follows the remainder, and for/where
      -- cardinalities compose from the return expression outward.
      let mut c := ctx
      let mut after : List (IType → M IType) := []
      let mut result := IType.empty
      let count := es.length
      for (cl, i) in es.zipIdx do
        if i + 1 == count then
          result ← go c cl
        else
          match cl with
          | .ext "c:let" [a] [vt] [v] _ =>
            let actual ← go c a
            let t := if isTop vt then actual else vt
            c := { c with vars := (v,t) :: c.vars }
            after := (fun r => do let _ ← bindType actual vt; pure r) :: after
          | .ext "c:for" [src] [vt] [v,pv] _ =>
            let srcT ← go c src
            let t ← bindType (itemType srcT) vt
            c := { c with vars := (v,t) :: (pv,integerT) :: c.vars }
            after := (fun r => pure (composed srcT r)) :: after
          | .ext "c:where" [a] _ _ _ | .ext "c:while" [a] _ _ _ =>
            checkEBV (← go c a)
            after := (fun r => pure (optional r)) :: after
          | .ext "c:count" _ _ [v] _ =>
            c := { c with vars := (v,integerT) :: c.vars }
          | .ext "c:forkv" [src] _ qs _ =>
            let _ ← go c src
            c := { c with vars := qs.map (fun q => (q, top)) ++ c.vars }
            after := (fun r => pure (repeated r)) :: after
          | .ext "c:group" keys _ qs _ =>
            let _ ← all keys c
            c := { c with vars := qs.map (fun q => (q,top)) ++ c.vars }
          | .ext _ as _ _ _ => let _ ← all as c; pure ()
          | other => let _ ← go c other; pure ()
      for finish in after do result ← finish result
      pure result
    | .ext tag es _ _ ss =>
      let ts ← all es ctx
      if tag.startsWith "upd-" then
        L4Factoidal.XQueryUpdate.checkOperandTypes tag ts ss
      match tag with
      | "elem" => pure (.elem none)
      | "attr" => pure (.attr none)
      | "text" => pure (.seq .text .opt)
      | "comment" => pure .comment
      | "pi" => pure (.pi none)
      | "ns" => pure .nsNode
      | "doc" => pure (.doc none)
      | "upd-copy" => pure (ts.headD top)
      | "upd-modify" => pure (ts.getD 1 top)
      | "upd-insert" | "upd-delete" | "upd-replace" | "upd-rename" => pure .empty
      | _ => pure top

def check (env : Env) (e : Expr) : M Unit := do
  let _ ← infer 1000 env { vars := env.staticVars, focus := env.staticFocus } e
  pure ()

end L4Factoidal.XPath4.StaticTyping
