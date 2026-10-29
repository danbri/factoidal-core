/-
L4Factoidal.XQuery4.Static — the static checks of XQuery 4.0 §2.2.5
that do not need types: every variable reference is to a variable in
scope (XPST0008), and every static function call names a known
function (XPST0017). They are static errors, so they are raised before
evaluation and a `try` around the reference does not catch them.

The walk is total by a fuel argument; when the fuel runs out the walk
reports nothing (the dynamic checks of the evaluator remain).
-/
import L4Factoidal.XQuery4.Grammar
import L4Factoidal.XPath4.Ext

namespace L4Factoidal.XQuery4

open L4Factoidal.XPath4

/-- The static context of the walk: variables in scope, and a test for
    known function names. -/
structure SCtx where
  vars : List QN
  knownFn : QN → Nat → Bool
  /-- Is a type name among the in-scope schema types (§2.2.5, XPST0008)? -/
  typeKnown : QN → Bool := fun _ => true
  /-- The in-scope element and attribute declarations. -/
  elemKnown : QN → Bool := fun _ => true
  attrKnown : QN → Bool := fun _ => true

def SCtx.add (c : SCtx) (qs : List QN) : SCtx :=
  { c with vars := qs.filter (fun q => !isNoName q) ++ c.vars }

def errVarNames : List QN :=
  ["code", "description", "value", "module", "line-number", "column-number", "additional",
   "stack-trace", "map"].map (fun l => { uri := nsERR, loc := l })

/-- A type or declaration name of a sequence type that is not in the
    in-scope schema definitions is XPST0008 (§2.2.5.1). -/
def typeStaticErr (c : SCtx) : Nat → IType → Option Err
  | 0, _ => none
  | f + 1, t =>
    match t with
    | .elemT _ ty _ | .attrT _ ty =>
      if c.typeKnown ty then none
      else some { code := "XPST0008", msg := "unknown schema type " ++ ty.show }
    | .schemaElem q =>
      if c.elemKnown q then none
      else some { code := "XPST0008", msg := "no element declaration " ++ q.show }
    | .schemaAttr q =>
      if c.attrKnown q then none
      else some { code := "XPST0008", msg := "no attribute declaration " ++ q.show }
    | .doc (some t') => typeStaticErr c f t'
    | .seq t' _ => typeStaticErr c f t'
    | _ => none

def nodeTestStaticErr (c : SCtx) : Nat → NodeTest → Option Err
  | 0, _ => none
  | f + 1, nt =>
    match nt with
    | .kind t => typeStaticErr c 8 t
    | .union ts => ts.foldl (fun acc x => acc <|> nodeTestStaticErr c f x) none
    | _ => none

/-- The first static error in `e`, if any. -/
def staticErr : Nat → SCtx → Expr → Option Err
  | 0, _, _ => none
  | f + 1, c, ex =>
    let go := staticErr f
    let all (es : List Expr) (c : SCtx) : Option Err :=
      es.foldl (fun acc x => acc <|> go c x) none
    match ex with
    | .lit _ | .ctx | .root | .ulookup none => none
    | .var q =>
      if c.vars.any (· == q) then none
      else some { code := "XPST0008", msg := "undeclared variable $" ++ q.show }
    | .seq es => all es c
    | .slash a b => go c a <|> go c b
    | .step _ nt ps => nodeTestStaticErr c 8 nt <|> all ps c
    | .dstep _ e ps => go c e <|> all ps c
    | .filter a p => go c a <|> go c p
    | .call q args kw =>
      let k := args.length + kw.length
      let here : Option Err :=
        if q.uri == nsXS || q.uri.startsWith "#" || c.knownFn q k then none
        else some { code := "XPST0017", msg := "unknown function " ++ q.show ++ "#" ++ toString k }
      here <|> all (args.filterMap id) c <|> all (kw.filterMap (·.2)) c
    | .dyn g args => go c g <|> all (args.filterMap id) c
    | .fref q k =>
      -- a named function reference names a function in scope (XPST0017)
      if q.uri == nsXS || q.uri.startsWith "#" || c.knownFn q k then none
      else some { code := "XPST0017", msg := "unknown function " ++ q.show ++ "#" ++ toString k }
    | .inline ps _ body _ => go (c.add (ps.map (·.1))) body
    | .mapC es => all (es.flatMap (fun (a, b) => [a, b])) c
    | .arrS es => all es c
    | .arrC e => go c e
    | .lookup e k => go c e <|> (match k with | some x => go c x | none => none)
    | .ulookup (some k) => go c k
    | .bin _ a b => go c a <|> go c b
    | .neg e | .plus e => go c e
    | .ifE a b d => go c a <|> go c b <|> go c d
    | .forE _ v v2 pv _ src body =>
      go c src <|> go (c.add ([v] ++ v2.toList ++ pv.toList)) body
    | .letE v _ e body => go c e <|> go (c.add [v]) body
    | .quant _ v _ src sat => go c src <|> go (c.add [v]) sat
    | .instOf e t | .treat e t => typeStaticErr c 8 t <|> go c e
    | .cast e _ _ | .castable e _ _ => go c e
    | .smap a b | .pipe a b => go c a <|> go c b
    | .mapArrow a g args => go c a <|> go c g <|> all (args.filterMap id) c
    | .tmpl ps => all ps c
    | .ext "flwor" es _ _ _ =>
      -- clauses in order, each in the scope the earlier ones made
      let rec clauses : List Expr → SCtx → Option Err
        | [], _ => none
        | [ret], c => go c ret
        | cl :: rest, c =>
          match cl with
          | .ext "c:for" [src] _ [v, pv] _ => go c src <|> clauses rest (c.add [v, pv])
          | .ext "c:forkv" [src] _ qs _ => go c src <|> clauses rest (c.add qs)
          | .ext "c:let" [e] _ [v] _ => go c e <|> clauses rest (c.add [v])
          | .ext "c:count" _ _ [v] _ => clauses rest (c.add [v])
          | .ext "c:group" keys _ vs _ => all keys c <|> clauses rest (c.add vs)
          | .ext "c:window" (src :: sc :: ec) _ (v :: qs) _ =>
            let sv := qs.take 4
            go c src <|> go (c.add sv) sc <|> all ec (c.add qs) <|> clauses rest (c.add (v :: qs))
          | .ext _ es' _ _ _ => all es' c <|> clauses rest c
          | other => go c other <|> clauses rest c
      clauses es c
    | .ext "typeswitch" (op :: rets) _ qs _ =>
      go c op <|> (rets.zip (List.range rets.length)).foldl (fun acc (r, i) =>
        acc <|> go (c.add [qs.getD i noName]) r) none
    | .ext "try" (body :: hs) _ _ ss =>
      let ncatch := (ss.filter (· != "#finally")).length
      go c body <|> all (hs.take ncatch) (c.add errVarNames) <|> all (hs.drop ncatch) c
    | .ext _ es _ _ _ => all es c

end L4Factoidal.XQuery4
