/-
L4Factoidal.XPath4.ExprEq — the static form of a function item (F&O 4.0
§1.5.1, "equivalent" function items, PR 2805): structural equality of
expressions (`BEq Expr`), renaming of bound variables, and the variables
that a body reads.

Two inline function items have the same static form when their bodies are
equal after the parameters of both are renamed to the same names
(`Expr.alphaEq`). The evaluator compares the captured values of the
variables that the bodies read (`Expr.varsRead`) with `deep-equal`.
-/
import L4Factoidal.XPath4.Syntax

namespace L4Factoidal.XPath4

/-- Atomic items of a static form (literals) are equal when they have the
    same type and the same lexical form. -/
instance : BEq Atomic := ⟨fun a b => a.ty == b.ty && a.str == b.str⟩

deriving instance BEq for NameTest
deriving instance BEq for JKeyTest
deriving instance BEq for IType
deriving instance BEq for NodeTest
deriving instance BEq for Expr

/-- Rename every occurrence of the variable names that `r` maps (variable
    references and binders). With fresh target names this keeps the
    meaning of the expression. Constructs not listed are kept as they are
    (the comparison is then stricter, never wrong). -/
def Expr.renameF (r : QN → QN) : Nat → Expr → Expr
  | 0, e => e
  | f + 1, e =>
    let go := Expr.renameF r f
    let goO (o : Option Expr) : Option Expr := o.map go
    match e with
    | .var q => .var (r q)
    | .seq es => .seq (es.map go)
    | .slash a b => .slash (go a) (go b)
    | .step ax t ps => .step ax t (ps.map go)
    | .dstep ax x ps => .dstep ax (go x) (ps.map go)
    | .filter a p => .filter (go a) (go p)
    | .call q args kw => .call q (args.map goO) (kw.map (fun (k, a) => (k, goO a)))
    | .dyn g args => .dyn (go g) (args.map goO)
    | .inline ps ret body focus => .inline (ps.map (fun (q, t) => (r q, t))) ret (go body) focus
    | .mapC es => .mapC (es.map (fun (k, v) => (go k, go v)))
    | .arrS es => .arrS (es.map go)
    | .arrC x => .arrC (go x)
    | .lookup x k => .lookup (go x) (goO k)
    | .ulookup k => .ulookup (goO k)
    | .bin op a b => .bin op (go a) (go b)
    | .neg x => .neg (go x)
    | .plus x => .plus (go x)
    | .ifE c t el => .ifE (go c) (go t) (go el)
    | .forE k v v2 pv vt src body => .forE k (r v) (v2.map r) (pv.map r) vt (go src) (go body)
    | .letE v vt x body => .letE (r v) vt (go x) (go body)
    | .quant ev v vt src sat => .quant ev (r v) vt (go src) (go sat)
    | .instOf x t => .instOf (go x) t
    | .treat x t => .treat (go x) t
    | .cast x t o => .cast (go x) t o
    | .castable x t o => .castable (go x) t o
    | .smap a b => .smap (go a) (go b)
    | .pipe a b => .pipe (go a) (go b)
    | .mapArrow a g args => .mapArrow (go a) (go g) (args.map goO)
    | .tmpl parts => .tmpl (parts.map go)
    | other => other

def Expr.rename (r : QN → QN) (e : Expr) : Expr := e.renameF r 100000

/-- The variable names an expression reads (an over-approximation: a
    name bound inside the expression is also listed). -/
def Expr.varsReadF : Nat → Expr → List QN
  | 0, _ => []
  | f + 1, e =>
    let go := Expr.varsReadF f
    let goL (es : List Expr) : List QN := es.flatMap go
    let goO (o : Option Expr) : List QN := match o with | some x => go x | none => []
    match e with
    | .var q => [q]
    | .seq es | .arrS es | .tmpl es => goL es
    | .slash a b | .filter a b | .bin _ a b | .smap a b | .pipe a b => go a ++ go b
    | .step _ _ ps => goL ps
    | .dstep _ x ps => go x ++ goL ps
    | .call _ args kw => args.flatMap goO ++ kw.flatMap (fun (_, a) => goO a)
    | .dyn g args => go g ++ args.flatMap goO
    | .inline _ _ body _ => go body
    | .mapC es => es.flatMap (fun (k, v) => go k ++ go v)
    | .arrC x | .neg x | .plus x | .instOf x _ | .treat x _ | .cast x _ _ | .castable x _ _ => go x
    | .lookup x k => go x ++ goO k
    | .ulookup k => goO k
    | .ifE c t el => go c ++ go t ++ go el
    | .forE _ _ _ _ _ src body | .letE _ _ src body | .quant _ _ _ src body => go src ++ go body
    | .mapArrow a g args => go a ++ go g ++ args.flatMap goO
    | _ => []

def Expr.varsRead (e : Expr) : List QN := (Expr.varsReadF 100000 e).eraseDups

/-- The static function calls of an expression: the name and the number
    of arguments (positional and keyword). -/
def Expr.callsF : Nat → Expr → List (QN × Nat)
  | 0, _ => []
  | f + 1, e =>
    let go := Expr.callsF f
    let goL (es : List Expr) : List (QN × Nat) := es.flatMap go
    let goO (o : Option Expr) : List (QN × Nat) := match o with | some x => go x | none => []
    match e with
    | .call q args kw => (q, args.length + (kw.filter (·.1 != "#at")).length) :: (args.flatMap goO ++ kw.flatMap (fun (_, a) => goO a))
    | .seq es | .arrS es | .tmpl es => goL es
    | .slash a b | .filter a b | .bin _ a b | .smap a b | .pipe a b => go a ++ go b
    | .step _ _ ps => goL ps
    | .dstep _ x ps => go x ++ goL ps
    | .dyn g args => go g ++ args.flatMap goO
    | .inline _ _ body _ => go body
    | .mapC es => es.flatMap (fun (k, v) => go k ++ go v)
    | .arrC x | .neg x | .plus x | .instOf x _ | .treat x _ | .cast x _ _ | .castable x _ _ => go x
    | .lookup x k => go x ++ goO k
    | .ulookup k => goO k
    | .ifE c t el => go c ++ go t ++ go el
    | .forE _ _ _ _ _ src body | .letE _ _ src body | .quant _ _ _ src body => go src ++ go body
    | .mapArrow a g args => go a ++ go g ++ args.flatMap goO
    | _ => []

/-- The variable names of an expression in first-occurrence order:
    references and binders (inline parameters, for, let and quantified
    variables), so two expressions of one shape list them in step. -/
def Expr.namesF : Nat → Expr → List QN
  | 0, _ => []
  | f + 1, e =>
    let go := Expr.namesF f
    let goL (es : List Expr) : List QN := es.flatMap go
    let goO (o : Option Expr) : List QN := match o with | some x => go x | none => []
    match e with
    | .var q => [q]
    | .seq es | .arrS es | .tmpl es => goL es
    | .slash a b | .filter a b | .bin _ a b | .smap a b | .pipe a b => go a ++ go b
    | .step _ _ ps => goL ps
    | .dstep _ x ps => go x ++ goL ps
    | .call _ args kw => args.flatMap goO ++ kw.flatMap (fun (_, a) => goO a)
    | .dyn g args => go g ++ args.flatMap goO
    | .inline ps _ body _ => ps.map (·.1) ++ go body
    | .mapC es => es.flatMap (fun (k, v) => go k ++ go v)
    | .arrC x | .neg x | .plus x | .instOf x _ | .treat x _ | .cast x _ _ | .castable x _ _ => go x
    | .lookup x k => go x ++ goO k
    | .ulookup k => goO k
    | .ifE c t el => go c ++ go t ++ go el
    | .forE _ v v2 pv _ src body =>
        go src ++ [v] ++ v2.toList ++ pv.toList ++ go body
    | .letE v _ src body => go src ++ [v] ++ go body
    | .quant _ v _ src body => go src ++ [v] ++ go body
    | .mapArrow a g args => go a ++ go g ++ args.flatMap goO
    | _ => []

/-- The canonical name of the `i`-th parameter (not a name the parser
    makes: its namespace is `#alpha`). -/
def alphaName (i : Nat) : QN := { uri := "#alpha", loc := toString i }

/-- Map each parameter name to its canonical name. -/
def alphaRenaming (ps : List QN) (q : QN) : QN :=
  match (ps.zip (List.range ps.length)).find? (fun (p, _) => p == q) with
  | some (_, i) => alphaName i
  | none => q

/-- The names of an inline function in canonical order: the parameters,
    then every other name of the body in first-occurrence order. -/
def inlineNames (ps : List (QN × IType)) (b : Expr) : List QN :=
  (ps.map (·.1) ++ Expr.namesF 100000 b).eraseDups

/-- Same static form of two inline functions: the same number of
    parameters with the same types, the same result type, and bodies
    equal when the names of both are replaced, in canonical order, by
    the same names. The result pairs the names the bodies read and do
    not bind as parameters (the captured variables to compare). -/
def inlineAlphaEq? (ps1 : List (QN × IType)) (r1 : IType) (b1 : Expr)
    (ps2 : List (QN × IType)) (r2 : IType) (b2 : Expr) : Option (List (QN × QN)) :=
  let n1 := inlineNames ps1 b1
  let n2 := inlineNames ps2 b2
  if ps1.length == ps2.length && n1.length == n2.length && (ps1.map (·.2)) == (ps2.map (·.2)) && r1 == r2 &&
      b1.rename (alphaRenaming n1) == b2.rename (alphaRenaming n2) then
    some ((n1.zip n2).drop ps1.length)
  else none

def inlineAlphaEq (ps1 : List (QN × IType)) (r1 : IType) (b1 : Expr)
    (ps2 : List (QN × IType)) (r2 : IType) (b2 : Expr) : Bool :=
  (inlineAlphaEq? ps1 r1 b1 ps2 r2 b2).isSome

/-- Renaming with no names to rename changes nothing. -/
theorem alphaRenaming_nil (q : QN) : alphaRenaming [] q = q := by
  simp [alphaRenaming]

#guard inlineAlphaEq [({ uri := "", loc := "x" }, .item)] .item (.var { uri := "", loc := "x" })
  [({ uri := "", loc := "y" }, .item)] .item (.var { uri := "", loc := "y" })
#guard !inlineAlphaEq [({ uri := "", loc := "x" }, .item)] .item (.var { uri := "", loc := "x" })
  [({ uri := "", loc := "y" }, .item)] .item (.var { uri := "", loc := "z" })

end L4Factoidal.XPath4
