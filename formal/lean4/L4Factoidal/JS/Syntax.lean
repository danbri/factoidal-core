/-!
# L4Factoidal.JS.Syntax — abstract syntax of the ECMAScript core subset

Record: `docs/designissues/2026-11-08-lean-js-engine.md`.

The node names follow the ECMA-262 grammar (§13 expressions, §14 statements,
§15 functions). A function literal carries what the parser found about its body
(`FunDef`): the `var` names to hoist (§10.2.11 FunctionDeclarationInstantiation,
step 27), whether the body names `arguments`, and the strictness of its code
(§11.2.2). The evaluator does not walk a body again to find them.
-/

namespace L4Factoidal.JS

/-- Binary operators (§13.6 to §13.12). -/
inductive BinOp where
  | add | sub | mul | div | mod | exp
  | shl | sar | shr
  | lt | gt | le | ge | instanceof | inOp
  | eq | ne | seq | sne
  | band | bor | bxor
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Short-circuit operators (§13.13). -/
inductive LogOp where
  | and | or | coalesce
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Unary operators (§13.5). -/
inductive UnOp where
  | neg | plus | not | bnot | typeof | void | delete
  deriving BEq, Repr, Inhabited, DecidableEq

/-- `let`, `const` or `var`. -/
inductive DeclKind where
  | var | letK | constK
  deriving BEq, Repr, Inhabited, DecidableEq

/-- What kind of function a function literal makes (§10.2: `[[ThisMode]]`,
`[[ConstructorKind]]`, and whether it has `[[HomeObject]]`). -/
inductive FunKind where
  | normal | arrow | method
  /-- A class constructor; `derived` when the class has `extends`. -/
  | ctor (derived : Bool)
  deriving BEq, Repr, Inhabited, DecidableEq

/-- Members of a class body (§15.7). -/
inductive MemberKind where
  | method | getter | setter | field
  deriving BEq, Repr, Inhabited, DecidableEq

mutual
/-- Expressions. -/
inductive Expr where
  | num (n : Float)
  | str (s : String)
  | bool (b : Bool)
  | null
  | ident (name : String)
  | this
  | array (elems : List Expr)
  | object (props : List PropDef)
  | func (f : FunDef)
  | unary (op : UnOp) (e : Expr)
  | binary (op : BinOp) (a b : Expr)
  | logical (op : LogOp) (a b : Expr)
  /-- `a = b` when `op` is `none`, else `a op= b`. -/
  | assign (op : Option BinOp) (target value : Expr)
  /-- `a &&= b`, `a ||= b`, `a ??= b`. -/
  | logAssign (op : LogOp) (target value : Expr)
  /-- Destructuring assignment `[a, b] = e`, `({a} = e)` (§13.15.5). -/
  | assignPat (p : Pat) (value : Expr)
  | update (pre inc : Bool) (target : Expr)
  | cond (c t e : Expr)
  | call (callee : Expr) (args : List Expr)
  | new (callee : Expr) (args : List Expr)
  /-- `o.name` -/
  | member (obj : Expr) (name : String)
  /-- `o[key]` -/
  | index (obj key : Expr)
  | seq (a b : Expr)
  /-- `...e` in an array literal or an argument list. -/
  | spread (e : Expr)
  /-- A template literal: the cooked strings and the substitutions between them. -/
  | template (cooked : List String) (subs : List Expr)
  /-- A tagged template: the tag, the cooked and raw strings, the substitutions. -/
  | tagged (tag : Expr) (cooked raw : List String) (subs : List Expr)
  | classE (c : ClassDef)
  | superCall (args : List Expr)
  | superMember (name : String)
  | superIndex (key : Expr)
  | newTarget
  /-- `yield e`, `yield* e` (§15.5). -/
  | yieldE (delegate : Bool) (arg : Option Expr)

/-- A property definition in an object literal (§13.2.5). -/
inductive PropDef where
  | init (key : PropKey) (value : Expr)
  | getter (key : PropKey) (f : FunDef)
  | setter (key : PropKey) (f : FunDef)
  | spread (e : Expr)

/-- A literal property name, or a computed one. -/
inductive PropKey where
  | lit (s : String)
  | computed (e : Expr)

/-- A binding or assignment pattern (§14.3.3, §13.15.5). -/
inductive Pat where
  | id (name : String)
  /-- An assignment target that is not a name (`o.x`, `o[k]`), in assignment patterns. -/
  | target (e : Expr)
  | obj (props : List PatProp) (rest : Option Pat)
  | arr (elems : List (Option PatElem)) (rest : Option Pat)

inductive PatProp where
  | mk (key : PropKey) (value : Pat) (dflt : Option Expr)

inductive PatElem where
  | mk (p : Pat) (dflt : Option Expr)

/-- A function literal: declaration, expression, arrow, method, accessor or class
constructor. `params` are patterns with initialisers; `rest` is `...p`. -/
inductive FunDef where
  | mk (name : Option String) (params : List PatElem) (rest : Option Pat) (body : List Stmt)
      (vars : List String) (usesArgs : Bool) (strict : Bool) (kind : FunKind) (gen : Bool)

/-- A class (§15.7): name, heritage, constructor, members. A field is a member whose
function returns the initial value. -/
inductive ClassDef where
  | mk (name : Option String) (heritage : Option Expr) (ctor : Option FunDef)
      (members : List Member)

inductive Member where
  | mk (static : Bool) (kind : MemberKind) (key : PropKey) (f : FunDef)

/-- The `case` clauses of a `switch`; `none` is `default`. -/
inductive Case where
  | mk (test : Option Expr) (body : List Stmt)

/-- What a `for` statement starts with. -/
inductive ForInit where
  | decl (kind : DeclKind) (decls : List Decl)
  | expr (e : Expr)

/-- One declarator: `p = e`. -/
inductive Decl where
  | mk (target : Pat) (init : Option Expr)

/-- Statements. -/
inductive Stmt where
  | expr (e : Expr)
  | decl (kind : DeclKind) (decls : List Decl)
  | funDecl (name : String) (f : FunDef)
  | classDecl (name : String) (c : ClassDef)
  | ret (e : Option Expr)
  | ifS (c : Expr) (t : Stmt) (e : Option Stmt)
  | whileS (c : Expr) (body : Stmt)
  | doWhile (body : Stmt) (c : Expr)
  | forS (init : Option ForInit) (test update : Option Expr) (body : Stmt)
  /-- `for (p in o)` / `for (p of o)`: the binding kind (`none`: assignment) and pattern. -/
  | forIn (kind : Option DeclKind) (target : Pat) (obj : Expr) (body : Stmt)
  | forOf (kind : Option DeclKind) (target : Pat) (obj : Expr) (body : Stmt)
  | block (body : List Stmt)
  | throwS (e : Expr)
  | tryS (body : List Stmt) (param : Option Pat) (handler : Option (List Stmt))
      (finalizer : Option (List Stmt))
  | brk (label : Option String)
  | cont (label : Option String)
  | labeled (label : String) (body : Stmt)
  | switchS (disc : Expr) (cases : List Case)
  | empty
end

instance : Inhabited Expr := ⟨.null⟩
instance : Inhabited FunDef := ⟨.mk none [] none [] [] false false .normal false⟩
instance : Inhabited Stmt := ⟨.empty⟩
instance : Inhabited PropDef := ⟨.init (.lit "") .null⟩
instance : Inhabited PropKey := ⟨.lit ""⟩
instance : Inhabited Case := ⟨.mk none []⟩
instance : Inhabited Pat := ⟨.id ""⟩
instance : Inhabited Decl := ⟨.mk (.id "") none⟩
instance : Inhabited ForInit := ⟨.expr .null⟩
instance : Inhabited ClassDef := ⟨.mk none none none []⟩

def FunDef.name : FunDef → Option String | .mk n .. => n
def FunDef.params : FunDef → List PatElem | .mk _ p .. => p
def FunDef.rest : FunDef → Option Pat | .mk _ _ r .. => r
def FunDef.body : FunDef → List Stmt | .mk _ _ _ b .. => b
def FunDef.vars : FunDef → List String | .mk _ _ _ _ v .. => v
def FunDef.usesArgs : FunDef → Bool | .mk _ _ _ _ _ u .. => u
def FunDef.strict : FunDef → Bool | .mk _ _ _ _ _ _ s _ _ => s
def FunDef.kind : FunDef → FunKind | .mk _ _ _ _ _ _ _ k _ => k
def FunDef.gen : FunDef → Bool | .mk _ _ _ _ _ _ _ _ g => g
def FunDef.arrow (f : FunDef) : Bool := f.kind == .arrow
def FunDef.withName (f : FunDef) (n : String) : FunDef :=
  match f with | .mk _ p r b v u s k g => .mk (some n) p r b v u s k g

/-- The `length` of a function: parameters before the first initialiser or rest (§15.1.5). -/
def FunDef.expectedArgs (f : FunDef) : Nat :=
  (f.params.takeWhile fun p => match p with | .mk _ none => true | .mk _ (some _) => false).length

mutual
/-- The names a pattern binds (§8.2.1 BoundNames). -/
def Pat.names : Pat → List String
  | .id x => [x]
  | .target _ => []
  | .obj ps r => Pat.propNames ps ++ Pat.restNames r
  | .arr es r => Pat.elemNames es ++ Pat.restNames r

def Pat.propNames : List PatProp → List String
  | [] => []
  | .mk _ v _ :: rest => v.names ++ Pat.propNames rest

def Pat.elemNames : List (Option PatElem) → List String
  | [] => []
  | none :: rest => Pat.elemNames rest
  | some (.mk p _) :: rest => p.names ++ Pat.elemNames rest

def Pat.restNames : Option Pat → List String
  | some p => p.names
  | none => []
end

def Decl.names : Decl → List String | .mk p _ => p.names

/-- A pattern that is a single name. -/
def Pat.name? : Pat → Option String
  | .id x => some x
  | _ => none

/-- A script: its statements, its `var` and top-level function names, strictness. -/
structure Script where
  body : List Stmt
  vars : List String
  strict : Bool
  deriving Inhabited

end L4Factoidal.JS

namespace L4Factoidal.JS
mutual
/-- The expression holds a `yield` outside nested functions. `fuel` bounds the
walk (out of fuel answers `true`, the safe side). -/
def Expr.hasYieldF : Nat → Expr → Bool
  | 0, _ => true
  | n + 1, e =>
    match e with
    | .yieldE .. => true
    | .num _ | .str _ | .bool _ | .null | .ident _ | .this | .newTarget | .superMember _
    | .func _ | .classE _ => false
    | .array es | .template _ es | .superCall es | .tagged _ _ _ es => Expr.anyYield n es
    | .object ps => PropDef.anyYield n ps
    | .unary _ a | .update _ _ a | .spread a | .superIndex a | .member a _ => Expr.hasYieldF n a
    | .binary _ a b | .logical _ a b | .assign _ a b | .logAssign _ a b | .index a b | .seq a b =>
      Expr.hasYieldF n a || Expr.hasYieldF n b
    | .assignPat _ v => Expr.hasYieldF n v
    | .cond a b c => Expr.hasYieldF n a || Expr.hasYieldF n b || Expr.hasYieldF n c
    | .call f args | .new f args => Expr.hasYieldF n f || Expr.anyYield n args

def Expr.anyYield : Nat → List Expr → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, e :: es => Expr.hasYieldF n e || Expr.anyYield n es

def PropDef.anyYield : Nat → List PropDef → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, p :: ps =>
    (match p with
      | .init (.computed k) v => Expr.hasYieldF n k || Expr.hasYieldF n v
      | .init _ v => Expr.hasYieldF n v
      | .spread e => Expr.hasYieldF n e
      | .getter (.computed k) _ | .setter (.computed k) _ => Expr.hasYieldF n k
      | _ => false) || PropDef.anyYield n ps

def Stmt.hasYieldF : Nat → Stmt → Bool
  | 0, _ => true
  | n + 1, s =>
    match s with
    | .expr e | .throwS e => Expr.hasYieldF n e
    | .decl _ ds => Decl.anyYield n ds
    | .funDecl .. | .classDecl .. | .brk _ | .cont _ | .empty | .ret none => false
    | .ret (some e) => Expr.hasYieldF n e
    | .ifS c t e => Expr.hasYieldF n c || Stmt.hasYieldF n t ||
        (match e with | some e => Stmt.hasYieldF n e | none => false)
    | .whileS c b | .doWhile b c => Expr.hasYieldF n c || Stmt.hasYieldF n b
    | .forS i t u b =>
      (match i with
        | some (.expr e) => Expr.hasYieldF n e
        | some (.decl _ ds) => Decl.anyYield n ds
        | none => false) ||
      (match t with | some e => Expr.hasYieldF n e | none => false) ||
      (match u with | some e => Expr.hasYieldF n e | none => false) || Stmt.hasYieldF n b
    | .forIn _ _ o b | .forOf _ _ o b => Expr.hasYieldF n o || Stmt.hasYieldF n b
    | .block ss => Stmt.anyYield n ss
    | .tryS b _ h f => Stmt.anyYield n b ||
        (match h with | some h => Stmt.anyYield n h | none => false) ||
        (match f with | some f => Stmt.anyYield n f | none => false)
    | .labeled _ b => Stmt.hasYieldF n b
    | .switchS d cs => Expr.hasYieldF n d || Case.anyYield n cs

def Stmt.anyYield : Nat → List Stmt → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, s :: ss => Stmt.hasYieldF n s || Stmt.anyYield n ss

def Decl.anyYield : Nat → List Decl → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, (.mk _ i) :: ds =>
    (match i with | some e => Expr.hasYieldF n e | none => false) || Decl.anyYield n ds

def Case.anyYield : Nat → List Case → Bool
  | 0, _ => true
  | _ + 1, [] => false
  | n + 1, (.mk t b) :: cs =>
    (match t with | some e => Expr.hasYieldF n e | none => false) || Stmt.anyYield n b ||
      Case.anyYield n cs
end

def Expr.hasYield (e : Expr) : Bool := Expr.hasYieldF 100000 e
def Stmt.hasYield (s : Stmt) : Bool := Stmt.hasYieldF 100000 s
def Decl.hasYield (d : Decl) : Bool := Decl.anyYield 100000 [d]

end L4Factoidal.JS
