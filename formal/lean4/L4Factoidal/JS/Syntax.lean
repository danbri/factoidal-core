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
      (vars : List String) (usesArgs : Bool) (strict : Bool) (kind : FunKind)

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
instance : Inhabited FunDef := ⟨.mk none [] none [] [] false false .normal⟩
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
def FunDef.strict : FunDef → Bool | .mk _ _ _ _ _ _ s _ => s
def FunDef.kind : FunDef → FunKind | .mk _ _ _ _ _ _ _ k => k
def FunDef.arrow (f : FunDef) : Bool := f.kind == .arrow
def FunDef.withName (f : FunDef) (n : String) : FunDef :=
  match f with | .mk _ p r b v u s k => .mk (some n) p r b v u s k

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
