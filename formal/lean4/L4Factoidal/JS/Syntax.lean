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
  | update (pre inc : Bool) (target : Expr)
  | cond (c t e : Expr)
  | call (callee : Expr) (args : List Expr)
  | new (callee : Expr) (args : List Expr)
  /-- `o.name` -/
  | member (obj : Expr) (name : String)
  /-- `o[key]` -/
  | index (obj key : Expr)
  | seq (a b : Expr)

/-- A property definition in an object literal (§13.2.5). -/
inductive PropDef where
  | init (key : PropKey) (value : Expr)
  | getter (key : PropKey) (f : FunDef)
  | setter (key : PropKey) (f : FunDef)

/-- A literal property name, or a computed one. -/
inductive PropKey where
  | lit (s : String)
  | computed (e : Expr)

/-- A function literal: declaration, expression, arrow, method or accessor. -/
inductive FunDef where
  | mk (name : Option String) (params : List String) (body : List Stmt)
      (vars : List String) (usesArgs : Bool) (strict : Bool) (arrow : Bool)

/-- The `case` clauses of a `switch`; `none` is `default`. -/
inductive Case where
  | mk (test : Option Expr) (body : List Stmt)

/-- What a `for` statement starts with. -/
inductive ForInit where
  | decl (kind : DeclKind) (decls : List Decl)
  | expr (e : Expr)

/-- One declarator: `x = e`. -/
inductive Decl where
  | mk (name : String) (init : Option Expr)

/-- Statements. -/
inductive Stmt where
  | expr (e : Expr)
  | decl (kind : DeclKind) (decls : List Decl)
  | funDecl (name : String) (f : FunDef)
  | ret (e : Option Expr)
  | ifS (c : Expr) (t : Stmt) (e : Option Stmt)
  | whileS (c : Expr) (body : Stmt)
  | doWhile (body : Stmt) (c : Expr)
  | forS (init : Option ForInit) (test update : Option Expr) (body : Stmt)
  /-- `for (x in o)`: the binding kind (`none`: an assignment target) and name. -/
  | forIn (kind : Option DeclKind) (target : Expr) (obj : Expr) (body : Stmt)
  | block (body : List Stmt)
  | throwS (e : Expr)
  | tryS (body : List Stmt) (param : Option String) (handler : Option (List Stmt))
      (finalizer : Option (List Stmt))
  | brk (label : Option String)
  | cont (label : Option String)
  | labeled (label : String) (body : Stmt)
  | switchS (disc : Expr) (cases : List Case)
  | empty
end

instance : Inhabited Expr := ⟨.null⟩
instance : Inhabited FunDef := ⟨.mk none [] [] [] false false false⟩
instance : Inhabited Stmt := ⟨.empty⟩
instance : Inhabited PropDef := ⟨.init (.lit "") .null⟩
instance : Inhabited PropKey := ⟨.lit ""⟩
instance : Inhabited Case := ⟨.mk none []⟩
instance : Inhabited Decl := ⟨.mk "" none⟩
instance : Inhabited ForInit := ⟨.expr .null⟩

def FunDef.name : FunDef → Option String | .mk n .. => n
def FunDef.params : FunDef → List String | .mk _ p .. => p
def FunDef.body : FunDef → List Stmt | .mk _ _ b .. => b
def FunDef.vars : FunDef → List String | .mk _ _ _ v .. => v
def FunDef.usesArgs : FunDef → Bool | .mk _ _ _ _ u .. => u
def FunDef.strict : FunDef → Bool | .mk _ _ _ _ _ s _ => s
def FunDef.arrow : FunDef → Bool | .mk _ _ _ _ _ _ a => a

/-- A script: its statements, its `var` and top-level function names, strictness. -/
structure Script where
  body : List Stmt
  vars : List String
  strict : Bool
  deriving Inhabited

end L4Factoidal.JS
