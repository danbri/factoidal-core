/-
L4Factoidal.XQueryUpdate.Grammar — the expression productions of the
XQuery Update Facility 3.0 (https://www.w3.org/TR/xquery-update-30/,
Appendix A, productions [199] to [208]) on top of the XQuery 4.0
grammar extension (`XQuery4.Grammar.grammar`).

`grammarU cfg` is an `XPath4.ExtGrammar`: at every ExprSingle it tries

* `insert (node|nodes) SourceExpr ((as (first|last))? into | after | before) TargetExpr`,
* `delete (node|nodes) TargetExpr`,
* `replace (value of)? node TargetExpr with ExprSingle`,
* `rename node TargetExpr as NewNameExpr`,
* `copy $v := ExprSingle (, $v := ExprSingle)* modify ExprSingle return ExprSingle`,
* `invoke updating PrimaryExpr ( args )`,

then the XQuery 4.0 productions. A keyword starts an update expression
only when the next word is the one the production needs (`insert node`,
`replace value`, `copy $`), so a path step named `insert` or a call of
`fn:replace` parses as before.

The trees are `Expr.ext` nodes with tags `upd-…` for
`XQueryUpdate.Expr.evalUpd`. Copy modify is the nested `let` of its
copy clauses (each value an `upd-copy`) around an `upd-modify` that
names the copy variables, so the XQuery 4.0 static checks see the
variable scopes of §5.6.

Not here: `TransformWithExpr` (§5.7), a postfix of UnaryExpr inside the
XPath 4.0 operator grammar (no `upd/` test uses it,
https://github.com/danbri/factoidal/issues/1101).
-/
import L4Factoidal.XQuery4.Grammar

namespace L4Factoidal.XQueryUpdate

open L4Factoidal.XPath4
open L4Factoidal.XQuery4

/-- `node` or `nodes`. -/
def pNodeKw : P Unit := do
  if ← eatKw "nodes" then pure () else expectKw "node"

def pInsert (sp : SubParsers) : P Expr := do
  expectKw "insert"; pNodeKw
  let src ← subE sp.exprSingle
  let mode ← if ← eatKw "as" then
      let m ← if ← eatKw "first" then pure "first"
        else if ← eatKw "last" then pure "last"
        else synErr "expected 'first' or 'last'"
      expectKw "into"; pure m
    else if ← eatKw "into" then pure "into"
    else if ← eatKw "after" then pure "after"
    else if ← eatKw "before" then pure "before"
    else synErr "expected 'into', 'after' or 'before'"
  let tgt ← subE sp.exprSingle
  pure (.ext "upd-insert" [src, tgt] [] [] [mode])

def pDelete (sp : SubParsers) : P Expr := do
  expectKw "delete"; pNodeKw
  pure (.ext "upd-delete" [← subE sp.exprSingle] [] [] [])

def pReplace (sp : SubParsers) : P Expr := do
  expectKw "replace"
  let value ← eatKw "value"
  if value then expectKw "of"
  expectKw "node"
  let tgt ← subE sp.exprSingle
  expectKw "with"
  let w ← subE sp.exprSingle
  pure (.ext (if value then "upd-replace-value" else "upd-replace") [tgt, w] [] [] [])

def pRename (sp : SubParsers) : P Expr := do
  expectKw "rename"; expectKw "node"
  let tgt ← subE sp.exprSingle
  expectKw "as"
  let nm ← subE sp.exprSingle
  pure (.ext "upd-rename" [tgt, nm] [] (← staticNs) [])

/-- Copy modify (§5.6) as nested `let` clauses. -/
def pCopy (sp : SubParsers) : P Expr := do
  let i0 ← get
  expectKw "copy"
  let mut bs : Array (QN × Expr) := #[]
  for _ in [0:10000] do
    let v ← pVar
    expectS ":="
    let e ← subE sp.exprSingle
    bs := bs.push (v, e)
    if !(← eatS ",") then break
  expectKw "modify"
  let m ← subE sp.exprSingle
  expectKw "return"
  let r ← subE sp.exprSingle
  let vs := bs.toList.map (·.1)
  let body : Expr := .ext "upd-modify" [m, r] [] vs []
  pure (bs.toList.zipIdx.foldr (fun ((v, e), k) acc =>
    .letE v (.seq .item .star) (.ext "upd-copy" [e] [] [] [toString i0 ++ "." ++ toString k]) acc) body)

/-- `invoke updating PrimaryExpr ( args )` (§5.5): the primary is a
    variable reference, a parenthesized expression or a named function
    reference. -/
def pInvoke (sp : SubParsers) : P Expr := do
  expectKw "invoke"; expectKw "updating"
  ws
  let f ← if (← peekAt 0) == '$' then pure (Expr.var (← pVar))
    else if ← eatS "(" then
      let e ← subE sp.expr
      expectS ")"; pure e
    else match ← peekQName with
      | some (p, u, l, e) =>
        set e
        expectS "#"
        let q ← resolve p u l ((← read).ns.lookup "#fn" |>.getD nsFN)
        ws
        let st ← get
        let src := (← read).s
        let mut n := 0
        let mut j := st
        for _ in [0:20] do
          let c := chAt src j
          if c.isDigit then n := n * 10 + (c.toNat - '0'.toNat); j := j + 1 else break
        if j == st then synErr "expected an arity after #"
        set j
        pure (.fref q n)
      | none => synErr "expected a function after invoke updating"
  expectS "("
  let mut args : Array Expr := #[]
  if !(← eatS ")") then
    for _ in [0:10000] do
      args := args.push (← subE sp.exprSingle)
      if !(← eatS ",") then break
    expectS ")"
  pure (.ext "upd-invoke" (f :: args.toList) [] [] [])

def exprSingleU (sp : SubParsers) : P (Option Expr) := do
  if (← kwThenKw "insert" "node") || (← kwThenKw "insert" "nodes") then return some (← pInsert sp)
  if (← kwThenKw "delete" "node") || (← kwThenKw "delete" "nodes") then return some (← pDelete sp)
  if (← kwThenKw "replace" "node") || (← kwThenKw "replace" "value") then return some (← pReplace sp)
  if ← kwThenKw "rename" "node" then return some (← pRename sp)
  if ← kwThen "copy" '$' then return some (← pCopy sp)
  if ← kwThenKw "invoke" "updating" then return some (← pInvoke sp)
  pure none

/-- The `%updating` or `%simple` annotation at offset `i` (an inline
    function expression, §7.9), if the annotations there name one. -/
def updAnnotationAt (s : Array Char) (i : Nat) : Option String := Id.run do
  let isWs (c : Char) := c == ' ' || c == '\t' || c == '\n' || c == '\r'
  let isNm (c : Char) := c.isAlphanum || c == '-' || c == '_' || c == ':' || c == '.'
  let mut j := i
  let mut found : Option String := none
  for _ in [0:100] do
    for _ in [0:s.size] do
      if j < s.size && isWs (chAt s j) then j := j + 1 else break
    if chAt s j != '%' then break
    j := j + 1
    let st := j
    for _ in [0:s.size] do
      if j < s.size && isNm (chAt s j) then j := j + 1 else break
    let nm := String.ofList ((List.range (j - st)).map (fun k => chAt s (st + k)))
    let lname := (nm.splitOn ":").getLast?.getD nm
    if lname == "updating" || lname == "simple" then found := some lname
    -- skip an argument list
    if chAt s j == '(' then
      for _ in [0:s.size] do
        if j < s.size && chAt s j != ')' then j := j + 1 else break
      j := j + 1
  return found

/-- The XQuery 4.0 grammar extension with the update productions. -/
def grammarU (cfg : Cfg) : ExtGrammar :=
  let base := grammar cfg
  { base with
    exprSingle := fun s ns sp i =>
      match liftOpt (runP (exprSingleU sp) s ns i) with
      | .ok (some r) => .ok (some r)
      | .ok none => base.exprSingle s ns sp i
      | .error e => .error e
    primary := fun s ns sp i =>
      match base.primary s ns sp i with
      | .ok (some (e, j)) =>
        match updAnnotationAt s i with
        | some a => .ok (some (.ext "upd-fn" [e] [] [] [a], j))
        | none => .ok (some (e, j))
      | other => other }

end L4Factoidal.XQueryUpdate
