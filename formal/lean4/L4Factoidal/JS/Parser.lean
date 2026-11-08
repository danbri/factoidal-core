import L4Factoidal.JS.Syntax
import L4Factoidal.JS.Number

/-!
# L4Factoidal.JS.Parser — a recursive-descent parser for the core subset

Grammar: ECMA-262 §13 (expressions) and §14 (statements), with automatic
semicolon insertion (§12.10) and the restricted productions (`return`, `break`,
`continue`, `throw`, postfix `++`/`--`). Binary operators are parsed by
precedence climbing; the precedence table is the nesting of §13.6 to §13.13.

Every parser function takes a fuel argument and each recursive call passes a
smaller one, so each is total by structural recursion. `parse` gives fuel
proportional to the token count (`parseFuel`); running out is reported as an
error, not a wrong tree.

Not parsed (a `SyntaxError` that names the feature): classes, destructuring,
default and rest parameters, spread, template literals, regular expression
literals, generators, `async`/`await`, optional chaining, `for`-`of`, modules,
`with`, getters and setters in classes. Early errors checked: `return` outside a
function, invalid assignment targets, `let`/`const` without names, `const`
without an initialiser.
-/

namespace L4Factoidal.JS

structure PState where
  toks : Array Token
  pos : Nat := 0
  /-- `var` and function names of the current function body. -/
  vars : Array String := #[]
  usesArgs : Bool := false
  strict : Bool := false
  inFun : Bool := false
  /-- In the body of a generator: `yield` is an operator. -/
  inGen : Bool := false
  /-- Enclosing loops, and loops or switches, of the current function (§14.8.1,
  §14.9.1 early errors for `continue` and `break`). -/
  loops : Nat := 0
  breakables : Nat := 0
  /-- Labels in scope, with whether each labels a loop. -/
  labels : List (String × Bool) := []
  deriving Inhabited

abbrev P := EStateM String PState

namespace P

def peek : P Token := do let s ← get; pure (s.toks.getD s.pos default)
def peekAt (k : Nat) : P Token := do let s ← get; pure (s.toks.getD (s.pos + k) default)
def advance : P Unit := modify fun s => { s with pos := s.pos + 1 }
def isP (t : Token) (p : String) : Bool := t.kind == .punct && t.text == p
def isK (t : Token) (k : String) : Bool := t.kind == .kw && t.text == k
def atP (p : String) : P Bool := do pure (isP (← peek) p)
def atK (k : String) : P Bool := do pure (isK (← peek) k)

def describe (t : Token) : String :=
  match t.kind with
  | .eof => "end of input"
  | .num => "number"
  | .str => "string"
  | _ => s!"'{t.text}'"

def fail {α} (msg : String) : P α := do
  let t ← peek
  throw s!"SyntaxError: {msg} at {describe t} (offset {t.pos})"

def expectP (p : String) : P Unit := do
  if ← atP p then advance else fail s!"expected '{p}'"

def eatP (p : String) : P Bool := do
  if ← atP p then advance; pure true else pure false

/-- §12.10: a `;`, or a place where one is inserted. -/
def semi : P Unit := do
  let t ← peek
  if isP t ";" then advance
  else if isP t "}" || t.kind == .eof || t.nl then pure ()
  else fail "missing ';'"

/-- An identifier that may be a binding name. -/
def bindingName : P String := do
  let t ← peek
  if t.kind == .ident && t.escaped && keywords.contains t.text then
    fail s!"keyword '{t.text}' must not contain escapes"
  if t.kind == .ident then
    let s ← get
    if s.strict && (t.text == "eval" || t.text == "arguments") then
      fail s!"'{t.text}' cannot be a binding name in strict mode code"
    if s.strict && ["implements", "interface", "package", "private", "protected", "public",
        "static", "yield", "let"].contains t.text then
      fail s!"'{t.text}' is a reserved word in strict mode code"
    if s.inGen && t.text == "yield" then fail "'yield' cannot be a binding name in a generator"
    advance; pure t.text
  else if t.kind == .kw && (t.text == "let" || t.text == "yield") then advance; pure t.text
  else fail "expected an identifier"

def addVar (n : String) : P Unit :=
  modify fun s => if s.vars.contains n then s else { s with vars := s.vars.push n }

end P

open P

/-- The lexically declared names of a statement list (§8.2.4). -/
def lexNames (ss : List Stmt) : List String :=
  ss.flatMap fun s => match s with
    | .decl .letK ds | .decl .constK ds => ds.flatMap Decl.names
    | .classDecl x _ => [x]
    | _ => []

/-- Early errors of a block (§14.2.1): a name declared twice lexically, or both
lexically and with `var` inside the block. -/
def checkDecls (ss : List Stmt) (vars : List String) : P Unit := do
  let lex := lexNames ss
  if lex.eraseDups.length != lex.length then fail "identifier has already been declared"
  let funs := ss.flatMap fun s => match s with | .funDecl x _ => [x] | _ => []
  if lex.any (fun x => vars.contains x || funs.contains x) then
    fail "identifier has already been declared"

/-- Binary operator precedence; `in` is excluded in a `for` head (`noIn`). -/
def binPrec (t : Token) (noIn : Bool) : Option (Nat × Sum BinOp LogOp) :=
  if t.kind == .kw then
    if t.text == "instanceof" then some (8, .inl .instanceof)
    else if t.text == "in" && !noIn then some (8, .inl .inOp)
    else none
  else if t.kind != .punct then none
  else match t.text with
    | "??" => some (1, .inr .coalesce)
    | "||" => some (2, .inr .or)
    | "&&" => some (3, .inr .and)
    | "|" => some (4, .inl .bor)
    | "^" => some (5, .inl .bxor)
    | "&" => some (6, .inl .band)
    | "==" => some (7, .inl .eq) | "!=" => some (7, .inl .ne)
    | "===" => some (7, .inl .seq) | "!==" => some (7, .inl .sne)
    | "<" => some (8, .inl .lt) | ">" => some (8, .inl .gt)
    | "<=" => some (8, .inl .le) | ">=" => some (8, .inl .ge)
    | "<<" => some (9, .inl .shl) | ">>" => some (9, .inl .sar) | ">>>" => some (9, .inl .shr)
    | "+" => some (10, .inl .add) | "-" => some (10, .inl .sub)
    | "*" => some (11, .inl .mul) | "/" => some (11, .inl .div) | "%" => some (11, .inl .mod)
    | "**" => some (12, .inl .exp)
    | _ => none

def assignOp (t : Token) : Option (Option BinOp ⊕ LogOp) :=
  if t.kind != .punct then none else
  match t.text with
  | "=" => some (.inl none)
  | "+=" => some (.inl (some .add)) | "-=" => some (.inl (some .sub))
  | "*=" => some (.inl (some .mul)) | "/=" => some (.inl (some .div))
  | "%=" => some (.inl (some .mod)) | "**=" => some (.inl (some .exp))
  | "<<=" => some (.inl (some .shl)) | ">>=" => some (.inl (some .sar))
  | ">>>=" => some (.inl (some .shr))
  | "&=" => some (.inl (some .band)) | "|=" => some (.inl (some .bor))
  | "^=" => some (.inl (some .bxor))
  | "&&=" => some (.inr .and) | "||=" => some (.inr .or) | "??=" => some (.inr .coalesce)
  | _ => none

def isTarget : Expr → Bool
  | .ident _ | .member _ _ | .index _ _ => true
  | _ => false

/-- The hole of an array literal `[,]` (an empty name cannot come from source). -/
def holeExpr : Expr := .ident ""

mutual
/-- An array or object literal read again as an assignment pattern
(§13.15.5, the cover grammar AssignmentPattern). -/
def exprToPat : Nat → Expr → Option Pat
  | 0, _ => none
  | n + 1, e =>
    match e with
    | .ident "" => none
    | .ident x => some (.id x)
    | .member _ _ | .index _ _ => some (.target e)
    | .array es => do
      let (elems, rest) ← arrElems n es []
      pure (.arr elems rest)
    | .object ps => do
      let (props, rest) ← objProps n ps []
      pure (.obj props rest)
    | _ => none

def arrElems : Nat → List Expr → List (Option PatElem) → Option (List (Option PatElem) × Option Pat)
  | 0, _, _ => none
  | _ + 1, [], acc => some (acc.reverse, none)
  | n + 1, [.spread t], acc => do
    let p ← exprToPat n t
    some (acc.reverse, some p)
  | n + 1, e :: es, acc =>
    match e with
    | .ident "" => arrElems n es (none :: acc)
    | .spread _ => none
    | .assign none t d => do
      let p ← exprToPat n t
      arrElems n es (some (.mk p (some d)) :: acc)
    | .assignPat p d => arrElems n es (some (.mk p (some d)) :: acc)
    | _ => do
      let p ← exprToPat n e
      arrElems n es (some (.mk p none) :: acc)

def objProps : Nat → List PropDef → List PatProp → Option (List PatProp × Option Pat)
  | 0, _, _ => none
  | _ + 1, [], acc => some (acc.reverse, none)
  | n + 1, [.spread t], acc => do
    let p ← exprToPat n t
    match p with
    | .id _ | .target _ => some (acc.reverse, some p)
    | _ => none
  | n + 1, p :: ps, acc =>
    match p with
    | .init k (.assign none t d) => do
      let q ← exprToPat n t
      objProps n ps (.mk k q (some d) :: acc)
    | .init k (.assignPat q d) => objProps n ps (.mk k q (some d) :: acc)
    | .init k v => do
      let q ← exprToPat n v
      objProps n ps (.mk k q none :: acc)
    | _ => none
end

/-- A property name from a token: identifier name, string or number. -/
def propName? (t : Token) : Option String :=
  match t.kind with
  | .ident | .kw => some t.text
  | .str => some t.text
  | .num => some (numToString t.num)
  | .big => some t.text
  | _ => none

/-- Does the token after the `(` at the current position, past its `)`, read `=>`? -/
def arrowAhead (toks : Array Token) (start : Nat) : Bool :=
  let rec go : Nat → Nat → Nat → Bool
    | 0, _, _ => false
    | fuel + 1, i, depth =>
      let t := toks.getD i default
      if t.kind == .eof then false
      else if isP t "(" || isP t "[" || isP t "{" then go fuel (i + 1) (depth + 1)
      else if isP t ")" || isP t "]" || isP t "}" then
        if depth == 1 then
          let n := toks.getD (i + 1) default
          isP t ")" && isP n "=>" && !n.nl
        else go fuel (i + 1) (depth - 1)
      else go fuel (i + 1) depth
  go toks.size start 0

/-- The directive prologue (§11.2.1) holds `"use strict"`. -/
def hasUseStrict (toks : Array Token) (start : Nat) : Bool :=
  let rec go : Nat → Nat → Bool
    | 0, _ => false
    | fuel + 1, i =>
      let t := toks.getD i default
      if t.kind != .str then false
      else
        let n := toks.getD (i + 1) default
        let ends := isP n ";" || isP n "}" || n.kind == .eof || n.nl
        if !ends then false
        else if t.text == "use strict" then true
        else go fuel (if isP n ";" then i + 2 else i + 1)
  go toks.size start

mutual

def parseStmt : Nat → P Stmt
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    let t ← peek
    if isP t "{" then return .block (← parseBlock n)
    if isP t ";" then advance; return .empty
    if t.kind == .kw then
      match t.text with
      | "var" =>
        advance
        let ds ← parseDecls n .var false []
        semi; return .decl .var ds
      | "const" =>
        advance
        let ds ← parseDecls n .constK false []
        semi; return .decl .constK ds
      | "function" =>
        advance
        let gen ← eatP "*"
        let name ← bindingName
        addVar name
        let f ← parseFunction n (some name) .normal gen
        return .funDecl name f
      | "if" =>
        advance; expectP "("
        let c ← parseExpr n false
        expectP ")"
        let th ← parseSubStmt n
        if ← atK "else" then advance; return .ifS c th (some (← parseSubStmt n))
        return .ifS c th none
      | "while" =>
        advance; expectP "("
        let c ← parseExpr n false
        expectP ")"
        return .whileS c (← parseLoopBody n)
      | "do" =>
        advance
        let body ← parseLoopBody n
        if !(← atK "while") then fail "expected 'while'"
        advance; expectP "("
        let c ← parseExpr n false
        expectP ")"
        let _ ← eatP ";"
        return .doWhile body c
      | "for" => advance; parseFor n
      | "return" =>
        advance
        if !(← get).inFun then fail "'return' outside of a function"
        let t' ← peek
        if isP t' ";" || isP t' "}" || t'.kind == .eof || t'.nl then semi; return .ret none
        let e ← parseExpr n false
        semi; return .ret (some e)
      | "break" | "continue" =>
        advance
        let t' ← peek
        let label ← if t'.kind == .ident && !t'.nl then advance; pure (some t'.text) else pure none
        let st ← get
        match label with
        | some l =>
          match st.labels.lookup l with
          | none => fail s!"undefined label '{l}'"
          | some isLoop => if t.text == "continue" && !isLoop then fail s!"'{l}' does not label a loop"
        | none =>
          if t.text == "continue" && st.loops == 0 then fail "'continue' outside of a loop"
          if t.text == "break" && st.breakables == 0 then fail "'break' outside of a loop or switch"
        semi
        return if t.text == "break" then .brk label else .cont label
      | "throw" =>
        advance
        if (← peek).nl then fail "line break after 'throw'"
        let e ← parseExpr n false
        semi; return .throwS e
      | "try" => advance; parseTry n
      | "switch" =>
        advance; expectP "("
        let d ← parseExpr n false
        expectP ")"; expectP "{"
        let st ← get
        set { st with breakables := st.breakables + 1 }
        let cs ← parseCases n false []
        modify fun s => { s with breakables := st.breakables }
        let after := (← get).vars
        checkDecls (cs.flatMap fun c => match c with | .mk _ b => b) (after.toList.filter (!st.vars.contains ·))
        return .switchS d cs
      | "debugger" => advance; semi; return .empty
      | "class" =>
        advance
        let name ← bindingName
        return .classDecl name (← parseClass n (some name))
      | "import" | "export" => fail "modules are not supported"
      | "with" =>
        if (← get).strict then fail "strict mode code may not include a with statement"
        advance; expectP "("
        let o ← parseExpr n false
        expectP ")"
        return .withS o (← parseSubStmt n)
      | _ => parseExprStmt n
    else if t.kind == .ident then
      let t2 ← peekAt 1
      if isP t2 ":" then
        advance; advance
        let st ← get
        if st.labels.any (·.1 == t.text) then fail s!"label '{t.text}' has already been declared"
        let nt ← peek
        let isLoop := isK nt "for" || isK nt "while" || isK nt "do" ||
          (nt.kind == .ident && st.labels.isEmpty && false)
        if (← atK "function") then fail "labelled function declarations are not supported"
        set { st with labels := (t.text, isLoop) :: st.labels }
        let body ← parseSubStmt n
        modify fun s => { s with labels := st.labels }
        return .labeled t.text body
      if t.text == "let" && (t2.kind == .ident || isP t2 "[" || isP t2 "{" ||
          (t2.kind == .kw && (t2.text == "let" || t2.text == "yield"))) then
        advance
        let ds ← parseDecls n .letK false []
        semi; return .decl .letK ds
      if t.text == "async" && isK t2 "function" && !t2.nl then fail "async functions are not supported"
      parseExprStmt n
    else parseExprStmt n

/-- A statement in a single-statement position (the body of `if`, a loop or a
label): a lexical declaration there is an early error (§14.6.1, §14.7.1.1). -/
def parseSubStmt : Nat → P Stmt
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    let t ← peek
    let t2 ← peekAt 1
    if isK t "const" || isK t "class" then fail "lexical declaration in a single-statement context"
    if t.kind == .ident && t.text == "let" && isP t2 "[" then
      fail "lexical declaration in a single-statement context"
    if t.kind == .ident && t.text == "let" && t2.nl && !(← get).strict then
      return ← parseExprStmt n
    if isK t "function" && ((← get).strict || isP t2 "*") then
      fail "function declaration in a single-statement context"
    let s ← parseStmt n
    match s with
    | .decl .letK _ | .decl .constK _ | .classDecl .. =>
      fail "lexical declaration in a single-statement context"
    | _ => pure s

/-- A loop body: `break` and `continue` are allowed in it. -/
def parseLoopBody : Nat → P Stmt
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    let st ← get
    -- labels just before this loop label it
    set { st with loops := st.loops + 1, breakables := st.breakables + 1 }
    let b ← parseSubStmt n
    modify fun s => { s with loops := st.loops, breakables := st.breakables }
    pure b

def parseExprStmt : Nat → P Stmt
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    let e ← parseExpr n false
    semi; return .expr e

/-- Statements up to `}` (not consumed) or the end of input. -/
def parseStmts : Nat → Array Stmt → P (List Stmt)
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, acc => do
    let t ← peek
    if isP t "}" || t.kind == .eof then return acc.toList
    let s ← parseStmt n
    parseStmts n (acc.push s)

def parseBlock : Nat → P (List Stmt)
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    expectP "{"
    let before := (← get).vars
    let ss ← parseStmts n #[]
    let after := (← get).vars
    checkDecls ss (after.toList.filter (!before.contains ·))
    expectP "}"
    return ss

def parseDecls : Nat → DeclKind → Bool → List Decl → P (List Decl)
  | 0, _, _, _ => fail "parser fuel exhausted"
  | n + 1, kind, noIn, acc => do
    let t ← peek
    let target ← if isP t "[" || isP t "{" then parsePattern n kind
      else do
        let name ← bindingName
        if kind != .var && name == "let" then fail "'let' cannot be a lexically bound name"
        pure (Pat.id name)
    if kind == .var then for x in target.names do addVar x
    let init ← if ← atP "=" then advance; pure (some (← parseAssign n noIn)) else pure none
    let acc := acc ++ [Decl.mk target init]
    if ← atP "," then advance; parseDecls n kind noIn acc
    else
      -- an initialiser is needed for `const` and patterns, except in a for-in/of head
      let headOk ← if noIn then do
          let t ← peek
          pure (isK t "in" || (t.kind == .ident && t.text == "of"))
        else pure false
      if init.isNone && !headOk then
        if kind == .constK then fail "missing initializer in const declaration"
        if target.name?.isNone then fail "missing initializer in destructuring declaration"
      return acc

def parseFor : Nat → P Stmt
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    expectP "("
    let t ← peek
    let t2 ← peekAt 1
    let declKind : Option DeclKind :=
      if isK t "var" then some .var
      else if isK t "const" then some .constK
      else if t.kind == .ident && t.text == "let" &&
        (t2.kind == .ident || isP t2 "[" || isP t2 "{") then some .letK
      else none
    let init : Option ForInit ← match declKind with
      | some k => do advance; pure (some (ForInit.decl k (← parseDecls n k true [])))
      | none => if isP t ";" then pure none else pure (some (ForInit.expr (← parseExpr n true)))
    let isOf := (← peek).kind == .ident && (← peek).text == "of"
    if isOf || (← atK "in") then
      advance
      let obj ← if isOf then parseAssign n false else parseExpr n false
      expectP ")"
      let body ← parseLoopBody n
      let (kind, pat) ← match init with
        | some (.decl k [Decl.mk p none]) => pure (some k, p)
        | some (.decl .var [Decl.mk (.id x) (some _)]) =>
          if isOf || (← get).strict then fail "for-in/of declarations may not have initializers"
          pure (some DeclKind.var, Pat.id x)
        | some (.decl _ _) => fail "invalid for-in/of declaration"
        | some (.expr e) =>
          match exprToPat 64 e with
          | some p => pure (none, p)
          | none => fail "invalid left-hand side in for-in/of"
        | none => fail "invalid for-in/of"
      return if isOf then .forOf kind pat obj body else .forIn kind pat obj body
    expectP ";"
    let test ← if ← atP ";" then pure none else pure (some (← parseExpr n false))
    expectP ";"
    let update ← if ← atP ")" then pure none else pure (some (← parseExpr n false))
    expectP ")"
    let body ← parseLoopBody n
    return .forS init test update body

def parseTry : Nat → P Stmt
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    let body ← parseBlock n
    let (param, handler) ← if ← atK "catch" then do
        advance
        let p ← if ← atP "(" then do
            advance
            let x ← if (← atP "[") || (← atP "{") then parsePattern n .letK else do pure (Pat.id (← bindingName))
            expectP ")"; pure (some x)
          else pure none
        pure (p, some (← parseBlock n))
      else pure (none, none)
    let fin ← if ← atK "finally" then advance; pure (some (← parseBlock n)) else pure none
    if handler.isNone && fin.isNone then fail "missing catch or finally after try"
    return .tryS body param handler fin

def parseCases : Nat → Bool → List Case → P (List Case)
  | 0, _, _ => fail "parser fuel exhausted"
  | n + 1, seenDefault, acc => do
    if ← atP "}" then advance; return acc
    let test ← if ← atK "case" then do
        advance; let e ← parseExpr n false; expectP ":"; pure (some e)
      else if ← atK "default" then do
        if seenDefault then fail "more than one default clause in switch"
        advance; expectP ":"; pure none
      else fail "expected 'case' or 'default'"
    let body ← parseCaseBody n #[]
    parseCases n (seenDefault || test.isNone) (acc ++ [Case.mk test body])

def parseCaseBody : Nat → Array Stmt → P (List Stmt)
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, acc => do
    let t ← peek
    if isP t "}" || isK t "case" || isK t "default" || t.kind == .eof then return acc.toList
    let s ← parseStmt n
    parseCaseBody n (acc.push s)

/-- Parameters and body of a function, after its name. -/
def parseFunction : Nat → Option String → FunKind → Bool → P FunDef
  | 0, _, _, _ => fail "parser fuel exhausted"
  | n + 1, name, kind, gen => do
    expectP "("
    let outerGen := (← get).inGen
    modify fun s => { s with inGen := gen }
    let (ps, rest) ← parseParams n #[]
    modify fun s => { s with inGen := outerGen }
    parseBody n name ps rest kind gen

/-- A parameter list after `(`, to the `)` (consumed): patterns with initialisers
and a rest parameter (§15.1). -/
def parseParams : Nat → Array PatElem → P (List PatElem × Option Pat)
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, acc => do
    if ← atP ")" then advance; return (acc.toList, none)
    if ← atP "..." then
      advance
      let r ← if (← atP "[") || (← atP "{") then parsePattern n .letK else do pure (Pat.id (← bindingName))
      if ← atP "=" then fail "a rest parameter may not have an initializer"
      expectP ")"
      return (acc.toList, some r)
    let p ← if (← atP "[") || (← atP "{") then parsePattern n .letK else do pure (Pat.id (← bindingName))
    let d ← if ← atP "=" then advance; pure (some (← parseAssign n false)) else pure none
    let acc := acc.push (.mk p d)
    if ← atP "," then advance; parseParams n acc
    else expectP ")"; return (acc.toList, none)

/-- A function body `{ ... }` with its own `var` scope. -/
def parseBody : Nat → Option String → List PatElem → Option Pat → FunKind → Bool → P FunDef
  | 0, _, _, _, _, _ => fail "parser fuel exhausted"
  | n + 1, name, params, rest, kind, gen => do
    let outer ← get
    if !(isP (← peek) "{") then fail "expected '{'"
    let strict := outer.strict || hasUseStrict outer.toks (outer.pos + 1)
    let names := params.flatMap (fun p => match p with | .mk q _ => q.names) ++
      (match rest with | some r => r.names | none => [])
    if strict && names.any (fun p => p == "eval" || p == "arguments") then
      fail "'eval' or 'arguments' cannot be a parameter in strict mode code"
    let simple := rest.isNone && params.all (fun p => match p with | .mk (.id _) none => true | _ => false)
    if (strict || kind == .arrow || kind == .method || !simple) && names.eraseDups.length != names.length then
      fail "duplicate parameter name not allowed in this context"
    set { outer with vars := #[], usesArgs := false, strict, inFun := true, loops := 0,
                     breakables := 0, labels := [],
                     inGen := gen }
    let body ← parseBlock n
    let inner ← get
    let usesArgs := inner.usesArgs
    let arrow := kind == .arrow
    set { inner with vars := outer.vars, strict := outer.strict, inFun := outer.inFun,
                     loops := outer.loops, breakables := outer.breakables, labels := outer.labels,
                     inGen := outer.inGen, usesArgs := outer.usesArgs || (arrow && usesArgs) }
    return FunDef.mk name params rest body inner.vars.toList (usesArgs && !arrow) strict kind gen

/-- An arrow function after its parameters and `=>`. -/
def parseArrowBody : Nat → List PatElem → Option Pat → P Expr
  | 0, _, _ => fail "parser fuel exhausted"
  | n + 1, params, rest => do
    if ← atP "{" then return .func (← parseBody n none params rest .arrow false)
    let outer ← get
    set { outer with vars := #[], inFun := true }
    let e ← parseAssign n false
    let inner ← get
    set { inner with vars := outer.vars, inFun := outer.inFun }
    return .func (FunDef.mk none params rest [.ret (some e)] inner.vars.toList false outer.strict .arrow false)

def parseExpr : Nat → Bool → P Expr
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, noIn => do
    let e ← parseAssign n noIn
    parseSeqRest n noIn e

def parseSeqRest : Nat → Bool → Expr → P Expr
  | 0, _, _ => fail "parser fuel exhausted"
  | n + 1, noIn, e => do
    if ← atP "," then
      advance
      let r ← parseAssign n noIn
      parseSeqRest n noIn (.seq e r)
    else return e

def parseAssign : Nat → Bool → P Expr
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, noIn => do
    let t ← peek
    let t2 ← peekAt 1
    if (← get).inGen && (t.kind == .ident || t.kind == .kw) && t.text == "yield" && !t.escaped then
      advance
      if ← atP "*" then
        advance
        return .yieldE true (some (← parseAssign n noIn))
      let nt ← peek
      let ends := nt.nl || nt.kind == .eof || isP nt ")" || isP nt "]" || isP nt "}" ||
        isP nt "," || isP nt ";" || isP nt ":" || isK nt "in"
      if ends then return .yieldE false none
      return .yieldE false (some (← parseAssign n noIn))
    -- arrow functions
    if (t.kind == .ident || (t.kind == .kw && t.text == "yield")) && isP t2 "=>" && !t2.nl then
      if t.text == "async" then fail "async functions are not supported"
      advance; advance
      return ← parseArrowBody n [.mk (.id t.text) none] none
    if isP t "(" && arrowAhead (← get).toks (← get).pos then
      advance
      let (ps, rest) ← parseParams n #[]
      expectP "=>"
      return ← parseArrowBody n ps rest
    if t.kind == .ident && t.text == "async" && !t2.nl && (t2.kind == .ident || isP t2 "(") then
      if isP t2 "(" && !arrowAhead (← get).toks ((← get).pos + 1) then pure ()
      else fail "async functions are not supported"
    let lhs ← parseCond n noIn
    match assignOp (← peek) with
    | none => return lhs
    | some op =>
      if !isTarget lhs then
        match op, lhs with
        | .inl none, .array _ | .inl none, .object _ =>
          match exprToPat 256 lhs with
          | some p =>
            if (← get).strict && p.names.any (fun x => x == "eval" || x == "arguments") then
              fail "cannot assign to 'eval' or 'arguments' in strict mode code"
            advance
            let rhs ← parseAssign n noIn
            return .assignPat p rhs
          | none => fail "invalid destructuring assignment target"
        | _, _ => fail "invalid assignment target"
      if (← get).strict then
        match lhs with
        | .ident x => if x == "eval" || x == "arguments" then
            fail "cannot assign to 'eval' or 'arguments' in strict mode code"
        | _ => pure ()
      advance
      let rhs ← parseAssign n noIn
      match op with
      | .inl o => return .assign o lhs rhs
      | .inr o => return .logAssign o lhs rhs

def parseCond : Nat → Bool → P Expr
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, noIn => do
    let c ← parseBin n 1 noIn
    if ← atP "?" then
      advance
      let a ← parseAssign n false
      expectP ":"
      let b ← parseAssign n noIn
      return .cond c a b
    return c

def parseBin : Nat → Nat → Bool → P Expr
  | 0, _, _ => fail "parser fuel exhausted"
  | n + 1, minPrec, noIn => do
    let lhs ← parseUnary n
    parseBinRest n minPrec noIn lhs

def parseBinRest : Nat → Nat → Bool → Expr → P Expr
  | 0, _, _, _ => fail "parser fuel exhausted"
  | n + 1, minPrec, noIn, lhs => do
    match binPrec (← peek) noIn with
    | none => return lhs
    | some (prec, op) =>
      if prec < minPrec then return lhs
      advance
      let rhs ← parseBin n (if prec == 12 then prec else prec + 1) noIn
      let e := match op with
        | .inl b => Expr.binary b lhs rhs
        | .inr l => Expr.logical l lhs rhs
      parseBinRest n minPrec noIn e

def parseUnary : Nat → P Expr
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    let t ← peek
    let un : Option UnOp :=
      if t.kind == .kw then
        match t.text with
        | "typeof" => some .typeof | "void" => some .void | "delete" => some .delete
        | _ => none
      else if t.kind == .punct then
        match t.text with
        | "!" => some .not | "~" => some .bnot | "-" => some .neg | "+" => some .plus
        | _ => none
      else none
    match un with
    | some op =>
      advance
      let e ← parseUnary n
      if op == .delete && (← get).strict then
        match e with
        | .ident _ => fail "delete of an unqualified identifier in strict mode"
        | _ => pure ()
      if op != .delete && op != .typeof && op != .void && (← atP "**") then
        fail "unary operator before '**' needs parentheses"
      return .unary op e
    | none =>
      if isP t "++" || isP t "--" then
        advance
        let e ← parseUnary n
        if !isTarget e then fail "invalid update target"
        return .update true (t.text == "++") e
      if t.kind == .ident && t.text == "await" && (← get).inFun == false then pure ()
      parsePostfix n

def parsePostfix : Nat → P Expr
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    let e ← parseLHS n
    let t ← peek
    if (isP t "++" || isP t "--") && !t.nl then
      if !isTarget e then fail "invalid update target"
      advance
      return .update false (t.text == "++") e
    return e

def parseLHS : Nat → P Expr
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    if ← atK "new" then
      let e ← parseNew n
      parseTail n e true
    else
      let p ← parsePrimary n
      parseTail n p true

def parseNew : Nat → P Expr
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    advance -- `new`
    if ← atP "." then
      advance
      let t ← peek
      if t.kind == .ident && t.text == "target" then advance; return .newTarget
      fail "expected new.target"
    let callee ← if ← atK "new" then parseNew n else do
      let p ← parsePrimary n
      parseTail n p false
    let args ← if ← atP "(" then advance; parseArgs n [] else pure []
    return .new callee args

def parseTail : Nat → Expr → Bool → P Expr
  | 0, _, _ => fail "parser fuel exhausted"
  | n + 1, e, allowCall => do
    let t ← peek
    if isP t "." then
      advance
      let nt ← peek
      if nt.kind == .ident || nt.kind == .kw then
        advance; parseTail n (.member e nt.text) allowCall
      else if isP nt "#" then fail "private names are not supported"
      else fail "expected a property name"
    else if isP t "[" then
      advance
      let k ← parseExpr n false
      expectP "]"
      parseTail n (.index e k) allowCall
    else if isP t "(" && allowCall then
      advance
      let args ← parseArgs n []
      parseTail n (.call e args) allowCall
    else if t.kind == .tmpl then
      advance
      let subs ← parseSubs n t.tmpl.subs.toList []
      parseTail n (.tagged e t.tmpl.cooked.toList t.tmpl.raw.toList subs) allowCall
    else if isP t "?." then fail "optional chaining is not supported"
    else return e

def parseArgs : Nat → List Expr → P (List Expr)
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, acc => do
    if ← atP ")" then advance; return acc.reverse
    let a ← if ← atP "..." then do advance; pure (Expr.spread (← parseAssign n false))
      else parseAssign n false
    if ← atP "," then advance; parseArgs n (a :: acc)
    else expectP ")"; return (a :: acc).reverse

def parsePrimary : Nat → P Expr
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    let t ← peek
    match t.kind with
    | .num => advance; return .num t.num
    | .big => advance; return .bigint t.text.toNat!
    | .str => advance; return .str t.text
    | .tmpl =>
      advance
      let subs ← parseSubs n t.tmpl.subs.toList []
      return .template t.tmpl.cooked.toList subs
    | .ident =>
      if t.escaped && (keywords.contains t.text ||
          ((← get).strict && ["implements", "interface", "package", "private", "protected",
            "public", "static", "yield", "let"].contains t.text)) then
        fail s!"keyword '{t.text}' must not contain escapes"
      advance
      if t.text == "arguments" then modify fun s => { s with usesArgs := true }
      return .ident t.text
    | .kw =>
      match t.text with
      | "this" => advance; return .this
      | "null" => advance; return .null
      | "true" => advance; return .bool true
      | "false" => advance; return .bool false
      | "function" =>
        advance
        let gen ← eatP "*"
        let name ← if (← peek).kind == .ident then pure (some (← bindingName)) else pure none
        return .func (← parseFunction n name .normal gen)
      | "let" | "yield" => advance; return .ident t.text
      | "class" =>
        advance
        let name ← if (← peek).kind == .ident then pure (some (← bindingName)) else pure none
        return .classE (← parseClass n name)
      | "super" =>
        advance
        if ← atP "(" then advance; return .superCall (← parseArgs n [])
        if ← atP "." then
          advance
          let nt ← peek
          if nt.kind == .ident || nt.kind == .kw then advance; return .superMember nt.text
          fail "expected a property name"
        if ← atP "[" then
          advance
          let k ← parseExpr n false
          expectP "]"
          return .superIndex k
        fail "'super' keyword unexpected here"
      | "import" => fail "modules are not supported"
      | _ => fail "unexpected keyword"
    | .punct =>
      match t.text with
      | "(" =>
        advance
        let e ← parseExpr n false
        expectP ")"
        return e
      | "[" => advance; return .array (← parseArray n [])
      | "{" => advance; return .object (← parseObject n [])
      | "/" | "/=" => fail "regular expression literals are not supported"
      | _ => fail "unexpected token"
    | .eof => fail "unexpected end of input"

def parseArray : Nat → List Expr → P (List Expr)
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, acc => do
    if ← atP "]" then advance; return acc.reverse
    if ← atP "," then advance; parseArray n (holeExpr :: acc)
    else
      let e ← if ← atP "..." then do advance; pure (Expr.spread (← parseAssign n false))
        else parseAssign n false
      if ← atP "," then advance; parseArray n (e :: acc)
      else expectP "]"; return (e :: acc).reverse

def parsePropKey : Nat → P PropKey
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    let t ← peek
    if isP t "[" then
      advance
      let e ← parseAssign n false
      expectP "]"
      return .computed e
    match propName? t with
    | some s => advance; return .lit s
    | none => fail "expected a property name"

def parseObject : Nat → List PropDef → P (List PropDef)
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, acc => do
    if ← atP "}" then advance; return acc.reverse
    let t ← peek
    let t2 ← peekAt 1
    let p ← do
      if isP t "..." then
        advance; pure (PropDef.spread (← parseAssign n false))
      else if t.kind == .ident && !t.escaped && (t.text == "get" || t.text == "set") &&
          !(isP t2 ":" || isP t2 "(" || isP t2 "," || isP t2 "}" || isP t2 "=") then
        advance
        let k ← parsePropKey n
        expectP "("
        let (ps, rest) ← parseParams n #[]
        let f ← parseBody n none ps rest .method false
        pure (if t.text == "get" then PropDef.getter k f else PropDef.setter k f)
      else if isP t "*" then
        advance
        let k ← parsePropKey n
        expectP "("
        let og := (← get).inGen
        let (ps, rest) ← parseParams n #[]
        let f ← parseBody n none ps rest .method true
        modify fun s => { s with inGen := og }
        pure (PropDef.init k (.func f))
      else if t.kind == .ident && t.text == "async" && !(isP t2 ":" || isP t2 "(" || isP t2 "," || isP t2 "}" || isP t2 "=") then
        fail "async methods are not supported"
      else if t.kind == .ident && (isP t2 "," || isP t2 "}") then
        if t.escaped && keywords.contains t.text then fail s!"keyword '{t.text}' must not contain escapes"
        advance; pure (PropDef.init (.lit t.text) (.ident t.text))
      else if t.kind == .ident && isP t2 "=" then
        -- CoverInitializedName: only valid when the literal becomes a pattern
        advance; advance
        let d ← parseAssign n false
        pure (PropDef.init (.lit t.text) (.assign none (.ident t.text) d))
      else
        let k ← parsePropKey n
        if ← atP "(" then
          advance
          let (ps, rest) ← parseParams n #[]
          pure (PropDef.init k (.func (← parseBody n none ps rest .method false)))
        else
          expectP ":"
          pure (PropDef.init k (← parseAssign n false))
    if ← atP "," then advance; parseObject n (p :: acc)
    else expectP "}"; return (p :: acc).reverse

/-- A binding pattern `[...]` or `{...}` (§14.3.3). -/
def parsePattern : Nat → DeclKind → P Pat
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, kind => do
    if ← atP "[" then
      advance
      let (es, rest) ← parsePatElems n kind []
      return .arr es rest
    if ← atP "{" then
      advance
      let (ps, rest) ← parsePatProps n kind []
      return .obj ps rest
    return .id (← bindingName)

def parsePatElems : Nat → DeclKind → List (Option PatElem) → P (List (Option PatElem) × Option Pat)
  | 0, _, _ => fail "parser fuel exhausted"
  | n + 1, kind, acc => do
    if ← atP "]" then advance; return (acc.reverse, none)
    if ← atP "," then advance; return ← parsePatElems n kind (none :: acc)
    if ← atP "..." then
      advance
      let r ← parsePattern n kind
      expectP "]"
      return (acc.reverse, some r)
    let p ← parsePattern n kind
    let d ← if ← atP "=" then advance; pure (some (← parseAssign n false)) else pure none
    let acc := some (PatElem.mk p d) :: acc
    if ← atP "," then advance; parsePatElems n kind acc
    else expectP "]"; return (acc.reverse, none)

def parsePatProps : Nat → DeclKind → List PatProp → P (List PatProp × Option Pat)
  | 0, _, _ => fail "parser fuel exhausted"
  | n + 1, kind, acc => do
    if ← atP "}" then advance; return (acc.reverse, none)
    if ← atP "..." then
      advance
      let r ← bindingName
      expectP "}"
      return (acc.reverse, some (.id r))
    let t ← peek
    let t2 ← peekAt 1
    let (k, p) ← if (t.kind == .ident || (t.kind == .kw && (t.text == "let" || t.text == "yield"))) && !isP t2 ":" then do
        let x ← bindingName
        pure (PropKey.lit x, Pat.id x)
      else do
        let k ← parsePropKey n
        expectP ":"
        pure (k, ← parsePattern n kind)
    let d ← if ← atP "=" then advance; pure (some (← parseAssign n false)) else pure none
    let acc := PatProp.mk k p d :: acc
    if ← atP "," then advance; parsePatProps n kind acc
    else expectP "}"; return (acc.reverse, none)

/-- The substitutions of a template literal: each source text parsed as an
Expression with the state of the enclosing code. -/
def parseSubs : Nat → List String → List Expr → P (List Expr)
  | 0, _, _ => fail "parser fuel exhausted"
  | _ + 1, [], acc => return acc.reverse
  | n + 1, src :: rest, acc => do
    match lex src with
    | .error e => throw e
    | .ok toks =>
      let outer ← get
      set { outer with toks, pos := 0 }
      let e ← parseExpr n false
      if (← peek).kind != .eof then fail "unexpected token in template substitution"
      modify fun s => { s with toks := outer.toks, pos := outer.pos }
      parseSubs n rest (e :: acc)

/-- A class body after the name (§15.7). Class code is strict. -/
def parseClass : Nat → Option String → P ClassDef
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, name => do
    let outerStrict := (← get).strict
    modify fun s => { s with strict := true }
    let heritage ← if ← atK "extends" then advance; pure (some (← parseLHS n)) else pure none
    expectP "{"
    let (ctor, members) ← parseMembers n heritage.isSome none []
    modify fun s => { s with strict := outerStrict }
    return .mk name heritage ctor members

def parseMembers : Nat → Bool → Option FunDef → List Member → P (Option FunDef × List Member)
  | 0, _, _, _ => fail "parser fuel exhausted"
  | n + 1, derived, ctor, acc => do
    if ← atP "}" then advance; return (ctor, acc.reverse)
    if ← atP ";" then advance; return ← parseMembers n derived ctor acc
    let t0 ← peek
    let t1 ← peekAt 1
    let static := t0.kind == .ident && t0.text == "static" &&
      !(isP t1 "(" || isP t1 "=" || isP t1 ";" || isP t1 "}")
    if static then advance
    if static && (← atP "{") then fail "class static blocks are not supported"
    let t ← peek
    let t2 ← peekAt 1
    let gen := isP t "*"
    if gen then advance
    let t ← peek
    let t2 ← peekAt 1
    if isP t "#" then fail "private class members are not supported"
    if t.kind == .ident && t.text == "async" && !t2.nl && !(isP t2 "(" || isP t2 "=" || isP t2 ";" || isP t2 "}") then
      fail "async methods are not supported"
    let accessor := t.kind == .ident && (t.text == "get" || t.text == "set") &&
      !(isP t2 "(" || isP t2 "=" || isP t2 ";" || isP t2 "}")
    if accessor then advance
    if ← atP "#" then fail "private class members are not supported"
    let kt ← peek
    let k ← parsePropKey n
    if ← atP "(" then
      advance
      let (ps, rest) ← parseParams n #[]
      let isCtor := !static && !accessor && (kt.kind == .ident || kt.kind == .kw || kt.kind == .str) && kt.text == "constructor"
      if isCtor then
        if ctor.isSome then fail "a class may only have one constructor"
        let f ← parseBody n none ps rest (.ctor derived) false
        return ← parseMembers n derived (some f) acc
      let f ← parseBody n none ps rest .method gen
      let kind := if accessor then (if t.text == "get" then MemberKind.getter else .setter) else .method
      parseMembers n derived ctor (.mk static kind k f :: acc)
    else
      if accessor then fail "expected '('"
      -- a field: its initialiser is the body of a method that returns it
      let outer ← get
      set { outer with vars := #[], inFun := true }
      let init ← if ← atP "=" then advance; pure (some (← parseAssign n false)) else pure none
      set { (← get) with vars := outer.vars, inFun := outer.inFun }
      semi
      let f := FunDef.mk none [] none [.ret init] [] false true .method false
      parseMembers n derived ctor (.mk static .field k f :: acc)

end

/-- Fuel for a token count: each token is passed by a bounded number of calls
on any path from the root. -/
def parseFuel (tokens : Nat) : Nat := 64 * tokens + 1024

/-- Parse a script (§16.1). `strict` forces strict mode code. -/
def parseScript (src : String) (strict : Bool := false) : Except String Script :=
  match lex src with
  | .error e => .error e
  | .ok toks =>
    let strict := strict || hasUseStrict toks 0
    let st : PState := { toks, strict }
    match (parseStmts (parseFuel toks.size) #[]).run st with
    | .ok body st' =>
      if (st'.toks.getD st'.pos default).kind != .eof then
        .error s!"SyntaxError: unexpected '{(st'.toks.getD st'.pos default).text}'"
      else
        let lex := lexNames body
        let funs := body.flatMap fun s => match s with | .funDecl x _ => [x] | _ => []
        if lex.eraseDups.length != lex.length || lex.any (fun x => st'.vars.contains x || funs.contains x) then
          .error "SyntaxError: identifier has already been declared"
        else .ok { body, vars := st'.vars.toList, strict }
    | .error e _ => .error e

end L4Factoidal.JS
