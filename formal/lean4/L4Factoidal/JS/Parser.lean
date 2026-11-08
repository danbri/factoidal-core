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
  if t.kind == .ident then
    let s ← get
    if s.strict && (t.text == "eval" || t.text == "arguments") then
      fail s!"'{t.text}' cannot be a binding name in strict mode code"
    advance; pure t.text
  else if t.kind == .kw && (t.text == "let" || t.text == "yield") then advance; pure t.text
  else fail "expected an identifier"

def addVar (n : String) : P Unit :=
  modify fun s => if s.vars.contains n then s else { s with vars := s.vars.push n }

end P

open P

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

/-- A property name from a token: identifier name, string or number. -/
def propName? (t : Token) : Option String :=
  match t.kind with
  | .ident | .kw => some t.text
  | .str => some t.text
  | .num => some (numToString t.num)
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
        let name ← bindingName
        addVar name
        let f ← parseFunction n (some name) false
        return .funDecl name f
      | "if" =>
        advance; expectP "("
        let c ← parseExpr n false
        expectP ")"
        let th ← parseStmt n
        if ← atK "else" then advance; return .ifS c th (some (← parseStmt n))
        return .ifS c th none
      | "while" =>
        advance; expectP "("
        let c ← parseExpr n false
        expectP ")"
        return .whileS c (← parseStmt n)
      | "do" =>
        advance
        let body ← parseStmt n
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
        let cs ← parseCases n false []
        return .switchS d cs
      | "debugger" => advance; semi; return .empty
      | "class" => fail "classes are not supported"
      | "import" | "export" => fail "modules are not supported"
      | "with" => fail "'with' is not supported"
      | _ => parseExprStmt n
    else if t.kind == .ident then
      let t2 ← peekAt 1
      if isP t2 ":" then
        advance; advance
        if (← atK "function") then fail "labelled function declarations are not supported"
        return .labeled t.text (← parseStmt n)
      if t.text == "let" && (t2.kind == .ident || isP t2 "[" || isP t2 "{" ||
          (t2.kind == .kw && (t2.text == "let" || t2.text == "yield"))) then
        advance
        let ds ← parseDecls n .letK false []
        semi; return .decl .letK ds
      if t.text == "async" && isK t2 "function" && !t2.nl then fail "async functions are not supported"
      parseExprStmt n
    else parseExprStmt n

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
    let ss ← parseStmts n #[]
    expectP "}"
    return ss

def parseDecls : Nat → DeclKind → Bool → List Decl → P (List Decl)
  | 0, _, _, _ => fail "parser fuel exhausted"
  | n + 1, kind, noIn, acc => do
    let t ← peek
    if isP t "[" || isP t "{" then fail "destructuring is not supported"
    let name ← bindingName
    if kind != .var && name == "let" then fail "'let' cannot be a lexically bound name"
    if kind == .var then addVar name
    let init ← if ← atP "=" then advance; pure (some (← parseAssign n noIn)) else pure none
    let acc := acc ++ [Decl.mk name init]
    if ← atP "," then advance; parseDecls n kind noIn acc
    else
      -- a `const` needs an initialiser, except as the head of `for`-`in`
      if kind == .constK && init.isNone && !(noIn && (← atK "in")) then
        fail "missing initializer in const declaration"
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
    if (← peek).kind == .ident && (← peek).text == "of" then fail "for-of is not supported"
    if ← atK "in" then
      advance
      let obj ← parseExpr n false
      expectP ")"
      let body ← parseStmt n
      match init with
      | some (.decl k [Decl.mk name none]) => return .forIn (some k) (.ident name) obj body
      | some (.decl _ _) => fail "invalid for-in declaration"
      | some (.expr e) =>
        if isTarget e then return .forIn none e obj body
        else fail "invalid left-hand side in for-in"
      | none => fail "invalid for-in"
    expectP ";"
    let test ← if ← atP ";" then pure none else pure (some (← parseExpr n false))
    expectP ";"
    let update ← if ← atP ")" then pure none else pure (some (← parseExpr n false))
    expectP ")"
    let body ← parseStmt n
    return .forS init test update body

def parseTry : Nat → P Stmt
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    let body ← parseBlock n
    let (param, handler) ← if ← atK "catch" then do
        advance
        let p ← if ← atP "(" then do
            advance
            if (← atP "[") || (← atP "{") then fail "destructuring is not supported"
            let x ← bindingName
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
def parseFunction : Nat → Option String → Bool → P FunDef
  | 0, _, _ => fail "parser fuel exhausted"
  | n + 1, name, isExpr => do
    let _ := isExpr
    if ← atP "*" then fail "generators are not supported"
    expectP "("
    let ps ← parseParams n []
    parseBody n name ps false

def parseParams : Nat → List String → P (List String)
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, acc => do
    if ← atP ")" then advance; return acc
    if ← atP "..." then fail "rest parameters are not supported"
    if (← atP "[") || (← atP "{") then fail "destructuring is not supported"
    let p ← bindingName
    if ← atP "=" then fail "default parameters are not supported"
    if ← atP "," then advance; parseParams n (acc ++ [p])
    else expectP ")"; return acc ++ [p]

/-- A function body `{ ... }` with its own `var` scope. -/
def parseBody : Nat → Option String → List String → Bool → P FunDef
  | 0, _, _, _ => fail "parser fuel exhausted"
  | n + 1, name, params, arrow => do
    let outer ← get
    if !(isP (← peek) "{") then fail "expected '{'"
    let strict := outer.strict || hasUseStrict outer.toks (outer.pos + 1)
    if strict && params.any (fun p => p == "eval" || p == "arguments") then
      fail "'eval' or 'arguments' cannot be a parameter in strict mode code"
    set { outer with vars := #[], usesArgs := false, strict, inFun := true }
    let body ← parseBlock n
    let inner ← get
    let usesArgs := inner.usesArgs
    set { inner with vars := outer.vars, strict := outer.strict, inFun := outer.inFun,
                     usesArgs := outer.usesArgs || (arrow && usesArgs) }
    return FunDef.mk name params body inner.vars.toList (usesArgs && !arrow) strict arrow

/-- An arrow function after its parameters and `=>`. -/
def parseArrowBody : Nat → List String → P Expr
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, params => do
    if ← atP "{" then return .func (← parseBody n none params true)
    let outer ← get
    set { outer with vars := #[], inFun := true }
    let e ← parseAssign n false
    let inner ← get
    set { inner with vars := outer.vars, inFun := outer.inFun }
    return .func (FunDef.mk none params [.ret (some e)] inner.vars.toList false outer.strict true)

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
    -- arrow functions
    if (t.kind == .ident || (t.kind == .kw && t.text == "yield")) && isP t2 "=>" && !t2.nl then
      if t.text == "async" then fail "async functions are not supported"
      advance; advance
      return ← parseArrowBody n [t.text]
    if isP t "(" && arrowAhead (← get).toks (← get).pos then
      advance
      let ps ← parseParams n []
      expectP "=>"
      return ← parseArrowBody n ps
    if t.kind == .ident && t.text == "async" && !t2.nl && (t2.kind == .ident || isP t2 "(") then
      if isP t2 "(" && !arrowAhead (← get).toks ((← get).pos + 1) then pure ()
      else fail "async functions are not supported"
    let lhs ← parseCond n noIn
    match assignOp (← peek) with
    | none => return lhs
    | some op =>
      if !isTarget lhs then fail "invalid assignment target"
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
    if ← atP "." then fail "new.target is not supported"
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
    else if isP t "?." then fail "optional chaining is not supported"
    else return e

def parseArgs : Nat → List Expr → P (List Expr)
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, acc => do
    if ← atP ")" then advance; return acc
    if ← atP "..." then fail "spread is not supported"
    let a ← parseAssign n false
    if ← atP "," then advance; parseArgs n (acc ++ [a])
    else expectP ")"; return acc ++ [a]

def parsePrimary : Nat → P Expr
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    let t ← peek
    match t.kind with
    | .num => advance; return .num t.num
    | .str => advance; return .str t.text
    | .ident =>
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
        let name ← if (← peek).kind == .ident then pure (some (← bindingName)) else pure none
        return .func (← parseFunction n name true)
      | "let" | "yield" => advance; return .ident t.text
      | "class" => fail "classes are not supported"
      | "super" => fail "super is not supported"
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
    if ← atP "]" then advance; return acc
    if ← atP "," then advance; parseArray n (acc ++ [.ident "undefined"])
    else
      if ← atP "..." then fail "spread is not supported"
      let e ← parseAssign n false
      if ← atP "," then advance; parseArray n (acc ++ [e])
      else expectP "]"; return acc ++ [e]

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
    if ← atP "}" then advance; return acc
    let t ← peek
    let t2 ← peekAt 1
    let p ← do
      if t.kind == .ident && (t.text == "get" || t.text == "set") &&
          !(isP t2 ":" || isP t2 "(" || isP t2 "," || isP t2 "}") then
        advance
        let k ← parsePropKey n
        expectP "("
        let ps ← parseParams n []
        let f ← parseBody n none ps false
        pure (if t.text == "get" then PropDef.getter k f else PropDef.setter k f)
      else if isP t "*" || (t.kind == .ident && t.text == "async" && !(isP t2 ":" || isP t2 "(" || isP t2 "," || isP t2 "}")) then
        fail "generator and async methods are not supported"
      else if t.kind == .ident && (isP t2 "," || isP t2 "}") then
        advance; pure (PropDef.init (.lit t.text) (.ident t.text))
      else
        let k ← parsePropKey n
        if ← atP "(" then
          advance
          let ps ← parseParams n []
          pure (PropDef.init k (.func (← parseBody n none ps false)))
        else
          expectP ":"
          pure (PropDef.init k (← parseAssign n false))
    if ← atP "," then advance; parseObject n (acc ++ [p])
    else expectP "}"; return acc ++ [p]

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
      else .ok { body, vars := st'.vars.toList, strict }
    | .error e _ => .error e

end L4Factoidal.JS
