import Std.Data.HashMap
import Std.Data.HashSet
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
  /-- The characters that `toks` came from. `Token.pos` is an index in it (`P.relexAt`). -/
  src : Array Char := #[]
  /-- `var` and function names of the current function body. -/
  vars : Array String := #[]
  /-- The names in `vars`, for the test in `P.addVar` (a function of a generated program has
  thousands of `var` names). -/
  varSet : Std.HashSet String := {}
  /-- The names of the `var` declarations of the current function body, in order, with
  repeats, and without the Annex B.3.3 names of functions in blocks: a block's
  VarDeclaredNames for its early errors (§14.2.1) are a range of it. -/
  realVars : Array String := #[]
  usesArgs : Bool := false
  strict : Bool := false
  inFun : Bool := false
  /-- In the body of a generator: `yield` is an operator. -/
  inGen : Bool := false
  /-- In the body of an async function: `await` is an operator. -/
  inAsync : Bool := false
  /-- Enclosing loops, and loops or switches, of the current function (§14.8.1,
  §14.9.1 early errors for `continue` and `break`). -/
  loops : Nat := 0
  breakables : Nat := 0
  /-- Labels in scope, with whether each labels a loop. -/
  labels : List (String × Bool) := []
  /-- Module code (§16.2): `import.meta` is valid. -/
  module : Bool := false
  /-- The module's code names `import.meta`. -/
  usesMeta : Bool := false
  /-- The blocks around the current statement in the current function (a function body is
  one), and the depth at which its top-level statements are: 0 in a script, 1 in a function. -/
  depth : Nat := 0
  topDepth : Nat := 0
  /-- The names declared lexically so far (`let`, `const`, `class`, parameters) in each block
  around the current statement, innermost first (Annex B.3.3.1: a block's function declaration
  is not also a `var` when that would clash with one of them). -/
  lexStack : List (List String) := [[]]
  /-- Statements to put after the statement being parsed (`annexBLabel`). -/
  pending : Array Stmt := #[]
  /-- In the initialiser of a class field or in a static block (arrow functions keep it):
  `arguments` and `super()` are early errors there (§15.7.1). `staticNext`: the body that
  `parseBody` reads next is a static block. -/
  fieldInit : Bool := false
  staticNext : Bool := false
  /-- The classes around the current position, and the private names used in the class
  being read that it has not been seen to declare yet (§15.7.1: AllPrivateIdentifiersValid).
  `privAny`: code of a direct `eval`, which may use the private names of the classes around
  the call. -/
  classDepth : Nat := 0
  privRefs : List String := []
  privAny : Bool := false
  /-- May `super(...)` (a derived class's constructor) and `super.x` (a method) appear here
  (§15.7.1, §15.2.1, §15.4.1 early errors)? True outside every function (a direct `eval`'s
  code may be in either); a function body sets them for its kind, an arrow function keeps
  its context's, and method parameters allow both. -/
  superCall : Bool := true
  superProp : Bool := true
  /-- May `new.target` appear here (§15.1.1, §16.1.1): in a function that is not an arrow
  function, and in an arrow function or field initialiser inside one. -/
  newTargetOk : Bool := true
  deriving Inhabited

abbrev P := EStateM String PState

/-- The name `import.meta` is read through in module code (`JS/Modules.lean`): not an identifier
of the language, so no source text can name it. -/
def metaName : String := "%meta"

/-- The name `import(...)` calls: a hidden property of the global object (a private-name key,
so no identifier or String key of a script is it). The realm's function answers a rejected
promise: no host loads a module for a script yet (`NativeX.dynImport`). -/
def dynImportName : String := privKey "import"

/-- Equal identifier texts become one `String` object: names compare by pointer first. -/
def internToks (toks : Array Token) : Array Token :=
  (toks.foldl (init := ((Array.emptyWithCapacity toks.size, {}) : Array Token × Std.HashMap String String))
    fun (out, m) t =>
      if t.kind == .ident then
        match m.get? t.text with
        | some s => (out.push { t with text := s }, m)
        | none => (out.push t, m.insert t.text t.text)
      else (out.push t, m)).1

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

/-- Lex again from the current token with the other reading of its `/`. The token is a `/` or
`/=` punctuator (`asRegex`: read it as the start of a regular expression literal) or a regular
expression literal (read its `/` as a division). §12: the syntactic grammar chooses the lexical
goal symbol, InputElementRegExp or InputElementDiv. The lexer makes a first choice from the
tokens before the `/` (`regexAllowed`); the parser calls this at the two places where the
grammar decides against it: a `/` where a primary expression starts, and a regular expression
literal after an operand. The tokens before the current one stay as they are. -/
def relexAt (asRegex : Bool) : P Unit := do
  let s ← get
  let t := s.toks.getD s.pos default
  match lexFrom s.src t.pos asRegex t.nl (openBefore s.toks s.pos) with
  | .error e => throw e
  | .ok tail => set { s with toks := s.toks.extract 0 s.pos ++ internToks tail }

def eatP (p : String) : P Bool := do
  if ← atP p then advance; pure true else pure false

/-- §12.10: a `;`, or a place where one is inserted. -/
def semi : P Unit := do
  let t ← peek
  if isP t ";" then advance
  else if isP t "}" || t.kind == .eof || t.nl then pure ()
  else fail "missing ';'"

/-- The words reserved in strict mode code only (§12.7.2). -/
def strictReserved : List String :=
  ["implements", "interface", "package", "private", "protected", "public", "static", "yield", "let"]

/-- An identifier that may be a binding name. -/
def bindingName : P String := do
  let t ← peek
  if t.kind == .ident && t.escaped && keywords.contains t.text then
    fail s!"keyword '{t.text}' must not contain escapes"
  if t.kind == .ident then
    let s ← get
    if s.strict && (t.text == "eval" || t.text == "arguments") then
      fail s!"'{t.text}' cannot be a binding name in strict mode code"
    if s.strict && strictReserved.contains t.text then
      fail s!"'{t.text}' is a reserved word in strict mode code"
    if s.inGen && t.text == "yield" then fail "'yield' cannot be a binding name in a generator"
    if s.inAsync && t.text == "await" then fail "'await' cannot be a binding name in an async function"
    advance; pure t.text
  else if t.kind == .kw && (t.text == "let" || t.text == "yield") then advance; pure t.text
  else fail "expected an identifier"

/-- The name of a class: class code is strict (§15.7.1), its name too. -/
def classBindingName : P String := do
  let st := (← get).strict
  modify fun s => { s with strict := true }
  let n ← bindingName
  modify fun s => { s with strict := st }
  pure n

/-- Add a `var` or function name of the current function body, once. `vars` only grows at its
end while a body is parsed, so the names added after a point are `vars` from the size it had
there (`parseBlock`, `switch`). -/
def addVar (n : String) : P Unit :=
  modify fun s =>
    if s.varSet.contains n then s
    else { s with vars := s.vars.push n, varSet := s.varSet.insert n }

/-- A name of a `var` declaration (`realVars`). -/
def addRealVar (n : String) : P Unit :=
  modify fun s => { s with realVars := s.realVars.push n }

/-- Record lexically declared names in the current block (`lexStack`). -/
def addLex (names : List String) : P Unit :=
  modify fun s => match s.lexStack with
    | top :: rest => { s with lexStack := (names ++ top) :: rest }
    | [] => { s with lexStack := [names] }

/-- Enter a block scope: one more level, and a new frame of `lexStack` holding `names`. -/
def pushScope (names : List String := []) : P Unit :=
  modify fun s => { s with depth := s.depth + 1, lexStack := names :: s.lexStack }

def popScope : P Unit :=
  modify fun s => { s with depth := s.depth - 1, lexStack := s.lexStack.drop 1 }

/-- A private name is `#` and an IdentifierName with nothing between them (§12.7.1). -/
def privAdjacent (hash name : Token) : P Unit :=
  if name.pos == hash.pos + 1 then pure () else fail "a private name has no space after '#'"

/-- A use of the private name with key `k` (`o.#x`, `#x in o`): checked when its class ends. -/
def usePriv (k : String) : P Unit :=
  modify fun s => if s.privRefs.contains k then s else { s with privRefs := k :: s.privRefs }

/-- The statements queued for after the current one, taken. -/
def takePending : P (Array Stmt) := do
  let s ← get
  if s.pending.isEmpty then pure #[] else
  set { s with pending := #[] }
  pure s.pending

end P

open P

/-- The function declarations of a block, as (name, generator or async): may they stand
together? A name declared twice is an early error (§14.2.1), except in code that is not strict
when every declaration of it is a plain function (Annex B.3.2.4). -/
def blockFunsOk (strict : Bool) (fdecls : List (String × Bool)) : Bool :=
  let funs := fdecls.map (·.1)
  funs.eraseDups.length == funs.length ||
    (!strict && fdecls.all fun (x, special) => !special || funs.count x == 1)

/-- §15.4.1: a getter has no parameters; a setter has exactly one, not a rest parameter
(PropertySetParameterList). -/
def accessorParamsOk (getter : Bool) (count : Nat) (hasRest : Bool) : Bool :=
  !hasRest && count == (if getter then 0 else 1)

/-- §15.7.1 ClassElement early errors on the PropName of a literal key (a computed key has
none): a special method (getter, setter, generator, async) is not named "constructor"; a
static method or field is not named "prototype"; a field is not named "constructor". -/
def classElementOk (static special isField : Bool) (k : PropKey) : Bool :=
  match k with
  | .lit s =>
    !(static && s == "prototype") &&
    !(s == "constructor" && (isField || (!static && special)))
  | _ => true

/-- The lexically declared names of a statement list (§8.2.4). -/
def lexNames (ss : List Stmt) : List String :=
  ss.flatMap fun s => match s with
    | .decl .letK ds | .decl .constK ds => ds.flatMap Decl.names
    | .classDecl x _ => [x]
    | _ => []

/-- Early errors of a block (§14.2.1, §14.12.1): a name declared twice lexically, or both
lexically and with `var` inside the block. `inBlock`: a block or a `switch`, where function
declarations are lexical too; not the top level of a function body, where they are `var`s. -/
def checkDecls (ss : List Stmt) (vars : List String) (inBlock : Bool := true) : P Unit := do
  let lex := lexNames ss
  if lex.eraseDups.length != lex.length then fail "identifier has already been declared"
  let fdecls := ss.filterMap fun s => match s with
    | .funDecl x f => some (x, f.gen || f.async)
    | _ => none
  let funs := fdecls.map (·.1)
  if lex.any (fun x => vars.contains x || funs.contains x) then
    fail "identifier has already been declared"
  if inBlock then
    if funs.any vars.contains then fail "identifier has already been declared"
    if !blockFunsOk (← get).strict fdecls then fail "identifier has already been declared"

/-- Where `super(...)` may appear in a function body of this kind (§15.7.1, §15.2.1): only
in a derived class's constructor; an arrow function keeps its context's answer. -/
def superCallIn (k : FunKind) (outer : Bool) : Bool :=
  match k with
  | .ctor d => d
  | .arrow => outer
  | _ => false

/-- Where `super.x` may appear in a function body of this kind (§15.2.1): in methods and
constructors; not in a plain function; an arrow function keeps its context's answer. -/
def superPropIn (k : FunKind) (outer : Bool) : Bool :=
  match k with
  | .normal => false
  | .arrow => outer
  | _ => true

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
  | .ident _ | .member _ _ | .index _ _ | .superMember _ | .superIndex _ => true
  | _ => false

/-- May `e` stand left of an assignment operator or under `++`/`--`? A target (`isTarget`),
or, in code that is not strict, a call (§13.15.1 with the web's exception: the call is
evaluated, then PutValue throws a ReferenceError; the evaluator's `evalRef`, `putTarget`). -/
def targetOk (e : Expr) : P Bool := do
  if isTarget e then return true
  match e with
  -- an ImportCall is never a target (§13.3.10.1: it is not a CallExpression of Annex B's kind)
  | .call (.ident f) _ => pure (f != dynImportName && !(← get).strict)
  | .call .. => pure !(← get).strict
  | _ => pure false

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
    | .member _ _ | .index _ _ | .superMember _ | .superIndex _ => some (.target e)
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
  | .str => some (strKey t.text)
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

/-- `for await (target of obj) body` (§14.7.5.6 and §14.7.5.7 with iteratorKind async) as
statements of the language the evaluator already runs. `aw e` is `await e` in the form the
enclosing function reads it (`inGen`: an async generator).

```
{ const I = %forAwait0(obj);            // GetIterator(obj, async)
  const X = I.next; let S = false;      // S: the body is running (an abrupt end closes I)
  try { while (true) {
      S = false;
      const T = await %forAwait1(X, I); // Call(next, iterator), awaited
      %forAwait2(T);                    // TypeError unless an Object
      if (T.done) break;
      const V = T.value; S = true;
      target = V;  body } }
  catch (E) {                           // a throw: `return` is called and awaited, its
    if (S) { S = false;                 // errors dropped (AsyncIteratorClose, step 5)
      try { const M = I.return; if (M != null) await %forAwait1(M, I); } catch {} }
    throw E; }
  finally {                             // break, return, continue to an outer loop
    if (S) { const M = I.return;
      if (M != null) { const Q = await %forAwait1(M, I); %forAwait2(Q); } } } }
```

The names `I`, `X`, ... start with `%` and carry `uid` (the head's position): source text
cannot name them, and each loop has its own. The iterator is not closed when `next` or
reading `done` or `value` fails (S is false there), as §7.4.3 to §7.4.10 say. -/
def forAwaitStmt (inGen : Bool) (uid : Nat) (kind : Option DeclKind) (pat : Pat) (obj : Expr)
    (body : Stmt) : Stmt :=
  let nm (c : String) : String := "%f" ++ c ++ toString uid
  let i := nm "i"; let x := nm "x"; let st := nm "s"; let t := nm "t"; let v := nm "v"
  let e := nm "e"; let m := nm "m"; let q := nm "q"
  let aw (a : Expr) : Expr :=
    if inGen then .yieldE false (some (.call (.ident "%await") [a])) else .yieldE false (some a)
  let call1 (f : String) : Expr := .call (.ident (forAwaitFn 1)) [.ident f, .ident i]
  let isObj (r : String) : Stmt := .expr (.call (.ident (forAwaitFn 2)) [.ident r])
  let setS (b : Bool) : Stmt := .expr (.assign none (.ident st) (.bool b))
  let const1 (name : String) (init : Expr) : Stmt := .decl .constK [Decl.mk (.id name) (some init)]
  let bind : Stmt := match kind, pat with
    | some k, p => .decl k [Decl.mk p (some (.ident v))]
    | none, .id y => .expr (.assign none (.ident y) (.ident v))
    | none, .target tg => .expr (.assign none tg (.ident v))
    | none, p => .expr (.assignPat p (.ident v))
  let getReturn : Stmt := const1 m (.member (.ident i) "return")
  let hasReturn : Expr := .binary .ne (.ident m) .null
  let closeQuiet : Stmt :=
    .tryS [getReturn, .ifS hasReturn (.expr (aw (call1 m))) none] none (some []) none
  let closeChecked : Stmt :=
    .block [getReturn, .ifS hasReturn (.block [const1 q (aw (call1 m)), isObj q]) none]
  .block [
    const1 i (.call (.ident (forAwaitFn 0)) [obj]),
    const1 x (.member (.ident i) "next"),
    .decl .letK [Decl.mk (.id st) (some (.bool false))],
    .tryS
      [.whileS (.bool true) (.block [
        setS false,
        const1 t (aw (call1 x)),
        isObj t,
        .ifS (.member (.ident t) "done") (.brk none) none,
        const1 v (.member (.ident t) "value"),
        setS true,
        bind,
        body])]
      (some (.id e))
      (some [.ifS (.ident st) (.block [setS false, closeQuiet]) none, .throwS (.ident e)])
      (some [.ifS (.ident st) closeChecked none])]

/-- Is the statement at token `i`, after any further labels (`b: c:`), an iteration
statement (§14.13.1: `continue label` needs a label of one)? -/
def labelsLoop (toks : Array Token) : Nat → Nat → Bool
  | _, 0 => false
  | i, fuel + 1 =>
    let t := toks.getD i default
    if t.kind == .ident && P.isP (toks.getD (i + 1) default) ":" then labelsLoop toks (i + 2) fuel
    else P.isK t "for" || P.isK t "while" || P.isK t "do"

/-- The labels around a statement, innermost first, and the statement inside them (at most
`fuel` labels; a loop, not a recursion on the stack). -/
def unlabel : Nat → List String → Stmt → List String × Stmt
  | 0, acc, s => (acc, s)
  | n + 1, acc, s =>
    match s with
    | .labeled l inner => unlabel n (l :: acc) inner
    | _ => (acc, s)

/-- A label on the statements of a `for await` (`forAwaitStmt`) labels their loop too, so
`continue label` and `break label` in the body reach it. Other statements are unchanged. -/
def labelForAwait (l : String) (s : Stmt) : Stmt :=
  let (inner, core) := unlabel 64 [] s
  match core with
  | .block [d, x, st, .tryS [w] p h f] =>
    match d with
    | .decl .constK [Decl.mk (.id name) _] =>
      if name.startsWith "%fi" then
        inner.foldl (fun acc l2 => .labeled l2 acc) (.block [d, x, st, .tryS [.labeled l w] p h f])
      else s
    | _ => s
  | _ => s

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
        addLex (ds.flatMap Decl.names)
        semi; return .decl .constK ds
      | "function" =>
        advance
        let gen ← eatP "*"
        let name ← bindingName
        -- At the top level of a function or script the name is a `var`-scoped name. In a
        -- block it is the block's (§14.2.3); Annex B.3.3.1 makes a plain function in code
        -- that is not strict a `var` too, set when the declaration is evaluated, unless a
        -- `let`, `const`, `class` or parameter of an enclosing block has the name.
        let st ← get
        let inBlock := st.depth > st.topDepth
        let hoist := !inBlock || (!st.strict && !gen && name != "arguments" &&
          !(st.lexStack.drop 1).any (·.contains name))
        if hoist then addVar name
        let f ← parseFunction n (some name) .normal (if gen then 1 else 0)
        if inBlock && hoist then
          modify fun s => { s with pending := s.pending.push (.labeled annexBLabel (.expr (.ident name))) }
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
        semi
        -- in an async generator `return e` awaits `e` (§14.10.1 ReturnStatement, step 3)
        let st ← get
        if st.inGen && st.inAsync then return .ret (some (.yieldE false (some (.call (.ident "%await") [e]))))
        return .ret (some e)
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
        pushScope
        let cs ← parseCases n false []
        popScope
        modify fun s => { s with breakables := st.breakables }
        let after := (← get).realVars
        checkDecls (cs.flatMap fun c => match c with | .mk _ b => b) (after.extract st.realVars.size after.size).toList
        return .switchS d cs
      | "debugger" => advance; semi; return .empty
      | "class" =>
        advance
        let name ← classBindingName
        addLex [name]
        return .classDecl name (← parseClass n (some name))
      | "import" =>
        -- `import(...)` and `import.meta` start an expression statement; a declaration
        -- is only valid at the top level of a module (`parseModule`)
        let t2 ← peekAt 1
        if isP t2 "(" || isP t2 "." then parseExprStmt n
        else fail "import declarations may only appear at top level of a module"
      | "export" => fail "export declarations may only appear at top level of a module"
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
        if (st.inAsync && t.text == "await") || ((st.inGen || st.strict) && t.text == "yield") then
          fail s!"'{t.text}' cannot be a label here"
        -- the statement after this label and the labels that follow it (`a: b: for ...`)
        let isLoop := labelsLoop st.toks st.pos st.toks.size
        if (← atK "function") then fail "labelled function declarations are not supported"
        set { st with labels := (t.text, isLoop) :: st.labels }
        let body ← parseSubStmt n
        modify fun s => { s with labels := st.labels }
        return .labeled t.text (labelForAwait t.text body)
      if t.text == "let" && (t2.kind == .ident || isP t2 "[" || isP t2 "{" ||
          (t2.kind == .kw && (t2.text == "let" || t2.text == "yield"))) then
        advance
        let ds ← parseDecls n .letK false []
        addLex (ds.flatMap Decl.names)
        semi; return .decl .letK ds
      if t.text == "async" && isK t2 "function" && !t2.nl then
        advance; advance
        let g ← eatP "*"
        let name ← bindingName
        -- in a block the name is the block's only (Annex B.3.3 is for plain functions)
        if (← get).depth == (← get).topDepth then addVar name
        let f ← parseFunction n (some name) .normal (if g then 3 else 2)
        return .funDecl name f
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
    if t.kind == .ident && t.text == "async" && !t.escaped && isK t2 "function" && !t2.nl then
      fail "async function declaration in a single-statement context"
    if isK t "function" then
      -- Annex B.3.4: a function declaration as the clause of an `if` is in a block of its own
      pushScope
      let s ← parseStmt n
      popScope
      return .block (#[s] ++ (← takePending)).toList
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
    -- Annex B.3.4 lets a function declaration be the clause of an `if`, never a loop's body
    if ← atK "function" then fail "function declaration as the body of a loop"
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
    parseStmts n (acc.push s ++ (← takePending))

def parseBlock : Nat → P (List Stmt)
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    expectP "{"
    let before := (← get).realVars
    pushScope
    let inBlock := (← get).depth != (← get).topDepth
    let ss ← parseStmts n #[]
    popScope
    let after := (← get).realVars
    checkDecls ss (after.extract before.size after.size).toList inBlock
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
    if kind == .var then
      for x in target.names do
        addVar x
        addRealVar x
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
    -- `for await` (§14.7.5): in an async function only
    let t0 ← peek
    let isAwait ← if t0.kind == .ident && t0.text == "await" && !t0.escaped && (← get).inAsync then do
        advance; pure true
      else pure false
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
    let isOf := (← peek).kind == .ident && (← peek).text == "of" && !(← peek).escaped
    if isAwait && !isOf then fail "expected 'of' in a for await statement"
    if isOf || (← atK "in") then
      advance
      let obj ← if isOf then parseAssign n false else parseExpr n false
      expectP ")"
      pushScope (match init with | some (.decl .var _) => [] | some (.decl _ ds) => ds.flatMap Decl.names | _ => [])
      let body ← parseLoopBody n
      popScope
      let (kind, pat) ← match init with
        | some (.decl k [Decl.mk p none]) => pure (some k, p)
        | some (.decl .var [Decl.mk (.id x) (some _)]) =>
          if isOf || (← get).strict then fail "for-in/of declarations may not have initializers"
          pure (some DeclKind.var, Pat.id x)
        | some (.decl _ _) | some (.letOnce _) => fail "invalid for-in/of declaration"
        | some (.expr e) =>
          match exprToPat 64 e with
          | some p => pure (none, p)
          | none =>
            match e with
            | .call .. => if (← get).strict then fail "invalid left-hand side in for-in/of" else pure (none, Pat.target e)
            | _ => fail "invalid left-hand side in for-in/of"
        | none => fail "invalid for-in/of"
      if isAwait then return forAwaitStmt (← get).inGen t.pos kind pat obj body
      return if isOf then .forOf kind pat obj body else .forIn kind pat obj body
    expectP ";"
    let test ← if ← atP ";" then pure none else pure (some (← parseExpr n false))
    expectP ";"
    let update ← if ← atP ")" then pure none else pure (some (← parseExpr n false))
    expectP ")"
    pushScope (match init with | some (.decl .var _) => [] | some (.decl _ ds) => ds.flatMap Decl.names | _ => [])
    let body ← parseLoopBody n
    popScope
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
    parseCaseBody n (acc.push s ++ (← takePending))

/-- Parameters and body of a function, after its name. -/
def parseFunction : Nat → Option String → FunKind → Nat → P FunDef
  | 0, _, _, _ => fail "parser fuel exhausted"
  | n + 1, name, kind, gen => do
    expectP "("
    let outerGen := (← get).inGen
    modify fun s => { s with inGen := gen == 1 || gen == 3 }
    let (ps, rest) ← parseMethodParams n (kind != FunKind.normal)
    modify fun s => { s with inGen := outerGen }
    parseBody n name ps rest kind gen

/-- The parameter list of a function that is not an arrow function: `arguments` there is the
function's own, so the class-initialiser rule (§15.7.1) of an enclosing field initialiser or
static block does not reach into it. -/
def parseMethodParams : Nat → Bool → P (List PatElem × Option Pat)
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, method => do
    let o ← get
    -- `super` in the parameters of a method (or constructor) is the method's; a plain
    -- function's parameters have none
    modify fun s => { s with fieldInit := false, superCall := method, superProp := method, newTargetOk := true }
    let r ← parseParams n #[]
    modify fun s => { s with fieldInit := o.fieldInit, superCall := o.superCall, superProp := o.superProp,
                             newTargetOk := o.newTargetOk }
    return r

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
def parseBody : Nat → Option String → List PatElem → Option Pat → FunKind → Nat → P FunDef
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
    if !simple && hasUseStrict outer.toks (outer.pos + 1) then
      fail "a function with a 'use strict' directive needs a simple parameter list"
    if (strict || kind == .arrow || kind == .method || !simple) && names.eraseDups.length != names.length then
      fail "duplicate parameter name not allowed in this context"
    set { outer with vars := #[], varSet := {}, realVars := #[], usesArgs := false, strict, inFun := true, loops := 0,
                     breakables := 0, labels := [],
                     inGen := gen == 1 || gen == 3, inAsync := gen == 2 || gen == 3,
                     depth := 0, topDepth := 1, lexStack := [names], pending := #[],
                     fieldInit := outer.staticNext || (kind == FunKind.arrow && outer.fieldInit),
                     staticNext := false, superCall := superCallIn kind outer.superCall,
                     superProp := superPropIn kind outer.superProp,
                     newTargetOk := kind != FunKind.arrow || outer.newTargetOk }
    let body ← parseBlock n
    let inner ← get
    let usesArgs := inner.usesArgs
    let arrow := kind == .arrow
    set { inner with vars := outer.vars, varSet := outer.varSet, realVars := outer.realVars, strict := outer.strict, inFun := outer.inFun,
                     loops := outer.loops, breakables := outer.breakables, labels := outer.labels,
                     inGen := outer.inGen, inAsync := outer.inAsync, usesArgs := outer.usesArgs || (arrow && usesArgs),
                     depth := outer.depth, topDepth := outer.topDepth, lexStack := outer.lexStack,
                     pending := outer.pending, fieldInit := outer.fieldInit, staticNext := false,
                     superCall := outer.superCall, superProp := outer.superProp, newTargetOk := outer.newTargetOk }
    return FunDef.mk name params rest body inner.vars.toList (usesArgs && !arrow) strict kind
      (gen == 1 || gen == 3) (gen == 2 || gen == 3) {}

/-- An arrow function after its parameters and `=>`. -/
def parseArrowBody : Nat → List PatElem → Option Pat → Nat → P Expr
  | 0, _, _, _ => fail "parser fuel exhausted"
  | n + 1, params, rest, coro => do
    if ← atP "{" then return .func (← parseBody n none params rest .arrow coro)
    let outer ← get
    set { outer with vars := #[], varSet := {}, inFun := true, inAsync := coro == 2, inGen := false }
    let e ← parseAssign n false
    let inner ← get
    set { inner with vars := outer.vars, varSet := outer.varSet, inFun := outer.inFun, inAsync := outer.inAsync, inGen := outer.inGen }
    return .func (FunDef.mk none params rest [.ret (some e)] inner.vars.toList false outer.strict .arrow false (coro == 2) {})

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
        let arg ← parseAssign n noIn
        -- in an async generator `yield*` delegates to an async iterator (§15.5.5): the
        -- evaluator reads the `%await` form of the operand as that
        if (← get).inAsync then return .yieldE true (some (.call (.ident "%await") [arg]))
        return .yieldE true (some arg)
      let nt ← peek
      let ends := nt.nl || nt.kind == .eof || isP nt ")" || isP nt "]" || isP nt "}" ||
        isP nt "," || isP nt ";" || isP nt ":" || isK nt "in"
      if ends then return .yieldE false none
      return .yieldE false (some (← parseAssign n noIn))
    -- arrow functions
    if (t.kind == .ident || (t.kind == .kw && t.text == "yield")) && isP t2 "=>" && !t2.nl then
      if t.text == "async" then fail "async functions are not supported"
      advance; advance
      return ← parseArrowBody n [.mk (.id t.text) none] none 0
    if isP t "(" && arrowAhead (← get).toks (← get).pos then
      advance
      let (ps, rest) ← parseParams n #[]
      expectP "=>"
      return ← parseArrowBody n ps rest 0
    if t.kind == .ident && t.text == "async" && !t2.nl && t2.kind == .ident && isP (← peekAt 2) "=>" then
      advance
      let x ← bindingName
      expectP "=>"
      return ← parseArrowBody n [.mk (.id x) none] none 2
    if t.kind == .ident && t.text == "async" && !t2.nl && isP t2 "(" && arrowAhead (← get).toks ((← get).pos + 1) then
      advance; advance
      let (ps, rest) ← parseParams n #[]
      expectP "=>"
      return ← parseArrowBody n ps rest 2
    let lhs ← parseCond n noIn
    match assignOp (← peek) with
    | none => return lhs
    | some op =>
      if !(← targetOk lhs) then
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
    -- after an operand a `/` is a division: the lexer's first choice was a regular expression
    if (← peek).kind == .regex then relexAt false
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
      if op == .delete then
        -- §13.5.1.1: `delete o.#x` (with or without parentheses, also after `?.`)
        match e with
        | .member _ k | .chain (.member _ k) =>
          if isPrivKey k then fail "private fields can not be deleted"
        | _ => pure ()
      if op != .delete && op != .typeof && op != .void && (← atP "**") then
        fail "unary operator before '**' needs parentheses"
      return .unary op e
    | none =>
      if isP t "++" || isP t "--" then
        advance
        let e ← parseUnary n
        if !(← targetOk e) then fail "invalid update target"
        return .update true (t.text == "++") e
      if t.kind == .ident && t.text == "await" && !t.escaped && (← get).inAsync then
        advance
        let e ← parseUnary n
        if (← get).inGen then return .yieldE false (some (.call (.ident "%await") [e]))
        return .yieldE false (some e)
      parsePostfix n

def parsePostfix : Nat → P Expr
  | 0 => fail "parser fuel exhausted"
  | n + 1 => do
    let e ← parseLHS n
    let t ← peek
    if (isP t "++" || isP t "--") && !t.nl then
      if !(← targetOk e) then fail "invalid update target"
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
      if t.kind == .ident && t.text == "target" && !t.escaped then
        if !(← get).newTargetOk then fail "new.target is only valid in functions"
        advance; return .newTarget
      fail "expected new.target"
    -- `new import(...)`, `new import.source(...)`, `new import.defer(...)`: an ImportCall is not
    -- a MemberExpression (§13.3.10)
    if ← atK "import" then
      let t1 ← peekAt 1
      let t2 ← peekAt 2
      if isP t1 "(" || (isP t1 "." && t2.kind == .ident && (t2.text == "source" || t2.text == "defer")) then
        fail "an import call cannot be the target of 'new'"
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
      else if isP nt "#" then
        advance
        let pt ← peek
        if !(pt.kind == .ident || pt.kind == .kw) then fail "expected a private name"
        privAdjacent nt pt
        advance; usePriv (privKey pt.text); parseTail n (.member e (privKey pt.text)) allowCall
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
    else if isP t "?." then
      -- Optional chaining (§13.3.9): the rest of the chain is inside one `chain`.
      advance
      let nt ← peek
      let first ← if isP nt "(" then do
          advance; pure (Expr.call (.optCallee e) (← parseArgs n []))
        else if isP nt "[" then do
          advance
          let k ← parseExpr n false
          expectP "]"
          pure (Expr.index (.optBase e) k)
        else if nt.kind == .ident || nt.kind == .kw then do
          advance; pure (Expr.member (.optBase e) nt.text)
        else if isP nt "#" then do
          advance
          let pt ← peek
          if !(pt.kind == .ident || pt.kind == .kw) then fail "expected a private name"
          privAdjacent nt pt
          advance; usePriv (privKey pt.text); pure (Expr.member (.optBase e) (privKey pt.text))
        else fail "expected a property name after ?."
      if (← peek).kind == .tmpl then fail "Invalid tagged template on optional chain"
      return .chain (← parseTail n first allowCall)
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
    | .regex => advance; return .regex t.text t.flags
    | .tmpl =>
      advance
      let subs ← parseSubs n t.tmpl.subs.toList []
      return .template t.tmpl.cooked.toList subs
    | .ident =>
      if t.text == "async" && !t.escaped && isK (← peekAt 1) "function" && !(← peekAt 1).nl then
        advance; advance
        let g ← eatP "*"
        let name ← if (← peek).kind == .ident then pure (some (← bindingName)) else pure none
        return .func (← parseFunction n name .normal (if g then 3 else 2))
      if t.escaped && (keywords.contains t.text ||
          ((← get).strict && ["implements", "interface", "package", "private", "protected",
            "public", "static", "yield", "let"].contains t.text)) then
        fail s!"keyword '{t.text}' must not contain escapes"
      if t.text == "await" && (← get).inAsync then fail "'await' is not an identifier in an async function"
      if (t.text == "yield" && ((← get).inGen || (← get).strict)) || (t.text == "let" && (← get).strict) then
        fail s!"'{t.text}' is not an identifier here"
      advance
      if t.text == "arguments" then
        if (← get).fieldInit then fail "'arguments' is not allowed in a class field initializer or static block"
        modify fun s => { s with usesArgs := true }
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
        return .func (← parseFunction n name .normal (if gen then 1 else 0))
      | "let" | "yield" =>
        -- an identifier in code that is not strict; `yield` is never one in a generator
        -- (a YieldExpression is read by `parseAssign`, not as an operand)
        let st ← get
        if st.strict || (t.text == "yield" && st.inGen) then fail s!"'{t.text}' is not an identifier here"
        advance; return .ident t.text
      | "class" =>
        advance
        let name ← if (← peek).kind == .ident then pure (some (← classBindingName)) else pure none
        return .classE (← parseClass n name)
      | "super" =>
        advance
        if ← atP "(" then
          if (← get).fieldInit then fail "'super()' is not allowed in a class field initializer or static block"
          if !(← get).superCall then fail "'super()' is only valid in the constructor of a derived class"
          advance; return .superCall (← parseArgs n [])
        if !(← get).superProp then fail "'super' property access is only valid in methods"
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
      | "import" =>
        advance
        if ← atP "." then
          advance
          let mt ← peek
          if mt.kind == .ident && mt.text == "meta" && !mt.escaped && (← get).module then
            advance
            modify fun s => { s with usesMeta := true }
            return .ident metaName
          -- `import.source(x)` and `import.defer(x)` (the source phase and deferred import
          -- proposals): an ImportCall with a phase; read as `import(x)`
          if mt.kind == .ident && (mt.text == "source" || mt.text == "defer") && !mt.escaped &&
              isP (← peekAt 1) "(" then
            advance
          else fail "'import.meta' may only be used in module code"
        if ← atP "(" then
          -- ImportCall (§13.3.10): a specifier and, optionally, an options argument
          advance
          let spec ← parseAssign n false
          if ← eatP "," then
            if !(← atP ")") then
              let _ ← parseAssign n false
              let _ ← eatP ","
          expectP ")"
          return .call (.ident dynImportName) [spec]
        fail "unexpected 'import'"
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
      | "/" | "/=" =>
        -- where a primary expression starts a `/` is the start of a regular expression literal:
        -- the lexer's first choice was a division
        relexAt true
        let r ← peek
        if r.kind == .regex then advance; return .regex r.text r.flags
        fail "unexpected token"
      | "#" =>
        -- `#x in o` (§13.10.1)
        advance
        let pt ← peek
        if !(pt.kind == .ident || pt.kind == .kw) || !isK (← peekAt 1) "in" then fail "unexpected private name"
        privAdjacent t pt
        advance; usePriv (privKey pt.text); return privIn (privKey pt.text)
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
    if isP t "#" then
      advance
      let nt ← peek
      if nt.kind == .ident || nt.kind == .kw then
        privAdjacent t nt
        if nt.text == "constructor" then fail "'#constructor' is not a valid private name"
        advance; return .lit (privKey nt.text)
      fail "expected a private name"
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
        let (ps, rest) ← parseMethodParams n true
        if !accessorParamsOk (t.text == "get") ps.length rest.isSome then fail "wrong number of accessor parameters"
        let f ← parseBody n none ps rest .method 0
        pure (if t.text == "get" then PropDef.getter k f else PropDef.setter k f)
      else if isP t "*" then
        advance
        let k ← parsePropKey n
        expectP "("
        let og := (← get).inGen
        let (ps, rest) ← parseMethodParams n true
        let f ← parseBody n none ps rest .method 1
        modify fun s => { s with inGen := og }
        pure (PropDef.init k (.func f))
      else if t.kind == .ident && t.text == "async" && !t.escaped && !t2.nl && !(isP t2 ":" || isP t2 "(" || isP t2 "," || isP t2 "}" || isP t2 "=") then
        advance
        let g ← eatP "*"
        let k ← parsePropKey n
        expectP "("
        let og := (← get).inAsync
        let (ps, rest) ← parseMethodParams n true
        let f ← parseBody n none ps rest .method (if g then 3 else 2)
        modify fun s => { s with inAsync := og }
        pure (PropDef.init k (.func f))
      else if t.kind == .ident && (isP t2 "," || isP t2 "}") then
        if t.escaped && keywords.contains t.text then fail s!"keyword '{t.text}' must not contain escapes"
        -- a shorthand property is an IdentifierReference (§13.2.5.1, §13.1.1)
        let s ← get
        if s.strict && strictReserved.contains t.text then fail s!"'{t.text}' is a reserved word in strict mode code"
        if (s.inGen || s.strict) && t.text == "yield" then fail "'yield' is not a valid identifier here"
        if s.inAsync && t.text == "await" then fail "'await' is not a valid identifier here"
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
          let (ps, rest) ← parseMethodParams n true
          pure (PropDef.init k (.func (← parseBody n none ps rest .method 0)))
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
    let cs := src.toList.toArray
    match lexChars cs with
    | .error e => throw e
    | .ok toks =>
      let outer ← get
      set { outer with toks, pos := 0, src := cs }
      let e ← parseExpr n false
      if (← peek).kind != .eof then fail "unexpected token in template substitution"
      modify fun s => { s with toks := outer.toks, pos := outer.pos, src := outer.src }
      parseSubs n rest (e :: acc)

/-- A class body after the name (§15.7). Class code is strict. -/
def parseClass : Nat → Option String → P ClassDef
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, name => do
    let outerStrict := (← get).strict
    modify fun s => { s with strict := true }
    let heritage ← if ← atK "extends" then advance; pure (some (← parseLHS n)) else pure none
    expectP "{"
    let outer ← get
    set { outer with classDepth := outer.classDepth + 1, privRefs := [] }
    let (ctor, members) ← parseMembers n heritage.isSome none []
    -- §15.7.1: a private name is declared once (a getter and a setter may share one, both
    -- static or both not), and every private name used is declared by this class or one around it
    let declared := members.filterMap fun m => match m with
      | .mk st kind (.lit k) _ => if isPrivKey k then some (k, st, kind) else none
      | _ => none
    let clash := declared.zipIdx.any fun ((k, st, kind), i) =>
      declared.zipIdx.any fun ((k2, st2, kind2), j) =>
        i < j && k == k2 && !(st == st2 && ((kind == .getter && kind2 == .setter) || (kind == .setter && kind2 == .getter)))
    if clash then fail "a private name is declared twice"
    let unresolved := (← get).privRefs.filter fun k => !declared.any (·.1 == k)
    if outer.classDepth == 0 && !outer.privAny then
      if let some k := unresolved.head? then
        fail s!"private name #{(k.drop 1).toString} is not declared in an enclosing class"
    modify fun s => { s with strict := outerStrict, classDepth := outer.classDepth,
                             privRefs := unresolved.foldl (fun acc k => if acc.contains k then acc else k :: acc) outer.privRefs }
    return .mk name heritage ctor members

def parseMembers : Nat → Bool → Option FunDef → List Member → P (Option FunDef × List Member)
  | 0, _, _, _ => fail "parser fuel exhausted"
  | n + 1, derived, ctor, acc => do
    if ← atP "}" then advance; return (ctor, acc.reverse)
    if ← atP ";" then advance; return ← parseMembers n derived ctor acc
    let t0 ← peek
    let t1 ← peekAt 1
    let static := t0.kind == .ident && t0.text == "static" && !t0.escaped &&
      !(isP t1 "(" || isP t1 "=" || isP t1 ";" || isP t1 "}")
    if static then advance
    if static && (← atP "{") then
      modify fun s => { s with staticNext := true }
      let f ← parseBody n none [] none .method 0
      return ← parseMembers n derived ctor (.mk true .staticBlock (.lit "") f :: acc)
    let t ← peek
    let t2 ← peekAt 1
    let gen := isP t "*"
    if gen then advance
    let t ← peek
    let t2 ← peekAt 1
    let isAsync := t.kind == .ident && t.text == "async" && !t.escaped && !t2.nl && !(isP t2 "(" || isP t2 "=" || isP t2 ";" || isP t2 "}")
    let mut gen := gen
    if isAsync then
      advance
      if ← eatP "*" then gen := true
    let accessor := t.kind == .ident && (t.text == "get" || t.text == "set") && !t.escaped &&
      !(isP t2 "(" || isP t2 "=" || isP t2 ";" || isP t2 "}")
    if accessor then advance
    let kt ← peek
    let k ← parsePropKey n
    -- §15.7.1: PropName "constructor" names the constructor, never a special method or a
    -- field; a static member is never "prototype" (and a static field never "constructor")
    let isField := !(← atP "(")
    if !classElementOk static (accessor || gen || isAsync) isField k then
      fail "a class element has a name it may not have"
    if ← atP "(" then
      advance
      let (ps, rest) ← parseMethodParams n true
      let isCtor := !static && !accessor && (kt.kind == .ident || kt.kind == .kw || kt.kind == .str) && kt.text == "constructor"
      if isCtor then
        if ctor.isSome then fail "a class may only have one constructor"
        let f ← parseBody n none ps rest (.ctor derived) 0
        return ← parseMembers n derived (some f) acc
      if accessor && !accessorParamsOk (t.text == "get") ps.length rest.isSome then
        fail "wrong number of accessor parameters"
      let f ← parseBody n none ps rest .method (if isAsync && gen then 3 else if isAsync then 2 else if gen then 1 else 0)
      let kind := if accessor then (if t.text == "get" then MemberKind.getter else .setter) else .method
      parseMembers n derived ctor (.mk static kind k f :: acc)
    else
      if accessor then fail "expected '('"
      -- a field: its initialiser is the body of a method that returns it
      let outer ← get
      set { outer with vars := #[], varSet := {}, inFun := true, fieldInit := true, superProp := true, newTargetOk := true }
      let init ← if ← atP "=" then advance; pure (some (← parseAssign n false)) else pure none
      set { (← get) with vars := outer.vars, varSet := outer.varSet, inFun := outer.inFun, fieldInit := outer.fieldInit,
                         superProp := outer.superProp, newTargetOk := outer.newTargetOk }
      semi
      let f := FunDef.mk none [] none [.ret init] [] false true .method false false {}
      parseMembers n derived ctor (.mk static .field k f :: acc)

end

/-- Fuel for a token count: each token is passed by a bounded number of calls
on any path from the root. `parseScript` gives the character count plus one, which no reading
of the source has more tokens than (`P.relexAt` can change the count). -/
def parseFuel (tokens : Nat) : Nat := 64 * tokens + 1024

/-- Parse a script (§16.1). `strict` forces strict mode code. -/
def parseScript (src : String) (strict : Bool := false) (evalCode : Bool := false) :
    Except String Script :=
  let cs := src.toList.toArray
  match lexChars cs with
  | .error e => .error e
  | .ok toks =>
    let toks := internToks toks
    let strict := strict || hasUseStrict toks 0
    -- global code has no super and no new.target (§16.1.1); eval code may be in a method
    let st : PState := { toks, strict, src := cs, privAny := evalCode, superCall := evalCode,
                         superProp := evalCode, newTargetOk := evalCode }
    match (parseStmts (parseFuel (cs.size + 1)) #[]).run st with
    | .ok body st' =>
      if (st'.toks.getD st'.pos default).kind != .eof then
        .error s!"SyntaxError: unexpected '{(st'.toks.getD st'.pos default).text}'"
      else if !evalCode && !st'.privRefs.isEmpty then
        .error "SyntaxError: a private name is used outside a class"
      else
        let lex := lexNames body
        let funs := body.flatMap fun s => match s with | .funDecl x _ => [x] | _ => []
        if lex.eraseDups.length != lex.length || lex.any (fun x => st'.vars.contains x || funs.contains x) then
          .error "SyntaxError: identifier has already been declared"
        else .ok { body, vars := st'.vars.toList, strict }
    | .error e _ => .error e

/-! ## Modules (§16.2)

`parseModule` reads a module: its import and export declarations become records (ParseModule,
§16.2.1.6.1), and its statements stay, with the `export` keywords taken off. The linker and the
evaluator are `JS/Modules.lean`. Module code is strict; `import.meta` reads `metaName`. -/

/-- What an import binds (§16.2.1.6, ImportEntry `[[ImportName]]`): one export, or the
module's namespace (`import * as x`). -/
inductive ImportName where
  | named (s : String)
  | ns
  deriving BEq, Repr, Inhabited, DecidableEq

/-- `import {name as localName} from "spec"`. -/
structure ImportEntry where
  spec : String
  name : ImportName
  localName : String
  deriving Repr, Inhabited, BEq

/-- The binding of an anonymous default export (`export default 1`, `export default
function () {}`): not an identifier, so module code cannot name it (§16.2.3.7 "*default*"). -/
def defaultLocal : String := "*default*"

/-- A parsed module (the Source Text Module Record's static fields, §16.2.1.6). -/
structure ModuleSyntax where
  /-- The statements: import declarations removed, export keywords taken off. -/
  body : List Stmt
  /-- The `var` and top-level function names. -/
  vars : List String
  /-- `[[RequestedModules]]`: the specifiers in source order, each once. -/
  requests : Array String := #[]
  imports : Array ImportEntry := #[]
  /-- `[[LocalExportEntries]]`: export name and local binding name. -/
  localExports : Array (String × String) := #[]
  /-- `[[IndirectExportEntries]]`: export name, specifier and import name (`.ns` for
  `export * as x from`). -/
  indirect : Array (String × String × ImportName) := #[]
  /-- `[[StarExportEntries]]`: `export * from "spec"`. -/
  stars : Array String := #[]
  usesMeta : Bool := false
  deriving Inhabited

namespace ModuleParse
open P

structure Acc where
  body : Array Stmt := #[]
  requests : Array String := #[]
  imports : Array ImportEntry := #[]
  localExports : Array (String × String) := #[]
  indirect : Array (String × String × ImportName) := #[]
  stars : Array String := #[]
  deriving Inhabited

def Acc.request (a : Acc) (s : String) : Acc :=
  if a.requests.contains s then a else { a with requests := a.requests.push s }

/-- An identifier that is not a keyword, with no escapes: `from`, `as`. -/
def contextual (t : Token) (w : String) : Bool := t.kind == .ident && t.text == w && !t.escaped

/-- A ModuleExportName (§16.2.2): an identifier name or a string literal. -/
def exportName : P String := do
  let t ← peek
  if t.kind == .ident || t.kind == .kw || t.kind == .str then advance; pure t.text
  else fail "expected an export name"

/-- `with { type: "json" }` after a specifier (import attributes). Only no attributes are
supported: a JSON or CSS module is refused, as an unknown `type` must be. -/
def attributes : P Unit := do
  if !(← atK "with") then return
  fail "import attributes are not supported (JSON and CSS modules)"

/-- `from "specifier"`. -/
def fromClause : P String := do
  if !contextual (← peek) "from" then fail "expected 'from'"
  advance
  let s ← peek
  if s.kind != .str then fail "expected a module specifier"
  advance
  attributes
  pure s.text

/-- `{ a, b as c, "d" as e }` of an import, after the `{`. -/
def importSpecs : Nat → Array (ImportName × String) → P (Array (ImportName × String))
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, acc => do
    if ← eatP "}" then return acc
    let acc ← if contextual (← peekAt 1) "as" then do
        let name ← exportName
        advance
        pure (acc.push (.named name, ← bindingName))
      else do
        let x ← bindingName
        pure (acc.push (.named x, x))
    if ← eatP "," then importSpecs n acc else do expectP "}"; pure acc

/-- `{ a, b as c }` of an export, after the `{`: the name in the module (or in the other module,
with `from`), the export name, and whether the first is an identifier (only then may it be a
local name). -/
def exportSpecs : Nat → Array (String × String × Bool) → P (Array (String × String × Bool))
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, acc => do
    if ← eatP "}" then return acc
    let t ← peek
    let loc ← exportName
    let ident := t.kind == .ident && !t.escaped &&
      !["implements", "interface", "package", "private", "protected", "public", "static", "yield", "let", "await",
        "eval", "arguments"].contains t.text
    let exported ← if contextual (← peek) "as" then do advance; exportName else pure loc
    let acc := acc.push (loc, exported, ident)
    if ← eatP "," then exportSpecs n acc else do expectP "}"; pure acc

/-- The name of an anonymous function or class in `export default` (NamedEvaluation with
"default", §16.2.3.7). -/
def namedDefault (e : Expr) : Expr :=
  match e with
  | .func f => if f.name.isNone then .func (f.withName "default") else e
  | .classE (.mk none h c ms) => .classE (.mk (some "default") h c ms)
  | _ => e

/-- An import declaration, after `import` (§16.2.2). -/
def importDecl (n : Nat) (a : Acc) : P Acc := do
  let t ← peek
  if t.kind == .str then
    advance
    attributes
    semi
    return a.request t.text
  let mut entries : Array (ImportName × String) := #[]
  let mut more := true
  if !(isP t "*" || isP t "{") then
    entries := entries.push (.named "default", ← bindingName)
    more ← eatP ","
  if more then
    if ← eatP "*" then
      if !contextual (← peek) "as" then fail "expected 'as'"
      advance
      entries := entries.push (.ns, ← bindingName)
    else if ← eatP "{" then
      entries ← importSpecs n entries
    else fail "expected '*' or '{'"
  let spec ← fromClause
  semi
  let a := a.request spec
  return { a with imports := a.imports ++ entries.map fun (nm, l) => { spec, name := nm, localName := l } }

/-- An export declaration, after `export` (§16.2.3). -/
def exportDecl (n : Nat) (a : Acc) : P Acc := do
  let t ← peek
  if isP t "*" then
    advance
    if contextual (← peek) "as" then
      advance
      let name ← exportName
      let spec ← fromClause
      semi
      let a := a.request spec
      return { a with indirect := a.indirect.push (name, spec, .ns) }
    let spec ← fromClause
    semi
    let a := a.request spec
    return { a with stars := a.stars.push spec }
  if isP t "{" then
    advance
    let specs ← exportSpecs n #[]
    if contextual (← peek) "from" then
      let spec ← fromClause
      semi
      let a := a.request spec
      return { a with indirect := a.indirect ++ specs.map fun (l, e, _) => (e, spec, .named l) }
    semi
    if specs.any (fun (_, _, ok) => !ok) then fail "an exported local name must be an identifier"
    return { a with localExports := a.localExports ++ specs.map fun (l, e, _) => (e, l) }
  if isK t "default" then
    advance
    let t ← peek
    let t2 ← peekAt 1
    if isK t "function" || (contextual t "async" && isK t2 "function" && !t2.nl) then
      let isAsync := !isK t "function"
      if isAsync then advance
      advance
      let gen ← eatP "*"
      let mode := (if isAsync then 2 else 0) + (if gen then 1 else 0)
      if (← peek).kind == .ident then
        let name ← bindingName
        addVar name
        let f ← parseFunction n (some name) .normal mode
        return { a with body := a.body.push (.funDecl name f), localExports := a.localExports.push ("default", name) }
      addVar defaultLocal
      let f ← parseFunction n (some "default") .normal mode
      return { a with body := a.body.push (.funDecl defaultLocal f),
                      localExports := a.localExports.push ("default", defaultLocal) }
    if isK t "class" then
      advance
      if (← peek).kind == .ident then
        let name ← bindingName
        let c ← parseClass n (some name)
        return { a with body := a.body.push (.classDecl name c), localExports := a.localExports.push ("default", name) }
      let c ← parseClass n (some "default")
      return { a with body := a.body.push (.classDecl defaultLocal c),
                      localExports := a.localExports.push ("default", defaultLocal) }
    let e ← parseAssign n false
    semi
    return { a with body := a.body.push (.decl .constK [.mk (.id defaultLocal) (some (namedDefault e))]),
                    localExports := a.localExports.push ("default", defaultLocal) }
  let t2 ← peekAt 1
  let declares := isK t "var" || isK t "const" || isK t "function" || isK t "class" ||
    (contextual t "let") || (contextual t "async" && isK t2 "function" && !t2.nl)
  if !declares then fail "unexpected token after 'export'"
  let s ← parseStmt n
  let names := match s with
    | .decl _ ds => ds.flatMap Decl.names
    | .funDecl x _ | .classDecl x _ => [x]
    | _ => []
  return { a with body := a.body.push s, localExports := a.localExports ++ (names.map fun x => (x, x)).toArray }

/-- The module items to the end of the input. -/
def items : Nat → Acc → P Acc
  | 0, _ => fail "parser fuel exhausted"
  | n + 1, a => do
    let t ← peek
    if t.kind == .eof then return a
    let t2 ← peekAt 1
    if isK t "import" && !(isP t2 "(" || isP t2 ".") then
      advance
      items n (← importDecl n a)
    else if isK t "export" then
      advance
      items n (← exportDecl n a)
    else
      let s ← parseStmt n
      items n { a with body := a.body.push s }

/-- The early errors of a module (§16.2.1.1), and the local exports of imported names made
indirect (ParseModule step 10). -/
def finish (a : Acc) (vars : List String) (usesMeta : Bool) : Except String ModuleSyntax := do
  let body := a.body.toList
  let lex := lexNames body
  let funs := body.flatMap fun s => match s with | .funDecl x _ => [x] | _ => []
  let imported := a.imports.toList.map (·.localName)
  let declared := lex ++ imported
  if declared.eraseDups.length != declared.length || declared.any (fun x => vars.contains x || funs.contains x) then
    throw "SyntaxError: identifier has already been declared"
  let names := a.localExports.toList.map (·.1) ++ a.indirect.toList.map (·.1)
  if names.eraseDups.length != names.length then throw "SyntaxError: duplicate export name"
  for (e, l) in a.localExports do
    if !(lex.contains l || vars.contains l || imported.contains l) then
      throw s!"SyntaxError: export '{e}' is not defined in the module"
  -- an exported import of one name is an indirect export; of a namespace, a local one
  let mut locals : Array (String × String) := #[]
  let mut indirect := a.indirect
  for (e, l) in a.localExports do
    match a.imports.find? (·.localName == l) with
    | some { spec, name := .named nm, .. } => indirect := indirect.push (e, spec, .named nm)
    | _ => locals := locals.push (e, l)
  return { body, vars, requests := a.requests, imports := a.imports, localExports := locals, indirect,
           stars := a.stars, usesMeta }

end ModuleParse

/-- Parse a module (§16.2.1.6.1 ParseModule). Module code is strict. -/
def parseModule (src : String) : Except String ModuleSyntax :=
  let cs := src.toList.toArray
  match lexChars cs with
  | .error e => .error e
  | .ok toks =>
    let toks := internToks toks
    let st : PState := { toks, strict := true, src := cs, module := true }
    match (ModuleParse.items (parseFuel (cs.size + 1)) {}).run st with
    | .ok a st' => ModuleParse.finish a st'.vars.toList st'.usesMeta
    | .error e _ => .error e

end L4Factoidal.JS
