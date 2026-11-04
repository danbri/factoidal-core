/-
L4Factoidal.SQL.Syntax — the SQL subset that the W3C RDB2RDF test cases use:
values, datatypes, the lexer and the parser of statements and queries.

Spec: ISO/IEC 9075-2:2008 (SQL:2008 Part 2, "Foundation"): §5.2 tokens and
identifiers, §5.3 literals, §6 scalar expressions, §7 query expressions, §11
schema definition (CREATE TABLE, ALTER TABLE), §14 data manipulation (INSERT).
Only the forms that the corpus uses are read; every other form is a parse
error that names it. Design record:
`docs/designissues/2026-11-01-r2rml-and-direct-mapping.md` §1.

## Identifiers (SQL:2008 §5.2, syntax rules 13 and 14)

A regular identifier is folded to upper case: `Name` and `NAME` are the same
identifier as the delimited `"NAME"`. A delimited identifier keeps its case.
`Ident.norm` is the folded form; tables and columns are found by it.

## Termination

The lexer is a tail-recursive loop over the characters. The parser is a
recursive descent over the token list with a fuel argument: each call
decreases the fuel, and the entry points give the fuel `4 * tokens + 8`, more
than any parse of the subset needs (each token is consumed by at most a
constant number of nested calls). A parse that runs out of fuel is an error,
never a partial result.

Tracking: https://github.com/danbri/factoidal/issues/1165.
-/

namespace L4Factoidal.SQL

/-! ## Datatypes and values -/

/-- The SQL datatypes of the subset (SQL:2008 §4.2 to §4.6). -/
inductive SqlType where
  | integer
  | decimal
  | double
  | varchar
  | char (len : Nat)
  | boolean
  | date
  | timestamp
  | binary
  deriving DecidableEq, Repr, Inhabited

/-- A SQL value. An approximate numeric (REAL, FLOAT, DOUBLE) is held as the
    exact decimal of the literal that made it, `mant × 10^(-scale)`; this
    record does not model binary rounding (design record §1). -/
inductive Value where
  | null
  | int (i : Int)
  | dec (mant : Int) (scale : Nat)
  | dbl (mant : Int) (scale : Nat)
  | str (s : String)
  | bool (b : Bool)
  | date (s : String)
  | timestamp (s : String)
  | bin (hex : String)
  deriving DecidableEq, Repr, Inhabited

/-! ## Tokens -/

inductive Tok where
  /-- An identifier: its text and whether it was delimited (`"..."`). -/
  | ident (s : String) (delimited : Bool)
  | str (s : String)
  | num (s : String)
  | hex (s : String)
  | sym (s : String)
  deriving DecidableEq, Repr, Inhabited

/-- An identifier as written, and its normal form (SQL:2008 §5.2). -/
structure Ident where
  text : String
  delimited : Bool
  deriving DecidableEq, Repr, Inhabited

def Ident.norm (i : Ident) : String :=
  if i.delimited then i.text else i.text.toUpper

def Ident.regular (s : String) : Ident := { text := s, delimited := false }

def isIdStart (c : Char) : Bool := c.isAlpha || c == '_' || c.toNat > 0x7F
def isIdPart (c : Char) : Bool := isIdStart c || c.isDigit || c == '$'

/-- Read up to the closing quote `q`; a doubled quote is one quote character
    (SQL:2008 §5.3, `<quote symbol>`; §5.2, `<doublequote symbol>`). -/
def readQuoted (q : Char) : List Char → List Char → Option (String × List Char)
  | [], _ => none
  | c :: d :: rest, acc =>
      if c == q then
        if d == q then readQuoted q rest (q :: acc)
        else some (String.ofList acc.reverse, d :: rest)
      else readQuoted q (d :: rest) (c :: acc)
  | [c], acc => if c == q then some (String.ofList acc.reverse, []) else none

def spanChars (p : Char → Bool) : List Char → List Char → List Char × List Char
  | [], acc => (acc.reverse, [])
  | c :: rest, acc => if p c then spanChars p rest (c :: acc) else (acc.reverse, c :: rest)

def dropLine : List Char → List Char
  | [] => []
  | '\n' :: rest => rest
  | _ :: rest => dropLine rest

def twoCharSyms : List String := ["||", "<=", ">=", "<>", "!="]

/-- The lexer. `--` comments run to the end of the line. Each step consumes
    at least one character, so a fuel of the input length is enough. -/
def lexLoop : Nat → List Char → List Tok → Except String (List Tok)
  | _, [], acc => .ok acc.reverse
  | 0, _ :: _, _ => .error "lexer fuel exhausted"
  | fuel + 1, c :: rest, acc =>
    if c.isWhitespace then lexLoop fuel rest acc
    else if c == '-' && rest.head? == some '-' then lexLoop fuel (dropLine rest) acc
    else if c == '\'' then
      match readQuoted '\'' rest [] with
      | some (s, r) => lexLoop fuel r (.str s :: acc)
      | none => .error "unterminated string literal"
    else if c == '"' then
      match readQuoted '"' rest [] with
      | some (s, r) => lexLoop fuel r (.ident s true :: acc)
      | none => .error "unterminated delimited identifier"
    else if (c == 'X' || c == 'x') && rest.head? == some '\'' then
      match readQuoted '\'' rest.tail [] with
      | some (s, r) => lexLoop fuel r (.hex s.toUpper :: acc)
      | none => .error "unterminated binary string literal"
    else if c.isDigit || (c == '.' && (rest.head?.map Char.isDigit).getD false) then
      let (ds, r) := spanChars (fun d => d.isDigit || d == '.') (c :: rest) []
      let (ex, r) := match r with
        | e :: r' =>
          if e == 'e' || e == 'E' then
            match r' with
            | s :: r'' =>
              if s == '+' || s == '-' then
                let (es, r3) := spanChars Char.isDigit r'' []
                ([e, s] ++ es, r3)
              else
                let (es, r3) := spanChars Char.isDigit r' []
                (e :: es, r3)
            | [] => ([], r)
          else ([], r)
        | [] => ([], r)
      lexLoop fuel r (.num (String.ofList (ds ++ ex)) :: acc)
    else if isIdStart c then
      let (w, r) := spanChars isIdPart (c :: rest) []
      lexLoop fuel r (.ident (String.ofList w) false :: acc)
    else
      match rest with
      | d :: r' =>
        let two := String.ofList [c, d]
        if twoCharSyms.contains two then lexLoop fuel r' (.sym two :: acc)
        else if "(),;.*=<>+-/".toList.contains c then lexLoop fuel rest (.sym (String.singleton c) :: acc)
        else .error s!"unexpected character '{c}'"
      | [] =>
        if "(),;.*=<>+-/".toList.contains c then lexLoop fuel rest (.sym (String.singleton c) :: acc)
        else .error s!"unexpected character '{c}'"

def lex (s : String) : Except String (List Tok) := lexLoop (s.length + 1) s.toList []

/-! ## Abstract syntax -/

inductive Expr where
  | lit (v : Value)
  /-- A column reference, optionally qualified by a table name. -/
  | col (qual : Option Ident) (name : Ident)
  | concat (a b : Expr)
  | cmp (op : String) (a b : Expr)
  | and (a b : Expr)
  | or (a b : Expr)
  | not (a : Expr)
  | isNull (a : Expr) (negated : Bool)
  /-- `CASE operand WHEN v THEN r ... ELSE e END`; with no operand, each
      `WHEN` is a condition (SQL:2008 §6.11). -/
  | case (operand : Option Expr) (branches : List (Expr × Expr)) (els : Option Expr)
  /-- `COUNT(e)`, or `COUNT(*)` when `none` (SQL:2008 §10.9). -/
  | count (arg : Option Expr)
  deriving Repr, Inhabited

inductive SelItem where
  | star
  | qualStar (t : Ident)
  | expr (e : Expr) (alias : Option Ident)
  deriving Repr, Inhabited

structure TableRef where
  name : Ident
  alias : Option Ident
  deriving Repr, Inhabited

structure Query where
  distinct : Bool
  items : List SelItem
  «from» : List TableRef
  «where» : Option Expr
  groupBy : List Expr
  deriving Repr, Inhabited

structure ColumnDef where
  name : Ident
  type : SqlType
  deriving Repr, Inhabited

structure ForeignKey where
  cols : List Ident
  refTable : Ident
  refCols : List Ident
  deriving Repr, Inhabited

/-- One element of a CREATE TABLE body. -/
inductive TableElem where
  | column (c : ColumnDef) (pk unique : Bool) (fk : Option (Ident × Ident))
  | primaryKey (cols : List Ident)
  | unique (cols : List Ident)
  | foreignKey (fk : ForeignKey)
  deriving Repr, Inhabited

inductive Stmt where
  | createTable (name : Ident) (elems : List TableElem)
  | dropTable (name : Ident)
  | addForeignKey (table : Ident) (fk : ForeignKey)
  | addPrimaryKey (table : Ident) (cols : List Ident)
  | insert (table : Ident) (cols : Option (List Ident)) (rows : List (List Expr))
  | select (q : Query)
  deriving Repr, Inhabited

/-! ## Parser -/

abbrev P (α : Type) := List Tok → Except String (α × List Tok)

def isKw (k : String) : Tok → Bool
  | .ident s false => s.toUpper == k
  | _ => false

def peekKw (k : String) (ts : List Tok) : Bool := (ts.head?.map (isKw k)).getD false

def expectKw (k : String) : P Unit
  | t :: ts => if isKw k t then .ok ((), ts) else .error s!"expected {k}, found {repr t}"
  | [] => .error s!"expected {k}, found end of input"

def peekSym (s : String) (ts : List Tok) : Bool := ts.head? == some (.sym s)

def expectSym (s : String) : P Unit
  | t :: ts => if t == .sym s then .ok ((), ts) else .error s!"expected '{s}', found {repr t}"
  | [] => .error s!"expected '{s}', found end of input"

/-- Words that end an expression or a select item and so are not aliases. -/
def reserved : List String :=
  ["SELECT", "FROM", "WHERE", "GROUP", "BY", "ORDER", "AND", "OR", "NOT", "AS",
   "CASE", "WHEN", "THEN", "ELSE", "END", "IS", "NULL", "TRUE", "FALSE", "ON",
   "JOIN", "INNER", "LEFT", "RIGHT", "OUTER", "UNION", "HAVING", "DISTINCT",
   "VALUES", "INTO", "LIMIT"]

def identOf : Tok → Option Ident
  | .ident s d => if !d && reserved.contains s.toUpper then none else some { text := s, delimited := d }
  | _ => none

def parseIdent : P Ident
  | t :: ts => match identOf t with
    | some i => .ok (i, ts)
    | none => .error s!"expected an identifier, found {repr t}"
  | [] => .error "expected an identifier, found end of input"

/-- A comma-separated list in parentheses, of identifiers. -/
def parseIdentListLoop : Nat → List Ident → P (List Ident)
  | 0, _ => fun _ => .error "parser fuel exhausted"
  | n + 1, acc => fun ts => do
    let (i, ts) ← parseIdent ts
    if peekSym "," ts then parseIdentListLoop n (i :: acc) ts.tail
    else .ok ((i :: acc).reverse, ts)

def parseParenIdents : P (List Ident) := fun ts => do
  let ((), ts) ← expectSym "(" ts
  let (is, ts) ← parseIdentListLoop (ts.length + 1) [] ts
  let ((), ts) ← expectSym ")" ts
  .ok (is, ts)

/-- `mant` and `scale` of a decimal lexeme `d.d`. -/
def decimalOf (s : String) : Option (Int × Nat) :=
  match s.splitOn "." with
  | [a] => a.toNat?.map (fun n => ((n : Int), 0))
  | [a, b] =>
      let a' := if a.isEmpty then "0" else a
      match (a' ++ b).toNat? with
      | some n => some ((n : Int), b.length)
      | none => none
  | _ => none

/-- A numeric literal: an exact integer, an exact decimal, or (with an
    exponent) an approximate numeric (SQL:2008 §5.3). -/
def numValue (s : String) : Option Value :=
  let parts := (s.toUpper).splitOn "E"
  match parts with
  | [m] => if m.contains '.' then (decimalOf m).map (fun (a, b) => .dec a b)
           else m.toNat?.map (fun n => .int n)
  | [m, e] =>
      let (neg, e') := if e.startsWith "-" then (true, e.drop 1) else (false, (if e.startsWith "+" then e.drop 1 else e))
      match decimalOf m, e'.toString.toNat? with
      | some (a, sc), some k =>
          if neg then some (.dbl a (sc + k))
          else if k ≤ sc then some (.dbl a (sc - k))
          else some (.dbl (a * (10 : Int) ^ (k - sc)) 0)
      | _, _ => none
  | _ => none

def negateValue : Value → Value
  | .int i => .int (-i)
  | .dec m s => .dec (-m) s
  | .dbl m s => .dbl (-m) s
  | v => v

def parseTypeName : P SqlType := fun ts => do
  let (i, ts) ← match ts with
    | .ident s false :: r => Except.ok (s.toUpper, r)
    | t :: _ => .error s!"expected a datatype, found {repr t}"
    | [] => .error "expected a datatype, found end of input"
  -- An optional `(n)` or `(p, s)` length.
  let (len, ts) : Option Nat × List Tok :=
    match ts with
    | .sym "(" :: .num n :: .sym ")" :: r => (n.toNat?, r)
    | .sym "(" :: .num n :: .sym "," :: .num _ :: .sym ")" :: r => (n.toNat?, r)
    | _ => (none, ts)
  match i with
  | "INTEGER" | "INT" | "SMALLINT" | "BIGINT" => .ok (.integer, ts)
  | "DECIMAL" | "NUMERIC" => .ok (.decimal, ts)
  | "REAL" | "FLOAT" => .ok (.double, ts)
  | "DOUBLE" =>
      let ts := if peekKw "PRECISION" ts then ts.tail else ts
      .ok (.double, ts)
  | "VARCHAR" | "TEXT" => .ok (.varchar, ts)
  | "CHAR" | "CHARACTER" =>
      if peekKw "VARYING" ts then
        match ts.tail with
        | .sym "(" :: .num _ :: .sym ")" :: r => .ok (.varchar, r)
        | r => .ok (.varchar, r)
      else .ok (.char (len.getD 1), ts)
  | "BOOLEAN" => .ok (.boolean, ts)
  | "DATE" => .ok (.date, ts)
  | "TIMESTAMP" => .ok (.timestamp, ts)
  | "VARBINARY" | "BINARY" | "BLOB" => .ok (.binary, ts)
  | other => .error s!"SQL datatype {other} is not in the subset"

mutual
/-- Expressions, by precedence: OR, AND, NOT, comparison, `||`, primary. -/
def parseOr : Nat → P Expr
  | 0 => fun _ => .error "parser fuel exhausted"
  | n + 1 => fun ts => do
    let (a, ts) ← parseAnd n ts
    if peekKw "OR" ts then
      let (b, ts) ← parseOr n ts.tail
      .ok (.or a b, ts)
    else .ok (a, ts)

def parseAnd : Nat → P Expr
  | 0 => fun _ => .error "parser fuel exhausted"
  | n + 1 => fun ts => do
    let (a, ts) ← parseNot n ts
    if peekKw "AND" ts then
      let (b, ts) ← parseAnd n ts.tail
      .ok (.and a b, ts)
    else .ok (a, ts)

def parseNot : Nat → P Expr
  | 0 => fun _ => .error "parser fuel exhausted"
  | n + 1 => fun ts =>
    if peekKw "NOT" ts then do
      let (a, ts) ← parseNot n ts.tail
      .ok (.not a, ts)
    else parseCmp n ts

def parseCmp : Nat → P Expr
  | 0 => fun _ => .error "parser fuel exhausted"
  | n + 1 => fun ts => do
    let (a, ts) ← parseConcat n ts
    match ts with
    | .sym op :: r =>
      if ["=", "<", ">", "<=", ">=", "<>", "!="].contains op then do
        let (b, r) ← parseConcat n r
        .ok (.cmp (if op == "!=" then "<>" else op) a b, r)
      else .ok (a, ts)
    | t :: r =>
      if isKw "IS" t then
        if peekKw "NOT" r then do
          let ((), r) ← expectKw "NULL" r.tail
          .ok (.isNull a true, r)
        else do
          let ((), r) ← expectKw "NULL" r
          .ok (.isNull a false, r)
      else .ok (a, ts)
    | [] => .ok (a, ts)

def parseConcat : Nat → P Expr
  | 0 => fun _ => .error "parser fuel exhausted"
  | n + 1 => fun ts => do
    let (a, ts) ← parsePrimary n ts
    if peekSym "||" ts then
      let (b, ts) ← parseConcat n ts.tail
      .ok (.concat a b, ts)
    else .ok (a, ts)

def parseWhens : Nat → List (Expr × Expr) → P (List (Expr × Expr))
  | 0, _ => fun _ => .error "parser fuel exhausted"
  | n + 1, acc => fun ts =>
    if peekKw "WHEN" ts then do
      let (w, ts) ← parseOr n ts.tail
      let ((), ts) ← expectKw "THEN" ts
      let (r, ts) ← parseOr n ts
      parseWhens n ((w, r) :: acc) ts
    else .ok (acc.reverse, ts)

def parsePrimary : Nat → P Expr
  | 0 => fun _ => .error "parser fuel exhausted"
  | n + 1 => fun ts =>
    match ts with
    | .str s :: r => .ok (.lit (.str s), r)
    | .hex h :: r => .ok (.lit (.bin h), r)
    | .num s :: r => match numValue s with
      | some v => .ok (.lit v, r)
      | none => .error s!"bad numeric literal {s}"
    | .sym "-" :: .num s :: r => match numValue s with
      | some v => .ok (.lit (negateValue v), r)
      | none => .error s!"bad numeric literal {s}"
    | .sym "(" :: r => do
      let (e, r) ← parseOr n r
      let ((), r) ← expectSym ")" r
      .ok (e, r)
    | t :: r =>
      if isKw "NULL" t then .ok (.lit .null, r)
      else if isKw "TRUE" t then .ok (.lit (.bool true), r)
      else if isKw "FALSE" t then .ok (.lit (.bool false), r)
      else if isKw "DATE" t && (r.head?.map (fun x => match x with | .str _ => true | _ => false)).getD false then
        match r with
        | .str s :: r' => .ok (.lit (.date s), r')
        | _ => .error "expected a date string"
      else if isKw "TIMESTAMP" t && (r.head?.map (fun x => match x with | .str _ => true | _ => false)).getD false then
        match r with
        | .str s :: r' => .ok (.lit (.timestamp s), r')
        | _ => .error "expected a timestamp string"
      else if isKw "CASE" t then do
        let (operand, r) ← if peekKw "WHEN" r then Except.ok (none, r)
          else do let (e, r) ← parseOr n r; Except.ok (some e, r)
        let (ws, r) ← parseWhens n [] r
        let (els, r) ← if peekKw "ELSE" r then do
            let (e, r) ← parseOr n r.tail; Except.ok (some e, r)
          else Except.ok (none, r)
        let ((), r) ← expectKw "END" r
        .ok (.case operand ws els, r)
      else if isKw "COUNT" t && peekSym "(" r then
        match r.tail with
        | .sym "*" :: .sym ")" :: r' => .ok (.count none, r')
        | r' => do
          let (e, r') ← parseOr n r'
          let ((), r') ← expectSym ")" r'
          .ok (.count (some e), r')
      else match identOf t with
        | some i =>
          match r with
          | .sym "." :: t2 :: r' =>
            if t2 == .sym "*" then .error "qualified * is not an expression"
            else match identOf t2 with
              | some c => .ok (.col (some i) c, r')
              | none => .error s!"expected a column name after '.', found {repr t2}"
          | _ =>
            if peekSym "(" r then .error s!"SQL function {i.text} is not in the subset"
            else .ok (.col none i, r)
        | none => .error s!"unexpected token {repr t} in an expression"
    | [] => .error "unexpected end of input in an expression"
end

def parseExprList : Nat → List Expr → P (List Expr)
  | 0, _ => fun _ => .error "parser fuel exhausted"
  | n + 1, acc => fun ts => do
    let (e, ts) ← parseOr n ts
    if peekSym "," ts then parseExprList n (e :: acc) ts.tail
    else .ok ((e :: acc).reverse, ts)

def parseSelItems : Nat → List SelItem → P (List SelItem)
  | 0, _ => fun _ => .error "parser fuel exhausted"
  | n + 1, acc => fun ts => do
    let (item, ts) ← match ts with
      | .sym "*" :: r => Except.ok (SelItem.star, r)
      | t :: .sym "." :: .sym "*" :: r =>
        match identOf t with
        | some i => .ok (.qualStar i, r)
        | none => .error s!"expected a table name before '.*', found {repr t}"
      | _ => do
        let (e, r) ← parseOr n ts
        if peekKw "AS" r then
          let (a, r) ← parseIdent r.tail
          .ok (.expr e (some a), r)
        else match r.head?.bind identOf with
          | some a => .ok (.expr e (some a), r.tail)
          | none => .ok (.expr e none, r)
    if peekSym "," ts then parseSelItems n (item :: acc) ts.tail
    else .ok ((item :: acc).reverse, ts)

def parseFromList : Nat → List TableRef → P (List TableRef)
  | 0, _ => fun _ => .error "parser fuel exhausted"
  | n + 1, acc => fun ts => do
    let (t, ts) ← parseIdent ts
    let (alias, ts) ←
      if peekKw "AS" ts then do let (a, r) ← parseIdent ts.tail; Except.ok (some a, r)
      else match ts.head?.bind identOf with
        | some a => Except.ok (some a, ts.tail)
        | none => Except.ok (none, ts)
    let ref : TableRef := { name := t, alias }
    if peekSym "," ts then parseFromList n (ref :: acc) ts.tail
    else .ok ((ref :: acc).reverse, ts)

def parseQuery (fuel : Nat) : P Query := fun ts => do
  let ((), ts) ← expectKw "SELECT" ts
  let (distinct, ts) := if peekKw "DISTINCT" ts then (true, ts.tail) else (false, ts)
  let (items, ts) ← parseSelItems fuel [] ts
  let ((), ts) ← expectKw "FROM" ts
  let (fr, ts) ← parseFromList fuel [] ts
  let (wh, ts) ← if peekKw "WHERE" ts then do
      let (e, r) ← parseOr fuel ts.tail; Except.ok (some e, r)
    else Except.ok (none, ts)
  let (gb, ts) ← if peekKw "GROUP" ts then do
      let ((), r) ← expectKw "BY" ts.tail
      parseExprList fuel [] r
    else Except.ok ([], ts)
  .ok ({ distinct, items, «from» := fr, «where» := wh, groupBy := gb }, ts)

/-- Column constraints after a column's datatype. -/
def parseColConstraints : Nat → (Bool × Bool × Option (Ident × Ident)) →
    P (Bool × Bool × Option (Ident × Ident))
  | 0, _ => fun _ => .error "parser fuel exhausted"
  | n + 1, acc@(pk, uq, fk) => fun ts =>
    if peekKw "PRIMARY" ts then do
      let ((), r) ← expectKw "KEY" ts.tail
      parseColConstraints n (true, uq, fk) r
    else if peekKw "UNIQUE" ts then parseColConstraints n (pk, true, fk) ts.tail
    else if peekKw "NOT" ts then do
      let ((), r) ← expectKw "NULL" ts.tail
      parseColConstraints n acc r
    else if peekKw "NULL" ts then parseColConstraints n acc ts.tail
    else if peekKw "REFERENCES" ts then do
      let (t, r) ← parseIdent ts.tail
      let (cs, r) ← parseParenIdents r
      match cs with
      | [c] => parseColConstraints n (pk, uq, some (t, c)) r
      | _ => .error "a column REFERENCES clause names one column"
    else .ok (acc, ts)

def parseForeignKey : P ForeignKey := fun ts => do
  let ((), ts) ← expectKw "FOREIGN" ts
  let ((), ts) ← expectKw "KEY" ts
  let (cs, ts) ← parseParenIdents ts
  let ((), ts) ← expectKw "REFERENCES" ts
  let (t, ts) ← parseIdent ts
  let (rcs, ts) ← parseParenIdents ts
  .ok ({ cols := cs, refTable := t, refCols := rcs }, ts)

def skipConstraintName (ts : List Tok) : List Tok :=
  if peekKw "CONSTRAINT" ts then ts.drop 2 else ts

def parseTableElems : Nat → List TableElem → P (List TableElem)
  | 0, _ => fun _ => .error "parser fuel exhausted"
  | n + 1, acc => fun ts => do
    let ts := skipConstraintName ts
    let (el, ts) ←
      if peekKw "PRIMARY" ts then do
        let ((), r) ← expectKw "KEY" ts.tail
        let (cs, r) ← parseParenIdents r
        Except.ok (TableElem.primaryKey cs, r)
      else if peekKw "UNIQUE" ts then do
        let (cs, r) ← parseParenIdents ts.tail
        Except.ok (TableElem.unique cs, r)
      else if peekKw "FOREIGN" ts then do
        let (fk, r) ← parseForeignKey ts
        Except.ok (TableElem.foreignKey fk, r)
      else do
        let (c, r) ← parseIdent ts
        let (ty, r) ← parseTypeName r
        let ((pk, uq, fk), r) ← parseColConstraints n (false, false, none) r
        Except.ok (TableElem.column { name := c, type := ty } pk uq fk, r)
    if peekSym "," ts then parseTableElems n (el :: acc) ts.tail
    else .ok ((el :: acc).reverse, ts)

def parseValueRows : Nat → List (List Expr) → P (List (List Expr))
  | 0, _ => fun _ => .error "parser fuel exhausted"
  | n + 1, acc => fun ts => do
    let ((), ts) ← expectSym "(" ts
    let (es, ts) ← parseExprList n [] ts
    let ((), ts) ← expectSym ")" ts
    if peekSym "," ts then parseValueRows n (es :: acc) ts.tail
    else .ok ((es :: acc).reverse, ts)

def parseStmt (fuel : Nat) : P Stmt := fun ts =>
  if peekKw "SELECT" ts then do
    let (q, r) ← parseQuery fuel ts
    .ok (.select q, r)
  else if peekKw "CREATE" ts then do
    let ((), r) ← expectKw "TABLE" ts.tail
    let (t, r) ← parseIdent r
    let ((), r) ← expectSym "(" r
    let (els, r) ← parseTableElems fuel [] r
    let ((), r) ← expectSym ")" r
    .ok (.createTable t els, r)
  else if peekKw "DROP" ts then do
    let ((), r) ← expectKw "TABLE" ts.tail
    let r := if peekKw "IF" r then r.drop 2 else r
    let (t, r) ← parseIdent r
    let r := if peekKw "CASCADE" r then r.tail else r
    .ok (.dropTable t, r)
  else if peekKw "ALTER" ts then do
    let ((), r) ← expectKw "TABLE" ts.tail
    let (t, r) ← parseIdent r
    let ((), r) ← expectKw "ADD" r
    let r := skipConstraintName r
    if peekKw "PRIMARY" r then do
      let ((), r) ← expectKw "KEY" r.tail
      let (cs, r) ← parseParenIdents r
      .ok (.addPrimaryKey t cs, r)
    else do
      let (fk, r) ← parseForeignKey r
      .ok (.addForeignKey t fk, r)
  else if peekKw "INSERT" ts then do
    let ((), r) ← expectKw "INTO" ts.tail
    let (t, r) ← parseIdent r
    let (cols, r) ← if peekSym "(" r then do
        let (cs, r) ← parseParenIdents r; Except.ok (some cs, r)
      else Except.ok (none, r)
    let ((), r) ← expectKw "VALUES" r
    let (rows, r) ← parseValueRows fuel [] r
    .ok (.insert t cols rows, r)
  else match ts.head? with
    | some t => .error s!"SQL statement starting {repr t} is not in the subset"
    | none => .error "empty statement"

def fuelFor (ts : List Tok) : Nat := 4 * ts.length + 8

/-- A script: statements separated by `;`. -/
def parseScriptLoop : Nat → List Stmt → List Tok → Except String (List Stmt)
  | 0, _, _ => .error "parser fuel exhausted"
  | n + 1, acc, ts =>
    match ts with
    | [] => .ok acc.reverse
    | .sym ";" :: r => parseScriptLoop n acc r
    | _ => do
      let (s, r) ← parseStmt (fuelFor ts) ts
      match r with
      | [] => .ok (s :: acc).reverse
      | .sym ";" :: r' => parseScriptLoop n (s :: acc) r'
      | t :: _ => .error s!"expected ';' after a statement, found {repr t}"

def parseScript (src : String) : Except String (List Stmt) := do
  let ts ← lex src
  parseScriptLoop (ts.length + 1) [] ts

/-- One query; a final `;` is allowed. -/
def parseSelect (src : String) : Except String Query := do
  let ts ← lex src
  let (q, r) ← parseQuery (fuelFor ts) ts
  match r with
  | [] | [.sym ";"] => .ok q
  | t :: _ => .error s!"unexpected {repr t} after the query"

/-! ## Build-time checks -/

#guard (lex "SELECT \"a\", b FROM t").toOption.map List.length == some 6
#guard match parseScript "CREATE TABLE \"T\" (\"ID\" INTEGER PRIMARY KEY, n VARCHAR(5)); INSERT INTO \"T\" VALUES (1, 'it''s');" with
  | .ok [.createTable _ [_, _], .insert _ none [[.lit (.int 1), .lit (.str "it's")]]] => true
  | _ => false
#guard (parseSelect "SELECT ('S' || \"ID\") AS sid, \"T\".* FROM \"T\" WHERE \"ID\" < 30;").isOk
#guard (parseSelect "THIS IS NOT A VALID SQL QUERY").toOption.isNone
#guard numValue "80.25" == some (.dec 8025 2)
#guard numValue "1E3" == some (.dbl 1000 0)
#guard (Ident.regular "StudentId").norm == "STUDENTID"

end L4Factoidal.SQL
