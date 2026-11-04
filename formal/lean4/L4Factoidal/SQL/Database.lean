/-
L4Factoidal.SQL.Database — tables with keys and rows, running a script of the
subset, and evaluating a query to a result set with typed columns.

Spec: ISO/IEC 9075-2:2008: §4.17 (primary key, unique and referential
constraints), §8.2 (comparison, three-valued: a comparison with NULL is
unknown), §7.5 to §7.12 (FROM as the cross product of its tables, WHERE keeps
the rows where the condition is true, GROUP BY), §14.11 (INSERT: a value is
cast to the column's datatype). Design record:
`docs/designissues/2026-11-01-r2rml-and-direct-mapping.md` §1.

A result column has a name and a datatype. R2RML 2012 §10.2 maps a value to
an RDF literal by the datatype of its column, so the datatype is part of the
result, decided here.

Tracking: https://github.com/danbri/factoidal/issues/1165.
-/
import L4Factoidal.SQL.Syntax

namespace L4Factoidal.SQL

structure Column where
  name : String
  type : SqlType
  deriving Repr, Inhabited, DecidableEq

structure FKey where
  cols : List String
  refTable : String
  refCols : List String
  deriving Repr, Inhabited, DecidableEq

structure Table where
  name : String
  columns : List Column
  primaryKey : List String := []
  uniques : List (List String) := []
  foreignKeys : List FKey := []
  rows : List (List Value) := []
  deriving Repr, Inhabited

structure Database where
  tables : List Table := []
  deriving Repr, Inhabited

def Database.find? (db : Database) (name : String) : Option Table :=
  db.tables.find? (·.name == name)

def Database.update (db : Database) (name : String) (f : Table → Table) : Database :=
  { tables := db.tables.map (fun t => if t.name == name then f t else t) }

def Table.colIndex? (t : Table) (c : String) : Option Nat :=
  t.columns.findIdx? (·.name == c)

/-! ## Casting a value to a column's datatype (SQL:2008 §6.12) -/

def pow10 (n : Nat) : Int := (10 : Int) ^ n

/-- Remove trailing zero digits of an exact decimal. -/
def trimDec (m : Int) : Nat → Int × Nat
  | 0 => (m, 0)
  | s + 1 => if m % 10 == 0 then trimDec (m / 10) s else (m, s + 1)

def isDigits (s : String) : Bool := !s.isEmpty && s.toList.all Char.isDigit

/-- `YYYY-MM-DD`. -/
def isDateLex (s : String) : Bool :=
  match s.splitOn "-" with
  | [y, m, d] => y.length == 4 && m.length == 2 && d.length == 2 && isDigits y && isDigits m && isDigits d
  | _ => false

def padRight (s : String) (n : Nat) : String :=
  if s.length < n then s ++ String.ofList (List.replicate (n - s.length) ' ') else s

def castTo (ty : SqlType) (v : Value) : Except String Value :=
  match ty, v with
  | _, .null => .ok .null
  | .integer, .int i => .ok (.int i)
  | .integer, .dec m s => if m % pow10 s == 0 then .ok (.int (m / pow10 s)) else .error s!"{repr v} is not an integer"
  | .integer, .str s => match s.trimAscii.toString.toInt? with
    | some i => .ok (.int i)
    | none => .error s!"'{s}' is not an integer"
  | .decimal, .int i => .ok (.dec i 0)
  | .decimal, .dec m s => .ok (.dec m s)
  | .double, .int i => .ok (.dbl i 0)
  | .double, .dec m s => .ok (.dbl m s)
  | .double, .dbl m s => .ok (.dbl m s)
  | .varchar, .str s => .ok (.str s)
  | .varchar, .int i => .ok (.str (toString i))
  | .char n, .str s => .ok (.str (padRight s n))
  | .boolean, .bool b => .ok (.bool b)
  | .date, .str s => if isDateLex s then .ok (.date s) else .error s!"'{s}' is not a date"
  | .date, .date s => .ok (.date s)
  | .timestamp, .str s => .ok (.timestamp s)
  | .timestamp, .timestamp s => .ok (.timestamp s)
  | .binary, .bin h => .ok (.bin h)
  | _, _ => .error s!"cannot cast {repr v} to {repr ty}"

/-! ## Running a script -/

def addElem (t : Table) : TableElem → Table
  | .column c pk uq fk =>
    let t := { t with columns := t.columns ++ [{ name := c.name.norm, type := c.type }] }
    let t := if pk then { t with primaryKey := [c.name.norm] } else t
    let t := if uq then { t with uniques := t.uniques ++ [[c.name.norm]] } else t
    match fk with
    | some (rt, rc) => { t with foreignKeys := t.foreignKeys ++ [{ cols := [c.name.norm], refTable := rt.norm, refCols := [rc.norm] }] }
    | none => t
  | .primaryKey cs => { t with primaryKey := cs.map Ident.norm }
  | .unique cs => { t with uniques := t.uniques ++ [cs.map Ident.norm] }
  | .foreignKey fk => { t with foreignKeys := t.foreignKeys ++ [{ cols := fk.cols.map Ident.norm, refTable := fk.refTable.norm, refCols := fk.refCols.map Ident.norm }] }

/-- A constant expression of an INSERT row. -/
def constValue : Expr → Except String Value
  | .lit v => .ok v
  | e => .error s!"INSERT value {repr e} is not a literal"

def mapExcept {α β : Type} (f : α → Except String β) (xs : List α) : Except String (List β) :=
  (xs.foldl (fun acc x => do let ys ← acc; let y ← f x; pure (y :: ys)) (.ok [])).map List.reverse

def insertRow (t : Table) (cols : Option (List Ident)) (es : List Expr) : Except String Table := do
  let vals ← mapExcept constValue es
  let names := match cols with
    | some cs => cs.map Ident.norm
    | none => t.columns.map (fun (c : Column) => c.name)
  if names.length != vals.length then
    throw s!"INSERT INTO {t.name}: {names.length} columns, {vals.length} values"
  for n in names do
    if (t.colIndex? n).isNone then throw s!"INSERT INTO {t.name}: no column {n}"
  let row ← mapExcept (fun (c : Column) =>
    match (names.zip vals).find? (fun (p : String × Value) => p.1 == c.name) with
    | some (_, v) => castTo c.type v
    | none => .ok .null) t.columns
  -- SQL:2008 §4.17.2: no NULL in a primary key column.
  for k in t.primaryKey do
    match t.colIndex? k with
    | some i => if row[i]? == some .null then throw s!"INSERT INTO {t.name}: NULL in primary key column {k}"
    | none => pure ()
  pure { t with rows := t.rows ++ [row] }

def runStmt (db : Database) : Stmt → Except String Database
  | .createTable n els =>
    let name := n.norm
    if (db.find? name).isSome then .error s!"table {name} exists"
    else .ok { tables := db.tables ++ [els.foldl addElem { name, columns := [] }] }
  | .dropTable n => .ok { tables := db.tables.filter (·.name != n.norm) }
  | .addForeignKey t fk =>
    if (db.find? t.norm).isNone then .error s!"no table {t.norm}" else
    .ok (db.update t.norm fun tb => { tb with foreignKeys := tb.foreignKeys ++
      [{ cols := fk.cols.map Ident.norm, refTable := fk.refTable.norm, refCols := fk.refCols.map Ident.norm }] })
  | .addPrimaryKey t cs =>
    if (db.find? t.norm).isNone then .error s!"no table {t.norm}" else
    .ok (db.update t.norm fun tb => { tb with primaryKey := cs.map Ident.norm })
  | .insert t cols rows => do
    let some tb := db.find? t.norm | throw s!"INSERT INTO {t.norm}: no such table"
    let tb' ← rows.foldl (fun acc r => do let tb ← acc; insertRow tb cols r) (.ok tb)
    pure (db.update t.norm fun _ => tb')
  | .select _ => .ok db

def runScript (src : String) : Except String Database := do
  let stmts ← parseScript src
  stmts.foldl (fun acc s => do let db ← acc; runStmt db s) (.ok {})

/-! ## Queries -/

/-- A result set: typed columns and rows (SQL:2008 §7.12). A column with no
    name (an expression with no alias) has the name `none`. -/
structure ResultSet where
  columns : List (Option String × SqlType)
  rows : List (List Value)
  deriving Repr, Inhabited

/-- One binding of a FROM item in a row: the name the query uses for the
    table, the column name, the column datatype and the value. -/
abbrev Env := List (String × String × SqlType × Value)

def lookupCol (env : Env) (qual : Option String) (c : String) : Except String (SqlType × Value) :=
  let hits := env.filter (fun (t, n, _, _) => n == c && (qual.map (· == t)).getD true)
  match hits with
  | [(_, _, ty, v)] => .ok (ty, v)
  | [] => .error s!"no column {match qual with | some q => q ++ "." | none => ""}{c}"
  | _ => .error s!"column {c} is ambiguous"

/-- The character string of a value, for `||` (SQL:2008 §6.29 needs character
    operands; an exact numeric operand is cast as by §6.12). -/
def Value.toChars : Value → Option String
  | .str s => some s
  | .int i => some (toString i)
  | .date s | .timestamp s => some s
  | _ => none

def cmpNum (a b : Int × Nat) : Ordering :=
  let s := max a.2 b.2
  compare (a.1 * pow10 (s - a.2)) (b.1 * pow10 (s - b.2))

def Value.num? : Value → Option (Int × Nat)
  | .int i => some (i, 0)
  | .dec m s | .dbl m s => some (m, s)
  | _ => none

/-- Trailing spaces do not count in a character comparison (SQL:2008 §8.2
    general rule 3, PAD SPACE). -/
def rtrimSpaces (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (· == ' ')).reverse

/-- SQL comparison: `none` is unknown (a NULL operand). -/
def compareValues (a b : Value) : Except String (Option Ordering) :=
  match a, b with
  | .null, _ | _, .null => .ok none
  | .str x, .str y => .ok (some (compare (rtrimSpaces x) (rtrimSpaces y)))
  | .bool x, .bool y => .ok (some (compare x.toNat y.toNat))
  | .date x, .date y | .timestamp x, .timestamp y => .ok (some (compare x y))
  | .date x, .str y | .timestamp x, .str y => .ok (some (compare x y))
  | .bin x, .bin y => .ok (some (compare x y))
  | x, y => match x.num?, y.num? with
    | some p, some q => .ok (some (cmpNum p q))
    | _, _ => match x, y with
      | .str s, _ => match s.trimAscii.toString.toInt?, y.num? with
        | some i, some q => .ok (some (cmpNum (i, 0) q))
        | _, _ => .error s!"cannot compare {repr x} with {repr y}"
      | _, .str s => match x.num?, s.trimAscii.toString.toInt? with
        | some p, some i => .ok (some (cmpNum p (i, 0)))
        | _, _ => .error s!"cannot compare {repr x} with {repr y}"
      | _, _ => .error s!"cannot compare {repr x} with {repr y}"

def opHolds (op : String) (o : Ordering) : Bool :=
  match op with
  | "=" => o == .eq
  | "<>" => o != .eq
  | "<" => o == .lt
  | ">" => o == .gt
  | "<=" => o != .gt
  | ">=" => o != .lt
  | _ => false

def ofTruth : Option Bool → Value
  | some b => .bool b
  | none => .null

def truth? : Value → Option Bool
  | .bool b => some b
  | _ => none

def literalType : Value → SqlType
  | .int _ => .integer
  | .dec _ _ => .decimal
  | .dbl _ _ => .double
  | .bool _ => .boolean
  | .date _ => .date
  | .timestamp _ => .timestamp
  | .bin _ => .binary
  | _ => .varchar

/-- Evaluate a scalar expression in one row. `group` is the rows of the
    row's group, for `COUNT`. The result carries the expression's datatype. -/
def evalExpr (group : List Env) (env : Env) : Nat → Expr → Except String (SqlType × Value)
  | 0, _ => .error "expression too deep"
  | _ + 1, .lit v => .ok (literalType v, v)
  | _ + 1, .col q c => lookupCol env (q.map Ident.norm) c.norm
  | n + 1, .concat a b => do
    let (_, x) ← evalExpr group env n a
    let (_, y) ← evalExpr group env n b
    match x, y with
    | .null, _ | _, .null => pure (.varchar, .null)
    | _, _ => match x.toChars, y.toChars with
      | some s, some t => pure (.varchar, .str (s ++ t))
      | _, _ => throw s!"|| needs character operands, found {repr x} and {repr y}"
  | n + 1, .cmp op a b => do
    let (_, x) ← evalExpr group env n a
    let (_, y) ← evalExpr group env n b
    let o ← compareValues x y
    pure (.boolean, ofTruth (o.map (opHolds op)))
  | n + 1, .and a b => do
    let (_, x) ← evalExpr group env n a
    let (_, y) ← evalExpr group env n b
    pure (.boolean, match truth? x, truth? y with
      | some false, _ | _, some false => .bool false
      | some true, some true => .bool true
      | _, _ => .null)
  | n + 1, .or a b => do
    let (_, x) ← evalExpr group env n a
    let (_, y) ← evalExpr group env n b
    pure (.boolean, match truth? x, truth? y with
      | some true, _ | _, some true => .bool true
      | some false, some false => .bool false
      | _, _ => .null)
  | n + 1, .not a => do
    let (_, x) ← evalExpr group env n a
    pure (.boolean, ofTruth ((truth? x).map (!·)))
  | n + 1, .isNull a neg => do
    let (_, x) ← evalExpr group env n a
    pure (.boolean, .bool ((x == .null) != neg))
  | n + 1, .case operand branches els => do
    let ty ← match branches.head? with
      | some (_, r) => do let (t, _) ← evalExpr group env n r; pure t
      | none => pure .varchar
    let opv ← match operand with
      | some o => do let (_, v) ← evalExpr group env n o; pure (some v)
      | none => pure none
    let rec pick : List (Expr × Expr) → Except String Value
      | [] => match els with
        | some e => do let (_, v) ← evalExpr group env n e; pure v
        | none => pure .null
      | (w, r) :: rest => do
        let (_, wv) ← evalExpr group env n w
        let hit ← match opv with
          | some v => do let o ← compareValues v wv; pure (o == some .eq)
          | none => pure (wv == .bool true)
        if hit then do let (_, v) ← evalExpr group env n r; pure v else pick rest
    let v ← pick branches
    pure (ty, v)
  | n + 1, .count arg => do
    let k ← match arg with
      | none => pure group.length
      | some e => group.foldl (fun acc g => do
          let k ← acc
          let (_, v) ← evalExpr [] g n e
          pure (if v == .null then k else k + 1)) (.ok 0)
    pure (.integer, .int k)

def exprDepth (e : Expr) : Nat := (toString (repr e)).length + 2

/-- Does the expression contain `COUNT`? Fuel: `exprDepth`, more than the
    depth of any expression. -/
def hasCountF : Nat → Expr → Bool
  | 0, _ => false
  | _ + 1, .count _ => true
  | n + 1, .concat a b | n + 1, .cmp _ a b | n + 1, .and a b | n + 1, .or a b => hasCountF n a || hasCountF n b
  | n + 1, .not a | n + 1, .isNull a _ => hasCountF n a
  | n + 1, .case o bs e => (o.map (hasCountF n)).getD false || bs.any (fun (w, r) => hasCountF n w || hasCountF n r)
      || (e.map (hasCountF n)).getD false
  | _ + 1, _ => false

def Expr.hasCount (e : Expr) : Bool := hasCountF (exprDepth e) e

/-- The name of a result column (SQL:2008 §7.12 syntax rule 18): the alias,
    else the column name of a column reference, else no name. -/
def itemName : Expr → Option Ident → Option String
  | _, some a => some a.norm
  | .col _ c, none => some c.norm
  | _, none => none

def crossProduct (parts : List (List Env)) : List Env :=
  parts.foldl (fun acc rows => acc.flatMap (fun a => rows.map (fun r => a ++ r))) [[]]

def Table.envRows (t : Table) (as : String) : List Env :=
  t.rows.map fun row => (t.columns.zip row).map fun (c, v) => (as, c.name, c.type, v)

def dedupRows : List (List Value) → List (List Value) → List (List Value)
  | [], acc => acc.reverse
  | r :: rs, acc => if acc.contains r then dedupRows rs acc else dedupRows rs (r :: acc)

/-- Evaluate a query against a database. -/
def evalQuery (db : Database) (q : Query) : Except String ResultSet := do
  let mut parts : List (List Env) := []
  let mut scope : List (String × Table) := []
  for r in q.«from» do
    let some t := db.find? r.name.norm | throw s!"no table {r.name.norm}"
    let as := (r.alias.map Ident.norm).getD t.name
    parts := parts ++ [t.envRows as]
    scope := scope ++ [(as, t)]
  let rows := crossProduct parts
  let rows ← rows.foldl (fun acc env => do
    let keep ← acc
    match q.«where» with
    | none => pure (keep ++ [env])
    | some w => do
      let (_, v) ← evalExpr [] env (exprDepth w) w
      pure (if v == .bool true then keep ++ [env] else keep)) (.ok [])
  -- Expand the select list.
  let mut items : List (Expr × Option Ident) := []
  for it in q.items do
    match it with
    | .star =>
      for (as, t) in scope do
        for c in t.columns do
          items := items ++ [(.col (some { text := as, delimited := true }) { text := c.name, delimited := true }, none)]
    | .qualStar tn =>
      match scope.find? (·.1 == tn.norm) with
      | some (as, t) =>
        for c in t.columns do
          items := items ++ [(.col (some { text := as, delimited := true }) { text := c.name, delimited := true }, none)]
      | none => throw s!"no table {tn.norm} in FROM"
    | .expr e a => items := items ++ [(e, a)]
  let grouped := !q.groupBy.isEmpty || items.any (·.1.hasCount)
  -- The groups: one per distinct GROUP BY key, in first-seen order.
  let groups : List (List Env) ←
    if !grouped then pure (rows.map ([·]))
    else do
      let mut gs : List (List Value × List Env) := []
      for env in rows do
        let key ← mapExcept (fun e => do let (_, v) ← evalExpr [] env (exprDepth e) e; pure v) q.groupBy
        match gs.findIdx? (·.1 == key) with
        | some i => gs := gs.modify i (fun (k, es) => (k, es ++ [env]))
        | none => gs := gs ++ [(key, [env])]
      pure (gs.map (·.2))
  let mut outRows : List (List Value) := []
  let mut types : List SqlType := items.map (fun _ => SqlType.varchar)
  for g in groups do
    let env := g.headD []
    let mut row : List Value := []
    let mut tys : List SqlType := []
    for (e, _) in items do
      if g.isEmpty then
        row := row ++ [Value.null]; tys := tys ++ [SqlType.integer]
      else
        let (ty, v) ← evalExpr g env (exprDepth e) e
        row := row ++ [v]; tys := tys ++ [ty]
    outRows := outRows ++ [row]
    types := tys
  -- The column types when there is no row: from the schema where they are
  -- column references.
  if groups.isEmpty then
    types := items.map fun (e, _) => match e with
      | .col q c =>
        let hits := scope.filter (fun (as, _) => (q.map (·.norm == as)).getD true)
        match hits.findSome? (fun (_, t) => t.columns.find? (·.name == c.norm)) with
        | some col => col.type
        | none => .varchar
      | .count _ => .integer
      | .lit v => literalType v
      | _ => .varchar
  let finalRows := if q.distinct then dedupRows outRows [] else outRows
  pure { columns := items.map (fun (e, a) => itemName e a) |>.zip types, rows := finalRows }

def runQuery (db : Database) (src : String) : Except String ResultSet := do
  let q ← parseSelect src
  evalQuery db q

/-- `SELECT * FROM t` (R2RML 2012 §5.1: `rr:tableName` is this query). -/
def selectStar (t : Ident) : Query :=
  { distinct := false, items := [.star], «from» := [{ name := t, alias := none }], «where» := none, groupBy := [] }

/-! ## Build-time checks -/

private def demo : Except String Database :=
  runScript "CREATE TABLE \"S\" (\"ID\" INTEGER PRIMARY KEY, \"Name\" VARCHAR(20), \"Sport\" INTEGER);
             INSERT INTO \"S\" VALUES (10, 'Venus', 100); INSERT INTO \"S\" VALUES (20, 'Demi', NULL);"

#guard match demo with
  | .ok db => (db.find? "S").map (·.rows.length) == some 2
  | .error _ => false
#guard match demo.bind (fun db => runQuery db "SELECT ('S' || \"ID\") AS sid, \"Name\" FROM \"S\" WHERE \"ID\" < 15") with
  | .ok rs => rs.rows == [[.str "S10", .str "Venus"]] && rs.columns.map (·.1) == [some "SID", some "Name"]
  | .error _ => false
#guard match demo.bind (fun db => runQuery db "SELECT \"Name\", COUNT(\"Sport\") FROM \"S\" GROUP BY \"Name\"") with
  | .ok rs => rs.rows == [[.str "Venus", .int 1], [.str "Demi", .int 0]]
  | .error _ => false
#guard match demo.bind (fun db => runQuery db "SELECT * FROM \"S\"") with
  | .ok rs => rs.rows.length == 2 && rs.columns.length == 3
  | .error _ => false

end L4Factoidal.SQL
