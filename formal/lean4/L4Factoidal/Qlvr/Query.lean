/-
L4Factoidal.Qlvr.Query — a SPARQL SELECT fragment answered from a QLever
index (Factoidal/qlvr, https://github.com/danbri/factoidal/issues/778).

The query text is parsed by the repository's SPARQL parser
(`L4Factoidal.SPARQL.parseSparql`). `translate` accepts this fragment and
refuses everything else with a message (`refused: ...`), so a query outside
it is never answered wrongly:

  * `SELECT` with `*`, variables, `(COUNT(*) AS ?n)` and `(COUNT(?x) AS ?n)`
    (not DISTINCT); `DISTINCT`, `REDUCED` (read as no modifier);
  * a WHERE clause that is a basic graph pattern with FILTERs (no OPTIONAL,
    UNION, MINUS, GRAPH, BIND, VALUES, sub-queries or property paths);
  * FILTER expressions built from `&&`, `||`, `!`, the comparisons
    `= != < > <= >=` and `sameTerm` between variables and constants, and
    `STRSTARTS`, `STRENDS`, `CONTAINS` of a variable and a string literal;
  * `GROUP BY` variables (with COUNT), `ORDER BY` variables (ASC or DESC),
    `LIMIT`, `OFFSET`. No HAVING, no FROM, no trailing VALUES.

Semantics follow QLever, the oracle (format record, section 1 and stage 4):

  * Constants are folded as QLever's parser folds literals: the 12 integer
    datatypes to an `Int` Id, `xsd:decimal`/`xsd:double`/`xsd:float` to a
    `Double` Id (binary64 bits shifted right by 4), `xsd:boolean` to a `Bool`
    Id. So `1936` (xsd:integer) matches `"1936"^^xsd:int`. Other literals and
    IRIs are looked up in the vocabulary in their stored form. Date and
    duration literals are refused (https://github.com/danbri/factoidal/issues/780).
  * FILTER comparisons use `cmpIdsCompatible` (QLever `compareIds`,
    `AlwaysUndef`): numbers by value, words by vocabulary position; a
    comparison of incompatible datatypes is an error and the row is dropped.
  * ORDER BY uses `cmpIdsOrder` (QLever `CompareByType`): words in vocabulary
    (ICU collation) order, numbers by value, otherwise by datatype tag.
  * Results print `Int` as `xsd:int` and `Double` as `xsd:decimal`, as QLever
    does.

## Loops

No function here recurses. The FILTER expression tree and the WHERE pattern
tree are walked with an explicit stack in a `for` loop of bounded length
(`maxNodes`); a filter is compiled to a postfix program that a `for` loop
evaluates with a value stack. Rendering is a tail call over rows with a fuel
`Nat` first.
-/
import L4Factoidal.Qlvr.Bgp
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.ResultsJson

namespace L4Factoidal.Qlvr.Query


open L4Factoidal.RDF
open L4Factoidal.SPARQL (Expr CompOp QueryPattern QueryForm SelectClause SelectItem
  GroupCondition OrderCondition PatternTerm PatternSubject AggregateFn)

/-- Bound on the nodes of a FILTER expression or WHERE pattern tree. -/
def maxNodes : Nat := 4096

def xsd (s : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ s

/-- The integer datatypes QLever folds into `Int` (`parser/RdfParser.cpp:676-721`). -/
def intTypes : List String :=
  ["int", "integer", "nonPositiveInteger", "negativeInteger", "long", "short", "byte",
   "nonNegativeInteger", "unsignedLong", "unsignedInt", "unsignedShort", "positiveInteger"].map xsd

def doubleTypes : List String := ["decimal", "double", "float"].map xsd

def dateTypes : List String :=
  ["date", "dateTime", "gYear", "gYearMonth", "dayTimeDuration"].map xsd

/-! ## Constant folding -/

def digitVal (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat) else none

/-- `[+-]?[0-9]+`. -/
def parseIntLex (s : String) : Option Int := Id.run do
  let cs := s.toList.toArray
  if cs.isEmpty then return none
  let neg := cs[0]! == '-'
  let start := if cs[0]! == '-' || cs[0]! == '+' then 1 else 0
  if start ≥ cs.size then return none
  let mut n : Nat := 0
  for i in [start:cs.size] do
    match digitVal cs[i]! with
    | some d => n := 10 * n + d
    | none => return none
  return some (if neg then -(n : Int) else n)

/-- An xsd:decimal / xsd:double lexical form: `[+-]? digits [. digits]
    [(e|E) [+-]? digits]`, `INF`, `-INF`, `+INF`, `NaN`. -/
def parseFloatLex (s : String) : Option Float := Id.run do
  if s == "INF" || s == "+INF" then return some (1.0 / 0.0)
  if s == "-INF" then return some (-1.0 / 0.0)
  if s == "NaN" then return some (0.0 / 0.0)
  let cs := s.toList.toArray
  if cs.isEmpty then return none
  let neg := cs[0]! == '-'
  let mut i := if cs[0]! == '-' || cs[0]! == '+' then 1 else 0
  let mut mant : Nat := 0
  let mut scale : Int := 0
  let mut digits := 0
  let mut seenDot := false
  let mut expPart : Option Nat := none
  for _ in [0:cs.size] do
    if i ≥ cs.size then break
    let c := cs[i]!
    if c == '.' && !seenDot && expPart.isNone then
      seenDot := true
      i := i + 1
    else if (c == 'e' || c == 'E') && expPart.isNone && digits > 0 then
      expPart := some (i + 1)
      break
    else match digitVal c with
      | some d =>
        mant := 10 * mant + d
        digits := digits + 1
        if seenDot then scale := scale - 1
        i := i + 1
      | none => return none
  if digits == 0 then return none
  let mut e : Int := scale
  match expPart with
  | some j =>
    match parseIntLex (String.ofList (cs.toList.drop j)) with
    | some x => e := e + x
    | none => return none
  | none => pure ()
  let f := if e ≥ 0 then Float.ofScientific mant false 0 * Float.ofScientific 1 false e.toNat
           else Float.ofScientific mant true e.natAbs
  return some (if neg then -f else f)

/-- The `Double` Id of a binary64 value (low 4 mantissa bits dropped). -/
def doubleId (f : Float) : Id := ⟨((3 : UInt64) <<< 60) ||| (f.toBits >>> 4)⟩

/-- The `Bool` Id: bit 0 the value, bit 1 set when the lexical form was 0/1. -/
def boolId (value lexical01 : Bool) : Id :=
  ⟨((1 : UInt64) <<< 60) ||| (if value then 1 else 0) ||| (if lexical01 then 2 else 0)⟩

def intMin : Int := -(2 ^ 59 : Nat)
def intMax : Int := (2 ^ 59 - 1 : Nat)

/-- A query constant before the vocabulary lookup. -/
inductive Arg where
  | var (v : String)
  | id (x : Id)
  /-- a stored form to look up in the vocabulary -/
  | word (stored : String)
  /-- a word that is not in the vocabulary -/
  | absent
  deriving Repr, BEq, Inhabited

/-- Fold a literal as QLever's parser does, or give its stored form. -/
def literalArg (l : Literal) : Except String Arg :=
  let dt := l.datatype.val
  match l.langTag with
  | some tag => .ok (.word s!"\"{l.lexicalForm}\"@{tag}")
  | none =>
    if intTypes.contains dt then
      match parseIntLex l.lexicalForm with
      | some i => if intMin ≤ i && i ≤ intMax then .ok (.id (Id.ofInt i))
                  else .ok (.word s!"\"{l.lexicalForm}\"^^<{dt}>")
      | none => .ok (.word s!"\"{l.lexicalForm}\"^^<{dt}>")
    else if doubleTypes.contains dt then
      match parseFloatLex l.lexicalForm with
      | some f => .ok (.id (doubleId f))
      | none => .ok (.word s!"\"{l.lexicalForm}\"^^<{dt}>")
    else if dt == xsd "boolean" then
      match l.lexicalForm with
      | "true" => .ok (.id (boolId true false))
      | "false" => .ok (.id (boolId false false))
      | "1" => .ok (.id (boolId true true))
      | "0" => .ok (.id (boolId false true))
      | _ => .ok (.word s!"\"{l.lexicalForm}\"^^<{dt}>")
    else if dateTypes.contains dt then
      .error s!"a {dt} constant needs a Date Id, which this reader does not encode (https://github.com/danbri/factoidal/issues/780)"
    else if dt == xsd "string" then .ok (.word s!"\"{l.lexicalForm}\"")
    else .ok (.word s!"\"{l.lexicalForm}\"^^<{dt}>")

def patTermArg : PatternTerm → Except String Arg
  | .var v => .ok (.var v)
  | .iri i => .ok (.word s!"<{i.val}>")
  | .bnode b => .ok (.var ("_:" ++ b))
  | .literal l => literalArg l.val
  | .tripleTerm _ _ _ => .error "triple terms (RDF 1.2)"

def patSubjArg : PatternSubject → Except String Arg
  | .var v => .ok (.var v)
  | .iri i => .ok (.word s!"<{i.val}>")
  | .bnode b => .ok (.var ("_:" ++ b))
  | .tripleTerm _ _ _ => .error "triple terms (RDF 1.2)"

/-- A FILTER operand. -/
def exprArg : Expr → Except String Arg
  | .var v => .ok (.var v)
  | .iri i => .ok (.word s!"<{i.val}>")
  | .lit l => literalArg l.val
  | .numericLit n =>
    if intMin ≤ n && n ≤ intMax then .ok (.id (Id.ofInt n)) else .error s!"integer {n} outside 60 bits"
  | .decimalLit s | .doubleLit s =>
    match parseFloatLex s with
    | some f => .ok (.id (doubleId f))
    | none => .error s!"numeric literal {s}"
  | .boolLit b => .ok (.id (boolId b false))
  | _ => .error "a FILTER operand that is not a variable or a constant"

/-! ## FILTER programs -/

/-- One instruction of a postfix FILTER program. -/
inductive FOp where
  /-- comparison (`sameTerm` is `cmp none`, Id equality) -/
  | cmp (op : Option CompOp) (a b : Arg)
  /-- 0 STRSTARTS, 1 STRENDS, 2 CONTAINS -/
  | str (k : Nat) (v : String) (needle : String) (lang : Option String)
  | and | or | not
  deriving Repr, Inhabited

/-- A walk item: an expression to translate, or an operator to emit after
    its operands. -/
inductive Walk where
  | visit (e : Expr)
  | emit (op : FOp)

def strArg (k : Nat) (a b : Expr) : Except String FOp :=
  match a, b with
  | .var v, .lit l =>
    let l := l.val
    if l.langTag.isSome || l.datatype.val == xsd "string" then .ok (.str k v l.lexicalForm l.langTag)
    else .error "a string function whose second argument is not a string literal"
  | _, _ => .error "a string function that is not (variable, string literal)"

/-- A FILTER expression as a postfix program. -/
def compileFilter (e : Expr) : Except String (Array FOp) := do
  let mut stack : Array Walk := #[.visit e]
  let mut out : Array FOp := #[]
  for _ in [0:maxNodes] do
    match stack.back? with
    | none => break
    | some w =>
      stack := stack.pop
      match w with
      | .emit op => out := out.push op
      | .visit x =>
        match x with
        | .and l r => stack := (stack.push (.emit .and)).push (.visit r) |>.push (.visit l)
        | .or l r => stack := (stack.push (.emit .or)).push (.visit r) |>.push (.visit l)
        | .not a => stack := (stack.push (.emit .not)).push (.visit a)
        | .compare op l r => out := out.push (.cmp (some op) (← exprArg l) (← exprArg r))
        | .sameTerm l r => out := out.push (.cmp none (← exprArg l) (← exprArg r))
        | .strStarts a b => out := out.push (← strArg 0 a b)
        | .strEnds a b => out := out.push (← strArg 1 a b)
        | .contains a b => out := out.push (← strArg 2 a b)
        | _ => throw "a FILTER expression outside the fragment (allowed: && || ! = != < > <= >= sameTerm STRSTARTS STRENDS CONTAINS)"
  if !stack.isEmpty then throw s!"a FILTER expression with more than {maxNodes} nodes"
  return out

/-! ## The query plan -/

inductive ProjItem where
  | var (v : String)
  /-- `COUNT(*)` (arg `none`) or `COUNT(?x)` -/
  | count (alias : String) (arg : Option String)
  deriving Repr, Inhabited

def ProjItem.name : ProjItem → String
  | .var v => v
  | .count a _ => a

structure Plan where
  pats : Array (Arg × Arg × Arg)
  filters : Array (Array FOp)
  proj : Array ProjItem
  groupVars : Array String
  agg : Bool
  /-- (variable, descending) -/
  order : Array (String × Bool)
  distinct : Bool
  offset : Nat
  limit : Option Nat
  deriving Inhabited

/-- Flatten a WHERE clause of BGPs, joins and FILTERs. -/
def flattenWhere (p : QueryPattern) :
    Except String (Array (Arg × Arg × Arg) × Array (Array FOp)) := do
  let mut stack : Array QueryPattern := #[p]
  let mut pats : Array (Arg × Arg × Arg) := #[]
  let mut filters : Array (Array FOp) := #[]
  for _ in [0:maxNodes] do
    match stack.back? with
    | none => break
    | some x =>
      stack := stack.pop
      match x with
      | .bgp tps =>
        for tp in tps do
          pats := pats.push (← patSubjArg tp.s, ← patTermArg tp.p, ← patTermArg tp.o)
      | .join l r => stack := (stack.push r).push l
      | .filter c q =>
        filters := filters.push (← compileFilter c)
        stack := stack.push q
      | .empty => pure ()
      | _ => throw "a WHERE clause outside the fragment (allowed: triple patterns, FILTER)"
  if !stack.isEmpty then throw s!"a WHERE clause with more than {maxNodes} nodes"
  return (pats, filters)

def argVar : Arg → Option String
  | .var v => some v
  | _ => none

/-- Variables of the patterns in order of first occurrence (blank-node
    variables excluded). -/
def patVars (pats : Array (Arg × Arg × Arg)) : Array String :=
  pats.foldl (fun acc (s, p, o) =>
    [s, p, o].foldl (fun acc a => match argVar a with
      | some v => if acc.contains v || v.startsWith "_:" then acc else acc.push v
      | none => acc) acc) #[]

/-- Accept the fragment or say why not. -/
def translate (q : L4Factoidal.SPARQL.Query) : Except String Plan := do
  let sel ← match q.form with
    | .select s => pure s
    | _ => throw "only SELECT queries"
  unless q.dataset.isEmpty do throw "FROM / FROM NAMED"
  unless q.having.isEmpty do throw "HAVING"
  if q.postValues.isSome then throw "a trailing VALUES block"
  let (pats, filters) ← flattenWhere q.pattern
  if pats.isEmpty then throw "a WHERE clause with no triple pattern"
  let groupVars ← match q.groupBy with
    | none => pure #[]
    | some gs => gs.toArray.mapM fun
        | .var v => pure v
        | _ => throw "GROUP BY an expression"
  let proj ← match sel with
    | .all => pure ((patVars pats).map ProjItem.var)
    | .vars items => items.toArray.mapM fun
        | .var v => pure (ProjItem.var v)
        | .expr (.aggregate .count false (.boolLit true)) a => pure (ProjItem.count a none)
        | .expr (.aggregate .count false (.var x)) a => pure (ProjItem.count a (some x))
        | .expr _ _ => throw "a SELECT expression other than COUNT(*) or COUNT(?x)"
  let agg := q.groupBy.isSome || proj.any fun | .count _ _ => true | _ => false
  if agg then
    for p in proj do
      match p with
      | .var v => unless groupVars.contains v do throw s!"?{v} is projected but not grouped"
      | _ => pure ()
  let order ← match q.modifier.orderBy with
    | none => pure #[]
    | some cs => cs.toArray.mapM fun
        | .asc (.var v) => pure (v, false)
        | .desc (.var v) => pure (v, true)
        | _ => throw "ORDER BY an expression"
  return { pats, filters, proj, groupVars, agg, order, distinct := q.modifier.distinct,
           offset := q.modifier.offset.getD 0, limit := q.modifier.limit }

/-- The stored forms the plan looks up in the vocabulary. -/
def Plan.words (p : Plan) : Array String :=
  let args := p.pats.foldl (fun a (s, q, o) => (a.push s).push q |>.push o) #[]
    ++ p.filters.foldl (fun a prog => prog.foldl (fun a op => match op with
      | .cmp _ x y => (a.push x).push y
      | _ => a) a) #[]
  args.foldl (fun a x => match x with
    | .word w => if a.contains w then a else a.push w
    | _ => a) #[]

/-! ## Terms -/

def mkWfLit (lex dt : String) (lang : Option String) : Except String WfLiteral :=
  if hdt : isIri dt = true then
    let l : Literal := { lexicalForm := lex, datatype := ⟨dt, hdt⟩, langTag := lang, direction := none }
    if h : literalWf l = true then .ok ⟨l, h⟩ else .error s!"literal {lex} {dt} is not well formed"
  else .error s!"datatype {dt} is not an IRI"

def utf8 (b : ByteArray) (what : String) : Except String String :=
  match String.fromUTF8? b with
  | some s => .ok s
  | none => .error s!"{what} is not UTF-8"

/-- A stored literal: (content, lang, datatype). -/
def splitStored (w : ByteArray) : Except String (String × Option String × Option String) := do
  let q := lastQuote w w.size (w.size - 1)
  if w.size == 0 || w.get! 0 != 34 || q == 0 then throw "vocabulary: not a literal"
  let content ← utf8 (w.extract 1 q) "literal"
  let suffix ← utf8 (w.extract (q + 1) w.size) "literal suffix"
  if suffix.isEmpty then return (content, none, none)
  if suffix.startsWith "@" then return (content, some (suffix.drop 1).toString, none)
  if suffix.startsWith "^^<" && suffix.endsWith ">" then
    return (content, none, some ((suffix.drop 3).dropEnd 1).toString)
  throw s!"vocabulary: literal suffix {suffix}"

/-- An Id as an RDF term, printed as QLever prints it. -/
def idTerm (v : Vocab) (x : Id) : Except String Term := do
  match x.decode with
  | .vocabIndex i =>
    let w ← v.wordBytes i
    if w.size ≥ 2 && w.get! 0 == 60 then
      let s ← utf8 (w.extract 1 (w.size - 1)) "IRI"
      if h : isIri s = true then return .iri ⟨s, h⟩ else throw s!"IRI {s} is not well formed"
    let (content, lang, dt) ← splitStored w
    match lang, dt with
    | some l, _ => return .literal (← mkWfLit content rdfLangString.val (some l))
    | none, some d => return .literal (← mkWfLit content d none)
    | none, none => return .literal (← mkWfLit content (xsd "string") none)
  | .int i => return .literal (← mkWfLit (Format.intLexical i) (xsd "int") none)
  | .double b =>
    let (lex, dt) := Format.doubleLexical b
    return .literal (← mkWfLit lex (xsd dt) none)
  | .bool val l01 => return .literal (← mkWfLit (Format.boolLexical val l01) (xsd "boolean") none)
  | .blankNodeIndex n => return .bnode s!"bn{n}"
  | other => throw s!"Id {x.bits}: no term for {repr other} (https://github.com/danbri/factoidal/issues/780)"

/-! ## FILTER evaluation -/

/-- Does `needle` occur in `hay` at `at`? -/
def bytesAt (hay needle : ByteArray) (at_ : Nat) : Bool := Id.run do
  if at_ + needle.size > hay.size then return false
  for j in [0:needle.size] do
    if hay.get! (at_ + j) != needle.get! j then return false
  return true

def bytesContain (hay needle : ByteArray) : Bool := Id.run do
  if needle.size > hay.size then return false
  for i in [0:hay.size - needle.size + 1] do
    if bytesAt hay needle i then return true
  return false

/-- One string-function test on a row value. `none` is an error. -/
def strTest (v : Vocab) (x : Id) (k : Nat) (needle : String) (lang : Option String) : Option Bool :=
  match x.decode with
  | .vocabIndex i =>
    match v.wordBytes i with
    | .error _ => none
    | .ok w =>
      match splitStored w with
      | .error _ => none
      | .ok (content, wl, wdt) =>
        let stringish := wl.isSome || wdt.isNone || wdt == some (xsd "string")
        let compat := match lang with
          | some l => wl == some l
          | none => true
        if !stringish || !compat then none
        else
          let h := content.toUTF8
          let n := needle.toUTF8
          some (match k with
            | 0 => bytesAt h n 0
            | 1 => n.size ≤ h.size && bytesAt h n (h.size - n.size)
            | _ => bytesContain h n)
  | _ => none

def cmpTest (op : Option CompOp) (a b : Option Id) : Option Bool :=
  match a, b with
  | some x, some y =>
    match op with
    | none => some (x.bits == y.bits)
    | some op =>
      if x.bits == y.bits && (op == .eq || op == .le || op == .ge) then some true
      else if x.bits == y.bits && (op == .ne || op == .lt || op == .gt) then some false
      else match cmpIdsCompatible x y with
        | none => none
        | some o => some (match op with
          | .eq => o == .eq | .ne => o != .eq | .lt => o == .lt
          | .gt => o == .gt | .le => o != .gt | .ge => o != .lt)
  -- one side is a term that is not in the index: it equals no stored term
  | some _, none | none, some _ =>
    match op with
    | none => some false
    | some .eq => some false
    | some .ne => some true
    | _ => none
  | none, none => none

/-- Evaluate a postfix program on row `i` of `t` (`col v` is the column of
    variable `v`). Three-valued: `none` is an error (SPARQL 17.2). -/
def evalProgram (v : Vocab) (t : Table) (col : String → Option Nat) (prog : Array FOp) (i : Nat) :
    Option Bool := Id.run do
  let val (a : Arg) : Option Id := match a with
    | .var x => (col x).map fun c => ⟨t.at c i⟩
    | .id x => some x
    | _ => none
  let mut st : Array (Option Bool) := #[]
  for op in prog do
    match op with
    | .cmp o a b =>
      let r := if a == .absent || b == .absent then cmpTest o (val a) none else cmpTest o (val a) (val b)
      st := st.push r
    | .str k x needle lang =>
      st := st.push (match col x with
        | some c => strTest v ⟨t.at c i⟩ k needle lang
        | none => none)
    | .not => st := (st.pop).push ((st.back?.getD none).map (!·))
    | .and =>
      let b := st.back?.getD none
      let a := (st.pop).back?.getD none
      let r := match a, b with
        | some false, _ | _, some false => some false
        | some true, some true => some true
        | _, _ => none
      st := (st.pop.pop).push r
    | .or =>
      let b := st.back?.getD none
      let a := (st.pop).back?.getD none
      let r := match a, b with
        | some true, _ | _, some true => some true
        | some false, some false => some false
        | _, _ => none
      st := (st.pop.pop).push r
  return st.back?.getD none

def applyFilters (v : Vocab) (filters : Array (Array FOp)) (t : Table) : Table :=
  if filters.isEmpty then t
  else t.select fun i => filters.all fun p => evalProgram v t t.idx p i == some true

/-! ## Results -/

/-- Rows `i..stop-1` of `t` as SPARQL JSON binding objects, comma-separated
    and appended to `acc` (`first`: no comma before the first). -/
def renderLoop (v : Vocab) (t : Table) (cols : Array (String × Nat)) (stop : Nat) :
    Nat → Nat → Bool → String → Except String String
  | 0, _, _, acc => .ok acc
  | k+1, i, first, acc =>
    if i ≥ stop then .ok acc
    else
      let row : Except String L4Factoidal.SPARQL.Binding :=
        cols.toList.mapM fun (name, c) => do pure (name, ← idTerm v ⟨t.at c i⟩)
      match row with
      | .error e => .error e
      | .ok b =>
        renderLoop v t cols stop k (i + 1) false
          ((if first then acc else acc ++ ",") ++ L4Factoidal.SPARQL.rowJson b)

def jsonHead (vars : Array String) : String :=
  "{\"head\":{\"vars\":[" ++ L4Factoidal.SPARQL.varListJson vars.toList ++ "]},\"results\":{\"bindings\":["

def jsonTail : String := "]}}"

/-! ## Execution -/

structure RunStats where
  plan : Array String := #[]
  rows : Nat := 0
  deriving Inhabited

/-- Resolve a `word` argument through the vocabulary lookup. -/
def resolveArg {m : Type → Type} [Monad m] (lookup : String → ExceptT String m (Option Nat)) :
    Arg → ExceptT String m Arg
  | .word s => do
    match ← lookup s with
    | some i => pure (.id (Id.ofVocabIndex i))
    | none => pure .absent
  | a => pure a

def toSlot : Arg → Slot
  | .var v => .var v
  | .id x => .const x
  | _ => .missing

/-- The variables a filter program reads. -/
def progVars (prog : Array FOp) : Array String :=
  prog.foldl (fun acc op => match op with
    | .cmp _ a b => [a, b].foldl (fun acc a => match argVar a with
        | some v => acc.push v
        | none => acc) acc
    | .str _ x _ _ => acc.push x
    | _ => acc) #[]

/-- Final modifiers on a collected table: ORDER BY, projection, DISTINCT,
    OFFSET, LIMIT. -/
def finish (plan : Plan) (t : Table) : Table := Id.run do
  let mut t := t
  if !plan.order.isEmpty then
    let keys := plan.order.filterMap fun (v, desc) => (t.idx v).map fun c => (c, desc)
    let le (i j : Nat) : Bool := Id.run do
      for (c, desc) in keys do
        let o := cmpIdsOrder ⟨t.at c i⟩ ⟨t.at c j⟩
        if o != .eq then return (if desc then o == .gt else o == .lt)
      return true
    t := t.reorder (mergeSortBy (List.range t.rows).toArray le)
  if plan.distinct then
    let cols := plan.proj.filterMap fun p => t.idx p.name
    let mut seen : Std.HashSet (List UInt64) := {}
    let mut keep : Array Nat := #[]
    for i in [0:t.rows] do
      let k := (cols.map fun c => t.at c i).toList
      if !seen.contains k then
        seen := seen.insert k
        keep := keep.push i
    t := t.reorder keep
  let hi := match plan.limit with
    | some l => plan.offset + l
    | none => t.rows
  return t.slice plan.offset hi

/-- Count the rows of `t` per group key (the Ids of the group variables). -/
def countGroups (plan : Plan) (t : Table)
    (acc : Std.HashMap (List UInt64) Nat × Array (List UInt64)) :
    Std.HashMap (List UInt64) Nat × Array (List UInt64) := Id.run do
  let gc := plan.groupVars.map fun g => (t.idx g).getD 0
  let mut h := acc.1
  let mut ks := acc.2
  for i in [0:t.rows] do
    let k := (gc.map fun c => t.at c i).toList
    match h.get? k with
    | some n => h := h.insert k (n + 1)
    | none => h := h.insert k 1; ks := ks.push k
  return (h, ks)

/-- The aggregated table: the group variables, then one `Int` column per
    COUNT. With no GROUP BY there is one group, also over no rows. -/
def groupTable (plan : Plan) (h : Std.HashMap (List UInt64) Nat) (keys : Array (List UInt64)) :
    Table := Id.run do
  let ks := if keys.isEmpty && plan.groupVars.isEmpty then #[[]] else keys
  let cnt := plan.proj.filterMap fun | .count a _ => some a | _ => none
  let mut cols := (plan.groupVars ++ cnt).map fun _ => ByteArray.empty
  for k in ks do
    let mut j := 0
    for x in k do
      cols := cols.modify j (Side.put64 · x)
      j := j + 1
    for _ in cnt do
      cols := cols.modify j (Side.put64 · (Id.ofInt (h.getD k 0)).bits)
      j := j + 1
  return { vars := plan.groupVars ++ cnt, cols, rows := ks.size }

/-- Run a translated plan. `emit` receives the SPARQL JSON text in pieces. -/
def runPlanM {m : Type → Type} [Monad m] (srcs : Array (PermSrc m)) (v : Vocab) (plan : Plan)
    (lookup : String → ExceptT String m (Option Nat)) (emit : String → m Unit) :
    ExceptT String m RunStats := do
  let pats ← plan.pats.mapM fun (s, p, o) => do
    pure ({ s := toSlot (← resolveArg lookup s), p := toSlot (← resolveArg lookup p),
            o := toSlot (← resolveArg lookup o) } : TriplePat)
  let filters ← plan.filters.mapM fun prog => prog.mapM fun op => match op with
    | .cmp o a b => do pure (FOp.cmp o (← resolveArg lookup a) (← resolveArg lookup b))
    | other => pure other
  let used : Array String :=
    plan.proj.foldl (fun a p => match p with
      | .var x => a.push x
      | .count _ (some x) => a.push x
      | .count _ none => a) #[]
    ++ filters.foldl (fun a p => a ++ progVars p) #[] ++ plan.order.map (·.1) ++ plan.groupVars
  let need (x : String) : Bool := used.contains x
  let outVars := plan.proj.map (·.name)
  let projCols (t : Table) : Array (String × Nat) :=
    plan.proj.filterMap fun p => (t.idx p.name).map fun c => (p.name, c)
  let mut stats : RunStats := {}
  emit (jsonHead outVars)
  -- the BGP, as chunks of rows
  let streamable := pats.size == 1 && !plan.agg && plan.order.isEmpty && !plan.distinct
  if streamable then
    -- one pattern, no modifier that needs all rows: block by block
    let t := pats[0]!
    if t.hasMissing then
      stats := { stats with plan := #["a constant is not in the index: no solutions"] }
    else
      let spec := mkSpec t (permFor t none) need
      let src := srcs[spec.perm]!
      let lim := plan.limit.getD (2 ^ 63)
      -- state: rows skipped, rows emitted
      let ((_, emitted), st) ← scanFoldM src spec ((0 : Nat), (0 : Nat)) fun (skipped, emitted) chunk => do
        let ch := applyFilters v filters chunk
        let skipHere := min (plan.offset - skipped) ch.rows
        let takeHere := min (lim - emitted) (ch.rows - skipHere)
        if takeHere > 0 then
          let s ← match renderLoop v ch (projCols ch) (skipHere + takeHere) (takeHere + 1) skipHere
              (emitted == 0) "" with
            | .ok s => pure s
            | .error e => throw e
          (emit s : m Unit)
        let emitted := emitted + takeHere
        pure ((skipped + skipHere, emitted), emitted < lim)
      stats := { plan := #[s!"pattern 0 streamed: {permInfos[spec.perm]!.name} key {spec.key.size}; blocks {st.blocksRead} of {st.blocksTotal}, frames {st.framesRead}, {st.bytesRead} bytes; rows {st.rowsOut}"],
                 rows := emitted }
  else
    let mut table : Table := default
    let tps : Array TriplePat := pats
    if tps.size == 1 && !(tps[0]!.hasMissing) then
      let t := tps[0]!
      let spec := mkSpec t (permFor t none) need
      if plan.agg then
        -- aggregate block by block: group key -> count
        let ((groups, keys), st) ← scanFoldM srcs[spec.perm]! spec
            (({} : Std.HashMap (List UInt64) Nat), (#[] : Array (List UInt64))) fun acc chunk =>
          pure (countGroups plan (applyFilters v filters chunk) acc, true)
        stats := { stats with plan := #[s!"pattern 0 aggregated while streaming: {permInfos[spec.perm]!.name} key {spec.key.size}; blocks {st.blocksRead} of {st.blocksTotal}, frames {st.framesRead}, {st.bytesRead} bytes; rows {st.rowsOut}; groups {keys.size}"] }
        table := groupTable plan groups keys
      else
        let (t0, st) ← scanTableM srcs[spec.perm]! spec
        stats := { stats with plan := #[s!"pattern 0: {permInfos[spec.perm]!.name} key {spec.key.size}; blocks {st.blocksRead} of {st.blocksTotal}, frames {st.framesRead}, {st.bytesRead} bytes; rows {t0.rows}"] }
        table := applyFilters v filters t0
    else
      let (t0, lines) ← evalBgpM srcs tps need
      stats := { stats with plan := lines }
      let t1 := applyFilters v filters t0
      table := if plan.agg then
          let (h, ks) := countGroups plan t1 ({}, #[])
          groupTable plan h ks
        else t1
    let out := finish plan table
    let pc := projCols out
    -- render in pieces of 4,096 rows
    let pieces := (out.rows + 4095) / 4096
    for k in [0:pieces] do
      let lo := 4096 * k
      let hi := min out.rows (lo + 4096)
      match renderLoop v out pc hi (hi - lo + 1) lo (lo == 0) "" with
      | .ok s => (emit s : m Unit)
      | .error e => throw e
    stats := { stats with rows := out.rows }
  emit jsonTail
  return stats

end L4Factoidal.Qlvr.Query
