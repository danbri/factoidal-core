/-
L4Factoidal.N3.Builtins — the N3 built-in predicates the reasoner evaluates.

Specification: Notation3 Builtin Functions (W3C N3 Community Group editor's
draft, `spec/builtins.html` at commit `1d29dea7` of https://github.com/w3c/N3,
last changed 2026-06-03; `third_party/testing/n3-PROVENANCE.md`). Each entry of
`builtinTable` names the section of that draft it implements. Design record:
`docs/designissues/2026-10-28-n3.md` § 4. Tracking:
https://github.com/danbri/factoidal/issues/1171 (step 3).

## Reuse of the SPARQL 1.2 expression evaluator

Where the draft defines a built-in by an XPath or SPARQL function, the value
is computed by `SPARQL.Expr.eval` on an expression built from the terms, so
there is one implementation of numeric arithmetic, numeric comparison,
string functions and regular expressions:

| built-in | SPARQL expression |
|---|---|
| `math:sum`, `math:difference`, `math:product`, `math:quotient` | `+`, `-`, `*`, `/` (op:numeric-add and the rest) |
| `math:negation`, `math:absoluteValue`, `math:ceiling`, `math:floor`, `math:rounded` | unary `-`, `ABS`, `CEIL`, `FLOOR`, `ROUND` |
| `math:equalTo`, `math:notEqualTo`, `math:lessThan`, `math:greaterThan`, `math:notLessThan`, `math:notGreaterThan` | `=`, `!=`, `<`, `>`, `>=`, `<=` |
| `string:concatenation` | `CONCAT` of `STR` |
| `string:startsWith`, `string:endsWith`, `string:contains` | `STRSTARTS`, `STRENDS`, `CONTAINS` |
| `string:matches`, `string:notMatches` | `REGEX` |
| `string:replace` | `REPLACE` |

A numeric argument may be a numeric literal, or a string literal whose
lexical form is a Turtle numeric literal (the draft: "math:sum ... the
subject is a list of numerical values"; the suite's `math/strings.n3` and
`math/sum.n3` give `("2" "3") math:sum 5`): `numeric?` reads such a string
with the Turtle reader's numeric terminal.

## Results

A built-in gives `none` when its predicate is not a built-in (the triple is
matched against the data), `notReady` when an argument it needs is still a
variable (the body solver tries it later), or `sols`: the substitutions under
which the triple holds, binding a variable object (or subject) to the
computed value. A computed value and a written value are compared by value
(`=` of the SPARQL evaluator), so `(2 3) math:sum 5.0` holds.

Not implemented (the triple then has no solution, and a test that needs it
fails): the trigonometric functions, `math:exponentiation` with a non-integer
argument, `string:format`, `string:scrape`, `string:containsRoughly`,
`log:semantics`, `log:content`, `log:parsedAsN3` (these read a document from
the Web or a file; with no retrieval record in this layer they are refused,
rule of 2026-10-25 on network retrieval), `log:outputString`.

No `sorry`, no `axiom`, no `partial def`.
-/
import L4Factoidal.N3.Compare
import L4Factoidal.N3.Parser
import L4Factoidal.SPARQL.Expr

namespace L4Factoidal.N3

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- A substitution: variable key (`?name`, or `_:label` for a blank node of a
rule body) to term. -/
abbrev Subst := List (String × N3Term)

def Subst.get? (σ : Subst) (k : String) : Option N3Term := (σ.find? (·.1 == k)).map (·.2)

/-- The labels of blank nodes that are variables of the rule body being
solved. -/
abbrev BVars := List BNodeId

/-- The variable key of a term, if it is a variable here. -/
def varKey (bv : BVars) : N3Term → Option String
  | .var v => some ("?" ++ v)
  | .bnode b => if bv.contains b then some ("_:" ++ b) else none
  | _ => none

/-- Recursion bound for the term functions below (a term the reader gives
nests at most `maxNesting`; a substitution can at most double it). -/
def termFuel : Nat := 2 * maxNesting + 8

/-- Replace the variables of a term by their values. -/
def subst (bv : BVars) (σ : Subst) : Nat → N3Term → N3Term
  | 0, t => t
  | f + 1, t =>
    match varKey bv t with
    | some k => (σ.get? k).getD t
    | none =>
      match t with
      | .list xs => .list (xs.map (subst bv σ f))
      | .graph ts => .graph (ts.map fun (s, p, o) => (subst bv σ f s, subst bv σ f p, subst bv σ f o))
      | t => t

def substT (bv : BVars) (σ : Subst) (t : N3Triple) : N3Triple :=
  (subst bv σ termFuel t.1, subst bv σ termFuel t.2.1, subst bv σ termFuel t.2.2)

/-- Whether a term has a variable (here) at any depth outside graph terms. -/
def hasVar (bv : BVars) : Nat → N3Term → Bool
  | 0, _ => true
  | f + 1, t =>
    match varKey bv t with
    | some _ => true
    | none =>
      match t with
      | .list xs => xs.any (hasVar bv f)
      | _ => false

/-- Two ground terms are the same term (`{}` read as `true`). -/
def termEq (a b : N3Term) : Bool :=
  a.normalize.key (fun b => "_:" ++ b) == b.normalize.key (fun b => "_:" ++ b)

/-- Each element with the rest of the list, in order. A tail call per element. -/
def picks {α : Type} (xs : List α) : List (α × List α) :=
  let rec go : List α → List α → List (α × List α) → List (α × List α)
    | [], _, acc => acc.reverse
    | x :: rest, before, acc => go rest (x :: before) ((x, before.reverse ++ rest) :: acc)
  go xs [] []

/-- The most solutions one match may give; more are dropped. -/
def maxSolutions : Nat := 4096

mutual

/-- Match a pattern term with a term: the substitutions that extend `σ` and
make them equal. A list matches member by member; a graph term matches a
graph term of the same size, triple by triple, in any order. -/
def unify (bv : BVars) (fuel : Nat) (p t : N3Term) (σ : Subst) : List Subst :=
  match fuel with
  | 0 => []
  | f + 1 =>
    match varKey bv p with
    | some k =>
        match σ.get? k with
        | some v => if termEq v t then [σ] else []
        | none => [(k, t) :: σ]
    | none =>
      match p, t with
      | .list ps, .list ts => if ps.length != ts.length then [] else unifyList bv f ps ts σ
      | .graph ps, .graph ts =>
          if ps.length != ts.length then [] else unifyGraph bv f ps ts σ
      | _, _ => if termEq p t then [σ] else []
termination_by (fuel, 0)

def unifyList (bv : BVars) (fuel : Nat) (ps ts : List N3Term) (σ : Subst) : List Subst :=
  match ps, ts with
  | [], [] => [σ]
  | p :: ps', t :: ts' =>
      (unify bv fuel p t σ).flatMap fun σ' => unifyList bv fuel ps' ts' σ'
  | _, _ => []
termination_by (fuel, ps.length + 1)

def unifyTriple (bv : BVars) (fuel : Nat) (p t : N3Triple) (σ : Subst) : List Subst :=
  (unify bv fuel p.1 t.1 σ).flatMap fun σ1 =>
    (unify bv fuel p.2.1 t.2.1 σ1).flatMap fun σ2 => unify bv fuel p.2.2 t.2.2 σ2
termination_by (fuel, 1)

/-- Each pattern triple to a different triple of `ts`. -/
def unifyGraph (bv : BVars) (fuel : Nat) (ps ts : List N3Triple) (σ : Subst) : List Subst :=
  match ps with
  | [] => if ts.isEmpty then [σ] else []
  | p :: ps' =>
      ((picks ts).flatMap fun (t, rest) =>
        (unifyTriple bv fuel p t σ).flatMap fun σ' => unifyGraph bv fuel ps' rest σ').take maxSolutions
termination_by (fuel, ps.length + 2)

end

/-- `log:includes`: every triple of the pattern matches some triple of the
graph (the same triple may serve two patterns). -/
def includesMatch (bv : BVars) (ps ts : List N3Triple) (σ : Subst) : List Subst :=
  (ps.foldl (fun (acc : List Subst) p =>
    (acc.flatMap fun σ' => ts.flatMap fun t => unifyTriple bv termFuel p t σ').take maxSolutions) [σ])

/-! ## Values -/

def xsdIri (s : String) : String := "http://www.w3.org/2001/XMLSchema#" ++ s

def isNumericDt (dt : String) : Bool :=
  ["integer", "decimal", "double", "float", "long", "int", "short", "byte",
   "nonNegativeInteger", "nonPositiveInteger", "positiveInteger", "negativeInteger",
   "unsignedLong", "unsignedInt", "unsignedShort", "unsignedByte"].any (fun n => dt == xsdIri n)

/-- A numeric literal, or a string literal whose lexical form is a Turtle
numeric literal, as a numeric literal (module header). -/
def numeric? (t : N3Term) : Option WfLiteral :=
  match t with
  | .lit l =>
      if isNumericDt l.val.datatype.val then some l
      else if l.val.datatype == xsdString then
        match readNumericLiteral 0 l.val.lexicalForm.trimAscii.toString.toList with
        | .ok ((lex, dt), _, []) =>
            match mkLiteral 0 { lexicalForm := lex, datatype := dt, langTag := none, direction := none } with
            | .ok wl => some wl
            | .error _ => none
        | _ => none
      else none
  | _ => none

/-- The value of an expression as a term. -/
def evalExpr (e : SPARQL.Expr) : Option N3Term :=
  (SPARQL.Expr.eval [] e).toTerm?.map ofRdfTerm

/-- Whether an expression is true (its effective boolean value). -/
def evalTrue (e : SPARQL.Expr) : Bool := SPARQL.ebvOrFalse (SPARQL.Expr.eval [] e)

/-- The string value of a term (`STR`): a literal's lexical form, an IRI. -/
def strValue? : N3Term → Option String
  | .lit l => some l.val.lexicalForm
  | .iri i => some i.val
  | _ => none

def strLit (s : String) : N3Term := .lit (SPARQL.mkTypedLiteral s xsdString)

def litE (l : WfLiteral) : SPARQL.Expr := .lit l

/-- A string term as an expression: the literal itself, or the string of an
IRI. -/
def strE? (t : N3Term) : Option SPARQL.Expr :=
  match t with
  | .lit l => some (.lit l)
  | .iri i => some (.lit (SPARQL.mkTypedLiteral i.val xsdString))
  | _ => none

def intLit (n : Int) : N3Term := .lit (SPARQL.mkTypedLiteral (toString n) xsdInteger)

/-! ## The built-ins -/

/-- What a built-in gives (module header). -/
inductive BResult where
  | notBuiltin
  | notReady
  | sols (l : List Subst)

def mathNs : String := "http://www.w3.org/2000/10/swap/math#"
def stringNs : String := "http://www.w3.org/2000/10/swap/string#"
def listNs : String := "http://www.w3.org/2000/10/swap/list#"

/-- The object given a computed value: bind a variable, or compare a written
value with it by value. -/
def giveValue (bv : BVars) (o : N3Term) (v : N3Term) (σ : Subst) : List Subst :=
  if (varKey bv o).isSome then unify bv termFuel o v σ
  else
    match numeric? o, numeric? v with
    | some a, some b => if evalTrue (.compare .eq (litE a) (litE b)) then [σ] else []
    | _, _ => if termEq o v then [σ] else []

/-- A list of ground numbers, folded with a binary operator from `init`. -/
def foldNumbers (op : SPARQL.ArithOp) (init : Option N3Term) (xs : List N3Term) : Option N3Term :=
  let start := match init, xs with
    | some i, _ => some (i, xs)
    | none, x :: rest => (numeric? x).map fun l => (.lit l, rest)
    | none, [] => none
  match start with
  | none => none
  | some (acc0, rest) =>
      rest.foldl (fun (acc : Option N3Term) x =>
        match acc, (acc.bind numeric?), numeric? x with
        | some _, some a, some b => evalExpr (.arith op (litE a) (litE b))
        | _, _, _ => none) (some acc0)

/-- A two-argument numeric test. -/
def numTest (bv : BVars) (op : SPARQL.CompOp) (s o : N3Term) (σ : Subst) : BResult :=
  if (varKey bv s).isSome || (varKey bv o).isSome then .notReady
  else
    match numeric? s, numeric? o with
    | some a, some b => .sols (if evalTrue (.compare op (litE a) (litE b)) then [σ] else [])
    | _, _ => .sols []

/-- A two-argument string test, on the code points of the two strings. -/
def strTest (bv : BVars) (f : String → String → Bool) (s o : N3Term) (σ : Subst) : BResult :=
  if (varKey bv s).isSome || (varKey bv o).isSome then .notReady
  else
    match strValue? s, strValue? o with
    | some a, some b => .sols (if f a b then [σ] else [])
    | _, _ => .sols []

/-- A two-argument test through a SPARQL function on two string terms. -/
def strExprTest (bv : BVars) (mk : SPARQL.Expr → SPARQL.Expr → SPARQL.Expr) (s o : N3Term)
    (σ : Subst) : BResult :=
  if (varKey bv s).isSome || (varKey bv o).isSome then .notReady
  else
    match strE? s, strE? o with
    | some a, some b => .sols (if evalTrue (mk a b) then [σ] else [])
    | _, _ => .sols []

/-- A list subject whose members are all ground. -/
def groundList? (bv : BVars) (s : N3Term) : Option (List N3Term) :=
  match s with
  | .list xs => if xs.any (hasVar bv termFuel) then none else some xs
  | _ => none

/-- A function of a ground list subject giving the object. -/
def listFn (bv : BVars) (f : List N3Term → Option N3Term) (s o : N3Term) (σ : Subst) : BResult :=
  match s with
  | .list _ =>
      match groundList? bv s with
      | none => .notReady
      | some xs =>
          match f xs with
          | some v => .sols (giveValue bv o v σ)
          | none => .sols []
  | _ => if (varKey bv s).isSome then .notReady else .sols []

/-- A function of a ground subject giving the object. -/
def unaryFn (bv : BVars) (f : N3Term → Option N3Term) (s o : N3Term) (σ : Subst) : BResult :=
  if hasVar bv termFuel s then .notReady
  else
    match f s with
    | some v => .sols (giveValue bv o v σ)
    | none => .sols []

def lowerStr (s : String) : String := Text.CaseMap.lowerCase s

/-- `math:negation` (Builtins § math:negation): either side computes the other. -/
def negation (bv : BVars) (s o : N3Term) (σ : Subst) : BResult :=
  let neg (t : N3Term) : Option N3Term := (numeric? t).bind fun l => evalExpr (.unaryMinus (litE l))
  if !hasVar bv termFuel s then
    match neg s with
    | some v => .sols (giveValue bv o v σ)
    | none => .sols []
  else if !hasVar bv termFuel o then
    match neg o with
    | some v => .sols (giveValue bv s v σ)
    | none => .sols []
  else .notReady

/-- Integer power, for `math:exponentiation` with integer arguments. -/
def intPow (b : Int) : Nat → Int
  | 0 => 1
  | n + 1 => b * intPow b n

def intOf? (t : N3Term) : Option Int :=
  match numeric? t with
  | some l => if l.val.datatype == xsdInteger then l.val.lexicalForm.trimAscii.toString.toInt? else none
  | none => none

/-- The math, string and list built-ins with a ground-argument rule
(Builtins §§ "math", "string", "list"). `log:` built-ins that need the
reasoner are in `N3/Reason.lean`. -/
def evalBuiltin (bv : BVars) (p : String) (s o : N3Term) (σ : Subst) : BResult :=
  if p.startsWith mathNs then
    match p.drop mathNs.length |>.toString with
    | "sum" => listFn bv (foldNumbers .add (some (intLit 0))) s o σ
    | "product" => listFn bv (foldNumbers .mul (some (intLit 1))) s o σ
    | "difference" => listFn bv (fun xs => if xs.length == 2 then foldNumbers .sub none xs else none) s o σ
    | "quotient" => listFn bv (fun xs => if xs.length == 2 then foldNumbers .div none xs else none) s o σ
    | "remainder" => listFn bv (fun xs => match xs with
        | [a, b] => match intOf? a, intOf? b with
          | some x, some y => if y == 0 then none else some (intLit (x.tmod y))
          | _, _ => none
        | _ => none) s o σ
    | "exponentiation" => listFn bv (fun xs => match xs with
        | [a, b] => match intOf? a, intOf? b with
          | some x, some y => if y ≥ 0 then some (intLit (intPow x y.toNat)) else none
          | _, _ => none
        | _ => none) s o σ
    | "negation" => negation bv s o σ
    | "absoluteValue" => unaryFn bv (fun t => (numeric? t).bind fun l => evalExpr (.abs (litE l))) s o σ
    | "ceiling" => unaryFn bv (fun t => (numeric? t).bind fun l => evalExpr (.ceil (litE l))) s o σ
    | "floor" => unaryFn bv (fun t => (numeric? t).bind fun l => evalExpr (.floor (litE l))) s o σ
    | "rounded" => unaryFn bv (fun t => (numeric? t).bind fun l => evalExpr (.round (litE l))) s o σ
    | "memberCount" => listFn bv (fun xs => some (intLit xs.length)) s o σ
    | "equalTo" => numTest bv .eq s o σ
    | "notEqualTo" => numTest bv .ne s o σ
    | "lessThan" => numTest bv .lt s o σ
    | "greaterThan" => numTest bv .gt s o σ
    | "notLessThan" => numTest bv .ge s o σ
    | "notGreaterThan" => numTest bv .le s o σ
    | _ => .notBuiltin
  else if p.startsWith stringNs then
    match p.drop stringNs.length |>.toString with
    | "concatenation" | "concat" =>
        listFn bv (fun xs => do
          let es ← xs.mapM strE?
          evalExpr (.concat (es.map .str))) s o σ
    | "lessThan" => strTest bv (fun a b => a < b) s o σ
    | "greaterThan" => strTest bv (fun a b => b < a) s o σ
    | "notLessThan" => strTest bv (fun a b => !(a < b)) s o σ
    | "notGreaterThan" => strTest bv (fun a b => !(b < a)) s o σ
    | "equalIgnoringCase" => strTest bv (fun a b => lowerStr a == lowerStr b) s o σ
    | "notEqualIgnoringCase" => strTest bv (fun a b => lowerStr a != lowerStr b) s o σ
    | "startsWith" => strExprTest bv (fun a b => .strStarts a b) s o σ
    | "endsWith" => strExprTest bv (fun a b => .strEnds a b) s o σ
    | "contains" => strExprTest bv (fun a b => .contains a b) s o σ
    | "containsIgnoringCase" =>
        strTest bv (fun a b => ((lowerStr a).splitOn (lowerStr b)).length > 1 || b.isEmpty) s o σ
    | "matches" => strExprTest bv (fun a b => .regex a b none) s o σ
    | "notMatches" => strExprTest bv (fun a b => .not (.regex a b none)) s o σ
    | "replace" => listFn bv (fun xs => match xs.mapM strE? with
        | some [a, pat, rep] => evalExpr (.replace a pat rep none)
        | _ => none) s o σ
    | _ => .notBuiltin
  else if p.startsWith listNs then
    match p.drop listNs.length |>.toString with
    | "length" => listFn bv (fun xs => some (intLit xs.length)) s o σ
    | "first" => listFn bv (fun xs => xs.head?) s o σ
    | "last" => listFn bv (fun xs => xs.getLast?) s o σ
    | "append" => listFn bv (fun xs => do
        let parts ← xs.mapM fun | .list ys => some ys | _ => none
        pure (.list parts.flatten)) s o σ
    | "in" =>
        match o with
        | .list xs =>
            if xs.any (hasVar bv termFuel) then .notReady
            else .sols ((xs.flatMap fun x => unify bv termFuel s x σ).take maxSolutions)
        | _ => if (varKey bv o).isSome then .notReady else .sols []
    | "member" =>
        match s with
        | .list xs =>
            if xs.any (hasVar bv termFuel) then .notReady
            else .sols ((xs.flatMap fun x => unify bv termFuel o x σ).take maxSolutions)
        | _ => if (varKey bv s).isSome then .notReady else .sols []
    | "iterate" =>
        match s with
        | .list xs =>
            if xs.any (hasVar bv termFuel) then .notReady
            else .sols (((xs.zipIdx).flatMap fun (x, i) =>
              unify bv termFuel o (.list [intLit i, x]) σ).take maxSolutions)
        | _ => if (varKey bv s).isSome then .notReady else .sols []
    | _ => .notBuiltin
  else .notBuiltin

end L4Factoidal.N3
