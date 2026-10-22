/-
L4Factoidal.Storage.Sbm11.IdQuery — SPARQL over an SBM11 generation on term
ids (stage 4, https://github.com/danbri/factoidal/issues/790; tracking
https://github.com/danbri/factoidal/issues/787). Design:
docs/designissues/2026-10-11-shardborough-vs-qlever.md section 6.9; record:
docs/designissues/2026-10-12-sbm11-stage4.md.

The module is pure and generic over the monad of a `Store` (positioned reads
of PRB1 blocks, PRM1 entries, dictionary lookups); `Harness/Sbm11Query.lean`
gives the `IO` store over verified `pread`.

## The fragment (`translate`)

`SELECT` with variables, `*`, `(COUNT(*) AS ?n)` and `(COUNT(?x) AS ?n)`
(not DISTINCT); `DISTINCT`; a WHERE clause of triple patterns, group joins,
FILTERs and `GRAPH <iri>` / `GRAPH ?g` around such a group (not nested);
`GROUP BY` variables; `ORDER BY` variables; `LIMIT`, `OFFSET`. A FILTER is
admitted when its expression is `Expr.backendLocal` (the repository's set of
operators that read only their operands) and every variable it reads occurs
in a triple pattern of the group it belongs to (so the FILTER can be applied
after the joins of the whole BGP: every such variable is bound in every row
of the group, with the same value after the join).

OPTIONAL (https://github.com/danbri/factoidal/issues/775): `{ base OPTIONAL
{ g1 } ... OPTIONAL { gk } }` at the top level of the WHERE clause, the base
a group of the fragment above, each group triple patterns of the default
graph and FILTERs over the group's own variables, every variable a group
shares with anything outside it bound by the base's triple patterns, a
FILTER beside the OPTIONALs over base variables only (`flattenOptional`).
Evaluation: `evalOptionalsM` and `OptJoin.leftOuterJoin`; an unbound
variable is the id `OptJoin.unbound` (0) in its column.

Issue 823 (https://github.com/danbri/factoidal/issues/823): a FILTER conjunct
outside `backendLocal` (REGEX, LANGMATCHES, casts, IRI(), hashes, ...), or one
that reads a variable no pattern of the WHERE clause binds, is a residual
conjunct (`FKind.residual`): the reference FILTER on the decoded terms,
applied after the joins of its group's BGP. A FILTER beside the OPTIONALs that
reads a group variable is applied after the left joins (`Plan.postFilters`).
A query whose WHERE clause is in the fragment but whose SELECT clause is not
(expressions, aggregates other than COUNT, HAVING, GROUP BY or ORDER BY an
expression, REDUCED), and every ASK and CONSTRUCT, run the WHERE clause on
ids and the reference evaluator's post-WHERE function on the decoded
solutions (`PostSpec`, `runPostM`; theorems in `IdPostTheorems`). EXISTS and
NOT EXISTS, anywhere, and DESCRIBE stay refused.

RDF 1.2 triple terms (https://github.com/danbri/factoidal/issues/792 item
1). A stored triple term has an id of tag 9 (dictionary class 7), and joins,
DISTINCT, GROUP BY and COUNT compare it by id, which is RDF term identity
(`TermIdTheorems.toId?_eq_iff`). In a triple pattern, a triple term with no
variable and no blank node inside, in the object position, is a constant
(`argOfObject`: a dictionary lookup of its class-7 key, language tags folded as
the packer folds them); a triple term with a variable or a blank node inside,
or in the subject or predicate position, is refused, and the reference
evaluator matches it. The SPARQL 1.2 functions TRIPLE, SUBJECT, PREDICATE,
OBJECT and isTRIPLE are outside `backendLocal`: in a FILTER they are residual
conjuncts, in a SELECT expression the reference post-processing evaluates
them, in both cases with the reference evaluator's own functions on the
decoded terms (`IdPostTheorems`). The key printer has no class-7 shape, so a
tag-9 id is printed by `jsonOfTerm`; ORDER BY decodes it (`orderKeysByIds?`
reads tags 1, 2 and 4 only).

Everything else is refused with a reason; the caller then runs the reference
evaluator.

## Ids and values

A BGP constant is a term: it matches by RDF term identity, so it is mapped to
its id (inline, or a dictionary lookup) and compared by id; a constant that
has no id makes its pattern empty. Ids are injective on the dictionary
(`TermIdTheorems.toId?_eq_iff`).

A FILTER conjunct is evaluated in one of three ways (section "FILTER"):

  * `?v = c` and `c = ?v` with `c` an IRI, an `xsd:string` literal or a
    language-tagged literal without direction, and `sameTerm(?v, c)`: the row
    is kept exactly when the id of `?v` is the id of `c`.
  * `STRSTARTS`, `STRENDS`, `CONTAINS` of a variable and a simple literal:
    for a dictionary literal of class `xsd:string` or `rdf:langString`, a
    test on the key bytes; for any other id, the reference evaluator.
  * any other admitted expression: the reference evaluator
    (`Expr.evalIn`, `ebvOrFalse`) on the terms of the variables it reads,
    once per distinct tuple of ids (a memo keyed by the ids).

So `FILTER(?x = 72)` over `"72"^^xsd:int` is decided by the reference
evaluator on the decoded term, by value. `#guard`s in
`Storage/Sbm11/IdQueryTests.lean` compare each fast path with the reference
evaluator on sample terms.

## ORDER BY

SPARQL 1.1 section 15.1 as the reference evaluator orders
(`sparqlOrderValue` on `Expr.evalIn` of the variable): the distinct ids of a
column are decoded, sorted with that comparison, and numbered (equal values
one number); rows are then sorted by the numbers (`sortPermByKey`, stable;
`topK` with LIMIT). The order of rows that compare equal is not specified by
SPARQL and may differ from the reference.

## Loops

Every loop over rows, blocks or ids is a `for` loop or a tail call with fuel;
WHERE trees and FILTER expressions are walked with explicit stacks.
-/
import L4Factoidal.Qlvr.Query
import L4Factoidal.Storage.Sbm11.Block
import L4Factoidal.Storage.Sbm11.TermId
import L4Factoidal.Storage.Sbm11.FrameWords
import L4Factoidal.Storage.Sbm11.Overlay
import L4Factoidal.Storage.Sbm11.OptJoin
import L4Factoidal.Storage.Sbm11.IdAgg
import L4Factoidal.Storage.Sbm11.Sip
import L4Factoidal.Storage.Sbm11.ParallelScan
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQL.ResultsJson
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.Storage.Sbm11.IdQuery

open L4Factoidal.RDF
open L4Factoidal.SPARQL (Expr CompOp QueryPattern QueryForm SelectClause SelectItem GroupCondition
  OrderCondition PatternTerm PatternSubject AggregateFn TriplePattern EvalEnv EvalResult Binding)
open L4Factoidal.Qlvr (Table gather joinVars sharedCols mergeJoin hashJoin mergeSortBy)
open L4Factoidal.Codec.Zstd (word64 word64U)
open L4Factoidal.Storage.Sbm11.Block (BlockMeta Row)

/-- Bound on the nodes of a WHERE tree or FILTER expression. -/
def maxNodes : Nat := 4096

/-! ## The plan -/

/-- A pattern position before the dictionary lookup. -/
inductive Arg where
  | var (v : String)
  | term (t : Term)
  deriving Inhabited

/-- The graph of a triple pattern: the default graph, a named graph given by
    an IRI, or a variable over the named graphs. -/
inductive GArg where
  | dflt
  | term (t : Term)
  | var (v : String)
  deriving Inhabited

structure PatSpec where
  s : Arg
  p : Arg
  o : Arg
  g : GArg
  deriving Inhabited

inductive ProjItem where
  | var (v : String)
  /-- `COUNT(*)` (`none`) or `COUNT(?x)` -/
  | count (alias : String) (arg : Option String)
  deriving Inhabited

def ProjItem.name : ProjItem → String
  | .var v => v
  | .count a _ => a

/-- An OPTIONAL group of the WHERE clause's top level (issue 775): triple
    patterns of the default graph and the LeftJoin condition as conjuncts,
    each `backendLocal` and reading only variables of `pats`. -/
structure OptGroup where
  pats : Array PatSpec
  filters : Array Expr
  /-- the group's FILTER conjuncts that the reference evaluator decides on
      decoded terms (`FKind.residual`, issue 823), applied to the group's
      rows before the left outer join, as `filters` -/
  residuals : Array Expr := #[]
  deriving Inhabited

/-- The reference post-processing of a plan (issue 823). The id path computes
    the solutions of the WHERE clause on ids, decodes them, and applies the
    reference evaluator's own post-WHERE functions to that solution sequence:
    `selectPost` (SELECT), `formHasSolution` (ASK), `formSolutions` and
    `constructGraphOf` (CONSTRUCT). `firstRows = some n`: the answer reads
    only the first `n` solutions (`firstRowsOf`), so the id path stops after
    them. -/
structure PostSpec where
  query : L4Factoidal.SPARQL.Query
  firstRows : Option Nat

structure Plan where
  pats : Array PatSpec
  /-- FILTER conjuncts; each is `backendLocal` and its variables are bound by
      the patterns of its group -/
  filters : Array Expr
  /-- FILTER conjuncts that the reference evaluator decides on the decoded
      terms of the variables they read (`FKind.residual`, issue 823): not
      `backendLocal`, or reading a variable that no pattern of the WHERE
      clause binds. Each reads only variables of its group's patterns or
      variables unbound in every row, so it is applied after the joins of
      the whole BGP (SPARQL 1.1 section 18.2.2.6 gives it the group). -/
  residuals : Array Expr := #[]
  /-- FILTER conjuncts beside the OPTIONAL groups that read a variable of a
      group: `Filter(f, LeftJoin(...))`, applied after the left outer joins
      (`FKind.residual`; an id `OptJoin.unbound` is an unbound variable) -/
  postFilters : Array Expr := #[]
  /-- the reference post-processing (issue 823); `none`: the plan's own
      projection, COUNT, ORDER BY, DISTINCT, OFFSET and LIMIT on ids -/
  post : Option PostSpec := none
  /-- the OPTIONAL groups, in order: `LeftJoin(...LeftJoin(base, g1), ..., gk)`;
      every variable a group shares with anything outside it is bound by
      `pats` -/
  optionals : Array OptGroup := #[]
  proj : Array ProjItem
  /-- the result variables (`Query.projectedVars`) -/
  outVars : Array String
  groupVars : Array String
  agg : Bool
  /-- (variable, descending) -/
  order : Array (String × Bool)
  distinct : Bool
  offset : Nat
  limit : Option Nat
  deriving Inhabited

def argOfSubject : PatternSubject → Except String Arg
  | .var v => .ok (.var v)
  | .iri i => .ok (.term (.iri i))
  | .bnode b => .ok (.var ("_bnode_" ++ b))
  | .tripleTerm _ _ _ => .error "a triple term pattern (RDF 1.2)"

def argOfTerm : PatternTerm → Except String Arg
  | .var v => .ok (.var v)
  | .iri i => .ok (.term (.iri i))
  | .bnode b => .ok (.var ("_bnode_" ++ b))
  | .literal l => .ok (.term (.literal l))
  | .tripleTerm _ _ _ => .error "a triple term pattern (RDF 1.2)"

/-- The term a triple-term pattern denotes when it has no variable and no
    blank node in it (a blank node of a query pattern is a variable, SPARQL
    1.1 section 18.1.6): the subject of every level an IRI, the predicate an
    IRI, the innermost object an IRI or a literal. `levels` holds the
    enclosing levels, innermost first; nesting is walked as a loop. `none`
    for every other pattern: the id path refuses it and the reference
    evaluator answers (https://github.com/danbri/factoidal/issues/792
    item 1). -/
def groundTermGo (levels : List (Subject × WfIri)) : PatternTerm → Option Term
  | .tripleTerm (.iri s) (.iri p) o => groundTermGo ((.iri s, p) :: levels) o
  | .iri i => some (L4Factoidal.Storage.Sbm11.wrapLevels levels (.iri i))
  | .literal l => some (L4Factoidal.Storage.Sbm11.wrapLevels levels (.literal l))
  | _ => none

/-- The object position of a triple pattern: `argOfTerm`, and a triple-term
    pattern with no variable and no blank node inside as a constant, matched
    by its id (a dictionary lookup of its class-7 key; RDF term identity, as
    every other constant, with language tags folded by `normalizeTerm` in
    the lookup). A triple-term pattern with a variable or a blank node inside
    is refused: the id path has no structural match. -/
def argOfObject : PatternTerm → Except String Arg
  | .tripleTerm s p o =>
    match groundTermGo [] (.tripleTerm s p o) with
    | some t => .ok (.term t)
    | none => .error "a triple term pattern with a variable or a blank node inside (RDF 1.2)"
  | t => argOfTerm t

def Arg.var? : Arg → Option String
  | .var v => some v
  | _ => none

def PatSpec.vars (t : PatSpec) : Array String :=
  let base := [t.s, t.p, t.o].foldl (fun acc a => match a.var? with
    | some v => if acc.contains v then acc else acc.push v
    | none => acc) #[]
  match t.g with
  | .var v => if base.contains v then base else base.push v
  | _ => base

/-- The variables of a group's triple patterns. -/
def OptGroup.vars (g : OptGroup) : Array String :=
  g.pats.foldl (fun a t => t.vars.foldl (fun a v => if a.contains v then a else a.push v) a) #[]

/-- The variables an admitted (`backendLocal`) expression reads, by an
    explicit stack. `none` for a constructor outside `backendLocal`. -/
def exprVars (e : Expr) : Option (Array String) := Id.run do
  let mut stack : Array Expr := #[e]
  let mut out : Array String := #[]
  for _ in [0:maxNodes] do
    match stack.back? with
    | none => break
    | some x =>
      stack := stack.pop
      match x with
      | .var v | .bound v => if !out.contains v then out := out.push v
      | .iri _ | .lit _ | .boolLit _ | .numericLit _ | .decimalLit _ | .doubleLit _ => pure ()
      | .arith _ a b | .compare _ a b | .and a b | .or a b | .sameTerm a b
      | .strDt a b | .strLang a b | .strStarts a b | .strEnds a b | .contains a b
      | .strBefore a b | .strAfter a b => stack := (stack.push a).push b
      | .unaryMinus a | .unaryPlus a | .not a | .isIri a | .isBlank a | .isLiteral a
      | .isNumeric a | .str a | .lang a | .datatype a | .hasLang a | .hasLangDir a
      | .langDir a | .strLen a | .uCase a | .lCase a | .encodeForUri a | .abs a | .round a
      | .ceil a | .floor a | .year a | .month a | .day a | .hours a | .minutes a
      | .seconds a | .timezone a | .tz a => stack := stack.push a
      | .strLangDir a b c | .cond a b c => stack := ((stack.push a).push b).push c
      | .substr a b none => stack := (stack.push a).push b
      | .substr a b (some c) => stack := ((stack.push a).push b).push c
      | .coalesce es | .concat es => stack := stack ++ es.toArray
      | .inList a es | .notInList a es => stack := (stack ++ es.toArray).push a
      | _ => return none
  if !stack.isEmpty then return none
  return some out

/-- The variables an EXISTS-free expression reads (`?v` and `BOUND(?v)`), by
    an explicit stack, for any constructor; `none` for `EXISTS` and `NOT
    EXISTS` (they read the active graph), an aggregate (no FILTER holds one:
    SPARQL 1.1 grammar rule [69] Constraint), or a tree of more than
    `maxNodes` nodes. The match has no catch-all arm, so a new `Expr`
    constructor does not build until it is placed here. -/
def residualVars (e : Expr) : Option (Array String) := Id.run do
  let mut stack : Array Expr := #[e]
  let mut out : Array String := #[]
  for _ in [0:maxNodes] do
    match stack.back? with
    | none => break
    | some x =>
      stack := stack.pop
      match x with
      | .var v | .bound v => if !out.contains v then out := out.push v
      | .iri _ | .lit _ | .boolLit _ | .numericLit _ | .decimalLit _ | .doubleLit _ | .now => pure ()
      | .arith _ a b | .compare _ a b | .and a b | .or a b | .sameTerm a b
      | .strDt a b | .strLang a b | .strStarts a b | .strEnds a b | .contains a b
      | .strBefore a b | .strAfter a b => stack := (stack.push a).push b
      | .unaryMinus a | .unaryPlus a | .not a | .isIri a | .isBlank a | .isLiteral a
      | .isNumeric a | .str a | .lang a | .datatype a | .iriFn a | .hasLang a | .hasLangDir a
      | .langDir a | .strLen a | .uCase a | .lCase a | .encodeForUri a | .abs a | .round a
      | .ceil a | .floor a | .md5 a | .sha1 a | .sha256 a | .sha384 a | .sha512 a
      | .year a | .month a | .day a | .hours a | .minutes a | .seconds a | .timezone a | .tz a
      | .ttSubject a | .ttPredicate a | .ttObject a | .isTriple a => stack := stack.push a
      | .strLangDir a b c | .cond a b c | .tripleTerm a b c => stack := ((stack.push a).push b).push c
      | .substr a b none | .regex a b none => stack := (stack.push a).push b
      | .substr a b (some c) | .regex a b (some c) | .replace a b c none =>
        stack := ((stack.push a).push b).push c
      | .replace a b c (some d) => stack := (((stack.push a).push b).push c).push d
      | .coalesce es | .concat es | .functionCall _ es => stack := stack ++ es.toArray
      | .inList a es | .notInList a es => stack := (stack ++ es.toArray).push a
      | .existsPat _ | .notExistsPat _ | .aggregate _ _ _ => return none
  if !stack.isEmpty then return none
  return some out

/-- The conjuncts of `a && b && ...`. `ebvOrFalse` of a conjunction is the
    conjunction of the `ebvOrFalse` of its operands
    (`ebvOrFalse_evalIn_and`), so each conjunct is a FILTER of its own. -/
def conjuncts (e : Expr) : Array Expr := Id.run do
  let mut stack : Array Expr := #[e]
  let mut out : Array Expr := #[]
  for _ in [0:maxNodes] do
    match stack.back? with
    | none => break
    | some x =>
      stack := stack.pop
      match x with
      | .and a b => stack := (stack.push b).push a
      | other => out := out.push other
  -- a pathological depth: keep the rest whole (still correct)
  return out ++ stack.reverse

/-- The variables of the triple patterns of a WHERE subtree (a `GRAPH ?g`
    variable is not counted: inside the group it is not bound). `none` for a
    subtree outside the fragment. -/
def subtreeVars (p : QueryPattern) : Option (Array String) := Id.run do
  let mut stack : Array QueryPattern := #[p]
  let mut out : Array String := #[]
  for _ in [0:maxNodes] do
    match stack.back? with
    | none => break
    | some x =>
      stack := stack.pop
      match x with
      | .bgp tps =>
        for tp in tps do
          for a in [argOfSubject tp.s, argOfTerm tp.p, argOfObject tp.o] do
            match a with
            | .ok (.var v) => if !out.contains v then out := out.push v
            | .ok _ => pure ()
            | .error _ => return none
      | .join l r => stack := (stack.push r).push l
      | .filter _ q | .graph _ q => stack := stack.push q
      | .empty => pure ()
      | _ => return none
  if !stack.isEmpty then return none
  return some out

/-- The variables bound in every solution of a WHERE subtree of the fragment:
    the variables of its triple patterns and the names `?g` of the `GRAPH ?g`
    groups inside it (`Graph(?g, P)` binds `?g` in each of its solutions,
    SPARQL 1.1 section 18.5). A `GRAPH ?g` around the subtree is not inside
    it, so its `?g` is not counted: the subtree's own solutions do not bind
    it. `none` for a subtree outside the fragment. -/
def scopeVars (p : QueryPattern) : Option (Array String) := Id.run do
  let some vs := subtreeVars p | return none
  let mut out := vs
  let mut stack : Array QueryPattern := #[p]
  for _ in [0:maxNodes] do
    match stack.back? with
    | none => break
    | some x =>
      stack := stack.pop
      match x with
      | .join l r => stack := (stack.push r).push l
      | .filter _ q => stack := stack.push q
      | .graph (.var v) q =>
        if !out.contains v then out := out.push v
        stack := stack.push q
      | .graph _ q => stack := stack.push q
      | _ => pure ()
  if !stack.isEmpty then return none
  return some out

/-- Every variable that a solution of some part of the WHERE tree can bind:
    the variables of its triple patterns and of its `GRAPH ?g` names,
    OPTIONAL groups included. A FILTER may read a variable outside its group
    when the variable is not here: then it is unbound in every row, before
    and after the joins, and the FILTER has the same value on each.
    (`flattenWhere` refuses a tree outside the fragment, so only the
    fragment's constructors need to be walked.) -/
def whereVars (p : QueryPattern) : Array String := Id.run do
  let mut stack : Array QueryPattern := #[p]
  let mut out : Array String := #[]
  for _ in [0:maxNodes] do
    match stack.back? with
    | none => break
    | some x =>
      stack := stack.pop
      match x with
      | .bgp tps =>
        for tp in tps do
          for a in [argOfSubject tp.s, argOfTerm tp.p, argOfObject tp.o] do
            match a with
            | .ok (.var v) => if !out.contains v then out := out.push v
            | _ => pure ()
      | .join l r | .leftJoin l r _ => stack := (stack.push r).push l
      | .filter _ q => stack := stack.push q
      | .graph (.var v) q =>
        if !out.contains v then out := out.push v
        stack := stack.push q
      | .graph _ q => stack := stack.push q
      | _ => pure ()
  return out

/-- One item of the WHERE walk: a pattern and the graph it reads. -/
structure WalkItem where
  p : QueryPattern
  g : GArg

/-- Split a group's FILTER into the conjuncts the id path evaluates on ids
    (`backendLocal`, every variable bound by the group) and the residual
    conjuncts (`FKind.residual`: any other EXISTS-free conjunct whose
    variables are bound by the group or by no pattern of the WHERE clause,
    `allVars`). Refused: EXISTS, NOT EXISTS, an aggregate, and a variable
    that a pattern outside the group binds (inside the group it is unbound,
    after the joins it may be bound). -/
def splitFilter (c : Expr) (inScope allVars : Array String) :
    Except String (Array Expr × Array Expr) := do
  let mut onIds : Array Expr := #[]
  let mut residual : Array Expr := #[]
  for cj in conjuncts c do
    let some vs := residualVars cj | throw "a FILTER with EXISTS, NOT EXISTS or an aggregate"
    unless cj.existsFree do throw "a FILTER with EXISTS, NOT EXISTS or an aggregate"
    unless vs.all (fun v => inScope.contains v || !allVars.contains v) do
      throw "a FILTER that reads a variable no triple pattern of its group binds"
    if cj.backendLocal && (exprVars cj).isSome && vs.all inScope.contains then onIds := onIds.push cj
    else residual := residual.push cj
  return (onIds, residual)

/-- Flatten a WHERE tree of BGPs, joins, FILTERs and one level of GRAPH: the
    triple patterns, the FILTER conjuncts on ids and the residual FILTER
    conjuncts (`splitFilter`). `allVars`: `whereVars` of the whole WHERE
    clause. -/
def flattenWhere (p : QueryPattern) (allVars : Array String) :
    Except String (Array PatSpec × Array Expr × Array Expr) := do
  let mut stack : Array WalkItem := #[⟨p, .dflt⟩]
  let mut pats : Array PatSpec := #[]
  let mut filters : Array Expr := #[]
  let mut residuals : Array Expr := #[]
  for _ in [0:maxNodes] do
    match stack.back? with
    | none => break
    | some ⟨x, g⟩ =>
      stack := stack.pop
      match x with
      | .bgp tps =>
        for tp in tps do
          pats := pats.push { s := ← argOfSubject tp.s, p := ← argOfTerm tp.p, o := ← argOfObject tp.o, g }
      | .join l r => stack := (stack.push ⟨r, g⟩).push ⟨l, g⟩
      | .filter c q =>
        let some inScope := scopeVars q | throw "a FILTER over a group outside the fragment"
        let (onIds, residual) ← splitFilter c inScope allVars
        filters := filters ++ onIds
        residuals := residuals ++ residual
        stack := stack.push ⟨q, g⟩
      | .graph n q =>
        match g with
        | .dflt => pure ()
        | _ => throw "a GRAPH inside a GRAPH"
        match subtreeVars q with
        | some _ => pure ()
        | none => throw "a GRAPH group outside the fragment"
        let gArg : GArg ← match n with
          | .iri i => pure (.term (.iri i))
          | .var v => pure (.var v)
          | _ => throw "a GRAPH name that is not an IRI or a variable"
        -- a GRAPH group with no triple pattern reads the graph names only
        if !(hasPattern q) then throw "a GRAPH group with no triple pattern"
        stack := stack.push ⟨q, gArg⟩
      | .empty => pure ()
      | _ => throw "a WHERE clause outside the fragment (OPTIONAL, UNION, MINUS, BIND, VALUES, sub-SELECT, SERVICE or a property path)"
  if !stack.isEmpty then throw s!"a WHERE clause with more than {maxNodes} nodes"
  return (pats, filters, residuals)
where
  /-- Whether a subtree holds a triple pattern. -/
  hasPattern (q : QueryPattern) : Bool := Id.run do
    let mut stack : Array QueryPattern := #[q]
    for _ in [0:maxNodes] do
      match stack.back? with
      | none => break
      | some x =>
        stack := stack.pop
        match x with
        | .bgp tps => if !tps.isEmpty then return true
        | .join l r => stack := (stack.push r).push l
        | .filter _ y | .graph _ y => stack := stack.push y
        | _ => pure ()
    return false

/-- The OPTIONAL spine of a WHERE clause: `filter* (leftJoin (... (leftJoin
    base g1 c1) ...) gk ck)` as the parser builds `{ base OPTIONAL { g1 } ...
    OPTIONAL { gk } FILTER(...) }` (the FILTERs of a group wrap the whole
    group). Returns the FILTERs around the spine, the base, and the groups
    with their conditions in order; no group when the top level has no
    OPTIONAL. -/
def optionalSpine (p : QueryPattern) : Array Expr × QueryPattern × Array (QueryPattern × Expr) :=
  Id.run do
    let mut x := p
    let mut tops : Array Expr := #[]
    for _ in [0:maxNodes] do
      match x with
      | .filter c q =>
        tops := tops.push c
        x := q
      | _ => break
    let mut groups : Array (QueryPattern × Expr) := #[]
    for _ in [0:maxNodes] do
      match x with
      | .leftJoin l r c =>
        groups := groups.push (r, c)
        x := l
      | _ => break
    return (tops, x, groups.reverse)

/-- Whether a subtree holds a GRAPH. -/
def hasGraph (q : QueryPattern) : Bool := Id.run do
  let mut stack : Array QueryPattern := #[q]
  for _ in [0:maxNodes] do
    match stack.back? with
    | none => break
    | some x =>
      stack := stack.pop
      match x with
      | .graph _ _ => return true
      | .join l r => stack := (stack.push r).push l
      | .filter _ y => stack := stack.push y
      | _ => pure ()
  return !stack.isEmpty

/-- The WHERE clause as the base (patterns, FILTER conjuncts) and the
    OPTIONAL groups (issue 775). Without a top-level OPTIONAL this is
    `flattenWhere`. With one: the base is a group of the `flattenWhere`
    fragment; a FILTER around the spine reads only variables of the base's
    triple patterns (it is applied to the base rows: every output row has
    its left row's values on them); each group is triple patterns and
    FILTERs whose variables its own triple patterns bind (no GRAPH, no
    nested OPTIONAL); a variable of a group that the base does not bind
    occurs in no other group (a well-designed pattern: every variable a
    group shares with anything outside it is bound in every left row). -/
def flattenOptional (p : QueryPattern) :
    Except String (Array PatSpec × Array Expr × Array Expr × Array Expr × Array OptGroup) := do
  let allVars := whereVars p
  let (tops, base, raw) := optionalSpine p
  if raw.isEmpty then
    let (pats, filters, residuals) ← flattenWhere p allVars
    return (pats, filters, residuals, #[], #[])
  let (pats, filters, residuals) ← flattenWhere base allVars
  if pats.isEmpty then throw "an OPTIONAL with no triple pattern before it"
  let some baseScope := scopeVars base | throw "a group before an OPTIONAL outside the fragment"
  -- A FILTER beside the OPTIONALs is `Filter(f, LeftJoin(...))` (section
  -- 18.2.2.6: its group is the whole group). Over base variables only it is
  -- applied to the base rows (each output row has its left row's values on
  -- them); otherwise after the left joins, on the rows they output.
  let mut topFilters : Array Expr := #[]
  let mut topResiduals : Array Expr := #[]
  let mut postFilters : Array Expr := #[]
  for c in tops do
    for cj in conjuncts c do
      let some vs := residualVars cj | throw "a FILTER with EXISTS, NOT EXISTS or an aggregate"
      unless cj.existsFree do throw "a FILTER with EXISTS, NOT EXISTS or an aggregate"
      if vs.all baseScope.contains then
        if cj.backendLocal && (exprVars cj).isSome then topFilters := topFilters.push cj
        else topResiduals := topResiduals.push cj
      else postFilters := postFilters.push cj
  let baseVars := pats.foldl (fun a t => t.vars.foldl (fun a v => if a.contains v then a else a.push v) a) #[]
  let mut groups : Array OptGroup := #[]
  for (r, c) in raw do
    if hasGraph r then throw "a GRAPH inside an OPTIONAL group"
    let (gp, gf, gr) ← flattenWhere r allVars
    if gp.isEmpty then throw "an OPTIONAL group with no triple pattern"
    let g0 : OptGroup := { pats := gp, filters := gf, residuals := gr }
    let (cf, cr) ← match c with
      | .boolLit true => pure (#[], #[])
      | e => do
        let mut cf : Array Expr := #[]
        let mut cr : Array Expr := #[]
        for cj in conjuncts e do
          let some vs := residualVars cj
            | throw "an OPTIONAL condition with EXISTS, NOT EXISTS or an aggregate"
          unless cj.existsFree do throw "an OPTIONAL condition with EXISTS, NOT EXISTS or an aggregate"
          unless vs.all (fun v => g0.vars.contains v || !allVars.contains v) do
            throw "an OPTIONAL condition that reads a variable the group's triple patterns do not bind"
          if cj.backendLocal && (exprVars cj).isSome && vs.all g0.vars.contains then cf := cf.push cj
          else cr := cr.push cj
        pure (cf, cr)
    groups := groups.push { g0 with filters := gf ++ cf, residuals := gr ++ cr }
  for k in [0:groups.size] do
    for v in groups[k]!.vars do
      if !baseVars.contains v then
        for j in [0:groups.size] do
          if j != k && groups[j]!.vars.contains v then
            throw s!"?{v} occurs in two OPTIONAL groups and not in the triple patterns before them"
  return (pats, filters ++ topFilters, residuals ++ topResiduals, postFilters, groups)

/-- The number of first WHERE solutions the answer of a post-processed query
    reads (`PostSpec.firstRows`), or `none` for all of them.

    * ASK with no GROUP BY, HAVING, trailing VALUES, OFFSET or LIMIT: 1.
      `formHasSolution` is then "the sequence is not empty"
      (`StoreDataset.formHasSolution_no_modifiers`), and the first solution
      decides it (`IdPostTheorems.formHasSolution_take_one`).
    * SELECT without grouping (no GROUP BY, no aggregate, no HAVING), ORDER
      BY, DISTINCT, REDUCED or trailing VALUES, with LIMIT: OFFSET + LIMIT.
      `selectPost` then evaluates the SELECT expressions row by row (the row
      number is the solution's position, so a prefix keeps it), projects and
      slices.
    * CONSTRUCT with the same restrictions (DISTINCT and REDUCED do not
      apply): OFFSET + LIMIT; `formSolutions` slices before the template is
      instantiated. -/
def firstRowsOf (q : L4Factoidal.SPARQL.Query) : Option Nat :=
  let md := q.modifier
  let plain := q.groupBy.isNone && q.having.isEmpty && q.postValues.isNone && md.orderBy.isNone
  match q.form with
  | .ask =>
    if !(q.groupsSolutions || q.postValues.isSome || md.offset.isSome || md.limit.isSome) then some 1
    else none
  | .select sel =>
    if plain && !L4Factoidal.SPARQL.selectHasAggregates sel && !md.distinct && !md.reduced then
      md.limit.map (md.offset.getD 0 + ·)
    else none
  | .construct _ => if plain then md.limit.map (md.offset.getD 0 + ·) else none
  | .describe _ => none

/-- The plan's own SELECT on ids: projection of variables, `COUNT(*)` and
    `COUNT(?x)`, GROUP BY variables, ORDER BY variables, DISTINCT, OFFSET,
    LIMIT. Anything else says why; `translate` then gives the query to the
    reference post-processing (`PostSpec`). -/
def selectOnIds (q : L4Factoidal.SPARQL.Query) (sel : SelectClause) (base : Plan)
    (patVars : Array String) : Except String Plan := do
  unless q.having.isEmpty do throw "HAVING"
  if q.postValues.isSome then throw "a trailing VALUES block"
  if q.modifier.reduced then throw "REDUCED"
  let groupVars ← match q.groupBy with
    | none => pure #[]
    | some gs => gs.toArray.mapM fun
        | .var v => pure v
        | _ => throw "GROUP BY an expression"
  for v in groupVars do
    unless patVars.contains v do throw s!"GROUP BY ?{v}, which no triple pattern binds"
  let proj ← match sel with
    | .all => pure ((L4Factoidal.SPARQL.Query.projectedVars q).toArray.map ProjItem.var)
    | .vars items => items.toArray.mapM fun
        | .var v => pure (ProjItem.var v)
        | .expr (.aggregate .count false (.boolLit true)) a => pure (ProjItem.count a none)
        | .expr (.aggregate .count false (.var x)) a =>
          if patVars.contains x then pure (ProjItem.count a (some x))
          else throw s!"COUNT(?{x}) of a variable no triple pattern binds"
        | .expr _ _ => throw "a SELECT expression other than COUNT(*) or COUNT(?x)"
  let agg := q.groupBy.isSome || proj.any fun | .count _ _ => true | _ => false
  let aliases := proj.filterMap fun | .count a _ => some a | _ => none
  if agg then
    if (match sel with | .all => true | _ => false) then throw "SELECT * with GROUP BY"
    for p in proj do
      match p with
      | .var v => unless groupVars.contains v do throw s!"?{v} is projected but not grouped"
      | _ => pure ()
    for a in aliases do
      if patVars.contains a then throw s!"the COUNT alias ?{a} is bound by a triple pattern"
  -- two items with one name
  let names := proj.map ProjItem.name
  for i in [0:names.size] do
    for j in [i + 1:names.size] do
      if names[i]! == names[j]! then throw s!"?{names[i]!} is projected twice"
  let order ← match q.modifier.orderBy with
    | none => pure #[]
    | some cs => cs.toArray.mapM fun
        | .asc (.var v) => pure (v, false)
        | .desc (.var v) => pure (v, true)
        | _ => throw "ORDER BY an expression"
  for (v, _) in order do
    let ok := if agg then groupVars.contains v || aliases.contains v else patVars.contains v
    unless ok do throw s!"ORDER BY ?{v}, which is not bound in every row"
  return { base with
           proj := proj, outVars := (L4Factoidal.SPARQL.Query.projectedVars q).toArray,
           groupVars := groupVars, agg := agg, order := order, distinct := q.modifier.distinct,
           offset := q.modifier.offset.getD 0, limit := q.modifier.limit }

/-- Accept the fragment or say why not.

    The WHERE clause must be in the id fragment (`flattenOptional`). Then:

    * a SELECT that `selectOnIds` accepts runs all on ids (`runPlanM`);
    * any other SELECT, every ASK and every CONSTRUCT run the WHERE clause on
      ids and the reference post-processing on the decoded solutions
      (`PostSpec`, `runPostM`; issue 823), when no expression outside the
      WHERE clause holds EXISTS or NOT EXISTS
      (`Query.expressionsOutsidePatternExistsFree`: they read the active
      graph, which the id path does not build);
    * DESCRIBE goes to the fallback: its description reads statements that no
      pattern of the query selects. -/
def translate (q : L4Factoidal.SPARQL.Query) : Except String Plan := do
  if let .describe _ := q.form then
    throw "DESCRIBE: the description reads statements no pattern of the query selects"
  unless q.dataset.isEmpty do throw "FROM / FROM NAMED"
  if q.pattern.mentionsFulltext then
    throw "text:query (full-text search): the reference evaluator answers it"
  let (pats, filters, residuals, postFilters, optionals) ← flattenOptional q.pattern.rewriteBnodes
  let allPats : Array PatSpec := pats ++ optionals.foldl (fun (a : Array PatSpec) (g : OptGroup) => a ++ g.pats) #[]
  let patVars := allPats.foldl
    (fun a (t : PatSpec) => t.vars.foldl (fun a v => if a.contains v then a else a.push v) a) #[]
  let base : Plan := {
    pats, filters, residuals, postFilters, optionals, proj := #[], outVars := #[],
    groupVars := #[], agg := false, order := #[], distinct := false, offset := 0,
    limit := none }
  let post (why : String) : Except String Plan := do
    unless q.expressionsOutsidePatternExistsFree do
      throw s!"{why}; EXISTS or NOT EXISTS outside the WHERE clause"
    return { base with post := some { query := q, firstRows := firstRowsOf q } }
  match q.form with
  | .select sel =>
    if pats.isEmpty then post "a WHERE clause with no triple pattern"
    else
      match selectOnIds q sel base patVars with
      | .ok plan => pure plan
      | .error why => post why
  | _ => post "not a SELECT query"

/-! ## Patterns over ids and permutations -/

inductive Slot where
  | var (v : String)
  | const (x : UInt64)
  /-- a constant with no id: the pattern has no solutions -/
  | missing
  deriving Repr, BEq, Inhabited

/-- Positions 0 subject, 1 predicate, 2 object, 3 graph. The graph of a
    default-graph pattern is `.const 0`. -/
structure Pat where
  s : Slot
  p : Slot
  o : Slot
  g : Slot
  /-- `g` is a variable over the NAMED graphs (`GRAPH ?g`): id 0 excluded -/
  named : Bool
  deriving Repr, Inhabited

def Pat.slot (t : Pat) : Nat → Slot
  | 0 => t.s
  | 1 => t.p
  | 2 => t.o
  | _ => t.g

def Pat.vars (t : Pat) : Array String := Id.run do
  let mut out : Array String := #[]
  for i in [0:4] do
    match t.slot i with
    | .var v => if !out.contains v then out := out.push v
    | _ => pure ()
  return out

def Pat.hasMissing (t : Pat) : Bool :=
  t.s == .missing || t.p == .missing || t.o == .missing || t.g == .missing

def Pat.bound (t : Pat) (i : Nat) : Bool :=
  match t.slot i with
  | .var _ => false
  | _ => true

/-- The four permutations: the triple positions of columns 0, 1, 2 (column 3
    is the graph). -/
def permOrder : Array (Array Nat) := #[#[1, 0, 2], #[1, 2, 0], #[0, 1, 2], #[2, 0, 1]]

def permNames : Array String := #["pso", "pos", "spo", "osp"]

/-- The permutation for `t`: its bound triple positions first (every set of
    bound positions is a prefix of one of the four); then position `pref`
    when that is possible. -/
def permFor (t : Pat) (pref : Option Nat) : Nat := Id.run do
  let m := ([0, 1, 2].filter t.bound).length
  let mut first : Option Nat := none
  for k in [0:permOrder.size] do
    let o := permOrder[k]!
    let prefixOk := (List.range m).all fun j => t.bound o[j]!
    if prefixOk then
      if first.isNone then first := some k
      match pref with
      | some q => if m < 3 && o[m]! == q then return k
      | none => pure ()
  return first.getD 0

/-- What a scan of one pattern reads. Columns are permutation columns 0..3. -/
structure ScanSpec where
  perm : Nat
  /-- the leading columns' values -/
  key : Array UInt64
  /-- other columns that must hold a value -/
  checks : Array (Nat × UInt64)
  /-- the graph column must not be 0 -/
  named : Bool
  outVars : Array String
  outCols : Array Nat
  /-- pairs of columns that hold one variable -/
  eqs : Array (Nat × Nat)
  deriving Repr, Inhabited

structure ScanStats where
  blocksRead : Nat := 0
  blocksSelected : Nat := 0
  blocksTotal : Nat := 0
  framesRead : Nat := 0
  bytesRead : Nat := 0
  rowsOut : Nat := 0
  /-- a scan with candidates (issue 809): selected blocks that no candidate
      can match (`Sip.mayHold`), not read -/
  sipSkipped : Nat := 0
  /-- a scan with candidates: join-key values tested against the candidates
      (the rows of the key range of every block read) -/
  keysTested : Nat := 0
  /-- a scan with candidates: rows whose other needed columns were decoded
      (the rows whose join key is a candidate) -/
  rowsGathered : Nat := 0
  /-- a scan with candidates: blocks read whose join column is a delta frame
      decoded by the word loop (`Sip.deltaFindGoW`, issue 930) -/
  sipWordBlocks : Nat := 0
  /-- rows decoded: of a full scan the rows of its table (`rowsOut`), of a
      scan with candidates the rows gathered (`ScanStats.full`,
      `ScanStats.withSip`, set once per scan by the planner) -/
  rowsDecoded : Nat := 0
  deriving Repr, Inhabited

def ScanStats.add (a b : ScanStats) : ScanStats :=
  { blocksRead := a.blocksRead + b.blocksRead, blocksSelected := a.blocksSelected + b.blocksSelected,
    blocksTotal := a.blocksTotal + b.blocksTotal, framesRead := a.framesRead + b.framesRead,
    bytesRead := a.bytesRead + b.bytesRead, rowsOut := a.rowsOut + b.rowsOut,
    sipSkipped := a.sipSkipped + b.sipSkipped, keysTested := a.keysTested + b.keysTested,
    rowsGathered := a.rowsGathered + b.rowsGathered, sipWordBlocks := a.sipWordBlocks + b.sipWordBlocks,
    rowsDecoded := a.rowsDecoded + b.rowsDecoded }

/-- The rows decoded by one full scan: the rows of its table. -/
def ScanStats.full (s : ScanStats) : ScanStats := { s with rowsDecoded := s.rowsOut }

/-- The rows decoded by one scan with candidates: the rows gathered. -/
def ScanStats.withSip (s : ScanStats) : ScanStats := { s with rowsDecoded := s.rowsGathered }

/-! ## The store -/

/-- What the id engine reads. `blockCount perm` is the number of blocks of a
    permutation (its PRM1 header); `blocksForRange perm key` the PRM1 entries
    of the blocks that may hold a row with the key prefix (`metasFor`);
    `prb perm off len` bytes of its PRB1 file; `idOf` the id of a term
    (inline or by dictionary lookup; `none` when the term has no id); `keyOf`
    the dictionary key of an id of tag 1, 2 or 3; `termOf` the term of any
    id. -/
structure Store (m : Type → Type) where
  /-- The number of blocks of a permutation (the count of its PRM1 header). -/
  blockCount : Nat → ExceptT String m Nat
  /-- The PRM1 entries of the blocks of a permutation that may hold a row
      whose first `key.size` columns are `key`, in row order: `metasFor` of
      the permutation's PRM1 entries
      (https://github.com/danbri/factoidal/issues/805). The planner asks for
      the entries of one key range; it never receives the whole PRM1 array.
      `PrmRange.rangeM` computes it by two binary searches and one read of the
      entries between, over an array (`arrayReader`, the in-memory store) or
      over positioned reads of the PRM1 file (`bytesReader`, the I/O store);
      `PrmRangeTheorems.rangeM_array` and `rangeM_bytes` prove both equal to
      `metasFor`. -/
  blocksForRange : Nat → Array UInt64 → ExceptT String m (Array BlockMeta)
  prb : Nat → Nat → Nat → ExceptT String m ByteArray
  idOf : Term → ExceptT String m (Option UInt64)
  keyOf : UInt64 → ExceptT String m ByteArray
  /-- the key of a dictionary id as a range `[a, e)` of a byte array (no
      copy) -/
  keySlice : UInt64 → ExceptT String m (ByteArray × Nat × Nat)
  termOf : UInt64 → ExceptT String m Term
  /-- the rank of the first dictionary key not below the bytes
      (`DictRange.lowerBoundM`) -/
  lowerBound : ByteArray → ExceptT String m Nat
  /-- the delta overlay of a permutation (stage 5, `Overlay.forPerm`):
      inserts and deletes in its row order, sorted; cleared graph ids. Empty
      for a generation without a delta log. -/
  ovl : Nat → L4Factoidal.Storage.Sbm11.Overlay.PermOverlay := fun _ => {}
  /-- A hint before rows `[0, n)` of a table are rendered (issue 799, stage
      1b: the divided streamed path calls it): the store may load the
      dictionary entries of their ids at once. No effect on any answer. -/
  prefetch : Option (Table → Nat → ExceptT String m Unit) := none
  /-- stage 1 (issue 799): a replacement for `scanTableM`, used by every BGP
      scan of `evalBgpM`. `none` is the single-thread path. The parallel
      driver (`Harness/Sbm11Query.lean`) sets it when `--threads` is above 1;
      it must return the table of `scanTableM` (`ParallelScanTheorems`). -/
  scanTable : Option (ScanSpec → ExceptT String m (Table × ScanStats)) := none
  /-- issue 799, KR 1.2: a replacement for `scanSipTableM` (the scan with
      candidates), used by `scanForJoinM`. `none` is the single-thread path.
      The parallel driver sets it when `--threads` is above 1; it must return
      the table and the statistics of `scanSipTableM`. -/
  scanSipTable : Option (ScanSpec → Array UInt64 → ExceptT String m (Table × ScanStats)) := none
  /-- issue 809: the right scan of a merge join takes the left values of the
      join variable as candidates when `k × left rows < estimate` for
      `sipFactor = some k` (`sipRule`; 16 by default, 0 whenever the shape
      allows it: `l4sbm11 query --sip always`); `none` never
      (`--sip off`). -/
  sipFactor : Option Nat := some 16
  /-- issue 825: a grouped SELECT that `AggStream.aggPlan?` accepts aggregates
      its id table itself (`IdAgg.aggregateM`). `false` (`l4sbm11 query
      --no-agg-ids`) decodes the rows and runs `selectPost`, as every other
      post-processed query does: the measurement of the two paths and the
      oracle of their comparison. -/
  aggOnIds : Bool := true

def ScanSpec.colPos (perm c : Nat) : Nat := if c < 3 then permOrder[perm]![c]! else 3

def mkSpec (t : Pat) (perm : Nat) (need : String → Bool) : ScanSpec := Id.run do
  let mut key : Array UInt64 := #[]
  let mut checks : Array (Nat × UInt64) := #[]
  let mut outVars : Array String := #[]
  let mut outCols : Array Nat := #[]
  let mut eqs : Array (Nat × Nat) := #[]
  let mut seen : Array (String × Nat) := #[]
  let mut leading := true
  for c in [0:4] do
    match t.slot (ScanSpec.colPos perm c) with
    | .const x =>
      if leading then key := key.push x else checks := checks.push (c, x)
    | .missing =>
      if leading then key := key.push 0 else checks := checks.push (c, 0)
    | .var v =>
      leading := false
      match seen.find? (·.1 == v) with
      | some (_, c0) => eqs := eqs.push (c0, c)
      | none =>
        seen := seen.push (v, c)
        if need v then
          outVars := outVars.push v
          outCols := outCols.push c
  return { perm, key, checks, named := t.named, outVars, outCols, eqs }

/-! ## Block metadata -/

def rowCol (r : Row) : Nat → Nat
  | 0 => r.c0
  | 1 => r.c1
  | 2 => r.c2
  | _ => r.g

/-- Columns `j..` of `r` against `key` (a tail call with fuel). -/
def prefixCmpGo (r : Row) (key : Array UInt64) : Nat → Nat → Ordering
  | 0, _ => .eq
  | f + 1, j =>
    if j < key.size then
      if rowCol r j < key[j]!.toNat then .lt
      else if key[j]!.toNat < rowCol r j then .gt
      else prefixCmpGo r key f (j + 1)
    else .eq

/-- Compare the first `key.size` columns of `r` with `key`. -/
def prefixCmp (r : Row) (key : Array UInt64) : Ordering := prefixCmpGo r key key.size 0

def selects (b : BlockMeta) (key : Array UInt64) : Bool :=
  prefixCmp b.first key != .gt && prefixCmp b.last key != .lt

def fullFor (b : BlockMeta) (key : Array UInt64) : Bool :=
  prefixCmp b.first key == .eq && prefixCmp b.last key == .eq

/-- The value of column `c` when every row of the block has the same value
    there. Columns 0..2: the first and last row agree on columns `0..c`, so
    every row between them does (the rows are sorted). Column 3 (graph): a
    block of one row, or a graph frame of 9 bytes in a block of 9 rows or
    more. The packer's encoder writes a constant frame (tag and one u64: 9
    bytes) exactly when all values are equal; a delta frame has at least one
    byte per row after its tag, a raw frame eight; activation re-encodes every
    column and compares the bytes, so an activated generation has the
    encoder's frames. -/
def colConst? (b : BlockMeta) (c : Nat) : Option Nat :=
  if c < 3 then
    if (List.range (c + 1)).all (fun j => rowCol b.first j == rowCol b.last j) then some (rowCol b.first c)
    else none
  else if b.rows == 1 || (b.rows ≥ 9 && b.len3 == 9) then some b.first.g
  else none

/-- The first block whose last row is not below the key prefix (binary
    search with fuel). -/
def firstBlockGo (metas : Array BlockMeta) (key : Array UInt64) : Nat → Nat → Nat → Nat
  | 0, l, _ => l
  | f + 1, l, h =>
    if l < h then
      let mid := (l + h) / 2
      if prefixCmp metas[mid]!.last key == .lt then firstBlockGo metas key f (mid + 1) h
      else firstBlockGo metas key f l mid
    else l

/-- Blocks `i, i + 1, ...` while the first row is not above the key prefix,
    appended to `out` (a tail call with fuel). -/
def blocksForGo (metas : Array BlockMeta) (key : Array UInt64) : Nat → Nat → Array Nat → Array Nat
  | 0, _, out => out
  | f + 1, i, out =>
    if i ≥ metas.size then out
    else if prefixCmp metas[i]!.first key == .gt then out
    else blocksForGo metas key f (i + 1) (out.push i)

/-- The indices of the blocks that may hold a row with the key prefix
    (`ScanTheorems.blocksFor_complete`). -/
def blocksFor (metas : Array BlockMeta) (key : Array UInt64) : Array Nat :=
  blocksForGo metas key metas.size (firstBlockGo metas key (Nat.log2 metas.size + 2) 0 metas.size) #[]

/-- The PRM1 entries of the blocks that `blocksFor` selects, in order: what
    `Store.blocksForRange` answers (the reference of `PrmRange.rangeM`). -/
def metasFor (metas : Array BlockMeta) (key : Array UInt64) : Array BlockMeta :=
  (blocksFor metas key).map (metas[·]!)

/-- The rows of some selected blocks: exact when every one is full. -/
def selRows (sel : Array BlockMeta) : Nat :=
  sel.foldl (fun a b => a + b.rows) 0

/-- Rows of the selected blocks: exact when every one is full. -/
def estimate (metas : Array BlockMeta) (key : Array UInt64) : Nat :=
  (blocksFor metas key).foldl (fun a i => a + metas[i]!.rows) 0

/-! ## Reading columns -/

/-- 8-byte little-endian words of a column of ids. -/
def wordsOf (xs : Array Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity (8 * xs.size)
  for x in xs do
    out := L4Factoidal.Qlvr.Side.put64 out x.toUInt64
  return out

/-- A column of `rows` copies of `x`. -/
def constWordsGo (x : UInt64) : Nat → ByteArray → ByteArray
  | 0, out => out
  | k + 1, out => constWordsGo x k (L4Factoidal.Qlvr.Side.put64 out x)

def constWords (x : UInt64) (rows : Nat) : ByteArray :=
  constWordsGo x rows (ByteArray.emptyWithCapacity (8 * rows))


/-- The bytes of the frames `need` of block `b`: one positioned read of the
    contiguous frames from the first to the last needed one. Returns the
    bytes, the start of each frame in them, and the bytes read. -/
def frameStarts (b : BlockMeta) : Array Nat := #[0, b.len0, b.len0 + b.len1, b.len0 + b.len1 + b.len2]

/-- The byte range `[lo, hi)` of a block (from its first frame) that holds
    the frames `need`: from the start of the first needed frame to the end
    of the last; `none` when no frame is needed. -/
def frameSpan (b : BlockMeta) (need : Array Bool) : Option (Nat × Nat) :=
  let lo? : Option Nat :=
    if need[0]! then some 0
    else if need[1]! then some b.len0
    else if need[2]! then some (b.len0 + b.len1)
    else if need[3]! then some (b.len0 + b.len1 + b.len2)
    else none
  let hi :=
    if need[3]! then b.len0 + b.len1 + b.len2 + b.len3
    else if need[2]! then b.len0 + b.len1 + b.len2
    else if need[1]! then b.len0 + b.len1
    else b.len0
  lo?.map fun lo => (lo, hi)

def readFrames {m : Type → Type} [Monad m] (st : Store m) (perm : Nat) (b : BlockMeta)
    (need : Array Bool) : ExceptT String m (ByteArray × Array Nat × Nat) := do
  let starts := frameStarts b
  let some (lo0, hi) := frameSpan b need | return (.empty, starts, 0)
  let bytes ← st.prb perm (b.offset + lo0) (hi - lo0)
  if bytes.size != hi - lo0 then throw s!"block at {b.offset}: short read"
  return (bytes, starts.map (· - lo0), hi - lo0)

/-- Column `c` of the block, all rows, as words (`FrameWords.decodeWords`,
    tested equal to `Column.decodeColumnAt`, which is proved equal to the
    specification decoder, `ColumnTheorems.decodeColumnAt_eq`); the frame
    must end at its PRM1 length. -/
def colAll (b : BlockMeta) (bytes : ByteArray) (starts : Array Nat) (c : Nat) : Except String ByteArray :=
  let lens : Array Nat := #[b.len0, b.len1, b.len2, b.len3]
  match L4Factoidal.Storage.Sbm11.FrameWords.decodeWordsF bytes b.rows starts[c]! with
  | some (ws, j) =>
    if j != starts[c]! + lens[c]! || ws.size != 8 * b.rows then
      .error s!"block at {b.offset}: frame {c} does not end at its length"
    else .ok ws
  | none => .error s!"block at {b.offset}: frame {c} does not decode"

/-- Rows `[lo, hi)` of column `c` as words (`FrameWords.decodeWordsRange`:
    the frame is read only up to row `hi - 1`). -/
def colRange (b : BlockMeta) (bytes : ByteArray) (starts : Array Nat) (c lo hi : Nat) :
    Except String ByteArray :=
  match L4Factoidal.Storage.Sbm11.FrameWords.decodeWordsRangeF bytes b.rows starts[c]! lo hi with
  | some ws => .ok ws
  | none => .error s!"block at {b.offset}: frame {c} does not decode"

@[inline] def at64 (col : ByteArray) (i : Nat) : UInt64 := word64 col (8 * i)

/-- Key columns `j..` of row `r` against `key` (a tail call with fuel). -/
def rowKeyCmpGo (cols : Array ByteArray) (key : Array UInt64) (r : Nat) : Nat → Nat → Ordering
  | 0, _ => .eq
  | f + 1, j =>
    if j < key.size then
      if at64 cols[j]! r < key[j]! then .lt
      else if key[j]! < at64 cols[j]! r then .gt
      else rowKeyCmpGo cols key r f (j + 1)
    else .eq

/-- Compare the key columns of row `r` with `key`. -/
def rowKeyCmp (cols : Array ByteArray) (key : Array UInt64) (r : Nat) : Ordering :=
  rowKeyCmpGo cols key r key.size 0

/-- Binary search in rows `[lo, hi)` (key order): the least row whose key
    prefix is not below `key` (`strict = false`) or is above it. -/
def keyBound (cols : Array ByteArray) (key : Array UInt64) (strict : Bool) : Nat → Nat → Nat → Nat
  | 0, lo, _ => lo
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      let c := rowKeyCmp cols key mid
      if c == .lt || (strict && c == .eq) then keyBound cols key strict fuel (mid + 1) hi
      else keyBound cols key strict fuel lo mid
    else lo

/-- Rows `i..hi-1`: keep those that pass the checks, the named-graph test and
    the repeated-variable tests; append their output columns. -/
def selectRows (cols : Array ByteArray) (checks : Array (Nat × UInt64)) (named : Bool)
    (eqs : Array (Nat × Nat)) (outCols : Array Nat) (hi : Nat) :
    Nat → Nat → Array ByteArray → Nat → Array ByteArray × Nat
  | 0, _, acc, n => (acc, n)
  | k + 1, i, acc, n =>
    if i ≥ hi then (acc, n)
    else
      let ok := checks.all (fun (c, x) => at64 cols[c]! i == x) &&
        (!named || at64 cols[3]! i != 0) &&
        eqs.all (fun (a, b) => at64 cols[a]! i == at64 cols[b]! i)
      if ok then
        let acc := (List.range outCols.size).foldl (fun acc k =>
          acc.modify k fun out => L4Factoidal.Qlvr.Side.put64 out (at64 cols[outCols[k]!]! i)) acc
        selectRows cols checks named eqs outCols hi k (i + 1) acc (n + 1)
      else selectRows cols checks named eqs outCols hi k (i + 1) acc n

/-- One block's matching rows. `consts` gives, per output variable, the value
    when it is the same in every row of the chunk (the column is then not
    filled unless `fill`). -/
structure Chunk where
  table : Table
  consts : Array (Option UInt64)
  deriving Inhabited

/-- Rows `[lo, lo + k)` of the columns as rows (a tail call from the end). -/
def rowsOfColsGo (cols : Array ByteArray) (lo : Nat) : Nat → List Row → List Row
  | 0, acc => acc
  | k + 1, acc =>
    rowsOfColsGo cols lo k
      (⟨(at64 cols[0]! (lo + k)).toNat, (at64 cols[1]! (lo + k)).toNat,
        (at64 cols[2]! (lo + k)).toNat, (at64 cols[3]! (lo + k)).toNat⟩ :: acc)

/-- Rows as four columns of words: a tail call with each column its own
    argument, so every column has one reference and each push is in place
    (an array of the four columns, read with `cs[0]!` and rebuilt, copied
    every column on every row: q01 over the overlay took 40 ms for 7 blocks). -/
def colsOfRowsGo : List Row → ByteArray → ByteArray → ByteArray → ByteArray → Array ByteArray
  | [], a, b, c, d => #[a, b, c, d]
  | r :: rs, a, b, c, d =>
    let put := L4Factoidal.Qlvr.Side.put64
    colsOfRowsGo rs (put a r.c0.toUInt64) (put b r.c1.toUInt64) (put c r.c2.toUInt64) (put d r.g.toUInt64)

def colsOfRows (rows : List Row) (n : Nat) : Array ByteArray :=
  colsOfRowsGo rows (ByteArray.emptyWithCapacity (8 * n)) (ByteArray.emptyWithCapacity (8 * n))
    (ByteArray.emptyWithCapacity (8 * n)) (ByteArray.emptyWithCapacity (8 * n))

/-- A chunk of rows (all four columns known): every check of the scan applied
    row by row (`selectRows`). -/
def chunkOfRows (spec : ScanSpec) (rows : List Row) (sortVar : Option String) : Chunk :=
  let n := rows.length
  let cols := colsOfRows rows n
  let (out, k) := selectRows cols spec.checks spec.named spec.eqs spec.outCols n (n + 1) 0
    (spec.outVars.map fun _ => ByteArray.emptyWithCapacity (8 * n)) 0
  { table := { vars := spec.outVars, cols := out, rows := k, sortVar },
    consts := spec.outVars.map fun _ => none }

/-- Columns `c, c + 1, ...` (`k` of them) of a block in full, as words
    (`colAll`), appended to `acc`; the first error stops (a tail call with
    a count). -/
def colsAllGo (b : BlockMeta) (bytes : ByteArray) (starts : Array Nat) :
    Nat → Nat → Array ByteArray → Except String (Array ByteArray)
  | 0, _, acc => .ok acc
  | k + 1, c, acc =>
    match colAll b bytes starts c with
    | .ok w => colsAllGo b bytes starts k (c + 1) (acc.push w)
    | .error e => .error e

/-- A pure `Except` in the scan's monad. -/
@[inline] def ofExceptM {m : Type → Type} [Monad m] {α : Type} : Except String α → ExceptT String m α
  | .ok a => pure a
  | .error e => throw e

/-- A block with overlay rows in its range: all four frames are read and
    decoded, the rows with the key prefix are merged with the deletes, the
    cleared graphs and the inserts (`Overlay.mergeRows`, proved:
    `OverlayTheorems.mergeRows_spec`), and the checks run per row. Returns
    the chunk and the bytes read. -/
def overlayChunkM {m : Type → Type} [Monad m] (st : Store m) (spec : ScanSpec) (b : BlockMeta)
    (ins del : List Row) (cleared : Array Nat) (sortVar : Option String) :
    ExceptT String m (Chunk × Nat) := do
  let (bytes, starts, nbytes) ← readFrames st spec.perm b #[true, true, true, true]
  let cols ← ofExceptM (colsAllGo b bytes starts 4 0 #[])
  let fuel := Nat.log2 b.rows + 2
  let lo := keyBound cols spec.key false fuel 0 b.rows
  let hi := keyBound cols spec.key true fuel lo b.rows
  let base := rowsOfColsGo cols lo (hi - lo) []
  let merged := L4Factoidal.Storage.Sbm11.Overlay.mergeRows (fun g => cleared.contains g) base del ins
  return (chunkOfRows spec merged sortVar, nbytes)

/-! ## The scan, block by block

`scanFoldM` asks the store for the PRM1 entries of the selected blocks
(`Store.blocksForRange`, `metasFor`: the blocks `blocksFor` returns) and is a
`forIn` over their positions, with the body `scanBlockM`. For each block the
work is split into pure functions:

  * `blockPlan`: what the PRM1 entry decides (`selects` is tested first):
    the checks that fail for every row (`skip`), the checks left to test row
    by row, the named-graph test, the `full` shortcut;
  * `needOf`: the frames to read;
  * `readFrames`: one positioned read (the only store access);
  * `blockChunk`: from the frame bytes to the chunk.

`ScanFoldTheorems.scanFoldM_tuples` proves, over an in-memory store of an
admitted permutation with no overlay, that the chunks are the rows of the
permutation with the key prefix that pass the checks, the named-graph test
and the repeated-variable tests, projected to the output columns, in row
order. -/

/-- The checks of a block that `colConst?` decides: `skip` becomes true when
    one fails for every row; the undecided checks are kept (a tail call over
    the list). -/
def planChecksGo (b : BlockMeta) : List (Nat × UInt64) → Bool → Array (Nat × UInt64) →
    Bool × Array (Nat × UInt64)
  | [], skip, acc => (skip, acc)
  | (c, x) :: cs, skip, acc =>
    match colConst? b c with
    | some y => planChecksGo b cs (skip || y != x.toNat) acc
    | none => planChecksGo b cs skip (acc.push (c, x))

/-- What the PRM1 entry of a block decides. -/
structure BlockPlan where
  /-- a check or the named-graph test fails for every row -/
  skip : Bool
  /-- the checks to test row by row -/
  checks : Array (Nat × UInt64)
  /-- the named-graph test is needed row by row -/
  named : Bool
  /-- every row carries the key prefix (`fullFor`) -/
  full : Bool

def blockPlan (spec : ScanSpec) (b : BlockMeta) : BlockPlan :=
  let (skip, checks) := planChecksGo b spec.checks.toList false #[]
  let (skip, named) :=
    if spec.named then
      match colConst? b 3 with
      | some 0 => (true, true)
      | some _ => (skip, false)
      | none => (skip, true)
    else (skip, false)
  { skip, checks, named, full := fullFor b spec.key }

def BlockPlan.perRow (bp : BlockPlan) (spec : ScanSpec) : Bool :=
  !bp.checks.isEmpty || bp.named || !spec.eqs.isEmpty

/-- Per output column, its value when the block is `full` and the column is
    constant over the block. -/
def constOutOf (spec : ScanSpec) (b : BlockMeta) (bp : BlockPlan) : Array (Option Nat) :=
  spec.outCols.map fun c => if bp.full then colConst? b c else none

/-- Whether output `k` or a later one reads column `c` (a tail call). -/
def outNeedGo (outCols : Array Nat) (constOut : Array (Option Nat)) (perRow : Bool) (c : Nat) :
    Nat → Nat → Bool
  | 0, _ => false
  | f + 1, k =>
    if outCols[k]! == c && ((constOut[k]!).isNone || perRow) then true
    else outNeedGo outCols constOut perRow c f (k + 1)

/-- Whether the chunk reads column `c`: a key column (unless `full`), a
    checked column, the graph for the named-graph test, a column of a
    repeated variable, an output column that is not constant (or any output
    column when rows are tested one by one). -/
def needCol (spec : ScanSpec) (bp : BlockPlan) (constOut : Array (Option Nat)) (c : Nat) : Bool :=
  (!bp.full && decide (c < spec.key.size)) || bp.checks.any (fun ck => ck.1 == c) ||
    (bp.named && c == 3) || spec.eqs.any (fun e => e.1 == c || e.2 == c) ||
    outNeedGo spec.outCols constOut (bp.perRow spec) c spec.outCols.size 0

def needOf (spec : ScanSpec) (bp : BlockPlan) (constOut : Array (Option Nat)) : Array Bool :=
  #[needCol spec bp constOut 0, needCol spec bp constOut 1, needCol spec bp constOut 2,
    needCol spec bp constOut 3]

/-- Column `c` cut to rows `[lo, hi)`: empty when not needed; from the full
    key column when there is one; else by the range decoder. -/
def cutCol (b : BlockMeta) (bytes : ByteArray) (starts : Array Nat) (need : Array Bool)
    (keyWords : Array ByteArray) (lo hi c : Nat) : Except String ByteArray :=
  if need[c]! then
    if h : c < keyWords.size then .ok (keyWords[c].extract (8 * lo) (8 * hi))
    else colRange b bytes starts c lo hi
  else .ok .empty

/-- The key columns `0 .. k - 1` of a block in full; none when the block is
    `full` (every row carries the key prefix). -/
def keyWordsOf (b : BlockMeta) (bytes : ByteArray) (starts : Array Nat) (full : Bool) (k : Nat) :
    Except String (Array ByteArray) :=
  if full then .ok #[] else colsAllGo b bytes starts k 0 #[]

/-- The rows `[lo, hi)` of a block that carry the key prefix: all rows when
    the block is `full`; else two binary searches over the key columns. -/
def keyRange (spec : ScanSpec) (b : BlockMeta) (full : Bool) (keyWords : Array ByteArray) : Nat × Nat :=
  if full then (0, b.rows)
  else
    let fuel := Nat.log2 b.rows + 2
    let lo := keyBound keyWords spec.key false fuel 0 b.rows
    (lo, keyBound keyWords spec.key true fuel lo b.rows)

/-- The chunk of `n` rows from the cut columns: the row tests
    (`selectRows`) or, with none, the columns as they are (a constant output
    column filled, or left empty and given in `consts` when `fill = false`). -/
def chunkOfCols (spec : ScanSpec) (fill : Bool) (sortVar : Option String) (bp : BlockPlan)
    (constOut : Array (Option Nat)) (cols : Array ByteArray) (n : Nat) : Chunk :=
  if bp.perRow spec then
    let (out, k) := selectRows cols bp.checks bp.named spec.eqs spec.outCols n (n + 1) 0
      (spec.outVars.map fun _ => ByteArray.emptyWithCapacity (8 * n)) 0
    { table := { vars := spec.outVars, cols := out, rows := k, sortVar },
      consts := spec.outVars.map fun _ => none }
  else
    let outs := (List.range spec.outCols.size).toArray.map fun k =>
      match constOut[k]! with
      | some x => if fill then constWords x.toUInt64 n else ByteArray.empty
      | none => cols[spec.outCols[k]!]!
    { table := { vars := spec.outVars, cols := outs, rows := n, sortVar },
      consts := constOut.map (·.map Nat.toUInt64) }

/-- The chunk of one block from the bytes of its needed frames: the key
    columns in full (to find the rows with the key prefix, unless `full`),
    then every needed column for those rows only (`cutCol`), then
    `chunkOfCols`. -/
def blockChunk (spec : ScanSpec) (fill : Bool) (sortVar : Option String) (b : BlockMeta)
    (bp : BlockPlan) (constOut : Array (Option Nat)) (need : Array Bool) (bytes : ByteArray)
    (starts : Array Nat) : Except String Chunk := do
  let keyWords ← keyWordsOf b bytes starts bp.full spec.key.size
  let (lo, hi) := keyRange spec b bp.full keyWords
  -- columns cut to rows [lo, hi): row r of the chunk is row lo + r
  let c0 ← cutCol b bytes starts need keyWords lo hi 0
  let c1 ← cutCol b bytes starts need keyWords lo hi 1
  let c2 ← cutCol b bytes starts need keyWords lo hi 2
  let c3 ← cutCol b bytes starts need keyWords lo hi 3
  pure (chunkOfCols spec fill sortVar bp constOut #[c0, c1, c2, c3] (hi - lo))

/-- The state of the scan between blocks. -/
structure ScanState (σ : Type) where
  acc : σ
  stats : ScanStats
  /-- the next overlay insert not yet given to a chunk -/
  insPos : Nat
  /-- `f` asked to stop -/
  stopped : Bool

/-- The delta overlay of a scan (stage 5): the permutation's overlay and its
    inserts with the key prefix, in row order. -/
structure OvCtx where
  ov : L4Factoidal.Storage.Sbm11.Overlay.PermOverlay
  on : Bool
  insK : Array Row
  insFuel : Nat
  delFuel : Nat

def ovCtx (ov : L4Factoidal.Storage.Sbm11.Overlay.PermOverlay) (key : Array UInt64) : OvCtx :=
  let on := !ov.isEmpty
  let insK : Array Row := if on then ov.ins.filter (fun r => prefixCmp r key == .eq) else #[]
  { ov, on, insK, insFuel := Nat.log2 insK.size + 2, delFuel := Nat.log2 ov.del.size + 2 }

/-- `f`'s answer as the loop's step. -/
@[inline] def stepOf {σ : Type} (s : ScanState σ) (acc : σ) (stats : ScanStats) (insPos : Nat)
    (more : Bool) : ForInStep (ScanState σ) :=
  if more then .yield { s with acc, stats, insPos }
  else .done { s with acc, stats, insPos, stopped := true }

/-- One block of the scan. With an overlay, a block that holds inserts,
    deletes or cleared graphs in its range is read whole and merged
    (`overlayChunkM`); each insert with the key prefix goes to the first
    selected block whose last row is not below it. -/
def scanBlockM {m : Type → Type} [Monad m] {σ : Type} (st : Store m) (spec : ScanSpec) (fill : Bool)
    (f : σ → Chunk → ExceptT String m (σ × Bool)) (metas : Array BlockMeta) (sortVar : Option String)
    (ox : OvCtx) (i : Nat) (s : ScanState σ) : ExceptT String m (ForInStep (ScanState σ)) := do
  let b := metas[i]!
  if !selects b spec.key then return .yield s
  let bp := blockPlan spec b
  if ox.on then
    let insEnd := L4Factoidal.Storage.Sbm11.Overlay.upperIdx ox.insK b.last ox.insFuel s.insPos ox.insK.size
    let dLo := L4Factoidal.Storage.Sbm11.Overlay.lowerIdx ox.ov.del b.first ox.delFuel 0 ox.ov.del.size
    let dHi := L4Factoidal.Storage.Sbm11.Overlay.upperIdx ox.ov.del b.last ox.delFuel dLo ox.ov.del.size
    let clHit := !ox.ov.cleared.isEmpty && (match colConst? b 3 with
      | some g => ox.ov.cleared.contains g
      | none => true)
    if insEnd > s.insPos || (!bp.skip && (dHi > dLo || clHit)) then
      let insL := L4Factoidal.Storage.Sbm11.Overlay.sliceList ox.insK s.insPos (insEnd - s.insPos) []
      let delL := L4Factoidal.Storage.Sbm11.Overlay.sliceList ox.ov.del dLo (dHi - dLo) []
      let (chunk, nbytes) ← overlayChunkM st spec b insL delL ox.ov.cleared sortVar
      let stats := { s.stats with blocksSelected := s.stats.blocksSelected + 1,
                                  blocksRead := s.stats.blocksRead + 1, framesRead := s.stats.framesRead + 4,
                                  bytesRead := s.stats.bytesRead + nbytes,
                                  rowsOut := s.stats.rowsOut + chunk.table.rows }
      let (acc', more) ← f s.acc chunk
      return stepOf s acc' stats insEnd more
  if bp.skip then return .yield s
  let stats := { s.stats with blocksSelected := s.stats.blocksSelected + 1 }
  let constOut := constOutOf spec b bp
  let need := needOf spec bp constOut
  let (bytes, starts, nbytes) ← readFrames st spec.perm b need
  let stats := if need.any id then
      { stats with blocksRead := stats.blocksRead + 1, framesRead := stats.framesRead + (need.filter id).size,
                   bytesRead := stats.bytesRead + nbytes }
    else stats
  let chunk ← ofExceptM (blockChunk spec fill sortVar b bp constOut need bytes starts)
  let stats := { stats with rowsOut := stats.rowsOut + chunk.table.rows }
  let (acc', more) ← f s.acc chunk
  return stepOf s acc' stats s.insPos more

/-- Scan block by block; `f` gets each block's rows and says whether to go
    on. With `fill = false` a column that is constant over a chunk is left
    empty and given in `consts` (the aggregate path counts it so). With an
    overlay, the inserts after the last selected block form a last chunk. -/
def scanFoldM {m : Type → Type} [Monad m] {σ : Type} (st : Store m) (spec : ScanSpec) (fill : Bool)
    (init : σ) (f : σ → Chunk → ExceptT String m (σ × Bool)) : ExceptT String m (σ × ScanStats) := do
  -- the PRM1 entries of the selected blocks only (issue 805)
  let sel ← st.blocksForRange spec.perm spec.key
  let total ← st.blockCount spec.perm
  let sortVar := match spec.outCols[0]? with
    | some c => if c == spec.key.size then spec.outVars[0]? else none
    | none => none
  let ox := ovCtx (st.ovl spec.perm) spec.key
  let s0 : ScanState σ := { acc := init, stats := { blocksTotal := total }, insPos := 0, stopped := false }
  let s ← forIn (List.range sel.size) s0 (scanBlockM st spec fill f sel sortVar ox)
  if ox.on && !s.stopped && s.insPos < ox.insK.size then
    let chunk := chunkOfRows spec
      (L4Factoidal.Storage.Sbm11.Overlay.sliceList ox.insK s.insPos (ox.insK.size - s.insPos) []) sortVar
    let (acc', _) ← f s.acc chunk
    return (acc', { s.stats with rowsOut := s.stats.rowsOut + chunk.table.rows })
  return (s.acc, s.stats)

/-- The whole scan as one table. -/
def scanTableM {m : Type → Type} [Monad m] (st : Store m) (spec : ScanSpec) :
    ExceptT String m (Table × ScanStats) := do
  let sel ← st.blocksForRange spec.perm spec.key
  let sortVar := match spec.outCols[0]? with
    | some c => if c == spec.key.size then spec.outVars[0]? else none
    | none => none
  let cap := 8 * selRows sel
  let init : Table := { vars := spec.outVars, cols := spec.outVars.map fun _ => ByteArray.emptyWithCapacity cap,
                        rows := 0, sortVar }
  scanFoldM st spec true init fun acc ch => pure (acc.append ch.table, true)

/-- The sort variable of a scan's output (the first output column, when it is
    the key's successor column), as `scanFoldM` computes it. -/
def sortVarOf (spec : ScanSpec) : Option String :=
  match spec.outCols[0]? with
  | some c => if c == spec.key.size then spec.outVars[0]? else none
  | none => none

/-- The scan of a list of selected blocks (in the given order) with `f`, from
    the state `init`, as `scanFoldM` runs its loop. The parallel scan
    (`Harness/Sbm11Query.lean`, issue 799) runs one such loop per block range
    and appends the results in range order
    (`ParallelScanTheorems.parallel_acc_eq`). -/
def scanListM {m : Type → Type} [Monad m] {σ : Type} (st : Store m) (spec : ScanSpec) (fill : Bool)
    (init : σ) (f : σ → Chunk → ExceptT String m (σ × Bool)) (metas : Array BlockMeta)
    (sortVar : Option String) (ox : OvCtx) (sel : List Nat) : ExceptT String m (σ × ScanStats) := do
  let s ← forIn sel { acc := init, stats := {}, insPos := 0, stopped := false }
    (scanBlockM st spec fill f metas sortVar ox)
  return (s.acc, s.stats)

/-! ## A count from the PRM1 entries (https://github.com/danbri/factoidal/issues/932)

A COUNT with no FILTER, no GROUP BY and no delta overlay needs only the number
of rows the scan keeps. For most blocks the PRM1 entry gives that number
(`metaStep`): 0 when the block is not selected or a check fails on a column
that is constant over the block; all its rows when every row carries the key
prefix (`fullFor`), every check is on a constant column, and the scan has no
repeated variable and no named-graph test. `metaCountM` adds those numbers in
one loop over the entries (`metaSplitGo`) and scans only the other blocks,
with `scanBlockM` and a count as the accumulator (`countAdd`).
`MetaCountTheorems.metaCountM_eq_scan`: over an admitted permutation in memory
with no overlay, the count is the length of the tuple list of the scan
(`ScanFoldTheorems.scanFoldM_tuples`). -/

/-- A check fails for every row of the block: its column is constant over
    the block with another value. -/
def checkFails (b : BlockMeta) (ck : Nat × UInt64) : Bool :=
  match colConst? b ck.1 with
  | some y => y != ck.2.toNat
  | none => false

/-- The rows of the block that the scan keeps, when the PRM1 entry gives it;
    `none` when the block must be read. -/
def metaStep (spec : ScanSpec) (b : BlockMeta) : Option Nat :=
  if !selects b spec.key || spec.checks.any (checkFails b) then some 0
  else if fullFor b spec.key && spec.checks.all (fun ck => (colConst? b ck.1).isSome) &&
      spec.eqs.isEmpty && !spec.named then some b.rows
  else none

/-- Over the entries `i, i + 1, ...`: the sum of `metaStep` of the blocks it
    gives, and the positions of the other blocks, in order (a tail call with
    fuel). -/
def metaSplitGo (spec : ScanSpec) (metas : Array BlockMeta) : Nat → Nat → Nat → Array Nat → Nat × Array Nat
  | 0, _, n, rest => (n, rest)
  | f + 1, i, n, rest =>
    if i < metas.size then
      match metaStep spec metas[i]! with
      | some r => metaSplitGo spec metas f (i + 1) (n + r) rest
      | none => metaSplitGo spec metas f (i + 1) n (rest.push i)
    else (n, rest)

/-- The count accumulator of a scan: the rows of each chunk. -/
@[inline] def countAdd {m : Type → Type} [Monad m] (acc : Nat) (ch : Chunk) : ExceptT String m (Nat × Bool) :=
  pure (acc + ch.table.rows, true)

/-- The number of rows the scan of `spec` keeps, the number of blocks decided
    by their PRM1 entries, and the statistics of the scan of the others. The
    caller uses it only when the overlay of the permutation is empty. -/
def metaCountM {m : Type → Type} [Monad m] (st : Store m) (spec : ScanSpec) :
    ExceptT String m (Nat × Nat × ScanStats) := do
  let sel ← st.blocksForRange spec.perm spec.key
  let total ← st.blockCount spec.perm
  let (n, rest) := metaSplitGo spec sel sel.size 0 0 #[]
  let ox := ovCtx (st.ovl spec.perm) spec.key
  let s ← forIn rest.toList
    ({ acc := n, stats := { blocksTotal := total }, insPos := 0, stopped := false } : ScanState Nat)
    (scanBlockM st spec false countAdd sel (sortVarOf spec) ox)
  return (s.acc, sel.size - rest.size, s.stats)

/-- `scanTableM`, or the store's `scanTable` when it sets one (stage 1). -/
def scanTableOf {m : Type → Type} [Monad m] (st : Store m) (spec : ScanSpec) :
    ExceptT String m (Table × ScanStats) :=
  match st.scanTable with
  | some f => f spec
  | none => scanTableM st spec

/-! ## Sideways information passing (https://github.com/danbri/factoidal/issues/809)

A scan with candidates returns the rows of the scan whose value in column
`jc = spec.key.size` (the column after the key: the sort variable of the
scan, the join variable of the merge join that consumes it) is a candidate.
`SipScanTheorems.scanFoldSipM_tuples`: over an in-memory store with no
overlay and candidates in non-decreasing order, the tuples are those of
`scanFoldM` restricted to the rows whose column `jc` holds a candidate.

Per block: blocks the PRM1 entry rules out are skipped as in `scanBlockM`;
then a block whose first and last rows bound column `jc` below and above
every candidate (`sipRange`, `Sip.mayHold`) is skipped unread; then the
needed frames and the `jc` frame are read, the key range is found as in
`blockChunk`, and `sipChunk` decodes the `jc` frame, finds the rows whose
value is a candidate, and decodes the other needed columns at those rows
only. -/

/-- The values column `c` can hold in the rows of block `b` that carry the
    key prefix: from the first row's value when the first row carries the
    prefix (else 0) to the last row's value when the last row carries it
    (else the largest word). The rows are sorted, so a row with the prefix
    has its column `c = key.size` between them. -/
def sipRange (b : BlockMeta) (key : Array UInt64) (c : Nat) : UInt64 × UInt64 :=
  (if prefixCmp b.first key == .eq then (rowCol b.first c).toUInt64 else 0,
   if prefixCmp b.last key == .eq then (rowCol b.last c).toUInt64 else 0xFFFFFFFFFFFFFFFF)

/-- Column `c` of the chunk at the found rows `pos`: for the join column
    `jc` the found values `jw`; for a needed key column its decoded words at
    `pos`; for any other needed column the words of its frame at `pos`
    (`Sip.gatherWords`). -/
def sipCol (b : BlockMeta) (bytes : ByteArray) (starts : Array Nat) (need : Array Bool)
    (keyWords : Array ByteArray) (jc : Nat) (jw : ByteArray) (pos : Array Nat) (c : Nat) :
    Except String ByteArray :=
  if c == jc then .ok jw
  else if need[c]! then
    if h : c < keyWords.size then .ok (Sip.pickWords keyWords[c] pos)
    else match Sip.gatherWords bytes b.rows starts[c]! pos with
      | some w => .ok w
      | none => .error s!"block at {b.offset}: frame {c} does not decode"
  else .ok .empty

/-- The chunk of one block with candidates: the key range as in
    `blockChunk`, the rows of the range whose column `jc` value is a
    candidate (`Sip.findWords`, from the candidate pointer `p`), every
    needed column at those rows (`sipCol`), then `chunkOfCols` with
    `fill = true`. Also returns the join-key values tested and the rows
    found. -/
def sipChunk (spec : ScanSpec) (cands : Array UInt64) (sortVar : Option String) (b : BlockMeta)
    (bp : BlockPlan) (constOut : Array (Option Nat)) (need : Array Bool) (bytes : ByteArray)
    (starts : Array Nat) (p : Nat) : Except String (Chunk × Nat × Nat) := do
  let keyWords ← keyWordsOf b bytes starts bp.full spec.key.size
  let (lo, hi) := keyRange spec b bp.full keyWords
  let jc := spec.key.size
  match Sip.findWords bytes b.rows starts[jc]! lo hi cands p with
  | none => throw s!"block at {b.offset}: frame {jc} does not decode"
  | some (pos, jw) =>
    let c0 ← sipCol b bytes starts need keyWords jc jw pos 0
    let c1 ← sipCol b bytes starts need keyWords jc jw pos 1
    let c2 ← sipCol b bytes starts need keyWords jc jw pos 2
    let c3 ← sipCol b bytes starts need keyWords jc jw pos 3
    pure (chunkOfCols spec true sortVar bp constOut #[c0, c1, c2, c3] pos.size, hi - lo, pos.size)

/-- Whether `w` is a candidate (`cands` in non-decreasing order). -/
@[inline] def sipMem (cands : Array UInt64) (w : UInt64) : Bool :=
  let q := Sip.probeFrom cands w (Sip.lbHint cands w)
  q < cands.size && cands[q]! == w

/-- The rows of a chunk whose first output column (the column `jc`) holds a
    candidate: the delta overlay's chunks, which are built from merged rows. -/
def sipFilterChunk (cands : Array UInt64) (ch : Chunk) : Chunk :=
  let t := ch.table
  if t.cols.isEmpty then ch
  else { ch with table := t.select fun i => sipMem cands (t.at 0 i) }

/-- One block of a scan with candidates. With an overlay, a block that holds
    overlay rows in its range is merged as in `scanBlockM` and its chunk
    filtered (`sipFilterChunk`). -/
def scanBlockSipM {m : Type → Type} [Monad m] {σ : Type} (st : Store m) (spec : ScanSpec)
    (cands : Array UInt64) (f : σ → Chunk → ExceptT String m (σ × Bool)) (metas : Array BlockMeta)
    (sortVar : Option String) (ox : OvCtx) (i : Nat) (s : ScanState σ) :
    ExceptT String m (ForInStep (ScanState σ)) := do
  let b := metas[i]!
  if !selects b spec.key then return .yield s
  let bp := blockPlan spec b
  if ox.on then
    let insEnd := L4Factoidal.Storage.Sbm11.Overlay.upperIdx ox.insK b.last ox.insFuel s.insPos ox.insK.size
    let dLo := L4Factoidal.Storage.Sbm11.Overlay.lowerIdx ox.ov.del b.first ox.delFuel 0 ox.ov.del.size
    let dHi := L4Factoidal.Storage.Sbm11.Overlay.upperIdx ox.ov.del b.last ox.delFuel dLo ox.ov.del.size
    let clHit := !ox.ov.cleared.isEmpty && (match colConst? b 3 with
      | some g => ox.ov.cleared.contains g
      | none => true)
    if insEnd > s.insPos || (!bp.skip && (dHi > dLo || clHit)) then
      let insL := L4Factoidal.Storage.Sbm11.Overlay.sliceList ox.insK s.insPos (insEnd - s.insPos) []
      let delL := L4Factoidal.Storage.Sbm11.Overlay.sliceList ox.ov.del dLo (dHi - dLo) []
      let (chunk0, nbytes) ← overlayChunkM st spec b insL delL ox.ov.cleared sortVar
      let chunk := sipFilterChunk cands chunk0
      let stats := { s.stats with blocksSelected := s.stats.blocksSelected + 1,
                                  blocksRead := s.stats.blocksRead + 1, framesRead := s.stats.framesRead + 4,
                                  bytesRead := s.stats.bytesRead + nbytes,
                                  rowsOut := s.stats.rowsOut + chunk.table.rows,
                                  keysTested := s.stats.keysTested + chunk0.table.rows,
                                  rowsGathered := s.stats.rowsGathered + chunk0.table.rows }
      let (acc', more) ← f s.acc chunk
      return stepOf s acc' stats insEnd more
  if bp.skip then return .yield s
  let jc := spec.key.size
  let (vlo, vhi) := sipRange b spec.key jc
  let p := Sip.lbHint cands vlo
  if !Sip.mayHold cands vlo vhi p then
    return .yield { s with stats := { s.stats with blocksSelected := s.stats.blocksSelected + 1,
                                                   sipSkipped := s.stats.sipSkipped + 1 } }
  let stats := { s.stats with blocksSelected := s.stats.blocksSelected + 1 }
  let constOut := constOutOf spec b bp
  let need := (needOf spec bp constOut).set! jc true
  let (bytes, starts, nbytes) ← readFrames st spec.perm b need
  let stats := { stats with blocksRead := stats.blocksRead + 1, framesRead := stats.framesRead + (need.filter id).size,
                            bytesRead := stats.bytesRead + nbytes }
  let (chunk, tested, found) ← ofExceptM (sipChunk spec cands sortVar b bp constOut need bytes starts p)
  let jcs := starts[jc]!
  let word := bytes.size < Sip.smallBytes && jcs < bytes.size && bytes.get! jcs == Column.tagDelta
  let stats := { stats with rowsOut := stats.rowsOut + chunk.table.rows, keysTested := stats.keysTested + tested,
                            rowsGathered := stats.rowsGathered + found,
                            sipWordBlocks := stats.sipWordBlocks + (if word then 1 else 0) }
  let (acc', more) ← f s.acc chunk
  return stepOf s acc' stats s.insPos more

/-- `scanFoldM` with candidates for column `spec.key.size`: the rows of the
    scan whose value there is a candidate (`cands` in non-decreasing order).
    With an overlay, the inserts after the last selected block form a last
    chunk, filtered. -/
def scanFoldSipM {m : Type → Type} [Monad m] {σ : Type} (st : Store m) (spec : ScanSpec)
    (cands : Array UInt64) (init : σ) (f : σ → Chunk → ExceptT String m (σ × Bool)) :
    ExceptT String m (σ × ScanStats) := do
  let sel ← st.blocksForRange spec.perm spec.key
  let total ← st.blockCount spec.perm
  let sortVar := match spec.outCols[0]? with
    | some c => if c == spec.key.size then spec.outVars[0]? else none
    | none => none
  let ox := ovCtx (st.ovl spec.perm) spec.key
  let s0 : ScanState σ := { acc := init, stats := { blocksTotal := total }, insPos := 0, stopped := false }
  let s ← forIn (List.range sel.size) s0 (scanBlockSipM st spec cands f sel sortVar ox)
  if ox.on && !s.stopped && s.insPos < ox.insK.size then
    let chunk := sipFilterChunk cands (chunkOfRows spec
      (L4Factoidal.Storage.Sbm11.Overlay.sliceList ox.insK s.insPos (ox.insK.size - s.insPos) []) sortVar)
    let (acc', _) ← f s.acc chunk
    return (acc', { s.stats with rowsOut := s.stats.rowsOut + chunk.table.rows })
  return (s.acc, s.stats)

/-- The scan with candidates as one table. -/
def scanSipTableM {m : Type → Type} [Monad m] (st : Store m) (spec : ScanSpec) (cands : Array UInt64) :
    ExceptT String m (Table × ScanStats) := do
  let init : Table := { vars := spec.outVars, cols := spec.outVars.map fun _ => ByteArray.empty,
                        rows := 0, sortVar := sortVarOf spec }
  scanFoldSipM st spec cands init fun acc ch => pure (acc.append ch.table, true)

/-- `scanSipTableM`, or the store's `scanSipTable` when it sets one. -/
def scanSipTableOf {m : Type → Type} [Monad m] (st : Store m) (spec : ScanSpec) (cands : Array UInt64) :
    ExceptT String m (Table × ScanStats) :=
  match st.scanSipTable with
  | some f => f spec cands
  | none => scanSipTableM st spec cands

/-- The loop of `scanFoldSipM` over the selected-block positions `sel`
    (positions in `metas`), from the state `init`, with no delta overlay
    (`ox.on = false`): the parallel scan with candidates
    (`Harness/Sbm11Query.lean`, issue 799, KR 1.2) runs one such loop per
    block range, as `scanListM` does for a scan without candidates, and
    appends the tables in range order. -/
def scanListSipM {m : Type → Type} [Monad m] {σ : Type} (st : Store m) (spec : ScanSpec)
    (cands : Array UInt64) (init : σ) (f : σ → Chunk → ExceptT String m (σ × Bool))
    (metas : Array BlockMeta) (sortVar : Option String) (ox : OvCtx) (sel : List Nat) :
    ExceptT String m (σ × ScanStats) := do
  let s ← forIn sel { acc := init, stats := {}, insPos := 0, stopped := false }
    (scanBlockSipM st spec cands f metas sortVar ox)
  return (s.acc, s.stats)

/-- The rule that selects sideways information passing for a scan, with
    the store's factor `k` (`Store.sipFactor`, 16 by default): the left input
    has fewer than `1/k` of the rows the PRM1 entries give for the scan
    (`k × left < estimate`). At sixteen, a block of 4,096 rows holds on
    average fewer than 256 candidate rows; the scan still decodes the join
    column of every block it reads, so the saving is in the other columns,
    the blocks no candidate can match, and the rows the join does not read. -/
def sipRule (factor : Option Nat) (leftRows estimate : Nat) : Bool :=
  match factor with
  | some k => k * leftRows < estimate
  | none => false

/-- The distinct values of `xs` (in order), appended to `out`: a value is
    pushed when it differs from the last one pushed (a tail call with
    fuel). -/
def dedupGo (xs : Array UInt64) : Nat → Nat → Array UInt64 → Array UInt64
  | 0, _, out => out
  | f + 1, i, out =>
    if i < xs.size then
      let x := xs[i]!
      match out.back? with
      | some y => dedupGo xs f (i + 1) (if y != x then out.push x else out)
      | none => dedupGo xs f (i + 1) (out.push x)
    else out

/-- Every row `i, i + 1, ...` of column `c` of `t` is a candidate (`sipMem`;
    a tail call with fuel). -/
def allMemGo (t : Table) (c : Nat) (cands : Array UInt64) : Nat → Nat → Bool
  | 0, _ => true
  | f + 1, i => if i < t.rows then (if sipMem cands (t.at c i) then allMemGo t c cands f (i + 1) else false) else true

/-- The two run-time checks of `sipCands`. -/
def sipCheck (t : Table) (c : Nat) (cands : Array UInt64) : Option (Array UInt64) :=
  if Sip.sorted cands && allMemGo t c cands t.rows 0 then some cands else none

/-- The distinct values of column `c` (sorted first unless `isSorted`). -/
def sipDistinct (t : Table) (c : Nat) (isSorted : Bool) : Array UInt64 := Id.run do
  let mut col : Array UInt64 := Array.mkEmpty t.rows
  for i in [0:t.rows] do
    col := col.push (t.at c i)
  let ordered := if isSorted then col else mergeSortBy col (· ≤ ·)
  return dedupGo ordered ordered.size 0 (Array.mkEmpty ordered.size)

/-- The candidates for the join variable `v` of a scan: the distinct values
    of the left table's column `v`, in non-decreasing order (the column as
    it is when the table is sorted on `v`, else sorted here). Used only when
    two checks pass at run time: the candidates are in non-decreasing order
    (`Sip.sorted`), and every value of the column is a candidate
    (`allMemGo`); else `none`, and the scan runs without candidates.
    `SipScanTheorems.sipCands_sound` derives from the two checks what the
    semi-join reduction needs. -/
def sipCands (t : Table) (v : String) : Option (Array UInt64) :=
  match t.idx v with
  | none => none
  | some c => sipCheck t c (sipDistinct t c (t.sortVar == some v))

/-- The right scan of a join with the table `left`: when the scan's sort
    variable `v` (the column after its key) is a variable of `left` and
    `sipRule` selects it, the scan with the left values of `v` as candidates
    (`scanSipTableM`); else the full scan. A right row whose `v` is not a
    left value joins no left row, in an inner join and in the left outer
    join of an OPTIONAL group (whose shared variables are bound in every left
    row, `flattenOptional`), so the join is the same
    (`SemiJoinTheorems`). Returns the explain text of the choice. -/
def scanForJoinM {m : Type → Type} [Monad m] (st : Store m) (spec : ScanSpec) (left : Table)
    (estimate : Nat) : ExceptT String m (Table × ScanStats × String) := do
  match sortVarOf spec with
  | some v =>
    if left.vars.contains v && sipRule st.sipFactor left.rows estimate then
      match sipCands left v with
      | some cands =>
        let (t, s0) ← scanSipTableOf st spec cands
        let s := s0.withSip
        return (t, s, s!"; sideways ?{v}: {cands.size} candidates, blocks skipped {s.sipSkipped}, key values tested {s.keysTested} (on words in {s.sipWordBlocks} blocks), rows gathered {s.rowsGathered}")
      | none => pure ()
  | none => pure ()
  let (t, s) ← scanTableOf st spec
  return (t, s.full, "")

/-! ## The BGP -/

def varCount (pats : Array Pat) (v : String) : Nat :=
  pats.foldl (fun a t => if t.vars.contains v then a + 1 else a) 0

/-- A triple position of `t` holding the variable that occurs in most
    patterns. -/
def bestSortPos (t : Pat) (pats : Array Pat) : Option Nat := Id.run do
  let mut best : Option (Nat × Nat) := none
  for i in [0:3] do
    match t.slot i with
    | .var v =>
      let c := varCount pats v
      match best with
      | some (_, c0) => if c > c0 then best := some (i, c)
      | none => best := some (i, c)
    | _ => pure ()
  return best.map (·.1)

def posOf (t : Pat) (v : String) : Option Nat :=
  [0, 1, 2].find? fun i => t.slot i == .var v

/-- Evaluate a BGP over ids (the join rules of `Qlvr.evalBgpM`, with the four
    SBM11 permutations). `need v`: the query reads `v` after the BGP. `pref`:
    a variable to sort the first scan on when that pattern has it (the join
    variable of a left outer join, so that the join can merge). -/
def evalBgpM {m : Type → Type} [Monad m] (st : Store m) (pats : Array Pat) (need : String → Bool)
    (pref : Option String := none) (left0 : Option Table := none) :
    ExceptT String m (Table × Array String × ScanStats) := do
  let allVars := pats.foldl (fun a t => t.vars.foldl (fun a v => if a.contains v then a else a.push v) a) #[]
  let keep (v : String) : Bool := need v || varCount pats v ≥ 2
  if pats.isEmpty then throw "empty basic graph pattern"
  if pats.any (·.hasMissing) then
    return (Table.empty (allVars.filter keep), #["a constant has no id: no solutions"], {})
  let mut ests : Array Nat := #[]
  for t in pats do
    let spec := mkSpec t (permFor t none) keep
    ests := ests.push (selRows (← st.blocksForRange spec.perm spec.key))
  let mut remaining := (List.range pats.size).toArray
  let mut lines : Array String := #[]
  let first := remaining.foldl (fun b k => if ests[k]! < ests[b]! then k else b) remaining[0]!
  remaining := remaining.filter (· != first)
  let t0 := pats[first]!
  let sortPos0 := match pref.bind (posOf t0) with
    | some q => some q
    | none => bestSortPos t0 pats
  let spec0 := mkSpec t0 (permFor t0 sortPos0) keep
  -- an OPTIONAL group's first scan takes the left table's join values as
  -- candidates (issue 809)
  let (tab0, st0, sip0) ← match left0 with
    | some l => scanForJoinM st spec0 l ests[first]!
    | none => do
      let (t, s) ← scanTableOf st spec0
      pure (t, s.full, "")
  let mut total := st0
  lines := lines.push s!"pattern {first}: {permNames[spec0.perm]!} key {spec0.key.size} estimate {ests[first]!}; blocks {st0.blocksRead} read of {st0.blocksSelected} selected of {st0.blocksTotal}, frames {st0.framesRead}, {st0.bytesRead} bytes; rows {tab0.rows}{sip0}"
  let mut tab := tab0
  for _ in [0:pats.size] do
    if remaining.isEmpty then break
    let connected := remaining.filter fun k => pats[k]!.vars.any tab.vars.contains
    let cands := if connected.isEmpty then remaining else connected
    let next := cands.foldl (fun b k => if ests[k]! < ests[b]! then k else b) cands[0]!
    remaining := remaining.filter (· != next)
    let t := pats[next]!
    let mergeVar : Option (String × Nat) := match tab.sortVar with
      | some v => (posOf t v).bind fun q => if t.bound q then none else some (v, q)
      | none => none
    let perm := match mergeVar with
      | some (_, q) => permFor t (some q)
      | none => permFor t (bestSortPos t pats)
    let spec := mkSpec t perm keep
    let (rt, s, sipNote) ← scanForJoinM st spec tab ests[next]!
    total := total.add s
    let (joined, how) := match mergeVar with
      | some (v, _) =>
        if rt.sortVar == some v then (mergeJoin tab rt v, s!"merge join on ?{v}")
        else (hashJoin tab rt, "hash join")
      | none => (hashJoin tab rt, if (sharedCols tab rt).isEmpty then "cross product" else "hash join")
    lines := lines.push s!"pattern {next}: {permNames[perm]!} key {spec.key.size} estimate {ests[next]!}; blocks {s.blocksRead} read of {s.blocksSelected} selected of {s.blocksTotal}, frames {s.framesRead}, {s.bytesRead} bytes; rows {rt.rows}{sipNote}; {how}: {joined.rows} rows"
    tab := joined
  return (tab, lines, total)

/-! ## FILTER -/

/-- The reference value of a FILTER conjunct on one row: `ebvOrFalse` of
    `Expr.evalIn` (the FILTER of `QueryPattern.lowerWith`; for an `EXISTS`-free
    expression `substituteExistentials` is the identity). -/
def refFilter (e : Expr) (mu : Binding) : Bool :=
  L4Factoidal.SPARQL.ebvOrFalse (L4Factoidal.SPARQL.Expr.evalIn {} mu e)

/-- A constant whose `=` with any term is true exactly when the term is the
    same term: an IRI, an `xsd:string` literal, a language-tagged literal
    without direction (`valueCompare`: two IRIs by their strings, two literals
    of one datatype by language tag and lexical form, anything else false or
    an error). -/
def eqByTermConst? : Expr → Option Term
  | .iri i => some (.iri i)
  | .lit l =>
    if l.val.direction.isNone && (l.val.langTag.isSome || l.val.datatype == xsdString) then
      some (.literal l)
    else none
  | _ => none

/-- A constant for `sameTerm`: any IRI or literal. -/
def sameTermConst? : Expr → Option Term
  | .iri i => some (.iri i)
  | .lit l => some (.literal l)
  | _ => none

/-- How one FILTER conjunct is evaluated. -/
inductive FKind where
  /-- keep the row when the id of `v` is `c` (`none`: the constant has no
      id, no row is kept) -/
  | idEq (v : String) (c : Option UInt64)
  /-- `sameTerm(?v, ?w)`: equal ids -/
  | idEqVar (v w : String)
  /-- 0 STRSTARTS, 1 STRENDS, 2 CONTAINS of `v` and a simple literal: key
      bytes for `xsd:string` and `rdf:langString` dictionary literals, the
      reference evaluator otherwise -/
  | str (k : Nat) (v : String) (needle : ByteArray) (e : Expr)
  /-- STRSTARTS of `v` and a simple literal without U+0000: a dictionary
      literal whose rank is in `[classLo, classHi)` (the keys of classes 3
      and 4, `xsd:string` and `rdf:langString`) passes exactly when the rank
      is in one of `ranges` (the keys `[c] ++ needle ...` for c = 3, 4); any
      other id goes to the reference evaluator -/
  | strRange (v : String) (ranges : Array (Nat × Nat)) (classLo classHi : Nat) (e : Expr)
  /-- the reference evaluator on the terms of `vars`, memoised by their ids -/
  | general (e : Expr) (vars : Array String)
  /-- issue 823: an EXISTS-free FILTER conjunct outside `backendLocal`, or
      one that reads a variable a row may leave unbound (`OptJoin.unbound`,
      or no column: no pattern binds it). The reference FILTER
      (`residualHolds`, with the query's environment `env`: NOW, BASE,
      extension functions) on the decoded terms of the bound variables of
      `vars`, memoised by the ids (0 for unbound) -/
  | residual (env : EvalEnv) (e : Expr) (vars : Array String)
  deriving Inhabited

/-- `?a, ?b` for `--explain`. -/
def varsText (vs : Array String) : String :=
  ", ".intercalate (vs.toList.map fun v => "?" ++ v)

/-- How a compiled conjunct is evaluated, for `--explain`
    (tests/sbm11/filter_keys.sh reads it; issue 948). -/
def FKind.explainName : FKind → String
  | .idEq v _ => s!"?{v} = constant on ids"
  | .idEqVar v w => s!"sameTerm(?{v}, ?{w}) on ids"
  | .str _ v _ _ => s!"string test of ?{v} on key bytes"
  | .strRange v _ _ _ _ => s!"STRSTARTS of ?{v} on key ranks"
  | .general _ vs => s!"reference evaluator on the decoded terms of {varsText vs}"
  | .residual _ _ vs => s!"residual: reference evaluator on the decoded terms of {varsText vs}"

/-- The `--explain` line of the compiled FILTER conjuncts. -/
def filterKindsLine (fs : Array FKind) : String :=
  s!"FILTER conjuncts on ids: {fs.size}" ++
    (if fs.isEmpty then "" else ": " ++ "; ".intercalate (fs.map FKind.explainName).toList)

/-- The reference FILTER on one solution mapping, as `QueryPattern.lowerWith`
    builds it: `ebvOrFalse (Expr.evalIn env mu (substituteExistentials env
    active mu e))`. The id path has no active graph; a residual conjunct is
    EXISTS-free (`residualVars`), and on an EXISTS-free expression
    `substituteExistentials` rebuilds the expression unchanged
    (`IdPostTheorems.substituteExistentials_existsFree`), so the empty graph
    stands for it. -/
def residualHolds (env : EvalEnv) (e : Expr) (mu : Binding) : Bool :=
  L4Factoidal.SPARQL.ebvOrFalse
    (L4Factoidal.SPARQL.Expr.evalIn env mu (L4Factoidal.SPARQL.substituteExistentials env Graph.empty mu e))

/-- The residual FILTER conjunct of `e` (its variables by `residualVars`;
    `translate` admits only conjuncts with some). -/
def residualKind (env : EvalEnv) (e : Expr) : FKind :=
  .residual env e ((residualVars e).getD #[])

/-- A simple literal needle (no language tag, `xsd:string`). -/
def simpleNeedle? : Expr → Option String
  | .lit l => if l.val.langTag.isNone && l.val.direction.isNone && l.val.datatype == xsdString then
      some l.val.lexicalForm else none
  | _ => none

/-- Classify a conjunct; constants are looked up. -/
def compileFilter {m : Type → Type} [Monad m] (st : Store m) (e : Expr) : ExceptT String m FKind := do
  let general : ExceptT String m FKind := do
    let some vs := exprVars e | throw "a FILTER expression outside the fragment"
    pure (.general e vs)
  match e with
  | .compare .eq (.var v) c | .compare .eq c (.var v) =>
    match eqByTermConst? c with
    | some t => pure (.idEq v (← st.idOf (L4Factoidal.Storage.Sbm11.normalizeTerm t)))
    | none => general
  | .sameTerm (.var v) (.var w) => pure (.idEqVar v w)
  | .sameTerm (.var v) c | .sameTerm c (.var v) =>
    match sameTermConst? c with
    | some t =>
      -- `sameTerm` does not fold language-tag case: a constant that the
      -- packer's normalisation would change is no stored term
      let n := L4Factoidal.Storage.Sbm11.normalizeTerm t
      if n == t then pure (.idEq v (← st.idOf t)) else pure (.idEq v none)
    | none => general
  | .strStarts (.var v) c | .strEnds (.var v) c | .contains (.var v) c =>
    match simpleNeedle? c with
    | some s =>
      let k := match e with | .strStarts _ _ => 0 | .strEnds _ _ => 1 | _ => 2
      let n := s.toUTF8
      if k == 0 && !n.data.contains 0 then
        -- keys with the prefix [c] ++ n: [lowerBound P, lowerBound (P ++ [0xFF]))
        let lb (bytes : ByteArray) : ExceptT String m Nat := st.lowerBound bytes
        let mut ranges : Array (Nat × Nat) := #[]
        for c in [3, 4] do
          let p := (ByteArray.mk #[c.toUInt8]) ++ n
          ranges := ranges.push (← lb p, ← lb (p.push 255))
        pure (.strRange v ranges (← lb (ByteArray.mk #[3])) (← lb (ByteArray.mk #[5])) e)
      else pure (.str k v n e)
    | none => general
  | _ => general

/-- Does `needle` occur in `hay` at `at_`? -/
def bytesAt (hay needle : ByteArray) (at_ : Nat) : Bool := Id.run do
  if at_ + needle.size > hay.size then return false
  for j in [0:needle.size] do
    if hay.get! (at_ + j) != needle.get! j then return false
  return true

/-- The string test on the lexical form `key[a, b)`. -/
def strTestRange (key : ByteArray) (a b : Nat) (k : Nat) (needle : ByteArray) : Bool :=
  if needle.size > b - a then false
  else match k with
    | 0 => bytesAt key needle a
    | 1 => bytesAt key needle (b - needle.size)
    | _ => Id.run do
      for i in [a:b - needle.size + 1] do
        if bytesAt key needle i then return true
      return false

/-- The string test on a dictionary key of class 3 (`xsd:string`: the body
    is the lexical form) or 4 (`rdf:langString`: lexical form, 0x00, tag; the
    tag has no 0x00, so the lexical form ends at the last 0x00). `none` for
    any other key. -/
def strTestKey (key : ByteArray) (k : Nat) (needle : ByteArray) : Option Bool :=
  if key.size == 0 then none
  else
    let cls := key.get! 0
    if cls == 3 then some (strTestRange key 1 key.size k needle)
    else if cls == 4 then
      let z := Id.run do
        let mut z := 0
        for i in [1:key.size] do
          if key.get! (key.size - i) == 0 then
            z := key.size - i
            break
        return z
      if z == 0 then none else some (strTestRange key 1 z k needle)
    else none

/-- The id's tag. -/
@[inline] def tagOf (x : UInt64) : Nat := (x >>> 60).toNat

/-- The id test of `FKind.strRange` on the id `x`: a dictionary literal
    (tag 3) whose rank is in `[classLo, classHi)` (classes 3 and 4) is decided
    by the rank ranges of the needle (`some`); any other id goes to the
    reference evaluator (`none`). -/
@[inline] def strRangeFast? (ranges : Array (Nat × Nat)) (classLo classHi : Nat) (x : UInt64) :
    Option Bool :=
  let rank := (x &&& 0x0FFFFFFFFFFFFFFF).toNat
  if tagOf x == 3 && classLo ≤ rank && rank < classHi then
    some (ranges.any fun (lo, hi) => lo ≤ rank && rank < hi)
  else none

/-- Memo of the reference evaluation per FILTER conjunct. -/
abbrev Memo := Std.HashMap (List UInt64) Bool

/-- Keep the rows of `t` that pass every conjunct. -/
def applyFilters {m : Type → Type} [Monad m] (st : Store m) (fs : Array FKind) (memos : Array Memo)
    (t : Table) : ExceptT String m (Table × Array Memo) := do
  if fs.isEmpty || t.rows == 0 then return (t, memos)
  let mut memos := memos
  let mut keep : Array Bool := Array.replicate t.rows true
  for fi in [0:fs.size] do
    match fs[fi]! with
    | .idEq v c =>
      match t.idx v, c with
      | some col, some x =>
        for i in [0:t.rows] do
          if keep[i]! && t.at col i != x then keep := keep.set! i false
      | _, _ => keep := Array.replicate t.rows false
    | .idEqVar v w =>
      match t.idx v, t.idx w with
      | some a, some b =>
        for i in [0:t.rows] do
          if keep[i]! && t.at a i != t.at b i then keep := keep.set! i false
      | _, _ => keep := Array.replicate t.rows false
    | .str k v needle e =>
      match t.idx v with
      | none => keep := Array.replicate t.rows false
      | some col =>
        let mut memo := memos[fi]!
        for i in [0:t.rows] do
          if !keep[i]! then continue
          let x := t.at col i
          let fast : Option Bool ← if tagOf x == 3 then pure (strTestKey (← st.keyOf x) k needle)
            else pure none
          let r ← match fast with
            | some r => pure r
            | none => match memo.get? [x] with
              | some r => pure r
              | none => do
                let r := refFilter e [(v, ← st.termOf x)]
                memo := memo.insert [x] r
                pure r
          if !r then keep := keep.set! i false
        -- the memo of a string test holds one entry per distinct id; keep it
        -- bounded
        memos := memos.set! fi (if memo.size > 65536 then {} else memo)
    | .strRange v ranges classLo classHi e =>
      match t.idx v with
      | none => keep := Array.replicate t.rows false
      | some col =>
        let mut memo := memos[fi]!
        for i in [0:t.rows] do
          if !keep[i]! then continue
          let x := t.at col i
          let r ← match strRangeFast? ranges classLo classHi x with
            | some r => pure r
            | none => match memo.get? [x] with
              | some r => pure r
              | none => do
                let r := refFilter e [(v, ← st.termOf x)]
                memo := memo.insert [x] r
                pure r
          if !r then keep := keep.set! i false
        memos := memos.set! fi (if memo.size > 65536 then {} else memo)
    | .general e vs =>
      let cols := vs.filterMap t.idx
      if cols.size != vs.size then
        keep := Array.replicate t.rows false
      else
        let mut memo := memos[fi]!
        for i in [0:t.rows] do
          if !keep[i]! then continue
          let ids := (cols.map fun c => t.at c i).toList
          let r ← match memo.get? ids with
            | some r => pure r
            | none => do
              let mut mu : Binding := []
              for k in [0:vs.size] do
                mu := mu ++ [(vs[k]!, ← st.termOf (t.at cols[k]! i))]
              let r := refFilter e mu
              memo := memo.insert ids r
              pure r
          if !r then keep := keep.set! i false
        memos := memos.set! fi (if memo.size > 65536 then {} else memo)
    | .residual env e vs =>
      -- a variable with no column, or with the id `OptJoin.unbound` in a
      -- row, is unbound in that row's solution mapping
      let cols : Array (Option Nat) := vs.map t.idx
      let mut memo := memos[fi]!
      for i in [0:t.rows] do
        if !keep[i]! then continue
        let ids := (cols.map fun c => match c with
          | some c => t.at c i
          | none => OptJoin.unbound).toList
        let r ← match memo.get? ids with
          | some r => pure r
          | none => do
            let mut mu : Binding := []
            for k in [0:vs.size] do
              match cols[k]! with
              | some c =>
                let x := t.at c i
                if x != OptJoin.unbound then mu := mu ++ [(vs[k]!, ← st.termOf x)]
              | none => pure ()
            let r := residualHolds env e mu
            memo := memo.insert ids r
            pure r
        if !r then keep := keep.set! i false
      memos := memos.set! fi (if memo.size > 65536 then {} else memo)
  return (t.select fun i => keep[i]!, memos)

/-! ## FILTER windows on the scan column (https://github.com/danbri/factoidal/issues/929)

A STRSTARTS conjunct on the variable of the column after the scan key
(`FKind.strRange`) decides every dictionary literal of classes 3 and 4 by
its rank (`strRangeFast?`): the ranks that pass are the ranges of the keys
with the needle as prefix, so in a permutation sorted on that column the
rows that pass lie in a few id intervals. A selected block whose rows with
the key prefix all hold ids that the test decides `false` (their column is
bounded by `sipRange`, and `spanRejects` holds of the bounds) gives no row
after the FILTER; the scan does not read it. For DBpedia d13 (`?s foaf:name
?n FILTER(STRSTARTS(?n, "Tim Bern"))`) this reads a few blocks of the
POS range of foaf:name in place of all of them.

`WindowTheorems.scanFoldM_window`: over an admitted permutation with no
overlay, the scan of the window store gives the rows of the full scan that
`windowRejects` does not reject, together with some rows it rejects, in row
order; the FILTER removes those (`applyFilters` keeps a row only when
`strRangeFast?` does not answer `some false`). -/

/-- Every id `x` with `vlo ≤ x ≤ vhi` has tag 3 and a rank in
    `[classLo, classHi)` outside every range, so `strRangeFast?` answers
    `some false` for it (`WindowTheorems.strRangeFast?_of_span`). -/
def spanRejects (ranges : Array (Nat × Nat)) (classLo classHi : Nat) (vlo vhi : UInt64) : Bool :=
  let rlo := (vlo &&& 0x0FFFFFFFFFFFFFFF).toNat
  let rhi := (vhi &&& 0x0FFFFFFFFFFFFFFF).toNat
  tagOf vlo == 3 && tagOf vhi == 3 && classLo ≤ rlo && rhi < classHi &&
    ranges.all fun (lo, hi) => rhi < lo || hi ≤ rlo

/-- Some `strRange` conjunct of `fs` on the variable `v` decides the id `x`
    `false`. -/
def windowRejects (fs : Array FKind) (v : String) (x : UInt64) : Bool :=
  fs.any fun f => match f with
    | .strRange w ranges lo hi _ => w == v && strRangeFast? ranges lo hi x == some false
    | _ => false

/-- Block `b` holds no row with the key prefix that passes the `strRange`
    conjuncts on the scan's sort variable (the variable of column
    `key.size`): some conjunct rejects every id in the block's range of that
    column (`sipRange`). -/
def windowSkip (fs : Array FKind) (spec : ScanSpec) (b : BlockMeta) : Bool :=
  match sortVarOf spec with
  | none => false
  | some v =>
    let r := sipRange b spec.key spec.key.size
    fs.any fun f => match f with
      | .strRange w ranges lo hi _ => w == v && spanRejects ranges lo hi r.1 r.2
      | _ => false

/-- The store `st` whose answer for the scan `spec` is `kept` (the selected
    PRM1 entries without the blocks `windowSkip` rules out); every other
    request goes to `st`. -/
def windowStore {m : Type → Type} [Monad m] (st : Store m) (spec : ScanSpec) (fs : Array FKind)
    (sel : Array BlockMeta) : Store m :=
  let kept := sel.filter fun b => !windowSkip fs spec b
  { st with blocksForRange := fun perm key =>
      if perm == spec.perm && key == spec.key then pure kept else st.blocksForRange perm key }

/-- The window store for the scan `spec`, and (blocks skipped, blocks
    selected), when the scan has no delta overlay, a sort variable and a
    `strRange` conjunct; else `st` itself. -/
def windowStoreM {m : Type → Type} [Monad m] (st : Store m) (spec : ScanSpec) (fs : Array FKind) :
    ExceptT String m (Store m × Option (Nat × Nat)) := do
  let some v := sortVarOf spec | return (st, none)
  let hasRange := fs.any fun f => match f with
    | .strRange w _ _ _ _ => w == v
    | _ => false
  if !hasRange || !(st.ovl spec.perm).isEmpty then return (st, none)
  let sel ← st.blocksForRange spec.perm spec.key
  let kept := (sel.filter fun b => !windowSkip fs spec b).size
  return (windowStore st spec fs sel, some (sel.size - kept, sel.size))

/-- The position (0 subject, 1 predicate, 2 object) of the first variable
    of `t` that a `strRange` conjunct of `fs` tests, for `permFor`. -/
def windowPref (t : Pat) (fs : Array FKind) : Option Nat :=
  [0, 1, 2].find? fun q => match t.slot q with
    | .var v => fs.any fun f => match f with
      | .strRange w _ _ _ _ => w == v
      | _ => false
    | _ => false

/-- The `--explain` text of a window. -/
def windowNote : Option (Nat × Nat) → String
  | some (k, n) => s!"; FILTER window on the scan column: {k} of {n} selected blocks not read"
  | none => ""

/-! ## GROUP BY with COUNT -/

/-- Group key → count, and the keys in first-seen order. -/
structure Groups where
  counts : Std.HashMap (List UInt64) Nat := {}
  keys : Array (List UInt64) := #[]
  deriving Inhabited

def Groups.add (g : Groups) (k : List UInt64) (n : Nat) : Groups :=
  match g.counts.get? k with
  | some c => { g with counts := g.counts.insert k (c + n) }
  | none => { counts := g.counts.insert k n, keys := g.keys.push k }

/-- Rows `e` and `i` agree on every column of `vcols` (a loop, no closure per
    row; `Array.all` with a lambda took a quarter of d10's time). -/
@[inline] def sameKeyRows (t : Table) (vcols : Array Nat) (e i : Nat) : Bool := Id.run do
  for c in vcols do
    if t.at c e != t.at c i then return false
  return true

/-- The first row after `i` (at most `t.rows`) whose key differs from row
    `i` on the columns `vcols`. One column (the common case, a GROUP BY on
    one variable): the column and the word of row `i` are read once, and each
    row costs one word read (`Codec.Zstd.word64U`, equal to `word64`:
    `word64U_eq`). -/
def runEnd (t : Table) (vcols : Array Nat) (i : Nat) : Nat := Id.run do
  let mut e := i + 1
  if vcols.size == 1 then
    let col := t.cols[vcols[0]!]!
    let x := word64U col (8 * i).toUInt64
    for _ in [0:t.rows] do
      if e < t.rows && word64U col (8 * e).toUInt64 == x then e := e + 1 else break
  else
    for _ in [0:t.rows] do
      if e < t.rows && sameKeyRows t vcols e i then e := e + 1 else break
  return e

/-- Count the rows of a chunk per group key. A group column that is constant
    over the chunk counts the chunk at once. The key list is built once per run
    of equal keys (`runEnd`); `countChunkRef` builds one per row. -/
def countChunk (groupVars : Array String) (ch : Chunk) (g : Groups) : Groups := Id.run do
  let t := ch.table
  if t.rows == 0 then return g
  let gc := groupVars.map fun v => (t.idx v).getD 0
  let consts := gc.map fun c => ch.consts.getD c none
  if consts.all Option.isSome then
    return g.add (consts.map (·.getD 0)).toList t.rows
  let mut g := g
  let keyAt (i : Nat) : List UInt64 :=
    (List.range gc.size).map fun k => match consts[k]! with
      | some x => x
      | none => t.at gc[k]! i
  let vcols : Array Nat := (List.range gc.size).foldl
    (fun a k => if (consts[k]!).isSome then a else a.push gc[k]!) #[]
  let mut i := 0
  for _ in [0:t.rows] do
    if i ≥ t.rows then break
    let e := runEnd t vcols i
    g := g.add (keyAt i) (e - i)
    i := e
  return g

/-- The reference of `countChunk`: the first version, one key list per row.
    `Harness/ScanFoldTest.lean` compares the two. -/
def countChunkRef (groupVars : Array String) (ch : Chunk) (g : Groups) : Groups := Id.run do
  let t := ch.table
  if t.rows == 0 then return g
  let gc := groupVars.map fun v => (t.idx v).getD 0
  let consts := gc.map fun c => ch.consts.getD c none
  if consts.all Option.isSome then
    return g.add (consts.map (·.getD 0)).toList t.rows
  let mut g := g
  let keyAt (i : Nat) : List UInt64 :=
    (List.range gc.size).map fun k => match consts[k]! with
      | some x => x
      | none => t.at gc[k]! i
  let mut i := 0
  for _ in [0:t.rows] do
    if i ≥ t.rows then break
    let k := keyAt i
    let mut e := i + 1
    for _ in [0:t.rows] do
      if e < t.rows && keyAt e == k then e := e + 1 else break
    g := g.add k (e - i)
    i := e
  return g

/-- The groups of `b` added to `a`, in `b`'s key order (issue 799, stage 1b:
    the parent adds the groups of each block range in range order). Over the
    list model, `ParallelMergeTheorems.merge_foldl` and `groups_chunks`: the
    result has the keys and counts of one pass over the concatenation. -/
def Groups.merge (a b : Groups) : Groups :=
  b.keys.foldl (fun g k => g.add k (b.counts.getD k 0)) a

/-- The counted path's step for one scan chunk: the FILTERs, then `countChunk`
    (the chunk's constant columns count at once when there is no FILTER). -/
def countStepM {m : Type → Type} [Monad m] (st : Store m) (fs : Array FKind) (groupVars : Array String)
    (acc : Groups × Array Memo) (ch : Chunk) : ExceptT String m ((Groups × Array Memo) × Bool) := do
  let (g, memos) := acc
  if fs.isEmpty then
    pure ((countChunk groupVars ch g, memos), true)
  else
    let (tab, memos) ← applyFilters st fs memos ch.table
    pure ((countChunk groupVars { table := tab, consts := tab.vars.map fun _ => none } g, memos), true)

/-- The inline id of an `xsd:integer` count (`TermId`: tag 4, datatype 0,
    value + 2^55). -/
def countId (n : Nat) : UInt64 :=
  (L4Factoidal.Storage.Sbm11.tagInt * L4Factoidal.Storage.Sbm11.two60 + 0 + (n + 2 ^ 55)).toUInt64

/-- The aggregated table: the group variables, then one column per COUNT.
    With no GROUP BY there is one group, also over no rows. `items` (one per
    COUNT, in order; empty or `none`: the rows of the group) holds the counts
    of a `COUNT(?x)` over a variable that may be unbound: the rows of the
    group where `?x` is bound (SPARQL 1.1 section 18.5, Count). -/
def groupTable (plan : Plan) (g : Groups) (items : Array (Option Groups) := #[]) :
    Except String Table := Id.run do
  let ks := if g.keys.isEmpty && plan.groupVars.isEmpty then #[[]] else g.keys
  let cnt := plan.proj.filterMap fun | .count a _ => some a | _ => none
  let mut cols := (plan.groupVars ++ cnt).map fun _ => ByteArray.empty
  for k in ks do
    let n := g.counts.getD k 0
    if n ≥ 2 ^ 55 then return .error "a count of 2^55 or more"
    let mut j := 0
    for x in k do
      cols := cols.modify j (L4Factoidal.Qlvr.Side.put64 · x)
      j := j + 1
    for c in [0:cnt.size] do
      let nc := match items[c]? with
        | some (some gi) => gi.counts.getD k 0
        | _ => n
      cols := cols.modify j (L4Factoidal.Qlvr.Side.put64 · (countId nc))
      j := j + 1
  return .ok { vars := plan.groupVars ++ cnt, cols, rows := ks.size }

/-! ## ORDER BY, DISTINCT, OFFSET, LIMIT -/

/-- The value the reference ORDER BY compares for a variable bound to `t`. -/
def orderValue (t : Term) : EvalResult :=
  L4Factoidal.SPARQL.Expr.evalIn {} [("v", t)] (.var "v")

/-- Sort keys read from the ids alone, when every id of column `c` is a
    blank node or an IRI (tags 1 and 2), or every one is an inline integer
    (tag 4); `none` otherwise.

    * Tags 1 and 2: `sparqlOrderValue` puts blank nodes before IRIs and
      compares two blank nodes by label, two IRIs by `strCompare` (code point
      order, which is the byte order of UTF-8). A dictionary key is the class
      byte and the UTF-8 bytes; ranks are in key byte order
      (`DictTheorems.decodeDict_sorted`); the tag is above the rank. So the id
      order is the section 15.1 order.
    * Tag 4: `numericView` makes every integer literal a number, compared by
      value; bits 55..0 of the id are the value plus 2^55 for every integer
      datatype, so they are a key (equal values, equal keys). -/
def orderKeysByIds? (t : Table) (c : Nat) : Option (Array UInt64) := Id.run do
  if t.rows == 0 then return some #[]
  let mut allRef := true
  let mut allInt := true
  for i in [0:t.rows] do
    let g := tagOf (t.at c i)
    if g != 1 && g != 2 then allRef := false
    if g != 4 then allInt := false
    if !allRef && !allInt then return none
  let mut out : Array UInt64 := Array.mkEmpty t.rows
  for i in [0:t.rows] do
    let x := t.at c i
    out := out.push (if allRef then x else x &&& 0x00FFFFFFFFFFFFFF)
  return some out

/-- Per row of column `c`, the number of its value in the section 15.1 order
    of the column's distinct values (`sparqlOrderValue`), complemented for
    DESC. -/
def orderKeysM {m : Type → Type} [Monad m] (st : Store m) (t : Table) (c : Nat) (desc : Bool) :
    ExceptT String m (Array UInt64) := do
  match orderKeysByIds? t c with
  | some ks => return (if desc then ks.map (~~~ ·) else ks)
  | none => pure ()
  let mut idx : Std.HashMap UInt64 Nat := {}
  let mut ids : Array UInt64 := #[]
  for i in [0:t.rows] do
    let x := t.at c i
    if !idx.contains x then
      idx := idx.insert x ids.size
      ids := ids.push x
  let mut vals : Array EvalResult := #[]
  for x in ids do
    -- an unbound variable (`OptJoin.unbound`, after an OPTIONAL) evaluates
    -- to an error, which section 15.1 orders first, as the reference does
    if x == OptJoin.unbound then vals := vals.push .error
    else vals := vals.push (orderValue (← st.termOf x))
  let sorted := mergeSortBy (List.range ids.size).toArray fun a b =>
    L4Factoidal.SPARQL.sparqlOrderValue (vals.getD a .error) (vals.getD b .error) ≤ 0
  let mut rank : Array Nat := Array.replicate ids.size 0
  let mut r := 0
  for j in [0:sorted.size] do
    if j > 0 && L4Factoidal.SPARQL.sparqlOrderValue (vals.getD sorted[j - 1]! .error)
        (vals.getD sorted[j]! .error) != 0 then
      r := r + 1
    rank := rank.set! sorted[j]! r
  let mut out : Array UInt64 := Array.mkEmpty t.rows
  for i in [0:t.rows] do
    let k := (rank[idx.getD (t.at c i) 0]!).toUInt64
    out := out.push (if desc then ~~~k else k)
  return out

/-- The rows of `t` in the ORDER BY order of `plan` (stable: rows whose keys
    are equal keep their order), as row indices; with `firstK = some k` only
    the first `k` of them (`topK`). `finishM` uses it; so does each block range
    of the divided ORDER BY ... LIMIT path (`topPartM`). -/
def orderPermM {m : Type → Type} [Monad m] (st : Store m) (plan : Plan) (t : Table)
    (firstK : Option Nat) : ExceptT String m (Array Nat) := do
  let mut keys : Array (Array UInt64) := #[]
  for (v, desc) in plan.order do
    match t.idx v with
    | some c => keys := keys.push (← orderKeysM st t c desc)
    | none => pure ()
  match firstK with
  | some k =>
    if 4 * k < t.rows then pure (L4Factoidal.Qlvr.Query.topK t.rows k keys)
    else
      let mut p := (List.range t.rows).toArray
      for j in [0:keys.size] do
        p := L4Factoidal.Qlvr.Query.sortPermByKey p keys[keys.size - 1 - j]!
      pure (p.extract 0 k)
  | none =>
    let mut p := (List.range t.rows).toArray
    for j in [0:keys.size] do
      p := L4Factoidal.Qlvr.Query.sortPermByKey p keys[keys.size - 1 - j]!
    pure p

/-- ORDER BY, DISTINCT (on the projected columns: ids are injective, so equal
    ids are equal terms and different ids different terms), OFFSET, LIMIT.
    Without DISTINCT, ORDER BY with LIMIT keeps only the first OFFSET + LIMIT
    rows of the order (`topK`). -/
def finishM {m : Type → Type} [Monad m] (st : Store m) (plan : Plan) (t : Table) :
    ExceptT String m Table := do
  let mut t := t
  if !plan.order.isEmpty then
    let firstK := if plan.distinct then none else plan.limit.map (plan.offset + ·)
    let perm ← orderPermM st plan t firstK
    t := t.reorder perm
  if plan.distinct then
    let cols := plan.outVars.filterMap t.idx
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

/-! ## SPARQL JSON

`jsonOfTerm` (`SPARQL/ResultsJson.lean`) is the reference: a term is built
and printed. `keyJson` prints the same text from a dictionary key's bytes for
the classes it knows (blank node, IRI, `xsd:string`, `rdf:langString`,
other datatype); `tests/sbm11/run.sh` compares the two outputs byte for byte
on every oracle query (`--reference-render`). -/

open L4Factoidal.Qlvr.Query (jsonStr kUri kLit kBnode kLang kDt)

/-- The shape of the dictionary key `buf[a, e)` for the key printer: its
    class and the position of its 0x00 separator (classes 4 and 5), or `none`
    for a class the printer does not know. Class 4 (`rdf:langString`) is
    lexical form, 0x00, tag; the tag has no 0x00, so the separator is the last
    0x00. Class 5 (other datatype) is datatype IRI, 0x00, lexical form; the
    IRI has no 0x00, so the separator is the first. -/
def keyShape (buf : ByteArray) (a e : Nat) : Option (Nat × Nat) := Id.run do
  if e ≤ a || e > buf.size then return none
  let cls := (buf.get! a).toNat
  if cls == 1 || cls == 2 || cls == 3 then return some (cls, 0)
  if cls == 4 then
    for i in [1:e - a] do
      if buf.get! (e - i) == 0 then return some (4, e - i)
    return none
  if cls == 5 then
    for i in [a + 1:e] do
      if buf.get! i == 0 then return some (5, i)
    return none
  return none

/-- Append the SPARQL JSON object of the key `buf[a, e)` of shape
    `(cls, z)` to `out`: the text `jsonOfTerm` prints for the key's term. -/
def keyJsonInto (buf : ByteArray) (a e cls z : Nat) (out : ByteArray) : ByteArray :=
  if cls == 1 then (jsonStr buf (a + 1) e (out ++ kBnode)).push 125
  else if cls == 2 then (jsonStr buf (a + 1) e (out ++ kUri)).push 125
  else if cls == 3 then (jsonStr buf (a + 1) e (out ++ kLit)).push 125
  else if cls == 4 then (jsonStr buf (z + 1) e (jsonStr buf (a + 1) z (out ++ kLit) ++ kLang)).push 125
  else
    let dtIsString := buf.extract (a + 1) z == (L4Factoidal.Qlvr.Query.xsd "string").toUTF8
    let o := jsonStr buf (z + 1) e (out ++ kLit)
    if dtIsString then o.push 125 else (jsonStr buf (a + 1) z (o ++ kDt)).push 125

/-- The SPARQL JSON object of a dictionary key, or `none` for a class this
    printer does not know. -/
def keyJson (key : ByteArray) (out : ByteArray) : Option ByteArray :=
  match keyShape key 0 key.size with
  | some (cls, z) => some (keyJsonInto key 0 key.size cls z out)
  | none => none

def jsonHead (vars : Array String) : String :=
  "{\"head\":{\"vars\":[" ++ L4Factoidal.SPARQL.varListJson vars.toList ++ "]},\"results\":{\"bindings\":["

def jsonTail : String := "]}}"

/-- `"<escaped name>":` per result variable. -/
def nameBytes (vars : Array String) : Array ByteArray :=
  vars.map fun n => ("\"" ++ L4Factoidal.JSON.escapeString n ++ "\":").toUTF8

/-- Append the JSON of one id to `out`: the key printer for dictionary ids
    (unless `reference`), else `jsonOfTerm` of the decoded term. The shape is
    decided before `out` is used, so `out` has one reference in each branch
    and is appended to in place. (A first version passed `out` to a printer
    that returned `none` for some keys and then appended to `out` again; the
    second use kept a second reference, and every append in the printer
    copied the whole output: q19 took 3.7 s, quadratic in the rows of a
    block.) -/
def appendIdJsonM {m : Type → Type} [Monad m] (st : Store m) (reference : Bool) (x : UInt64)
    (out : ByteArray) : ExceptT String m ByteArray := do
  let tag := tagOf x
  if !reference && (tag == 1 || tag == 2 || tag == 3) then
    let (buf, a, e) ← st.keySlice x
    match keyShape buf a e with
    | some (cls, z) => return keyJsonInto buf a e cls z out
    | none => pure ()
  let t ← st.termOf x
  return out ++ (L4Factoidal.SPARQL.jsonOfTerm t).toString.toUTF8

/-- Rows `[lo, hi)` of `t` as comma-separated binding objects (`first`: no
    comma before the first). Variables without a column, and a column's
    `OptJoin.unbound` ids (after an OPTIONAL), are unbound and left out
    (`rowJson`). A comma goes before a binding unless the object is still
    empty (its last byte is `{`), so no flag is carried through the loop. -/
def renderRowsM {m : Type → Type} [Monad m] (st : Store m) (reference : Bool) (t : Table)
    (vars : Array String) (lo hi : Nat) (first : Bool) : ExceptT String m ByteArray := do
  let names := nameBytes vars
  let cols : Array (Nat × Nat) := (List.range vars.size).toArray.filterMap fun k =>
    (t.idx vars[k]!).map fun c => (k, c)
  let mut out := ByteArray.emptyWithCapacity (64 * (hi - lo))
  for i in [lo:hi] do
    if !(first && i == lo) then out := out.push 44
    out := out.push 123
    for j in [0:cols.size] do
      let (k, c) := cols[j]!
      let x := t.at c i
      if x != OptJoin.unbound then
        if out.get! (out.size - 1) != 123 then out := out.push 44
        out := out ++ names[k]!
        out ← appendIdJsonM st reference x out
    out := out.push 125
  return out

/-! ## Running a plan -/

structure RunStats where
  plan : Array String := #[]
  rows : Nat := 0
  scan : ScanStats := {}
  deriving Inhabited

def toSlot {m : Type → Type} [Monad m] (st : Store m) : Arg → ExceptT String m Slot
  | .var v => pure (.var v)
  | .term t => do
    match ← st.idOf t with
    | some x => pure (.const x)
    | none => pure .missing

def resolvePat {m : Type → Type} [Monad m] (st : Store m) (p : PatSpec) : ExceptT String m Pat := do
  let (g, named) ← match p.g with
    | .dflt => pure (Slot.const 0, false)
    | .term t => do pure (← toSlot st (.term t), false)
    | .var v => pure (Slot.var v, true)
  return { s := ← toSlot st p.s, p := ← toSlot st p.p, o := ← toSlot st p.o, g, named }

/-- The variables compiled FILTER conjuncts read. -/
def fkVars (fs : Array FKind) : Array String :=
  fs.foldl (fun a f => match f with
    | .idEq v _ => a.push v
    | .idEqVar v w => (a.push v).push w
    | .str _ v _ _ => a.push v
    | .strRange v _ _ _ _ => a.push v
    | .general _ vs => a ++ vs
    | .residual _ _ vs => a ++ vs) #[]

/-- The base of a plan with OPTIONAL groups (issue 775): its BGP and FILTERs,
    then, group by group, the left outer join with the group's BGP after the
    group's FILTERs (`OptJoin.leftOuterJoin`). A group's FILTER reads only the
    group's own variables (`flattenOptional`), so it gives the same answer on
    the group's row as on the merged row, and `LeftJoin(Ω1, Ω2, e)` is
    `LeftJoin(Ω1, Filter(e, Ω2), true)` (`OptJoinTheorems.leftJoin_filter_right`).
    A single base pattern is scanned sorted on a variable it shares with the
    first group, and each group's first scan on the left table's sort
    variable, so that the joins can merge. -/
def evalOptionalsM {m : Type → Type} [Monad m] (st : Store m) (plan : Plan) (pats : Array Pat)
    (fs : Array FKind) (need : String → Bool) (env : EvalEnv := {}) :
    ExceptT String m (Table × Array String × ScanStats) := do
  let groupVars := plan.optionals.foldl (fun a g => a ++ g.vars) #[]
  let needBase (v : String) : Bool := need v || groupVars.contains v
  let pref : Option String :=
    if pats.size == 1 then plan.optionals[0]?.bind fun g => g.vars.find? pats[0]!.vars.contains
    else none
  let (t0, lines0, s0) ← evalBgpM st pats needBase pref
  let (t1, _) ← applyFilters st fs (fs.map fun _ => {}) t0
  let mut tab := t1
  let mut lines := lines0
  let mut total := s0
  for k in [0:plan.optionals.size] do
    let g := plan.optionals[k]!
    let gp ← g.pats.mapM (resolvePat st)
    let gfs := (← g.filters.mapM (compileFilter st)) ++ g.residuals.map (residualKind env)
    let gfv := fkVars gfs
    let left := tab
    let gneed (v : String) : Bool := need v || left.vars.contains v || gfv.contains v
    let joinVar : Option String := match left.sortVar with
      | some v => if g.vars.contains v then some v else none
      | none => none
    let (rt0, glines, gs) ← evalBgpM st gp gneed joinVar (some left)
    let (rt, _) ← applyFilters st gfs (gfs.map fun _ => {}) rt0
    let (j, how) := OptJoin.leftOuterJoin left rt
    lines := lines ++ glines.map (s!"optional {k} " ++ ·)
    lines := lines.push s!"optional {k}: {gfs.size} condition conjuncts, {rt.rows} right rows; left outer join ({how}): {j.rows} rows"
    total := total.add gs
    tab := j
  -- the FILTERs beside the OPTIONALs that read a group's variable:
  -- `Filter(f, LeftJoin(...))`, on the rows of the last left join
  if !plan.postFilters.isEmpty then
    let pfs := plan.postFilters.map (residualKind env)
    let before := tab.rows
    let (t, _) ← applyFilters st pfs (pfs.map fun _ => {}) tab
    lines := lines.push s!"{pfs.size} FILTER conjuncts beside the OPTIONALs, after the left joins: {before} rows to {t.rows}"
    tab := t
  return (tab, lines, total)

/-- Per COUNT item, in order: for `COUNT(?x)` whose column holds an unbound
    id (after an OPTIONAL), the groups of the rows where `?x` is bound
    (SPARQL 1.1 section 18.5: Count counts the solutions whose expression
    has a value); `none` for every other item (the rows of the group). -/
def countItems (plan : Plan) (t : Table) : Array (Option Groups) :=
  plan.proj.filterMap fun
    | .var _ => none
    | .count _ none => some none
    | .count _ (some x) =>
      match t.idx x with
      | none => some (some {})
      | some c =>
        let anyUnbound : Bool := Id.run do
          for i in [0:t.rows] do
            if t.at c i == OptJoin.unbound then return true
          return false
        if anyUnbound then
          let tb := t.select fun i => t.at c i != OptJoin.unbound
          some (some (countChunk plan.groupVars { table := tb, consts := tb.vars.map fun _ => none } {}))
        else some none

/-! ## Divided single-pattern paths (issue 799, stage 1b)

Record: docs/designissues/2026-10-12-parallel-block-scans.md, section
"Stage 1b". The streamed path, the counted path and ORDER BY with LIMIT
over one pattern divide the selected blocks of their scan into consecutive
block ranges (`ParallelScan.chunksOf`) and run one job per range, each on
its own view of the store (`Par.fold`; the native driver runs one Lean task
per range, at most `threads` at once). The parent folds the range results in
range order:

  * streamed: each range applies the FILTERs and renders at most
    OFFSET + LIMIT of its rows (`streamPartM`); the parent takes the window
    [OFFSET, OFFSET + LIMIT) across the ranges in order (`emitPieceM`;
    `ParallelMergeTheorems.window_chunks`). The path is divided only when
    OFFSET + LIMIT is above the scan's estimate (the rows of its selected
    blocks): then the single scan never stops early, so the divided scan reads
    the same blocks.
  * counted: each range counts its rows per group (`countPartM`); the parent
    adds the range groups in range order (`Groups.merge`;
    `ParallelMergeTheorems.groups_chunks`).
  * ORDER BY ... LIMIT k without DISTINCT: each range keeps the first
    OFFSET + LIMIT rows of its rows in the order (`topPartM`); the parent
    orders the union of those rows and keeps the window (`finishM`;
    `ParallelMergeTheorems.topK_chunks`).

With `par = none` (`--threads 1`) none of this runs: `runPlanM` takes the
single-thread code. A scan with a delta overlay stays on one thread, as in
stage 1. -/

/-- The runner of the divided paths. `fold job chunks init g` runs `job` on
    every chunk of block numbers, each with its own view of the store, and
    folds `g` over the results in chunk order. Its meaning is
    `chunks.foldlM (fun b X => do g b (← job st X)) init`; the native driver
    (`Harness/Sbm11Query.lean`, `parFold`) runs the jobs as tasks. -/
structure Par (m : Type → Type) where
  threads : Nat
  /-- the fewest estimated rows per range (`rangeCount`); 0: no minimum -/
  minRows : Nat := 8192
  fold : {α β : Type} → (Store m → List Nat → ExceptT String m α) → List (List Nat) → β →
    (β → α → ExceptT String m β) → ExceptT String m β

/-- How many block ranges a scan of `est` estimated rows is divided into with
    `threads` threads: at most `threads`, and with `minRows > 0` at most
    `est / minRows`. Fewer than 2: the scan runs on one thread. A range costs
    its task a fixed amount (the task, its view of the store, fresh memory in
    the worker's heap): olympics q07, whose first two scans have 8,192 and
    16,384 rows, took 12.2 ms at 4 threads against 9.9 ms at 1 with one range
    per block. The default of 8,192 rows (two blocks of 4,096) is a measured
    choice for this machine, not a derived one (`SBM11_MIN_RANGE_ROWS`). -/
def rangeCount (threads minRows est : Nat) : Nat :=
  if minRows == 0 then threads else min threads (est / minRows)

/-- The block ranges of the scan `spec` when it is divided: two or more
    ranges (`rangeCount`), no delta overlay on the scan, two or more
    selected blocks; each range of at most `maxBlocks` blocks when
    `maxBlocks > 0` (then there can be more ranges than threads). Also the
    PRM1 entries of the selected blocks (`Store.blocksForRange`; a range is a
    list of positions in that array), the overlay context and the estimate
    (`selRows`). -/
def divide? {m : Type → Type} [Monad m] (st : Store m) (threads minRows : Nat) (spec : ScanSpec)
    (maxBlocks : Nat) :
    ExceptT String m (Option (Array BlockMeta × OvCtx × List (List Nat) × Nat)) := do
  if threads ≤ 1 then return none
  let ox := ovCtx (st.ovl spec.perm) spec.key
  if ox.on then return none
  -- the selected blocks' PRM1 entries (issue 805); the ranges are lists of
  -- positions in that array
  let metas ← st.blocksForRange spec.perm spec.key
  let sel := List.range metas.size
  let est := selRows metas
  let n := rangeCount threads minRows est
  if sel.length < 2 || n < 2 then return none
  let c0 := (sel.length + n - 1) / n
  let c := if maxBlocks == 0 then c0 else min c0 maxBlocks
  return some (metas, ox, L4Factoidal.Storage.Sbm11.ParallelScan.chunksOf c sel, est)

/-- `divide?` with the threads of `par`; none without `par`. -/
def divideFor? {m : Type → Type} [Monad m] (st : Store m) (par : Option (Par m)) (spec : ScanSpec)
    (maxBlocks : Nat) : ExceptT String m (Option (Array BlockMeta × OvCtx × List (List Nat) × Nat)) :=
  match par with
  | some p => divide? st p.threads p.minRows spec maxBlocks
  | none => pure none

/-- Rows `[lo, hi)` of `t`, each as a comma and its binding object (the text
    `renderRowsM` writes for a row after the first), into a new buffer; and
    the end offset of each row in it. -/
def renderRowsEndsM {m : Type → Type} [Monad m] (st : Store m) (reference : Bool) (t : Table)
    (vars : Array String) (lo hi : Nat) (rowBytes : Nat := 64) : ExceptT String m (ByteArray × Array Nat) := do
  let names := nameBytes vars
  let cols : Array (Nat × Nat) := (List.range vars.size).toArray.filterMap fun k =>
    (t.idx vars[k]!).map fun c => (k, c)
  let mut out := ByteArray.emptyWithCapacity (rowBytes * (hi - lo))
  let mut ends : Array Nat := Array.mkEmpty (hi - lo)
  for i in [lo:hi] do
    out := out.push 44
    out := out.push 123
    for j in [0:cols.size] do
      let (k, c) := cols[j]!
      let x := t.at c i
      if x != OptJoin.unbound then
        if out.get! (out.size - 1) != 123 then out := out.push 44
        out := out ++ names[k]!
        out ← appendIdJsonM st reference x out
    out := out.push 125
    ends := ends.push out.size
  return (out, ends)

/-- A copy of `spec` whose arrays, pairs, boxed words and strings are new
    objects, made by the task that calls it. A scan reads its spec in every
    block; the spec the parent made is reachable from every task, and the Lean
    runtime takes and releases references to an object that two threads can
    reach with atomic operations, here on cache lines that every task uses
    (DBpedia d17 at 4 threads: `planChecksGo`, `lean_array_to_list_impl` and
    `lean_dec_ref_cold` together a third of the profile). The copy has the
    same value (`ScanSpec.fresh_eq`). The words go through `toNat` and back
    and the strings through `++ ""` so that the compiler does not reduce the
    copy to the original object (it reduces `⟨x.a, x.b⟩` to `x`). -/
def ScanSpec.fresh (s : ScanSpec) : ScanSpec :=
  { perm := s.perm
    key := s.key.map fun x => UInt64.ofNat x.toNat
    checks := s.checks.map fun p => (p.1, UInt64.ofNat p.2.toNat)
    named := s.named
    outVars := s.outVars.map (· ++ "")
    outCols := s.outCols.toList.toArray
    eqs := s.eqs.map fun p => (p.1 + 0, p.2 + 0) }

theorem ScanSpec.fresh_eq (s : ScanSpec) : s.fresh = s := by
  obtain ⟨perm, key, checks, named, outVars, outCols, eqs⟩ := s
  simp only [ScanSpec.fresh, Nat.add_zero, String.append_empty, Array.toArray_toList]
  have hk : key.map (fun x => UInt64.ofNat x.toNat) = key := by
    conv => rhs; rw [← Array.map_id key]
    congr 1; funext x; simp
  have hc : checks.map (fun p => (p.1, UInt64.ofNat p.2.toNat)) = checks := by
    conv => rhs; rw [← Array.map_id checks]
    congr 1; funext p; simp
  rw [hk, hc]
  simp

/-- A copy of a compiled FILTER conjunct whose strings, words, ranges and
    needle are new objects (the reason is `ScanSpec.fresh`'s: the conjuncts
    are read for every row of every block). The expression `e` is shared: it
    is read only when the reference evaluator decides a row. -/
def FKind.fresh : FKind → FKind
  | .idEq v c => .idEq (v ++ "") (c.map fun x => UInt64.ofNat x.toNat)
  | .idEqVar v w => .idEqVar (v ++ "") (w ++ "")
  | .str k v needle e => .str k (v ++ "") (needle.extract 0 needle.size) e
  | .strRange v ranges lo hi e => .strRange (v ++ "") (ranges.map fun p => (p.1 + 0, p.2 + 0)) lo hi e
  | .general e vs => .general e (vs.map (· ++ ""))
  | .residual env e vs => .residual env e (vs.map (· ++ ""))

theorem FKind.fresh_eq (f : FKind) : f.fresh = f := by
  cases f with
  | idEq v c => cases c <;> simp [FKind.fresh]
  | idEqVar v w => simp [FKind.fresh]
  | str k v needle e => simp [FKind.fresh, ByteArray.extract_zero_size]
  | strRange v ranges lo hi e =>
    simp only [FKind.fresh, String.append_empty, Nat.add_zero]
    congr 1
    conv => rhs; rw [← Array.map_id ranges]
    rfl
  | general e vs => simp [FKind.fresh]
  | residual env e vs => simp [FKind.fresh]

/-- The overlay context of a divided scan (no overlay: `divide?` refuses a
    scan with one), made by the task that calls it. -/
def OvCtx.fresh (ox : OvCtx) (key : Array UInt64) : OvCtx :=
  if ox.on then ox else ovCtx {} key

/-- The most blocks in one range of the divided streamed path. The parent
    writes the ranges in order, so a range that finishes early waits in memory
    with its rendered pieces until the earlier ranges are written. With
    ranges of at most this many blocks there are more ranges than tasks, and
    `Par.fold` (window = threads) holds at most `threads` finished or running
    ranges: the bytes held are bounded by `threads * streamRangeBlocks`
    blocks of output, not by the whole scan (olympics q21 at 4 threads:
    4 ranges of 9 blocks, all held, 23 MB of rendered rows; issue 799,
    stage 1d). -/
def streamRangeBlocks : Nat := 1

/-- Rows per rendered piece of the divided streamed path. A piece is made by
    a task and freed by the parent after it is written; a buffer of a whole
    block (about 500 KB for olympics q21) was a large allocation of the task
    thread's heap that was not reused after a free from another thread, and
    the next run cleared new huge pages for it (`clear_page_erms`, a third of
    the profile of q19 at 4 threads). 512 rows of q21 are about 64 KB. -/
def pieceRows : Nat := 512

/-- One block range of the divided streamed path: per scan chunk, the rows
    that pass the FILTERs, rendered (`renderRowsEndsM`) in pieces of at most
    `pieceRows` rows, at most `cap` rows over the range; the scan stops when
    it has `cap` rows. Each piece is its own buffer (a buffer carried through
    the loop would be shared with the loop state and copied on its first
    append in every block). -/
def streamPartM {m : Type → Type} [Monad m] (st : Store m) (spec : ScanSpec) (fs : Array FKind)
    (reference : Bool) (vars : Array String) (cap : Nat) (metas : Array BlockMeta) (ox : OvCtx)
    (X : List Nat) : ExceptT String m (Array (ByteArray × Array Nat) × ScanStats) := do
  let spec := spec.fresh
  let fs := fs.map FKind.fresh
  let ox := ox.fresh spec.key
  let memos0 : Array Memo := fs.map fun _ => {}
  -- `rowBytes`: the capacity per row of the next piece, from the pieces so
  -- far (their bytes per row, one eighth more). A piece that outgrows its
  -- buffer is copied to a larger one, and the copies were the largest source of
  -- page faults and of peak memory of the divided path (olympics q21 at 4
  -- threads, issue 799, KR 1.2).
  let ((_, pieces, _, _), s) ← scanListM st spec true (memos0, (#[] : Array (ByteArray × Array Nat)), (0 : Nat), (64 * (vars.size + 1) : Nat))
      (fun (memos, pieces, n, rowBytes) ch => do
        let (tab, memos) ← applyFilters st fs memos ch.table
        let take := min (cap - n) tab.rows
        if take == 0 then return ((memos, pieces, n, rowBytes), n < cap)
        if let some f := st.prefetch then f tab take
        let mut pieces := pieces
        let mut rowBytes := rowBytes
        for k in [0:(take + pieceRows - 1) / pieceRows] do
          let lo := k * pieceRows
          let hi := min take (lo + pieceRows)
          let piece ← renderRowsEndsM st reference tab vars lo hi rowBytes
          if hi > lo then rowBytes := (piece.1.size / (hi - lo)) * 9 / 8 + 16
          pieces := pieces.push piece
        pure ((memos, pieces, n + take, rowBytes), n + take < cap))
      metas (sortVarOf spec) ox X
  return (pieces, s)

/-- The parent's step over one rendered piece, as the single-thread streamed
    path steps over one scan chunk: skip what is left of OFFSET, emit up to
    what is left of LIMIT (no comma before the first row emitted). -/
def emitPieceM {m : Type → Type} [Monad m] (emit : ByteArray → m Unit) (off lim : Nat)
    (acc : Nat × Nat) (piece : ByteArray × Array Nat) : ExceptT String m (Nat × Nat) := do
  let (skipped, emitted) := acc
  let (bytes, ends) := piece
  let r := ends.size
  let skipHere := min (off - skipped) r
  let takeHere := min (lim - emitted) (r - skipHere)
  if takeHere > 0 then
    let a0 := if skipHere == 0 then 0 else ends[skipHere - 1]!
    let a := if emitted == 0 then a0 + 1 else a0
    let e := ends[skipHere + takeHere - 1]!
    if a == 0 && e == bytes.size then (emit bytes : m Unit)
    else (emit (bytes.extract a e) : m Unit)
  return (skipped + skipHere, emitted + takeHere)

/-- One block range of the divided counted path: `countStepM` over the range,
    from no groups. -/
def countPartM {m : Type → Type} [Monad m] (st : Store m) (spec : ScanSpec) (fs : Array FKind)
    (groupVars : Array String) (metas : Array BlockMeta) (ox : OvCtx) (X : List Nat) :
    ExceptT String m (Groups × ScanStats) := do
  let spec := spec.fresh
  let fs := fs.map FKind.fresh
  let ox := ox.fresh spec.key
  let groupVars := groupVars.map (· ++ "")
  let ((g, _), s) ← scanListM st spec (!fs.isEmpty) (({} : Groups), (fs.map fun _ => ({} : Memo)))
    (countStepM st fs groupVars) metas (sortVarOf spec) ox X
  return (g, s)

/-- One block range of the divided ORDER BY ... LIMIT path: the range's table,
    its rows that pass the FILTERs, then the first `k` of them in the ORDER BY
    order (`orderPermM`), in that order. -/
def topPartM {m : Type → Type} [Monad m] (st : Store m) (plan : Plan) (spec : ScanSpec)
    (fs : Array FKind) (k : Nat) (metas : Array BlockMeta) (ox : OvCtx) (X : List Nat) :
    ExceptT String m (Table × ScanStats) := do
  let spec := spec.fresh
  let fs := fs.map FKind.fresh
  let ox := ox.fresh spec.key
  let sortVar := sortVarOf spec
  let cap := 8 * X.foldl (fun a i => a + metas[i]!.rows) 0
  let init : Table := { vars := spec.outVars, cols := spec.outVars.map fun _ => ByteArray.emptyWithCapacity cap,
                        rows := 0, sortVar }
  let (t, s) ← scanListM st spec true init (fun acc ch => pure (acc.append ch.table, true)) metas sortVar ox X
  let (t, _) ← applyFilters st fs (fs.map fun _ => {}) t
  let perm ← orderPermM st plan t (some k)
  return (t.reorder perm, s)

/-- Run a plan. `emit` receives the SPARQL JSON text in pieces. `par`: divide
    the single-pattern paths into block ranges (stage 1b); `none` is the
    single-thread path. -/
def runPlanM {m : Type → Type} [Monad m] (st : Store m) (plan : Plan) (emit : ByteArray → m Unit)
    (reference : Bool := false) (par : Option (Par m) := none) (env : EvalEnv := {}) :
    ExceptT String m RunStats := do
  let pats ← plan.pats.mapM (resolvePat st)
  let fs := (← plan.filters.mapM (compileFilter st)) ++ plan.residuals.map (residualKind env)
  let memos0 : Array Memo := fs.map fun _ => {}
  let filterVars : Array String := fkVars fs ++ fkVars (plan.postFilters.map (residualKind env))
  let used : Array String :=
    plan.proj.foldl (fun a p => match p with
      | .var x => a.push x
      | .count _ (some x) => a.push x
      | .count _ none => a) #[]
    ++ filterVars ++ plan.order.map (·.1) ++ plan.groupVars
  let need (x : String) : Bool := used.contains x
  let mut stats : RunStats := {}
  (emit (jsonHead plan.outVars).toUTF8 : m Unit)
  let single := pats.size == 1 && !pats[0]!.hasMissing && plan.optionals.isEmpty
  if single && !plan.agg && plan.order.isEmpty && !plan.distinct then
    -- one pattern, no modifier that needs every row: block by block
    let t := pats[0]!
    -- a STRSTARTS conjunct on a variable of the pattern: the permutation that
    -- sorts on it after the bound positions (`windowPref`), so that blocks
    -- that no passing row can come from are not read (`windowStoreM`)
    let spec := mkSpec t (permFor t (windowPref t fs)) need
    let (st, window) ← windowStoreM st spec fs
    let lim := plan.limit.getD (2 ^ 63)
    if lim == 0 then
      stats := { stats with plan := #["LIMIT 0"] }
    else
      -- stage 1b: divided when OFFSET + LIMIT is above the estimate (the single
      -- scan then reads every selected block)
      match par, (← divideFor? st par spec streamRangeBlocks).filter (fun d => plan.offset + lim > d.2.2.2) with
      | some p, some (metas, ox, chunks, est) =>
        let total ← st.blockCount spec.perm
        let ((_, emitted), s) ← p.fold
            (fun v X => streamPartM v spec fs reference plan.outVars (plan.offset + lim) metas ox X) chunks
            (((0 : Nat), (0 : Nat)), ({ blocksTotal := total } : ScanStats))
            fun (acc, s) (pieces, s') => do
              let acc ← pieces.foldlM (emitPieceM emit plan.offset lim) acc
              pure (acc, s.add s')
        stats := { plan := #[s!"pattern 0 streamed in {chunks.length} block ranges ({p.threads} tasks at once at most; OFFSET + LIMIT above the estimate {est}): {permNames[spec.perm]!} key {spec.key.size}; blocks {s.blocksRead} read of {s.blocksSelected} selected of {s.blocksTotal}, frames {s.framesRead}, {s.bytesRead} bytes; rows {s.rowsOut}{windowNote window}"],
                   rows := emitted, scan := s.full }
      | _, _ =>
        let ((_, emitted, _), s) ← scanFoldM st spec true ((0 : Nat), (0 : Nat), memos0)
            fun (skipped, emitted, memos) ch => do
          let (tab, memos) ← applyFilters st fs memos ch.table
          let skipHere := min (plan.offset - skipped) tab.rows
          let takeHere := min (lim - emitted) (tab.rows - skipHere)
          if takeHere > 0 then
            let bytes ← renderRowsM st reference tab plan.outVars skipHere (skipHere + takeHere) (emitted == 0)
            (emit bytes : m Unit)
          let emitted := emitted + takeHere
          pure ((skipped + skipHere, emitted, memos), emitted < lim)
        stats := { plan := #[s!"pattern 0 streamed: {permNames[spec.perm]!} key {spec.key.size}; blocks {s.blocksRead} read of {s.blocksSelected} selected of {s.blocksTotal}, frames {s.framesRead}, {s.bytesRead} bytes; rows {s.rowsOut}{windowNote window}"],
                   rows := emitted, scan := s.full }
  else
    let mut table : Table := default
    if single && plan.agg then
      -- aggregate block by block
      let t := pats[0]!
      let spec := mkSpec t (permFor t none) need
      -- issue 932: no FILTER, no GROUP BY, no overlay: the PRM1 entries give
      -- the count of the blocks they decide (`metaCountM`)
      let metaOk := fs.isEmpty && plan.groupVars.isEmpty && (st.ovl spec.perm).isEmpty
      -- stage 1b: one group map per block range, added in range order
      let (groups, s, how) ← if metaOk then do
          let (n, decided, s) ← metaCountM st spec
          let g : Groups := if n == 0 then {} else ({} : Groups).add [] n
          pure (g, s, s!" from PRM1 entries ({decided} blocks decided by their entries)")
        else match par, ← divideFor? st par spec 0 with
        | some p, some (metas, ox, chunks, _) => do
          let total ← st.blockCount spec.perm
          let (g, s) ← p.fold (fun v X => countPartM v spec fs plan.groupVars metas ox X) chunks
            (({} : Groups), ({ blocksTotal := total } : ScanStats))
            fun (g, s) (g', s') => pure (g.merge g', s.add s')
          pure (g, s, s!" in {chunks.length} block ranges ({p.threads} tasks at once at most)")
        | _, _ => do
          let ((groups, _), s) ← scanFoldM st spec (!fs.isEmpty) (({} : Groups), memos0)
            (countStepM st fs plan.groupVars)
          pure (groups, s, "")
      let line := s!"pattern 0 counted while streaming{how}: {permNames[spec.perm]!} key {spec.key.size}; blocks {s.blocksRead} read of {s.blocksSelected} selected of {s.blocksTotal}, frames {s.framesRead}, {s.bytesRead} bytes; rows {s.rowsOut}; groups {groups.keys.size}"
      stats := { stats with plan := #[line], scan := s.full }
      match groupTable plan groups with
      | .ok t => table := t
      | .error e => throw e
    else
      -- stage 1b: ORDER BY ... LIMIT over one pattern, without DISTINCT: the
      -- first OFFSET + LIMIT rows of each block range, then `finishM` over
      -- their union. The scan is the one `evalBgpM` makes for one pattern.
      let topDiv ← if par.isSome && single && !plan.agg && !plan.order.isEmpty && !plan.distinct &&
          plan.limit.isSome then do
          let t0 := pats[0]!
          let keep (v : String) : Bool := need v || varCount pats v ≥ 2
          -- the estimate `evalBgpM` computes (on the permutation of
          -- `permFor t0 none`, which it opens for that)
          let specE := mkSpec t0 (permFor t0 none) keep
          let est := selRows (← st.blocksForRange specE.perm specE.key)
          let spec0 := mkSpec t0 (permFor t0 (bestSortPos t0 pats)) keep
          pure ((← divideFor? st par spec0 0).map fun d => (spec0, est, d))
        else pure none
      let (t1, lines, s) ← match par, topDiv with
        | some p, some (spec0, est, metas, ox, chunks, _) => do
          let k := plan.offset + plan.limit.getD 0
          let init : Table := Table.empty spec0.outVars
          let total ← st.blockCount spec0.perm
          let (u, s) ← p.fold (fun v X => topPartM v plan spec0 fs k metas ox X) chunks
            (init, ({ blocksTotal := total } : ScanStats))
            fun (u, s) (t, s') => pure (u.append t, s.add s')
          pure (u, #[s!"pattern 0: {permNames[spec0.perm]!} key {spec0.key.size} estimate {est}; blocks {s.blocksRead} read of {s.blocksSelected} selected of {s.blocksTotal}, frames {s.framesRead}, {s.bytesRead} bytes; rows {s.rowsOut}; first {k} rows of the order kept in each of {chunks.length} block ranges ({p.threads} tasks at once at most): {u.rows} rows"], s.full)
        | _, _ =>
          if plan.optionals.isEmpty then do
            let (t0, lines, s) ← evalBgpM st pats need
            let (t1, _) ← applyFilters st fs memos0 t0
            pure (t1, lines, s)
          else evalOptionalsM st plan pats fs need env
      stats := { stats with plan := lines, scan := s }
      if plan.agg then
        let g := countChunk plan.groupVars { table := t1, consts := t1.vars.map fun _ => none } {}
        match groupTable plan g (countItems plan t1) with
        | .ok t => table := t
        | .error e => throw e
      else table := t1
    let out ← finishM st plan table
    let pieces := (out.rows + 4095) / 4096
    for k in [0:pieces] do
      let lo := 4096 * k
      let hi := min out.rows (lo + 4096)
      let bytes ← renderRowsM st reference out plan.outVars lo hi (lo == 0)
      (emit bytes : m Unit)
    stats := { stats with rows := out.rows }
  (emit jsonTail.toUTF8 : m Unit)
  let t := stats.scan
  let plan1 := stats.plan.push s!"total: rows decoded {t.rowsDecoded} (of a full scan the rows of its table, of a scan with candidates the rows gathered); join-key values tested {t.keysTested}; blocks read {t.blocksRead} of {t.blocksSelected} selected, {t.sipSkipped} skipped by candidates; {t.bytesRead} bytes"
  return { stats with plan := if fs.isEmpty then plan1 else plan1.push (filterKindsLine fs) }

/-! ## The reference post-processing on decoded solutions (issue 823)

A plan with `post = some ps` runs its WHERE clause on ids (`whereTableM`: the
BGP joins, the FILTERs on ids and the residual FILTERs, the OPTIONAL left
joins), decodes the rows into solution mappings (`decodeRowsM`; a variable
whose id is `OptJoin.unbound` is left unbound), and then calls the reference
evaluator's own function for the form, on that solution sequence:

  * SELECT: `selectPost` (SPARQL 1.1 section 18.2.4: GROUP BY, the
    aggregates, HAVING, the trailing VALUES join, the SELECT expressions,
    ORDER BY, projection, DISTINCT or REDUCED, OFFSET and LIMIT), the
    function `evalSelect` and `StoreDataset.runSelectQueryBackendDataset`
    call on the WHERE solutions;
  * ASK: `formHasSolution`, the function of `evalAsk` and
    `StoreDataset.evalAskBackendReference`;
  * CONSTRUCT: `formSolutions` then `constructGraphOf` (section 16.2), the
    two steps of `evalConstruct` (`IdPostTheorems.evalConstruct_eq`).

So each step equals the reference by definition once its input does. The
open step is that input: the decoded id rows are the reference's BGP-plus-
FILTER solutions (lemma L6a of https://github.com/danbri/factoidal/issues/776);
the W3C census (`tests/sbm11/census.sh`) is the differential check until it
is proved. The reference functions get `Graph.empty` as the active graph and
an environment without a dataset: `translate` admits a post-processed query
only when no expression outside its WHERE clause holds EXISTS or NOT EXISTS,
the only expressions that read them. -/

/-- SPARQL 1.1 section 16.2: the CONSTRUCT template instantiated for each
    solution (`instantiateSolutions`: fresh blank nodes per solution index,
    ill-formed triples dropped) and collected into a graph (`Graph.add`:
    duplicates collapse). This is the graph `evalConstruct` builds from its
    solution sequence (`IdPostTheorems.evalConstruct_eq`). -/
def constructGraphOf (template : List TriplePattern) (solutions : L4Factoidal.SPARQL.SolutionSeq) :
    Graph :=
  (L4Factoidal.SPARQL.instantiateSolutions template solutions 0).foldl (fun g t => g.add t) Graph.empty

/-- The answer of a post-processed plan; the harness writes it as the
    reference fallback writes its answer. -/
inductive PostAnswer where
  | solutions (vars : List String) (rows : L4Factoidal.SPARQL.SolutionSeq)
  | boolean (b : Bool)
  | graph (g : Graph)

/-- The rows of `t` as solution mappings: per row, each column whose id is
    not `OptJoin.unbound`, decoded (`Store.termOf`; each distinct id once,
    so equal ids share one term). The distinct ids are kept in a `Cache`
    (`IdAgg.Cache.getM`): every lookup returns `termOf` of the id and the
    cache holds only such values (`IdAgg.Cache.getPure_fst`, `getPure_valid`;
    any sequence of lookups: `IdAgg.Cache.getPure_list`). Cost (DBpedia,
    2026-10-13): the 326,365 rows of three variables of d19's join decode in
    about 2.0 s (warm), most of it `Session.termOf` on the distinct dictionary
    ids; decoding them in id order (each dictionary page read once) measured
    the same within the spread, so the rows are decoded in table order. -/
def decodeRowsM {m : Type → Type} [Monad m] (st : Store m) (t : Table) :
    ExceptT String m L4Factoidal.SPARQL.SolutionSeq := do
  let mut memo : IdAgg.Cache IdAgg.Id64 Term := {}
  let mut out : Array Binding := Array.mkEmpty t.rows
  for i in [0:t.rows] do
    let mut mu : Array (String × Term) := Array.mkEmpty t.vars.size
    for c in [0:t.vars.size] do
      let x := t.at c i
      if x != OptJoin.unbound then
        let (tm, memo') ← memo.getM (fun k => st.termOf k.val) (IdAgg.Id64.ofU x)
        memo := memo'
        mu := mu.push (t.vars[c]!, tm)
    out := out.push mu.toList
  return out.toList

/-- The solutions of the WHERE clause of a plan on ids, every variable kept:
    the BGP joins, the FILTERs (on ids and residual), the OPTIONAL left joins
    and the FILTERs beside them. With no triple pattern: one solution with
    no binding (the empty group), then the FILTERs. `firstRows = some n`:
    only the first `n` rows; a single pattern then streams and its scan stops
    after them. -/
def whereTableM {m : Type → Type} [Monad m] (st : Store m) (plan : Plan) (env : EvalEnv)
    (firstRows : Option Nat) : ExceptT String m (Table × Array String × ScanStats) := do
  let fs := (← plan.filters.mapM (compileFilter st)) ++ plan.residuals.map (residualKind env)
  let memos0 : Array Memo := fs.map fun _ => {}
  if plan.pats.isEmpty then
    let t0 : Table := { vars := #[], cols := #[], rows := 1 }
    let (t, _) ← applyFilters st fs memos0 t0
    return (t, #[s!"no triple pattern: one solution with no binding, {fs.size} FILTER conjuncts: {t.rows} rows"], {})
  let pats ← plan.pats.mapM (resolvePat st)
  let need : String → Bool := fun _ => true
  if let some n := firstRows then
    if pats.size == 1 && !pats[0]!.hasMissing && plan.optionals.isEmpty then
      let t := pats[0]!
      let spec := mkSpec t (permFor t none) need
      let init : Table := Table.empty spec.outVars
      if n == 0 then return (init, #["the first 0 rows: no scan"], {})
      let ((acc, _), s) ← scanFoldM st spec true (init, memos0) fun (acc, memos) ch => do
        let (tab, memos) ← applyFilters st fs memos ch.table
        let acc := acc.append (tab.slice 0 (n - acc.rows))
        pure ((acc, memos), acc.rows < n)
      return (acc, #[s!"pattern 0 streamed until {n} rows: {permNames[spec.perm]!} key {spec.key.size}; blocks {s.blocksRead} read of {s.blocksSelected} selected of {s.blocksTotal}, frames {s.framesRead}, {s.bytesRead} bytes; rows {acc.rows}"], s.full)
  let (t0, lines, s) ← if plan.optionals.isEmpty then do
      let (t0, lines, s) ← evalBgpM st pats need
      let (t1, _) ← applyFilters st fs memos0 t0
      pure (t1, lines, s)
    else evalOptionalsM st plan pats fs need env
  let t := match firstRows with
    | some n => t0.slice 0 n
    | none => t0
  return (t, if fs.isEmpty then lines else lines.push (filterKindsLine fs), s)

/-- Run a post-processed plan: the WHERE solutions on ids, decoded, then the
    reference function of the query form (section above).

    A SELECT that `AggStream.aggPlan?` accepts (GROUP BY variables or none,
    items that are variables or non-DISTINCT COUNT, SUM, MIN, MAX, AVG of a
    variable) is not decoded row by row: `IdAgg.aggregateM` groups the id
    table and steps the accumulators of `AggStream`, the rows of the groups
    are `groupedRow`, and the shared tail `groupedTail` (ORDER BY, projection,
    DISTINCT, OFFSET, LIMIT) is the reference's. When the table does not meet
    the conditions of `aggregateM` (a group column with an id that is not a
    blank node, an IRI, an inline integer or an inline boolean, or unbound) the
    rows are decoded and `selectPost` runs as for any other query
    (https://github.com/danbri/factoidal/issues/825). -/
def runPostM {m : Type → Type} [Monad m] (st : Store m) (plan : Plan) (ps : PostSpec) (env : EvalEnv) :
    ExceptT String m (PostAnswer × RunStats) := do
  let (t, lines, s) ← whereTableM st plan env ps.firstRows
  let q := ps.query
  let active : Graph := Graph.empty
  let totalLine := s!"total: rows decoded {s.rowsDecoded}; blocks read {s.blocksRead} of {s.blocksSelected} selected, {s.sipSkipped} skipped by candidates; {s.bytesRead} bytes"
  let fast ← match q.form, (if st.aggOnIds then L4Factoidal.SPARQL.AggStream.aggPlan? q else none) with
    | .select _, some p => do
      match ← IdAgg.aggregateM st.termOf t p with
      | some r => pure (some (p, r))
      | none => pure none
    | _, _ => pure none
  match fast with
  | some (p, r) =>
    let omega' := (List.range r.reps.size).map fun g =>
      L4Factoidal.SPARQL.AggStream.groupedRow env p.items (r.vals[g]!).toList r.reps[g]!
    let rows := L4Factoidal.SPARQL.AggStream.groupedTail env active p.items p.md omega'
    let line := s!"post: {t.rows} WHERE solutions aggregated on ids into {r.reps.size} groups ({r.decoded} distinct ids decoded, {r.repValues} values in the representative rows); reference tail: {rows.length} results"
    return (PostAnswer.solutions (L4Factoidal.SPARQL.Query.projectedVars q) rows,
            { plan := (lines.push line).push totalLine, rows := rows.length, scan := s })
  | none =>
  let omega0 ← decodeRowsM st t
  let (ans, n, how) ← match q.form with
    | .select _ =>
      let rows := L4Factoidal.SPARQL.selectPost env active q omega0
      pure (PostAnswer.solutions (L4Factoidal.SPARQL.Query.projectedVars q) rows, rows.length, "selectPost")
    | .ask =>
      let b := L4Factoidal.SPARQL.formHasSolution env active q omega0
      pure (PostAnswer.boolean b, (if b then 1 else 0), "formHasSolution")
    | .construct template =>
      let g := constructGraphOf template (L4Factoidal.SPARQL.formSolutions env active q omega0)
      pure (PostAnswer.graph g, g.length, "formSolutions, constructGraphOf")
    | .describe _ => throw "DESCRIBE is not post-processed on ids"
  let line := s!"post: {t.rows} WHERE solutions decoded{match ps.firstRows with | some k => s!" (the first {k} suffice)" | none => ""}; reference {how}: {n} results"
  return (ans, { plan := (lines.push line).push totalLine,
                 rows := n, scan := s })

end L4Factoidal.Storage.Sbm11.IdQuery
