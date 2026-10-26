/-
L4Factoidal.SPARQL.AggStream — COUNT, SUM, MIN, MAX and AVG over a plain
variable as one pass over a stream of values, and the SELECT items of a
grouped query computed from aggregate values that are already known
(https://github.com/danbri/factoidal/issues/825; record
docs/designissues/2026-10-12-sbm11-stage4.md section 16).

## Why

`evalAggregate` evaluates the argument of an aggregate at every row of a
group (`evalOverGroup`: a lookup in the row's binding), then filters, then
folds. The SBM11 id path (`Storage/Sbm11/IdAgg`)
holds the rows of a group as term ids. It decodes each distinct id once into a
`Summary` (the original evaluated value), and feeds the
summaries of a group's rows, in row order, to the accumulator of the aggregate.
The accumulator makes the same decisions as the list functions the reference
calls (`filterNonError`, `sumNumeric`, `findMin`, `findMax`, `avgNumeric`),
in the same order, so the theorems here say that its result IS
`evalAggregate`'s:

  * `evalAggregate_stream`: `evalAggregate env fn false (.var w) g` is
    `finish fn` of the left fold of `step fn` over the summaries of the values
    of `w` in the group's rows, for `fn` one of COUNT, SUM, MIN, MAX, AVG;
  * `evalAggregate_star`: `COUNT(*)` is the number of rows of the group;
  * `evalSelectItemsGroup_pre`: the SELECT items of a group, when each is a
    variable or a non-DISTINCT aggregate, are `itemsPre` of the values of the
    group's aggregates (`itemAggs`);
  * `selectPost_grouped`: for a SELECT with grouping and no HAVING and no
    trailing VALUES, `selectPost` is the shared tail `groupedTail` of the rows
    `groupOmegaRow` of the groups.

## What is not proved

That a table of ids, grouped by the id path, gives the groups of
`groupWhere` on the decoded rows, with the same representative rows and the
same sequence of values in each group (lemma L5k of the end-to-end record). It
is checked by the gate queries of `tests/sbm11/gate` and by the W3C census, and
is NOT proved. (The agreement of `groupSolutionsFast` with `groupSolutions` is
proved: `groupSolutionsFast_eq` in `L4Factoidal.SPARQL.GroupFastTheorems`.)

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.SPARQL.Query

namespace L4Factoidal.SPARQL.AggStream

open L4Factoidal.RDF

/-! ## The value a variable has -/

/-- A bound variable retains its RDF term. Numeric interpretation belongs to
arithmetic, so an xsd:float is not promoted to double before the operation. -/
def varView (t : Term) : EvalResult := .term t

/-- `Expr.evalIn` of a variable reads its binding and nothing else. -/
theorem evalIn_var (env : EvalEnv) (mu : Binding) (v : VarName) :
    Expr.evalIn env mu (.var v) =
      (match mu.lookup v with
       | some t => varView t
       | none => .error) := by
  simp only [Expr.evalIn]
  cases mu.lookup v <;> rfl

/-- A bound variable is never the type error, so `COUNT(?x)` counts the rows
where `?x` is bound, whatever term it is bound to. -/
theorem varView_ne_error (t : Term) : varView t ≠ .error := by
  simp [varView]

/-! ## What a step reads of one value -/

/-- The original evaluated value, cached once per distinct term id, with the
readings the shared arithmetic and the shared order make of it: `nv` is
`numericValue?`, `isInt` is `isIntegerOperand`, `isNum` is `isNumericOperand`.
The value itself is not promoted (that would lose the source float datatype);
the readings are made once here and not at every row
(https://github.com/danbri/factoidal/issues/862). A summary is only made by
`Summary.of`, so the readings are those of `v`. -/
structure Summary where
  v : EvalResult
  nv : Option XSD.Val
  isInt : Bool
  isNum : Bool

def Summary.of (v : EvalResult) : Summary :=
  ⟨v, v.numericValue?, v.isIntegerOperand, v.isNumericOperand⟩

/-- `Summary.of .error`, written out so that compiled code does not call
`Summary.of` (`tools/lean-csimp-reach.py`). -/
instance : Inhabited Summary := ⟨⟨.error, none, false, false⟩⟩

/-- `Summary.of` with one datatype lookup for a literal: the three readings
of a literal all start from `builtinOfIri?` of its datatype IRI, which on
DBpedia d19 was most of the cost of a summary
(https://github.com/danbri/factoidal/issues/862). -/
def Summary.ofFast (v : EvalResult) : Summary :=
  match v with
  | .term (.literal l) =>
    let bo := XSD.builtinOfIri? l.val.datatype.val
    ⟨v, bo.bind (fun b => if Fn.Numeric.isType b then XSD.lexicalFor .xsd10 b l.val.lexicalForm else none),
      bo.any (fun b => (XSD.intBounds b).isSome), bo.any Fn.Numeric.isType⟩
  | _ => ⟨v, v.numericValue?, v.isIntegerOperand, v.isNumericOperand⟩

/-- The summary of a literal whose datatype lookup `bo` is already made (by a
caller that keeps the lookups of the datatype IRIs it has met). -/
def Summary.ofLit (l : WfLiteral) (bo : Option XSD.Builtin) : Summary :=
  ⟨.term (.literal l),
    bo.bind (fun b => if Fn.Numeric.isType b then XSD.lexicalFor .xsd10 b l.val.lexicalForm else none),
    bo.any (fun b => (XSD.intBounds b).isSome), bo.any Fn.Numeric.isType⟩

/-- With the lookup of its own datatype IRI, `ofLit` is `Summary.of`. -/
theorem Summary.ofLit_eq (l : WfLiteral) :
    Summary.ofLit l (XSD.builtinOfIri? l.val.datatype.val) = Summary.of (.term (.literal l)) := rfl

/-- The compiler runs `Summary.ofFast` wherever the source says `Summary.of`. -/
@[csimp] theorem Summary.of_eq_ofFast : @Summary.of = @Summary.ofFast := by
  funext v
  cases v with
  | term t =>
    cases t with
    | literal l => rfl
    | _ => rfl
  | _ => rfl



theorem Summary.of_v (v : EvalResult) : (Summary.of v).v = v := rfl

/-! ## The accumulators -/

/-- The state of one aggregate over one group. -/
inductive AggAcc where
  /-- COUNT: the values counted -/
  | cnt (n : Nat)
  /-- SUM and AVG: the running shared-arithmetic result and non-error count.
      Arithmetic propagates a nonnumeric operand as `.error`. -/
  | num (s : EvalResult) (c : Nat)
  /-- MIN and MAX: the best original value so far, with its readings -/
  | best (b : Option Summary)

instance : Inhabited AggAcc := ⟨.cnt 0⟩

/-- The aggregate functions the accumulators cover. -/
def Streamed : AggregateFn → Bool
  | .count | .sum | .min | .max | .avg => true
  | _ => false

def AggAcc.init : AggregateFn → AggAcc
  | .count => .cnt 0
  | .sum | .avg => .num (.num 0) 0
  | _ => .best none

def AggAcc.stepCount : AggAcc → AggAcc
  | .cnt n => .cnt (n + 1)
  | a => a

def AggAcc.stepNum (a : AggAcc) (s : Summary) : AggAcc :=
  match a with
  | .num total c =>
    match total, s.nv, s.isInt with
    -- an integer value onto an integer sum: `evalArithInt .add`, without the
    -- reading of the sum (`Dec.ofInt`) at every row
    | .num t, some (.dec x), true => .num (.num (x.mantissa + t)) (c + 1)
    | _, _, _ =>
      .num (evalArithmeticRead .add s.nv total.numericValue? s.isInt total.isIntegerOperand) (c + 1)
  | a => a

/-- The integer branch of `stepNum` is the shared arithmetic on the readings. -/
theorem AggAcc.stepNum_read (total : EvalResult) (c : Nat) (s : Summary) :
    (AggAcc.num total c).stepNum s =
      .num (evalArithmeticRead .add s.nv total.numericValue? s.isInt total.isIntegerOperand) (c + 1) := by
  simp only [AggAcc.stepNum]
  split
  · rename_i t x h2 h3
    rw [h2, h3]
    simp [EvalResult.numericValue?, EvalResult.isIntegerOperand, evalArithmeticRead, evalArithInt,
      XSD.Dec.ofInt, Int.add_comm]
  · rfl

/-- On a summary made by `Summary.of`, the step is the shared arithmetic. -/
theorem AggAcc.stepNum_of (v total : EvalResult) (c : Nat) :
    (AggAcc.num total c).stepNum (Summary.of v) = .num (evalArithmetic .add v total) (c + 1) := by
  rw [AggAcc.stepNum_read, evalArithmetic_eq_read]
  rfl

/-- MAX and MIN: a later value replaces the best one when `keep` accepts the
comparison of the two original values. MAX keeps it when it is not below the best
(`findMax` keeps the last of equal values, §18.5.1.6); MIN when it is not above
it (`findMin`, §18.5.1.5). -/
def AggAcc.stepBest (keep : Int → Bool) (a : AggAcc) (s : Summary) : AggAcc :=
  match a with
  | .best none => .best (some s)
  | .best (some current) =>
    if keep (sparqlOrderReadFast s.v current.v s.isNum current.isNum s.nv current.nv)
    then .best (some s) else a
  | a => a

/-- On summaries made by `Summary.of`, the comparison is the shared order. -/
theorem AggAcc.stepBest_of (keep : Int → Bool) (v cur : EvalResult) :
    AggAcc.stepBest keep (.best (some (Summary.of cur))) (Summary.of v) =
      if keep (sparqlOrderValue v cur) then .best (some (Summary.of v))
      else .best (some (Summary.of cur)) := by
  simp only [AggAcc.stepBest, sparqlOrderReadFast_eq, sparqlOrderValue, sparqlOrder_eq_read]
  rfl

/-- The best-value step retains the reference engine's error-removal policy.
This agreement does not establish the unresolved SPARQL 1.1 error policy. -/
def AggAcc.stepKeep (keep : Int → Bool) (a : AggAcc) (s : Summary) : AggAcc :=
  match s.v with
  | .error => a
  | _ => a.stepBest keep s

def keepMax : Int → Bool := fun c => decide (c ≥ 0)
def keepMin : Int → Bool := fun c => decide (c ≤ 0)

/-- One value: retain the reference engine's error-removal policy, then
apply the chosen aggregate step. COUNT's error removal is normative; agreement
for the other aggregates is a compatibility result (errata-query-6). -/
def AggAcc.step (fn : AggregateFn) (a : AggAcc) (s : Summary) : AggAcc :=
  match fn with
  | .count => (match s.v with | .error => a | _ => a.stepCount)
  | .sum | .avg => (match s.v with | .error => a | _ => a.stepNum s)
  | .min => a.stepKeep keepMin s
  | .max => a.stepKeep keepMax s
  | _ => a

/-- §18.5.1.4 AVG from the shared sum and non-error count. The accumulator
uses the same reverse enumeration as `sumNumeric`; no reassociation is used.
The number of state fields is constant; arbitrary-precision values can grow.
The readings of each value are made once (`Summary.of`); the running sum is
read again at each step, which for an integer sum is `Dec.ofInt`. -/
def avgOfAcc (s : EvalResult) (c : Nat) : EvalResult :=
  if c == 0 then .num 0
  else evalArithmetic .div s (.num (Int.ofNat c))

theorem avgNumeric_eq (vals : List EvalResult) :
    avgNumeric vals = avgOfAcc (sumNumeric vals) vals.length := by
  cases vals <;> simp [avgNumeric, avgOfAcc]

/-- The value of the aggregate from its final state. -/
def AggAcc.finish (fn : AggregateFn) (a : AggAcc) : EvalResult :=
  match fn, a with
  | .count, .cnt n => .num (Int.ofNat n)
  | .sum, .num s _ => s
  | .avg, .num s c => avgOfAcc s c
  | .min, .best b | .max, .best b =>
    match b with
    | some v => v.v
    | none => .error
  | _, _ => .error

/-- The reference's aggregate over the values of a group's rows, for the
functions the accumulators cover (`evalAggregate` after `evalOverGroup`). -/
def aggVals : AggregateFn → List EvalResult → EvalResult
  | .count, vals => .num (Int.ofNat (filterNonError vals).length)
  | .sum, vals => sumNumeric (filterNonError vals)
  | .avg, vals => avgNumeric (filterNonError vals)
  | .min, vals => findMin (filterNonError vals)
  | .max, vals => findMax (filterNonError vals)
  | _, _ => .error

/-- `evalAggregate` of a non-DISTINCT aggregate over an expression other than
the two spellings of `COUNT(*)` is `aggVals` of the values of the expression. -/
theorem evalAggregate_eq_aggVals (env : EvalEnv) (fn : AggregateFn) (hfn : Streamed fn = true)
    (e : Expr) (hstar : (e = .var "*" ∨ e = .boolLit true) → False) (g : SolutionGroup) :
    evalAggregate env fn false e g = aggVals fn (evalOverGroup env e g) := by
  cases fn with
  | count =>
    simp only [evalAggregate, aggVals]
    split
    · exact absurd (Or.inl rfl) hstar
    · exact absurd (Or.inr rfl) hstar
    · simp
  | sum => simp [evalAggregate, aggVals]
  | avg => simp [evalAggregate, aggVals]
  | min => simp [evalAggregate, aggVals]
  | max => simp [evalAggregate, aggVals]
  | groupConcat s => simp [Streamed] at hfn
  | sample => simp [Streamed] at hfn

/-- COUNT(*) of a group is the number of its rows. -/
theorem evalAggregate_star (env : EvalEnv) (g : SolutionGroup) :
    evalAggregate env .count false (.boolLit true) g = .num (Int.ofNat g.solutions.length) ∧
    evalAggregate env .count false (.var "*") g = .num (Int.ofNat g.solutions.length) := by
  simp [evalAggregate]


/-! ## The stream is the list function -/

theorem filterNonError_cons (v : EvalResult) (rest : List EvalResult) :
    filterNonError (v :: rest) = if v = .error then filterNonError rest else v :: filterNonError rest := by
  cases v <;> simp [filterNonError]

/-- COUNT: one per value that is not the type error. -/
theorem count_stream (vals : List EvalResult) : ∀ n,
    (vals.map Summary.of).foldl (AggAcc.step .count) (.cnt n) =
      .cnt (n + (filterNonError vals).length) := by
  induction vals with
  | nil => intro n; simp [filterNonError]
  | cons v rest ih =>
    intro n
    rw [filterNonError_cons]
    cases v <;> simp [AggAcc.step, Summary.of, AggAcc.stepCount, ih] <;> omega


/-- The step of SUM and AVG on a value that is not the type error. -/
theorem step_num_of_ne (fn : AggregateFn) (hfn : fn = .sum ∨ fn = .avg) (a : AggAcc) (v : EvalResult)
    (hv : v ≠ .error) : AggAcc.step fn a (Summary.of v) = a.stepNum (Summary.of v) := by
  rcases hfn with rfl | rfl <;> cases v <;> first | exact absurd rfl hv | rfl

theorem step_num_error (fn : AggregateFn) (hfn : fn = .sum ∨ fn = .avg) (a : AggAcc) :
    AggAcc.step fn a (Summary.of .error) = a := by
  rcases hfn with rfl | rfl <;> rfl

/-- SUM and AVG use exactly the reference arithmetic step and count values
that survive `filterNonError`. The state has no input-sized value buffer. -/
theorem num_stream (fn : AggregateFn) (hfn : fn = .sum ∨ fn = .avg) (vals : List EvalResult) :
    ∀ total c,
    (vals.map Summary.of).foldl (AggAcc.step fn) (.num total c) =
      .num ((filterNonError vals).foldl (fun acc v => evalArithmetic .add v acc) total)
           (c + (filterNonError vals).length) := by
  induction vals with
  | nil => intro total c; simp [filterNonError]
  | cons v rest ih =>
    intro total c
    rw [filterNonError_cons]
    by_cases hv : v = .error
    · subst hv
      simp only [if_true, List.map_cons, List.foldl_cons, step_num_error fn hfn]
      exact ih total c
    · simp only [hv, if_false, List.map_cons, List.foldl_cons]
      rw [step_num_of_ne fn hfn _ v hv, AggAcc.stepNum_of]
      simp only [ih, List.length_cons]
      congr 1
      omega

/-- The fold of MAX and MIN: the best value so far against the next. -/
def bestFold (keep : Int → Bool) (a : EvalResult) (rest : List EvalResult) : EvalResult :=
  rest.foldl (fun acc x => if keep (sparqlOrderValue x acc) then x else acc) a

theorem findMax_eq (vals : List EvalResult) :
    findMax vals = (match vals with
      | [] => .error
      | v :: rest => bestFold keepMax v rest) := by
  cases vals with
  | nil => rfl
  | cons v rest => simp [findMax, bestFold, keepMax]

theorem findMin_eq (vals : List EvalResult) :
    findMin vals = (match vals with
      | [] => .error
      | v :: rest => bestFold keepMin v rest) := by
  cases vals with
  | nil => rfl
  | cons v rest => simp [findMin, bestFold, keepMin]

/-- MIN and MAX from a state that already holds a value. -/
theorem best_stream_from (keep : Int → Bool) (vals : List EvalResult) : ∀ (a : EvalResult),
    (vals.map Summary.of).foldl (AggAcc.stepKeep keep) (.best (some (Summary.of a))) =
      .best (some (Summary.of (bestFold keep a (filterNonError vals)))) := by
  induction vals with
  | nil => intro a; simp [filterNonError, bestFold]
  | cons v rest ih =>
    intro a
    rw [filterNonError_cons]
    by_cases hv : v = .error
    · subst hv
      simp only [if_true, List.map_cons, List.foldl_cons]
      exact ih a
    · have hs : AggAcc.stepKeep keep (.best (some (Summary.of a))) (Summary.of v) =
          AggAcc.stepBest keep (.best (some (Summary.of a))) (Summary.of v) := by
        cases v <;> first | exact absurd rfl hv | rfl
      simp only [hv, if_false, List.map_cons, List.foldl_cons, hs, AggAcc.stepBest_of]
      by_cases hk : keep (sparqlOrderValue v a) = true
      · simp only [hk, if_true]
        rw [ih v]
        simp [bestFold, hk]
      · simp only [hk, Bool.false_eq_true, if_false]
        rw [ih a]
        simp [bestFold, hk]

/-- MIN and MAX from the empty state: the first value that is not the type
error starts the fold. -/
theorem best_stream (keep : Int → Bool) (vals : List EvalResult) :
    (vals.map Summary.of).foldl (AggAcc.stepKeep keep) (.best none) =
      (match filterNonError vals with
       | [] => .best none
       | v :: rest => .best (some (Summary.of (bestFold keep v rest)))) := by
  induction vals with
  | nil => simp [filterNonError]
  | cons v rest ih =>
    rw [filterNonError_cons]
    by_cases hv : v = .error
    · subst hv
      simp only [if_true, List.map_cons, List.foldl_cons]
      exact ih
    · simp only [hv, if_false, List.map_cons, List.foldl_cons]
      have h1 : AggAcc.stepKeep keep (.best none) (Summary.of v) = .best (some (Summary.of v)) := by
        cases v <;> first | exact absurd rfl hv | rfl
      rw [h1, best_stream_from]


theorem step_min : AggAcc.step .min = AggAcc.stepKeep keepMin := rfl

theorem step_max : AggAcc.step .max = AggAcc.stepKeep keepMax := rfl

/-- COUNT, SUM, MIN, MAX and AVG of a variable are the value of the accumulator
after one pass over the summaries of the variable's values in the rows of the
group, in row order. -/
theorem evalAggregate_stream (env : EvalEnv) (fn : AggregateFn) (hfn : Streamed fn = true)
    (w : VarName) (hw : w ≠ "*") (g : SolutionGroup) :
    evalAggregate env fn false (.var w) g =
      AggAcc.finish fn ((g.solutions.map (fun mu => Summary.of (Expr.evalIn env mu (.var w)))).foldl
        (AggAcc.step fn) (AggAcc.init fn)) := by
  have hstar : ((Expr.var w) = .var "*" ∨ (Expr.var w) = .boolLit true) → False := by
    intro h
    rcases h with h | h
    · exact hw (by injection h)
    · cases h
  rw [evalAggregate_eq_aggVals env fn hfn _ hstar g]
  have hmap : (g.solutions.map (fun mu => Summary.of (Expr.evalIn env mu (.var w)))) =
      (evalOverGroup env (.var w) g).map Summary.of := by
    simp [evalOverGroup, List.map_map, Function.comp_def]
  rw [hmap]
  generalize evalOverGroup env (.var w) g = vals
  cases fn with
  | count =>
    simp only [AggAcc.init, aggVals]
    rw [count_stream vals 0]
    simp [AggAcc.finish]
  | sum =>
    have h := num_stream .sum (Or.inl rfl) vals (.num 0) 0
    simp only [AggAcc.init, aggVals]
    rw [h]
    rfl
  | avg =>
    have h := num_stream .avg (Or.inr rfl) vals (.num 0) 0
    simp only [AggAcc.init, aggVals]
    rw [h]
    simp only [AggAcc.finish, Nat.zero_add, avgNumeric_eq, sumNumeric]
  | min =>
    simp only [AggAcc.init, aggVals, step_min]
    rw [best_stream keepMin vals, findMin_eq]
    cases filterNonError vals <;> simp [AggAcc.finish, Summary.of_v]
  | max =>
    simp only [AggAcc.init, aggVals, step_max]
    rw [best_stream keepMax vals, findMax_eq]
    cases filterNonError vals <;> simp [AggAcc.finish, Summary.of_v]
  | groupConcat s => simp [Streamed] at hfn
  | sample => simp [Streamed] at hfn


/-! ## SELECT items from known aggregate values -/

/-- The expression `rewriteAggregates` puts in place of an aggregate whose value
is `r` (the match in its `.aggregate` arm). -/
def aggResultExpr : EvalResult → Expr
  | .num n => .numericLit n
  | .bool b => .boolLit b
  | .dec s => .decimalLit s
  | .dbl d => .doubleLit d
  | .term (.iri i) => .iri i
  | .term (.literal l) => .lit l
  | .term _ => .boolLit false
  | .error => .var "_:error:"

theorem rewriteAggregates_aggregate (env : EvalEnv) (g : SolutionGroup) (fn : AggregateFn)
    (d : Bool) (sub : Expr) :
    rewriteAggregates env g (.aggregate fn d sub) = aggResultExpr (evalAggregate env fn d sub g) := by
  simp only [rewriteAggregates]
  generalize evalAggregate env fn d sub g = result
  cases result with
  | term t => cases t <;> rfl
  | _ => rfl

/-- The items of a SELECT clause when the value of each aggregate is given, in
item order. A variable item reads the row; an aggregate item evaluates the
expression `rewriteAggregates` makes of its value, in the row. -/
def itemsPre (env : EvalEnv) : List SelectItem → List EvalResult → Binding → Binding
  | [], _, _ => []
  | .var v :: rest, aggs, row =>
      match row.lookup v with
      | some t => (v, t) :: itemsPre env rest aggs ((v, t) :: row)
      | none => itemsPre env rest aggs row
  | .expr _ a :: rest, r :: aggs, row =>
      match (Expr.evalIn env row (aggResultExpr r)).toTerm? with
      | some t => (a, t) :: itemsPre env rest aggs ((a, t) :: row)
      | none => itemsPre env rest aggs row
  | .expr _ _ :: _, [], _ => []

/-- A SELECT item that is a variable or a non-DISTINCT aggregate. -/
def simpleItem : SelectItem → Bool
  | .var _ => true
  | .expr (.aggregate _ false _) _ => true
  | _ => false

/-- The values of the aggregate items of a group, in item order. -/
def itemAggs (env : EvalEnv) (g : SolutionGroup) : List SelectItem → List EvalResult
  | [] => []
  | .expr (.aggregate fn d sub) _ :: rest => evalAggregate env fn d sub g :: itemAggs env g rest
  | _ :: rest => itemAggs env g rest

/-- The SELECT items of a group are `itemsPre` of the values of its aggregates. -/
theorem evalSelectItemsGroup_pre (env : EvalEnv) (active : Graph) (g : SolutionGroup) :
    ∀ (items : List SelectItem), (∀ it ∈ items, simpleItem it = true) → ∀ row,
    evalSelectItemsGroup env active items g row = itemsPre env items (itemAggs env g items) row := by
  intro items
  induction items with
  | nil => intro _ row; rfl
  | cons it rest ih =>
    intro hs row
    have hrest : ∀ it' ∈ rest, simpleItem it' = true := fun it' h => hs it' (List.mem_cons_of_mem _ h)
    have hit : simpleItem it = true := hs it (List.mem_cons_self ..)
    cases it with
    | var v =>
      simp only [evalSelectItemsGroup, evalSelectItemGroup, itemAggs, itemsPre]
      cases hl : row.lookup v with
      | none => simpa using ih hrest row
      | some t => simpa using ih hrest ((v, t) :: row)
    | expr e a =>
      cases e with
      | aggregate fn d sub =>
        cases d with
        | true => simp [simpleItem] at hit
        | false =>
          simp only [evalSelectItemsGroup, evalSelectItemGroup, itemAggs, itemsPre,
            substituteExistentials, rewriteAggregates_aggregate]
          cases hr : (Expr.evalIn env row (aggResultExpr (evalAggregate env fn false sub g))).toTerm? with
          | none => simpa using ih hrest row
          | some t => simpa using ih hrest ((a, t) :: row)
      | _ => simp [simpleItem] at hit

/-- The row a group contributes before ORDER BY, projection and slicing in
`selectPost`: its items, then the variables of the representative row that no
item names (ORDER BY can still read them). -/
def groupOmegaRow (env : EvalEnv) (active : Graph) (items : List SelectItem)
    (g : SolutionGroup) : Binding :=
  evalSelectItemsGroup env active items g g.representative ++
    g.representative.filter (fun p => !(selectItemVars items).contains p.1)

/-- The same row from the values of the aggregates. -/
def groupedRow (env : EvalEnv) (items : List SelectItem) (aggs : List EvalResult)
    (rep : Binding) : Binding :=
  itemsPre env items aggs rep ++ rep.filter (fun p => !(selectItemVars items).contains p.1)

theorem groupOmegaRow_pre (env : EvalEnv) (active : Graph) (items : List SelectItem)
    (hs : ∀ it ∈ items, simpleItem it = true) (g : SolutionGroup) :
    groupOmegaRow env active items g =
      groupedRow env items (itemAggs env g items) g.representative := by
  simp only [groupOmegaRow, groupedRow, evalSelectItemsGroup_pre env active g items hs]

/-- ORDER BY, projection, DISTINCT or REDUCED, OFFSET and LIMIT of a grouped
SELECT (steps 6 to 9 of `selectPost`). -/
def groupedTail (env : EvalEnv) (active : Graph) (items : List SelectItem)
    (md : SolutionModifier) (omega' : SolutionSeq) : SolutionSeq :=
  match md with
  | { orderBy := ob, distinct := dd, reduced := rr, offset := oo, limit := ll } =>
    match ob with
    | none => finishSelectRows none (projectBinding (selectItemVars items)) dd rr oo ll omega'
    | some o => finishSelectRows
        (some (fun mu1 mu2 => compareOnConditions env active o mu1 mu2))
        (projectBinding (selectItemVars items)) dd rr oo ll omega'

/-- `selectPost` of a SELECT with grouping, no HAVING and no trailing VALUES:
the rows of the groups, then the shared tail. -/
theorem selectPost_grouped (env : EvalEnv) (active : Graph) (dcs : List DatasetClause)
    (pat : QueryPattern) (gb : Option (List GroupCondition)) (md : SolutionModifier)
    (base : Option String) (items : List SelectItem)
    (hgroup : (gb.isSome || selectHasAggregates (.vars items)) = true) (omega0 : SolutionSeq) :
    selectPost env active (.mk (.select (.vars items)) dcs pat gb [] md none base) omega0 =
      groupedTail env active items md
        ((groupWhere env gb omega0).map (groupOmegaRow env active items)) := by
  cases md with
  | mk ob dd rr oo ll =>
    unfold selectPost
    dsimp only
    rw [if_pos hgroup]
    have hrows : ∀ gs : List SolutionGroup,
        (groupedRowsWithValues gb none gs).map (fun gr =>
          evalSelectItemsGroup env active items gr.1 gr.2 ++
            gr.2.filter (fun p => !(selectItemVars items).contains p.1)) =
        gs.map (groupOmegaRow env active items) := by
      intro gs
      simp only [groupedRowsWithValues, groupedRowsWithValuesOn, List.map_map]
      rfl
    simp only [List.isEmpty_nil, if_true, hrows]
    cases ob <;> rfl


/-! ## The grouped SELECTs the id path aggregates -/

/-- The argument of an aggregate the accumulators cover: a variable, or one of
the two spellings of `COUNT(*)` (no variable). -/
def argSpec? (fn : AggregateFn) : Expr → Option (Option VarName)
  | .boolLit true => if fn = .count then some none else none
  | .var w => if w = "*" then (if fn = .count then some none else none) else some (some w)
  | _ => none

/-- (function, argument variable) of a non-DISTINCT aggregate the accumulators
cover; no variable is `COUNT(*)`, in either of its two spellings. -/
def aggSpec? : Expr → Option (AggregateFn × Option VarName)
  | .aggregate fn false sub =>
    if Streamed fn = true then (argSpec? fn sub).map (fun a => (fn, a)) else none
  | _ => none

/-- The aggregate items of a SELECT clause whose items are all variables or such
aggregates, in item order. -/
def itemSpecs? : List SelectItem → Option (List (AggregateFn × Option VarName))
  | [] => some []
  | .var _ :: rest => itemSpecs? rest
  | .expr e _ :: rest =>
    match aggSpec? e, itemSpecs? rest with
    | some a, some r => some (a :: r)
    | _, _ => none

/-- The value of an aggregate over a group, from the accumulator: what the id
path computes. -/
def streamAgg (env : EvalEnv) (g : SolutionGroup) : AggregateFn × Option VarName → EvalResult
  | (_, none) => .num (Int.ofNat g.solutions.length)
  | (fn, some w) =>
    AggAcc.finish fn ((g.solutions.map (fun mu => Summary.of (Expr.evalIn env mu (.var w)))).foldl
      (AggAcc.step fn) (AggAcc.init fn))

theorem argSpec_spec {fn : AggregateFn} {sub : Expr} {arg : Option VarName}
    (h : argSpec? fn sub = some arg) :
    (arg = none → fn = .count ∧ (sub = .boolLit true ∨ sub = .var "*")) ∧
      (∀ w, arg = some w → sub = .var w ∧ w ≠ "*") := by
  unfold argSpec? at h
  split at h
  · split at h
    · rename_i hc
      obtain rfl := Option.some.inj h
      exact ⟨fun _ => ⟨hc, Or.inl rfl⟩, fun w hw => by simp at hw⟩
    · simp at h
  · rename_i w
    split at h
    · rename_i hw
      split at h
      · rename_i hc
        obtain rfl := Option.some.inj h
        subst hw
        exact ⟨fun _ => ⟨hc, Or.inr rfl⟩, fun w hw => by simp at hw⟩
      · simp at h
    · rename_i hw
      obtain rfl := Option.some.inj h
      exact ⟨fun h => by simp at h, fun w' hw' => by
        have : w = w' := by simpa using hw'
        subst this
        exact ⟨rfl, hw⟩⟩
  · simp at h

theorem aggSpec_spec {e : Expr} {fn : AggregateFn} {arg : Option VarName}
    (h : aggSpec? e = some (fn, arg)) :
    ∃ sub, e = .aggregate fn false sub ∧ Streamed fn = true ∧
      (arg = none → fn = .count ∧ (sub = .boolLit true ∨ sub = .var "*")) ∧
      (∀ w, arg = some w → sub = .var w ∧ w ≠ "*") := by
  cases e with
  | aggregate fn' d sub =>
    cases d with
    | true => simp [aggSpec?] at h
    | false =>
      simp only [aggSpec?] at h
      by_cases hs : Streamed fn' = true
      · simp only [hs, if_true] at h
        cases ha : argSpec? fn' sub with
        | none => simp [ha] at h
        | some a =>
          simp [ha] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨sub, rfl, hs, (argSpec_spec ha).1, (argSpec_spec ha).2⟩
      · simp [hs] at h
  | _ => simp [aggSpec?] at h


theorem itemSpecs_simple : ∀ {items : List SelectItem} {specs : List (AggregateFn × Option VarName)},
    itemSpecs? items = some specs → ∀ it ∈ items, simpleItem it = true := by
  intro items
  induction items with
  | nil => intro specs _ it hit; simp at hit
  | cons it0 rest ih =>
    intro specs h it hit
    cases it0 with
    | var v =>
      simp only [itemSpecs?] at h
      rcases List.mem_cons.mp hit with rfl | hmem
      · rfl
      · exact ih h it hmem
    | expr e a =>
      simp only [itemSpecs?] at h
      cases ha : aggSpec? e with
      | none => simp [ha] at h
      | some sp =>
        cases hr : itemSpecs? rest with
        | none => simp [ha, hr] at h
        | some r =>
          obtain ⟨sub, rfl, -, -, -⟩ := aggSpec_spec (e := e) (fn := sp.1) (arg := sp.2) (by simpa using ha)
          rcases List.mem_cons.mp hit with rfl | hmem
          · rfl
          · exact ih hr it hmem

theorem itemAggs_eq_streamAgg (env : EvalEnv) (g : SolutionGroup) :
    ∀ {items : List SelectItem} {specs : List (AggregateFn × Option VarName)},
    itemSpecs? items = some specs → itemAggs env g items = specs.map (streamAgg env g) := by
  intro items
  induction items with
  | nil => intro specs h; simp [itemSpecs?] at h; subst h; rfl
  | cons it0 rest ih =>
    intro specs h
    cases it0 with
    | var v =>
      simp only [itemSpecs?] at h
      simp only [itemAggs]
      exact ih h
    | expr e a =>
      simp only [itemSpecs?] at h
      cases ha : aggSpec? e with
      | none => simp [ha] at h
      | some sp =>
        cases hr : itemSpecs? rest with
        | none => simp [ha, hr] at h
        | some r =>
          simp only [ha, hr] at h
          obtain rfl := Option.some.inj h
          obtain ⟨fn, arg⟩ := sp
          obtain ⟨sub, rfl, hfn, hnone, hsome⟩ := aggSpec_spec ha
          simp only [itemAggs, List.map_cons, ih hr]
          congr 1
          cases arg with
          | none =>
            obtain ⟨rfl, hsub⟩ := hnone rfl
            rcases hsub with rfl | rfl
            · exact (evalAggregate_star env g).1
            · exact (evalAggregate_star env g).2
          | some w =>
            obtain ⟨rfl, hw⟩ := hsome w rfl
            exact evalAggregate_stream env fn hfn w hw g

/-- The pieces of a grouped SELECT whose aggregates the id path computes. -/
structure AggPlan where
  groupVars : List VarName
  /-- no GROUP BY: the whole sequence is one group, also when it is empty -/
  implicit : Bool
  items : List SelectItem
  specs : List (AggregateFn × Option VarName)
  md : SolutionModifier

def groupVarsOf? : List GroupCondition → Option (List VarName)
  | [] => some []
  | .var v :: rest => (groupVarsOf? rest).map (v :: ·)
  | .expr _ _ :: _ => none

/-- A SELECT with items that are variables or non-DISTINCT COUNT, SUM, MIN, MAX
and AVG of a variable (or `COUNT(*)`), GROUP BY variables or none, no HAVING and
no trailing VALUES. -/
def aggPlan? : Query → Option AggPlan
  | .mk (.select (.vars items)) _ _ gb [] md none _ =>
    match itemSpecs? items with
    | none => none
    | some specs =>
      match gb with
      | none => if specs.isEmpty then none else some ⟨[], true, items, specs, md⟩
      | some conds => (groupVarsOf? conds).map fun vs => ⟨vs, false, items, specs, md⟩
  | _ => none

theorem itemSpecs_hasAggregates : ∀ {items : List SelectItem} {specs : List (AggregateFn × Option VarName)},
    itemSpecs? items = some specs → specs.isEmpty = false → selectHasAggregates (.vars items) = true := by
  intro items
  induction items with
  | nil => intro specs h hne; simp [itemSpecs?] at h; subst h; simp at hne
  | cons it0 rest ih =>
    intro specs h hne
    cases it0 with
    | var v =>
      simp only [itemSpecs?] at h
      have := ih h hne
      simp only [selectHasAggregates, List.any_cons] at this ⊢
      simp [this]
    | expr e a =>
      simp only [itemSpecs?] at h
      cases ha : aggSpec? e with
      | none => simp [ha] at h
      | some sp =>
        cases hr : itemSpecs? rest with
        | none => simp [ha, hr] at h
        | some r =>
          obtain ⟨fn, arg⟩ := sp
          obtain ⟨sub, rfl, -, -, -⟩ := aggSpec_spec ha
          simp [selectHasAggregates, List.any_cons, exprHasAggregate]

theorem aggPlan_spec {q : Query} {p : AggPlan} (h : aggPlan? q = some p) :
    ∃ dcs pat gb base,
      q = .mk (.select (.vars p.items)) dcs pat gb [] p.md none base ∧
      itemSpecs? p.items = some p.specs ∧
      (gb.isSome || selectHasAggregates (.vars p.items)) = true := by
  match q, h with
  | .mk (.select (.vars items)) dcs pat gb [] md none base, h =>
    simp only [aggPlan?] at h
    cases hs : itemSpecs? items with
    | none => simp [hs] at h
    | some specs =>
      simp only [hs] at h
      cases gb with
      | none =>
        by_cases he : specs.isEmpty = true
        · simp [he] at h
        · simp only [he, Bool.false_eq_true, if_false] at h
          obtain rfl := Option.some.inj h
          have he' : specs.isEmpty = false := by simpa using he
          exact ⟨dcs, pat, none, base, rfl, hs, by simpa using itemSpecs_hasAggregates hs he'⟩
      | some conds =>
        cases hg : groupVarsOf? conds with
        | none => simp [hg] at h
        | some vs =>
          simp only [hg, Option.map_some] at h
          obtain rfl := Option.some.inj h
          exact ⟨dcs, pat, some conds, base, rfl, hs, by simp⟩

/-- What a query that `aggPlan?` accepts computes: the rows of the groups from
the values of their aggregates (`streamAgg`), then the shared tail. This is the
specification the id path implements; lemma L5k of the end-to-end record says that it
builds the groups, the representative rows and the streams as `groupWhere`
does. -/
theorem selectPost_aggPlan {q : Query} {p : AggPlan} (h : aggPlan? q = some p)
    (env : EvalEnv) (active : Graph) (omega0 : SolutionSeq) :
    selectPost env active q omega0 =
      groupedTail env active p.items p.md
        ((groupWhere env q.groupBy omega0).map
          (fun g => groupedRow env p.items (p.specs.map (streamAgg env g)) g.representative)) := by
  obtain ⟨dcs, pat, gb, base, hq, hs, hgroup⟩ := aggPlan_spec h
  subst hq
  rw [selectPost_grouped env active dcs pat gb p.md base p.items hgroup omega0]
  simp only [Query.groupBy]
  congr 1
  apply List.map_congr_left
  intro g _
  rw [groupOmegaRow_pre env active p.items (itemSpecs_simple hs) g,
    itemAggs_eq_streamAgg env g hs]

#print axioms evalAggregate_stream
#print axioms evalAggregate_star
#print axioms evalSelectItemsGroup_pre
#print axioms selectPost_grouped
#print axioms selectPost_aggPlan
#print axioms varView_ne_error

end L4Factoidal.SPARQL.AggStream
