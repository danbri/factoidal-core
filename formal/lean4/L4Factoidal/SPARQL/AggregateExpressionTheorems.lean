import L4Factoidal.SPARQL.Parser

namespace L4Factoidal.SPARQL.AggregateExpression

mutual
/-- Rewriting removes every aggregate at this expression's query scope.
    EXISTS bodies remain independent scopes, as they do in detection. -/
theorem rewritten_aggregateFree (env : EvalEnv) (group : SolutionGroup) (expression : Expr) :
    exprHasAggregate (rewriteAggregates env group expression) = false := by
  cases expression
  case aggregate fn distinct sub =>
    simp only [rewriteAggregates]
    generalize evalAggregate env fn distinct sub group = result
    cases result with
    | term term => cases term <;> rfl
    | _ => rfl
  all_goals simp only [rewriteAggregates, exprHasAggregate]
  all_goals simp only [rewritten_aggregateFree, rewrittenList_aggregateFree,
    rewrittenOpt_aggregateFree, Bool.false_or]

theorem rewrittenList_aggregateFree (env : EvalEnv) (group : SolutionGroup) (expressions : List Expr) :
    exprHasAggregateList (rewriteAggregateList env group expressions) = false := by
  cases expressions with
  | nil => rfl
  | cons expression rest =>
      simp only [rewriteAggregateList, exprHasAggregateList,
        rewritten_aggregateFree, rewrittenList_aggregateFree, Bool.false_or]

theorem rewrittenOpt_aggregateFree (env : EvalEnv) (group : SolutionGroup) (expression : Option Expr) :
    exprHasAggregateOpt (rewriteAggregateOpt env group expression) = false := by
  cases expression with
  | none => rfl
  | some expression =>
      simp only [rewriteAggregateOpt, exprHasAggregateOpt, rewritten_aggregateFree]
end

mutual
/-- Runtime and parser detection agree on every constructor, argument list
    and optional argument. This includes aggregates beneath string functions. -/
theorem detection_agrees (expression : Expr) :
    exprHasAggregate expression = exprHasAggregateFull expression := by
  cases expression <;> simp only [exprHasAggregate, exprHasAggregateFull]
  all_goals simp only [detection_agrees, detectionList_agrees, detectionOpt_agrees]

theorem detectionList_agrees (expressions : List Expr) :
    exprHasAggregateList expressions = exprsHaveAggregate expressions := by
  cases expressions with
  | nil => rfl
  | cons expression rest =>
      simp only [exprHasAggregateList, exprsHaveAggregate, detection_agrees, detectionList_agrees]

theorem detectionOpt_agrees (expression : Option Expr) :
    exprHasAggregateOpt expression = exprOptHasAggregate expression := by
  cases expression <;> rfl
end

/-- Nested COUNT(*) has the expected lexical count for every group. -/
theorem eval_str_count_star (env : EvalEnv) (group : SolutionGroup) :
    evalExprInGroup env group (.str (.aggregate .count false (.boolLit true))) =
      erString (toString (Int.ofNat group.solutions.length)) := by
  rfl

#print axioms rewritten_aggregateFree
#print axioms detection_agrees
#print axioms eval_str_count_star

end L4Factoidal.SPARQL.AggregateExpression
