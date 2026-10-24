/-
L4Factoidal.Storage.Sbm11.IdPostTheorems — the SBM11 id path's reference
post-processing (https://github.com/danbri/factoidal/issues/823; record:
docs/designissues/2026-10-12-sbm11-stage4.md section 12).

The id path runs the WHERE clause on term ids, decodes the rows, and then
calls the reference evaluator's own post-WHERE functions on that solution
sequence (`IdQuery.runPostM`): `selectPost`, `formHasSolution`,
`formSolutions` with `IdQuery.constructGraphOf`. It also evaluates the
FILTER conjuncts outside `Expr.backendLocal` with `IdQuery.residualHolds`.
The theorems below are the steps of that argument that do not need the
storage:

  * `substituteExistentials_existsFree`: on an EXISTS-free expression,
    `substituteExistentials` returns the expression unchanged, for every
    environment, active graph and solution mapping. So the id path, which
    has no active graph, can pass the empty graph: `residualHolds_eq` is
    the reference FILTER (`QueryPattern.lowerWith`) for every active graph.
  * `evalConstruct_eq`: `evalConstruct` is `constructGraphOf` of
    `formSolutions` of the WHERE solutions, so the id path's CONSTRUCT step
    is the reference's by definition.
  * `formHasSolution_take_one`, `firstRowsOf_ask`: an ASK that
    `firstRowsOf` gives `some n` has `n = 1` and no modifier, and its
    answer on the first solution is its answer on all of them.
  * `formSolutions_take`: a CONSTRUCT that `firstRowsOf` gives `some n`
    reads only the first `n` solutions.
  * `selectPost_take`: the same for a SELECT.

Open (record section 12): that the decoded id rows are the reference's
WHERE solutions (lemma L6a of https://github.com/danbri/factoidal/issues/776),
and that `Expr.evalIn` and the post-WHERE functions read no `EvalEnv.dataset`
(the id path's environment has none; by inspection, only EXISTS reads it,
and `translate` admits no EXISTS outside the WHERE clause).
-/
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.SPARQL.StoreDataset
import L4Factoidal.RDF.GraphSet

namespace L4Factoidal.Storage.Sbm11.IdPostTheorems

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreDataset (askUsesModifiers formHasSolution_no_modifiers)
open L4Factoidal.Storage.Sbm11.IdQuery

mutual
/-- On an EXISTS-free expression (`Expr.existsFree`), `substituteExistentials`
    rebuilds the expression unchanged: every arm but EXISTS and NOT EXISTS
    rebuilds its constructor from its substituted operands. -/
theorem substituteExistentials_existsFree (env : EvalEnv) (active : Graph) (mu : Binding) :
    (e : Expr) → Expr.existsFree e = true → substituteExistentials env active mu e = e
  | .existsPat _, h => by simp [Expr.existsFree] at h
  | .notExistsPat _, h => by simp [Expr.existsFree] at h
  | .var v, _ => by simp only [substituteExistentials]
  | .iri i, _ => by simp only [substituteExistentials]
  | .lit l, _ => by simp only [substituteExistentials]
  | .boolLit b, _ => by simp only [substituteExistentials]
  | .numericLit n, _ => by simp only [substituteExistentials]
  | .decimalLit s, _ => by simp only [substituteExistentials]
  | .doubleLit s, _ => by simp only [substituteExistentials]
  | .bound v, _ => by simp only [substituteExistentials]
  | .now, _ => by simp only [substituteExistentials]
  | .aggregate fn d a, _ => by simp only [substituteExistentials]
  | .unaryMinus a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .unaryPlus a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .not a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .isIri a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .isBlank a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .isLiteral a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .isNumeric a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .str a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .lang a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .datatype a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .iriFn a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .hasLang a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .hasLangDir a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .langDir a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .strLen a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .uCase a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .lCase a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .encodeForUri a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .abs a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .round a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .ceil a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .floor a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .md5 a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .sha1 a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .sha256 a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .sha384 a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .sha512 a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .year a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .month a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .day a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .hours a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .minutes a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .seconds a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .timezone a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .tz a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .ttSubject a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .ttPredicate a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .ttObject a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .isTriple a, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h]
  | .arith op a b, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .compare op a b, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .and a b, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .or a b, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .sameTerm a b, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .strDt a b, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .strLang a b, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .strStarts a b, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .strEnds a b, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .contains a b, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .strBefore a b, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .strAfter a b, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .strLangDir a b c, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1.1, substituteExistentials_existsFree env active mu b h.1.2, substituteExistentials_existsFree env active mu c h.2]
  | .cond a b c, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1.1, substituteExistentials_existsFree env active mu b h.1.2, substituteExistentials_existsFree env active mu c h.2]
  | .tripleTerm a b c, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1.1, substituteExistentials_existsFree env active mu b h.1.2, substituteExistentials_existsFree env active mu c h.2]
  | .coalesce es, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentialsList_existsFree env active mu es h]
  | .concat es, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentialsList_existsFree env active mu es h]
  | .functionCall i es, h => by
    simp only [Expr.existsFree] at h
    simp only [substituteExistentials, substituteExistentialsList_existsFree env active mu es h]
  | .inList a es, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentialsList_existsFree env active mu es h.2]
  | .notInList a es, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentials_existsFree env active mu a h.1, substituteExistentialsList_existsFree env active mu es h.2]
  | .substr a b none, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentialsOpt, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .substr a b (some c), h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentialsOpt, substituteExistentials_existsFree env active mu a h.1.1, substituteExistentials_existsFree env active mu b h.1.2, substituteExistentials_existsFree env active mu c h.2]
  | .regex a b none, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentialsOpt, substituteExistentials_existsFree env active mu a h.1, substituteExistentials_existsFree env active mu b h.2]
  | .regex a b (some c), h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentialsOpt, substituteExistentials_existsFree env active mu a h.1.1, substituteExistentials_existsFree env active mu b h.1.2, substituteExistentials_existsFree env active mu c h.2]
  | .replace a b c none, h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentialsOpt, substituteExistentials_existsFree env active mu a h.1.1, substituteExistentials_existsFree env active mu b h.1.2, substituteExistentials_existsFree env active mu c h.2]
  | .replace a b c (some d), h => by
    simp only [Expr.existsFree, Bool.and_eq_true] at h
    simp only [substituteExistentials, substituteExistentialsOpt, substituteExistentials_existsFree env active mu a h.1.1.1, substituteExistentials_existsFree env active mu b h.1.1.2, substituteExistentials_existsFree env active mu c h.1.2, substituteExistentials_existsFree env active mu d h.2]


/-- The list form of `substituteExistentials_existsFree`. -/
theorem substituteExistentialsList_existsFree (env : EvalEnv) (active : Graph) (mu : Binding) :
    (es : List Expr) → Expr.existsFreeList es = true → substituteExistentialsList env active mu es = es
  | [], _ => by simp only [substituteExistentialsList]
  | e :: es, h => by
    simp only [Expr.existsFreeList, Bool.and_eq_true] at h
    simp only [substituteExistentialsList, substituteExistentials_existsFree env active mu e h.1,
      substituteExistentialsList_existsFree env active mu es h.2]
end

/-- The residual FILTER of the id path is the reference FILTER of
    `QueryPattern.lowerWith`, `ebvOrFalse (Expr.evalIn env mu
    (substituteExistentials env active mu e))`, for every active graph, on an
    EXISTS-free conjunct (`translate` admits no other). -/
theorem residualHolds_eq (env : EvalEnv) (active : Graph) (mu : Binding) (e : Expr)
    (h : Expr.existsFree e = true) :
    residualHolds env e mu = ebvOrFalse (Expr.evalIn env mu (substituteExistentials env active mu e)) := by
  simp only [residualHolds, substituteExistentials_existsFree env _ mu e h]

/-- `evalConstruct` of a query without FROM is `constructGraphOf` of the
    template over `formSolutions` of the WHERE solutions: the two steps the id
    path calls on its decoded solutions (`IdQuery.runPostM`). -/
theorem evalConstruct_eq (env : EvalEnv) (ds : Dataset) (q : Query) (template : List TriplePattern)
    (hd : q.dataset = []) (hf : q.form = .construct template) :
    evalConstruct env ds q =
      constructGraphOf template
        (formSolutions { env with dataset := some ds } ds.default q
          ((q.pattern.rewriteBnodes.lower { env with dataset := some ds }).evalIn ds ds.default)) := by
  obtain ⟨form, dcs, pat, gb, hv, md, pv, b⟩ := q
  simp only [Query.form, Query.dataset] at hf hd
  subst hf hd
  simp [evalConstruct, applyDataset, constructGraphOf, Query.pattern, Query.dataset, Query.form]

/-- An ASK with no modifier that can change its answer is decided by its
    first solution. -/
theorem formHasSolution_take_one (env : EvalEnv) (active : Graph) (q : Query) (omega0 : SolutionSeq)
    (h : askUsesModifiers q = false) :
    formHasSolution env active q (omega0.take 1) = formHasSolution env active q omega0 := by
  rw [formHasSolution_no_modifiers env active q _ h, formHasSolution_no_modifiers env active q _ h]
  cases omega0 <;> simp

/-- `firstRowsOf` gives an ASK `some n` only for `n = 1` and no modifier. -/
theorem firstRowsOf_ask (q : Query) (hf : q.form = .ask) (n : Nat) (h : firstRowsOf q = some n) :
    n = 1 ∧ askUsesModifiers q = false := by
  simp only [firstRowsOf, hf] at h
  simp only [askUsesModifiers]
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    refine ⟨h.symm, ?_⟩
    simpa using hc
  · simp at h

/-- A CONSTRUCT that `firstRowsOf` gives `some n` reads only the first `n`
    WHERE solutions: with no GROUP BY, HAVING, trailing VALUES or ORDER BY,
    `formSolutions` is OFFSET and LIMIT on the solutions in order, and
    `n` is OFFSET + LIMIT. -/
theorem formSolutions_take (env : EvalEnv) (active : Graph) (q : Query) (template : List TriplePattern)
    (hf : q.form = .construct template) (n : Nat) (h : firstRowsOf q = some n) (omega0 : SolutionSeq) :
    formSolutions env active q (omega0.take n) = formSolutions env active q omega0 := by
  obtain ⟨form, dcs, pat, gb, hv, md, pv, b⟩ := q
  simp only [Query.form] at hf
  subst hf
  obtain ⟨ob, dd, rr, oo, ll⟩ := md
  simp only [firstRowsOf, Query.form, Query.modifier, Query.groupBy, Query.having, Query.postValues] at h
  cases gb <;> cases hv <;> cases pv <;> cases ob <;> simp at h
  obtain ⟨l, rfl, rfl⟩ := h
  cases oo <;>
    simp [formSolutions, formRows, sliceSolutions, Query.groupsSolutions, groupsSolutionsOf,
      Query.modifier, Query.postValues, Query.groupBy, Query.having, List.drop_take, List.take_take]

/-- `numberRows` numbers rows by position, so it commutes with a prefix. -/
theorem numberRows_take (f : String → Binding → Binding) :
    ∀ (omega : SolutionSeq) (n i : Nat), numberRows f (omega.take n) i = (numberRows f omega i).take n
  | [], _, _ => by simp [numberRows]
  | _ :: _, 0, _ => by simp [numberRows]
  | mu :: rest, n + 1, i => by
    simp [numberRows, numberRows_take f rest n (i + 1)]

/-- A SELECT that `firstRowsOf` gives `some n` reads only the first `n` WHERE
    solutions: with no grouping, trailing VALUES, ORDER BY, DISTINCT or
    REDUCED, `selectPost` evaluates the SELECT expressions row by row (the
    row's number is its position), projects, and applies OFFSET and LIMIT
    to the rows in order; `n` is OFFSET + LIMIT. -/
theorem selectPost_take (env : EvalEnv) (active : Graph) (q : Query) (sel : SelectClause)
    (hf : q.form = .select sel) (n : Nat) (h : firstRowsOf q = some n) (omega0 : SolutionSeq) :
    selectPost env active q (omega0.take n) = selectPost env active q omega0 := by
  obtain ⟨form, dcs, pat, gb, hv, md, pv, b⟩ := q
  simp only [Query.form] at hf
  subst hf
  obtain ⟨ob, dd, rr, oo, ll⟩ := md
  simp only [firstRowsOf, Query.form, Query.modifier, Query.groupBy, Query.having, Query.postValues] at h
  cases hagg : selectHasAggregates sel <;>
    cases gb <;> cases hv <;> cases pv <;> cases ob <;> cases dd <;> cases rr <;> simp [hagg] at h
  obtain ⟨l, rfl, rfl⟩ := h
  cases sel <;> cases oo <;>
    simp_all [selectPost, finishSelectRows, sliceSolutions, numberRows_take, List.map_take,
      List.drop_take, List.take_take]

#print axioms substituteExistentials_existsFree
#print axioms substituteExistentialsList_existsFree
#print axioms residualHolds_eq
#print axioms evalConstruct_eq

/-- The SBM11 id path's CONSTRUCT graph is a set, for every template and
solution sequence (https://github.com/danbri/factoidal/issues/973): an
instance of `Graph.KeyNodup.graphAddAll`. -/
theorem constructGraphOf_keyNodup (template : List TriplePattern) (solutions : SolutionSeq) :
    (constructGraphOf template solutions).KeyNodup := by
  unfold constructGraphOf
  rw [foldl_add_eq_graphAddAll]
  exact Graph.KeyNodup.graphAddAll _ Graph.keyNodup_nil

#print axioms constructGraphOf_keyNodup
#print axioms formHasSolution_take_one
#print axioms firstRowsOf_ask
#print axioms formSolutions_take
#print axioms numberRows_take
#print axioms selectPost_take

end L4Factoidal.Storage.Sbm11.IdPostTheorems
