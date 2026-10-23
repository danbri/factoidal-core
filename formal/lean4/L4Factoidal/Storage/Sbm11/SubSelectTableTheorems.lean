/-
L4Factoidal.Storage.Sbm11.SubSelectTableTheorems — a sub-SELECT as the nested
evaluator runs it (`IdGroup.subSelectM`;
https://github.com/danbri/factoidal/issues/776, lemma L4w of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`subSelectM` has two code paths. A projection of variables and nothing else
(`IdGroup.plainProjection?`) stays on ids: `IdJoin.keepVars`, then
`IdJoin.distinctRows` for DISTINCT. Any other sub-SELECT decodes the rows
(`IdQuery.decodeRowsM`), runs the reference post-processing `selectPost` with
the empty graph as the active graph, and encodes the values of the projected
variables (`IdQuery.valueIdM`). The reference (`IdGroup.Allowed.subSelect`)
is `selectPost` with the active graph of the pattern over an allowed answer
of the WHERE clause.

The reference side:

* `selectPost_active`: `selectPost` reads the active graph only through
  EXISTS; with no EXISTS outside the WHERE clause
  (`Query.expressionsOutsidePatternExistsFree`, which `nestedRefusal?`
  checks) its value does not depend on the active graph.
* `selectPost_plain`: for a projection of variables, `selectPost` is the
  projection of each row (`projectBinding`), then DISTINCT
  (`distinctSolutionsFast`) when the query asks for it.
* `selectPost_dom`: every row of `selectPost` of `SELECT items` binds only
  the variables of `items` (`selectItemVars`).
* `distinctSolutions_keys`: DISTINCT of rows whose `Binding.equiv` is the
  equality of a key keeps, per key, the last row with that key.

The id side:

* `keepVars_spec`: `keepVars` keeps the columns of the kept variables; each
  row is the row with the other pairs removed.
* `distinctRows_spec`: `distinctRows` keeps, per key of all columns, the
  first row with that key (`firstOcc`).
* `distinct_solEquiv`: on a table whose ids decode injectively, the first
  row of each key and the last row of each key decode to the same multiset
  of solution mappings (`firstOcc_perm_lastOcc`, `equiv_decRow`).
* `decodeRowsM_run`: `decodeRowsM` over a store that decodes every id of
  the table gives the rows of the table decoded.

The two code paths:

* `subSelectM_plain`: a projection of variables on ids answers a
  well-formed table whose decoded rows are `SolEquiv` to `selectPost` of the
  decoded input rows, for every active graph.
* `subSelectM_post`: any other sub-SELECT whose projected variables are
  distinct and bind every variable of a row of `selectPost` over the decoded
  rows of the WHERE table (for `SELECT *`: `ScopeTheorems.selectPost_all_keys`
  with `ScopeTheorems.allowed_keys`) refuses with a
  refusal of the query-local vocabulary (a value with a language tag not in
  lower case, a full vocabulary), or answers a well-formed table whose rows
  decode, row for row, to the rows of `selectPost` with the empty graph.

ORDER BY, LIMIT, OFFSET, GROUP BY, HAVING, aggregates and expressions need
no condition here: `IdGroup.Allowed.subSelect` is `selectPost` over any
allowed answer of the WHERE clause, so the order of the input rows (which
a slice without ORDER BY, GROUP_CONCAT and SAMPLE read) is the order the id
path gives. SPARQL 1.1 fixes no order of solutions (section 15.1), so a
LIMIT without ORDER BY may keep another multiset than the reference
evaluator; `Allowed` admits both.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.GraphVarTableTheorems
import L4Factoidal.Storage.Sbm11.IdPostTheorems
import L4Factoidal.SPARQL.QueryTheorems

namespace L4Factoidal.Storage.Sbm11.SubSelect

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.IdPostTheorems (substituteExistentials_existsFree
  substituteExistentialsList_existsFree)

/-! ## `selectPost` and the active graph -/

section active

variable (env : EvalEnv) (a1 a2 : Graph)

theorem compareOnConditions_active :
    ∀ (os : List OrderCondition), os.all OrderCondition.existsFree = true → ∀ (mu1 mu2 : Binding),
      compareOnConditions env a1 os mu1 mu2 = compareOnConditions env a2 os mu1 mu2
  | [], _, _, _ => rfl
  | c :: rest, h, mu1, mu2 => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hc : compareOnCondition env a1 c mu1 mu2 = compareOnCondition env a2 c mu1 mu2 := by
      cases c with
      | asc e =>
        simp only [OrderCondition.existsFree] at h
        simp only [compareOnCondition, substituteExistentials_existsFree _ _ _ e h.1]
      | desc e =>
        simp only [OrderCondition.existsFree] at h
        simp only [compareOnCondition, substituteExistentials_existsFree _ _ _ e h.1]
    simp only [compareOnConditions, hc, compareOnConditions_active rest h.2 mu1 mu2]

theorem havingSatisfies_active :
    ∀ (hv : List Expr), Expr.existsFreeList hv = true → ∀ (g : SolutionGroup),
      havingSatisfies env a1 hv g = havingSatisfies env a2 hv g
  | [], _, _ => rfl
  | c :: rest, h, g => by
    simp only [Expr.existsFreeList, Bool.and_eq_true] at h
    simp only [havingSatisfies, substituteExistentials_existsFree _ _ _ c h.1, havingSatisfies_active rest h.2 g]

theorem evalSelectItemGroup_active (it : SelectItem) (h : it.existsFree = true) (g : SolutionGroup)
    (row : Binding) : evalSelectItemGroup env a1 it g row = evalSelectItemGroup env a2 it g row := by
  cases it with
  | var v => rfl
  | expr e v =>
    simp only [SelectItem.existsFree] at h
    simp only [evalSelectItemGroup, substituteExistentials_existsFree _ _ _ e h]

theorem evalSelectItemsGroup_active :
    ∀ (items : List SelectItem), items.all SelectItem.existsFree = true → ∀ (g : SolutionGroup) (row : Binding),
      evalSelectItemsGroup env a1 items g row = evalSelectItemsGroup env a2 items g row
  | [], _, _, _ => rfl
  | it :: rest, h, g, row => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [evalSelectItemsGroup, evalSelectItemGroup_active env a1 a2 it h.1 g row]
    split
    · next b _ => rw [evalSelectItemsGroup_active rest h.2 g (b :: row)]
    · exact evalSelectItemsGroup_active rest h.2 g row

theorem evalSelectItemsRowFrom_active (row : String) :
    ∀ (items : List SelectItem), items.all SelectItem.existsFree = true → ∀ (acc : Binding) (i : Nat),
      evalSelectItemsRowFrom env a1 row items acc i = evalSelectItemsRowFrom env a2 row items acc i
  | [], _, _, _ => rfl
  | .var _ :: rest, h, acc, i => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [evalSelectItemsRowFrom, evalSelectItemsRowFrom_active row rest h.2 acc (i + 1)]
  | .expr e v :: rest, h, acc, i => by
    simp only [List.all_cons, Bool.and_eq_true, SelectItem.existsFree] at h
    simp only [evalSelectItemsRowFrom, substituteExistentials_existsFree _ _ _ e h.1]
    split
    · next t _ => exact evalSelectItemsRowFrom_active row rest h.2 _ _
    · exact evalSelectItemsRowFrom_active row rest h.2 _ _

/-- **`selectPost` and the active graph.** With no EXISTS outside the WHERE
    clause, `selectPost` gives the same rows for every active graph: the
    active graph is read only by `substituteExistentials`, which is the
    identity on an EXISTS-free expression. -/
theorem selectPost_active (q : Query) (h : q.expressionsOutsidePatternExistsFree = true) (rows : SolutionSeq) :
    selectPost env a1 q rows = selectPost env a2 q rows := by
  obtain ⟨form, dcs, pat, gb, hv, md, pv, b⟩ := q
  obtain ⟨ob, dd, rr, oo, ll⟩ := md
  simp only [Query.expressionsOutsidePatternExistsFree, Query.form, Query.groupBy, Query.having,
    Query.modifier, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hf, _⟩, hh⟩, ho⟩ := h
  have hO : ∀ o, ob = some o → ∀ mu1 mu2,
      compareOnConditions env a1 o mu1 mu2 = compareOnConditions env a2 o mu1 mu2 := by
    intro o e mu1 mu2
    subst e
    exact compareOnConditions_active env a1 a2 o (by simpa using ho) mu1 mu2
  cases form with
  | select sel =>
    have hH := havingSatisfies_active env a1 a2 hv hh
    cases sel with
    | vars items =>
      simp only [QueryForm.existsFree] at hf
      have hG := evalSelectItemsGroup_active env a1 a2 items hf
      have hR : ∀ row, evalSelectItemsRowFrom env a1 row items = evalSelectItemsRowFrom env a2 row items := by
        intro row; funext acc i; exact evalSelectItemsRowFrom_active env a1 a2 row items hf acc i
      cases ob with
      | none => simp only [selectPost, hH, hG, hR]
      | some o =>
        have hO' := hO o rfl
        simp only [selectPost, hH, hG, hR, hO']
    | all =>
      cases ob with
      | none => simp only [selectPost, hH]
      | some o =>
        have hO' := hO o rfl
        simp only [selectPost, hH, hO']
  | construct _ => rfl
  | ask => rfl
  | describe _ => rfl

end active

/-! ## `selectPost` and the dataset of the environment

The nested evaluator runs `selectPost` with the environment of the id path,
which has no dataset (`Harness/Sbm11Query.queryEnv`); the reference runs it
with the environment `evalSelect` builds, which has the query's dataset.
`selectPost` reads the environment through `Expr.evalIn` (which does not
read the dataset, `ExprLocalTheorems.evalIn_agree`), through the aggregates
and GROUP BY keys (which call `Expr.evalIn`), and through
`substituteExistentials` (the identity on an EXISTS-free expression). So two
environments that agree on `ext`, `now` and `base` give the same rows, for
any two active graphs, when no expression outside the WHERE clause has
EXISTS. -/

section agree

open L4Factoidal.Storage.Sbm11.ExprLocalTheorems (EnvAgree evalIn_agree)

theorem evalAggregate_agree {env1 env2 : EvalEnv} (hA : EnvAgree env1 env2) (fn : AggregateFn) (d : Bool)
    (e : Expr) (g : SolutionGroup) : evalAggregate env1 fn d e g = evalAggregate env2 fn d e g := by
  simp only [evalAggregate, evalOverGroup, evalIn_agree hA]

mutual
theorem rewriteAggregates_agree {env1 env2 : EvalEnv} (h : EnvAgree env1 env2) (g : SolutionGroup) :
    (e : Expr) → rewriteAggregates env1 g e = rewriteAggregates env2 g e
  | .existsPat p => rfl
  | .notExistsPat p => rfl
  | .var v => rfl
  | .iri i => rfl
  | .lit l => rfl
  | .boolLit b => rfl
  | .numericLit n => rfl
  | .decimalLit s => rfl
  | .doubleLit s => rfl
  | .bound v => rfl
  | .now => rfl
  | .arith op a b => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b]
  | .unaryMinus a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .unaryPlus a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .compare op a b => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b]
  | .and a b => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b]
  | .or a b => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b]
  | .not a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .isIri a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .isBlank a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .isLiteral a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .isNumeric a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .str a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .lang a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .datatype a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .iriFn a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .hasLang a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .hasLangDir a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .langDir a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .strDt a b => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b]
  | .strLang a b => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b]
  | .strLangDir a b c => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b, rewriteAggregates_agree h g c]
  | .cond c t e => by simp only [rewriteAggregates, rewriteAggregates_agree h g c, rewriteAggregates_agree h g t, rewriteAggregates_agree h g e]
  | .coalesce es => by simp only [rewriteAggregates, rewriteAggregateList_agree h g es]
  | .inList a es => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregateList_agree h g es]
  | .notInList a es => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregateList_agree h g es]
  | .strLen a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .substr a b c => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b, rewriteAggregateOpt_agree h g c]
  | .uCase a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .lCase a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .strStarts a b => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b]
  | .strEnds a b => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b]
  | .contains a b => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b]
  | .strBefore a b => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b]
  | .strAfter a b => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b]
  | .concat es => by simp only [rewriteAggregates, rewriteAggregateList_agree h g es]
  | .encodeForUri a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .replace a b c d => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b, rewriteAggregates_agree h g c, rewriteAggregateOpt_agree h g d]
  | .regex a b c => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b, rewriteAggregateOpt_agree h g c]
  | .abs a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .round a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .ceil a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .floor a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .md5 a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .sha1 a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .sha256 a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .sha384 a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .sha512 a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .year a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .month a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .day a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .hours a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .minutes a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .seconds a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .timezone a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .tz a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .sameTerm a b => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b]
  | .aggregate fn distinct sub => by simp only [rewriteAggregates, evalAggregate_agree h]
  | .functionCall i args => by simp only [rewriteAggregates, rewriteAggregateList_agree h g args]
  | .tripleTerm a b c => by simp only [rewriteAggregates, rewriteAggregates_agree h g a, rewriteAggregates_agree h g b, rewriteAggregates_agree h g c]
  | .ttSubject a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .ttPredicate a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .ttObject a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]
  | .isTriple a => by simp only [rewriteAggregates, rewriteAggregates_agree h g a]

theorem rewriteAggregateList_agree {env1 env2 : EvalEnv} (h : EnvAgree env1 env2) (g : SolutionGroup) :
    (es : List Expr) → rewriteAggregateList env1 g es = rewriteAggregateList env2 g es
  | [] => rfl
  | e :: es => by
    simp only [rewriteAggregateList, rewriteAggregates_agree h g e, rewriteAggregateList_agree h g es]

theorem rewriteAggregateOpt_agree {env1 env2 : EvalEnv} (h : EnvAgree env1 env2) (g : SolutionGroup) :
    (o : Option Expr) → rewriteAggregateOpt env1 g o = rewriteAggregateOpt env2 g o
  | none => rfl
  | some e => by simp only [rewriteAggregateOpt, rewriteAggregates_agree h g e]
end

theorem groupWhere_agree {env1 env2 : EvalEnv} (hA : EnvAgree env1 env2) (gb : Option (List GroupCondition))
    (omega : SolutionSeq) : groupWhere env1 gb omega = groupWhere env2 gb omega := by
  have hc : ∀ gc mu, evalGroupCondition env1 gc mu = evalGroupCondition env2 gc mu := by
    intro gc mu
    cases gc with
    | var v => rfl
    | expr e _ => simp only [evalGroupCondition, evalIn_agree hA]
  have hal : ∀ conds mu, extendWithGroupAliases env1 conds mu = extendWithGroupAliases env2 conds mu := by
    intro conds mu
    simp only [extendWithGroupAliases, evalIn_agree hA]
  cases gb with
  | none => rfl
  | some conds => simp only [groupWhere, groupSolutionsFast, evalGroupKey, hc, hal]

variable {env1 env2 : EvalEnv} (hA : EnvAgree env1 env2) (a1 a2 : Graph)
include hA

theorem compareOnConditions_agree :
    ∀ (os : List OrderCondition), os.all OrderCondition.existsFree = true → ∀ (mu1 mu2 : Binding),
      compareOnConditions env1 a1 os mu1 mu2 = compareOnConditions env2 a2 os mu1 mu2
  | [], _, _, _ => rfl
  | c :: rest, h, mu1, mu2 => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    have hc : compareOnCondition env1 a1 c mu1 mu2 = compareOnCondition env2 a2 c mu1 mu2 := by
      cases c with
      | asc e =>
        simp only [OrderCondition.existsFree] at h
        simp only [compareOnCondition, substituteExistentials_existsFree _ _ _ e h.1, evalIn_agree hA]
      | desc e =>
        simp only [OrderCondition.existsFree] at h
        simp only [compareOnCondition, substituteExistentials_existsFree _ _ _ e h.1, evalIn_agree hA]
    simp only [compareOnConditions, hc, compareOnConditions_agree rest h.2 mu1 mu2]

theorem havingSatisfies_agree :
    ∀ (hv : List Expr), Expr.existsFreeList hv = true → ∀ (g : SolutionGroup),
      havingSatisfies env1 a1 hv g = havingSatisfies env2 a2 hv g
  | [], _, _ => rfl
  | c :: rest, h, g => by
    simp only [Expr.existsFreeList, Bool.and_eq_true] at h
    simp only [havingSatisfies, substituteExistentials_existsFree _ _ _ c h.1, evalExprInGroup,
      rewriteAggregates_agree hA, evalIn_agree hA, havingSatisfies_agree rest h.2 g]

theorem evalSelectItemGroup_agree (it : SelectItem) (h : it.existsFree = true) (g : SolutionGroup)
    (row : Binding) : evalSelectItemGroup env1 a1 it g row = evalSelectItemGroup env2 a2 it g row := by
  cases it with
  | var v => rfl
  | expr e v =>
    simp only [SelectItem.existsFree] at h
    simp only [evalSelectItemGroup, substituteExistentials_existsFree _ _ _ e h, rewriteAggregates_agree hA,
      evalIn_agree hA]

theorem evalSelectItemsGroup_agree :
    ∀ (items : List SelectItem), items.all SelectItem.existsFree = true → ∀ (g : SolutionGroup) (row : Binding),
      evalSelectItemsGroup env1 a1 items g row = evalSelectItemsGroup env2 a2 items g row
  | [], _, _, _ => rfl
  | it :: rest, h, g, row => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [evalSelectItemsGroup, evalSelectItemGroup_agree hA a1 a2 it h.1 g row]
    split
    · next b _ => rw [evalSelectItemsGroup_agree rest h.2 g (b :: row)]
    · exact evalSelectItemsGroup_agree rest h.2 g row

theorem evalSelectItemsRowFrom_agree (row : String) :
    ∀ (items : List SelectItem), items.all SelectItem.existsFree = true → ∀ (acc : Binding) (i : Nat),
      evalSelectItemsRowFrom env1 a1 row items acc i = evalSelectItemsRowFrom env2 a2 row items acc i
  | [], _, _, _ => rfl
  | .var _ :: rest, h, acc, i => by
    simp only [List.all_cons, Bool.and_eq_true] at h
    simp only [evalSelectItemsRowFrom, evalSelectItemsRowFrom_agree row rest h.2 acc (i + 1)]
  | .expr e v :: rest, h, acc, i => by
    simp only [List.all_cons, Bool.and_eq_true, SelectItem.existsFree] at h
    simp only [evalSelectItemsRowFrom, substituteExistentials_existsFree _ _ _ e h.1, evalIn_agree hA]
    split
    · next t _ => exact evalSelectItemsRowFrom_agree row rest h.2 _ _
    · exact evalSelectItemsRowFrom_agree row rest h.2 _ _

/-- **`selectPost` and the environment.** With no EXISTS outside the WHERE
    clause, two environments that agree on `ext`, `now` and `base` (the
    dataset may differ) give `selectPost` the same rows, for any two active
    graphs. -/
theorem selectPost_agree (q : Query) (h : q.expressionsOutsidePatternExistsFree = true) (rows : SolutionSeq) :
    selectPost env1 a1 q rows = selectPost env2 a2 q rows := by
  obtain ⟨form, dcs, pat, gb, hv, md, pv, b⟩ := q
  obtain ⟨ob, dd, rr, oo, ll⟩ := md
  simp only [Query.expressionsOutsidePatternExistsFree, Query.form, Query.groupBy, Query.having,
    Query.modifier, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hf, _⟩, hh⟩, ho⟩ := h
  have hO : ∀ o, ob = some o → ∀ mu1 mu2,
      compareOnConditions env1 a1 o mu1 mu2 = compareOnConditions env2 a2 o mu1 mu2 := by
    intro o e mu1 mu2
    subst e
    exact compareOnConditions_agree hA a1 a2 o (by simpa using ho) mu1 mu2
  have hW := groupWhere_agree hA gb
  cases form with
  | select sel =>
    have hH := havingSatisfies_agree hA a1 a2 hv hh
    cases sel with
    | vars items =>
      simp only [QueryForm.existsFree] at hf
      have hG := evalSelectItemsGroup_agree hA a1 a2 items hf
      have hR : ∀ row, evalSelectItemsRowFrom env1 a1 row items = evalSelectItemsRowFrom env2 a2 row items := by
        intro row; funext acc i; exact evalSelectItemsRowFrom_agree hA a1 a2 row items hf acc i
      cases ob with
      | none => simp only [selectPost, hH, hG, hR, hW]
      | some o =>
        have hO' := hO o rfl
        simp only [selectPost, hH, hG, hR, hO', hW]
    | all =>
      cases ob with
      | none => simp only [selectPost, hH, hW]
      | some o =>
        have hO' := hO o rfl
        simp only [selectPost, hH, hO', hW]
  | construct _ => rfl
  | ask => rfl
  | describe _ => rfl

end agree

/-! ## `selectPost` of a projection of variables, and the variables it binds -/

section plain

open L4Factoidal.Storage.Sbm11.IdGroup (plainProjection?)

/-- The fold of `plainProjection?`: the variables of the items, when every
    item is a variable. -/
theorem fold_vars (F : Option (Array String) → SelectItem → Option (Array String))
    (hv : ∀ acc v, F (some acc) (.var v) = some (acc.push v)) (he : ∀ acc e v, F (some acc) (.expr e v) = none)
    (hn : ∀ it, F none it = none) : ∀ (items : List SelectItem) (acc vs : Array String),
    items.foldl F (some acc) = some vs →
    vs.toList = acc.toList ++ selectItemVars items ∧ ∀ it ∈ items, ∃ v, it = .var v
  | [], acc, vs, h => by
    simp only [List.foldl_nil, Option.some.injEq] at h
    subst h; simp [selectItemVars]
  | it :: rest, acc, vs, h => by
    have hnone : ∀ (l : List SelectItem), l.foldl F none = none := by
      intro l
      induction l with
      | nil => rfl
      | cons it _ ih => simp only [List.foldl_cons, hn, ih]
    cases it with
    | var v =>
      simp only [List.foldl_cons, hv] at h
      obtain ⟨h1, h2⟩ := fold_vars F hv he hn rest (acc.push v) vs h
      refine ⟨by rw [h1]; simp [selectItemVars], fun it hit => ?_⟩
      rcases List.mem_cons.mp hit with rfl | hm
      · exact ⟨v, rfl⟩
      · exact h2 it hm
    | expr e v =>
      simp only [List.foldl_cons, he] at h
      rw [hnone] at h; cases h

theorem evalSelectItemsRowFrom_vars (env : EvalEnv) (a : Graph) (row : String) :
    ∀ (items : List SelectItem), (∀ it ∈ items, ∃ v, it = .var v) → ∀ (acc : Binding) (i : Nat),
      evalSelectItemsRowFrom env a row items acc i = acc
  | [], _, _, _ => rfl
  | it :: rest, h, acc, i => by
    obtain ⟨v, rfl⟩ := h it List.mem_cons_self
    simp only [evalSelectItemsRowFrom]
    exact evalSelectItemsRowFrom_vars env a row rest (fun it' hit => h it' (List.mem_cons_of_mem _ hit)) acc (i + 1)

theorem numberRows_id (f : String → Binding → Binding) (hf : ∀ s mu, f s mu = mu) :
    ∀ (rows : SolutionSeq) (i : Nat), numberRows f rows i = rows
  | [], _ => rfl
  | mu :: rest, i => by simp only [numberRows, hf, numberRows_id f hf rest (i + 1)]

/-- **`selectPost` of a projection of variables.** For a sub-SELECT that
    `plainProjection?` accepts (a list of variables; no GROUP BY, HAVING,
    expression, ORDER BY, OFFSET, LIMIT, REDUCED or trailing VALUES),
    `selectPost` projects each row on the variables, then removes duplicates
    when the query asks for DISTINCT. -/
theorem selectPost_plain (env : EvalEnv) (a : Graph) (q : Query) (vs : Array String) (d : Bool)
    (h : plainProjection? q = some (vs, d)) (rows : SolutionSeq) :
    selectPost env a q rows =
      if d then distinctSolutionsFast (rows.map (projectBinding vs.toList)) else rows.map (projectBinding vs.toList) := by
  obtain ⟨form, dcs, pat, gb, hv, md, pv, b⟩ := q
  obtain ⟨ob, dd, rr, oo, ll⟩ := md
  unfold plainProjection? at h
  split at h
  · next items _ md' _ _ e =>
    simp only [Query.mk.injEq] at e
    obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := e
    split at h
    · next hc =>
      simp at hc
      obtain ⟨⟨⟨ho, hoff⟩, hl⟩, hr⟩ := hc
      subst ho hoff hl hr
      generalize hf : List.foldl _ (some #[]) items = F at h
      cases F with
      | none => cases h
      | some vs' =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨h1, h2⟩ := fold_vars _ (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ => rfl) items #[] vs' hf
        simp only [List.nil_append] at h1
        have hagg : selectHasAggregates (.vars items) = false := by
          simp only [selectHasAggregates, List.any_eq_false]
          intro it hit
          obtain ⟨v, rfl⟩ := h2 it hit
          simp
        have hn : numberRows (fun row mu => evalSelectItemsRowFrom env a row items mu 0) rows 0 = rows :=
          numberRows_id _ (fun s mu => evalSelectItemsRowFrom_vars env a s items h2 mu 0) rows 0
        simp only [selectPost, hagg, Option.isSome_none, Bool.or_false, Bool.false_eq_true, if_false, hn,
          finishSelectRows, sliceSolutions, h1]
    · cases h
  · cases h

/-- Every row of `finishSelectRows` is a projected row. -/
theorem finishSelectRows_mem (order : Option (Binding → Binding → Int)) (project : Binding → Binding)
    (dd rr : Bool) (oo ll : Option Nat) (rows : SolutionSeq) :
    ∀ mu ∈ finishSelectRows order project dd rr oo ll rows, ∃ nu, mu = project nu := by
  intro mu hmu
  unfold finishSelectRows sliceSolutions at hmu
  have hslice : ∀ (L : SolutionSeq), mu ∈ (match ll with
      | none => (match oo with | none => L | some n => L.drop n)
      | some n => (match oo with | none => L | some n => L.drop n).take n) → mu ∈ L := by
    intro L h
    cases ll <;> cases oo <;> simp at h
    all_goals first
      | exact h
      | exact List.mem_of_mem_drop h
      | exact List.mem_of_mem_take h
      | exact List.mem_of_mem_drop (List.mem_of_mem_take h)
  have h1 := hslice _ hmu
  have h2 : mu ∈ (match order with | none => rows | some cmp => sortSolutionsFast cmp rows).map project := by
    split at h1
    · rw [distinctSolutionsFast_eq] at h1
      exact mem_of_mem_distinctSolutions h1
    · split at h1
      · exact h1
      · exact h1
  obtain ⟨nu, _, e⟩ := List.mem_map.mp h2
  exact ⟨nu, e.symm⟩

theorem projectBinding_dom (vars : List VarName) : ∀ (mu : Binding), ∀ p ∈ projectBinding vars mu, p.1 ∈ vars
  | [], p, hp => by simp [projectBinding] at hp
  | (v, t) :: rest, p, hp => by
    simp only [projectBinding] at hp
    split at hp
    · next hc =>
      rcases List.mem_cons.mp hp with rfl | hm
      · simpa using hc
      · exact projectBinding_dom vars rest p hm
    · exact projectBinding_dom vars rest p hp

/-- **The variables of a row of `selectPost`.** Every row of `selectPost` of
    `SELECT items` binds only variables of `items`: the projection is the
    last step before DISTINCT and the slice. -/
theorem selectPost_dom (env : EvalEnv) (a : Graph) (items : List SelectItem) (dcs : List DatasetClause)
    (inner : QueryPattern) (gb : Option (List GroupCondition)) (hv : List Expr) (md : SolutionModifier)
    (pv : Option (List Binding)) (bs : Option String) (rows : SolutionSeq) :
    ∀ mu ∈ selectPost env a (.mk (.select (.vars items)) dcs inner gb hv md pv bs) rows,
      ∀ p ∈ mu, p.1 ∈ selectItemVars items := by
  intro mu hmu p hp
  obtain ⟨ob, dd, rr, oo, ll⟩ := md
  have key : ∃ nu, mu = projectBinding (selectItemVars items) nu := by
    unfold selectPost at hmu
    dsimp only at hmu
    split at hmu
    · split at hmu
      · exact finishSelectRows_mem _ _ _ _ _ _ _ mu hmu
      · exact finishSelectRows_mem _ _ _ _ _ _ _ mu hmu
    · split at hmu
      · exact finishSelectRows_mem _ _ _ _ _ _ _ mu hmu
      · exact finishSelectRows_mem _ _ _ _ _ _ _ mu hmu
  obtain ⟨nu, rfl⟩ := key
  exact projectBinding_dom _ nu p hp

end plain

/-! ## `keepVars`, `distinctRows` and `Table.reorder` -/

section ids

open L4Factoidal.Qlvr (Table gather)
open L4Factoidal.Codec.Zstd (word64)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup decRow RowIds unbound)
open L4Factoidal.Storage.Sbm11.TableTheorems (forIn_range_inv range'_succ_filter id_bind)

theorem map_range_getElem (L : List Nat) : (List.range L.length).map (fun k => L[k]!) = L := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range]
    exact getElem!_pos L k h2

theorem vars_map_range (vars : Array String) : (List.range vars.size).map (fun c => vars[c]!) = vars.toList := by
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    exact getElem!_pos vars k (by simpa using h2)

/-- The columns `keepVars` keeps. -/
def keptCols (t : Table) (keep : String → Bool) : List Nat :=
  (List.range' 0 t.vars.size).filter fun c => keep t.vars[c]!

/-- The table of the columns `C` of `t`. -/
def colsTable (t : Table) (C : List Nat) : Table :=
  { vars := (C.map fun c => t.vars[c]!).toArray, cols := (C.map fun c => t.cols[c]!).toArray, rows := t.rows }

theorem keepVars_eq (t : Table) (keep : String → Bool) : IdJoin.keepVars t keep = colsTable t (keptCols t keep) := by
  unfold IdJoin.keepVars
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [id_bind]
  generalize hF : forIn (m := _root_.Id) (List.range' 0 t.vars.size) ((#[] : Array String), (#[] : Array ByteArray)) _ = F
  have := forIn_range_inv t.vars.size (fun m (s : Array String × Array ByteArray) =>
      s.1.toList = ((List.range' 0 m).filter fun c => keep t.vars[c]!).map (fun c => t.vars[c]!) ∧
      s.2.toList = ((List.range' 0 m).filter fun c => keep t.vars[c]!).map (fun c => t.cols[c]!)) hF
    ⟨by simp, by simp⟩ (by
      intro k s _ ⟨h1, h2⟩
      by_cases hc : keep t.vars[k]! = true
      · refine ⟨(s.1.push t.vars[k]!, s.2.push t.cols[k]!), by simp [hc], ?_, ?_⟩
        · rw [range'_succ_filter, Array.toList_push, h1]; simp [hc]
        · rw [range'_succ_filter, Array.toList_push, h2]; simp [hc]
      · refine ⟨(s.1, s.2), by simp [hc], ?_, ?_⟩
        · rw [range'_succ_filter, h1]; simp [hc]
        · rw [range'_succ_filter, h2]; simp [hc])
  obtain ⟨h1, h2⟩ := this
  show ({ vars := F.run.1, cols := F.run.2, rows := t.rows } : Table) = _
  unfold colsTable keptCols
  rw [← h1, ← h2]

theorem keptCols_lt {t : Table} {keep : String → Bool} {c : Nat} (h : c ∈ keptCols t keep) : c < t.vars.size := by
  unfold keptCols at h
  rw [List.mem_filter, List.mem_range'] at h
  omega

/-- **`keepVars`.** The columns of the kept variables of a well-formed table:
    a well-formed table whose rows are the rows of `t` with the pairs of the
    other variables removed. -/
theorem keepVars_spec (t : Table) (ht : t.WF) (keep : String → Bool) :
    (IdJoin.keepVars t keep).WF ∧ (IdJoin.keepVars t keep).rows = t.rows ∧
      ∀ i, (IdJoin.keepVars t keep).idRow i = (t.idRow i).filter fun p => keep p.1 := by
  rw [keepVars_eq]
  generalize hC : keptCols t keep = C
  have hCl : ∀ c ∈ C, c < t.vars.size := fun c hc => keptCols_lt (hC ▸ hc)
  have hvars : (C.map fun c => t.vars[c]!) = t.vars.toList.filter keep := by
    rw [← hC, keptCols, ← vars_map_range, List.filter_map, List.range_eq_range']
    rfl
  refine ⟨⟨by simp [colsTable], ?_, ?_⟩, rfl, fun i => ?_⟩
  · intro k hk
    simp only [colsTable, List.size_toArray, List.length_map] at hk ⊢
    simp only [List.getElem_toArray, List.getElem_map]
    have hc := hCl C[k] (List.getElem_mem hk)
    rw [getElem!_pos t.cols C[k] (by rw [ht.cols_size]; exact hc)]
    exact ht.col_bytes _ (by rw [ht.cols_size]; exact hc)
  · simp only [colsTable, List.toList_toArray]
    rw [hvars]
    exact ht.nodup.filter _
  · unfold Table.idRow
    have hsz : (colsTable t C).vars.size = C.length := by simp [colsTable]
    have hvv : (colsTable t C).vars = (C.map fun c => t.vars[c]!).toArray := rfl
    rw [hsz, hvv]
    have hat : ∀ k, k < C.length → (colsTable t C).at k i = t.at C[k]! i := by
      intro k hk
      show word64 (C.map fun c => t.cols[c]!).toArray[k]! (8 * i) = word64 t.cols[C[k]!]! (8 * i)
      rw [getElem!_pos _ k (by simpa using hk), getElem!_pos C k hk]
      simp
    have hv : ∀ k, k < C.length → (C.map fun c => t.vars[c]!).toArray[k]! = t.vars[C[k]!]! := by
      intro k hk
      rw [getElem!_pos _ k (by simpa using hk), getElem!_pos C k hk]
      simp
    have e1 : ((List.range C.length).filterMap fun k =>
        if (colsTable t C).at k i == unbound then none
        else some ((C.map fun c => t.vars[c]!).toArray[k]!, (colsTable t C).at k i)) =
        (List.range C.length).filterMap fun k =>
          (fun c => if t.at c i == unbound then none else some (t.vars[c]!, t.at c i)) C[k]! := by
      apply OptJoin.filterMap_congr'
      intro k hk
      rw [List.mem_range] at hk
      simp only [hat k hk, hv k hk]
    have e2 : ∀ (g : Nat → Option (String × UInt64)),
        (List.range C.length).filterMap (fun k => g C[k]!) = C.filterMap g := by
      intro g
      conv => rhs; rw [← map_range_getElem C]
      rw [List.filterMap_map]; rfl
    rw [e1, e2 (fun c => if (t.at c i == unbound) = true then none else some (t.vars[c]!, t.at c i)), ← hC,
      keptCols, List.filterMap_filter,
      List.filter_filterMap, ← List.range_eq_range']
    apply OptJoin.filterMap_congr'
    intro c _
    by_cases hk : keep t.vars[c]! = true
    · rw [if_pos hk]
      by_cases hx : t.at c i = unbound
      · simp [hx]
      · simp [hx, Option.filter, hk]
    · rw [if_neg hk]
      by_cases hx : t.at c i = unbound
      · simp [hx]
      · simp [hx, Option.filter, hk]

/-- `Table.reorder` of a well-formed table by row indices of `t`: a
    well-formed table whose rows are those rows, in that order. -/
theorem reorder_spec (t : Table) (ht : t.WF) (idx : Array Nat) (hidx : ∀ i ∈ idx.toList, i < t.rows) :
    (t.reorder idx).WF ∧ (t.reorder idx).vars = t.vars ∧ (t.reorder idx).idRows = idx.toList.map t.idRow := by
  refine ⟨⟨?_, ?_, ht.nodup⟩, rfl, ?_⟩
  · simp [Table.reorder, ht.cols_size]
  · intro c hc
    simp only [Table.reorder, Array.size_map] at hc
    simp only [Table.reorder, Array.getElem_map]
    have hc' : c < t.vars.size := by rw [← ht.cols_size]; exact hc
    have := (TableTheorems.gather_at t ht c hc' idx hidx).1
    rw [getElem!_pos t.cols c hc] at this
    rw [this]; simp
  · apply List.ext_getElem
    · simp [Table.idRows, Table.reorder]
    · intro k h1 h2
      simp only [Table.idRows, List.getElem_map, List.getElem_range] at h1 ⊢
      simp only [List.length_map, Array.length_toList] at h2
      rw [Array.getElem_toList]
      unfold Table.idRow
      apply OptJoin.filterMap_congr' _ _ _
      intro c hc
      rw [List.mem_range] at hc
      have hw : (t.reorder idx).at c k = t.at c idx[k] := by
        show word64 (t.cols.map (gather · idx))[c]! (8 * k) = _
        have hc' : c < t.cols.size := by rw [ht.cols_size]; exact hc
        rw [getElem!_pos _ c (by simpa using hc'), Array.getElem_map,
          ← getElem!_pos t.cols c hc', TableTheorems.gather_word t ht c hc idx hidx k h2,
          getElem!_pos idx k h2]
      rw [hw]
      rfl

/-- The key of row `i` that `distinctRows` compares: the ids of every
    column, `unbound` included. -/
def keyAt (t : Table) (i : Nat) : List UInt64 := (List.range t.vars.size).map fun c => t.at c i

/-- The rows `0 .. n-1` whose key no earlier row has: the first row of each
    key. -/
def firstOcc {κ : Type} [BEq κ] (key : Nat → κ) (n : Nat) : List Nat :=
  (List.range' 0 n).filter fun i => !((List.range' 0 i).map key).contains (key i)

theorem distinctRows_idx (t : Table) {F : _root_.Id (Std.HashSet (List UInt64) × Array Nat)}
    (hF : forIn (List.range' 0 t.rows) ((∅ : Std.HashSet (List UInt64)), (#[] : Array Nat)) (fun i __s =>
      if (!__s.fst.contains (keyAt t i)) = true then
        pure (ForInStep.yield (__s.fst.insert (keyAt t i), __s.snd.push i))
      else pure (ForInStep.yield (__s.fst, __s.snd))) = F) :
    F.run.2.toList = firstOcc (keyAt t) t.rows := by
  have := forIn_range_inv t.rows (fun m (s : Std.HashSet (List UInt64) × Array Nat) =>
      (∀ k, s.1.contains k = ((List.range' 0 m).map (keyAt t)).contains k) ∧
      s.2.toList = (List.range' 0 m).filter fun i => !((List.range' 0 i).map (keyAt t)).contains (keyAt t i)) hF
    ⟨fun k => by simp, by simp⟩ (by
      intro m s _ ⟨h1, h2⟩
      have hL : ∀ k, ((List.range' 0 (m + 1)).map (keyAt t)).contains k =
          (((List.range' 0 m).map (keyAt t)).contains k || (k == keyAt t m)) := by
        intro k
        rw [List.range'_concat]
        simp only [Nat.zero_add, Nat.one_mul, List.map_append, List.map_cons, List.map_nil, List.contains_append,
          List.contains_cons, List.contains_nil, Bool.or_false]
      by_cases hc : ((List.range' 0 m).map (keyAt t)).contains (keyAt t m) = true
      · refine ⟨(s.1, s.2), ?_, fun k => ?_, ?_⟩
        · simp only [h1, hc, Bool.not_true, Bool.false_eq_true, if_false]; rfl
        · rw [h1 k, hL k]
          cases hk : (k == keyAt t m)
          · simp only [Bool.or_false]
          · have : k = keyAt t m := by simpa using hk
            subst this; simp only [hc, Bool.or_true]
        · rw [range'_succ_filter, h2]
          simp only [hc, Bool.not_true, Bool.false_eq_true, if_false, List.append_nil]
      · have hc' : ((List.range' 0 m).map (keyAt t)).contains (keyAt t m) = false := Bool.eq_false_iff.mpr hc
        clear hc
        refine ⟨(s.1.insert (keyAt t m), s.2.push m), ?_, fun k => ?_, ?_⟩
        · simp only [h1, hc', Bool.not_false, if_true]; rfl
        · rw [Std.HashSet.contains_insert, h1 k, hL k, Bool.or_comm]
          cases hk : (k == keyAt t m)
          · have : (keyAt t m == k) = false := by
              rw [Bool.eq_false_iff]; intro e; rw [beq_iff_eq] at e; subst e; simp at hk
            simp [this]
          · have : (keyAt t m == k) = true := by
              rw [beq_iff_eq] at hk ⊢; exact hk.symm
            simp [this]
        · rw [range'_succ_filter, Array.toList_push, h2]
          simp only [hc', Bool.not_false, if_true])
  exact this.2

/-- **`distinctRows`.** For a well-formed table: a well-formed table whose
    rows are the first row of each key (`firstOcc`), in order. -/
theorem distinctRows_spec (t : Table) (ht : t.WF) :
    (IdJoin.distinctRows t).WF ∧ (IdJoin.distinctRows t).vars = t.vars ∧
      (IdJoin.distinctRows t).idRows = (firstOcc (keyAt t) t.rows).map t.idRow := by
  unfold IdJoin.distinctRows
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  rw [id_bind]
  generalize hF : forIn (m := _root_.Id) (List.range' 0 t.rows) _ _ = F
  have hidx := distinctRows_idx t hF
  have hlt : ∀ i ∈ F.run.2.toList, i < t.rows := by
    intro i hi
    rw [hidx, firstOcc, List.mem_filter, List.mem_range'] at hi
    omega
  obtain ⟨h1, h2, h3⟩ := reorder_spec t ht F.run.2 hlt
  exact ⟨h1, h2, by show (t.reorder F.run.snd).idRows = _; rw [h3, hidx]⟩

end ids

/-! ## DISTINCT: the first row of each key against the last -/

section distinct

open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup decRow RowIds unbound lookup_decRow idLookup_mem)
open L4Factoidal.Storage.Sbm11.TableTheorems (range'_succ_filter)

/-- The rows of `L` whose key no later row of `L` has: the last row of each
    key, the rows `distinctSolutions` keeps. -/
def lastOcc {κ : Type} [BEq κ] (key : Nat → κ) : List Nat → List Nat
  | [] => []
  | i :: rest => if (rest.map key).contains (key i) then lastOcc key rest else i :: lastOcc key rest

variable {κ : Type} [BEq κ] [LawfulBEq κ]

theorem any_congr' {α : Type} {p q : α → Bool} : ∀ (L : List α), (∀ a ∈ L, p a = q a) → L.any p = L.any q
  | [], _ => rfl
  | a :: L, h => by
    simp only [List.any_cons]
    rw [h a List.mem_cons_self, any_congr' L fun b hb => h b (List.mem_cons_of_mem _ hb)]

omit [LawfulBEq κ] in
/-- **DISTINCT by a key.** When `Binding.equiv` of the rows `g i` and `g j`
    is the equality of their keys, `distinctSolutions` keeps the last row of
    each key. -/
theorem distinctSolutions_keys (g : Nat → Binding) (key : Nat → κ) :
    ∀ (L : List Nat), (∀ i ∈ L, ∀ j ∈ L, (g i).equiv (g j) = (key i == key j)) →
      distinctSolutions (L.map g) = (lastOcc key L).map g
  | [], _ => rfl
  | i :: rest, h => by
    have ih := distinctSolutions_keys g key rest fun a ha b hb =>
      h a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
    have hany : (rest.map g).any (fun x => (g i).equiv x) = (rest.map key).contains (key i) := by
      rw [List.any_map, List.contains_eq_any_beq, List.any_map]
      apply any_congr'
      intro j hj
      show (g i).equiv (g j) = (key i == key j)
      exact h i List.mem_cons_self j (List.mem_cons_of_mem _ hj)
    simp only [List.map_cons, distinctSolutions, lastOcc, hany]
    split
    · exact ih
    · rw [ih]; rfl

theorem mem_lastOcc_key (key : Nat → κ) : ∀ (L : List Nat) (k : κ), k ∈ (lastOcc key L).map key ↔ k ∈ L.map key
  | [], _ => by simp [lastOcc]
  | i :: rest, k => by
    simp only [lastOcc]
    split
    · next hc =>
      rw [mem_lastOcc_key key rest k, List.map_cons, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h)
        · exact List.contains_iff_mem.mp hc
        · exact h
    · rw [List.map_cons, List.mem_cons, mem_lastOcc_key key rest k, List.map_cons, List.mem_cons]

theorem lastOcc_nodup (key : Nat → κ) : ∀ (L : List Nat), ((lastOcc key L).map key).Nodup
  | [] => by simp [lastOcc]
  | i :: rest => by
    simp only [lastOcc]
    split
    · exact lastOcc_nodup key rest
    · next hc =>
      rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => hc ?_, lastOcc_nodup key rest⟩
      exact List.contains_iff_mem.mpr ((mem_lastOcc_key key rest _).mp hm)

omit [LawfulBEq κ] in
theorem lastOcc_sub (key : Nat → κ) : ∀ (L : List Nat), ∀ i ∈ lastOcc key L, i ∈ L
  | [], _, h => by simp [lastOcc] at h
  | j :: rest, i, h => by
    simp only [lastOcc] at h
    split at h
    · exact List.mem_cons_of_mem _ (lastOcc_sub key rest i h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (lastOcc_sub key rest i h)

omit [LawfulBEq κ] in
theorem firstOcc_succ (key : Nat → κ) (n : Nat) :
    firstOcc key (n + 1) = firstOcc key n ++
      (if ((List.range' 0 n).map key).contains (key n) then [] else [n]) := by
  unfold firstOcc
  rw [range'_succ_filter]
  cases ((List.range' 0 n).map key).contains (key n) <;> rfl

theorem mem_firstOcc_key (key : Nat → κ) : ∀ (n : Nat) (k : κ),
    k ∈ (firstOcc key n).map key ↔ k ∈ (List.range' 0 n).map key
  | 0, _ => by simp [firstOcc]
  | n + 1, k => by
    rw [firstOcc_succ, List.range'_concat]
    simp only [Nat.zero_add, Nat.one_mul, List.map_append, List.mem_append, mem_firstOcc_key key n k]
    split
    · next hc =>
      simp only [List.map_nil, List.not_mem_nil, or_false, List.map_cons, List.mem_cons]
      constructor
      · exact Or.inl
      · rintro (h | ⟨rfl⟩)
        · exact h
        · exact List.contains_iff_mem.mp hc
    · rfl

omit [LawfulBEq κ] in
theorem firstOcc_lt (key : Nat → κ) (n : Nat) : ∀ i ∈ firstOcc key n, i < n := by
  intro i hi
  unfold firstOcc at hi
  rw [List.mem_filter, List.mem_range'] at hi
  omega

theorem firstOcc_nodup (key : Nat → κ) : ∀ (n : Nat), ((firstOcc key n).map key).Nodup
  | 0 => by simp [firstOcc]
  | n + 1 => by
    rw [firstOcc_succ]
    split
    · simpa using firstOcc_nodup key n
    · next hc =>
      rw [List.map_append, List.nodup_append]
      refine ⟨firstOcc_nodup key n, by simp, ?_⟩
      intro a ha b hb e
      simp only [List.map_cons, List.map_nil, List.mem_singleton] at hb
      subst hb e
      exact hc (List.contains_iff_mem.mpr ((mem_firstOcc_key key n _).mp ha))

/-- The first and the last row of each key are the same keys, up to order. -/
theorem firstOcc_perm_lastOcc (key : Nat → κ) (n : Nat) :
    ((firstOcc key n).map key).Perm ((lastOcc key (List.range' 0 n)).map key) := by
  apply (List.perm_ext_iff_of_nodup (firstOcc_nodup key n) (lastOcc_nodup key _)).mpr
  intro k
  rw [mem_firstOcc_key, mem_lastOcc_key]

/-! ### Rows of ids as keys -/

/-- The row of ids that a key of all columns gives. -/
def rowOfKey (vars : Array String) (k : List UInt64) : IdRow :=
  (List.range vars.size).filterMap fun c => if k[c]! == unbound then none else some (vars[c]!, k[c]!)

theorem keyAt_get (t : Table) (i c : Nat) (hc : c < t.vars.size) : (keyAt t i)[c]! = t.at c i := by
  unfold keyAt
  rw [getElem!_pos _ c (by simpa using hc)]
  simp

theorem idRow_key (t : Table) (i : Nat) : t.idRow i = rowOfKey t.vars (keyAt t i) := by
  unfold Table.idRow rowOfKey
  apply OptJoin.filterMap_congr'
  intro c hc
  rw [List.mem_range] at hc
  rw [keyAt_get t i c hc]

theorem idLookup_isSome {p : String × UInt64} : ∀ {r : IdRow}, p ∈ r → (idLookup p.1 r).isSome = true
  | [], h => by simp at h
  | (w, x) :: rest, h => by
    simp only [idLookup]
    by_cases hw : w = p.1
    · simp [hw]
    · rw [if_neg hw]
      rcases List.mem_cons.mp h with rfl | h
      · exact absurd rfl hw
      · exact idLookup_isSome h

/-- `Binding.subsumes` of decoded rows whose ids `D` decodes injectively
    (`Term.eqb` is id equality): every variable of the first row has the
    same id in the second. -/
theorem subsumes_decRow (D : UInt64 → Term) (okD : UInt64 → Prop)
    (hD : ∀ x y, okD x → okD y → (D x).eqb (D y) = (x == y)) (r s : IdRow) (hr : RowIds okD r)
    (hs : RowIds okD s) :
    Binding.subsumes (decRow D r) (decRow D s) = true ↔ ∀ p ∈ r, idLookup p.1 r = idLookup p.1 s := by
  unfold Binding.subsumes
  rw [List.all_eq_true]
  constructor
  · intro h p hp
    have := h (p.1, D p.2) (List.mem_map.mpr ⟨p, hp, rfl⟩)
    simp only [lookup_decRow] at this
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (idLookup_isSome hp)
    rw [hy] at this ⊢
    cases hz : idLookup p.1 s with
    | none => rw [hz] at this; simp at this
    | some z =>
      rw [hz] at this
      simp only [Option.map_some] at this
      rw [hD y z (hr _ (idLookup_mem hy)) (hs _ (idLookup_mem hz))] at this
      rw [beq_iff_eq.mp this]
  · intro h b hb
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hb
    simp only [lookup_decRow]
    rw [← h p hp]
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (idLookup_isSome hp)
    rw [hy]
    simp only [Option.map_some]
    rw [hD y y (hr _ (idLookup_mem hy)) (hr _ (idLookup_mem hy))]
    simp

/-- `Binding.equiv` of decoded rows is equality of the lookups of ids. -/
theorem equiv_decRow (D : UInt64 → Term) (okD : UInt64 → Prop)
    (hD : ∀ x y, okD x → okD y → (D x).eqb (D y) = (x == y)) (r s : IdRow) (hr : RowIds okD r)
    (hs : RowIds okD s) :
    Binding.equiv (decRow D r) (decRow D s) = true ↔ ∀ v, idLookup v r = idLookup v s := by
  unfold Binding.equiv
  rw [Bool.and_eq_true, subsumes_decRow D okD hD r s hr hs, subsumes_decRow D okD hD s r hs hr]
  constructor
  · rintro ⟨h1, h2⟩ v
    cases e1 : idLookup v r with
    | some y => rw [← e1]; exact h1 (v, y) (idLookup_mem e1)
    | none =>
      cases e2 : idLookup v s with
      | none => rfl
      | some z => rw [← e1, ← e2]; exact (h2 (v, z) (idLookup_mem e2)).symm
  · intro h
    exact ⟨fun p _ => h p.1, fun p _ => (h p.1).symm⟩

/-- Two rows of a table with distinct variables have the same lookups
    exactly when they have the same key. -/
theorem lookups_iff_key (t : Table) (hnd : t.vars.toList.Nodup) (i j : Nat) :
    (∀ v, idLookup v (t.idRow i) = idLookup v (t.idRow j)) ↔ keyAt t i = keyAt t j := by
  simp only [TableTheorems.lookup_idRow t hnd]
  constructor
  · intro h
    unfold keyAt
    apply List.map_congr_left
    intro c hc
    rw [List.mem_range] at hc
    have e := h t.vars[c]!
    have hidx : t.idx t.vars[c]! = some c := by
      cases hx : t.idx t.vars[c]! with
      | none => exact absurd rfl (TableTheorems.idx_none hx c hc)
      | some c' =>
        obtain ⟨h1, h2⟩ := TableTheorems.idx_some hx
        rw [TableTheorems.nodup_idx hnd h1 hc h2]
    unfold Table.lookupAt at e
    rw [hidx] at e
    by_cases hi : t.at c i = unbound
    · by_cases hj : t.at c j = unbound
      · rw [hi, hj]
      · simp [hi, hj] at e
    · by_cases hj : t.at c j = unbound
      · simp [hi, hj] at e
      · simpa [hi, hj] using e
  · intro h v
    unfold Table.lookupAt
    cases hx : t.idx v with
    | none => rfl
    | some c =>
      obtain ⟨hc, _⟩ := TableTheorems.idx_some hx
      have := keyAt_get t i c hc
      rw [h, keyAt_get t j c hc] at this
      dsimp only
      rw [this]

/-- **DISTINCT on ids against the reference.** For a table with distinct
    variables whose ids `D` decodes injectively: the decoded rows of the
    first row of each key (`distinctRows`) and `distinctSolutions` of the
    decoded rows are the same multiset of solution mappings. -/
theorem distinct_solEquiv (t : Table) (hnd : t.vars.toList.Nodup) (D : UInt64 → Term) (okD : UInt64 → Prop)
    (hD : ∀ x y, okD x → okD y → (D x).eqb (D y) = (x == y)) (hok : ∀ i, i < t.rows → RowIds okD (t.idRow i)) :
    IdGroup.SolEquiv (distinctSolutions (t.idRows.map (decRow D)))
      (((firstOcc (keyAt t) t.rows).map t.idRow).map (decRow D)) := by
  let g : Nat → Binding := fun i => decRow D (t.idRow i)
  have hg : t.idRows.map (decRow D) = (List.range' 0 t.rows).map g := by
    simp only [Table.idRows, List.map_map, List.range_eq_range']; rfl
  rw [hg, List.map_map]
  rw [distinctSolutions_keys g (keyAt t) (List.range' 0 t.rows) (by
    intro i hi j hj
    rw [List.mem_range'] at hi hj
    apply Bool.eq_iff_iff.mpr
    rw [equiv_decRow D okD hD _ _ (hok i (by omega)) (hok j (by omega)), lookups_iff_key t hnd, beq_iff_eq])]
  apply IdGroup.SolEquiv.of_perm
  have hgk : ∀ (L : List Nat), L.map g = (L.map (keyAt t)).map fun k => decRow D (rowOfKey t.vars k) := by
    intro L
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    simp only [g, Function.comp_def, idRow_key]
  have : (List.map (decRow D ∘ t.idRow) (firstOcc (keyAt t) t.rows)) = (firstOcc (keyAt t) t.rows).map g := rfl
  rw [this, hgk, hgk]
  exact ((firstOcc_perm_lastOcc (keyAt t) t.rows).map _).symm

end distinct

/-! ## Decoding the rows of a table: `decodeRowsM` -/

section decode

open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup decRow RowIds unbound)
open L4Factoidal.Storage.Sbm11.IdAgg (Cache)

theorem getM_pure (c : Cache UInt64 Term) (f : UInt64 → ExceptT String _root_.Id Term) (D : UInt64 → Term)
    (k : UInt64) (hf : f k = pure (D k)) : c.getM f k = pure (c.getPure D k) := by
  unfold Cache.getM Cache.getPure
  cases c.map.get? k with
  | some v => rfl
  | none => rw [hf]; rfl

/-- A loop in `ExceptT String Id` whose every step yields, followed by `g`:
    a property `R` of the run holds when it holds of `g` on every final value
    with the invariant. -/
theorem forIn_bind_yields {α β γ : Type} (f : α → β → ExceptT String _root_.Id (ForInStep β)) (xs : List α)
    (P : Nat → β → Prop) (b0 : β) (h0 : P 0 b0)
    (hs : ∀ k (hk : k < xs.length) b, P k b → ∃ b', f xs[k] b = pure (.yield b') ∧ P (k + 1) b')
    (g : β → ExceptT String _root_.Id γ) (R : ExceptT String _root_.Id γ → Prop)
    (hg : ∀ b, P xs.length b → R (g b)) : R (forIn xs b0 f >>= g) := by
  obtain ⟨b, hb, hP⟩ := LocalTable.forIn_yields f xs P b0 h0 hs
  rw [hb, pure_bind]
  exact hg b hP

/-- **`decodeRowsM`.** Over a store that decodes every id of the table with
    `D` (`termOf x = pure (D x)`), `decodeRowsM` gives the rows of the table
    decoded with `D`, in order (the cache of decoded ids holds only values of
    `D`). -/
theorem decodeRowsM_run (st : IdQuery.Store _root_.Id) (t : Table) (D : UInt64 → Term)
    (hD : ∀ i, i < t.rows → ∀ c, c < t.vars.size → t.at c i ≠ unbound → st.termOf (t.at c i) = pure (D (t.at c i))) :
    IdQuery.decodeRowsM st t = pure (t.idRows.map (decRow D)) := by
  unfold IdQuery.decodeRowsM
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  let rowUpTo : Nat → Nat → IdRow := fun i n => (List.range' 0 n).filterMap fun c =>
    if t.at c i == unbound then none else some (t.vars[c]!, t.at c i)
  refine forIn_bind_yields _ _
    (fun n (s : Cache UInt64 Term × Array Binding) =>
      Cache.Valid D s.1 ∧ s.2.toList = (List.range' 0 n).map fun i => decRow D (t.idRow i))
    _ ?_ ?_ _ (fun z => z = pure (t.idRows.map (decRow D))) ?_
  · exact ⟨Cache.valid_empty D, by simp⟩
  · intro i hi s ⟨hv, hout⟩
    rw [List.length_range'] at hi
    rw [List.getElem_range', Nat.zero_add, Nat.one_mul]
    refine forIn_bind_yields _ _
      (fun n (r : Cache UInt64 Term × Array (String × Term)) =>
        Cache.Valid D r.1 ∧ r.2.toList = decRow D (rowUpTo i n))
      _ ?_ ?_ _ (fun z => ∃ b' : Cache UInt64 Term × Array Binding, z = pure (ForInStep.yield b') ∧
        Cache.Valid D b'.1 ∧ b'.2.toList = (List.range' 0 (i + 1)).map fun i => decRow D (t.idRow i)) ?_
    · exact ⟨hv, by simp [rowUpTo, decRow]⟩
    · intro c hc r ⟨hr1, hr2⟩
      rw [List.length_range'] at hc
      rw [List.getElem_range', Nat.zero_add, Nat.one_mul]
      have hstep : rowUpTo i (c + 1) = rowUpTo i c ++
          (if t.at c i == unbound then [] else [(t.vars[c]!, t.at c i)]) := by
        simp only [rowUpTo]
        rw [List.range'_concat, List.filterMap_append]
        simp only [Nat.zero_add, Nat.one_mul, List.filterMap_cons, List.filterMap_nil]
        by_cases hx : t.at c i = unbound <;> simp [hx]
      by_cases hx : t.at c i = unbound
      · refine ⟨(r.1, r.2), ?_, hr1, ?_⟩
        · simp [hx]
        · rw [hstep, hr2]; simp [hx]
      · have hne : (t.at c i != unbound) = true := by simpa using hx
        simp only [hne, if_true]
        rw [getM_pure r.1 st.termOf D _ (hD i hi c hc hx)]
        refine ⟨((r.1.getPure D (t.at c i)).2, r.2.push (t.vars[c]!, (r.1.getPure D (t.at c i)).1)), rfl,
          Cache.getPure_valid D r.1 hr1 _, ?_⟩
        rw [Array.toList_push, hr2, hstep, Cache.getPure_fst D r.1 hr1]
        simp [hx, decRow]
    · intro r ⟨hr1, hr2⟩
      refine ⟨(r.1, s.2.push r.2.toList), rfl, hr1, ?_⟩
      rw [Array.toList_push, hout, hr2, List.range'_concat]
      simp only [Nat.zero_add, Nat.one_mul, List.map_append, List.map_cons, List.map_nil, List.length_range']
      congr 2
      simp only [rowUpTo, Table.idRow, List.range_eq_range']
  · intro s ⟨_, hs2⟩
    show pure s.2.toList = _
    rw [hs2, List.length_range', Table.idRows, List.map_map, List.range_eq_range']
    rfl

end decode

/-! ## `subSelectM` -/

section run

open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup decRow RowIds unbound)
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdLeaf (CidOk)
open L4Factoidal.Storage.Sbm11.LocalVocab
open L4Factoidal.Storage.Sbm11.LocalTable (ColsOk CellOk cellOf cellL colsOk_step colsOk_mono colsOk_next
  values_table zip_at zip_notin)
open L4Factoidal.Storage.Sbm11.IdGroup (NCx NSt NM SolEquiv BindEq Pw PermPw)

/-- A solution mapping whose variables are among `vars` is the mapping
    `zipBindings` builds from the lookups of `vars`. -/
theorem zip_lookups (vars : List String) (hnd : vars.Nodup) (mu : Binding) (hdom : ∀ p ∈ mu, p.1 ∈ vars) :
    BindEq mu (zipBindings vars (vars.map mu.lookup) Binding.empty) := by
  intro w
  by_cases hw : w ∈ vars
  · obtain ⟨c, hc, e⟩ := List.getElem_of_mem hw
    rw [zip_at w vars _ Binding.empty hnd c hc e]
    have hcell : cellL (vars.map mu.lookup) c = mu.lookup w := by
      unfold cellL
      rw [List.getElem?_map, List.getElem?_eq_getElem hc, e, Option.map_some]
      cases mu.lookup w <;> rfl
    rw [hcell]
    cases mu.lookup w <;> rfl
  · rw [zip_notin w vars _ Binding.empty hw]
    show mu.lookup w = none
    cases h : mu.lookup w with
    | none => rfl
    | some t =>
      exfalso
      apply hw
      have : ∀ (m : Binding), m.lookup w = some t → (w, t) ∈ m := by
        intro m
        induction m with
        | nil => intro h; cases h
        | cons a rest ih =>
          intro h
          obtain ⟨v, x⟩ := a
          simp only [Binding.lookup] at h
          by_cases hv : v = w
          · subst hv; rw [if_pos rfl] at h; cases h; exact List.mem_cons_self
          · rw [if_neg hv] at h; exact List.mem_cons_of_mem _ (ih h)
      exact hdom (w, t) (this mu h)

theorem inv_congr' {cid : Term → Option UInt64} {s1 s2 : NSt} (h1 : s2.vocab = s1.vocab)
    (h2 : s2.localIdx = s1.localIdx) (h : LocalVocab.Inv cid s1) : LocalVocab.Inv cid s2 := by
  unfold LocalVocab.Inv; rw [h1, h2]; exact h

theorem ends_bindE {α β : Type} {r : ExceptT String _root_.Id (α × NSt)} {k : α × NSt → ExceptT String _root_.Id (β × NSt)}
    {P : α → NSt → Prop} {Q : β → NSt → Prop} (hr : Ends r P) (hk : ∀ a s, P a s → Ends (k (a, s)) Q) :
    Ends (r >>= k) Q := by
  rcases hr with ⟨e, he, hre⟩ | ⟨a, s, he, hP⟩
  · left; exact ⟨e, by rw [he]; rfl, hre⟩
  · rw [he, pure_bind]
    exact hk a s hP

theorem pw_map_self {α : Type} {R : α → α → Prop} (f : α → α) :
    ∀ (L : List α), (∀ a ∈ L, R a (f a)) → Pw R L (L.map f)
  | [], _ => .nil
  | a :: L, h => .cons (h a List.mem_cons_self) (pw_map_self f L fun b hb => h b (List.mem_cons_of_mem _ hb))

section
variable (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)

/-- **A sub-SELECT that is not a projection of variables**, as `subSelectM`
    runs it over a well-formed table `t` whose ids are ids of the state:
    decode the rows, `selectPost` with the empty graph, encode the values of
    the projected variables. When the projected variables are distinct and
    every row of `selectPost` over the decoded rows of `t` binds only them
    (`hdom`; `selectPost_dom` for `SELECT items`,
    `ScopeTheorems.selectPost_all_keys` for `SELECT *`), it refuses with a
    refusal of the query-local vocabulary, or returns a well-formed table
    whose rows decode, with the decoder of the new state, to the rows of
    `selectPost` row for row as solution mappings; the new state keeps the
    invariant and extends the vocabulary. -/
theorem subSelectM_post (cx : NCx _root_.Id) (hid : ∀ t, cx.st.idOf t = pure (cid t))
    (hcid : ∀ c, CidOk dec ok c (cid c)) (hcidok : ∀ t x, cid t = some x → ok x)
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t) (hloc : ∀ x, ok x → tagOf x ≠ tagLocal)
    (hcid0 : ∀ t x, cid t = some x → x ≠ 0) (htermOf : ∀ x, ok x → cx.st.termOf x = pure (dec x))
    (sq : Query) (hpp : IdGroup.plainProjection? sq = none) (hnd : sq.projectedVars.Nodup)
    (t : Table) (nst : NSt) (hi : Inv cid nst)
    (hok : ∀ r ∈ t.idRows, RowIds (okV ok nst.vocab) r)
    (hdom : ∀ mu ∈ selectPost cx.env Graph.empty sq (t.idRows.map (decRow (decV dec nst.vocab))),
      ∀ p ∈ mu, p.1 ∈ sq.projectedVars) :
    Ends ((IdGroup.subSelectM cx sq t).run nst) fun T nst' =>
      T.WF ∧ Pw BindEq (selectPost cx.env Graph.empty sq (t.idRows.map (decRow (decV dec nst.vocab))))
        (T.idRows.map (decRow (decV dec nst'.vocab))) ∧
      (∀ r ∈ T.idRows, RowIds (okV ok nst'.vocab) r) ∧ Inv cid nst' ∧ nst.vocab.toList <+: nst'.vocab.toList := by
  -- the decoded rows
  have hdecode : decodeRowsM (cx.st.withLocal nst.vocab) t = pure (t.idRows.map (decRow (decV dec nst.vocab))) := by
    apply decodeRowsM_run
    intro i hi' c hc hx
    apply termOf_withLocal cx.st cid dec ok htermOf hloc hi
    have hr := hok (t.idRow i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi', rfl⟩)
    exact hr (t.vars[c]!, t.at c i) (TableTheorems.mem_idRow.mpr ⟨c, hc, hx, rfl⟩)
  generalize hout : selectPost cx.env Graph.empty sq (t.idRows.map (decRow (decV dec nst.vocab))) = out
  have hdom' : ∀ mu ∈ out, ∀ p ∈ mu, p.1 ∈ sq.projectedVars := by rw [← hout]; exact hdom
  unfold IdGroup.subSelectM
  rw [hpp]
  simp only []
  unfold IdGroup.localStore IdGroup.liftE
  simp only [StateT.run_bind, StateT.run_get, StateT.run_pure, pure_bind, StateT.run_lift, hdecode, hout,
    Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  -- the encoding loop: the rows of `out` as the cells of a VALUES block
  let vars := sq.projectedVars
  let rowsL : List (List (Option Term)) := out.map fun mu => vars.map mu.lookup
  let rowsV : List (Array (Option Term)) := rowsL.map List.toArray
  have hsz : vars.toArray.size = vars.length := List.size_toArray
  have hcell : ∀ k, k < out.length → ∀ c, c < vars.length →
      cellOf rowsV[k]! c = Binding.lookup vars.toArray[c]! out[k]! := by
    intro k hk c hc
    have hk' : k < rowsV.length := by simpa [rowsV, rowsL] using hk
    rw [getElem!_pos rowsV k hk', getElem!_pos out k hk, getElem!_pos vars.toArray c (by rw [hsz]; exact hc)]
    simp only [rowsV, rowsL, List.getElem_map, cellOf, List.getElem?_toArray, List.getElem?_map,
      List.getElem?_eq_getElem hc, Option.map_some, List.getElem_toArray]
    cases Binding.lookup vars[c] out[k] <;> rfl
  refine ends_bindE (GraphVar.forIn_nm_ends _ out
    (fun i (cols : Array ByteArray) (s : NSt) => Inv cid s ∧ nst.vocab.toList <+: s.vocab.toList ∧
      ColsOk dec ok s.vocab rowsV vars.length i 0 cols) _ nst ?_ ?_) ?_
  · refine ⟨hi, List.prefix_refl _, by simp [vars], fun c' hc' => ⟨[], ?_, by simp, fun j hj => by simp at hj⟩⟩
    rw [getElem!_pos _ c' (by simpa [vars] using hc')]
    rw [Array.getElem_map]; exact TableTheorems.ColHolds.nil _ rfl
  · -- one row
    intro k hk cols s ⟨hs1, hs2, hs3⟩
    refine ends_bind (GraphVar.forIn_nm_ends _ (List.range' 0 vars.toArray.size)
      (fun c (cols : Array ByteArray) (s : NSt) => Inv cid s ∧ nst.vocab.toList <+: s.vocab.toList ∧
        ColsOk dec ok s.vocab rowsV vars.length k c cols) _ s ⟨hs1, hs2, hs3⟩ ?_) ?_
    · intro c hc cols' s' ⟨h1, h2, h3⟩
      rw [List.length_range', hsz] at hc
      rw [List.getElem_range', Nat.zero_add, Nat.one_mul]
      have hce := hcell k hk c hc
      rw [getElem!_pos out k hk] at hce
      split
      · next term e =>
        rw [e] at hce
        simp only [StateT.run_bind, StateT.run_get, pure_bind, StateT.run_lift]
        rcases valueIdM_spec cx.st cid hid dec ok hcid hcidok hcidN hloc hcid0 s'.vocab s'.localIdx h1 term with
          ⟨e', he, hr⟩ | ⟨y, voc', ix', he, g1, g2, g3, g4, g5⟩
        · left; exact ⟨e', by rw [he]; rfl, hr⟩
        · right
          rw [he]
          refine ⟨_, { vocab := voc', localIdx := ix', lines := s'.lines, stats := s'.stats }, rfl,
            _, rfl, g1, h2.trans g2, ?_⟩
          apply colsOk_step dec ok voc' rowsV vars.length k c hc _ (colsOk_mono dec hloc g2 g1.size h3)
          rw [hce]
          exact ⟨g3, g4, g5⟩
      · next e =>
        rw [e] at hce
        right
        refine ⟨_, s', rfl, _, rfl, h1, h2, ?_⟩
        exact colsOk_step dec ok s'.vocab rowsV vars.length k c hc _ h3 _ (by rw [hce]; rfl)
    · intro cols' s' ⟨h1, h2, h3⟩
      rw [List.length_range', hsz] at h3
      exact ends_pure rfl ⟨_, rfl, h1, h2, colsOk_next h3⟩
  · -- the table
    intro cols s ⟨hs1, hs2, hs3⟩
    obtain ⟨nst', hn, hv1, hv2⟩ := LeftJoinTableTheorems.note_run (toString "sub-SELECT: " ++ toString t.rows ++
      toString " rows decoded, reference selectPost: " ++ toString (List.length out) ++ toString " rows encoded") s
    simp only []
    rw [hn, pure_bind]
    have hc : ColsOk dec ok s.vocab (rowsL.map List.toArray) vars.length rowsL.length 0 cols := by
      rw [List.length_map]; exact hs3
    obtain ⟨t1, t2, t3⟩ := values_table dec ok s.vocab vars rowsL hnd cols hc
    have hlen : rowsL.length = out.length := by simp [rowsL]
    rw [hlen] at t1 t2 t3
    refine ends_pure rfl ⟨t1, ?_, ?_, inv_congr' hv1 hv2 hs1, by rw [hv1]; exact hs2⟩
    · rw [hv1]
      refine Pw.trans (R := BindEq) (fun _ _ _ h h' => BindEq.trans h h') ?_ t2
      simp only [evalValues, rowsL, List.map_map]
      exact pw_map_self _ out fun mu hmu => zip_lookups vars hnd mu (hdom' mu hmu)
    · rw [hv1]; exact t3

theorem note_ends (line : String) (s : NSt) :
    Ends ((IdGroup.note line).run s) fun _ s' => s'.vocab = s.vocab ∧ s'.localIdx = s.localIdx := by
  obtain ⟨nst', hn, hv1, hv2⟩ := LeftJoinTableTheorems.note_run line s
  exact ends_pure hn ⟨hv1, hv2⟩

theorem decRow_filter (D : UInt64 → Term) (vs : Array String) :
    ∀ (r : IdRow), decRow D (r.filter fun p => vs.contains p.1) = projectBinding vs.toList (decRow D r)
  | [] => rfl
  | (v, x) :: rest => by
    have ih := decRow_filter D vs rest
    rw [List.filter_cons]
    show _ = (if vs.toList.contains v then _ else _)
    rw [Array.contains_toList]
    by_cases hv : vs.contains v = true
    · rw [if_pos hv, if_pos hv]
      show (v, D x) :: decRow D (rest.filter fun p => vs.contains p.1) = _
      rw [ih]
      rfl
    · rw [if_neg hv, if_neg hv]
      exact ih

/-- **A sub-SELECT that is a projection of variables**, as `subSelectM` runs
    it on ids: `keepVars`, then `distinctRows` for DISTINCT. Over a
    well-formed table whose ids `decV` decodes injectively, the answer is a
    well-formed table whose decoded rows are the same multiset of solution
    mappings as `selectPost` of the decoded rows, for every active graph; the
    vocabulary does not change. -/
theorem subSelectM_plain (cx : NCx _root_.Id) (a : Graph) (sq : Query) (vs : Array String) (d : Bool)
    (hpp : IdGroup.plainProjection? sq = some (vs, d)) (t : Table) (ht : t.WF) (nst : NSt)
    (hi : Inv cid nst) (hok : ∀ r ∈ t.idRows, RowIds (okV ok nst.vocab) r)
    (hD : ∀ x y, okV ok nst.vocab x → okV ok nst.vocab y →
      (decV dec nst.vocab x).eqb (decV dec nst.vocab y) = (x == y)) :
    Ends ((IdGroup.subSelectM cx sq t).run nst) fun T nst' =>
      T.WF ∧ SolEquiv (selectPost cx.env a sq (t.idRows.map (decRow (decV dec nst.vocab))))
        (T.idRows.map (decRow (decV dec nst'.vocab))) ∧
      (∀ r ∈ T.idRows, RowIds (okV ok nst'.vocab) r) ∧ Inv cid nst' ∧ nst.vocab.toList <+: nst'.vocab.toList := by
  let D := decV dec nst.vocab
  let K := IdJoin.keepVars t vs.contains
  obtain ⟨hkwf, hkrows, hkrow⟩ := keepVars_spec t ht vs.contains
  have hKdec : K.idRows.map (decRow D) = (t.idRows.map (decRow D)).map (projectBinding vs.toList) := by
    simp only [K, Table.idRows, List.map_map, hkrows]
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_def, hkrow, decRow_filter]
  have hKok : ∀ r ∈ K.idRows, RowIds (okV ok nst.vocab) r := by
    intro r hr
    simp only [K, Table.idRows, List.mem_map, List.mem_range, hkrows] at hr
    obtain ⟨i, hi', rfl⟩ := hr
    rw [hkrow]
    intro p hp
    exact hok (t.idRow i) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi', rfl⟩) p (List.mem_filter.mp hp).1
  rw [selectPost_plain cx.env a sq vs d hpp]
  unfold IdGroup.subSelectM
  rw [hpp]
  simp only [StateT.run_bind]
  refine ends_bindE (note_ends _ nst) fun _ s ⟨hv1, hv2⟩ => ?_
  cases d with
  | false =>
    refine ends_pure rfl ⟨hkwf, ?_, ?_, inv_congr' hv1 hv2 hi, by rw [hv1]; exact List.prefix_refl _⟩
    · rw [hv1]
      simp only [Bool.false_eq_true, if_false]
      rw [← hKdec]
      exact IdGroup.SolEquiv.refl _
    · rw [hv1]; exact hKok
  | true =>
    obtain ⟨hdwf, hdv, hdrows⟩ := distinctRows_spec K hkwf
    refine ends_pure rfl ⟨hdwf, ?_, ?_, inv_congr' hv1 hv2 hi, by rw [hv1]; exact List.prefix_refl _⟩
    · rw [hv1]
      simp only [if_true]
      rw [← hKdec, distinctSolutionsFast_eq, hdrows]
      exact distinct_solEquiv K hkwf.nodup D (okV ok nst.vocab) hD (fun i hi' => hKok _
        (List.mem_map.mpr ⟨i, List.mem_range.mpr hi', rfl⟩))
    · simp only [if_true]
      rw [hv1, hdrows]
      intro r hr
      obtain ⟨i, hi', rfl⟩ := List.mem_map.mp hr
      exact hKok _ (List.mem_map.mpr ⟨i, List.mem_range.mpr (firstOcc_lt _ _ i hi'), rfl⟩)

end

end run

end L4Factoidal.Storage.Sbm11.SubSelect

#print axioms L4Factoidal.Storage.Sbm11.SubSelect.selectPost_active
#print axioms L4Factoidal.Storage.Sbm11.SubSelect.selectPost_plain
#print axioms L4Factoidal.Storage.Sbm11.SubSelect.selectPost_dom
#print axioms L4Factoidal.Storage.Sbm11.SubSelect.keepVars_spec
#print axioms L4Factoidal.Storage.Sbm11.SubSelect.distinctRows_spec
#print axioms L4Factoidal.Storage.Sbm11.SubSelect.distinct_solEquiv
#print axioms L4Factoidal.Storage.Sbm11.SubSelect.decodeRowsM_run
#print axioms L4Factoidal.Storage.Sbm11.SubSelect.subSelectM_plain
#print axioms L4Factoidal.Storage.Sbm11.SubSelect.subSelectM_post
