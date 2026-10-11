import L4Factoidal.SPARQL.OrderedSubject

namespace L4Factoidal.SPARQL.OrderedSubject

open L4Factoidal.RDF L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StorePlan L4Factoidal.SPARQL.StoreDataset

theorem binding_subject (plan : Plan) (triple : Triple) :
    (binding plan triple).lookup plan.subjectVar = some triple.s.toTerm := by
  simp [binding, Binding.lookup, Ne.symm plan.distinctVars]

theorem match_binding (plan : Plan) (triple : Triple)
    (predicate : triple.p = plan.predicate) :
    tpMatch plan.pattern triple [] = some (binding plan triple) := by
  simp [tpMatch, Plan.pattern, tryBindSubject, tryBindTerm, Binding.lookup,
    Binding.bind, plan.distinctVars, Ne.symm plan.distinctVars, predicate, binding]

theorem compare_binding (plan : Plan) (env : EvalEnv) (active : Graph)
    (a b : Triple) :
    compareOnConditions env active [plan.condition] (binding plan a) (binding plan b)
      = compareSubjects plan.descending a b := by
  simp only [compareOnConditions, Plan.condition]
  rcases a with ⟨asub, apred, aobj⟩
  rcases b with ⟨bsub, bpred, bobj⟩
  by_cases hd : plan.descending = true <;>
    simp [compareOnCondition, sparqlOrderValue, numericView, substituteExistentials,
      Expr.evalIn, binding_subject, compareSubjects, hd] <;>
    cases asub <;> cases bsub <;>
    simp [Subject.toTerm, binding_subject, sparqlOrder, erRank,
      subjectOrder, termOrder, termRank] <;> (intro hz; exact hz.symm)

theorem detect_query (query : Query) (plan : Plan) (found : detect query = some plan) :
    plan.query = query := by
  unfold detect at found
  split at found <;> try contradiction
  repeat first
    | (split at found <;> try contradiction)
    | (simp only [Option.some.injEq] at found; subst plan)
  all_goals simp_all [Plan.query, Plan.pattern, Plan.condition, beq_iff_eq]
  all_goals rcases found with ⟨_, rfl⟩; simp [Plan.query, Plan.pattern, Plan.condition]

theorem predicate_bucket (source : OWL.RL.Index) (valid : source.Wf graph)
    (predicate : WfIri) (triple : Triple) (member : triple ∈ source.withPred predicate) :
    triple.p = predicate := by
  rw [valid.withPred_eq] at member
  apply Subtype.ext
  simpa [OWL.RL.withPred] using (List.mem_filter.mp member).2

theorem singleton_rows (source : OWL.RL.Index) (valid : source.Wf graph) (plan : Plan) :
    evalSingleTpBackend plan.pattern (.indexed source) [] =
      (source.withPred plan.predicate).map (binding plan) := by
  simp only [evalSingleTpBackend, backendSearch, capsOfBackend, capsOfIndexed,
    patternBoundFor, Plan.pattern, boundSubjectOfPattern, boundPredicateOfPattern,
    boundObjectOfPattern, Binding.lookup, igSearch, tripleMatchesBound]
  have allPred := predicate_bucket source valid plan.predicate
  generalize source.withPred plan.predicate = triples at *
  induction triples with
  | nil => rfl
  | cons triple rest ih =>
      have hp := allPred triple List.mem_cons_self
      have hr : ∀ t ∈ rest, t.p = plan.predicate := fun t h => allPred t (List.mem_cons_of_mem _ h)
      have hm : tpMatch ⟨.var plan.subjectVar, .iri plan.predicate, .var plan.objectVar⟩
          triple [] = some (binding plan triple) := match_binding plan triple hp
      simp [boundMatches, hp, List.filterMap_cons, hm, ih hr]

theorem varsOnly_no_aggregates (selection : SelectClause)
    (valid : variablesOnly selection = true) : selectHasAggregates selection = false := by
  cases selection with
  | all => rfl
  | vars items =>
      simp only [variablesOnly, List.all_eq_true] at valid
      simp only [selectHasAggregates, List.any_eq_false]
      intro item member
      have hi := valid item member
      cases item <;> simp_all

theorem varsOnly_row (env : EvalEnv) (active : Graph) (row : String)
    (items : List SelectItem) (acc : Binding) (ordinal : Nat)
    (valid : variablesOnly (.vars items) = true) :
    evalSelectItemsRowFrom env active row items acc ordinal = acc := by
  induction items generalizing ordinal with
  | nil => rfl
  | cons item items ih =>
      cases item <;> simp_all [variablesOnly, evalSelectItemsRowFrom]

theorem varsOnly_rows (env : EvalEnv) (active : Graph) (items : List SelectItem)
    (rows : SolutionSeq) (ordinal : Nat)
    (valid : variablesOnly (.vars items) = true) :
    numberRows (fun row mu => evalSelectItemsRowFrom env active row items mu 0) rows ordinal = rows := by
  have hf : (fun row mu => evalSelectItemsRowFrom env active row items mu 0) =
      (fun (_ : String) mu => mu) := by
    funext row mu
    exact varsOnly_row env active row items mu 0 valid
  rw [hf]
  induction rows generalizing ordinal with
  | nil => rfl
  | cons row rows ih => simp [numberRows, ih]

theorem selectPost_plan (plan : Plan) (env : EvalEnv) (active : Graph) (rows : SolutionSeq) :
    selectPost env active plan.query rows =
      sliceSolutions plan.offset (some plan.limit)
        ((sortSolutionsFast (compareOnConditions env active [plan.condition]) rows).map
          (project plan.selection)) := by
  have noAgg := varsOnly_no_aggregates plan.selection plan.selectionVars
  cases hs : plan.selection with
  | all =>
      rw [hs] at noAgg
      simp [Plan.query, selectPost, hs, noAgg, finishSelectRows, project,
        stripSyntheticBnodeVars] <;> rfl
  | vars items =>
      rw [hs] at noAgg
      have hv : variablesOnly (.vars items) = true := hs ▸ plan.selectionVars
      simp [Plan.query, selectPost, hs, noAgg, finishSelectRows, project,
        varsOnly_rows _ _ _ _ _ hv] <;> rfl

theorem sorted_bindings (plan : Plan) (env : EvalEnv) (active : Graph) (triples : Graph) :
    ((triples.mergeSort (subjectLe plan.descending)).map (binding plan)) =
      sortSolutionsFast (compareOnConditions env active [plan.condition]) (triples.map (binding plan)) := by
  apply List.map_mergeSort
  intro a _ b _
  simp [subjectLe, compare_binding]

theorem execute_eq_selectPost (ordered : Index source) (valid : source.Wf graph)
    (plan : Plan) (env : EvalEnv) (active : Graph) :
    execute ordered plan =
      selectPost env active plan.query (evalBgpBackend [plan.pattern] (.indexed source)) := by
  rw [evalBgpBackend_single, singleton_rows source valid plan, selectPost_plan,
    ← sorted_bindings, execute_eq_sorted_slice]
  cases ho : plan.offset <;>
    simp [sliceSolutions, List.map_map, List.map_take, List.map_drop, Function.comp_def, ho]

theorem variable_items (items : List SelectItem)
    (valid : variablesOnly (.vars items) = true) :
    items = (selectItemVars items).map SelectItem.var := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      cases item with
      | var name =>
          have ht : variablesOnly (.vars items) = true := by
            simpa [variablesOnly] using valid
          simp only [selectItemVars, List.map_cons]
          exact congrArg (List.cons (.var name)) (ih ht)
      | expr _ _ => simp [variablesOnly] at valid

theorem count_detector_none (plan : Plan) :
    StoreFastPath.detectCountStarSelect plan.selection = none := by
  have hv := plan.selectionVars
  cases hs : plan.selection with
  | all => rfl
  | vars items =>
      rw [hs] at hv
      rw [variable_items items hv]
      cases selectItemVars items with
      | nil => rfl
      | cons name names =>
          cases names <;> rfl

theorem backend_plan (plan : Plan) (env : EvalEnv) (source : OWL.RL.Index) :
    runSelectQueryBackendDataset env plan.query { default := .indexed source, named := [] } =
      some (selectPost env env.activeGraph plan.query
        (evalBgpBackend [plan.pattern] (.indexed source))) := by
  have cg : StoreFastPath.detectStreamingCountGroupByGraph plan.query = none := by
    simp only [StoreFastPath.detectStreamingCountGroupByGraph, Plan.query,
      Query.form, Query.having, Query.postValues, Query.modifier, Query.groupBy, Query.pattern]
    repeat' split
    all_goals simp_all
    repeat' split
    all_goals simp_all
  have cp : StoreFastPath.detectStreamingCountGroupByPredicate plan.query = none := by
    simp only [StoreFastPath.detectStreamingCountGroupByPredicate, Plan.query,
      Query.form, Query.having, Query.postValues, Query.modifier, Query.groupBy, Query.pattern]
    repeat' split
    all_goals simp_all
    repeat' split
    all_goals simp_all
  have cs : StoreFastPath.detectStreamingCountStar plan.query = none := by
    simp [StoreFastPath.detectStreamingCountStar, Plan.query, Query.form, count_detector_none]
  have lim : StoreFastPath.detectLimitSingleTpScoped plan.query = none := by
    simp [StoreFastPath.detectLimitSingleTpScoped, Plan.query,
      Query.form, Query.having, Query.postValues, Query.modifier, Query.groupBy]
  unfold runSelectQueryBackendDataset
  change evalSelectBackendDataset env plan.query _ = _
  simp only [evalSelectBackendDataset, cg, evalSelectBackendOnGraph, cs,
    resolveStreamingCountGroupByPredicate, cp, lim]
  rfl

/-- The complete admitted query returns exactly the existing indexed SELECT
    answer, including projection, tie order and multiplicity. -/
theorem execute_eq_backend (ordered : Index source) (valid : source.Wf graph)
    (query : Query) (plan : Plan) (found : detect query = some plan) (env : EvalEnv) :
    some (execute ordered plan) =
      runSelectQueryBackendDataset env query { default := .indexed source, named := [] } := by
  rw [← detect_query query plan found, backend_plan,
    execute_eq_selectPost ordered valid plan env env.activeGraph]

#print axioms execute_eq_backend

end L4Factoidal.SPARQL.OrderedSubject
