/- Snapshot construction retains the admitted graph, in order and with its
multiplicity. This proves the materialisation boundary; it does not assert
a new universal refinement of the backend's entire query evaluator. -/
import L4Factoidal.SPARQL.PreparedSnapshot
import L4Factoidal.SPARQL.MetadataCountTheorems

namespace L4Factoidal.SPARQL.PreparedSnapshot

open L4Factoidal.RDF L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.SPARQL.StoreDataset

theorem prepare_graph (graph : Graph) : (prepare graph).graph = graph := rfl

theorem prepare_backend (graph : Graph) :
    (prepare graph).backend = indexedDatasetBackend { default := graph, named := [] } := rfl

/-- Every snapshot, not only a concrete fixture, materialises the exact graph
    its index was admitted against. No row is reordered or deduplicated. -/
theorem unbound_search_eq_graph (snapshot : Snapshot) :
    backendSearch snapshot.backend.default patternBoundAll = snapshot.graph := by
  simp [Snapshot.backend, backendSearch, capsOfBackend, capsOfIndexed,
    igSearch, patternBoundAll, tripleMatchesBound, boundMatches,
    OWL.RL.Index.toGraph, snapshot.valid.all]

theorem materialise_eq_dataset (snapshot : Snapshot) :
    materialiseDatasetBackend snapshot.backend = snapshot.dataset := by
  simp only [materialiseDatasetBackend, Snapshot.backend, List.filterMap_nil]
  change ({ default := backendSearch snapshot.backend.default patternBoundAll,
            named := [] } : Dataset) = snapshot.dataset
  rw [unbound_search_eq_graph]
  rfl

/-- Metadata counts and ordered physical access exactly replace the prior row evaluator
    for every query and environment. Detection failure keeps that evaluator. -/
theorem selectRows_eq_reference (snapshot : Snapshot) (query : Query) (env : EvalEnv) :
    snapshot.selectRows query env = snapshot.selectRowsReference query env := by
  unfold Snapshot.selectRows
  split
  next rows found =>
    have eq := MetadataCount.countRows_eq_backend snapshot.orderedSubjects snapshot.valid
      query rows found env
    unfold Snapshot.selectRowsReference
    change Except.ok _ = (match runSelectQueryBackendDataset env query
      { default := .indexed snapshot.index, named := [] } with
      | none => Except.error "SELECT evaluation failed"
      | some rows => Except.ok rows)
    rw [← eq]
  next =>
    split
    next plan found =>
      have eq := OrderedSubject.execute_eq_backend snapshot.orderedSubjects snapshot.valid
        query plan found env
      unfold Snapshot.selectRowsReference
      change Except.ok _ = (match runSelectQueryBackendDataset env query
        { default := .indexed snapshot.index, named := [] } with
        | none => Except.error "SELECT evaluation failed"
        | some rows => Except.ok rows)
      rw [← eq]
    next => rfl

/-- Zero rows are observable regardless of grouping, ordering, VALUES,
    slicing offset, dataset clauses or the admitted graph. -/
theorem selectPost_limit_zero (env : EvalEnv) (active : Graph) (query : Query)
    (rows : SolutionSeq) (limit : query.modifier.limit = some 0) :
    selectPost env active query rows = [] := by
  cases query with
  | mk form dataset pattern group having modifier values base =>
      cases modifier with
      | mk order distinct reduced offset count =>
          change count = some 0 at limit
          subst count
          cases form <;> cases order <;> simp [selectPost, finishSelectRows, sliceSolutions]

theorem evalSelect_limit_zero (env : EvalEnv) (dataset : Dataset) (query : Query)
    (selection : SelectClause) (form : query.form = .select selection)
    (limit : query.modifier.limit = some 0) :
    evalSelect env dataset query = (query.projectedVars, []) := by
  unfold evalSelect
  dsimp only
  simp only [form, selectPost_limit_zero _ _ query _ limit]

theorem run_limit_zero (snapshot : Snapshot) (env : EvalEnv) (query : Query)
    (selection : SelectClause) (form : query.form = .select selection)
    (limit : query.modifier.limit = some 0) :
    run snapshot query env =
      .ok (.bindings (evalSelect env snapshot.dataset query).1 []) := by
  rw [evalSelect_limit_zero env snapshot.dataset query selection form limit]
  simp [run, form, limit]
  rfl

#print axioms unbound_search_eq_graph
#print axioms materialise_eq_dataset
#print axioms evalSelect_limit_zero
#print axioms run_limit_zero
#print axioms selectRows_eq_reference

end L4Factoidal.SPARQL.PreparedSnapshot
