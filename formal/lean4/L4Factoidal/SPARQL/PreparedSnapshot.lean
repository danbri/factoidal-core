/- A read-only default-graph snapshot. Preparation builds the graph index
once; evaluation only reads that value. Storage admission and DLOG replay
remain at the native edge. This type does not promise live-update visibility.

Dataset clauses use the reference evaluator, whose local-dataset policy also
applies to unavailable FROM graphs. No graph is fetched from the network. -/
import L4Factoidal.SPARQL.MetadataCount
import L4Factoidal.SPARQL.Results

namespace L4Factoidal.SPARQL.PreparedSnapshot

open L4Factoidal.RDF L4Factoidal.SPARQL.StoreDataset

structure Snapshot where
  private mk ::
  graph : Graph
  index : OWL.RL.Index
  valid : index.Wf graph
  orderedSubjects : OrderedSubject.Index index

def prepare (graph : Graph) : Snapshot :=
  let index := OWL.RL.Index.ofGraph graph
  ⟨graph, index, OWL.RL.Index.Wf.ofGraph graph, OrderedSubject.prepare index⟩

def Snapshot.dataset (snapshot : Snapshot) : Dataset :=
  { default := snapshot.graph, named := [] }

def Snapshot.backend (snapshot : Snapshot) : DatasetBackend :=
  { default := .indexed snapshot.index, named := [] }

def Snapshot.selectRowsReference (snapshot : Snapshot) (query : Query) (env : EvalEnv) :
    Except String SolutionSeq :=
  match runSelectQueryBackendDataset env query snapshot.backend with
  | none => .error "SELECT evaluation failed"
  | some rows => .ok rows

def Snapshot.selectRows (snapshot : Snapshot) (query : Query) (env : EvalEnv) :
    Except String SolutionSeq :=
  match MetadataCount.countRows? snapshot.orderedSubjects query with
  | some rows => .ok rows
  | none =>
      match OrderedSubject.detect query with
      | some plan => .ok (OrderedSubject.execute snapshot.orderedSubjects plan)
      | none => snapshot.selectRowsReference query env

/-- Complete SELECT/ASK answers, including declared variables and row order.
    The caller supplies a query environment per request; the pinned graph is
    always authoritative for active-graph-dependent expressions. -/
def run (snapshot : Snapshot) (query : Query) (env : EvalEnv := emptyEnv) :
    Except String QueryResult := do
  let env := { env with
    dataset := some snapshot.dataset
    base := query.base.orElse (fun _ => env.base) }
  match query.form with
  | .select _ =>
      if query.modifier.limit == some 0 then
        return .bindings query.projectedVars []
      if !query.dataset.isEmpty then
        let (vars, rows) := evalSelect env snapshot.dataset query
        return .bindings vars rows
      else
        match snapshot.selectRows query env with
        | .error message => .error message
        | .ok rows =>
            return .bindings query.projectedVars rows
  | .ask =>
      if !query.dataset.isEmpty then
        return .boolean (evalAsk env snapshot.dataset query)
      else
        match runAskQueryBackendDataset env query snapshot.backend with
        | none => .error "ASK evaluation failed"
        | some answer => return .boolean answer
  | _ => .error "snapshot sessions support SELECT and ASK only"

end L4Factoidal.SPARQL.PreparedSnapshot
