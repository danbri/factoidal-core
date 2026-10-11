import L4Factoidal.SPARQL.StoreDataset
import Std.Data.HashMap.Lemmas

namespace L4Factoidal.SPARQL.OrderedSubject

open L4Factoidal.RDF L4Factoidal.SPARQL.StoreDataset

/-- Subject order is independent of projection, variable names and environment.
    DESC swaps operands, exactly as the query evaluator does. -/
def compareSubjects (descending : Bool) (a b : Triple) : Int :=
  if descending then subjectOrder b.s a.s else subjectOrder a.s b.s

def subjectLe (descending : Bool) (a b : Triple) : Bool :=
  compareSubjects descending a b ≤ 0

abbrev Buckets := Std.HashMap WfIri (Array Triple × Array Triple)

def bucket (buckets : Buckets) (predicate : WfIri) (descending : Bool) : Array Triple :=
  let pair := buckets.getD predicate (#[], #[])
  if descending then pair.2 else pair.1

/-- Two stable subject orders per predicate. The private constructor retains
    the exact full-sort invariant, including original tie order and duplicates. -/
structure Index (source : OWL.RL.Index) where
  private mk ::
  buckets : Buckets
  valid : ∀ predicate descending,
    (bucket buckets predicate descending).toList =
      (source.withPred predicate).mergeSort (subjectLe descending)

def prepare (source : OWL.RL.Index) : Index source :=
  let buckets := source.byP.map fun _ reversed =>
    let original := reversed.reverse
    ((original.mergeSort (subjectLe false)).toArray,
     (original.mergeSort (subjectLe true)).toArray)
  ⟨buckets, by
    intro predicate descending
    simp only [bucket, buckets, Std.HashMap.getD_map, OWL.RL.Index.withPred,
      Std.HashMap.getD_eq_getD_getElem?]
    cases h : source.byP[predicate]? <;> cases descending <;> simp [h]
  ⟩

def variablesOnly : SelectClause → Bool
  | .all => true
  | .vars items => items.all fun item => match item with
      | .var _ => true
      | .expr _ _ => false

/-- A physical plan admitted only for a complete predicate bucket, a single
    subject sort key and projection without expressions or duplicate removal. -/
structure Plan where
  predicate : WfIri
  subjectVar : VarName
  objectVar : VarName
  distinctVars : subjectVar ≠ objectVar
  selection : SelectClause
  selectionVars : variablesOnly selection = true
  descending : Bool
  offset : Option Nat
  limit : Nat
  base : Option String

def Plan.pattern (plan : Plan) : TriplePattern :=
  ⟨.var plan.subjectVar, .iri plan.predicate, .var plan.objectVar⟩

def Plan.condition (plan : Plan) : OrderCondition :=
  if plan.descending then .desc (.var plan.subjectVar) else .asc (.var plan.subjectVar)

def Plan.query (plan : Plan) : Query :=
  .mk (.select plan.selection) [] (.bgp [plan.pattern]) none []
    { orderBy := some [plan.condition], offset := plan.offset, limit := some plan.limit }
    none plan.base

def detect (query : Query) : Option Plan :=
  match query with
  | .mk (.select selection) [] (.bgp [⟨.var sv, .iri predicate, .var ov⟩]) none []
      ⟨some [condition], false, false, offset, some limit⟩ none base =>
      if hv : sv ≠ ov then
        if hs : variablesOnly selection = true then
          match condition with
          | .asc (.var key) =>
              if key == sv then some ⟨predicate, sv, ov, hv, selection, hs, false, offset, limit, base⟩
              else none
          | .desc (.var key) =>
              if key == sv then some ⟨predicate, sv, ov, hv, selection, hs, true, offset, limit, base⟩
              else none
          | _ => none
        else none
      else none
  | _ => none

/-- The ordinary matcher binds the object last, so its association-list order
    is object then subject. Preserve that exact representation too. -/
def binding (plan : Plan) (triple : Triple) : Binding :=
  [(plan.objectVar, triple.o), (plan.subjectVar, triple.s.toTerm)]

def project (selection : SelectClause) (row : Binding) : Binding :=
  match selection with
  | .all => row.filter fun pair => !isSyntheticBnodeVar pair.1
  | .vars items => projectBinding (selectItemVars items) row

/-- Array extraction reads only the requested interval. No full bucket is
    converted to a list or matched during this query. -/
def execute (ordered : Index source) (plan : Plan) : SolutionSeq :=
  let start := plan.offset.getD 0
  let rows := bucket ordered.buckets plan.predicate plan.descending
  ((rows.extract start (start + plan.limit)).toList).map fun triple =>
    project plan.selection (binding plan triple)

theorem execute_eq_sorted_slice (ordered : Index source) (plan : Plan) :
    execute ordered plan =
      (((source.withPred plan.predicate).mergeSort (subjectLe plan.descending)).drop
        (plan.offset.getD 0) |>.take plan.limit).map
          (fun triple => project plan.selection (binding plan triple)) := by
  simp [execute, Array.toList_extract, List.extract_eq_take_drop, ordered.valid]

end L4Factoidal.SPARQL.OrderedSubject
