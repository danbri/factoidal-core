import L4Factoidal.SPARQL.OrderedSubject

namespace L4Factoidal.SPARQL.MetadataCount

open L4Factoidal.RDF L4Factoidal.SPARQL.StorePlan
open L4Factoidal.SPARQL.StoreFastPath

/-- Exact cardinalities available without enumerating triples. Snapshot
    admission supplies source-index well-formedness; ordered arrays retain
    duplicates and their sizes, including zero for a missing predicate. -/
def cardinality? (ordered : OrderedSubject.Index source) (bound : PatternBound) : Option Nat :=
  match bound.s, bound.p, bound.o with
  | none, none, none => some source.all.size
  | none, some predicate, none => some (OrderedSubject.bucket ordered.buckets predicate false).size
  | _, _, _ => none

/-- The same one-time blank-node rewrite as the backend entry point. -/
def backendQuery (query : Query) : Query :=
  .mk query.form query.dataset query.pattern.rewriteBnodes query.groupBy query.having
    query.modifier query.postValues query.base

/-- Reuse the existing streaming-count admission rules and priority. This
    replaces only the physical count, not query parsing or aggregate semantics. -/
def countRows? (ordered : OrderedSubject.Index source) (query : Query) : Option SolutionSeq :=
  -- `text:query` is answered by the reference evaluator, as in
  -- `runSelectQueryBackendDataset` (SPARQL/StoreDataset.lean).
  if query.pattern.mentionsFulltext then none else
  let query := backendQuery query
  match detectStreamingCountGroupByGraph query with
  | some _ => none
  | none => match detectStreamingCountStar query with
    | some (alias, tp, none) =>
        match cardinality? ordered (patternBoundFor tp Binding.empty) with
        | none => none
        | some count =>
            some (sliceSolutions query.modifier.offset query.modifier.limit
              (countStarSolution alias count))
    | _ => none

end L4Factoidal.SPARQL.MetadataCount
