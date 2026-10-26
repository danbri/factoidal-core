import L4Factoidal.SPARQL.StorePlan

namespace L4Factoidal.SPARQL.StorePlan

open L4Factoidal.RDF L4Factoidal.SPARQL.StoreBackend

/-- The same candidate access paths as `igSearch`, without reversing hash
    buckets. Existence does not depend on their traversal order. Object keys
    with non-structural SPARQL equality still use the broader access path. -/
def indexedExistsCandidates (index : OWL.RL.Index) (bound : PatternBound) : Graph :=
  match bound.s, bound.p, bound.o with
  | some s, some p, _ => index.bySP.getD (s, p) []
  | _, some p, some o =>
      if exactObjectIndexKeySafe o then index.byPO.getD (p, o) []
      else index.byP.getD p []
  | some s, _, _ => index.byS.getD s []
  | _, some p, _ => index.byP.getD p []
  | _, _, some o =>
      if exactObjectIndexKeySafe o then index.byO.getD o [] else index.toGraph
  | _, _, _ => index.toGraph

/-- Stop at the first complete pattern match. A bound candidate alone is
    insufficient: repeated variables and invalid bindings must still fail. -/
def indexedSingleTpExists (index : OWL.RL.Index) (tp : TriplePattern)
    (mu : Binding) : Bool :=
  let bound := patternBoundFor tp mu
  (indexedExistsCandidates index bound).any fun triple =>
    boundMatches bound triple && (tpMatch tp triple mu).isSome

theorem indexedExistsCandidates_any (index : OWL.RL.Index) (bound : PatternBound)
    (test : Triple → Bool) :
    (indexedExistsCandidates index bound).any (fun t => boundMatches bound t && test t)
      = (igSearch index bound).any test := by
  rcases bound with ⟨s, p, o⟩
  cases s <;> cases p <;> cases o <;>
    simp [indexedExistsCandidates, igSearch, tripleMatchesBound,
      OWL.RL.Index.withSubjPred, OWL.RL.Index.withPredObj,
      OWL.RL.Index.withSubj, OWL.RL.Index.withPred, OWL.RL.Index.withObj,
      apply_ite List.any, List.any_filter] <;>
    split <;> simp_all

private theorem any_isSome_eq_not_isEmpty_filterMap (items : List α)
    (f : α → Option β) :
    items.any (fun x => (f x).isSome) = !(items.filterMap f).isEmpty := by
  induction items with
  | nil => rfl
  | cons x xs ih =>
      cases h : f x <;> simp [h, ih]

/-- Exact agreement with the existing indexed matcher, including arbitrary
    indices and bindings. Index completeness is a separate admission invariant. -/
theorem indexedSingleTpExists_eq (index : OWL.RL.Index) (tp : TriplePattern)
    (mu : Binding) :
    indexedSingleTpExists index tp mu
      = !(evalSingleTpBackend tp (.indexed index) mu).isEmpty := by
  rw [indexedSingleTpExists, indexedExistsCandidates_any,
    any_isSome_eq_not_isEmpty_filterMap]
  rfl

/-- A singleton BGP has no planning choice and returns the one-pattern rows. -/
theorem evalBgpBackend_single (tp : TriplePattern) (backend : GraphBackend) :
    evalBgpBackend [tp] backend = evalSingleTpBackend tp backend [] := by
  have concat (rows acc : SolutionSeq) :
      evalBgpConcatMapAcc [] backend 1 rows acc = rows.reverse ++ acc := by
    induction rows generalizing acc with
    | nil => simp [evalBgpConcatMapAcc]
    | cons mu rows ih =>
        simp [evalBgpConcatMapAcc, evalBgpFromMuFuel, ih, List.reverse_cons,
          List.append_assoc]
  simp [evalBgpBackend, evalBgpFromMuFuel, chooseBestTpBackend, concat,
    Binding.empty]

#print axioms indexedSingleTpExists_eq
#print axioms evalBgpBackend_single

end L4Factoidal.SPARQL.StorePlan
