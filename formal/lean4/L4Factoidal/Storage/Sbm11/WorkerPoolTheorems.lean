/-
L4Factoidal.Storage.Sbm11.WorkerPoolTheorems — the steps of the SBM11 id
path that issue https://github.com/danbri/factoidal/issues/961 changed for the
per-session worker pool (`Harness/WorkerPool.lean`; record
docs/designissues/2026-10-12-parallel-block-scans.md, stage 1g).

* `mergeJoinParM_eq`: the divided merge join is `Qlvr.mergeJoin` when the
  runner's `Par.mapList` is `fun f xs => pure (xs.map f)` (its contract; the
  native driver runs it on the worker pool) and the join columns are in
  non-decreasing order (the precondition of `mergeJoin` itself). With no
  `mapList` the join runs `ParallelJoin.mapPar`, which is `List.map`
  (`mapPar_eq`).
* `orderRanks_map`: the ranks of an ORDER BY column from the order readings
  (`IdQuery.OrderRead`, made once per value) are the ranks the code before
  issue 961 computed with `sparqlOrderValue` on the values
  (`orderRanksRef`).

The hypotheses are the runner's contract and the order of the join columns;
no hypothesis states a conclusion. Not proved: that the native `mapList`
meets its contract (tested by `tests/sbm11/threads.sh`).

No `sorry`, no user `axiom`, no `native_decide`.
-/
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.Sbm11.ParallelJoinTheorems

namespace L4Factoidal.Storage.Sbm11.IdQuery

open L4Factoidal.Qlvr (Table mergeJoin mergeSortBy)
open L4Factoidal.SPARQL (EvalResult)
open L4Factoidal.Storage.Sbm11.ParallelJoin (mapPar mapPar_eq mergeJoinRanges rangeChunks
  rangePairsOf concatPairs mergeJoinRanges_rangeChunks)

/-! ## The divided merge join -/

theorem mergeJoinParM_eq {m : Type → Type} [Monad m] [LawfulMonad m] (par : Option (Par m))
    (l r : Table) (v : String)
    (hmap : ∀ p, par = some p → ∀ mp, p.mapList = some mp →
      ∀ (xs : List (List Nat)), mp (rangePairsOf l r v) xs = pure (xs.map (rangePairsOf l r v)))
    (hA : ∀ x y, x ≤ y → y < l.rows →
      (l.at ((l.idx v).getD 0) x).toNat ≤ (l.at ((l.idx v).getD 0) y).toNat)
    (hB : ∀ x y, x ≤ y → y < r.rows →
      (r.at ((r.idx v).getD 0) x).toNat ≤ (r.at ((r.idx v).getD 0) y).toNat) :
    mergeJoinParM par l r v = pure (mergeJoin l r v) := by
  have hR : ∀ k, L4Factoidal.Qlvr.joinOutput l r (L4Factoidal.Qlvr.joinVars l r).1
      (L4Factoidal.Qlvr.joinVars l r).2
      (concatPairs ((rangeChunks l.rows k).map (rangePairsOf l r v))).1
      (concatPairs ((rangeChunks l.rows k).map (rangePairsOf l r v))).2 (some v) =
      mergeJoin l r v := fun k => mergeJoinRanges_rangeChunks l r v k hA hB
  cases par with
  | none => rfl
  | some p =>
    unfold mergeJoinParM
    simp only
    split <;> split
    all_goals first
      | rfl
      | (cases hmp : p.mapList with
          | none =>
            simp only [mapPar_eq, pure_bind]
            exact congrArg pure (hR _)
          | some mp =>
            simp only [hmap p rfl mp hmp, ExceptT.lift_pure, pure_bind]
            exact congrArg pure (hR _))

/-! ## The ORDER BY ranks -/

/-- The ranks of an ORDER BY column's distinct values as the code before
    issue 961 computed them: `mergeSortBy` with `sparqlOrderValue` on the
    values, then equal neighbours, equal ranks. -/
def orderRanksRef (vals : Array EvalResult) : Array Nat := Id.run do
  let sorted := mergeSortBy (List.range vals.size).toArray fun a b =>
    L4Factoidal.SPARQL.sparqlOrderValue (vals.getD a .error) (vals.getD b .error) ≤ 0
  let mut rank : Array Nat := Array.replicate vals.size 0
  let mut r := 0
  for j in [0:sorted.size] do
    if j > 0 && L4Factoidal.SPARQL.sparqlOrderValue (vals.getD sorted[j - 1]! .error)
        (vals.getD sorted[j]! .error) != 0 then
      r := r + 1
    rank := rank.set! sorted[j]! r
  return rank

theorem getD_map_of (vals : Array EvalResult) (i : Nat) :
    (vals.map OrderRead.of).getD i errorRead = OrderRead.of (vals.getD i .error) := by
  unfold Array.getD
  by_cases h : i < vals.size
  · simp [h]
  · simp [h, errorRead]

theorem cmp_map_of (vals : Array EvalResult) (a b : Nat) :
    ((vals.map OrderRead.of).getD a errorRead).cmp ((vals.map OrderRead.of).getD b errorRead) =
      L4Factoidal.SPARQL.sparqlOrderValue (vals.getD a .error) (vals.getD b .error) := by
  rw [getD_map_of, getD_map_of, OrderRead.cmp_of]

theorem orderRanks_map (vals : Array EvalResult) :
    orderRanks (vals.map OrderRead.of) = orderRanksRef vals := by
  unfold orderRanks ranksOfSorted sortReads orderRanksRef
  simp only [cmp_map_of, Array.size_map]

#print axioms mergeJoinParM_eq
#print axioms orderRanks_map

end L4Factoidal.Storage.Sbm11.IdQuery
