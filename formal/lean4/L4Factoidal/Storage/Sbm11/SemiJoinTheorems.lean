/-
L4Factoidal.Storage.Sbm11.SemiJoinTheorems — semi-join reduction: a join's
right input filtered to the rows whose join value is a left value gives the
same join (https://github.com/danbri/factoidal/issues/809; lemma L5h of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

The id path passes the left values of the join variable into the right scan
(sideways information passing); the scan returns the rows of the full scan
whose value is a candidate (`SipScanTheorems.scanFoldSipM_filter`), and the
candidates contain every left value (`IdQuery.sipCands` checks it at run
time). These theorems say that the join is then unchanged:

* over rows of any type (`joinRows`, the inner join pairs; `ljRows`, the left
  outer join): `joinRows_semijoin`, `ljRows_semijoin`;
* over the index arrays the id path computes: `mergeGo_semijoin` (the merge
  loop of `Qlvr.mergeJoin`, join columns in non-decreasing order) and
  `outerPairs_merge_semijoin` (the merge path of `OptJoin.leftOuterJoin`),
  both read back as pairs of rows (`mergeSpec_rows`, `ljSpec_rows`);
* over solution mappings of ids (`OptJoinTheorems.IdRow`) for the SPARQL 1.1
  operators: `idJoin_semijoin` and `idLeftJoin_semijoin` (a right row whose
  value of the join variable is not a candidate is compatible with no left
  row), with `join_decode`: decoding `idJoin` gives SPARQL 1.1 Join (section
  18.5) of the decoded rows, as `OptJoinTheorems.leftJoin_decode` does for
  LeftJoin.

Not covered: the hash join (`Qlvr.hashJoin`, lemma L5b open) and the `Table`
representation (L5a′, L5g″ open): the id path's hash joins over a scan with
candidates are tested (`tests/sbm11/run.sh` part (l), the census, DBpedia
d08), not proved.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.OptJoinTheorems

namespace L4Factoidal.Storage.Sbm11.SemiJoin

open L4Factoidal.Qlvr (mergeGo mergeSpec mergeGo_pairs flatMap_congr')
open L4Factoidal.Storage.Sbm11.OptJoin
open L4Factoidal.SPARQL (Binding SolutionSeq join)
open L4Factoidal.RDF (Term)

/-! ## Over rows -/

/-- The inner join pairs: each left row with each right row of the same key
    that `ok` accepts, in left-then-right order. -/
def joinRows {α β : Type} (kl : α → UInt64) (kr : β → UInt64) (ok : α → β → Bool) (L : List α) (R : List β) :
    List (α × β) :=
  L.flatMap fun l => (R.filter fun r => kl l == kr r && ok l r).map fun r => (l, r)

/-- **Semi-join reduction, inner join.** Filtering the right rows to those
    whose key passes a test that every left key passes does not change the
    join. -/
theorem joinRows_semijoin {α β : Type} (kl : α → UInt64) (kr : β → UInt64) (ok : α → β → Bool)
    (L : List α) (R : List β) (S : UInt64 → Bool) (hS : ∀ l ∈ L, S (kl l) = true) :
    joinRows kl kr ok L (R.filter fun r => S (kr r)) = joinRows kl kr ok L R := by
  unfold joinRows
  apply flatMap_congr'
  intro l hl
  rw [List.filter_filter]
  congr 1
  apply List.filter_congr
  intro r _
  cases he : (kl l == kr r) <;> simp only [Bool.false_and, Bool.true_and]
  · rw [beq_iff_eq] at he
    rw [← he, hS l hl, Bool.and_true]

/-- The left outer join over rows: each left row with the right rows it
    accepts, or alone. -/
def ljRows {α β : Type} (cand : α → β → Bool) (L : List α) (R : List β) : List (α × Option β) :=
  L.flatMap fun l => if (R.filter (cand l)).isEmpty then [(l, none)] else (R.filter (cand l)).map fun r => (l, some r)

/-- **Semi-join reduction, left outer join.** Filtering the right rows by a
    test that every right row a left row accepts passes does not change the
    left outer join: every left row keeps its matches, and a left row with no
    match keeps its row with `none`. -/
theorem ljRows_semijoin {α β : Type} (cand : α → β → Bool) (L : List α) (R : List β) (S : β → Bool)
    (hS : ∀ l ∈ L, ∀ r ∈ R, cand l r = true → S r = true) :
    ljRows cand L (R.filter S) = ljRows cand L R := by
  unfold ljRows
  apply flatMap_congr'
  intro l hl
  have e : (R.filter S).filter (cand l) = R.filter (cand l) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro r hr
    cases hc : cand l r
    · simp
    · simp [hS l hl r hr hc]
  rw [e]

/-! ## Index pairs read back as rows -/

/-- A filter and map of a list, by positions. -/
theorem filter_map_positions {β γ : Type} [Inhabited β] (R : List β) (p : β → Bool) (g : β → γ) :
    ((List.range' 0 R.length).filter (fun j => p R[j]!)).map (fun j => g R[j]!) = (R.filter p).map g := by
  have := filterMap_range' p g R 0 [] rfl
  simp only [List.nil_append] at this
  rw [← this]
  clear this
  induction R with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.filterMap_cons, List.filter_cons]
    cases p a <;> simp [ih]

/-- The merge loop's pairs, read back as rows, are the inner join pairs. -/
theorem mergeSpec_rows {α β : Type} [Inhabited α] [Inhabited β] (kl : α → UInt64) (kr : β → UInt64)
    (ok : α → β → Bool) (L : List α) (R : List β) :
    (mergeSpec (fun x => kl L[x]!) (fun y => kr R[y]!) (fun x y => ok L[x]! R[y]!) L.length R.length 0 0).map
      (fun p => (L[p.1]!, R[p.2]!)) = joinRows kl kr ok L R := by
  unfold mergeSpec joinRows
  rw [List.map_flatMap, Nat.sub_zero, Nat.sub_zero]
  rw [flatMap_range' (fun l => (R.filter fun r => kl l == kr r && ok l r).map fun r => (l, r)) L 0 [] rfl]
  apply flatMap_congr'
  intro x _
  simp only [List.nil_append, List.map_map]
  rw [← filter_map_positions R (fun r => kl L[x]! == kr r && ok L[x]! r) (fun r => (L[x]!, r))]
  rfl

/-- The left outer join over indices (`OptJoinTheorems.ljSpec`), read back as
    rows, is `ljRows`. -/
theorem ljSpec_rows {α β : Type} [Inhabited α] [Inhabited β] (cand : α → β → Bool) (L : List α) (R : List β) :
    (ljSpec L.length R.length (fun x y => cand L[x]! R[y]!)).map (fun p => (L[p.1]!, p.2.map (R[·]!))) =
      ljRows cand L R := by
  unfold ljSpec ljFrom ljRows
  rw [List.map_flatMap, Nat.sub_zero]
  rw [flatMap_range' (fun l => if (R.filter (cand l)).isEmpty then [(l, none)] else
    (R.filter (cand l)).map fun r => (l, some r)) L 0 [] rfl]
  apply flatMap_congr'
  intro x _
  simp only [List.nil_append]
  have hrows : (rowsOf R.length (fun x y => cand L[x]! R[y]!) x).map (fun j => R[j]!) = R.filter (cand L[x]!) := by
    unfold rowsOf
    rw [List.range_eq_range']
    show ((List.range' 0 R.length).filter (fun j => cand L[x]! R[j]!)).map (fun j => R[j]!) = _
    have := filter_map_positions R (cand L[x]!) (fun r => r)
    simpa using this
  unfold ljRow
  by_cases he : (rowsOf R.length (fun x y => cand L[x]! R[y]!) x).isEmpty = true
  · have he' : (R.filter (cand L[x]!)).isEmpty = true := by
      rw [← hrows]; simpa using he
    rw [if_pos he, if_pos he']
    rfl
  · have he' : (R.filter (cand L[x]!)).isEmpty = false := by
      rw [← hrows]; simpa using he
    rw [if_neg he, if_neg (by rw [he']; exact Bool.false_ne_true), ← hrows, List.map_map, List.map_map]
    rfl

theorem pairwise_index {β : Type} [Inhabited β] (k : β → UInt64) (R : List β)
    (h : R.Pairwise fun a b => (k a).toNat ≤ (k b).toNat) :
    ∀ x y, x ≤ y → y < R.length → (k R[x]!).toNat ≤ (k R[y]!).toNat := by
  intro x y hxy hy
  rw [getElem!_pos R x (by omega), getElem!_pos R y hy]
  rcases Nat.eq_or_lt_of_le hxy with e | l
  · subst e; exact Nat.le_refl _
  · exact (List.pairwise_iff_getElem.mp h) x y (by omega) hy l

/-- **The merge join over a reduced right side.** For join columns in
    non-decreasing order, the merge loop of `Qlvr.mergeJoin` over the right
    rows whose key passes a test that every left key passes gives the same
    pairs of rows as over all the right rows. -/
theorem mergeGo_semijoin {α β : Type} [Inhabited α] [Inhabited β] (kl : α → UInt64) (kr : β → UInt64)
    (ok : α → β → Bool) (L : List α) (R : List β) (S : UInt64 → Bool) (hS : ∀ l ∈ L, S (kl l) = true)
    (hL : L.Pairwise fun a b => (kl a).toNat ≤ (kl b).toNat) (hR : R.Pairwise fun a b => (kr a).toNat ≤ (kr b).toNat) :
    ((mergeGo (fun x => kl L[x]!) (fun y => kr (R.filter fun r => S (kr r))[y]!)
        (fun x y => ok L[x]! (R.filter fun r => S (kr r))[y]!) L.length (R.filter fun r => S (kr r)).length
        (L.length + (R.filter fun r => S (kr r)).length + 1) 0 0 #[] #[]).1.toList.zip
      (mergeGo (fun x => kl L[x]!) (fun y => kr (R.filter fun r => S (kr r))[y]!)
        (fun x y => ok L[x]! (R.filter fun r => S (kr r))[y]!) L.length (R.filter fun r => S (kr r)).length
        (L.length + (R.filter fun r => S (kr r)).length + 1) 0 0 #[] #[]).2.toList).map
        (fun p => (L[p.1]!, (R.filter fun r => S (kr r))[p.2]!)) =
    ((mergeGo (fun x => kl L[x]!) (fun y => kr R[y]!) (fun x y => ok L[x]! R[y]!) L.length R.length
        (L.length + R.length + 1) 0 0 #[] #[]).1.toList.zip
      (mergeGo (fun x => kl L[x]!) (fun y => kr R[y]!) (fun x y => ok L[x]! R[y]!) L.length R.length
        (L.length + R.length + 1) 0 0 #[] #[]).2.toList).map (fun p => (L[p.1]!, R[p.2]!)) := by
  have hR' : (R.filter fun r => S (kr r)).Pairwise fun a b => (kr a).toNat ≤ (kr b).toNat := hR.filter _
  rw [mergeGo_pairs _ _ _ _ _ (pairwise_index kl L hL) (pairwise_index kr _ hR'),
    mergeGo_pairs _ _ _ _ _ (pairwise_index kl L hL) (pairwise_index kr R hR),
    mergeSpec_rows, mergeSpec_rows, joinRows_semijoin kl kr ok L R S hS]

/-- **The left outer join over a reduced right side** (the merge path of
    `OptJoin.leftOuterJoin`): for join columns in non-decreasing order,
    `outerPairs` over the merge loop's pairs, read back as rows, is the same
    over the right rows whose key passes a test that every left key passes as
    over all the right rows. -/
theorem outerPairs_merge_semijoin {α β : Type} [Inhabited α] [Inhabited β] (kl : α → UInt64) (kr : β → UInt64)
    (ok : α → β → Bool) (L : List α) (R : List β) (S : UInt64 → Bool) (hS : ∀ l ∈ L, S (kl l) = true)
    (hL : L.Pairwise fun a b => (kl a).toNat ≤ (kl b).toNat) (hR : R.Pairwise fun a b => (kr a).toNat ≤ (kr b).toNat) :
    let R' := R.filter fun r => S (kr r)
    let m' := mergeGo (fun x => kl L[x]!) (fun y => kr R'[y]!) (fun x y => ok L[x]! R'[y]!) L.length R'.length
      (L.length + R'.length + 1) 0 0 #[] #[]
    let m := mergeGo (fun x => kl L[x]!) (fun y => kr R[y]!) (fun x y => ok L[x]! R[y]!) L.length R.length
      (L.length + R.length + 1) 0 0 #[] #[]
    ((outerPairs L.length m'.1 m'.2).1.toList.zip (outerPairs L.length m'.1 m'.2).2.toList).map
        (fun p => (L[p.1]!, p.2.map (R'[·]!))) =
      ((outerPairs L.length m.1 m.2).1.toList.zip (outerPairs L.length m.1 m.2).2.toList).map
        (fun p => (L[p.1]!, p.2.map (R[·]!))) := by
  intro R' m' m
  have hR' : R'.Pairwise fun a b => (kr a).toNat ≤ (kr b).toNat := hR.filter _
  obtain ⟨a1, a2⟩ := outerPairs_merge (fun x => kl L[x]!) (fun y => kr R'[y]!)
    (fun x y => ok L[x]! R'[y]!) L.length R'.length (pairwise_index kl L hL) (pairwise_index kr R' hR')
  obtain ⟨b1, b2⟩ := outerPairs_merge (fun x => kl L[x]!) (fun y => kr R[y]!)
    (fun x y => ok L[x]! R[y]!) L.length R.length (pairwise_index kl L hL) (pairwise_index kr R hR)
  rw [a1, a2, b1, b2, ← List.unzip_fst, ← List.unzip_snd, List.zip_unzip, ← List.unzip_fst, ← List.unzip_snd,
    List.zip_unzip]
  have e1 := ljSpec_rows (fun l r => kl l == kr r && ok l r) L R'
  have e2 := ljSpec_rows (fun l r => kl l == kr r && ok l r) L R
  rw [e1, e2]
  apply ljRows_semijoin
  intro l hl r _ hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  rw [← hc.1]
  exact hS l hl

/-! ## Over solution mappings of ids (SPARQL 1.1 Join and LeftJoin) -/

/-- Two compatible rows bind a variable they both bind to one id. -/
theorem idCompatible_lookup (v : String) :
    ∀ (l r : IdRow) (x y : UInt64), idCompatible l r = true → idLookup v l = some x → idLookup v r = some y → x = y := by
  intro l
  induction l with
  | nil => intro r x y _ hx _; simp [idLookup] at hx
  | cons a rest ih =>
    intro r x y hc hx hy
    obtain ⟨w, a⟩ := a
    simp only [idCompatible, Bool.and_eq_true] at hc
    simp only [idLookup] at hx
    by_cases hw : w = v
    · rw [if_pos hw] at hx
      cases hx
      subst hw
      rw [hy] at hc
      simpa using hc.1
    · rw [if_neg hw] at hx
      exact ih r x y hc.2 hx hy

/-- Join(Ω1, Ω2) over ids (SPARQL 1.1 section 18.5, compatibility by id
    equality). -/
def idJoin (L R : List IdRow) : List IdRow :=
  L.flatMap fun r1 => R.filterMap fun r2 => if idCompatible r1 r2 then some (idMerge r1 r2) else none

/-- Decoding the id-level join gives SPARQL 1.1 Join of the decoded
    solutions, row for row, when `Term.eqb` of two decoded ids is id equality
    on the ids that occur. -/
theorem join_decode (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (L R : List IdRow) (hL : ∀ r ∈ L, RowIds ok r) (hR : ∀ r ∈ R, RowIds ok r) :
    (idJoin L R).map (decRow dec) = join (L.map (decRow dec)) (R.map (decRow dec)) := by
  unfold idJoin join
  rw [List.map_flatMap, List.flatMap_map]
  apply flatMap_congr'
  intro r1 h1
  rw [List.filterMap_map, List.map_filterMap]
  apply filterMap_congr'
  intro r2 h2
  simp only [Function.comp_def]
  rw [compatible_decRow dec ok hdec r1 r2 (hL r1 h1) (hR r2 h2), merge_decRow]
  cases idCompatible r1 r2 <;> simp

/-- The right-row test of a scan with candidates `S` for variable `v`: the
    row's id of `v` is a candidate (a row that does not bind `v` is kept). -/
def keepRow (v : String) (S : UInt64 → Bool) (r : IdRow) : Bool :=
  match idLookup v r with
  | some y => S y
  | none => true

theorem filterMap_filter_none {β γ : Type} (F : β → Option γ) (q : β → Bool) :
    ∀ (R : List β), (∀ r ∈ R, q r = false → F r = none) → (R.filter q).filterMap F = R.filterMap F := by
  intro R
  induction R with
  | nil => intro _; rfl
  | cons a rest ih =>
    intro h
    have ih' := ih (fun r hr => h r (List.mem_cons_of_mem _ hr))
    simp only [List.filter_cons]
    cases hq : q a
    · simp only [Bool.false_eq_true, if_false, List.filterMap_cons]
      rw [h a List.mem_cons_self hq, ih']
    · simp only [if_true, List.filterMap_cons]
      rw [ih']

/-- A right row whose id of `v` is not a candidate is compatible with no
    left row, when every left row binds `v` to a candidate. -/
theorem keepRow_false (v : String) (S : UInt64 → Bool) (l r : IdRow)
    (hl : ∃ x, idLookup v l = some x ∧ S x = true) (hr : keepRow v S r = false) : idCompatible l r = false := by
  obtain ⟨x, hx, hsx⟩ := hl
  unfold keepRow at hr
  cases hy : idLookup v r with
  | none => rw [hy] at hr; cases hr
  | some y =>
    rw [hy] at hr
    simp only at hr
    cases hc : idCompatible l r
    · rfl
    · have := idCompatible_lookup v l r x y hc hx hy
      subst this
      rw [hsx] at hr
      cases hr

/-- **Semi-join reduction, SPARQL Join on ids.** When every left row binds
    `v` to a candidate, the right rows whose `v` is not a candidate can be
    removed. -/
theorem idJoin_semijoin (v : String) (S : UInt64 → Bool) (L R : List IdRow)
    (hL : ∀ l ∈ L, ∃ x, idLookup v l = some x ∧ S x = true) :
    idJoin L (R.filter (keepRow v S)) = idJoin L R := by
  unfold idJoin
  apply flatMap_congr'
  intro l hlm
  apply filterMap_filter_none
  intro r _ hr
  rw [keepRow_false v S l r (hL l hlm) hr]
  rfl

/-- **Semi-join reduction, SPARQL LeftJoin on ids** (an OPTIONAL group's
    rows; the id path's shared variables are bound in every left row,
    `IdQuery.flattenOptional`). -/
theorem idLeftJoin_semijoin (v : String) (S : UInt64 → Bool) (L R : List IdRow)
    (hL : ∀ l ∈ L, ∃ x, idLookup v l = some x ∧ S x = true) :
    idLeftJoin L (R.filter (keepRow v S)) = idLeftJoin L R := by
  unfold idLeftJoin
  apply flatMap_congr'
  intro l hlm
  have e : (R.filter (keepRow v S)).filterMap (fun r2 => if idCompatible l r2 then some (idMerge l r2) else none) =
      R.filterMap (fun r2 => if idCompatible l r2 then some (idMerge l r2) else none) := by
    apply filterMap_filter_none
    intro r _ hr
    rw [keepRow_false v S l r (hL l hlm) hr]
    rfl
  simp only [e]

#print axioms joinRows_semijoin
#print axioms ljRows_semijoin
#print axioms mergeSpec_rows
#print axioms ljSpec_rows
#print axioms mergeGo_semijoin
#print axioms outerPairs_merge_semijoin
#print axioms join_decode
#print axioms idJoin_semijoin
#print axioms idLeftJoin_semijoin

end L4Factoidal.Storage.Sbm11.SemiJoin
