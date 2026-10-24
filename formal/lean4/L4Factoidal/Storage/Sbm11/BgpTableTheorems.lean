/-
L4Factoidal.Storage.Sbm11.BgpTableTheorems — the join loop of the id path's
basic graph patterns against the leaf model
(https://github.com/danbri/factoidal/issues/776; lemma L4l of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`IdQuery.evalBgpM` scans one triple pattern (`scanTableM` of `mkSpec`, L4k),
then joins the scans of the others one by one in the order of their
estimates (`bgpStepM`: `pickNext`, `stepPerm`, `scanPatM`, `joinStep`), with
a merge join when both sides are sorted on the merge variable and a hash
join otherwise. `evalBgpM_model`: the table it returns denotes the model's
sequential evaluation of the patterns (`IdLeaf.idBgpFrom` over the listing
`T` of the graph), up to order (`IdEquiv`).

## Steps

* `idJoin_equiv`: SPARQL 1.1 Join on rows of ids is a congruence for
  `IdEquiv`, when the left rows bind no variable twice (`compat_congr`,
  `merge_congr`).
* `Good`: what the loop keeps of every table (`Table.WF`, `NoUnbound`,
  `SortOk`, the sort variable a variable of the table). `out_good_left`,
  `out_good_right`: `Qlvr.joinOutput` of index arrays in left-row order (or
  right-row order, with the shared columns equal) keeps it.
  `hashJoin_good` (with `TableTheorems.hashJoin_pairs`, now stating the sort
  variable of each branch), `mergeJoin_good`, `joinStep_good`.
* `scan_good`: one scan of the loop (L4k with the listings of the four
  permutations permutations of `T`, `BgpStore`); `scanForJoin_good`: the
  right scan of a join, with candidates (`sipCands`, `sipRule`) or without.
* `permFor_lt`, `pickNext_mem`, `bgpStep_spec` (the invariant `LoopInv`: the
  patterns joined so far and the remaining ones are all the patterns once
  each; the table is `Good` and `IdEquiv` to `IdLeaf.bgpJoin` of the
  patterns joined so far), `loop_final` (with `IdLeaf.bgpJoin_equiv` and
  `IdLeaf.idBgpFrom_perm`).
* `idBgpFrom_missing`: a pattern with a constant that has no id: the id
  path returns an empty table, the model no row.

## The divided merge join (issue 961)

`bgpStepM` joins with `joinStepM par`: with `par = some p` and two sides
sorted on the merge variable, the merge join is divided into block ranges
(`IdQuery.mergeJoinParM`). `joinStepM_par`: for tables of the invariant `Good`
(whose `SortOk` is the order `WorkerPoolTheorems.mergeJoinParM_eq` needs) and
a `par` of `ParOk` (`Par.mapList`, when set, is a map), `joinStepM` is
`joinStep`. `evalBgpM_modelS_par` and `evalBgpM_model_par` hold for any such
`par`; `evalBgpM_modelS` and `evalBgpM_model` are the case `par = none`
(`parOk_none`). Not proved: that the native `mapList` meets `ParOk` (tested
by `tests/sbm11/threads.sh`); the parallel scans (`Store.scanTable`,
`Store.scanSipTable`) are excluded by `Store.Sequential`.

## Hypotheses

`BgpStore st gid T`: each permutation is in memory (`PermMem`, L4k) and its
listing of the graph `gid` is a permutation of `T` (L3b); single-thread
scans (`Store.Sequential`: `Store.scanTable` and `Store.scanSipTable` are
`none`). Any `Store.sipFactor`: a right scan with
candidates (`scanForJoin_good`, from `SipTableTheorems.scanSipTableM_spec`
and the semi-join reduction `SemiJoin.idJoin_semijoin`) gives the same join
as the full scan. The patterns: graph
slot `.const gid`, not over the named graphs, no FROM merge or FROM NAMED
(`PatG`); every variable kept (`need = fun _ => true`, as
`IdGroup.bgpM` calls it); no `pref`, no left table. The loop is proved over
any `ScanStore` (`evalBgpM_modelS`: a model `S t` of each pattern that the
matches `ScanTableTheorems.rowM` of every permutation's rows are a
permutation of): `BgpStore` is the case of one graph (`evalBgpM_model`),
`GraphBgpTableTheorems.named_scanStore` the case of `GRAPH ?g` over the named
graphs.

## Code

`IdQuery.evalBgpM`'s join loop was factored into `pickNext`, `mergeVarOf`,
`stepPerm`, `joinStep` and `bgpStepM` (the same steps; the loop state is
the structure `BgpLoop`), so that the proof names them.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.ScanTableTheorems
import L4Factoidal.Storage.Sbm11.SipTableTheorems
import L4Factoidal.Storage.Sbm11.SemiJoinTheorems
import L4Factoidal.Storage.Sbm11.WorkerPoolTheorems

namespace L4Factoidal.Storage.Sbm11.BgpTableTheorems

open L4Factoidal (two64)
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup idCompatible idMerge unbound)
open L4Factoidal.Storage.Sbm11.TableTheorems (RowEq NoUnbound SortOk)
open L4Factoidal.Storage.Sbm11.IdLeaf (IdEquiv Nd OptRowEq IPat scanRows bgpJoin)
open L4Factoidal.Storage.Sbm11.IdGroup (Pw PermPw)
open L4Factoidal.Storage.Sbm11.IdJoin (idJoin)

/-! ## Join on rows of ids, up to order and `RowEq` -/

theorem nd_mem_lookup : ∀ {r : IdRow}, Nd r → ∀ p ∈ r, idLookup p.1 r = some p.2
  | [], _, p, hp => by cases hp
  | (w, x) :: rest, hnd, p, hp => by
    unfold Nd at hnd
    simp only [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hp with h | h
    · subst h; simp [idLookup]
    · have hne : w ≠ p.1 := by
        intro e; apply hnd.1; rw [e]; exact List.mem_map.mpr ⟨p, h, rfl⟩
      show (if w = p.1 then some x else idLookup p.1 rest) = some p.2
      rw [if_neg hne]
      exact nd_mem_lookup hnd.2 p h

theorem compat_lookups (r1 r2 : IdRow) (hn : Nd r1) :
    idCompatible r1 r2 = true ↔ ∀ v a b, idLookup v r1 = some a → idLookup v r2 = some b → a = b := by
  rw [TableTheorems.idCompatible_iff]
  constructor
  · intro h v a b ha hb
    exact h (v, a) (OptJoin.idLookup_mem ha) b hb
  · intro h p hp y hy
    exact h p.1 p.2 y (nd_mem_lookup hn p hp) hy

theorem compat_congr {r1 r1' r2 r2' : IdRow} (hn1 : Nd r1) (hn1' : Nd r1') (h1 : RowEq r1 r1')
    (h2 : RowEq r2 r2') : idCompatible r1 r2 = idCompatible r1' r2' := by
  apply Bool.eq_iff_iff.mpr
  rw [compat_lookups r1 r2 hn1, compat_lookups r1' r2' hn1']
  constructor
  · intro h v a b ha hb; exact h v a b (by rw [h1 v]; exact ha) (by rw [h2 v]; exact hb)
  · intro h v a b ha hb; exact h v a b (by rw [← h1 v]; exact ha) (by rw [← h2 v]; exact hb)

theorem merge_congr {r1 r1' r2 r2' : IdRow} (h1 : RowEq r1 r1') (h2 : RowEq r2 r2') :
    RowEq (idMerge r1 r2) (idMerge r1' r2') := by
  intro u
  rw [IdLeaf.lookup_idMerge, IdLeaf.lookup_idMerge, h1 u, h2 u]

theorem pw_filterMap2 (f g : IdRow → Option IdRow) :
    ∀ {A B : List IdRow}, Pw RowEq A B → (∀ a b, RowEq a b → OptRowEq (f a) (g b)) →
      Pw RowEq (A.filterMap f) (B.filterMap g)
  | _, _, .nil, _ => .nil
  | _, _, .cons (a := a) (b := b) h t, hfg => by
    have ih := pw_filterMap2 f g t hfg
    have hx := hfg a b h
    simp only [List.filterMap_cons]
    revert hx
    cases f a <;> cases g b <;> intro hx
    · exact ih
    · exact hx.elim
    · exact hx.elim
    · exact .cons hx ih

theorem pw_flatMap2 (F G : IdRow → List IdRow) :
    ∀ {A B : List IdRow}, Pw RowEq A B → (∀ a ∈ A, ∀ b ∈ B, RowEq a b → Pw RowEq (F a) (G b)) →
      Pw RowEq (A.flatMap F) (B.flatMap G)
  | _, _, .nil, _ => .nil
  | _, _, .cons (a := a) (b := b) h t, hFG => by
    simp only [List.flatMap_cons]
    exact Pw.append (hFG a List.mem_cons_self b List.mem_cons_self h)
      (pw_flatMap2 F G t fun x hx y hy hxy => hFG x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) hxy)

/-- SPARQL 1.1 Join on rows of ids is a congruence for the same multisets of
    solution mappings, when the left rows bind no variable twice. -/
theorem idJoin_equiv {L L' R R' : List IdRow} (hL : IdEquiv L L') (hR : IdEquiv R R')
    (ndL : ∀ r ∈ L, Nd r) (ndL' : ∀ r ∈ L', Nd r) : IdEquiv (idJoin L R) (idJoin L' R') := by
  obtain ⟨C, pLC, wCL'⟩ := hL
  obtain ⟨D, pRD, wDR'⟩ := hR
  have ndC : ∀ r ∈ C, Nd r := fun r hr => ndL r (pLC.mem_iff.mpr hr)
  refine ⟨idJoin C D, ?_, ?_⟩
  · unfold idJoin
    refine List.Perm.trans (List.Perm.flatMap_right _ pLC) ?_
    exact IdGroup.perm_flatMap_left _ _ C fun l _ => List.Perm.filterMap _ pRD
  · unfold idJoin
    apply pw_flatMap2 _ _ wCL'
    intro a ha b hbm hab
    have hb : Nd b := ndL' b hbm
    apply pw_filterMap2 _ _ wDR'
    intro c d hcd
    rw [compat_congr (ndC a ha) hb hab hcd]
    split
    · exact merge_congr hab hcd
    · trivial

/-! ## The tables of the join loop -/

open L4Factoidal.Qlvr (joinOutput joinVars sharedCols)
open L4Factoidal.Storage.Sbm11.TableTheorems (RowsEq idx_some idx_none idx_of_getElem lookupAt_some
  joinOutput_spec)

/-- What the join loop keeps of every table: well formed, no id 0, in the
    order its sort variable says, and the sort variable a variable of the
    table. -/
structure Good (t : Table) : Prop where
  wf : t.WF
  nu : NoUnbound t
  so : SortOk t
  sv : ∀ v, t.sortVar = some v → (t.idx v).isSome

theorem rowsEq_pw : ∀ {A B : List IdRow}, RowsEq A B → Pw RowEq A B
  | [], [], _ => .nil
  | [], _ :: _, h => absurd h.1 (by simp)
  | _ :: _, [], h => absurd h.1 (by simp)
  | a :: A, b :: B, h =>
    .cons (h.2 0 (by simp) (by simp)) (rowsEq_pw ⟨by simpa using h.1, fun k h1 h2 =>
      h.2 (k + 1) (by simpa using h1) (by simpa using h2)⟩)

theorem idEquiv_of_rowsEq_perm {A M B : List IdRow} (h1 : RowsEq A M) (h2 : M.Perm B) : IdEquiv A B := by
  obtain ⟨A', hp, hw⟩ := Pw.perm_right (rowsEq_pw h1) h2
  exact ⟨A', hp, hw⟩

/-- A variable of the join output that the left table does not have is a
    variable of the right table. -/
theorem out_var_right (l r : Table) (v : String) (hv : v ∈ (joinVars l r).1.toList) (hl : l.idx v = none)
    (hrnd : r.vars.toList.Nodup) : ∃ q, r.idx v = some q := by
  rw [TableTheorems.joinVars_vars] at hv
  rcases List.mem_append.mp hv with h | h
  · obtain ⟨c, hc, hcv⟩ := List.getElem_of_mem h
    have := idx_none hl c (by simpa using hc)
    rw [getElem!_pos l.vars c (by simpa using hc)] at this
    exact absurd (by simpa using hcv) this
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp h
    have hq' := ((TableTheorems.mem_extra (TableTheorems.joinVars_extra l r)).mp hq).1
    exact ⟨q, idx_of_getElem hrnd hq'⟩

/-- Every variable of the join output has an id in every row. -/
theorem out_lookup_some (l r : Table) (hl : l.WF) (hr : r.WF) (hlu : NoUnbound l) (hru : NoUnbound r)
    (li ri : Array Nat) (hsz : li.size = ri.size) (hli : ∀ i ∈ li.toList, i < l.rows)
    (hri : ∀ j ∈ ri.toList, j < r.rows) (sv : Option String) (k : Nat) (hk : k < li.size)
    (v : String) (hv : v ∈ (joinVars l r).1.toList) :
    ∃ y, (joinOutput l r (joinVars l r).1 (joinVars l r).2 li ri sv).lookupAt k v = some y := by
  obtain ⟨_, _, hlk⟩ := joinOutput_spec l r hl hr li ri hsz hli hri sv
  rw [hlk k hk v]
  have hlik : li[k]! < l.rows := hli _ (by rw [getElem!_pos li k hk]; simp)
  have hrik : ri[k]! < r.rows := hri _ (by rw [getElem!_pos ri k (by omega)]; simp)
  cases hlv : l.idx v with
  | some c =>
    simp only [TableTheorems.nz]
    have := hlu c li[k]! (idx_some hlv).1 hlik
    rw [if_neg (by simpa using this)]
    exact ⟨_, rfl⟩
  | none =>
    simp only
    obtain ⟨q, hq⟩ := out_var_right l r v hv hlv hr.nodup
    rw [TableTheorems.lookupAt_eq r, hq]
    simp only [TableTheorems.nz]
    have := hru q ri[k]! (idx_some hq).1 hrik
    rw [if_neg (by simpa using this)]
    exact ⟨_, rfl⟩

theorem out_noUnbound (l r : Table) (hl : l.WF) (hr : r.WF) (hlu : NoUnbound l) (hru : NoUnbound r)
    (li ri : Array Nat) (hsz : li.size = ri.size) (hli : ∀ i ∈ li.toList, i < l.rows)
    (hri : ∀ j ∈ ri.toList, j < r.rows) (sv : Option String) :
    NoUnbound (joinOutput l r (joinVars l r).1 (joinVars l r).2 li ri sv) := by
  obtain ⟨hT, hrows, _⟩ := joinOutput_spec l r hl hr li ri hsz hli hri sv
  intro c k hc hk
  have hv : (joinOutput l r (joinVars l r).1 (joinVars l r).2 li ri sv).vars[c]! ∈ (joinVars l r).1.toList := by
    rw [getElem!_pos _ c hc]; exact Array.getElem_mem_toList hc
  obtain ⟨y, hy⟩ := out_lookup_some l r hl hr hlu hru li ri hsz hli hri sv k (by rw [← hrows]; exact hk) _ hv
  obtain ⟨q, hq, hq0, _⟩ := lookupAt_some.mp hy
  rw [idx_of_getElem hT.nodup hc] at hq
  cases hq
  exact hq0

/-- A table whose column `v` holds `f k` in row `k`, with `f` monotone, is
    in the order of `v`. -/
theorem sortOk_of_values (T : Table) (v : String) (hsv : ∀ w, T.sortVar = some w → w = v)
    (f : Nat → UInt64) (hf : ∀ k, k < T.rows → T.lookupAt k v = some (f k))
    (hmono : ∀ x y, x ≤ y → y < T.rows → (f x).toNat ≤ (f y).toNat) : SortOk T := by
  intro w c hw hc x y hxy hy
  have := hsv w hw
  subst this
  have ex : ∀ k, k < T.rows → T.at c k = f k := by
    intro k hk
    obtain ⟨q, hq, _, e⟩ := lookupAt_some.mp (hf k hk)
    rw [hc] at hq; cases hq
    exact e
  rw [ex x (by omega), ex y hy]
  exact hmono x y hxy hy

/-! ## The order of the index arrays of the joins -/

theorem fst_sorted (a n : Nat) (L : Nat → List Nat) :
    (((List.range' a n).flatMap fun x => (L x).map fun y => (x, y)).map Prod.fst).Pairwise (· ≤ ·) := by
  rw [List.map_flatMap]
  simp only [List.map_map]
  rw [List.pairwise_flatMap]
  constructor
  · intro x _
    rw [List.pairwise_map]
    exact List.pairwise_of_forall (fun _ _ => Nat.le_refl _)
  · apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range'
    intro x y _ _ hxy u hu w hw
    simp only [List.mem_map, Function.comp] at hu hw
    obtain ⟨_, _, rfl⟩ := hu
    obtain ⟨_, _, rfl⟩ := hw
    exact Nat.le_of_lt hxy

theorem snd_sorted (a n : Nat) (L : Nat → List Nat) :
    (((List.range' a n).flatMap fun y => (L y).map fun x => (x, y)).map Prod.snd).Pairwise (· ≤ ·) := by
  rw [List.map_flatMap]
  simp only [List.map_map]
  rw [List.pairwise_flatMap]
  constructor
  · intro y _
    rw [List.pairwise_map]
    exact List.pairwise_of_forall (fun _ _ => Nat.le_refl _)
  · apply List.Pairwise.imp_of_mem _ List.pairwise_lt_range'
    intro x y _ _ hxy u hu w hw
    simp only [List.mem_map, Function.comp] at hu hw
    obtain ⟨_, _, rfl⟩ := hu
    obtain ⟨_, _, rfl⟩ := hw
    exact Nat.le_of_lt hxy

theorem arr_mono (a : Array Nat) (P : List Nat) (h : a.toList = P) (hP : P.Pairwise (· ≤ ·)) :
    ∀ x y, x ≤ y → y < a.size → a[x]! ≤ a[y]! := by
  intro x y hxy hy
  rw [getElem!_pos a x (by omega), getElem!_pos a y hy]
  have hx' : x < a.toList.length := by simp; omega
  have hy' : y < a.toList.length := by simp; omega
  rw [← Array.getElem_toList (h := by omega), ← Array.getElem_toList (h := hy)]
  rcases Nat.lt_or_eq_of_le hxy with hlt | heq
  · rw [← h] at hP
    exact List.pairwise_iff_getElem.mp hP x y hx' hy' hlt
  · subst heq; exact Nat.le_refl _

/-! ## Hash join and merge join keep the loop's invariant -/

open L4Factoidal.Storage.Sbm11.OptJoin (innerSpec)
open L4Factoidal.Storage.Sbm11.TableTheorems (shEq innerSpecR mem_innerSpec mem_innerSpecR shEq_iff
  mem_sharedCols nz)

theorem idx_isSome_of_mem (t : Table) (v : String) (h : v ∈ t.vars.toList) : (t.idx v).isSome := by
  unfold Table.idx
  cases hf : t.vars.findIdx? (· == v) with
  | some _ => rfl
  | none =>
    have := Array.findIdx?_eq_none_iff.mp hf v (Array.mem_toList_iff.mp h)
    simp at this

theorem mem_of_idx {t : Table} {v : String} {c : Nat} (h : t.idx v = some c) : v ∈ t.vars.toList := by
  obtain ⟨hc, hv⟩ := idx_some h
  rw [getElem!_pos t.vars c hc] at hv
  rw [← hv]; exact Array.getElem_mem_toList hc

theorem pair_at {li ri : Array Nat} {P : List (Nat × Nat)} (h1 : li.toList = P.map Prod.fst)
    (h2 : ri.toList = P.map Prod.snd) (k : Nat) (hk : k < li.size) : (li[k]!, ri[k]!) ∈ P := by
  have hl : li.size = P.length := by rw [← Array.length_toList, h1, List.length_map]
  have hr : ri.size = P.length := by rw [← Array.length_toList, h2, List.length_map]
  have e1 : li[k]! = P[k].1 := by
    rw [getElem!_pos li k hk, ← Array.getElem_toList]; simp [h1]
  have e2 : ri[k]! = P[k].2 := by
    rw [getElem!_pos ri k (by omega), ← Array.getElem_toList]; simp [h2]
  rw [e1, e2]
  exact List.getElem_mem (by omega)

theorem size_eq_of {li ri : Array Nat} {P : List (Nat × Nat)} (h1 : li.toList = P.map Prod.fst)
    (h2 : ri.toList = P.map Prod.snd) : li.size = ri.size := by
  rw [← Array.length_toList, ← Array.length_toList (xs := ri), h1, h2, List.length_map, List.length_map]

theorem range_of {li : Array Nat} {P : List (Nat × Nat)} (h1 : li.toList = P.map Prod.fst) (n : Nat)
    (hP : ∀ p ∈ P, p.1 < n) : ∀ i ∈ li.toList, i < n := by
  intro i hi
  rw [h1] at hi
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  exact hP p hp

theorem range_of2 {ri : Array Nat} {P : List (Nat × Nat)} (h2 : ri.toList = P.map Prod.snd) (n : Nat)
    (hP : ∀ p ∈ P, p.2 < n) : ∀ i ∈ ri.toList, i < n := by
  intro i hi
  rw [h2] at hi
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hi
  exact hP p hp

/-- The output of a join from pairs whose left rows are in order, carrying
    the left table's sort variable, is in that order. -/
theorem out_good_left (l r : Table) (gl : Good l) (gr : Good r) (li ri : Array Nat) (P : List (Nat × Nat))
    (h1 : li.toList = P.map Prod.fst) (h2 : ri.toList = P.map Prod.snd)
    (hPl : ∀ p ∈ P, p.1 < l.rows) (hPr : ∀ p ∈ P, p.2 < r.rows)
    (hmono : (P.map Prod.fst).Pairwise (· ≤ ·)) :
    Good (joinOutput l r (joinVars l r).1 (joinVars l r).2 li ri l.sortVar) := by
  have hsz := size_eq_of h1 h2
  have hli := range_of h1 l.rows hPl
  have hri := range_of2 h2 r.rows hPr
  obtain ⟨hT, hrows, hlk⟩ := joinOutput_spec l r gl.wf gr.wf li ri hsz hli hri l.sortVar
  have hnu := out_noUnbound l r gl.wf gr.wf gl.nu gr.nu li ri hsz hli hri l.sortVar
  have hvars : (joinOutput l r (joinVars l r).1 (joinVars l r).2 li ri l.sortVar).vars = (joinVars l r).1 := rfl
  have hsvT : (joinOutput l r (joinVars l r).1 (joinVars l r).2 li ri l.sortVar).sortVar = l.sortVar := rfl
  generalize joinOutput l r (joinVars l r).1 (joinVars l r).2 li ri l.sortVar = T at hT hrows hlk hnu hvars hsvT ⊢
  refine ⟨hT, hnu, ?_, ?_⟩
  · cases hsv : l.sortVar with
    | none => intro w c hw; rw [hsvT, hsv] at hw; cases hw
    | some v =>
      obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp (gl.sv v hsv)
      apply sortOk_of_values _ v (fun w hw => by rw [hsvT, hsv] at hw; cases hw; rfl)
        (fun k => l.at lc li[k]!)
      · intro k hk
        rw [hrows] at hk
        rw [hlk k hk v, hlc]
        simp only [nz]
        have := gl.nu lc li[k]! (idx_some hlc).1 (hli _ (by rw [getElem!_pos li k hk]; simp))
        rw [if_neg (by simpa using this)]
      · intro x y hxy hy
        rw [hrows] at hy
        have hm := arr_mono li _ h1 hmono x y hxy hy
        exact gl.so v lc hsv hlc _ _ hm (hli _ (by rw [getElem!_pos li y hy]; simp))
  · intro w hw
    rw [hsvT] at hw
    obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp (gl.sv w hw)
    apply idx_isSome_of_mem
    rw [hvars, TableTheorems.joinVars_vars]
    exact List.mem_append_left _ (mem_of_idx hlc)

/-- The output of a join from pairs whose right rows are in order and whose
    shared columns agree, carrying the right table's sort variable, is in
    that order. -/
theorem out_good_right (l r : Table) (gl : Good l) (gr : Good r) (li ri : Array Nat) (P : List (Nat × Nat))
    (h1 : li.toList = P.map Prod.fst) (h2 : ri.toList = P.map Prod.snd)
    (hPl : ∀ p ∈ P, p.1 < l.rows) (hPr : ∀ p ∈ P, p.2 < r.rows)
    (hsh : ∀ p ∈ P, shEq l r p.1 p.2 = true)
    (hmono : (P.map Prod.snd).Pairwise (· ≤ ·)) (sv : Option String)
    (hsv : ∀ v, sv = some v → r.sortVar = some v) :
    Good (joinOutput l r (joinVars l r).1 (joinVars l r).2 li ri sv) := by
  have hsz := size_eq_of h1 h2
  have hli := range_of h1 l.rows hPl
  have hri := range_of2 h2 r.rows hPr
  obtain ⟨hT, hrows, hlk⟩ := joinOutput_spec l r gl.wf gr.wf li ri hsz hli hri sv
  have hnu := out_noUnbound l r gl.wf gr.wf gl.nu gr.nu li ri hsz hli hri sv
  have hvars : (joinOutput l r (joinVars l r).1 (joinVars l r).2 li ri sv).vars = (joinVars l r).1 := rfl
  have hsvT : (joinOutput l r (joinVars l r).1 (joinVars l r).2 li ri sv).sortVar = sv := rfl
  generalize joinOutput l r (joinVars l r).1 (joinVars l r).2 li ri sv = T at hT hrows hlk hnu hvars hsvT ⊢
  refine ⟨hT, hnu, ?_, ?_⟩
  · cases hs : sv with
    | none => intro w c hw; rw [hsvT, hs] at hw; cases hw
    | some v =>
      have hrv := hsv v hs
      obtain ⟨rc, hrc⟩ := Option.isSome_iff_exists.mp (gr.sv v hrv)
      apply sortOk_of_values _ v (fun w hw => by rw [hsvT, hs] at hw; cases hw; rfl)
        (fun k => r.at rc ri[k]!)
      · intro k hk
        rw [hrows] at hk
        have hp := pair_at h1 h2 k hk
        have hlik : li[k]! < l.rows := hPl _ hp
        have hrik : ri[k]! < r.rows := hPr _ hp
        rw [hlk k hk v]
        cases hlv : l.idx v with
        | some lc =>
          simp only [nz]
          have hshared : (lc, rc) ∈ sharedCols l r := by
            obtain ⟨hc, hcv⟩ := idx_some hlv
            exact mem_sharedCols.mpr ⟨hc, by rw [hcv]; exact hrc⟩
          have he := (shEq_iff l r _ _).mp (hsh _ hp) lc rc hshared
          have := gl.nu lc li[k]! (idx_some hlv).1 hlik
          rw [if_neg (by simpa using this)]
          simp only at he
          rw [he]
        | none =>
          simp only
          rw [TableTheorems.lookupAt_eq r, hrc]
          simp only [nz]
          have := gr.nu rc ri[k]! (idx_some hrc).1 hrik
          rw [if_neg (by simpa using this)]
      · intro x y hxy hy
        rw [hrows] at hy
        have hm := arr_mono ri _ h2 hmono x y hxy (by omega)
        exact gr.so v rc hrv hrc _ _ hm (hri _ (by rw [getElem!_pos ri y (by omega)]; simp))
  · intro w hw
    rw [hsvT] at hw
    obtain ⟨rc, hrc⟩ := Option.isSome_iff_exists.mp (gr.sv w (hsv w hw))
    apply idx_isSome_of_mem
    rw [hvars, TableTheorems.joinVars_vars]
    by_cases hlw : w ∈ l.vars.toList
    · exact List.mem_append_left _ hlw
    · apply List.mem_append_right
      obtain ⟨hc, hcv⟩ := idx_some hrc
      refine List.mem_map.mpr ⟨rc, ?_, hcv⟩
      rw [TableTheorems.mem_extra (TableTheorems.joinVars_extra l r)]
      refine ⟨hc, ?_⟩
      rw [hcv]
      intro hm; exact hlw (Array.mem_toList_iff.mpr hm)

/-- **Hash join in the loop.** `Qlvr.hashJoin` of two tables of the loop's
    invariant keeps the invariant and denotes SPARQL 1.1 Join of their rows,
    up to order (L5b). -/
theorem hashJoin_good (l r : Table) (gl : Good l) (gr : Good r) :
    Good (L4Factoidal.Qlvr.hashJoin l r) ∧
      IdEquiv (L4Factoidal.Qlvr.hashJoin l r).idRows (idJoin l.idRows r.idRows) := by
  obtain ⟨_, M, hM, hRE, _⟩ := TableTheorems.hashJoin_rows l r gl.wf gr.wf gl.nu gr.nu
  refine ⟨?_, idEquiv_of_rowsEq_perm hRE hM⟩
  obtain ⟨li, ri, sv, he, hcase⟩ := TableTheorems.hashJoin_pairs l r
  rw [he]
  rcases hcase with ⟨_, hsv, h1, h2⟩ | ⟨_, hsv, h1, h2⟩
  · subst hsv
    apply out_good_left l r gl gr li ri _ h1 h2
      (fun p hp => by obtain ⟨i, j⟩ := p; exact (mem_innerSpec.mp hp).1)
      (fun p hp => by obtain ⟨i, j⟩ := p; exact (mem_innerSpec.mp hp).2.1)
    rw [TableTheorems.innerSpec_eq]; exact fst_sorted 0 l.rows _
  · apply out_good_right l r gl gr li ri _ h1 h2
      (fun p hp => by obtain ⟨i, j⟩ := p; exact (mem_innerSpecR.mp hp).1)
      (fun p hp => by obtain ⟨i, j⟩ := p; exact (mem_innerSpecR.mp hp).2.1)
      (fun p hp => by obtain ⟨i, j⟩ := p; exact (mem_innerSpecR.mp hp).2.2)
      (by unfold innerSpecR; exact snd_sorted 0 r.rows _)
    intro v hv
    rw [hsv] at hv
    cases hr : r.sortVar with
    | none => rw [hr] at hv; cases hv
    | some w =>
      rw [hr] at hv
      simp only at hv
      split at hv
      · cases hv; rfl
      · cases hv

/-- **Merge join in the loop.** `Qlvr.mergeJoin l r v` of two tables of the
    loop's invariant, both sorted on `v`, keeps the invariant and denotes
    SPARQL 1.1 Join of their rows (L5a′). -/
theorem mergeJoin_good (l r : Table) (v : String) (gl : Good l) (gr : Good r)
    (hlv : l.sortVar = some v) (hrv : r.sortVar = some v) :
    Good (L4Factoidal.Qlvr.mergeJoin l r v) ∧
      IdEquiv (L4Factoidal.Qlvr.mergeJoin l r v).idRows (idJoin l.idRows r.idRows) := by
  obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp (gl.sv v hlv)
  obtain ⟨rc, hrc⟩ := Option.isSome_iff_exists.mp (gr.sv v hrv)
  have hA := gl.so v lc hlv hlc
  have hB := gr.so v rc hrv hrc
  obtain ⟨_, hRE⟩ := TableTheorems.mergeJoin_rows l r v gl.wf gr.wf
    (TableTheorems.sharedBound_of l r gl.nu gr.nu) lc rc hlc hrc hA hB
  refine ⟨?_, idEquiv_of_rowsEq_perm hRE (List.Perm.refl _)⟩
  rw [L4Factoidal.Qlvr.mergeJoin_eq, hlc, hrc]
  simp only [Option.getD_some]
  let ok : Nat → Nat → Bool := fun x y => ((sharedCols l r).filter fun pq => pq.1 != lc).all
    fun pq => l.at pq.1 x == r.at pq.2 y
  obtain ⟨h1, h2⟩ := L4Factoidal.Qlvr.mergeGo_spec (l.at lc) (r.at rc) ok l.rows r.rows hA hB
    (l.rows + r.rows + 1) 0 0 #[] #[] (by omega)
  have hs : L4Factoidal.Qlvr.mergeSpec (l.at lc) (r.at rc) ok l.rows r.rows 0 0 =
      innerSpec l.rows r.rows (shEq l r) := by
    rw [TableTheorems.innerSpec_eq]
    unfold L4Factoidal.Qlvr.mergeSpec
    simp only [Nat.sub_zero]
    congr 1; funext x; congr 1
    apply List.filter_congr
    intro y _
    exact TableTheorems.merge_cand l r v lc rc hlc hrc x y
  rw [hs, List.nil_append] at h1 h2
  rw [← hlv]
  apply out_good_left l r gl gr _ _ _ h1 h2
    (fun p hp => by obtain ⟨i, j⟩ := p; exact (mem_innerSpec.mp hp).1)
    (fun p hp => by obtain ⟨i, j⟩ := p; exact (mem_innerSpec.mp hp).2.1)
  rw [TableTheorems.innerSpec_eq]; exact fst_sorted 0 l.rows _

/-! ## Rows of the loop -/

theorem filterMap_sublist_map {α β : Type} (h : α → Option β) (f : α → β)
    (hh : ∀ a, h a = none ∨ h a = some (f a)) : ∀ (l : List α), (l.filterMap h).Sublist (l.map f)
  | [] => List.Sublist.slnil
  | a :: l => by
    rw [List.filterMap_cons, List.map_cons]
    rcases hh a with e | e
    · rw [e]; exact (filterMap_sublist_map h f hh l).cons _
    · rw [e]; exact (filterMap_sublist_map h f hh l).cons_cons _

/-- A row of a table with no variable twice binds no variable twice. -/
theorem nd_idRow (t : Table) (hnd : t.vars.toList.Nodup) (i : Nat) : Nd (t.idRow i) := by
  unfold Nd Table.idRow
  rw [List.map_filterMap]
  have hsub := filterMap_sublist_map (fun c => Option.map Prod.fst
      (if t.at c i == unbound then none else some (t.vars[c]!, t.at c i))) (fun c => t.vars[c]!)
    (fun c => by by_cases h : t.at c i == unbound <;> simp [h]) (List.range t.vars.size)
  apply hsub.nodup
  have : (List.range t.vars.size).map (fun c => t.vars[c]!) = t.vars.toList := by
    apply List.ext_getElem
    · simp
    · intro n h1 h2
      simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
      rw [getElem!_pos t.vars n (by simpa using h1)]
  rw [this]; exact hnd

theorem nd_idRows (t : Table) (hnd : t.vars.toList.Nodup) : ∀ r ∈ t.idRows, Nd r := by
  intro r hr
  unfold Table.idRows at hr
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hr
  exact nd_idRow t hnd i

theorem nd_bgpJoin (Tof : IPat → List IdPath.IdTriple) :
    ∀ (ps : List IPat) (L : List IdRow), (∀ r ∈ L, Nd r) → ∀ r ∈ bgpJoin Tof ps L, Nd r
  | [], _, h => h
  | _ :: ps, L, h => nd_bgpJoin Tof ps _ (IdLeaf.nd_idJoin L _ h)

theorem bgpJoin_snoc (Tof : IPat → List IdPath.IdTriple) (ps : List IPat) (t : IPat) (L : List IdRow) :
    bgpJoin Tof (ps ++ [t]) L = idJoin (bgpJoin Tof ps L) (scanRows t (Tof t)) := by
  unfold bgpJoin
  rw [List.foldl_append]
  rfl

/-- Joining with the unit row (`{}`) changes no solution mapping. -/
theorem idJoin_unit (R : List IdRow) : IdEquiv (idJoin [[]] R) R := by
  apply IdEquiv.of_pw
  unfold idJoin
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  induction R with
  | nil => exact .nil
  | cons r R ih =>
    rw [List.filterMap_cons, show idCompatible [] r = true from rfl, if_pos rfl]
    refine .cons ?_ ih
    intro u
    rw [IdLeaf.lookup_idMerge]
    rfl

/-! ## The loop over `ExceptT String Id` -/

theorem forIn_exc {β : Type} (P : Nat → β → Prop) (Q : β → Prop)
    (f : Nat → β → ExceptT String Id (ForInStep β)) :
    ∀ (n s : Nat) (b : β), P s b →
      (∀ a b, s ≤ a → a < s + n → P a b →
        (∃ b', f a b = pure (.yield b') ∧ P (a + 1) b') ∨ (∃ b', f a b = pure (.done b') ∧ Q b')) →
      ∃ b', forIn (List.range' s n) b f = pure b' ∧ (P (s + n) b' ∨ Q b') := by
  intro n
  induction n with
  | zero => intro s b h _; exact ⟨b, rfl, Or.inl (by simpa using h)⟩
  | succ n ih =>
    intro s b h hs
    rw [List.range'_succ, List.forIn_cons]
    rcases hs s b (Nat.le_refl _) (by omega) h with ⟨b', hf, hP⟩ | ⟨b', hf, hQ⟩
    · rw [hf, pure_bind]
      obtain ⟨b'', h1, h2⟩ := ih (s + 1) b' hP (fun a b2 h1 h2 h3 => hs a b2 (by omega) (by omega) h3)
      refine ⟨b'', h1, ?_⟩
      rw [show s + 1 + n = s + (n + 1) by omega] at h2
      exact h2
    · rw [hf, pure_bind]
      exact ⟨b', rfl, Or.inr hQ⟩

/-- A loop over a list whose body always yields a value. -/
theorem forIn_exc_list {α β : Type} (f : α → β → ExceptT String Id (ForInStep β))
    (hf : ∀ a b, ∃ b', f a b = pure (.yield b')) : ∀ (l : List α) (b : β), ∃ b', forIn l b f = pure b' := by
  intro l
  induction l with
  | nil => intro b; exact ⟨b, rfl⟩
  | cons a l ih =>
    intro b
    obtain ⟨b', hb⟩ := hf a b
    rw [List.forIn_cons, hb, pure_bind]
    exact ih b'

/-! ## The arrays of the planner -/

/-- The index the planner picks (the first one of least estimate) is one of
    the candidates. -/
theorem argmin_mem (est : Array Nat) (cands : Array Nat) (h : 0 < cands.size) :
    cands.foldl (fun b k => if est[k]! < est[b]! then k else b) cands[0]! ∈ cands.toList := by
  rw [← Array.foldl_toList]
  have h0 : cands[0]! ∈ cands.toList := by rw [getElem!_pos cands 0 h]; exact Array.getElem_mem_toList h
  generalize cands[0]! = b0 at h0 ⊢
  generalize cands.toList = l at h0 ⊢
  suffices ∀ (m : List Nat) (b : Nat), b ∈ l → (∀ x ∈ m, x ∈ l) →
      m.foldl (fun b k => if est[k]! < est[b]! then k else b) b ∈ l from this l b0 h0 (fun _ h => h)
  intro m
  induction m with
  | nil => intro b hb _; exact hb
  | cons x m ih =>
    intro b hb hm
    simp only [List.foldl_cons]
    apply ih _ _ (fun y hy => hm y (List.mem_cons_of_mem _ hy))
    split
    · exact hm x List.mem_cons_self
    · exact hb

theorem filter_ne_perm (l : List Nat) (hnd : l.Nodup) (a : Nat) (ha : a ∈ l) :
    l.Perm (a :: l.filter (fun x => x != a)) := by
  have : l.filter (fun x => x != a) = l.erase a := by
    rw [List.Nodup.erase_eq_filter hnd]
  rw [this]
  exact List.perm_cons_erase ha

/-! ## One scan of the loop -/

open L4Factoidal.Storage.Sbm11.ScanTableTheorems (PermMem permListing ipatOf scanTable_model GSlot rowM rowM_const
  scanTable_modelG keptRows_pwG idRows_eqG)

/-- `permFor` names one of the four permutations. -/
theorem permFor_lt (t : Pat) (pref : Option Nat) : permFor t pref < 4 := by
  unfold permFor
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    show permOrder.size = 4 from rfl, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  generalize hF : (forIn (m := Id) (List.range' 0 4) ((none, none) : Option Nat × Option Nat) _) = F
  have := TableTheorems.forIn_inv'
    (fun _ (s : Option Nat × Option Nat) => (∀ x, s.1 = some x → x < 4) ∧ (∀ x, s.2 = some x → x < 4))
    (fun (s : Option Nat × Option Nat) => (∀ x, s.1 = some x → x < 4) ∧ (∀ x, s.2 = some x → x < 4))
    hF ⟨fun x h => (by cases h), fun x h => (by cases h)⟩ (fun a b _ ha hP => ⟨fun b' hb' => ?_, fun b' hb' => ?_⟩)
  · have h : (∀ x, F.run.1 = some x → x < 4) ∧ (∀ x, F.run.2 = some x → x < 4) := by
      rcases this with h | h <;> exact h
    rw [TableTheorems.id_bind]
    cases h1 : F.run.1 with
    | some r => exact h.1 r h1
    | none =>
      cases h2 : F.run.2 with
      | some r => exact h.2 r h2
      | none => show 0 < 4; omega
  all_goals
    try dsimp only at hb'
    repeat' split at hb'
    all_goals
      cases hb' <;> exact ⟨fun x h => by first | (cases h; done) | (cases h; omega) | exact hP.1 x h,
          fun x h => by first | (cases h; done) | (cases h; omega) | exact hP.2 x h⟩

/-- The single-thread scans: no replacement for `scanTableM` (issue 799) and
    none for `scanSipTableM` (issue 799, KR 1.2), so `scanTableOf` is
    `scanTableM` and `scanSipTableOf` is `scanSipTableM`. -/
def _root_.L4Factoidal.Storage.Sbm11.IdQuery.Store.Sequential {m : Type → Type} (st : Store m) : Prop :=
  st.scanTable = none ∧ st.scanSipTable = none

/-- The store of a basic graph pattern over one graph `gid`: each of the four
    permutations is in memory (`PermMem`) and its listing of the graph is a
    permutation of the listing `T` (lemma L3b gives this for an admitted
    generation); the scans are the single-thread `scanTableM`
    (`Store.Sequential`). -/
structure BgpStore (st : Store Id) (gid : UInt64) (T : List IdPath.IdTriple) : Prop where
  perm : ∀ perm, perm < 4 → ∃ prb ms, PermMem st perm prb ms ∧
    (permListing perm gid (ms.flatMap (ScanFoldTheorems.blockRows prb))).Perm T
  scan : st.Sequential

theorem sortVarOf_mem (spec : ScanSpec) (v : String) (h : sortVarOf spec = some v) : v ∈ spec.outVars.toList := by
  unfold sortVarOf at h
  split at h
  · split at h
    · exact Array.mem_toList_iff.mpr (Array.mem_of_getElem? h)
    · cases h
  · cases h

/-- A store whose four permutations are in memory, with single-thread scans,
    and whose model of each pattern `t` with `P t` is the list `S t`: the
    matches `ScanTableTheorems.rowM t perm` of each permutation's rows are a
    permutation of `S t`. `BgpStore` is the case of one graph
    (`BgpStore.scanStore`); `GRAPH ?g` as one scan is the case of the named
    graphs (`GraphBgpTableTheorems`). -/
structure ScanStore (st : Store Id) (P : Pat → Prop) (S : Pat → List IdRow) : Prop where
  perm : ∀ perm, perm < 4 → ∃ prb ms, PermMem st perm prb ms ∧
    ∀ t, P t → ((ms.flatMap (ScanFoldTheorems.blockRows prb)).filterMap (rowM t perm)).Perm (S t)
  scan : st.Sequential

theorem BgpStore.scanStore {st : Store Id} {gid : UInt64} {T : List IdPath.IdTriple} (h : BgpStore st gid T) :
    ScanStore st (fun t => t.g = .const gid) (fun t => scanRows (ipatOf t) T) := by
  refine ⟨fun perm hp => ?_, h.scan⟩
  obtain ⟨prb, ms, hpm, hP⟩ := h.perm perm hp
  refine ⟨prb, ms, hpm, fun t ht => ?_⟩
  rw [rowM_const t perm gid ht]
  exact List.Perm.filterMap _ hP

/-- One scan of the loop over a `ScanStore`: a table of the invariant whose
    rows are the model `S t`, up to order. -/
theorem scan_goodS (st : Store Id) (P : Pat → Prop) (S : Pat → List IdRow) (t : Pat) (perm : Nat)
    (hperm : perm < 4) (hP : P t) (hgs : GSlot t) (hmiss : t.hasMissing = false) (hst : ScanStore st P S) :
    ∃ tb stats, scanTableM st (mkSpec t perm (fun _ => true)) = pure (tb, stats) ∧ Good tb ∧
      IdEquiv tb.idRows (S t) := by
  obtain ⟨prb, ms, hpm, hPS⟩ := hst.perm perm hperm
  obtain ⟨tb, stats, he, hwf, hnu, hvars, hsv, hso, hpw⟩ :=
    scanTable_modelG st t perm hperm hgs hmiss prb ms hpm
  refine ⟨tb, stats, he, ⟨hwf, hnu, hso, fun v hv => ?_⟩, ?_⟩
  · rw [hsv] at hv
    apply idx_isSome_of_mem
    rw [hvars]
    exact sortVarOf_mem _ v hv
  · obtain ⟨A', hp, hw⟩ := Pw.perm_right hpw (hPS t hP)
    exact ⟨A', hp, hw⟩

/-- One scan of the loop: a table of the invariant whose rows are the
    model's scan of the pattern over `T`, up to order. -/
theorem scan_good (st : Store Id) (t : Pat) (perm : Nat) (hperm : perm < 4) (gid : UInt64)
    (T : List IdPath.IdTriple) (htg : t.g = .const gid) (hnamed : t.named = false) (hmiss : t.hasMissing = false)
    (hst : BgpStore st gid T) :
    ∃ tb stats, scanTableM st (mkSpec t perm (fun _ => true)) = pure (tb, stats) ∧ Good tb ∧
      IdEquiv tb.idRows (scanRows (ipatOf t) T) :=
  scan_goodS st (fun t => t.g = .const gid) (fun t => scanRows (ipatOf t) T) t perm hperm htg
    (Or.inl ⟨gid, htg, hnamed⟩) hmiss hst.scanStore

/-! ## The join loop (`IdQuery.bgpStepM`) -/

/-- The phase marks of issue 961 (`Store.markM`) have no effect over `Id`. -/
theorem markM_id (st : Store Id) (l : String) : st.markM l = pure () := by
  unfold Store.markM
  split <;> rfl

/-- A pattern of the loop: of the store's model (`P`), a graph slot of
    `GSlot`, no FROM merge or FROM NAMED, no constant without an id. -/
structure PatOk (P : Pat → Prop) (t : Pat) : Prop where
  p : P t
  gs : GSlot t
  plain : t.plain = true
  miss : t.hasMissing = false

theorem pickNext_mem (ests : Array Nat) (pats : Array Pat) (rem : Array Nat) (tab : Table)
    (h : rem.isEmpty = false) : pickNext ests pats rem tab ∈ rem.toList := by
  unfold pickNext
  simp only
  have pos : ∀ (a : Array Nat), a.isEmpty ≠ true → 0 < a.size := fun a ha =>
    Nat.pos_of_ne_zero (fun h0 => ha (Array.isEmpty_iff.mpr (Array.size_eq_zero_iff.mp h0)))
  have hsz : 0 < rem.size := pos rem (by rw [h]; decide)
  split
  · exact argmin_mem ests rem hsz
  · rename_i hc
    have hcsz : 0 < (rem.filter fun k => pats[k]!.vars.any tab.vars.contains).size := pos _ hc
    have := argmin_mem ests _ hcsz
    rw [Array.toList_filter] at this
    exact (List.mem_filter.mp this).1

theorem stepPerm_lt (t : Pat) (pats : Array Pat) (mv : Option (String × Nat)) : stepPerm t pats mv < 4 := by
  unfold stepPerm
  split <;> exact permFor_lt _ _

theorem scanPatM_plain (st : Store Id) (t : Pat) (ht : t.plain = true) (spec : ScanSpec) (keep : String → Bool)
    (left : Option Table) (est : Nat) :
    scanPatM st t spec keep left est =
      match left with
      | some l => scanForJoinM st spec l est
      | none => (do let (tb, s) ← scanTableOf st spec; pure (tb, s.full, "")) := by
  unfold scanPatM
  simp only [ht, if_true]
  rfl

theorem mergeVarOf_sortVar {tab : Table} {t : Pat} {v : String} {q : Nat} (h : mergeVarOf tab t = some (v, q)) :
    tab.sortVar = some v := by
  unfold mergeVarOf at h
  split at h
  · rename_i w hw
    rw [hw]
    cases hp : posOf t w with
    | none => rw [hp] at h; cases h
    | some q' =>
      rw [hp] at h
      simp only [Option.bind_some] at h
      split at h
      · cases h
      · cases h; rfl
  · cases h

/-- The join of the loop keeps the invariant and denotes SPARQL 1.1 Join. -/
theorem joinStep_good (tab rt : Table) (t : Pat) (gt : Good tab) (gr : Good rt) :
    Good (joinStep tab rt (mergeVarOf tab t)).1 ∧
      IdEquiv (joinStep tab rt (mergeVarOf tab t)).1.idRows (idJoin tab.idRows rt.idRows) := by
  unfold joinStep
  cases hmv : mergeVarOf tab t with
  | none => exact hashJoin_good tab rt gt gr
  | some p =>
    obtain ⟨v, q⟩ := p
    simp only
    split
    · rename_i hrv
      exact mergeJoin_good tab rt v gt gr (mergeVarOf_sortVar hmv) (by simpa using hrv)
    · exact hashJoin_good tab rt gt gr

/-- The contract of `Par.mapList` (issue 961) over `Id`: when set, it is
    `fun f xs => pure (xs.map f)`. The native driver runs it on the worker
    pool; that it meets the contract is tested (`tests/sbm11/threads.sh`),
    not proved. -/
def ParOk (par : Option (Par Id)) : Prop :=
  ∀ p, par = some p → ∀ mp, p.mapList = some mp →
    ∀ (α β : Type) (f : α → β) (xs : List α), mp f xs = pure (xs.map f)

theorem parOk_none : ParOk none := fun _ h => by cases h

/-- The next-scan hint of `evalBgpM` (stage 1o) does nothing in `Id`: a
    value of `Id Unit` is `()`. -/
theorem hintScanM_id (par : Option (Par Id)) (s : Option ScanSpec) :
    hintScanM par s = (pure () : ExceptT String Id Unit) := by
  unfold hintScanM
  split
  · split <;> rfl
  · rfl

/-- The join of the loop as executed (`joinStepM`, the merge join divided
    into ranges when `par` is set) is `joinStep`, for tables of the
    invariant (`Good`: the merge join columns are in non-decreasing order)
    and a `par` of `ParOk` (`WorkerPoolTheorems.mergeJoinParM_eq`). -/
theorem joinStepM_par (par : Option (Par Id)) (hpar : ParOk par) (tab rt : Table) (t : Pat)
    (gt : Good tab) (gr : Good rt) :
    joinStepM par tab rt (mergeVarOf tab t) = pure (joinStep tab rt (mergeVarOf tab t)) := by
  cases hmv : mergeVarOf tab t with
  | none => unfold joinStepM; rfl
  | some p =>
    obtain ⟨v, q⟩ := p
    unfold joinStepM joinStep
    simp only
    by_cases hrv : (rt.sortVar == some v) = true
    · rw [if_pos hrv, if_pos hrv]
      have hlv := mergeVarOf_sortVar hmv
      have hrv' : rt.sortVar = some v := by simpa using hrv
      obtain ⟨lc, hlc⟩ := Option.isSome_iff_exists.mp (gt.sv v hlv)
      obtain ⟨rc, hrc⟩ := Option.isSome_iff_exists.mp (gr.sv v hrv')
      have hA := gt.so v lc hlv hlc
      have hB := gr.so v rc hrv' hrc
      rw [mergeJoinParM_eq par tab rt v (fun p hp mp hmp xs => hpar p hp mp hmp _ _ _ xs)
        (by rw [hlc]; exact hA) (by rw [hrc]; exact hB), pure_bind]
    · rw [if_neg hrv, if_neg hrv]

/-! ## The right scan of a join, with candidates or without -/

open L4Factoidal.Storage.Sbm11.ScanTableTheorems (keep_eq_test specOk_mkSpec specAcc seenRow idRows_eq rows_fit
  rows_sorted scanTable_sortOk keptRows_pw seen_sortVar TableOf)

/-- **The right scan of a join** (`IdQuery.scanForJoinM`): with candidates
    from the left table when `sipRule` selects them and `sipCands` gives
    them (L4i, `SipTableTheorems.scanSipTableM_spec`), else the full scan.
    Either way the table is of the invariant `Good`, and its join with the
    left table is the join with rows `F` that are the model `S t` of the
    pattern, up to order (the semi-join reduction,
    `SemiJoin.idJoin_semijoin`: a right row whose join value is not a
    candidate joins no left row). -/
theorem scanForJoin_goodS (st : Store Id) (P : Pat → Prop) (S : Pat → List IdRow) (t : Pat) (perm : Nat)
    (hperm : perm < 4) (hP : P t) (hgs : GSlot t) (hmiss : t.hasMissing = false)
    (hst : ScanStore st P S) (tab : Table) (gt : Good tab) (est : Nat) :
    ∃ rt sc note, scanForJoinM st (mkSpec t perm (fun _ => true)) tab est = pure (rt, sc, note) ∧ Good rt ∧
      ∃ F, IdEquiv F (S t) ∧ idJoin tab.idRows rt.idRows = idJoin tab.idRows F := by
  obtain ⟨tb, stats, hsc, gtb, htb⟩ := scan_goodS st P S t perm hperm hP hgs hmiss hst
  have hfull : (do
      let x ← scanTableOf st (mkSpec t perm (fun _ => true))
      match x with
      | (t, s) => pure (t, s.full, "") : ExceptT String Id _) = pure (tb, stats.full, "") := by
    unfold scanTableOf
    rw [hst.scan.1]
    simp only []
    rw [hsc]
    rfl
  have hfullR : ∃ rt sc note, (do
      let x ← scanTableOf st (mkSpec t perm (fun _ => true))
      match x with
      | (t, s) => pure (t, s.full, "") : ExceptT String Id _) = pure (rt, sc, note) ∧ Good rt ∧
      ∃ F, IdEquiv F (S t) ∧ idJoin tab.idRows rt.idRows = idJoin tab.idRows F :=
    ⟨tb, _, _, hfull, gtb, tb.idRows, htb, rfl⟩
  unfold scanForJoinM
  cases hsv : sortVarOf (mkSpec t perm (fun _ => true)) with
  | none => exact hfullR
  | some v =>
    simp only []
    by_cases hc : (tab.vars.contains v && sipRule st.sipFactor tab.rows est) = true
    · rw [if_pos hc]
      cases hcand : sipCands tab v with
      | none => exact hfullR
      | some cands =>
        simp only []
        -- the scan with candidates
        have hspec := specOk_mkSpec t perm hmiss
        have hperm' : (mkSpec t perm (fun _ => true)).perm = perm := by rw [ScanTableTheorems.mkSpec_eq]; rfl
        obtain ⟨hs, c, hcidx, hcm⟩ := SipScanTheorems.sipCands_sound tab v cands hcand
        have hk : (mkSpec t perm (fun _ => true)).key.size < 4 := by
          have hv := hsv
          unfold sortVarOf at hv
          cases ho : (mkSpec t perm (fun _ => true)).outCols[0]? with
          | none => rw [ho] at hv; cases hv
          | some c0 =>
            rw [ho] at hv
            simp only at hv
            by_cases hce : (c0 == (mkSpec t perm (fun _ => true)).key.size) = true
            · have := hspec.outCols c0 (Array.mem_of_getElem? ho)
              have he : c0 = (mkSpec t perm (fun _ => true)).key.size := by simpa using hce
              omega
            · rw [if_neg hce] at hv; cases hv
        obtain ⟨prb, ms, hpm, hPS⟩ := hst.perm perm hperm
        have hP' := hPS t hP
        obtain ⟨T', stats', he', hT'⟩ := SipTableTheorems.scanSipTableM_spec st _ hspec hk cands hs prb ms
          (by rw [hperm']; exact hpm.range _) (by rw [hperm']; exact hpm.count) (by rw [hperm']; exact hpm.bytes)
          (by rw [hperm']; exact hpm.ovl) (by rw [hperm']; exact hpm.adm) hpm.blocks
        unfold scanSipTableOf
        rw [hst.scan.2]
        simp only []
        rw [he', pure_bind]
        refine ⟨T', _, _, rfl, ?_⟩
        generalize hR : ms.flatMap (ScanFoldTheorems.blockRows prb) = R at hT' hP'
        have hfitR : ∀ r ∈ R, ScanTableTheorems.Fits r := by rw [← hR]; exact rows_fit prb ms
        have hnzR : ∀ r ∈ R, ∀ c, c < 3 → rowCol r c ≠ 0 := by rw [← hR]; exact hpm.nz
        have hsorted : R.Pairwise (fun a b => a.lt b = true) := by
          rw [← hR]; exact rows_sorted prb ms hpm.adm hpm.blocks
        generalize hK : R.filter (fun r => ScanFoldTheorems.keep (mkSpec t perm (fun _ => true)) r &&
          SipScanTheorems.candOf (mkSpec t perm (fun _ => true)) cands r) = K at hT'
        have hKsub : ∀ r ∈ K, r ∈ R ∧ ScanFoldTheorems.keep (mkSpec t perm (fun _ => true)) r = true := by
          intro r hr
          rw [← hK] at hr
          obtain ⟨h1, h2⟩ := List.mem_filter.mp hr
          simp only [Bool.and_eq_true] at h2
          exact ⟨h1, h2.1⟩
        obtain ⟨hrows, hnu⟩ := idRows_eqG t perm hmiss hgs T' K hT'
          (fun r hr => hfitR r (hKsub r hr).1) (fun r hr => hnzR r (hKsub r hr).1) (fun r hr => (hKsub r hr).2)
        have hI := ScanTableTheorems.specInv_four t perm hmiss
        have hnd : T'.vars.toList.Nodup := by
          rw [hT'.vars, ScanTableTheorems.mkSpec_eq]
          show (specAcc t perm (fun _ => true)).outVars.toList.Nodup
          rw [hI.outVars]
          simpa using hI.nodup
        have hKs : K.Pairwise (fun a b => a.lt b = true) := by rw [← hK]; exact hsorted.filter _
        refine ⟨⟨⟨by rw [hT'.size, hT'.vars], hT'.bytes, hnd⟩, hnu,
          scanTable_sortOk t perm hmiss T' K hT' hKs (fun r hr => (hKsub r hr).2) hnd, fun w hw => ?_⟩, ?_⟩
        · rw [hT'.sortVar] at hw
          apply idx_isSome_of_mem
          rw [hT'.vars]
          exact sortVarOf_mem _ w hw
        · -- the rows: the full scan's, filtered by the candidates
          let F := (R.filter (ScanFoldTheorems.keep (mkSpec t perm (fun _ => true)))).map
            (seenRow (specAcc t perm (fun _ => true)))
          refine ⟨F, ?_, ?_⟩
          · obtain ⟨A', hp, hw⟩ := Pw.perm_right (keptRows_pwG t perm hperm hgs hmiss R hfitR) hP'
            exact ⟨A', hp, hw⟩
          · have hKF : T'.idRows = F.filter (SemiJoin.keepRow v (fun x => cands.contains x)) := by
              rw [hrows, ← hK, List.filter_map, List.filter_filter]
              congr 1
              apply List.filter_congr
              intro r _
              have e : (SemiJoin.keepRow v (fun x => cands.contains x) ∘ seenRow (specAcc t perm (fun _ => true))) r =
                  SipScanTheorems.candOf (mkSpec t perm (fun _ => true)) cands r := by
                simp only [Function.comp, SemiJoin.keepRow]
                rw [seen_sortVar t perm hmiss v hsv r]
                rfl
              rw [e, Bool.and_comm]
            rw [hKF]
            apply SemiJoin.idJoin_semijoin
            intro l hl
            unfold Table.idRows at hl
            obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
            have hi' := List.mem_range.mp hi
            refine ⟨tab.at c i, ?_, hcm i hi'⟩
            rw [TableTheorems.lookup_idRow tab gt.wf.nodup, TableTheorems.lookupAt_eq tab, hcidx]
            simp only [nz]
            rw [if_neg (by simpa using gt.nu c i (idx_some hcidx).1 hi')]
    · rw [if_neg hc]
      exact hfullR

/-- `scanForJoin_goodS` over one graph: `F` the model's scan of the pattern
    over `T`. -/
theorem scanForJoin_good (st : Store Id) (t : Pat) (perm : Nat) (hperm : perm < 4) (gid : UInt64)
    (T : List IdPath.IdTriple) (htg : t.g = .const gid) (hnamed : t.named = false) (hmiss : t.hasMissing = false)
    (hst : BgpStore st gid T) (tab : Table) (gt : Good tab) (est : Nat) :
    ∃ rt sc note, scanForJoinM st (mkSpec t perm (fun _ => true)) tab est = pure (rt, sc, note) ∧ Good rt ∧
      ∃ F, IdEquiv F (scanRows (ipatOf t) T) ∧ idJoin tab.idRows rt.idRows = idJoin tab.idRows F :=
  scanForJoin_goodS st (fun t => t.g = .const gid) (fun t => scanRows (ipatOf t) T) t perm hperm htg
    (Or.inl ⟨gid, htg, hnamed⟩) hmiss hst.scanStore tab gt est

/-- The model of the loop: the models `S t` of the patterns in the order
    given, joined left to right with `IdJoin.idJoin`. -/
def joinL (S : Pat → List IdRow) (ps : List Pat) (L : List IdRow) : List IdRow :=
  ps.foldl (fun acc t => idJoin acc (S t)) L

theorem joinL_snoc (S : Pat → List IdRow) (ps : List Pat) (t : Pat) (L : List IdRow) :
    joinL S (ps ++ [t]) L = idJoin (joinL S ps L) (S t) := by
  unfold joinL
  rw [List.foldl_append]
  rfl

theorem bgpJoin_joinL (T : List IdPath.IdTriple) (ps : List Pat) (L : List IdRow) :
    bgpJoin (fun _ => T) (ps.map ipatOf) L = joinL (fun t => scanRows (ipatOf t) T) ps L := by
  unfold bgpJoin joinL
  rw [List.foldl_map]

theorem nd_joinL (S : Pat → List IdRow) : ∀ (ps : List Pat) (L : List IdRow), (∀ r ∈ L, Nd r) →
    ∀ r ∈ joinL S ps L, Nd r
  | [], _, h => h
  | t :: ps, L, h => nd_joinL S ps _ (IdLeaf.nd_idJoin L (S t) h)

theorem joinL_empty (S : Pat → List IdRow) : ∀ (ps : List Pat), joinL S ps [] = []
  | [] => rfl
  | t :: ps => by
    show joinL S ps (idJoin [] (S t)) = []
    exact joinL_empty S ps

/-- A pattern whose model has no row: the joins have no row. -/
theorem joinL_nil (S : Pat → List IdRow) : ∀ (ps : List Pat) (L : List IdRow), (∃ t ∈ ps, S t = []) →
    joinL S ps L = []
  | [], _, ⟨_, h, _⟩ => by cases h
  | t :: ps, L, ⟨u, hu, he⟩ => by
    show joinL S ps (idJoin L (S t)) = []
    rcases List.mem_cons.mp hu with e | e
    · subst e
      rw [he]
      have : idJoin L [] = [] := by unfold idJoin; simp
      rw [this]
      exact joinL_empty S ps
    · exact joinL_nil S ps _ ⟨u, e, he⟩

/-- The invariant of the join loop after `k` steps: the patterns joined so
    far (`vis`) and the remaining ones are all the patterns, once each; the
    table is of the invariant `Good` and denotes the joins of the models of
    the patterns joined so far, in that order, up to order. -/
def LoopInv (pats : Array Pat) (S : Pat → List IdRow) (k : Nat) (s : BgpLoop) : Prop :=
  ∃ vis : List Nat, (vis ++ s.remaining.toList).Perm (List.range pats.size) ∧ s.remaining.toList.Nodup ∧
    s.remaining.size + k + 1 = pats.size ∧ Good s.tab ∧
    IdEquiv s.tab.idRows (joinL S (vis.map fun i => pats[i]!) [[]])

/-- The loop's end: every pattern joined. -/
def LoopDone (pats : Array Pat) (S : Pat → List IdRow) (s : BgpLoop) : Prop :=
  ∃ vis : List Nat, vis.Perm (List.range pats.size) ∧ Good s.tab ∧
    IdEquiv s.tab.idRows (joinL S (vis.map fun i => pats[i]!) [[]])

/-- **One step of the join loop.** -/
theorem bgpStep_spec (st : Store Id) (pats : Array Pat) (P : Pat → Prop) (S : Pat → List IdRow)
    (hst : ScanStore st P S) (hpats : ∀ i, i < pats.size → PatOk P pats[i]!) (ests : Array Nat)
    (par : Option (Par Id)) (hpar : ParOk par)
    (k : Nat) (s : BgpLoop) (hI : LoopInv pats S k s) :
    (∃ s', bgpStepM st pats (fun _ => true) ests s par = pure (.yield s') ∧ LoopInv pats S (k + 1) s') ∨
      (∃ s', bgpStepM st pats (fun _ => true) ests s par = pure (.done s') ∧ LoopDone pats S s') := by
  obtain ⟨vis, hperm, hnd, hcount, hgood, heq⟩ := hI
  by_cases hE : s.remaining.isEmpty = true
  · right
    refine ⟨s, ?_, ?_⟩
    · unfold bgpStepM
      simp [hE]
    · have h0 : s.remaining.toList = [] := by
        have := Array.isEmpty_iff.mp hE
        rw [this]
      rw [h0, List.append_nil] at hperm
      exact ⟨vis, hperm, hgood, heq⟩
  · left
    have hE' : s.remaining.isEmpty = false := by simpa using hE
    have hmem := pickNext_mem ests pats s.remaining s.tab hE'
    generalize hnext : pickNext ests pats s.remaining s.tab = next at hmem
    have hnlt : next < pats.size := by
      have := hperm.mem_iff.mp (List.mem_append_right _ hmem)
      exact List.mem_range.mp this
    have hok := hpats next hnlt
    have hpl := stepPerm_lt pats[next]! pats (mergeVarOf s.tab pats[next]!)
    obtain ⟨rt, sc, note, hsc, grt, F, hF, hjF⟩ := scanForJoin_goodS st P S pats[next]! _ hpl hok.p hok.gs
      hok.miss hst s.tab hgood ests[next]!
    obtain ⟨gj, hj⟩ := joinStep_good s.tab rt pats[next]! hgood grt
    apply Exists.intro
    constructor
    · unfold bgpStepM
      simp only [hE', Bool.false_eq_true, if_false]
      rw [hnext, scanPatM_plain st _ hok.plain]
      simp only []
      rw [hsc, pure_bind]
      simp only []
      rw [markM_id, pure_bind, joinStepM_par par hpar s.tab rt pats[next]! hgood grt, pure_bind]
      try simp only []
      rw [markM_id, pure_bind]
    · have hrp : s.remaining.toList.Perm (next :: s.remaining.toList.filter fun x => x != next) :=
        filter_ne_perm _ hnd next hmem
      refine ⟨vis ++ [next], ?_, ?_, ?_, gj, ?_⟩
      · simp only [Array.toList_filter]
        refine List.Perm.trans ?_ hperm
        rw [List.append_assoc, List.singleton_append]
        exact List.Perm.append_left _ hrp.symm
      · simp only [Array.toList_filter]
        exact hnd.filter _
      · have hl := hrp.length_eq
        rw [List.length_cons, Array.length_toList] at hl
        have hf : (s.remaining.filter fun x => x != next).size =
            (s.remaining.toList.filter fun x => x != next).length := by
          rw [← Array.length_toList, Array.toList_filter]
        show (s.remaining.filter fun x => x != next).size + (k + 1) + 1 = pats.size
        rw [hf]
        omega
      · rw [List.map_append, List.map_singleton, joinL_snoc]
        refine IdEquiv.trans hj ?_
        rw [hjF]
        exact idJoin_equiv heq hF (nd_idRows s.tab hgood.wf.nodup)
          (nd_joinL S _ [[]] (fun r hr => by
            rw [List.mem_singleton] at hr; subst hr; exact List.nodup_nil))

/-- The loop from a state of the invariant ends with every pattern joined:
    the table denotes the joins of the models of the patterns in some order,
    up to order. -/
theorem loop_final (st : Store Id) (pats : Array Pat) (P : Pat → Prop) (S : Pat → List IdRow)
    (hst : ScanStore st P S) (hok : ∀ i, i < pats.size → PatOk P pats[i]!) (ests : Array Nat)
    (par : Option (Par Id)) (hpar : ParOk par)
    (s0 : BgpLoop) (h0 : LoopInv pats S 0 s0) :
    ∃ tab lines stats,
      (do
        let s ← forIn (List.range' 0 pats.size) s0 (fun _ s => bgpStepM st pats (fun _ => true) ests s par)
        pure (s.tab, s.lines, s.total)) = (pure (tab, lines, stats) : ExceptT String Id _) ∧
      tab.WF ∧ (∀ r ∈ tab.idRows, Nd r) ∧ ∃ vis : List Nat, vis.Perm (List.range pats.size) ∧
        IdEquiv tab.idRows (joinL S (vis.map fun i => pats[i]!) [[]]) := by
  obtain ⟨b, hfor, hb⟩ := forIn_exc (LoopInv pats S) (LoopDone pats S)
    (fun _ s => bgpStepM st pats (fun _ => true) ests s par) pats.size 0 s0 h0
    (fun a b _ _ hP => bgpStep_spec st pats P S hst hok ests par hpar a b hP)
  rw [hfor, pure_bind]
  refine ⟨b.tab, b.lines, b.total, rfl, ?_⟩
  have hdone : LoopDone pats S b := by
    rcases hb with hP | hQ
    · obtain ⟨_, _, _, hc, _⟩ := hP; omega
    · exact hQ
  obtain ⟨vis, hvis, hg, he⟩ := hdone
  exact ⟨hg.wf, nd_idRows b.tab hg.wf.nodup, vis, hvis, he⟩

/-! ## A constant with no id -/

theorem matchSlots_missing : ∀ (S : List (IdLeaf.ISlot × UInt64)) (r : IdRow) (y : UInt64),
    (IdLeaf.ISlot.missing, y) ∈ S → IdLeaf.matchSlots S r = none
  | [], _, _, h => by cases h
  | (s, z) :: rest, r, y, h => by
    simp only [IdLeaf.matchSlots]
    rcases List.mem_cons.mp h with e | e
    · cases e; rfl
    · cases IdLeaf.slotMatch s z r with
      | none => rfl
      | some r1 => exact matchSlots_missing rest r1 y e

/-- A triple pattern with a constant that has no id. -/
def IMiss (t : IPat) : Prop := t.s = .missing ∨ t.p = .missing ∨ t.o = .missing

theorem idEvalTP_missing (t : IPat) (ht : IMiss t) (T : List IdPath.IdTriple) (r : IdRow) :
    IdLeaf.idEvalTP t T r = [] := by
  unfold IdLeaf.idEvalTP
  rw [List.filterMap_eq_nil_iff]
  intro x _
  unfold IdLeaf.idTpMatch IPat.slots
  rcases ht with h | h | h
  · exact matchSlots_missing _ r x.1 (by rw [h]; simp)
  · exact matchSlots_missing _ r x.2.1 (by rw [h]; simp)
  · exact matchSlots_missing _ r x.2.2 (by rw [h]; simp)

theorem idBgpFrom_missing (T : List IdPath.IdTriple) :
    ∀ (ps : List IPat) (r : IdRow), (∃ t ∈ ps, IMiss t) → IdLeaf.idBgpFrom T ps r = []
  | [], _, h => by obtain ⟨_, h, _⟩ := h; cases h
  | t :: ps, r, ⟨u, hu, hm⟩ => by
    simp only [IdLeaf.idBgpFrom]
    rcases List.mem_cons.mp hu with e | e
    · subst e; rw [idEvalTP_missing u hm]; rfl
    · rw [List.flatMap_eq_nil_iff]
      intro r' _
      exact idBgpFrom_missing T ps r' ⟨u, e, hm⟩

theorem slot_beq_missing (x : Slot) (h : (x == .missing) = true) : x = .missing := by
  cases x with
  | missing => rfl
  | var v => cases h
  | const c => cases h

theorem iMiss_of (gid : UInt64) (t : Pat) (hg : t.g = .const gid) (h : t.hasMissing = true) : IMiss (ipatOf t) := by
  unfold Pat.hasMissing at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((h | h) | h) | h
  · left; show ScanTableTheorems.islot t.s = _; rw [slot_beq_missing _ h]; rfl
  · right; left; show ScanTableTheorems.islot t.p = _; rw [slot_beq_missing _ h]; rfl
  · right; right; show ScanTableTheorems.islot t.o = _; rw [slot_beq_missing _ h]; rfl
  · rw [slot_beq_missing _ h] at hg; cases hg

/-! ## The basic graph pattern -/

/-- A pattern of a basic graph pattern over the graph `gid`. -/
structure PatG (gid : UInt64) (t : Pat) : Prop where
  g : t.g = .const gid
  named : t.named = false
  plain : t.plain = true

theorem forIn_arr_exc {α β : Type} (xs : Array α) (b : β) (f : α → β → ExceptT String Id (ForInStep β))
    (hf : ∀ a b, ∃ b', f a b = pure (.yield b')) : ∃ b', forIn xs b f = pure b' := by
  rw [← Array.forIn_toList]
  exact forIn_exc_list f hf xs.toList b

/-- The variables of the patterns, each once (the fold `evalBgpM` gives the
    columns of an empty answer). -/
theorem varsFold_nodup (pats : Array Pat) :
    (pats.foldl (fun a t => t.vars.foldl (fun a v => if a.contains v then a else a.push v) a)
      (#[] : Array String)).toList.Nodup := by
  have inner : ∀ (vs : List String) (a : Array String), a.toList.Nodup →
      (vs.foldl (fun a v => if a.contains v then a else a.push v) a).toList.Nodup := by
    intro vs
    induction vs with
    | nil => intro a h; exact h
    | cons v rest ih =>
      intro a h
      rw [List.foldl_cons]
      apply ih
      split
      · exact h
      · next hc =>
        rw [Array.toList_push, List.nodup_append]
        refine ⟨h, by simp, ?_⟩
        intro x hx y hy e
        rw [List.mem_singleton] at hy
        subst hy; subst e
        exact hc (Array.contains_iff_mem.mpr (Array.mem_toList_iff.mp hx))
  rw [← Array.foldl_toList]
  generalize pats.toList = ps
  have : ∀ (a : Array String), a.toList.Nodup → (ps.foldl (fun a t =>
      t.vars.foldl (fun a v => if a.contains v then a else a.push v) a) a).toList.Nodup := by
    induction ps with
    | nil => intro a h; exact h
    | cons t rest ih =>
      intro a h
      rw [List.foldl_cons]
      apply ih
      rw [← Array.foldl_toList]
      exact inner _ a h
  exact this #[] List.nodup_nil

theorem empty_wf (vars : Array String) (h : vars.toList.Nodup) : (Table.empty vars).WF :=
  ⟨by simp [Table.empty], fun c hc => by simp [Table.empty], h⟩

/-- **`evalBgpM` over a `ScanStore`.** For patterns of the store's model
    (`P`), each with a graph slot of `GSlot` and no FROM merge or FROM NAMED,
    whose model has no row when the pattern has a constant with no id,
    `evalBgpM` returns a well-formed table whose rows bind no variable twice
    and denote the joins of the models of the patterns in some order, up to
    order. -/
theorem evalBgpM_modelS_par (st : Store Id) (pats : Array Pat) (hne : 0 < pats.size) (P : Pat → Prop)
    (S : Pat → List IdRow) (hst : ScanStore st P S)
    (hpats : ∀ i, i < pats.size → P pats[i]! ∧ GSlot pats[i]! ∧ pats[i]!.plain = true)
    (hmissS : ∀ t, P t → t.hasMissing = true → S t = []) (par : Option (Par Id)) (hpar : ParOk par) :
    ∃ tab lines stats, evalBgpM st pats (fun _ => true) none none par = pure (tab, lines, stats) ∧
      tab.WF ∧ (∀ r ∈ tab.idRows, Nd r) ∧ ∃ vis : List Nat, vis.Perm (List.range pats.size) ∧
        IdEquiv tab.idRows (joinL S (vis.map fun i => pats[i]!) [[]]) := by
  unfold evalBgpM
  simp only [Bool.true_or]
  have hne' : pats.isEmpty = false := by
    cases h : pats.isEmpty
    · rfl
    · have := Array.isEmpty_iff.mp h; subst this; simp at hne
  by_cases hm : (pats.any fun x => x.hasMissing) = true
  · simp only [hne', hm, Bool.false_eq_true, if_false, if_true]
    refine ⟨_, _, _, rfl, empty_wf _ (by rw [Array.toList_filter]; exact (varsFold_nodup pats).filter _),
      fun r hr => by simp [Table.idRows, Table.empty] at hr, List.range pats.size, List.Perm.refl _, ?_⟩
    have hrows : (Table.empty ((pats.foldl (fun a t => t.vars.foldl
        (fun a v => if a.contains v then a else a.push v) a) #[]).filter fun _ => true)).idRows = [] := by
      simp [Table.idRows, Table.empty]
    rw [hrows]
    obtain ⟨i, hi, him⟩ := Array.any_eq_true.mp hm
    rw [joinL_nil S _ _ ⟨pats[i]!, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩,
      hmissS _ (hpats i hi).1 (by rw [getElem!_pos pats i hi]; exact him)⟩]
    exact IdEquiv.refl []
  · have hm' : (pats.any fun x => x.hasMissing) = false := by simpa using hm
    simp only [hne', hm', Bool.false_eq_true, if_false]
    have hnomiss : ∀ i, i < pats.size → pats[i]!.hasMissing = false := by
      intro i hi
      have := Array.any_eq_false.mp hm' i hi
      rw [getElem!_pos pats i hi]; simpa using this
    have hok : ∀ i, i < pats.size → PatOk P pats[i]! := fun i hi =>
      ⟨(hpats i hi).1, (hpats i hi).2.1, (hpats i hi).2.2, hnomiss i hi⟩
    -- the estimates
    obtain ⟨ests, hests⟩ := forIn_arr_exc pats (#[] : Array Nat)
      (fun t (r : Array Nat) => do
        let x ← st.blocksForRange (mkSpec t (permFor t none) fun _ => true).perm
          (mkSpec t (permFor t none) fun _ => true).key
        pure (ForInStep.yield (r.push (selRows x))))
      (fun a b => by
        obtain ⟨prb, ms, hpm, _⟩ := hst.perm _ (permFor_lt a none)
        have hperm : (mkSpec a (permFor a none) fun _ => true).perm = permFor a none := by
          rw [ScanTableTheorems.mkSpec_eq]; rfl
        apply Exists.intro
        rw [hperm, hpm.range]
        rfl)
    rw [hests, pure_bind]
    -- the first scan
    have hrange : ∀ k, k ∈ (List.range pats.size).toArray.toList ↔ k < pats.size := by
      intro k; simp
    have hfirst := argmin_mem ests (List.range pats.size).toArray (by simpa using hne)
    generalize Array.foldl (fun b k => if ests[k]! < ests[b]! then k else b) (List.range pats.size).toArray[0]!
      (List.range pats.size).toArray = first at hfirst ⊢
    have hfl : first < pats.size := (hrange first).mp hfirst
    have hp0 := permFor_lt pats[first]! (match none.bind (posOf pats[first]!) with
      | some q => some q
      | none => bestSortPos pats[first]! pats)
    generalize permFor pats[first]! (match none.bind (posOf pats[first]!) with
      | some q => some q
      | none => bestSortPos pats[first]! pats) = p0 at hp0 ⊢
    have hok0 := hok first hfl
    obtain ⟨tb0, stats0, hsc0, g0, he0⟩ := scan_goodS st P S pats[first]! p0 hp0 hok0.p hok0.gs hok0.miss hst
    rw [hintScanM_id, pure_bind]
    rw [scanPatM_plain st _ hok0.plain]
    simp only []
    unfold scanTableOf
    rw [hst.scan.1]
    simp only []
    rw [hsc0, pure_bind]
    simp only []
    rw [markM_id, pure_bind]
    simp only []
    rw [pure_bind]
    -- the loop
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    have hI0 : ∀ ls, LoopInv pats S 0 (BgpLoop.mk ((List.range pats.size).toArray.filter (· != first))
        ls stats0.full tb0) := by
      intro ls
      have hrp := filter_ne_perm (List.range pats.size) List.nodup_range first (List.mem_range.mpr hfl)
      refine ⟨[first], ?_, ?_, ?_, g0, ?_⟩
      · simp only [Array.toList_filter]
        exact hrp.symm
      · simp only [Array.toList_filter]
        exact List.nodup_range.filter _
      · have hl := hrp.length_eq
        rw [List.length_cons, List.length_range] at hl
        have hf : ((List.range pats.size).toArray.filter fun x => x != first).size =
            ((List.range pats.size).filter fun x => x != first).length := by
          rw [← Array.length_toList, Array.toList_filter, List.toList_toArray]
        show ((List.range pats.size).toArray.filter fun x => x != first).size + 0 + 1 = pats.size
        rw [hf]; omega
      · show IdEquiv tb0.idRows (idJoin [[]] (S pats[first]!))
        exact IdEquiv.trans he0 (idJoin_unit _).symm
    apply loop_final st pats P S hst hok ests par hpar
    exact hI0 _

theorem evalBgpM_modelS (st : Store Id) (pats : Array Pat) (hne : 0 < pats.size) (P : Pat → Prop)
    (S : Pat → List IdRow) (hst : ScanStore st P S)
    (hpats : ∀ i, i < pats.size → P pats[i]! ∧ GSlot pats[i]! ∧ pats[i]!.plain = true)
    (hmissS : ∀ t, P t → t.hasMissing = true → S t = []) :
    ∃ tab lines stats, evalBgpM st pats (fun _ => true) = pure (tab, lines, stats) ∧
      tab.WF ∧ (∀ r ∈ tab.idRows, Nd r) ∧ ∃ vis : List Nat, vis.Perm (List.range pats.size) ∧
        IdEquiv tab.idRows (joinL S (vis.map fun i => pats[i]!) [[]]) :=
  evalBgpM_modelS_par st pats hne P S hst hpats hmissS none parOk_none

theorem evalBgpM_model_par (st : Store Id) (pats : Array Pat) (hne : 0 < pats.size) (gid : UInt64)
    (T : List IdPath.IdTriple) (hst : BgpStore st gid T) (hpats : ∀ i, i < pats.size → PatG gid pats[i]!)
    (par : Option (Par Id)) (hpar : ParOk par) :
    ∃ tab lines stats, evalBgpM st pats (fun _ => true) none none par = pure (tab, lines, stats) ∧
      tab.WF ∧ (∀ r ∈ tab.idRows, Nd r) ∧ IdEquiv tab.idRows (IdLeaf.idBgpFrom T (pats.toList.map ipatOf) []) := by
  obtain ⟨tab, lines, stats, he, hwf, hnd, vis, hvis, heq⟩ := evalBgpM_modelS_par st pats hne
    (fun t => t.g = .const gid) (fun t => scanRows (ipatOf t) T) hst.scanStore
    (fun i hi => ⟨(hpats i hi).g, Or.inl ⟨gid, (hpats i hi).g, (hpats i hi).named⟩, (hpats i hi).plain⟩)
    (fun t ht hm => idEvalTP_missing _ (iMiss_of gid t ht hm) T []) par hpar
  refine ⟨tab, lines, stats, he, hwf, hnd, ?_⟩
  rw [← bgpJoin_joinL, List.map_map] at heq
  have hnd0 : ∀ r ∈ ([[]] : List IdRow), Nd r := by
    intro r hr
    simp only [List.mem_singleton] at hr
    subst hr
    exact List.nodup_nil
  have h1 := IdLeaf.bgpJoin_equiv T (fun _ => T) (fun _ => List.Perm.refl T)
    (vis.map (ipatOf ∘ fun i => pats[i]!)) [[]] hnd0
  rw [List.flatMap_singleton] at h1
  have hps : (vis.map (ipatOf ∘ fun i => pats[i]!)).Perm (pats.toList.map ipatOf) := by
    have : pats.toList.map ipatOf = (List.range pats.size).map (ipatOf ∘ fun i => pats[i]!) := by
      apply List.ext_getElem
      · simp
      · intro n h1 h2
        simp only [List.getElem_map, List.getElem_range, Array.getElem_toList, Function.comp]
        rw [getElem!_pos pats n (by simpa using h1)]
    rw [this]
    exact hvis.map _
  exact IdEquiv.trans heq (IdEquiv.trans h1 (IdLeaf.idBgpFrom_perm T hps [] [] (TableTheorems.RowEq.refl _)))

/-- **`evalBgpM` against the model**, single-thread join (`par = none`):
    `evalBgpM_model_par` with `parOk_none`. -/
theorem evalBgpM_model (st : Store Id) (pats : Array Pat) (hne : 0 < pats.size) (gid : UInt64)
    (T : List IdPath.IdTriple) (hst : BgpStore st gid T) (hpats : ∀ i, i < pats.size → PatG gid pats[i]!) :
    ∃ tab lines stats, evalBgpM st pats (fun _ => true) = pure (tab, lines, stats) ∧
      tab.WF ∧ (∀ r ∈ tab.idRows, Nd r) ∧ IdEquiv tab.idRows (IdLeaf.idBgpFrom T (pats.toList.map ipatOf) []) :=
  evalBgpM_model_par st pats hne gid T hst hpats none parOk_none

end L4Factoidal.Storage.Sbm11.BgpTableTheorems

#print axioms L4Factoidal.Storage.Sbm11.BgpTableTheorems.evalBgpM_model
#print axioms L4Factoidal.Storage.Sbm11.BgpTableTheorems.evalBgpM_model_par
#print axioms L4Factoidal.Storage.Sbm11.BgpTableTheorems.evalBgpM_modelS_par
#print axioms L4Factoidal.Storage.Sbm11.BgpTableTheorems.joinStepM_par
#print axioms L4Factoidal.Storage.Sbm11.BgpTableTheorems.evalBgpM_modelS
#print axioms L4Factoidal.Storage.Sbm11.BgpTableTheorems.bgpStep_spec
#print axioms L4Factoidal.Storage.Sbm11.BgpTableTheorems.idJoin_equiv
#print axioms L4Factoidal.Storage.Sbm11.BgpTableTheorems.hashJoin_good
#print axioms L4Factoidal.Storage.Sbm11.BgpTableTheorems.mergeJoin_good
#print axioms L4Factoidal.Storage.Sbm11.BgpTableTheorems.scanForJoin_good
