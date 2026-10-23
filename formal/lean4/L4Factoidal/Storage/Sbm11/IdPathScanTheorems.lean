/-
L4Factoidal.Storage.Sbm11.IdPathScanTheorems — the scans of the property path
evaluator on ids (`IdQuery.pathScanM`, `pairsOf`, `nodesAmongM`,
`allNodesM`, `pathFuelM`) against the listing of the graph
(https://github.com/danbri/factoidal/issues/776; part of lemma L4n of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

A path step scans one permutation of graph `gid` with the pattern
`?s P ?o` (`P` a predicate id or the variable `?p`), with candidates on the
permutation's first unbound column when a restriction is given. Over a store
of `BgpStore` (each permutation in memory, `PermMem`, its listing of the
graph a permutation of `T`):

* `pathScan_rows`: the table's rows are, row for row (`Pw RowEq`), the
  model's scan of the pattern over the permutation's listing, the rows whose
  sort variable is not a candidate removed.
* `pairsOf_eq`: the pairs `pairsOf` reads from a table are the pairs of the
  lookups of its rows.
* `pathScan_link`, `pathScan_all`: the pairs of a one-step scan and of a
  scan of every triple, up to order, are the triples of `T` the restriction
  (`Restr`) keeps.
* `allNodes_spec`, `nodesAmong_spec`: the nodes of the graph
  (`IdPath.idGraphNodes`), in increasing order, each once; among the
  restriction for `nodesAmongM`.
* `pathFuel_ge`: the round bound of a closure is above the number of nodes
  of the graph plus the size of the restriction.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdPathPureTheorems
import L4Factoidal.Storage.Sbm11.BgpTableTheorems

namespace L4Factoidal.Storage.Sbm11.IdPathScanTheorems

open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdPath (IdTriple IdPairs Pairs idGraphNodes)
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup unbound)
open L4Factoidal.Storage.Sbm11.TableTheorems (RowEq NoUnbound)
open L4Factoidal.Storage.Sbm11.IdGroup (Pw)
open L4Factoidal.Storage.Sbm11.IdLeaf (scanRows matchSlots slotMatch ISlot)
open L4Factoidal.Storage.Sbm11.ScanTableTheorems (PermMem permListing ipatOf scanTable_model)
open L4Factoidal.Storage.Sbm11.BgpTableTheorems (BgpStore)

/-! ## The restriction -/

/-- The pairs a restriction keeps: `none` every pair; `some rs` with `fwd`
    the pairs whose subject is in `rs`, without `fwd` those whose object is. -/
def Restr (fwd : Bool) (R : Option (Array UInt64)) (p : UInt64 × UInt64) : Bool :=
  match R with
  | none => true
  | some rs => if fwd then rs.contains p.1 else rs.contains p.2

/-- The pattern of a path scan (`pathScanM`). -/
def pathPat (g : UInt64) (pid : Option UInt64) : Pat :=
  { s := .var "s", p := (match pid with | some x => .const x | none => .var "p"),
    o := .var "o", g := .const g, named := false }

/-! ## Rows element for element -/

theorem pw_map_eq {β : Type} (f : IdRow → β) (hf : ∀ r s, RowEq r s → f r = f s) :
    ∀ {A B : List IdRow}, Pw RowEq A B → A.map f = B.map f
  | _, _, .nil => rfl
  | _, _, .cons h t => by simp [hf _ _ h, pw_map_eq f hf t]

theorem pw_filter (q : IdRow → Bool) (hq : ∀ r s, RowEq r s → q r = q s) :
    ∀ {A B : List IdRow}, Pw RowEq A B → Pw RowEq (A.filter q) (B.filter q)
  | _, _, .nil => .nil
  | _, _, .cons h t => by
    simp only [List.filter_cons]
    rw [hq _ _ h]
    split
    · exact .cons h (pw_filter q hq t)
    · exact pw_filter q hq t

theorem pw_nil_right {A : List IdRow} (h : Pw RowEq A []) : A = [] := by
  cases h; rfl

/-! ## `pairsOf` -/

/-- The two lookups of a row, `0` for an unbound variable. -/
def proj2 (a b : String) (r : IdRow) : UInt64 × UInt64 := ((idLookup a r).getD 0, (idLookup b r).getD 0)

theorem pairsOf_loop (t : Table) (ca cb : Nat) :
    (Id.run do
      let mut out : Pairs := Array.mkEmpty t.rows
      for i in [0:t.rows] do
        out := out.push (t.at ca i, t.at cb i)
      return out).toList = (List.range t.rows).map (fun i => (t.at ca i, t.at cb i)) := by
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  generalize hF : forIn (m := Id) (List.range' 0 t.rows) (Array.mkEmpty t.rows : Pairs) _ = F
  have := TableTheorems.forIn_range_inv t.rows
    (fun k (out : Pairs) => out.toList = (List.range k).map (fun i => (t.at ca i, t.at cb i))) hF
    (by simp) (fun k out _ h => ⟨_, rfl, by simp [h, List.range_succ]⟩)
  exact this

theorem idx_of_lookup {t : Table} (hnd : t.vars.toList.Nodup) {i : Nat} {v : String}
    (h : (idLookup v (t.idRow i)).isSome) : ∃ c, t.idx v = some c := by
  rw [TableTheorems.lookup_idRow t hnd, TableTheorems.lookupAt_eq] at h
  cases e : t.idx v with
  | none => rw [e] at h; cases h
  | some c => exact ⟨c, rfl⟩

theorem lookup_at {t : Table} (hnd : t.vars.toList.Nodup) (hnu : NoUnbound t) {i c : Nat} {v : String}
    (hi : i < t.rows) (hc : t.idx v = some c) : idLookup v (t.idRow i) = some (t.at c i) := by
  rw [TableTheorems.lookup_idRow t hnd, TableTheorems.lookupAt_eq, hc]
  have := hnu c i (TableTheorems.idx_some hc).1 hi
  simp [TableTheorems.nz, this]

/-- **`pairsOf`**: the pairs of the lookups of the rows. -/
theorem pairsOf_eq (t : Table) (hnd : t.vars.toList.Nodup) (hnu : NoUnbound t) (M : List IdRow)
    (hpw : Pw RowEq t.idRows M) (a b : String)
    (hM : ∀ r ∈ M, (idLookup a r).isSome ∧ (idLookup b r).isSome) :
    (pairsOf t a b).toList = M.map (proj2 a b) := by
  have hmap : t.idRows.map (proj2 a b) = M.map (proj2 a b) :=
    pw_map_eq _ (fun r s h => by simp [proj2, h a, h b]) hpw
  rw [← hmap]
  by_cases h0 : t.rows = 0
  · have : t.idRows = [] := by simp [Table.idRows, h0]
    rw [this]
    unfold pairsOf
    split
    · rw [pairsOf_loop, h0]; rfl
    · rfl
  · have hlen := Pw.length_eq hpw
    have hl0 : 0 < M.length := by rw [← hlen, TableTheorems.idRows_length]; omega
    have hr0 := hM M[0] (List.getElem_mem hl0)
    have hrow0 : t.idRows[0]! = t.idRow 0 := TableTheorems.idRows_get t 0 (by omega)
    -- the lookups of row 0 of the table are those of the first row of `M`
    have hrel : RowEq (t.idRow 0) M[0] := by
      have : ∀ {A B : List IdRow}, Pw RowEq A B → ∀ k (hk : k < B.length), RowEq A[k]! B[k] := by
        intro A B h
        induction h with
        | nil => intro k hk; cases hk
        | cons hab _ ih =>
          intro k hk
          cases k with
          | zero => simpa using hab
          | succ k => simpa using ih k (by simpa using hk)
      rw [← hrow0]; exact this hpw 0 hl0
    obtain ⟨ca, hca⟩ := idx_of_lookup hnd (v := a) (i := 0) (by rw [hrel a]; exact hr0.1)
    obtain ⟨cb, hcb⟩ := idx_of_lookup hnd (v := b) (i := 0) (by rw [hrel b]; exact hr0.2)
    unfold pairsOf
    rw [hca, hcb]
    simp only []
    rw [pairsOf_loop]
    unfold Table.idRows
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp hi
    simp [proj2, lookup_at hnd hnu hi' hca, lookup_at hnd hnu hi' hcb]

/-! ## One scan -/

/-- The candidate test of a restriction on the sort variable `sv`. -/
def candR (sv : String) : Option (Array UInt64) → IdRow → Bool
  | none, _ => true
  | some cs, r => SemiJoin.keepRow sv (fun x => cs.contains x) r

theorem candR_congr (sv : String) (R : Option (Array UInt64)) (r s : IdRow) (h : RowEq r s) :
    candR sv R r = candR sv R s := by
  cases R with
  | none => rfl
  | some cs => simp only [candR, SemiJoin.keepRow, h sv]

theorem pathPat_miss (g : UInt64) (pid : Option UInt64) : (pathPat g pid).hasMissing = false := by
  cases pid <;> rfl

theorem pathScanM_eq (st : Store Id) (g : UInt64) (pid : Option UInt64) (perm : Nat) (R : Option (Array UInt64)) :
    pathScanM st g pid perm R =
      match R with
      | some cs =>
        if cs.isEmpty then pure (Table.empty (mkSpec (pathPat g pid) perm (fun _ => true)).outVars, {})
        else do
          let (tb, s) ← scanSipTableM st (mkSpec (pathPat g pid) perm (fun _ => true)) cs
          return (tb, s.withSip)
      | none => do
        let (tb, s) ← scanTableOf st (mkSpec (pathPat g pid) perm (fun _ => true))
        return (tb, s.full) := rfl

/-- **One scan of a path step.** The table of `pathScanM` from permutation
    `perm` of an in-memory store: no variable twice, no id 0, and its rows
    are, row for row, the model's scan of the pattern over the
    permutation's listing of the graph whose sort variable `sv` holds a
    candidate. -/
theorem pathScan_rows (st : Store Id) (g : UInt64) (pid : Option UInt64) (perm : Nat) (hperm : perm < 4)
    (sv : String) (hsv : sortVarOf (mkSpec (pathPat g pid) perm (fun _ => true)) = some sv)
    (hk : (mkSpec (pathPat g pid) perm (fun _ => true)).key.size < 4)
    (prb : ByteArray) (ms : List Block.BlockMeta) (hpm : PermMem st perm prb ms) (hscan : st.scanTable = none)
    (R : Option (Array UInt64)) (hR : ∀ cs, R = some cs → Sip.Sorted cs) :
    ∃ t s, pathScanM st g pid perm R = pure (t, s) ∧ t.vars.toList.Nodup ∧ NoUnbound t ∧
      Pw RowEq t.idRows ((scanRows (ipatOf (pathPat g pid))
        (permListing perm g (ms.flatMap (ScanFoldTheorems.blockRows prb)))).filter (candR sv R)) := by
  have hmiss := pathPat_miss g pid
  have htg : (pathPat g pid).g = .const g := rfl
  have hnamed : (pathPat g pid).named = false := rfl
  have hI := ScanTableTheorems.specInv_four (pathPat g pid) perm hmiss
  have hndv : (mkSpec (pathPat g pid) perm (fun _ => true)).outVars.toList.Nodup := by
    rw [ScanTableTheorems.mkSpec_eq]
    show (ScanTableTheorems.specAcc (pathPat g pid) perm (fun _ => true)).outVars.toList.Nodup
    rw [hI.outVars]
    simpa using hI.nodup
  generalize hR0 : ms.flatMap (ScanFoldTheorems.blockRows prb) = Rw
  have hfitR : ∀ r ∈ Rw, ScanTableTheorems.Fits r := by rw [← hR0]; exact ScanTableTheorems.rows_fit prb ms
  have hnzR : ∀ r ∈ Rw, ∀ c, c < 3 → rowCol r c ≠ 0 := by rw [← hR0]; exact hpm.nz
  have hkept := ScanTableTheorems.keptRows_pw (pathPat g pid) perm hperm g htg hnamed hmiss Rw hfitR
  -- every row of the model binds the sort variable
  have hsvm : ∀ r ∈ scanRows (ipatOf (pathPat g pid)) (permListing perm g Rw), (idLookup sv r).isSome := by
    intro r hr
    have : ∀ {A B : List IdRow}, Pw RowEq A B → ∀ r ∈ B, ∃ a ∈ A, RowEq a r := by
      intro A B h
      induction h with
      | nil => intro r hr; cases hr
      | cons hab _ ih =>
        intro r hr
        rcases List.mem_cons.mp hr with e | e
        · subst e; exact ⟨_, List.mem_cons_self, hab⟩
        · obtain ⟨a, ha, hra⟩ := ih r e; exact ⟨a, List.mem_cons_of_mem _ ha, hra⟩
    obtain ⟨a, ha, hra⟩ := this hkept r hr
    obtain ⟨row, _, rfl⟩ := List.mem_map.mp ha
    rw [← hra sv, ScanTableTheorems.seen_sortVar (pathPat g pid) perm hmiss sv hsv row]
    rfl
  rw [pathScanM_eq]
  cases R with
  | none =>
    obtain ⟨T, stats, he, hwf, hnu, _, _, _, hpw⟩ :=
      scanTable_model st (pathPat g pid) perm hperm g htg hnamed hmiss prb ms hpm
    refine ⟨T, stats.full, ?_, hwf.nodup, hnu, ?_⟩
    · unfold scanTableOf
      rw [hscan]
      simp only []
      rw [he]
      rfl
    · rw [hR0] at hpw
      have : (scanRows (ipatOf (pathPat g pid)) (permListing perm g Rw)).filter (candR sv none) =
          scanRows (ipatOf (pathPat g pid)) (permListing perm g Rw) :=
        List.filter_eq_self.mpr (fun _ _ => rfl)
      rw [this]
      exact hpw
  | some cs =>
    dsimp only
    by_cases hce : cs.isEmpty = true
    · rw [if_pos hce]
      refine ⟨_, _, rfl, hndv, fun c i _ hi => absurd hi (by simp [Table.empty]), ?_⟩
      have h1 : (Table.empty (mkSpec (pathPat g pid) perm (fun _ => true)).outVars).idRows = [] := by
        simp [Table.idRows, Table.empty]
      have h2 : (scanRows (ipatOf (pathPat g pid)) (permListing perm g Rw)).filter (candR sv (some cs)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro r hr
        have hs := hsvm r hr
        simp only [candR, SemiJoin.keepRow]
        cases e : idLookup sv r with
        | none => rw [e] at hs; cases hs
        | some y =>
          have : cs = #[] := Array.isEmpty_iff.mp hce
          subst this; simp
      rw [h1, h2]; exact Pw.nil
    · rw [if_neg hce]
      have hs := hR cs rfl
      have hspec := ScanTableTheorems.specOk_mkSpec (pathPat g pid) perm hmiss
      have hperm' : (mkSpec (pathPat g pid) perm (fun _ => true)).perm = perm := by
        rw [ScanTableTheorems.mkSpec_eq]; rfl
      obtain ⟨T', stats', he', hT'⟩ := SipTableTheorems.scanSipTableM_spec st _ hspec hk cs hs prb ms
        (by rw [hperm']; exact hpm.range _) (by rw [hperm']; exact hpm.count) (by rw [hperm']; exact hpm.bytes)
        (by rw [hperm']; exact hpm.ovl) (by rw [hperm']; exact hpm.adm) hpm.blocks
      rw [he']
      refine ⟨T', stats'.withSip, rfl, ?_⟩
      rw [hR0] at hT'
      generalize hK : Rw.filter (fun r => ScanFoldTheorems.keep (mkSpec (pathPat g pid) perm (fun _ => true)) r &&
        SipScanTheorems.candOf (mkSpec (pathPat g pid) perm (fun _ => true)) cs r) = K at hT'
      have hKsub : ∀ r ∈ K, r ∈ Rw := by
        intro r hr; rw [← hK] at hr; exact (List.mem_filter.mp hr).1
      obtain ⟨hrows, hnu⟩ := ScanTableTheorems.idRows_eq (pathPat g pid) perm hmiss g htg T' K hT'
        (fun r hr => hfitR r (hKsub r hr)) (fun r hr => hnzR r (hKsub r hr))
      refine ⟨by rw [hT'.vars]; exact hndv, hnu, ?_⟩
      have hKF : T'.idRows = ((Rw.filter (ScanFoldTheorems.keep (mkSpec (pathPat g pid) perm (fun _ => true)))).map
          (ScanTableTheorems.seenRow (ScanTableTheorems.specAcc (pathPat g pid) perm (fun _ => true)))).filter
          (candR sv (some cs)) := by
        rw [hrows, ← hK, List.filter_map, List.filter_filter]
        congr 1
        apply List.filter_congr
        intro r _
        have e : (candR sv (some cs) ∘ ScanTableTheorems.seenRow (ScanTableTheorems.specAcc (pathPat g pid) perm
            (fun _ => true))) r = SipScanTheorems.candOf (mkSpec (pathPat g pid) perm (fun _ => true)) cs r := by
          simp only [Function.comp, candR, SemiJoin.keepRow]
          rw [ScanTableTheorems.seen_sortVar (pathPat g pid) perm hmiss sv hsv r]
          rfl
        rw [e, Bool.and_comm]
      rw [hKF]
      exact pw_filter _ (candR_congr sv (some cs)) hkept

/-! ## The model's rows of a path scan -/

theorem scanRows_some (g x : UInt64) (L : List IdTriple) :
    scanRows (ipatOf (pathPat g (some x))) L =
      L.filterMap (fun t => if x == t.2.1 then some [("o", t.2.2), ("s", t.1)] else none) := by
  unfold scanRows IdLeaf.idEvalTP
  congr 1; funext t
  simp [IdLeaf.idTpMatch, IdLeaf.IPat.slots, matchSlots, slotMatch, ipatOf, pathPat, ScanTableTheorems.islot,
    OptJoin.idLookup]
  by_cases h : x = t.2.1 <;> simp [h, OptJoin.idLookup]

theorem scanRows_none (g : UInt64) (L : List IdTriple) :
    scanRows (ipatOf (pathPat g none)) L = L.map (fun t => [("o", t.2.2), ("p", t.2.1), ("s", t.1)]) := by
  unfold scanRows IdLeaf.idEvalTP
  rw [← List.filterMap_eq_map]
  congr 1

theorem restr_isNone (fwd : Bool) (R : Option (Array UInt64)) : Restr (R.isNone || fwd) R = Restr fwd R := by
  funext p; cases R <;> rfl

theorem candR_link (fwd : Bool) (R : Option (Array UInt64)) (s o : UInt64) :
    candR (if fwd then "s" else "o") R [("o", o), ("s", s)] = Restr fwd R (s, o) := by
  cases R <;> cases fwd <;> simp [candR, SemiJoin.keepRow, Restr, OptJoin.idLookup]

theorem candR_all (fwd : Bool) (R : Option (Array UInt64)) (s p o : UInt64) :
    candR (if fwd then "s" else "o") R [("o", o), ("p", p), ("s", s)] = Restr fwd R (s, o) := by
  cases R <;> cases fwd <;> simp [candR, SemiJoin.keepRow, Restr, OptJoin.idLookup]

theorem link_model (g x : UInt64) (L : List IdTriple) (fwd : Bool) (R : Option (Array UInt64)) :
    ((scanRows (ipatOf (pathPat g (some x))) L).filter (candR (if fwd then "s" else "o") R)).map (proj2 "s" "o") =
      (L.filterMap (fun t => if x == t.2.1 then some (t.1, t.2.2) else none)).filter (Restr fwd R) := by
  rw [scanRows_some]
  induction L with
  | nil => rfl
  | cons t L ih =>
    by_cases h : x = t.2.1
    · have h' : (x == t.2.1) = true := by rw [h]; exact beq_self_eq_true _
      simp only [List.filterMap_cons, h', if_true, List.filter_cons, candR_link]
      by_cases hr : Restr fwd R (t.1, t.2.2) = true
      · simp only [hr, if_true, List.map_cons, ih]
        congr 1
      · simp only [hr, Bool.false_eq_true, if_false]
        exact ih
    · have h' : (x == t.2.1) = false := by simpa using h
      simp only [List.filterMap_cons, h', Bool.false_eq_true, if_false]
      exact ih

/-- The rows of a scan of every triple, filtered by the restriction. -/
def allRows (L : List IdTriple) (byS : Bool) (R : Option (Array UInt64)) : List IdRow :=
  (L.filter (fun t => Restr byS R (t.1, t.2.2))).map (fun t => [("o", t.2.2), ("p", t.2.1), ("s", t.1)])

theorem all_model (g : UInt64) (L : List IdTriple) (byS : Bool) (R : Option (Array UInt64)) :
    (scanRows (ipatOf (pathPat g none)) L).filter (candR (if byS then "s" else "o") R) = allRows L byS R := by
  rw [scanRows_none]
  unfold allRows
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro t _
  simp only [Function.comp, candR_all]

theorem allRows_perm {L L' : List IdTriple} (h : L.Perm L') (byS : Bool) (R : Option (Array UInt64)) :
    (allRows L byS R).Perm (allRows L' byS R) :=
  (h.filter _).map _

/-! ## The scans of `evalIM` -/

theorem sortVar_link (g x : UInt64) (fwd : Bool) :
    sortVarOf (mkSpec (pathPat g (some x)) (if fwd then 0 else 1) (fun _ => true)) =
      some (if fwd then "s" else "o") := by
  cases fwd
  · show sortVarOf (mkSpec (pathPat g (some x)) 1 (fun _ => true)) = some "o"
    rw [ScanTableTheorems.mkSpec_eq]; rfl
  · show sortVarOf (mkSpec (pathPat g (some x)) 0 (fun _ => true)) = some "s"
    rw [ScanTableTheorems.mkSpec_eq]; rfl

theorem key_link (g x : UInt64) (fwd : Bool) :
    (mkSpec (pathPat g (some x)) (if fwd then 0 else 1) (fun _ => true)).key.size < 4 := by
  cases fwd
  · have : (mkSpec (pathPat g (some x)) 1 (fun _ => true)).key.size = 1 := by
      rw [ScanTableTheorems.mkSpec_eq]; rfl
    show (mkSpec (pathPat g (some x)) 1 (fun _ => true)).key.size < 4
    omega
  · have : (mkSpec (pathPat g (some x)) 0 (fun _ => true)).key.size = 1 := by
      rw [ScanTableTheorems.mkSpec_eq]; rfl
    show (mkSpec (pathPat g (some x)) 0 (fun _ => true)).key.size < 4
    omega

theorem sortVar_all (g : UInt64) (byS : Bool) :
    sortVarOf (mkSpec (pathPat g none) (if byS then 2 else 3) (fun _ => true)) = some (if byS then "s" else "o") := by
  cases byS
  · show sortVarOf (mkSpec (pathPat g none) 3 (fun _ => true)) = some "o"
    rw [ScanTableTheorems.mkSpec_eq]; rfl
  · show sortVarOf (mkSpec (pathPat g none) 2 (fun _ => true)) = some "s"
    rw [ScanTableTheorems.mkSpec_eq]; rfl

theorem key_all (g : UInt64) (byS : Bool) :
    (mkSpec (pathPat g none) (if byS then 2 else 3) (fun _ => true)).key.size < 4 := by
  cases byS
  · have : (mkSpec (pathPat g none) 3 (fun _ => true)).key.size = 0 := by
      rw [ScanTableTheorems.mkSpec_eq]; rfl
    show (mkSpec (pathPat g none) 3 (fun _ => true)).key.size < 4
    omega
  · have : (mkSpec (pathPat g none) 2 (fun _ => true)).key.size = 0 := by
      rw [ScanTableTheorems.mkSpec_eq]; rfl
    show (mkSpec (pathPat g none) 2 (fun _ => true)).key.size < 4
    omega

/-- **A one-step scan** (`.link (some x)` of `evalIM`): the pairs, up to
    order, are the triples of `T` with predicate `x` that the restriction
    keeps. -/
theorem pathScan_link (st : Store Id) (g x : UInt64) (T : List IdTriple) (hst : BgpStore st g T)
    (fwd : Bool) (R : Option (Array UInt64)) (hR : ∀ cs, R = some cs → Sip.Sorted cs) :
    ∃ t s, pathScanM st g (some x) (if R.isNone || fwd then 0 else 1) R = pure (t, s) ∧
      (pairsOf t "s" "o").toList.Perm
        ((T.filterMap (fun t => if x == t.2.1 then some (t.1, t.2.2) else none)).filter (Restr fwd R)) := by
  generalize hf : (R.isNone || fwd) = f
  have hperm : (if f then 0 else 1) < 4 := by cases f <;> decide
  obtain ⟨prb, ms, hpm, hP⟩ := hst.perm _ hperm
  obtain ⟨t, s, he, hnd, hnu, hpw⟩ := pathScan_rows st g (some x) _ hperm _ (sortVar_link g x f) (key_link g x f)
    prb ms hpm hst.scan R hR
  refine ⟨t, s, he, ?_⟩
  have hr : Restr f R = Restr fwd R := by rw [← hf, restr_isNone]
  rw [pairsOf_eq t hnd hnu _ hpw "s" "o" ?_, link_model, hr]
  · exact (hP.filterMap _).filter _
  · intro r hr
    rw [scanRows_some] at hr
    obtain ⟨y, _, e⟩ := List.mem_filterMap.mp (List.mem_filter.mp hr).1
    split at e
    · cases e; simp [OptJoin.idLookup]
    · cases e

/-- **A scan of every triple** (`?s ?p ?o` on SPO or OSP): the rows, up to
    order and row for row, are the triples of `T` the restriction keeps. -/
theorem pathScan_all (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T)
    (byS : Bool) (R : Option (Array UInt64)) (hR : ∀ cs, R = some cs → Sip.Sorted cs) :
    ∃ t s, pathScanM st g none (if byS then 2 else 3) R = pure (t, s) ∧ t.vars.toList.Nodup ∧ NoUnbound t ∧
      ∃ M, Pw RowEq t.idRows M ∧ M.Perm (allRows T byS R) := by
  have hperm : (if byS then 2 else 3) < 4 := by cases byS <;> decide
  obtain ⟨prb, ms, hpm, hP⟩ := hst.perm _ hperm
  obtain ⟨t, s, he, hnd, hnu, hpw⟩ := pathScan_rows st g none _ hperm _ (sortVar_all g byS) (key_all g byS)
    prb ms hpm hst.scan R hR
  rw [all_model] at hpw
  exact ⟨t, s, he, hnd, hnu, _, hpw, allRows_perm hP byS R⟩

theorem allRows_lookups (L : List IdTriple) (byS : Bool) (R : Option (Array UInt64)) :
    ∀ r ∈ allRows L byS R, (idLookup "s" r).isSome ∧ (idLookup "p" r).isSome ∧ (idLookup "o" r).isSome := by
  intro r hr
  obtain ⟨t, _, rfl⟩ := List.mem_map.mp hr
  simp [OptJoin.idLookup]

theorem allRows_proj (L : List IdTriple) (byS : Bool) (R : Option (Array UInt64)) :
    (allRows L byS R).map (proj2 "s" "o") = (L.filter (fun t => Restr byS R (t.1, t.2.2))).map (fun t => (t.1, t.2.2)) := by
  unfold allRows
  rw [List.map_map]
  congr 1

theorem allRows_proj_ss (L : List IdTriple) (byS : Bool) (R : Option (Array UInt64)) :
    (allRows L byS R).map (proj2 "s" "s") = (L.filter (fun t => Restr byS R (t.1, t.2.2))).map (fun t => (t.1, t.1)) := by
  unfold allRows
  rw [List.map_map]
  congr 1

theorem allRows_proj_oo (L : List IdTriple) (byS : Bool) (R : Option (Array UInt64)) :
    (allRows L byS R).map (proj2 "o" "o") = (L.filter (fun t => Restr byS R (t.1, t.2.2))).map (fun t => (t.2.2, t.2.2)) := by
  unfold allRows
  rw [List.map_map]
  congr 1

/-! ## Negated property sets -/

theorem pw_get : ∀ {A B : List IdRow}, Pw RowEq A B → ∀ k (hk : k < B.length), RowEq A[k]! B[k] := by
  intro A B h
  induction h with
  | nil => intro k hk; cases hk
  | cons hab _ ih =>
    intro k hk
    cases k with
    | zero => simpa using hab
    | succ k => simpa using ih k (by simpa using hk)

/-- A variable every row of `M` binds has a column in a table whose rows are
    `M` row for row (when the table has a row). -/
theorem idx_of_pw (t : Table) (hnd : t.vars.toList.Nodup) (M : List IdRow) (hpw : Pw RowEq t.idRows M)
    (h0 : 0 < t.rows) (v : String) (hM : ∀ r ∈ M, (idLookup v r).isSome) : ∃ c, t.idx v = some c := by
  have hlen := Pw.length_eq hpw
  have hl0 : 0 < M.length := by rw [← hlen, TableTheorems.idRows_length]; exact h0
  have hrel := pw_get hpw 0 hl0
  rw [TableTheorems.idRows_get t 0 h0] at hrel
  exact idx_of_lookup hnd (i := 0) (by rw [hrel v]; exact hM _ (List.getElem_mem hl0))

theorem npsPairs_loop (t : Table) (ex : Array UInt64) (inv : Bool) (cs cp co : Nat) :
    (Id.run do
      let mut out : Pairs := #[]
      for i in [0:t.rows] do
        if !ex.contains (t.at cp i) then
          out := out.push (if inv then (t.at co i, t.at cs i) else (t.at cs i, t.at co i))
      return out).toList =
      ((List.range t.rows).filter (fun i => !ex.contains (t.at cp i))).map
        (fun i => if inv then (t.at co i, t.at cs i) else (t.at cs i, t.at co i)) := by
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  generalize hF : forIn (m := Id) (List.range' 0 t.rows) (#[] : Pairs) _ = F
  have := TableTheorems.forIn_range_inv t.rows
    (fun k (out : Pairs) => out.toList = ((List.range k).filter (fun i => !ex.contains (t.at cp i))).map
      (fun i => if inv then (t.at co i, t.at cs i) else (t.at cs i, t.at co i))) hF
    (by simp) (fun k out _ h => ⟨if !ex.contains (t.at cp k) then
        out.push (if inv then (t.at co k, t.at cs k) else (t.at cs k, t.at co k)) else out,
      by split <;> rfl, by
      rw [List.range_succ, List.filter_append, List.map_append, ← h]
      by_cases hc : ex.contains (t.at cp k) = true
      · simp only [hc, Bool.not_true, Bool.false_eq_true, if_false, List.filter_cons, List.filter_nil,
          List.map_nil, List.append_nil]
      · simp only [hc, Bool.not_false, if_true, List.filter_cons, List.filter_nil, List.map_cons,
          List.map_nil, Array.toList_push]⟩)
  exact this

/-- **`npsPairs`**: per row whose predicate is not excluded, the pair of its
    subject and object (swapped for the inverse members). -/
theorem npsPairs_eq (t : Table) (hnd : t.vars.toList.Nodup) (hnu : NoUnbound t) (M : List IdRow)
    (hpw : Pw RowEq t.idRows M) (ex : Array UInt64) (inv : Bool)
    (hM : ∀ r ∈ M, (idLookup "s" r).isSome ∧ (idLookup "p" r).isSome ∧ (idLookup "o" r).isSome) :
    (npsPairs t ex inv).toList =
      (M.filter (fun r => !ex.contains ((idLookup "p" r).getD 0))).map
        (fun r => if inv then proj2 "o" "s" r else proj2 "s" "o" r) := by
  have hq : ∀ r s, RowEq r s → (!ex.contains ((idLookup "p" r).getD 0)) = !ex.contains ((idLookup "p" s).getD 0) :=
    fun r s h => by rw [h "p"]
  have hf : ∀ r s, RowEq r s → (if inv then proj2 "o" "s" r else proj2 "s" "o" r) =
      (if inv then proj2 "o" "s" s else proj2 "s" "o" s) := fun r s h => by simp [proj2, h "o", h "s"]
  rw [← pw_map_eq _ hf (pw_filter _ hq hpw)]
  by_cases h0 : t.rows = 0
  · have : t.idRows = [] := by simp [Table.idRows, h0]
    rw [this]
    unfold npsPairs
    split
    · rw [npsPairs_loop, h0]; rfl
    · rfl
  · obtain ⟨cs, hcs⟩ := idx_of_pw t hnd M hpw (by omega) "s" (fun r hr => (hM r hr).1)
    obtain ⟨cp, hcp⟩ := idx_of_pw t hnd M hpw (by omega) "p" (fun r hr => (hM r hr).2.1)
    obtain ⟨co, hco⟩ := idx_of_pw t hnd M hpw (by omega) "o" (fun r hr => (hM r hr).2.2)
    unfold npsPairs
    rw [hcs, hcp, hco]
    simp only []
    rw [npsPairs_loop]
    unfold Table.idRows
    rw [List.filter_map, List.map_map]
    have e1 : (List.range t.rows).filter (fun i => !ex.contains (t.at cp i)) =
        (List.range t.rows).filter ((fun r => !ex.contains ((idLookup "p" r).getD 0)) ∘ t.idRow) := by
      apply List.filter_congr
      intro i hi
      have hi' := List.mem_range.mp hi
      simp [lookup_at hnd hnu hi' hcp]
    rw [e1]
    apply List.map_congr_left
    intro i hi
    have hi' := List.mem_range.mp (List.mem_filter.mp hi).1
    simp [proj2, lookup_at hnd hnu hi' hcs, lookup_at hnd hnu hi' hco]

/-! ## Nodes of the graph -/

theorem pairsOf_perm (t : Table) (hnd : t.vars.toList.Nodup) (hnu : NoUnbound t) (M M' : List IdRow)
    (hpw : Pw RowEq t.idRows M) (hp : M.Perm M') (a b : String)
    (hM : ∀ r ∈ M', (idLookup a r).isSome ∧ (idLookup b r).isSome) :
    (pairsOf t a b).toList.Perm (M'.map (proj2 a b)) := by
  rw [pairsOf_eq t hnd hnu M hpw a b (fun r hr => hM r (hp.mem_iff.mp hr))]
  exact hp.map _

theorem allRows_ab (L : List IdTriple) (byS : Bool) (R : Option (Array UInt64)) (a b : String)
    (ha : a = "s" ∨ a = "o") (hb : b = "s" ∨ b = "o") :
    ∀ r ∈ allRows L byS R, (idLookup a r).isSome ∧ (idLookup b r).isSome := by
  intro r hr
  obtain ⟨h1, _, h3⟩ := allRows_lookups L byS R r hr
  exact ⟨by rcases ha with rfl | rfl <;> assumption, by rcases hb with rfl | rfl <;> assumption⟩

theorem mem_graphNodes (T : List IdTriple) (n : UInt64) :
    n ∈ idGraphNodes T ↔ ∃ t ∈ T, t.1 = n ∨ t.2.2 = n := by
  rw [IdPath.mem_nodes]
  constructor
  · rintro ⟨x, hx, h | h⟩ <;> exact ⟨x, hx, by simp [h]⟩
  · rintro ⟨x, hx, h | h⟩ <;> exact ⟨x, hx, by simp [h]⟩

theorem contains_iff (a : Array UInt64) (x : UInt64) : a.contains x = true ↔ x ∈ a.toList := by simp

/-- **Every node of the graph** (`allNodesM`): increasing, each once. -/
theorem allNodes_spec (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T) :
    ∃ ns s, allNodesM st (some g) = pure (ns, s) ∧ ns.toList.Pairwise (· < ·) ∧
      ∀ n, n ∈ ns.toList ↔ n ∈ idGraphNodes T := by
  obtain ⟨t, s, he, hnd, hnu, M, hpw, hp⟩ := pathScan_all st g T hst true none (fun _ h => by cases h)
  have hpo := pairsOf_perm t hnd hnu M _ hpw hp "s" "o" (allRows_ab T true none "s" "o" (.inl rfl) (.inr rfl))
  rw [allRows_proj] at hpo
  refine ⟨IdPath.sortedDistinct ((pairsOf t "s" "o").map (·.1) ++ (pairsOf t "s" "o").map (·.2)), s, ?_,
    (IdPath.sortedDistinct_spec _).1, ?_⟩
  · unfold allNodesM
    simp only []
    rw [show (2 : Nat) = (if true then 2 else 3) from rfl, he]
    rfl
  · intro n
    rw [(IdPath.sortedDistinct_spec _).2, mem_graphNodes]
    simp only [Array.toList_append, Array.toList_map, List.mem_append, List.mem_map]
    have hm : ∀ p, p ∈ (pairsOf t "s" "o").toList ↔ ∃ t ∈ T, (t.1, t.2.2) = p := by
      intro p
      rw [hpo.mem_iff, List.mem_map]
      constructor
      · rintro ⟨x, hx, e⟩
        exact ⟨x, (List.mem_filter.mp hx).1, e⟩
      · rintro ⟨x, hxT, e⟩
        exact ⟨x, List.mem_filter.mpr ⟨hxT, rfl⟩, e⟩
    constructor
    · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · obtain ⟨x, hx, rfl⟩ := (hm p).mp hp; exact ⟨x, hx, .inl rfl⟩
      · obtain ⟨x, hx, rfl⟩ := (hm p).mp hp; exact ⟨x, hx, .inr rfl⟩
    · rintro ⟨x, hx, h | h⟩
      · exact .inl ⟨(x.1, x.2.2), (hm _).mpr ⟨x, hx, rfl⟩, h⟩
      · exact .inr ⟨(x.1, x.2.2), (hm _).mpr ⟨x, hx, rfl⟩, h⟩

/-- **The nodes of the graph among a restriction** (`nodesAmongM`):
    increasing, each once. -/
theorem nodesAmong_spec (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T)
    (rs : Array UInt64) (hrs : Sip.Sorted rs) :
    ∃ ns s, nodesAmongM st (some g) rs = pure (ns, s) ∧ ns.toList.Pairwise (· < ·) ∧
      ∀ n, n ∈ ns.toList ↔ n ∈ rs.toList ∧ n ∈ idGraphNodes T := by
  have hR : ∀ cs, some rs = some cs → Sip.Sorted cs := fun _ h => by cases h; exact hrs
  obtain ⟨t1, s1, he1, hnd1, hnu1, M1, hpw1, hp1⟩ := pathScan_all st g T hst true (some rs) hR
  obtain ⟨t2, s2, he2, hnd2, hnu2, M2, hpw2, hp2⟩ := pathScan_all st g T hst false (some rs) hR
  have h1 := pairsOf_perm t1 hnd1 hnu1 M1 _ hpw1 hp1 "s" "s" (allRows_ab T true _ "s" "s" (.inl rfl) (.inl rfl))
  have h2 := pairsOf_perm t2 hnd2 hnu2 M2 _ hpw2 hp2 "o" "o" (allRows_ab T false _ "o" "o" (.inr rfl) (.inr rfl))
  rw [allRows_proj_ss] at h1
  rw [allRows_proj_oo] at h2
  refine ⟨IdPath.sortedDistinct ((pairsOf t1 "s" "s").map (·.1) ++ (pairsOf t2 "o" "o").map (·.1)), s1.add s2, ?_,
    (IdPath.sortedDistinct_spec _).1, ?_⟩
  · unfold nodesAmongM
    simp only []
    rw [show (2 : Nat) = (if true then 2 else 3) from rfl, he1, show (3 : Nat) = (if false then 2 else 3) from rfl, he2]
    rfl
  · intro n
    rw [(IdPath.sortedDistinct_spec _).2, mem_graphNodes]
    simp only [Array.toList_append, Array.toList_map, List.mem_append, List.mem_map]
    have hm1 : ∀ p, p ∈ (pairsOf t1 "s" "s").toList ↔ ∃ t ∈ T, t.1 ∈ rs.toList ∧ (t.1, t.1) = p := by
      intro p
      rw [h1.mem_iff, List.mem_map]
      constructor
      · rintro ⟨x, hx, e⟩
        obtain ⟨hxT, hr⟩ := List.mem_filter.mp hx
        exact ⟨x, hxT, (contains_iff _ _).mp hr, e⟩
      · rintro ⟨x, hxT, hr, e⟩
        exact ⟨x, List.mem_filter.mpr ⟨hxT, (contains_iff _ _).mpr hr⟩, e⟩
    have hm2 : ∀ p, p ∈ (pairsOf t2 "o" "o").toList ↔ ∃ t ∈ T, t.2.2 ∈ rs.toList ∧ (t.2.2, t.2.2) = p := by
      intro p
      rw [h2.mem_iff, List.mem_map]
      constructor
      · rintro ⟨x, hx, e⟩
        obtain ⟨hxT, hr⟩ := List.mem_filter.mp hx
        exact ⟨x, hxT, (contains_iff _ _).mp hr, e⟩
      · rintro ⟨x, hxT, hr, e⟩
        exact ⟨x, List.mem_filter.mpr ⟨hxT, (contains_iff _ _).mpr hr⟩, e⟩
    constructor
    · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · obtain ⟨x, hx, hr, rfl⟩ := (hm1 p).mp hp; exact ⟨hr, x, hx, .inl rfl⟩
      · obtain ⟨x, hx, hr, rfl⟩ := (hm2 p).mp hp; exact ⟨hr, x, hx, .inr rfl⟩
    · rintro ⟨hr, x, hx, h | h⟩
      · subst h; exact .inl ⟨(x.1, x.1), (hm1 _).mpr ⟨x, hx, hr, rfl⟩, rfl⟩
      · subst h; exact .inr ⟨(x.2.2, x.2.2), (hm2 _).mpr ⟨x, hx, hr, rfl⟩, rfl⟩

/-! ## The round bound of a closure -/

/-- A scan specification that keeps every row of permutation 0. -/
def specAll : ScanSpec :=
  { perm := 0, key := #[], checks := #[], named := false, outVars := #[], outCols := #[], eqs := #[] }

theorem keep_specAll (r : Block.Row) : ScanFoldTheorems.keep specAll r = true := by
  simp [ScanFoldTheorems.keep, specAll, prefixCmp, prefixCmpGo]

theorem sum_map_le {α : Type} (f g : α → Nat) : ∀ (l : List α), (∀ x ∈ l, f x ≤ g x) → (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | x :: xs, h => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_map_le f g xs (fun y hy => h y (List.mem_cons_of_mem _ hy))
    have := h x List.mem_cons_self
    omega

theorem foldl_rows (l : List Block.BlockMeta) (n : Nat) :
    l.foldl (fun a b => a + b.rows) n = n + (l.map (·.rows)).sum := by
  induction l generalizing n with
  | nil => simp
  | cons b l ih => rw [List.foldl_cons, ih]; simp; omega

theorem blockRows_length (prb : ByteArray) (b : Block.BlockMeta) : (ScanFoldTheorems.blockRows prb b).length ≤ b.rows := by
  unfold ScanFoldTheorems.blockRows
  split <;> simp

/-- The rows of permutation 0 are at most the rows of the PRM1 entries of
    the empty key, which `pathFuelM` counts. -/
theorem rows_le_selRows (prb : ByteArray) (ms : List Block.BlockMeta) (hadm : Block.prmAdmitted 0 ms = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, Block.decodeBlockAt prb b b.offset = .ok cols) :
    (ms.flatMap (ScanFoldTheorems.blockRows prb)).length ≤ selRows (metasFor ms.toArray #[]) := by
  have h := ScanTableTheorems.blocksFor_out specAll prb ms hadm hblocks
  have hl := congrArg List.length h
  rw [List.length_map, List.filter_eq_self.mpr (fun r _ => keep_specAll r)] at hl
  rw [← hl, List.length_flatMap]
  unfold selRows metasFor
  rw [← Array.foldl_toList, foldl_rows, Array.toList_map, List.map_map, Nat.zero_add]
  apply sum_map_le
  intro k hk
  have hlt := ScanTableTheorems.blocksFor_lt specAll ms k hk
  simp only [Function.comp]
  rw [show ms.toArray[k]! = ms[k]! by simp [getElem!_pos, hlt]]
  unfold ScanFoldTheorems.blockOut
  rw [List.length_map]
  exact Nat.le_trans (List.length_filter_le _ _) (blockRows_length prb _)

theorem idDedup_length (l : IdPairs) : (IdPath.idDedup l).length ≤ l.length := by
  induction l with
  | nil => simp [IdPath.idDedup]
  | cons x xs ih =>
    unfold IdPath.idDedup
    split <;> simp <;> omega

theorem graphNodes_length (T : List IdTriple) : (idGraphNodes T).length ≤ 2 * T.length := by
  unfold idGraphNodes
  rw [List.length_map]
  refine Nat.le_trans (idDedup_length _) ?_
  simp; omega

/-- **The round bound of a closure** is at least the number of nodes of the
    graph plus the size of the restriction plus two. -/
theorem pathFuel_ge (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T) (extra : Nat) :
    ∃ f, pathFuelM st extra = pure f ∧ (idGraphNodes T).length + extra + 2 ≤ f := by
  obtain ⟨prb, ms, hpm, hP⟩ := hst.perm 0 (by decide)
  refine ⟨2 * (selRows (metasFor ms.toArray #[]) + (st.ovl 0).ins.size) + extra + 2, ?_, ?_⟩
  · unfold pathFuelM
    rw [hpm.range]
    rfl
  · have h1 := graphNodes_length T
    have h2 : T.length ≤ (ms.flatMap (ScanFoldTheorems.blockRows prb)).length := by
      rw [← hP.length_eq]
      unfold permListing
      rw [List.length_map]
      exact List.length_filter_le _ _
    have h3 := rows_le_selRows prb ms hpm.adm hpm.blocks
    show _ ≤ 2 * (selRows (metasFor ms.toArray #[]) + (st.ovl 0).ins.size) + extra + 2
    omega

end L4Factoidal.Storage.Sbm11.IdPathScanTheorems

#print axioms L4Factoidal.Storage.Sbm11.IdPathScanTheorems.pathScan_rows
#print axioms L4Factoidal.Storage.Sbm11.IdPathScanTheorems.pathScan_link
#print axioms L4Factoidal.Storage.Sbm11.IdPathScanTheorems.pathScan_all
#print axioms L4Factoidal.Storage.Sbm11.IdPathScanTheorems.npsPairs_eq
#print axioms L4Factoidal.Storage.Sbm11.IdPathScanTheorems.allNodes_spec
#print axioms L4Factoidal.Storage.Sbm11.IdPathScanTheorems.nodesAmong_spec
#print axioms L4Factoidal.Storage.Sbm11.IdPathScanTheorems.pathFuel_ge
