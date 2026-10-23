/-
L4Factoidal.Storage.Sbm11.SemiTableTheorems — the semi-join test
`IdQuery.semiMatches` on `Table`s, for MINUS and for EXISTS
(https://github.com/danbri/factoidal/issues/776; lemmas L5t and L5r of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md). Moved from
`GroupTableTheorems` on 2026-10-23, so that `ExistsTableTheorems` can use it.

* `semiMatches_spec'`: for each left row `i`, the entry of `semiMatches l r
  ns` is whether some row of `r` is compatible with row `i` (and, with
  `ns`, shares a bound variable with it: `semiHit`): the hash set of the
  right rows bound in every shared column, cached per set of bound shared
  columns of the left row (`mask_loop`, `kj_loop`, `set_loop`, `tight_hit`,
  `tight_compat`), and the other right rows one by one.
* `semiMatches_spec`: the MINUS case (`ns = true`, `minusHit`).
* `semiMatches_rows`: without `ns`, the entry is `IdExists.idSemi`'s test on
  the rows of the two tables.
* `minus_rows`: the rows of the MINUS table are `IdMinus.idMinus` of the
  rows of the two tables, in order.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.FilterTableTheorems
import L4Factoidal.Storage.Sbm11.IdExistsTheorems

namespace L4Factoidal.Storage.Sbm11.SemiTableTheorems

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Qlvr (Table gather)
open L4Factoidal.Codec.Zstd (word64)
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow idLookup idCompatible idMerge unbound RowIds decRow)
open L4Factoidal.Storage.Sbm11.TableTheorems (RowEq RowsEq ColHolds forIn_range_inv range'_succ_filter
  gather_at)
open L4Factoidal.Storage.Sbm11.IdLeaf (IdEquiv Nd)
open L4Factoidal.Storage.Sbm11.FilterTableTheorems (select_spec)

/-! ## MINUS: `IdQuery.semiMatches` with `needShared` -/

section minus

open L4Factoidal.Storage.Sbm11.TableTheorems (mem_idRow lookup_idRow lookupAt_some mem_sharedCols compatAt_iff
  id_bind forIn_list_inv)
open L4Factoidal.Storage.Sbm11.IdMinus (idMinus idDisjoint)

theorem idDisjoint_iff : ∀ (r1 r2 : IdRow), idDisjoint r1 r2 = true ↔ ∀ p ∈ r1, idLookup p.1 r2 = none
  | [], _ => by simp [idDisjoint]
  | (v, x) :: rest, r2 => by
    simp only [idDisjoint, Bool.and_eq_true, Option.isNone_iff_eq_none, idDisjoint_iff rest r2, List.mem_cons,
      forall_eq_or_imp]

/-- Row `i` of `l` and row `j` of `r` share a variable that both bind. -/
def sharesAt (l r : Table) (i j : Nat) : Bool :=
  (L4Factoidal.Qlvr.sharedCols l r).any fun a => l.at a.1 i != unbound && r.at a.2 j != unbound

theorem sharesAt_iff (l r : Table) (hr : r.vars.toList.Nodup) (i j : Nat) :
    sharesAt l r i j = !idDisjoint (l.idRow i) (r.idRow j) := by
  apply Bool.eq_iff_iff.mpr
  unfold sharesAt
  rw [Array.any_eq_true', Bool.not_eq_true', ← Bool.not_eq_true, idDisjoint_iff]
  constructor
  · rintro ⟨⟨p, q⟩, hm, hpq⟩ hd
    obtain ⟨hp, hq⟩ := mem_sharedCols.mp hm
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hpq
    have := hd (l.vars[p]!, l.at p i) (mem_idRow.mpr ⟨p, hp, hpq.1, rfl⟩)
    rw [lookup_idRow r hr] at this
    have h2 : r.lookupAt j l.vars[p]! = some (r.at q j) := lookupAt_some.mpr ⟨q, hq, hpq.2, rfl⟩
    rw [h2] at this; cases this
  · intro h
    apply Classical.byContradiction
    intro hn
    apply h
    intro pr hpr
    obtain ⟨c, hc, hx, e⟩ := mem_idRow.mp hpr
    subst e
    rw [lookup_idRow r hr]
    cases hy : r.lookupAt j l.vars[c]! with
    | none => rfl
    | some y =>
      obtain ⟨q, hq, hq0, _⟩ := lookupAt_some.mp hy
      exact absurd ⟨(c, q), mem_sharedCols.mpr ⟨hc, hq⟩, by simp [hx, hq0]⟩ hn

/-- The specification of the MINUS test: some row of `r` is compatible with
    row `i` of `l` and shares a bound variable with it. -/
def minusHit (l r : Table) (i : Nat) : Bool :=
  (List.range' 0 r.rows).any fun j =>
    L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r (L4Factoidal.Qlvr.sharedCols l r) i j && sharesAt l r i j

/-- The test of `semiMatches l r ns` in row `i` of `l`: some row of `r` is
    compatible with it and, when `ns` (MINUS), shares a bound variable with
    it. -/
def semiHit (l r : Table) (ns : Bool) (i : Nat) : Bool :=
  (List.range' 0 r.rows).any fun j =>
    L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r (L4Factoidal.Qlvr.sharedCols l r) i j && (!ns || sharesAt l r i j)

theorem minusHit_eq (l r : Table) (i : Nat) : minusHit l r i = semiHit l r true i := by
  unfold minusHit semiHit; simp

theorem testBit_shift (m k : Nat) : m.testBit k = (m >>> k % 2 == 1) := by
  rw [Nat.testBit]; simp

/-- The key of the bound shared columns of a row, in the order the loops of
    `semiMatches` build it (the last column first). -/
def keyOf (S : Array (Nat × Nat)) (sel : Nat → Bool) (val : Nat → UInt64) : List UInt64 :=
  (((List.range' 0 S.size).filter sel).map val).reverse

theorem mask_loop (S : Array (Nat × Nat)) (lv : Nat → UInt64) {F : _root_.Id (Nat × List UInt64)}
    (hF : forIn (List.range' 0 S.size) ((0 : Nat), ([] : List UInt64)) (fun k (s : Nat × List UInt64) =>
      if (lv k != unbound) = true then pure (ForInStep.yield (s.1 ||| 1 <<< k, lv k :: s.2))
      else pure (ForInStep.yield (s.1, s.2))) = F) :
    (∀ b, F.run.1.testBit b = (decide (b < S.size) && lv b != unbound)) ∧
      F.run.2 = keyOf S (fun k => lv k != unbound) lv := by
  have := forIn_range_inv S.size (fun m (s : Nat × List UInt64) =>
      (∀ b, s.1.testBit b = (decide (b < m) && lv b != unbound)) ∧
        s.2 = (((List.range' 0 m).filter (fun k => lv k != unbound)).map lv).reverse) hF
    ⟨fun b => by simp, rfl⟩ (by
      intro k s _ ⟨h1, h2⟩
      by_cases hb : (lv k != unbound) = true
      · refine ⟨(s.1 ||| 1 <<< k, lv k :: s.2), by simp [hb], fun b => ?_, ?_⟩
        · rw [Nat.testBit_or, h1, Nat.shiftLeft_eq, Nat.one_mul, Nat.testBit_two_pow]
          by_cases e : k = b
          · subst e; simp [hb]
          · have : (decide (b < k + 1)) = decide (b < k) := by
              apply decide_eq_decide.mpr; omega
            simp [e, this]
        · rw [range'_succ_filter, h2]; simp [hb]
      · refine ⟨(s.1, s.2), by simp [hb], fun b => ?_, ?_⟩
        · rw [h1]
          by_cases e : k = b
          · subst e; simp at hb; simp [hb]
          · have : (decide (b < k + 1)) = decide (b < k) := by
              apply decide_eq_decide.mpr; omega
            simp [this]
        · rw [range'_succ_filter, h2]; simp [hb])
  exact this

theorem kj_loop (S : Array (Nat × Nat)) (mask : Nat) (rv : Nat → UInt64) {F : _root_.Id (List UInt64)}
    (hF : forIn (List.range' 0 S.size) ([] : List UInt64) (fun k (s : List UInt64) =>
      if (mask >>> k % 2 == 1) = true then pure (ForInStep.yield (rv k :: s))
      else pure (ForInStep.yield s)) = F) :
    F.run = keyOf S (fun k => mask.testBit k) rv := by
  have := forIn_range_inv S.size (fun m (s : List UInt64) =>
      s = (((List.range' 0 m).filter (fun k => mask.testBit k)).map rv).reverse) hF rfl (by
      intro k s _ h
      by_cases hb : (mask >>> k % 2 == 1) = true
      · refine ⟨rv k :: s, by simp [hb], ?_⟩
        rw [range'_succ_filter, h, testBit_shift]; simp [hb]
      · refine ⟨s, by simp [hb], ?_⟩
        rw [range'_succ_filter, h, testBit_shift]; simp [hb])
  exact this

theorem keyOf_congr (S : Array (Nat × Nat)) (s1 s2 : Nat → Bool) (val : Nat → UInt64)
    (h : ∀ k, k < S.size → s1 k = s2 k) : keyOf S s1 val = keyOf S s2 val := by
  unfold keyOf
  congr 2
  apply List.filter_congr
  intro k hk
  rw [List.mem_range'] at hk
  exact h k (by omega)

theorem keyOf_beq (S : Array (Nat × Nat)) (sel : Nat → Bool) (v1 v2 : Nat → UInt64) :
    (keyOf S sel v1 == keyOf S sel v2) = true ↔ ∀ k, k < S.size → sel k = true → v1 k = v2 k := by
  unfold keyOf
  rw [beq_iff_eq, List.reverse_inj, List.map_inj_left]
  simp only [List.mem_filter, List.mem_range']
  constructor
  · intro h k hk hs; exact h k ⟨⟨by omega, by omega⟩, hs⟩
  · intro h k ⟨⟨_, hk⟩, hs⟩; exact h k (by omega) hs

/-- For a row `j` of `r` whose shared columns are all bound, the MINUS test
    is the hash-set test of `semiMatches`: some shared column of row `i` is
    bound (`mask != 0`) and the keys of the bound shared columns agree. -/
theorem tight_hit (l r : Table) (i j : Nat) (mask : Nat) (key : List UInt64)
    (hT : ((L4Factoidal.Qlvr.sharedCols l r).all fun a => r.at a.2 j != unbound) = true)
    (hmask : ∀ b, mask.testBit b = (decide (b < (L4Factoidal.Qlvr.sharedCols l r).size) &&
      l.at (L4Factoidal.Qlvr.sharedCols l r)[b]!.1 i != unbound))
    (hkey : key = keyOf (L4Factoidal.Qlvr.sharedCols l r)
      (fun k => l.at (L4Factoidal.Qlvr.sharedCols l r)[k]!.1 i != unbound)
      (fun k => l.at (L4Factoidal.Qlvr.sharedCols l r)[k]!.1 i)) :
    (L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r (L4Factoidal.Qlvr.sharedCols l r) i j && sharesAt l r i j) =
      ((mask != 0) && (keyOf (L4Factoidal.Qlvr.sharedCols l r) (fun k => mask.testBit k)
        (fun k => r.at (L4Factoidal.Qlvr.sharedCols l r)[k]!.2 j) == key)) := by
  generalize hS : L4Factoidal.Qlvr.sharedCols l r = S at hT hmask hkey ⊢
  have hS' : L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r S i j =
      S.all fun a => l.at a.1 i == unbound || r.at a.2 j == unbound || l.at a.1 i == r.at a.2 j := rfl
  have hsh : sharesAt l r i j = S.any fun a => l.at a.1 i != unbound && r.at a.2 j != unbound := by
    unfold sharesAt; rw [hS]
  rw [hS', hsh, keyOf_congr S _ (fun k => l.at S[k]!.1 i != unbound) _ (fun k hk => by rw [hmask k]; simp [hk]),
    hkey]
  rw [Array.all_eq_true] at hT
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  rw [keyOf_beq, Array.all_eq_true, Array.any_eq_true]
  have hT' : ∀ k (hk : k < S.size), r.at S[k].2 j ≠ unbound := fun k hk => by simpa using hT k hk
  constructor
  · rintro ⟨hc, ⟨k, hk, hb⟩⟩
    refine ⟨?_, ?_⟩
    · rw [bne_iff_ne]
      intro h0
      have := hmask k
      rw [h0, Nat.zero_testBit, getElem!_pos S k hk] at this
      simp only [Bool.and_eq_true, bne_iff_ne] at hb
      simp [hk, hb.1] at this
    · intro k' hk' hb'
      have hc' := hc k' hk'
      rw [getElem!_pos S k' hk'] at hb' ⊢
      simp only [Bool.or_eq_true, beq_iff_eq] at hc'
      simp only [bne_iff_ne, ne_eq] at hb'
      rcases hc' with (h | h) | h
      · exact absurd h hb'
      · exact absurd h (hT' k' hk')
      · exact h.symm
  · rintro ⟨hm, he⟩
    refine ⟨?_, ?_⟩
    · intro k hk
      have := he k hk
      rw [getElem!_pos S k hk] at this
      simp only [Bool.or_eq_true, beq_iff_eq]
      by_cases h0 : l.at S[k].1 i = unbound
      · exact Or.inl (Or.inl h0)
      · exact Or.inr (this (by simpa using h0)).symm
    · have : ∃ b, mask.testBit b = true := by
        apply Classical.byContradiction
        intro hn
        apply (show mask ≠ 0 by simpa using hm)
        apply Nat.eq_of_testBit_eq
        intro b
        rw [Nat.zero_testBit]
        cases h : mask.testBit b
        · rfl
        · exact absurd ⟨b, h⟩ hn
      obtain ⟨b, hb⟩ := this
      rw [hmask b] at hb
      simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne] at hb
      refine ⟨b, hb.1, ?_⟩
      rw [getElem!_pos S b hb.1] at hb
      simp [hb.2, hT' b hb.1]

/-- For a row `j` of `r` whose shared columns are all bound, compatibility
    with row `i` of `l` is the hash-set test of `semiMatches`: the keys of the
    bound shared columns of row `i` agree. -/
theorem tight_compat (l r : Table) (i j : Nat) (mask : Nat) (key : List UInt64)
    (hT : ((L4Factoidal.Qlvr.sharedCols l r).all fun a => r.at a.2 j != unbound) = true)
    (hmask : ∀ b, mask.testBit b = (decide (b < (L4Factoidal.Qlvr.sharedCols l r).size) &&
      l.at (L4Factoidal.Qlvr.sharedCols l r)[b]!.1 i != unbound))
    (hkey : key = keyOf (L4Factoidal.Qlvr.sharedCols l r)
      (fun k => l.at (L4Factoidal.Qlvr.sharedCols l r)[k]!.1 i != unbound)
      (fun k => l.at (L4Factoidal.Qlvr.sharedCols l r)[k]!.1 i)) :
    L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r (L4Factoidal.Qlvr.sharedCols l r) i j =
      (keyOf (L4Factoidal.Qlvr.sharedCols l r) (fun k => mask.testBit k)
        (fun k => r.at (L4Factoidal.Qlvr.sharedCols l r)[k]!.2 j) == key) := by
  generalize hS : L4Factoidal.Qlvr.sharedCols l r = S at hT hmask hkey ⊢
  have hS' : L4Factoidal.Storage.Sbm11.IdJoin.compatAt l r S i j =
      S.all fun a => l.at a.1 i == unbound || r.at a.2 j == unbound || l.at a.1 i == r.at a.2 j := rfl
  rw [hS', keyOf_congr S _ (fun k => l.at S[k]!.1 i != unbound) _ (fun k hk => by rw [hmask k]; simp [hk]),
    hkey]
  rw [Array.all_eq_true] at hT
  apply Bool.eq_iff_iff.mpr
  rw [keyOf_beq, Array.all_eq_true]
  have hT' : ∀ k (hk : k < S.size), r.at S[k].2 j ≠ unbound := fun k hk => by simpa using hT k hk
  constructor
  · intro hc k' hk' hb'
    have hc' := hc k' hk'
    rw [getElem!_pos S k' hk'] at hb' ⊢
    simp only [Bool.or_eq_true, beq_iff_eq] at hc'
    simp only [bne_iff_ne, ne_eq] at hb'
    rcases hc' with (h | h) | h
    · exact absurd h hb'
    · exact absurd h (hT' k' hk')
    · exact h.symm
  · intro he k hk
    have := he k hk
    rw [getElem!_pos S k hk] at this
    simp only [Bool.or_eq_true, beq_iff_eq]
    by_cases h0 : l.at S[k].1 i = unbound
    · exact Or.inl (Or.inl h0)
    · exact Or.inr (this (by simpa using h0)).symm

theorem set_loop (S : Array (Nat × Nat)) (tight : Array Nat) (mk : Nat) (rv : Nat → Nat → UInt64)
    {H : _root_.Id (Std.HashSet (List UInt64))}
    (hH : forIn tight (∅ : Std.HashSet (List UInt64)) (fun j (h : Std.HashSet (List UInt64)) => do
      let kj ← forIn (List.range' 0 S.size) ([] : List UInt64) (fun k (s : List UInt64) =>
        if (mk >>> k % 2 == 1) = true then pure (ForInStep.yield (rv j k :: s))
        else pure (ForInStep.yield s))
      pure (ForInStep.yield (h.insert kj))) = H) :
    ∀ key, H.run.contains key = tight.toList.any fun j => keyOf S (fun k => mk.testBit k) (rv j) == key := by
  rw [← Array.forIn_toList] at hH
  have := List.length_take_of_le (Nat.le_refl tight.toList.length)
  have hP := forIn_list_inv tight.toList (fun n (h : Std.HashSet (List UInt64)) => ∀ key,
      h.contains key = (tight.toList.take n).any fun j => keyOf S (fun k => mk.testBit k) (rv j) == key) hH
    (fun key => by simp) (by
      intro n h hn ih
      rw [id_bind]
      generalize hK : forIn (m := _root_.Id) (List.range' 0 S.size) ([] : List UInt64) _ = K
      have hk := kj_loop S mk (rv tight.toList[n]) hK
      refine ⟨h.insert K.run, rfl, fun key => ?_⟩
      rw [Std.HashSet.contains_insert, ih key, List.take_add_one, List.getElem?_eq_getElem hn, List.any_append,
        hk]
      simp [Bool.or_comm])
  intro key
  rw [hP key, List.take_length]

theorem any_congr_mem {α : Type} {p q : α → Bool} : ∀ (L : List α), (∀ a ∈ L, p a = q a) → L.any p = L.any q
  | [], _ => rfl
  | a :: L, h => by
    simp only [List.any_cons]
    rw [h a List.mem_cons_self, any_congr_mem L fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem any_split (xs : List Nat) (T p : Nat → Bool) :
    xs.any p = ((xs.filter T).any p || (xs.filter fun j => !T j).any p) := by
  rw [List.any_filter, List.any_filter]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.any_cons]
    rw [ih]
    cases T x <;> cases p x <;> simp

/-- **The MINUS test of `semiMatches`.** For every row `i` of `l`, the
    entry of `semiMatches l r true` is whether some row of `r` is compatible
    with row `i` and shares a bound variable with it (`minusHit`): the hash
    set of the rows of `r` whose shared columns are all bound, cached per set
    of bound shared columns of a left row, and the other rows of `r` one by
    one. -/
theorem semiMatches_spec' (l r : Table) (ns : Bool) (i : Nat) (hi : i < l.rows) :
    (semiMatches l r ns)[i]! = semiHit l r ns i := by
  unfold semiMatches
  simp only [_root_.Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
    Nat.add_sub_cancel, Nat.div_one]
  have hSc : (Array.filterMap (fun c => Option.map (fun q => (c, q)) (r.idx l.vars[c]!))
      (List.range l.vars.size).toArray) = L4Factoidal.Qlvr.sharedCols l r := rfl
  rw [hSc]
  generalize hS : L4Factoidal.Qlvr.sharedCols l r = S
  let T : Nat → Bool := fun j => S.all fun a => r.at a.2 j != unbound
  rw [id_bind]
  generalize hTL : forIn (m := _root_.Id) (List.range' 0 r.rows) ((#[] : Array Nat), (#[] : Array Nat)) _ = TL
  have hTLs := forIn_range_inv r.rows (fun m (s : Array Nat × Array Nat) =>
      s.1.toList = (List.range' 0 m).filter T ∧ s.2.toList = (List.range' 0 m).filter fun j => !T j) hTL
    ⟨by simp, by simp⟩ (by
      intro m s _ ⟨h1, h2⟩
      by_cases hc : T m = true
      · refine ⟨(s.1.push m, s.2), by simp only [T] at hc; simp [hc], ?_, ?_⟩
        · rw [range'_succ_filter, Array.toList_push, h1]; simp [hc]
        · rw [range'_succ_filter, h2]; simp [hc]
      · refine ⟨(s.1, s.2.push m), by simp only [T] at hc; simp [hc], ?_, ?_⟩
        · rw [range'_succ_filter, h1]; simp [hc]
        · rw [range'_succ_filter, Array.toList_push, h2]; simp [hc])
  obtain ⟨hT1, hT2⟩ := hTLs
  rw [id_bind]
  generalize hF : forIn (m := _root_.Id) (List.range' 0 l.rows)
    ((∅ : Std.HashMap Nat (Std.HashSet (List UInt64))), Array.mkEmpty l.rows) _ = F
  let rv : Nat → Nat → UInt64 := fun j k => r.at S[k]!.2 j
  have hout := forIn_range_inv l.rows (fun m (s : Std.HashMap Nat (Std.HashSet (List UInt64)) × Array Bool) =>
      (∀ (mk : Nat) (h : Std.HashSet (List UInt64)), s.1[mk]? = some h → ∀ key,
        h.contains key = TL.run.1.toList.any fun j => keyOf S (fun k => mk.testBit k) (rv j) == key) ∧
      s.2.toList = (List.range' 0 m).map (semiHit l r ns)) hF
    ⟨fun mk h e => by simp at e, by simp⟩ (by
      intro m s _ ⟨h1, h2⟩
      rw [id_bind]
      generalize hM : forIn (m := _root_.Id) (List.range' 0 S.size) ((0 : Nat), ([] : List UInt64)) _ = M
      obtain ⟨hmask, hkey⟩ := mask_loop S (fun k => l.at S[k]!.1 m) hM
      -- the test of row `m`, given the set of the bound shared columns of `m`
      have hhit : ∀ h : Std.HashSet (List UInt64), (∀ key,
          h.contains key = TL.run.1.toList.any fun j => keyOf S (fun k => M.run.1.testBit k) (rv j) == key) →
          ((!ns || M.run.1 != 0) && h.contains M.run.2 ||
            TL.run.2.any fun a =>
              (S.all fun a_1 => l.at a_1.1 m == unbound || r.at a_1.2 a == unbound || l.at a_1.1 m == r.at a_1.2 a) &&
              (!ns || S.any fun a_1 => l.at a_1.1 m != unbound && r.at a_1.2 a != unbound)) = semiHit l r ns m := by
        intro h hh
        unfold semiHit
        rw [any_split _ T, hS]
        rw [hh, ← Array.any_toList, hT2, hT1]
        congr 1
        · have hc : ∀ (L : List Nat) (c : Bool) (f : Nat → Bool), (c && L.any f) = L.any fun j => c && f j := by
            intro L c f; cases c <;> simp
          rw [hc]
          apply any_congr_mem
          intro j hj
          have hTj : T j = true := (List.mem_filter.mp hj).2
          cases ns
          · have := tight_compat l r m j M.run.1 M.run.2
            rw [hS] at this
            rw [this hTj (fun b => by rw [hmask b]) hkey]
            simp only [Bool.not_false, Bool.true_or, Bool.and_true, Bool.true_and]
            rfl
          · have := tight_hit l r m j M.run.1 M.run.2
            rw [hS] at this
            simp only [Bool.not_true, Bool.false_or]
            rw [this hTj (fun b => by rw [hmask b]) hkey]
        · congr 1
          funext j
          unfold sharesAt
          rw [hS]
          rfl
      split
      · next h e =>
        refine ⟨(s.1, s.2.push _), rfl, h1, ?_⟩
        erw [Array.toList_push, h2, hhit h (h1 _ h e), List.range'_concat]
        simp
      · next e =>
        rw [id_bind]
        generalize hH : forIn (m := _root_.Id) TL.run.1 (∅ : Std.HashSet (List UInt64)) _ = H
        have hHs := set_loop S TL.run.1 M.run.1 rv hH
        refine ⟨(s.1.insert M.run.1 H.run, s.2.push _), rfl, ?_, ?_⟩
        · intro mk h e'
          rw [Std.HashMap.getElem?_insert] at e'
          split at e'
          · next hb =>
            cases e'
            have : M.run.1 = mk := by simpa using hb
            subst this
            exact hHs
          · exact h1 mk h e'
        · erw [Array.toList_push, h2, hhit H.run hHs, List.range'_concat]
          simp)
  obtain ⟨_, hout2⟩ := hout
  show F.run.2[i]! = _
  rw [getElem!_pos F.run.2 i (by rw [← Array.length_toList, hout2]; simpa using hi)]
  rw [← Array.getElem_toList]
  simp only [hout2, List.getElem_map, List.getElem_range']
  simp

/-- **The MINUS test of `semiMatches`.** For every row `i` of `l`, the
    entry of `semiMatches l r true` is whether some row of `r` is compatible
    with row `i` and shares a bound variable with it (`minusHit`). -/
theorem semiMatches_spec (l r : Table) (i : Nat) (hi : i < l.rows) :
    (semiMatches l r true)[i]! = minusHit l r i := by
  rw [semiMatches_spec' l r true i hi, minusHit_eq]

/-- **The EXISTS test of `semiMatches`.** For every row `i` of `l`, the entry
    of `semiMatches l r` (no `needShared`) is `IdExists.idSemi`'s test: some
    row of `r` is compatible with row `i`. -/
theorem semiMatches_rows (l r : Table) (hr : r.WF) (i : Nat) (hi : i < l.rows) :
    (semiMatches l r false)[i]! = r.idRows.any (idCompatible (l.idRow i)) := by
  rw [semiMatches_spec' l r false i hi]
  unfold semiHit Table.idRows
  rw [List.any_map, ← List.range_eq_range']
  apply any_congr_mem
  intro j _
  simp only [Function.comp_def, Bool.not_false, Bool.true_or, Bool.and_true]
  rw [compatAt_iff l r hr.nodup]

/-- **MINUS on id tables.** `evalGroupM` keeps the rows of the left table
    whose entry of `semiMatches` is false: a well-formed table whose rows are
    `IdMinus.idMinus` of the rows of the two tables, in order. -/
theorem minus_rows (tl tr : Table) (hl : tl.WF) (hr : tr.WF) :
    (tl.select fun i => !(semiMatches tl tr true)[i]!).WF ∧
      (tl.select fun i => !(semiMatches tl tr true)[i]!).idRows = idMinus tl.idRows tr.idRows := by
  obtain ⟨hwf, _, hrows⟩ := select_spec tl hl fun i => !(semiMatches tl tr true)[i]!
  refine ⟨hwf, ?_⟩
  rw [hrows]
  unfold idMinus Table.idRows
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro i hi
  rw [List.mem_range] at hi
  simp only [Function.comp_def]
  rw [semiMatches_spec tl tr i hi]
  congr 1
  unfold minusHit
  rw [List.any_map, ← List.range_eq_range']
  apply any_congr_mem
  intro j _
  simp only [Function.comp_def]
  rw [compatAt_iff tl tr hr.nodup, sharesAt_iff tl tr hr.nodup]

end minus


end L4Factoidal.Storage.Sbm11.SemiTableTheorems

#print axioms L4Factoidal.Storage.Sbm11.SemiTableTheorems.semiMatches_spec'
#print axioms L4Factoidal.Storage.Sbm11.SemiTableTheorems.semiMatches_spec
#print axioms L4Factoidal.Storage.Sbm11.SemiTableTheorems.semiMatches_rows
#print axioms L4Factoidal.Storage.Sbm11.SemiTableTheorems.minus_rows
