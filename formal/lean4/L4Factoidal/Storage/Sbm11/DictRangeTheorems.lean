/-
L4Factoidal.Storage.Sbm11.DictRangeTheorems — the dictionary lower bound of
the query path equals its definition (lemma L1e of
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776).

* `lowerBoundM_encodeDict`: for `encodeDict? keys = some (v, x)` and any
  `k`, `DictRange.lowerBoundM` over those bytes (`m = Id`, `fetchOf`)
  answers, without error, `lowerBoundList` of the keys: the number of keys
  below `k`. The STRSTARTS rank-range rule of the id path
  (`IdQuery.compileFilter`) reads two such bounds.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.DictLookupTheorems
import L4Factoidal.Storage.Sbm11.DictRange

namespace L4Factoidal.Storage.Sbm11.DictRange

open L4Factoidal.Storage.Sbm11.Dict
open L4Factoidal (two32 two64)

/-! ## Order lemmas -/

theorem cmpKey_lt_of_lt_of_le (a b c : List UInt8) (h1 : cmpKey a b = .lt) (h2 : cmpKey b c ≠ .gt) :
    cmpKey a c = .lt := by
  cases h : cmpKey b c with
  | lt => exact cmpKey_lt_trans _ _ _ h1 h
  | eq => rw [(cmpKey_eq_iff _ _).mp h] at h1; exact h1
  | gt => exact absurd h h2

theorem cmpKey_not_lt_of_le (a b c : List UInt8) (h1 : cmpKey b c ≠ .lt) (h2 : cmpKey b a ≠ .gt) :
    cmpKey a c ≠ .lt := by
  intro h
  exact h1 (cmpKey_lt_of_lt_of_le' b a c h2 h)
where
  cmpKey_lt_of_lt_of_le' (b a c : List UInt8) (h2 : cmpKey b a ≠ .gt) (h : cmpKey a c = .lt) :
      cmpKey b c = .lt := by
    cases hb : cmpKey b a with
    | lt => exact cmpKey_lt_trans _ _ _ hb h
    | eq => rw [(cmpKey_eq_iff _ _).mp hb]; exact h
    | gt => exact absurd hb h2

/-! ## The page scan -/

theorem firstNotBelowGo_spec (ks : Array ByteArray) (k : ByteArray) : ∀ f i, i ≤ ks.size → ks.size - i ≤ f →
    ∀ r, firstNotBelowGo ks k f i = r →
      i ≤ r ∧ r ≤ ks.size ∧ (∀ j, i ≤ j → j < r → j < ks.size → cmpBytesAt ks[j]! k = .lt) ∧
      (r < ks.size → cmpBytesAt ks[r]! k ≠ .lt) := by
  intro f
  induction f with
  | zero =>
    intro i hi hf r hr
    have : i = ks.size := by omega
    subst this
    simp only [firstNotBelowGo] at hr
    subst hr
    exact ⟨Nat.le_refl _, Nat.le_refl _, fun j h1 h2 h3 => absurd h3 (by omega), fun h => absurd h (by omega)⟩
  | succ f ih =>
    intro i hi hf r hr
    simp only [firstNotBelowGo] at hr
    by_cases hlt : i < ks.size
    · rw [if_pos hlt] at hr
      by_cases hc : (cmpBytesAt ks[i]! k != .lt) = true
      · rw [if_pos hc] at hr
        subst hr
        exact ⟨Nat.le_refl _, by omega, fun j h1 h2 _ => absurd h2 (by omega), fun _ => by simpa using hc⟩
      · rw [if_neg hc] at hr
        obtain ⟨h1, h2, h3, h4⟩ := ih (i + 1) (by omega) (by omega) r hr
        refine ⟨by omega, h2, fun j hj1 hj2 hj => ?_, h4⟩
        by_cases hji : j = i
        · subst hji; simpa using hc
        · exact h3 j (by omega) hj2 hj
    · rw [if_neg hlt] at hr
      subst hr
      exact ⟨by omega, Nat.le_refl _, fun j h1 h2 h3 => absurd h3 (by omega), fun h => absurd h (by omega)⟩

theorem firstNotBelow_spec (ks : Array ByteArray) (k : ByteArray) :
    firstNotBelow ks k ≤ ks.size ∧
    (∀ j (hj : j < ks.size), j < firstNotBelow ks k → cmpBytesAt ks[j] k = .lt) ∧
    (∀ (hj : firstNotBelow ks k < ks.size), cmpBytesAt ks[firstNotBelow ks k] k ≠ .lt) := by
  obtain ⟨_, h2, h3, h4⟩ := firstNotBelowGo_spec ks k ks.size 0 (Nat.zero_le _) (by omega) _ rfl
  refine ⟨h2, fun j hj h => ?_, fun hj => ?_⟩
  · have := h3 j (Nat.zero_le _) h hj
    rwa [getElem!_pos ks j hj] at this
  · have := h4 hj
    rwa [getElem!_pos ks _ hj] at this

/-! ## Counting the keys below -/

theorem filter_prefix_length (keys : List Key) (kL : List UInt8) (n : Nat) (hn : n ≤ keys.length)
    (h1 : ∀ i (hi : i < keys.length), i < n → cmpKey keys[i] kL = .lt)
    (h2 : ∀ i (hi : i < keys.length), n ≤ i → cmpKey keys[i] kL ≠ .lt) :
    (keys.filter fun x => cmpKey x kL == .lt).length = n := by
  rw [← List.take_append_drop n keys, List.filter_append]
  have ht : (keys.take n).filter (fun x => cmpKey x kL == .lt) = keys.take n := by
    apply List.filter_eq_self.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_take]
    simp only [List.length_take] at hi
    simp [h1 i (by omega) (by omega)]
  have hd : (keys.drop n).filter (fun x => cmpKey x kL == .lt) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    rw [List.getElem_drop]
    simp only [List.length_drop] at hi
    simp [h2 (n + i) (by omega) (by omega)]
  rw [ht, hd, List.append_nil, List.length_take]
  omega

theorem lowerBoundList_map (keys : List Key) (k : ByteArray) :
    lowerBoundList (keys.map fun key => (⟨key.toArray⟩ : ByteArray)) k =
      (keys.filter fun x => cmpKey x (bytesToList k) == .lt).length := by
  unfold lowerBoundList
  rw [List.filter_map, List.length_map]
  congr 2
  funext x
  simp only [Function.comp, cmpBytesAt_eq, bytesToList_mk]

/-! ## The lower bound -/

/-- The query path's dictionary lower bound equals its definition over the
    bytes `encodeDict?` writes. -/
theorem lowerBoundM_encodeDict (keys : List Key) (v x : List UInt8) (h : encodeDict? keys = some (v, x))
    (k : ByteArray) :
    lowerBoundM (m := Id) (fetchOf ⟨x.toArray⟩) (fetchOf ⟨v.toArray⟩)
        ⟨keys.length, (chunk pageTerms keys).length⟩ k =
      pure (lowerBoundList (keys.map fun key => (⟨key.toArray⟩ : ByteArray)) k) := by
  rw [lowerBoundList_map]
  unfold encodeDict? at h
  dsimp only at h
  split at h
  · rename_i hadm
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [dictAdmitted, Bool.and_eq_true, decide_eq_true_eq] at hadm
    obtain ⟨⟨⟨⟨hsorted, hmax⟩, hpcl⟩, hpf⟩, hef⟩ := hadm
    generalize hps : chunk pageTerms keys = ps at *
    have hlen : ps.length = (keys.length + 63) / 64 := by rw [← hps]; exact chunk64_length _ keys rfl
    have hpage : ∀ p (hp : p < ps.length), ps[p] = (keys.drop (64 * p)).take 64 := by
      intro p hp
      have := chunk_getElem pageTerms (by decide) p keys (by rw [hps]; exact hp)
      simp only [hps] at this
      exact this
    have hp64 : ∀ p, p < ps.length → 64 * p < keys.length := by
      intro p hp; rw [hlen] at hp; omega
    have hpel : ∀ p (hp : p < ps.length) j (hj : j < ps[p].length), ps[p][j] = keys[64 * p + j]'(by
        rw [hpage p hp] at hj; simp at hj; omega) := by
      intro p hp j hj
      simp only [hpage p hp, List.getElem_take, List.getElem_drop]
    have hplen : ∀ p (hp : p < ps.length), ps[p].length = min 64 (keys.length - 64 * p) := by
      intro p hp; rw [hpage p hp]; simp
    let FK : Nat → Key := fun p => keys.getD (64 * p) []
    have hFK : ∀ p (hp : p < ps.length), FK p = keys[64 * p]'(hp64 p hp) := by
      intro p hp; simp [FK, List.getD_eq_getElem?_getD, hp64 p hp]
    have hfirst : ∀ j, j < ps.length → ∃ pb fk,
        pageBytesM (m := Id) (fetchOf ⟨(gdxBytes keys.length (dirEntries ps)).toArray⟩)
          (fetchOf ⟨(gdvBytes ps).toArray⟩) j = pure pb ∧ firstKeyAt pb = some fk ∧ bytesToList fk = FK j := by
      intro j hj
      obtain ⟨pb, hpb, hl⟩ := pageBytesM_dict ps keys.length hef j hj
      have h0 : 0 < ps[j].length := by rw [hplen j hj]; have := hp64 j hj; omega
      obtain ⟨a, t, hat⟩ : ∃ a t, ps[j] = a :: t :=
        List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos h0)
      have ha : a = keys[64 * j]'(hp64 j hj) := by
        have := hpel j hj 0 h0
        simp only [hat, List.getElem_cons_zero] at this
        simpa using this
      have hpf' := List.all_eq_true.mp hpf ps[j] (List.getElem_mem hj)
      rw [hat] at hl hpf'
      obtain ⟨fk, hfk, hfkl⟩ := firstKeyAt_page pb _ _ hl hpf'
      exact ⟨pb, fk, hpb, hfk, by rw [hfkl, hFK j hj, ha]⟩
    have e : lowerBoundM (m := Id) (fetchOf ⟨(gdxBytes keys.length (dirEntries ps)).toArray⟩)
        (fetchOf ⟨(gdvBytes ps).toArray⟩) ⟨keys.length, ps.length⟩ k =
        (do
          if ps.length == 0 then return 0
          let (lo, _) ← searchPagesM (m := Id) (fetchOf ⟨(gdxBytes keys.length (dirEntries ps)).toArray⟩)
            (fetchOf ⟨(gdvBytes ps).toArray⟩) k (Nat.log2 ps.length + 2) 0 ps.length 0
          let ks ← pageM (m := Id) (fetchOf ⟨(gdxBytes keys.length (dirEntries ps)).toArray⟩)
            (fetchOf ⟨(gdvBytes ps).toArray⟩) lo
          return min keys.length (lo * pageTerms + firstNotBelow ks k)) := rfl
    rw [e]
    by_cases hpc0 : ps.length = 0
    · have hk0 : keys = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [hpc0] at hlen; omega
      subst hk0
      rw [hpc0]
      rfl
    · rw [if_neg (by simpa using hpc0)]
      obtain ⟨res, pr, hs, _, hres, hP, hQ⟩ := searchPagesM_spec _ _ k ps.length FK hfirst
        (Nat.log2 ps.length + 2) 0 ps.length 0 (by omega) (Nat.le_refl _)
        (by
          have := @Nat.lt_log2_self ps.length
          have h2 : 2 ^ (Nat.log2 ps.length + 1) ≤ 2 ^ (Nat.log2 ps.length + 2) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          omega)
        (Or.inl rfl) (Or.inl rfl)
      rw [hs, pure_bind]
      simp only
      obtain ⟨ks, hks, hksl⟩ := pageM_dict ps keys.length hef hpf res hres
      rw [hks, pure_bind]
      have hksz : ks.size = ps[res].length := by
        have := congrArg List.length hksl
        simpa using this
      have hksel : ∀ i (hi : i < ks.size), bytesToList ks[i] = ps[res][i]'(by omega) := by
        intro i hi
        have := congrArg (fun l => l[i]?) hksl
        simp only [List.getElem?_map, Array.getElem?_toList] at this
        rw [Array.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega)] at this
        simpa using this
      obtain ⟨hjle, hjlt, hjge⟩ := firstNotBelow_spec ks k
      have hplr := hplen res hres
      have h64 := hp64 res hres
      -- the keys of page res, by rank
      have hkey : ∀ i (hi : i < ks.size), cmpBytesAt ks[i] k =
          cmpKey (keys[64 * res + i]'(by rw [hksz, hplr] at hi; omega)) (bytesToList k) := by
        intro i hi
        rw [cmpBytesAt_eq, hksel i hi, hpel res hres i (by omega)]
      let kL := bytesToList k
      have hcount := filter_prefix_length keys kL (64 * res + firstNotBelow ks k)
        (by rw [hksz, hplr] at hjle; omega)
        (by
          intro i hi hin
          by_cases hlo : i < 64 * res
          · -- before page res: below its first key, which is not above k
            rcases hP with hP | hP
            · omega
            · rw [hFK res hres] at hP
              exact cmpKey_lt_of_lt_of_le _ _ _ (strictlySorted_lt keys hsorted i (64 * res) hi h64 hlo) hP
          · have hr := hjlt (i - 64 * res) (by omega) (by omega)
            rw [hkey _ (by omega)] at hr
            have e2 : 64 * res + (i - 64 * res) = i := by omega
            simp only [e2] at hr
            exact hr)
        (by
          intro i hi hin
          by_cases hin2 : i < 64 * res + ks.size
          · -- in page res, at or after the first key not below k
            have hj : firstNotBelow ks k < ks.size := by omega
            have hnb := hjge hj
            rw [hkey _ hj] at hnb
            exact cmpKey_not_lt_of_le _ _ _ hnb
              (sorted_le keys hsorted _ i _ hi (by omega))
          · -- after page res: page res + 1 exists and its first key is above k
            rcases hQ with hQ | hQ
            · rw [hksz, hplr] at hin2
              rw [hlen] at hQ
              omega
            · have hn1 : res + 1 < ps.length := by
                rcases Nat.lt_or_ge (res + 1) ps.length with h' | h'
                · exact h'
                · rw [hksz, hplr] at hin2; rw [hlen] at h'; omega
              rw [hFK (res + 1) hn1] at hQ
              intro hlt
              have hle := sorted_le keys hsorted (64 * (res + 1)) i (hp64 _ hn1) hi
                (by rw [hksz, hplr] at hin2; omega)
              have := cmpKey_lt_of_lt_of_le' _ _ _ hle hlt
              rw [hQ] at this
              cases this)
      rw [hcount]
      congr 1
      rw [hksz, hplr] at hjle
      simp only [pageTerms]
      omega
  · cases h
where
  cmpKey_lt_of_lt_of_le' (b a c : List UInt8) (h2 : cmpKey b a ≠ .gt) (h : cmpKey a c = .lt) :
      cmpKey b c = .lt := cmpKey_not_lt_of_le.cmpKey_lt_of_lt_of_le' b a c h2 h

/-! ## `firstNotBelow` before the refactor, compared on samples -/

private def firstNotBelowOld (ks : Array ByteArray) (k : ByteArray) : Nat := Id.run do
  for i in [0:ks.size] do
    if cmpBytesAt ks[i]! k != .lt then return i
  return ks.size

private def samplePage : Array ByteArray :=
  #[⟨#[2, 97]⟩, ⟨#[2, 97, 98]⟩, ⟨#[2, 98]⟩, ⟨#[3]⟩, ⟨#[3, 0, 1]⟩]

#guard [ByteArray.mk #[], ⟨#[1]⟩, ⟨#[2, 97]⟩, ⟨#[2, 97, 0]⟩, ⟨#[2, 99]⟩, ⟨#[3, 0]⟩, ⟨#[3, 0, 1]⟩, ⟨#[9]⟩].all
  fun k => firstNotBelow samplePage k == firstNotBelowOld samplePage k &&
    firstNotBelow #[] k == firstNotBelowOld #[] k

end L4Factoidal.Storage.Sbm11.DictRange
