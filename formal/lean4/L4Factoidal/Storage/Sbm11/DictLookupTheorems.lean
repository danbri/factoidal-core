/-
L4Factoidal.Storage.Sbm11.DictLookupTheorems — string-to-id lookup over the
bytes the dictionary encoder writes (lemma L1d of
`docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776,
https://github.com/danbri/factoidal/issues/792 item 4).

Part 1: the order and the pages.

* `cmpBytesAt_eq`: `cmpBytesAt a b = cmpKey (bytesToList a) (bytesToList b)`.
* `cmpKey` is a strict total order: `cmpKey_eq_iff`, `cmpKey_swap`,
  `cmpKey_lt_trans`.
* `strictlySorted_lt`: a strictly sorted list is pairwise increasing.
* `chunk_getElem`, `chunk64_length`: page `i` of `chunk n l` is
  `(l.drop (n * i)).take n`; there are `⌈len / 64⌉` pages.
* `indexInPage_some`, `indexInPage_none`: the page scan finds a key exactly
  when it is in the page.

Part 2: the bytes `encodeDict?` writes, read through `fetchOf` (`m = Id`).

* `parseGdxHeader_gdxBytes`, `entryM_gdxBytes`: the GDX1 header and entries.
* `pageBytesM_dict`, `firstKeyAt_page`, `pageM_dict`: page `i` of GDV1, its
  first key and its keys.

Part 3: `searchPagesM_spec`, the binary search over the pages' first keys.

Part 4: `lookupM_encodeDict`. For `encodeDict? keys = some (v, x)` and any
`k`, the GDX1 header decodes to the key and page counts, and `lookupM` over
those bytes answers without error a result `res` with
`res = some r ↔ keys[r]? = some (bytesToList k)`: the rank of `k` when it is
a key, `none` when it is not. The only hypothesis is the encoder's output.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.DictTheorems
import L4Factoidal.Storage.Sbm11.DictFastTheorems

namespace L4Factoidal.Storage.Sbm11.Dict

open L4Factoidal (two32 two64)

/-! ## Byte order -/

private theorem get!_eq (b : ByteArray) (i : Nat) (h : i < b.size) : b.get! i = b[i] := by
  simp [ByteArray.get!, ByteArray.getElem_eq_getElem_data, getElem!_pos, h]

theorem cmpBytesAtGo_eq (a b : ByteArray) : ∀ k i, i ≤ min a.size b.size → min a.size b.size - i < k →
    cmpBytesAtGo a b (min a.size b.size) k i = cmpKey ((bytesToList a).drop i) ((bytesToList b).drop i) := by
  intro k
  induction k with
  | zero => intro i _ h; omega
  | succ k ih =>
    intro i hi hk
    simp only [cmpBytesAtGo]
    by_cases hlt : i < min a.size b.size
    · rw [if_pos hlt]
      have ha : i < a.size := by omega
      have hb : i < b.size := by omega
      rw [drop_bytesToList_cons a i ha, drop_bytesToList_cons b i hb, get!_eq a i ha, get!_eq b i hb]
      simp only [cmpKey]
      split
      · rfl
      · split
        · rfl
        · exact ih (i + 1) (by omega) (by omega)
    · rw [if_neg hlt]
      have hi' : i = min a.size b.size := by omega
      subst hi'
      by_cases hab : a.size ≤ b.size
      · rw [drop_bytesToList_of_le a _ (by omega)]
        by_cases hba : b.size ≤ a.size
        · rw [drop_bytesToList_of_le b _ (by omega)]
          simp only [cmpKey]
          rw [show a.size = b.size by omega]
          simp
        · rw [drop_bytesToList_cons b _ (by omega)]
          simp only [cmpKey]
          simp only [compare, compareOfLessAndEq]
          rw [if_pos (by omega)]
      · rw [drop_bytesToList_of_le b _ (by omega), drop_bytesToList_cons a _ (by omega)]
        simp only [cmpKey]
        simp only [compare, compareOfLessAndEq]
        rw [if_neg (by omega), if_neg (by omega)]

/-- The byte-array comparison is the list comparison of the round trip. -/
theorem cmpBytesAt_eq (a b : ByteArray) : cmpBytesAt a b = cmpKey (bytesToList a) (bytesToList b) := by
  unfold cmpBytesAt
  have := cmpBytesAtGo_eq a b (min a.size b.size + 1) 0 (Nat.zero_le _) (by omega)
  simpa using this

/-! ## `cmpKey` is a strict total order -/

theorem cmpKey_eq_iff : ∀ (a b : List UInt8), cmpKey a b = .eq ↔ a = b := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [cmpKey]
  | cons x xs ih =>
    intro b
    cases b with
    | nil => simp [cmpKey]
    | cons y ys =>
      simp only [cmpKey, List.cons.injEq]
      by_cases h1 : x < y
      · rw [if_pos h1]; simp only [reduceCtorEq, false_iff, not_and]; intro he; subst he
        exact absurd h1 (UInt8.lt_irrefl x)
      · rw [if_neg h1]
        by_cases h2 : y < x
        · rw [if_pos h2]; simp only [reduceCtorEq, false_iff, not_and]; intro he; subst he
          exact absurd h2 (UInt8.lt_irrefl x)
        · rw [if_neg h2, ih ys]
          have : x = y := by
            apply UInt8.toNat_inj.mp
            rw [UInt8.lt_iff_toNat_lt] at h1 h2
            omega
          simp [this]

theorem cmpKey_swap : ∀ (a b : List UInt8), cmpKey a b = .lt ↔ cmpKey b a = .gt := by
  intro a
  induction a with
  | nil => intro b; cases b <;> simp [cmpKey]
  | cons x xs ih =>
    intro b
    cases b with
    | nil => simp [cmpKey]
    | cons y ys =>
      simp only [cmpKey]
      by_cases h1 : x < y
      · have h2 : ¬ y < x := by rw [UInt8.lt_iff_toNat_lt] at h1 ⊢; omega
        rw [if_pos h1, if_neg h2, if_pos h1]
        simp
      · rw [if_neg h1]
        by_cases h2 : y < x
        · rw [if_pos h2, if_pos h2]; simp
        · rw [if_neg h2, if_neg h2, if_neg h1]
          exact ih ys

theorem cmpKey_lt_trans : ∀ (a b c : List UInt8), cmpKey a b = .lt → cmpKey b c = .lt → cmpKey a c = .lt := by
  intro a
  induction a with
  | nil =>
    intro b c h1 h2
    cases c with
    | nil => cases b <;> simp [cmpKey] at h1 h2
    | cons _ _ => rfl
  | cons x xs ih =>
    intro b c h1 h2
    cases b with
    | nil => simp [cmpKey] at h1
    | cons y ys =>
      cases c with
      | nil => simp [cmpKey] at h2
      | cons z zs =>
        simp only [cmpKey] at h1 h2 ⊢
        have tx := UInt8.lt_iff_toNat_lt (a := x) (b := y)
        have ty := UInt8.lt_iff_toNat_lt (a := y) (b := z)
        have tz := UInt8.lt_iff_toNat_lt (a := x) (b := z)
        have tx' := UInt8.lt_iff_toNat_lt (a := y) (b := x)
        have ty' := UInt8.lt_iff_toNat_lt (a := z) (b := y)
        have tz' := UInt8.lt_iff_toNat_lt (a := z) (b := x)
        have exy : x.toNat = y.toNat → x = y := fun h => UInt8.toNat_inj.mp h
        have eyz : y.toNat = z.toNat → y = z := fun h => UInt8.toNat_inj.mp h
        by_cases a1 : x < y
        · rw [if_pos a1] at h1
          by_cases b1 : y < z
          · rw [if_pos (tz.mpr (by have := tx.mp a1; have := ty.mp b1; omega))]
          · rw [if_neg b1] at h2
            by_cases b2 : z < y
            · rw [if_pos b2] at h2; cases h2
            · rw [if_pos (tz.mpr (by
                have := tx.mp a1; have e := eyz (by
                  have := mt ty.mpr b1; have := mt ty'.mpr b2; omega)
                rw [← e]; exact this))]
        · rw [if_neg a1] at h1
          by_cases a2 : y < x
          · rw [if_pos a2] at h1; cases h1
          · rw [if_neg a2] at h1
            have e := exy (by have := mt tx.mpr a1; have := mt tx'.mpr a2; omega)
            subst e
            by_cases b1 : x < z
            · rw [if_pos b1]
            · rw [if_neg b1] at h2 ⊢
              by_cases b2 : z < x
              · rw [if_pos b2] at h2; cases h2
              · rw [if_neg b2] at h2 ⊢
                exact ih ys zs h1 h2

/-! ## Sorted keys -/

theorem strictlySortedGo_lt : ∀ (ks : List Key) (prev : Key), strictlySortedGo prev ks = true →
    (∀ k ∈ ks, cmpKey prev k = .lt) ∧ ks.Pairwise (fun a b => cmpKey a b = .lt) := by
  intro ks
  induction ks with
  | nil => intro _ _; exact ⟨fun _ h => absurd h List.not_mem_nil, List.Pairwise.nil⟩
  | cons k ks ih =>
    intro prev h
    simp only [strictlySortedGo] at h
    split at h
    · rename_i hpk
      have hpk' : cmpKey prev k = .lt := by simpa using hpk
      obtain ⟨h1, h2⟩ := ih k h
      refine ⟨fun x hx => ?_, List.Pairwise.cons h1 h2⟩
      rcases List.mem_cons.mp hx with hx | hx
      · subst hx; exact hpk'
      · exact cmpKey_lt_trans _ _ _ hpk' (h1 x hx)
    · cases h

/-- A strictly sorted list is pairwise increasing in `cmpKey`. -/
theorem strictlySorted_lt (ks : List Key) (h : strictlySorted ks = true) (i j : Nat)
    (hi : i < ks.length) (hj : j < ks.length) (hij : i < j) : cmpKey ks[i] ks[j] = .lt := by
  cases ks with
  | nil => simp at hi
  | cons k r =>
    simp only [strictlySorted] at h
    obtain ⟨h1, h2⟩ := strictlySortedGo_lt r k h
    exact List.pairwise_iff_getElem.mp (List.Pairwise.cons h1 h2) i j hi hj hij

/-! ## Pages -/

theorem chunkGo_acc {α : Type} (n : Nat) : ∀ f (l : List α) acc,
    chunkGo n f l acc = acc.reverse ++ chunkGo n f l [] := by
  intro f
  induction f with
  | zero => intro l acc; simp [chunkGo]
  | succ f ih =>
    intro l acc
    cases l with
    | nil => simp [chunkGo]
    | cons x xs =>
      simp only [chunkGo]
      rw [ih, ih _ [_]]
      simp

theorem chunkGo_fuel {α : Type} (n : Nat) (hn : 0 < n) : ∀ f f' (l : List α),
    l.length < f → l.length < f' → chunkGo n f l [] = chunkGo n f' l [] := by
  intro f
  induction f with
  | zero => intro _ _ h; omega
  | succ f ih =>
    intro f' l h h'
    cases f' with
    | zero => omega
    | succ f' =>
      cases l with
      | nil => simp [chunkGo]
      | cons x xs =>
        simp only [chunkGo]
        rw [chunkGo_acc, chunkGo_acc n f', ih f' _ (by simp at h ⊢; omega) (by simp at h' ⊢; omega)]

theorem chunk_cons {α : Type} (n : Nat) (hn : 0 < n) (l : List α) (hl : l ≠ []) :
    chunk n l = l.take n :: chunk n (l.drop n) := by
  unfold chunk
  cases l with
  | nil => exact absurd rfl hl
  | cons x xs =>
    rw [show chunkGo n ((x :: xs).length + 1) (x :: xs) [] =
        chunkGo n ((x :: xs).length) ((x :: xs).drop n) [(x :: xs).take n] from rfl]
    rw [chunkGo_acc, chunkGo_fuel n hn _ ((x :: xs).drop n).length.succ _
      (by simp; omega) (by simp)]
    rfl

theorem chunk_nil {α : Type} (n : Nat) : chunk n ([] : List α) = [] := rfl

theorem chunk_getElem {α : Type} (n : Nat) (hn : 0 < n) : ∀ (i : Nat) (l : List α)
    (hi : i < (chunk n l).length), (chunk n l)[i] = (l.drop (n * i)).take n := by
  intro i
  induction i with
  | zero =>
    intro l hi
    cases l with
    | nil => simp [chunk_nil] at hi
    | cons x xs => simp only [chunk_cons n hn _ (by simp : x :: xs ≠ []), List.getElem_cons_zero]; simp
  | succ i ih =>
    intro l hi
    cases l with
    | nil => simp [chunk_nil] at hi
    | cons x xs =>
      have hc := chunk_cons n hn (x :: xs) (by simp)
      have hi' : i < (chunk n ((x :: xs).drop n)).length := by
        rw [hc] at hi; simpa using hi
      simp only [hc, List.getElem_cons_succ]
      rw [ih _ hi', List.drop_drop, Nat.mul_succ, Nat.add_comm]

/-! ## The page scan -/

theorem ba_beq_iff (a b : ByteArray) : (a == b) = true ↔ a = b := by
  show ByteArray.beq a b = true ↔ a = b
  unfold ByteArray.beq
  rw [beq_iff_eq]
  exact ⟨ByteArray.ext, fun h => h ▸ rfl⟩

theorem indexInPageGo_spec (ks : Array ByteArray) (k : ByteArray) : ∀ f i, ks.size - i ≤ f →
    (∀ x, indexInPageGo ks k f i = some x → i ≤ x ∧ x < ks.size ∧ ks[x]! = k) ∧
    (indexInPageGo ks k f i = none → ∀ x, i ≤ x → x < ks.size → ks[x]! ≠ k) := by
  intro f
  induction f with
  | zero =>
    intro i hi
    refine ⟨?_, ?_⟩
    · intro x h; simp [indexInPageGo] at h
    · intro _ x h1 h2; omega
  | succ f ih =>
    intro i hi
    simp only [indexInPageGo]
    by_cases hlt : i < ks.size
    · rw [if_pos hlt]
      by_cases he : (ks[i]! == k) = true
      · rw [if_pos he]
        have he' : ks[i]! = k := (ba_beq_iff _ _).mp he
        exact ⟨fun x h => by simp only [Option.some.injEq] at h; subst h; exact ⟨Nat.le_refl _, hlt, he'⟩,
          fun h => by cases h⟩
      · rw [if_neg he]
        obtain ⟨h1, h2⟩ := ih (i + 1) (by omega)
        refine ⟨fun x h => by have := h1 x h; exact ⟨by omega, this.2⟩, fun h x hx1 hx2 => ?_⟩
        by_cases hx : x = i
        · subst hx
          intro heq
          exact he ((ba_beq_iff _ _).mpr heq)
        · exact h2 h x (by omega) hx2
    · rw [if_neg hlt]
      refine ⟨?_, ?_⟩
      · intro x h; cases h
      · intro _ x h1 h2; omega

theorem indexInPage_some (ks : Array ByteArray) (k : ByteArray) (x : Nat) (h : indexInPage ks k = some x) :
    x < ks.size ∧ ks[x]! = k :=
  ((indexInPageGo_spec ks k ks.size 0 (by omega)).1 x h).2

theorem indexInPage_none (ks : Array ByteArray) (k : ByteArray) (h : indexInPage ks k = none) :
    ∀ x, x < ks.size → ks[x]! ≠ k :=
  fun x hx => (indexInPageGo_spec ks k ks.size 0 (by omega)).2 h x (Nat.zero_le _) hx

/-! ## Part 2: the bytes the encoder writes -/

/-- Positioned reads of an in-memory byte array: the store of `m = Id`. -/
def fetchOf (b : ByteArray) (off len : Nat) : Id ByteArray := b.extract off (off + len)

theorem bytesToList_mk (l : List UInt8) : bytesToList ⟨l.toArray⟩ = l := by simp [bytesToList]

theorem bytesToList_inj (a b : ByteArray) (h : bytesToList a = bytesToList b) : a = b :=
  ByteArray.ext (Array.toList_inj.mp h)

theorem drop_flatten_uniform {α : Type} (f : α → List UInt8) (w : Nat) (hf : ∀ a, (f a).length = w) :
    ∀ (l : List α) (k : Nat), ((l.map f).flatten).drop (w * k) = ((l.drop k).map f).flatten := by
  intro l
  induction l with
  | nil => intro k; simp
  | cons x xs ih =>
    intro k
    cases k with
    | zero => simp
    | succ k =>
      rw [List.map_cons, List.flatten_cons, show w * (k + 1) = (f x).length + w * k by
        rw [hf]; rw [Nat.mul_succ]; omega, List.drop_length_add_append, ih]
      rfl

theorem word64At_of_drop (b : ByteArray) (p : Nat) (x0 x1 x2 x3 x4 x5 x6 x7 : UInt8) (rest : List UInt8)
    (h : (bytesToList b).drop p = x0 :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: rest) :
    word64At b p = x0.toNat + x1.toNat * 256 + x2.toNat * 65536 + x3.toNat * 16777216 +
      x4.toNat * 4294967296 + x5.toNat * 1099511627776 + x6.toNat * 281474976710656 +
      x7.toNat * 72057594037927936 := by
  have hs : p + 8 ≤ b.size := by
    have := congrArg List.length h
    simp only [List.length_drop, bytesToList_length, List.length_cons] at this; omega
  rw [drop_bytesToList_cons b p (by omega), drop_bytesToList_cons b (p + 1) (by omega),
    drop_bytesToList_cons b (p + 2) (by omega), drop_bytesToList_cons b (p + 3) (by omega),
    drop_bytesToList_cons b (p + 4) (by omega), drop_bytesToList_cons b (p + 5) (by omega),
    drop_bytesToList_cons b (p + 6) (by omega), drop_bytesToList_cons b (p + 7) (by omega)] at h
  simp only [List.cons.injEq] at h
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, -⟩ := h
  unfold word64At
  rw [get!_eq b p (by omega), get!_eq b (p + 1) (by omega), get!_eq b (p + 2) (by omega),
    get!_eq b (p + 3) (by omega), get!_eq b (p + 4) (by omega), get!_eq b (p + 5) (by omega),
    get!_eq b (p + 6) (by omega), get!_eq b (p + 7) (by omega), e0, e1, e2, e3, e4, e5, e6, e7]

theorem word32At_of_drop (b : ByteArray) (p : Nat) (x0 x1 x2 x3 : UInt8) (rest : List UInt8)
    (h : (bytesToList b).drop p = x0 :: x1 :: x2 :: x3 :: rest) :
    word32At b p = x0.toNat + x1.toNat * 256 + x2.toNat * 65536 + x3.toNat * 16777216 := by
  have hs : p + 4 ≤ b.size := by
    have := congrArg List.length h
    simp only [List.length_drop, bytesToList_length, List.length_cons] at this; omega
  rw [drop_bytesToList_cons b p (by omega), drop_bytesToList_cons b (p + 1) (by omega),
    drop_bytesToList_cons b (p + 2) (by omega), drop_bytesToList_cons b (p + 3) (by omega)] at h
  simp only [List.cons.injEq] at h
  obtain ⟨e0, e1, e2, e3, -⟩ := h
  unfold word32At
  rw [get!_eq b p (by omega), get!_eq b (p + 1) (by omega), get!_eq b (p + 2) (by omega),
    get!_eq b (p + 3) (by omega), e0, e1, e2, e3]

theorem word32At_write (b : ByteArray) (p : Nat) (n : UInt32) (rest : List UInt8)
    (h : (bytesToList b).drop p = L4Factoidal.Storage.writeU32LE n ++ rest) : word32At b p = n.toNat := by
  simp only [L4Factoidal.Storage.writeU32LE, List.cons_append, List.nil_append] at h
  rw [word32At_of_drop b p _ _ _ _ _ h]
  simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight]
  have := n.toNat_lt
  simp only [Nat.shiftRight_eq_div_pow, UInt32.toNat_ofNat, Nat.reduceMod, Nat.reducePow] at *
  omega

theorem word64At_write (b : ByteArray) (p : Nat) (n : UInt64) (rest : List UInt8)
    (h : (bytesToList b).drop p = L4Factoidal.Storage.writeU64LE n ++ rest) : word64At b p = n.toNat := by
  simp only [L4Factoidal.Storage.writeU64LE, L4Factoidal.Storage.writeU32LE, List.cons_append,
    List.nil_append] at h
  rw [word64At_of_drop b p _ _ _ _ _ _ _ _ _ h]
  simp only [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, UInt64.toNat_toUInt32, UInt64.toNat_shiftRight]
  have := n.toNat_lt
  simp only [Nat.shiftRight_eq_div_pow, UInt32.toNat_ofNat, UInt64.toNat_ofNat, Nat.reduceMod,
    Nat.reducePow] at *
  omega

/-! ### GDX1 -/

theorem gdxBytes_size (tc : Nat) (es : List DirEntry) :
    (gdxBytes tc es).length = 21 + 12 * es.length := by
  have : ∀ l : List DirEntry, ((l.map entryBytes).flatten).length = 12 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons e l ih =>
      simp only [List.map_cons, List.flatten_cons, List.length_append, ih, List.length_cons, entryBytes,
        L4Factoidal.Storage.writeU64LE_length, L4Factoidal.Storage.writeU32LE_length]
      omega
  simp only [gdxBytes, List.length_append, L4Factoidal.Storage.writeU64LE_length, this]
  rfl

theorem parseGdxHeader_gdxBytes (tc : Nat) (es : List DirEntry) (htc : tc < two64) (hn : es.length < two64) :
    parseGdxHeader ⟨(gdxBytes tc es).toArray⟩ = .ok ⟨tc, es.length⟩ := by
  have hsz : (⟨(gdxBytes tc es).toArray⟩ : ByteArray).size = 21 + 12 * es.length := by
    show (gdxBytes tc es).toArray.size = _
    rw [List.size_toArray, gdxBytes_size]
  unfold parseGdxHeader
  rw [if_neg (by rw [hsz]; simp [gdxHeaderBytes])]
  have hmag : bytesToList ((⟨(gdxBytes tc es).toArray⟩ : ByteArray).extract 0 5) = gdxMagic := by
    rw [bytesToList_extract, bytesToList_mk]
    simp [gdxBytes, gdxMagic]
  rw [if_neg (by rw [hmag]; simp)]
  have h5 : (bytesToList ⟨(gdxBytes tc es).toArray⟩).drop 5 =
      L4Factoidal.Storage.writeU64LE (UInt64.ofNat tc) ++
        (L4Factoidal.Storage.writeU64LE (UInt64.ofNat es.length) ++ (es.map entryBytes).flatten) := by
    rw [bytesToList_mk]; simp [gdxBytes, gdxMagic]
  have h13 : (bytesToList ⟨(gdxBytes tc es).toArray⟩).drop 13 =
      L4Factoidal.Storage.writeU64LE (UInt64.ofNat es.length) ++ (es.map entryBytes).flatten := by
    rw [show 13 = 5 + 8 from rfl, ← List.drop_drop, h5, List.drop_left' (L4Factoidal.Storage.writeU64LE_length _)]
  rw [word64At_write _ _ _ _ h5, word64At_write _ _ _ _ h13]
  simp only [UInt64.toNat_ofNat_of_lt' htc, UInt64.toNat_ofNat_of_lt' hn]

theorem entryM_gdxBytes (tc : Nat) (es : List DirEntry) (hfit : es.all entryFits = true)
    (i : Nat) (hi : i < es.length) :
    entryM (m := Id) (fetchOf ⟨(gdxBytes tc es).toArray⟩) i = pure es[i] := by
  have hdrop : (gdxBytes tc es).drop (gdxHeaderBytes + entrySize * i) =
      entryBytes es[i] ++ ((es.drop (i + 1)).map entryBytes).flatten := by
    have e21 : (gdxBytes tc es).drop 21 = (es.map entryBytes).flatten := by
      simp [gdxBytes, gdxMagic, List.drop_append]
    rw [show gdxHeaderBytes + entrySize * i = 21 + 12 * i by simp [gdxHeaderBytes, entrySize],
      ← List.drop_drop, e21, drop_flatten_uniform entryBytes 12 (fun e => by
        simp [entryBytes, L4Factoidal.Storage.writeU64LE_length, L4Factoidal.Storage.writeU32LE_length]),
      List.drop_eq_getElem_cons hi, List.map_cons, List.flatten_cons]
  let e12 := (⟨(gdxBytes tc es).toArray⟩ : ByteArray).extract (gdxHeaderBytes + entrySize * i)
    (gdxHeaderBytes + entrySize * i + entrySize)
  have hl : bytesToList e12 = entryBytes es[i] := by
    show bytesToList (ByteArray.extract _ _ _) = _
    rw [bytesToList_extract, bytesToList_mk, Nat.add_sub_cancel_left, hdrop]
    have : (entryBytes es[i]).length = entrySize := by
      simp [entryBytes, entrySize, L4Factoidal.Storage.writeU64LE_length, L4Factoidal.Storage.writeU32LE_length]
    rw [← this, List.take_left' rfl]
  have hsz : e12.size = entrySize := by
    rw [← bytesToList_length, hl]
    simp [entryBytes, entrySize, L4Factoidal.Storage.writeU64LE_length, L4Factoidal.Storage.writeU32LE_length]
  have hf := List.all_eq_true.mp hfit es[i] (List.getElem_mem hi)
  simp only [entryFits, Bool.and_eq_true, decide_eq_true_eq] at hf
  have hp : parseEntryBytes e12 = .ok es[i] := by
    unfold parseEntryBytes
    rw [if_neg (by rw [hsz]; simp)]
    have d0 : (bytesToList e12).drop 0 = L4Factoidal.Storage.writeU64LE (UInt64.ofNat es[i].pageOffset) ++
        L4Factoidal.Storage.writeU32LE (UInt32.ofNat es[i].pageLen) := by
      rw [hl]; simp [entryBytes]
    have d8 : (bytesToList e12).drop 8 = L4Factoidal.Storage.writeU32LE (UInt32.ofNat es[i].pageLen) ++ [] := by
      rw [hl]; simp [entryBytes, List.drop_left' (L4Factoidal.Storage.writeU64LE_length _)]
    rw [word64At_write _ _ _ _ d0, word32At_write _ _ _ _ d8, UInt64.toNat_ofNat_of_lt' hf.1,
      L4Factoidal.Storage.u32_toNat_ofNat_of_lt hf.2]
  have e1 : entryM (m := Id) (fetchOf ⟨(gdxBytes tc es).toArray⟩) i =
      (match parseEntryBytes e12 with
        | .ok e => (pure e : ExceptT String Id DirEntry) | .error e => throw e) := rfl
  rw [e1, hp]

/-! ### GDV1 pages -/

/-- The bytes of the pages before page `i`. -/
def pagesBefore (ps : List (List Key)) (i : Nat) : Nat := ((ps.take i).map fun p => (encodePage p).length).sum

theorem dirEntriesGo_acc (ps : List (List Key)) : ∀ off acc,
    dirEntriesGo ps off acc = acc.reverse ++ dirEntriesGo ps off [] := by
  induction ps with
  | nil => intro off acc; simp [dirEntriesGo]
  | cons p ps ih =>
    intro off acc
    simp only [dirEntriesGo]
    rw [ih, ih _ [_]]
    simp

theorem dirEntriesGo_getElem (ps : List (List Key)) : ∀ off i (hi : i < ps.length),
    (dirEntriesGo ps off [])[i]'(by rw [dirEntriesGo_length]; simpa using hi) =
      ⟨off + pagesBefore ps i, (encodePage ps[i]).length⟩ := by
  induction ps with
  | nil => intro off i hi; simp at hi
  | cons p ps ih =>
    intro off i hi
    have e : dirEntriesGo (p :: ps) off [] =
        ⟨off, (encodePage p).length⟩ :: dirEntriesGo ps (off + (encodePage p).length) [] := by
      simp only [dirEntriesGo]
      rw [dirEntriesGo_acc]
      simp
    simp only [e]
    cases i with
    | zero => simp [pagesBefore]
    | succ i =>
      simp only [List.getElem_cons_succ]
      rw [ih _ i (by simpa using hi)]
      simp only [pagesBefore, List.take_succ_cons, List.map_cons, List.sum_cons]
      congr 1
      omega

theorem gdvBytes_drop (ps : List (List Key)) (i : Nat) (hi : i < ps.length) :
    (gdvBytes ps).drop (6 + pagesBefore ps i) = encodePage ps[i] ++ ((ps.drop (i + 1)).map encodePage).flatten := by
  have hsplit : ps = ps.take i ++ ps[i] :: ps.drop (i + 1) := by
    conv => lhs; rw [← List.take_append_drop i ps]
    rw [List.drop_eq_getElem_cons hi]
  have hlen : ((ps.take i).map encodePage).flatten.length = pagesBefore ps i := by
    simp [pagesBefore, List.length_flatten, List.map_map, Function.comp_def]
  have hm : (ps.map encodePage).flatten = ((ps.take i).map encodePage).flatten ++
      (encodePage ps[i] ++ ((ps.drop (i + 1)).map encodePage).flatten) := by
    conv => lhs; rw [hsplit]
    rw [List.map_append, List.flatten_append, List.map_cons, List.flatten_cons]
  have : (gdvBytes ps) = gdvHeader ++ (((ps.take i).map encodePage).flatten ++
      (encodePage ps[i] ++ ((ps.drop (i + 1)).map encodePage).flatten)) := by
    unfold gdvBytes; rw [hm]
  rw [this, ← List.append_assoc, List.drop_left' (by rw [List.length_append, hlen]; rfl)]

/-- What the page fetch of the encoder's bytes returns: the bytes of the page. -/
theorem pageBytesM_dict (ps : List (List Key)) (tc : Nat) (hfit : (dirEntries ps).all entryFits = true)
    (i : Nat) (hi : i < ps.length) :
    ∃ pb, pageBytesM (m := Id) (fetchOf ⟨(gdxBytes tc (dirEntries ps)).toArray⟩) (fetchOf ⟨(gdvBytes ps).toArray⟩) i
      = pure pb ∧ bytesToList pb = encodePage ps[i] := by
  have hlen : (dirEntries ps).length = ps.length := by
    simp [dirEntries, dirEntriesGo_length]
  have hi' : i < (dirEntries ps).length := by omega
  have he := entryM_gdxBytes tc (dirEntries ps) hfit i hi'
  have hel : (dirEntries ps)[i] = ⟨6 + pagesBefore ps i, (encodePage ps[i]).length⟩ := by
    have := dirEntriesGo_getElem ps gdvHeader.length i hi
    unfold dirEntries
    exact this
  let pb := (⟨(gdvBytes ps).toArray⟩ : ByteArray).extract (6 + pagesBefore ps i)
    (6 + pagesBefore ps i + (encodePage ps[i]).length)
  have hpb : bytesToList pb = encodePage ps[i] := by
    show bytesToList (ByteArray.extract _ _ _) = _
    rw [bytesToList_extract, bytesToList_mk, Nat.add_sub_cancel_left, gdvBytes_drop ps i hi,
      List.take_left' rfl]
  have hsz : pb.size = (encodePage ps[i]).length := by rw [← bytesToList_length, hpb]
  refine ⟨pb, ?_, hpb⟩
  have e1 : pageBytesM (m := Id) (fetchOf ⟨(gdxBytes tc (dirEntries ps)).toArray⟩) (fetchOf ⟨(gdvBytes ps).toArray⟩) i =
      (do
        let e ← entryM (m := Id) (fetchOf ⟨(gdxBytes tc (dirEntries ps)).toArray⟩) i
        let b := (⟨(gdvBytes ps).toArray⟩ : ByteArray).extract e.pageOffset (e.pageOffset + e.pageLen)
        if b.size != e.pageLen then throw s!"GDV1: short read of page {i}"
        pure b) := rfl
  rw [e1, he, pure_bind, hel]
  simp only
  rw [show (⟨(gdvBytes ps).toArray⟩ : ByteArray).extract (6 + pagesBefore ps i)
      (6 + pagesBefore ps i + (encodePage ps[i]).length) = pb from rfl, hsz]
  simp

/-! ### One page -/

theorem firstKeyAt_page (b : ByteArray) (k0 : Key) (rest : List Key) (hb : bytesToList b = encodePage (k0 :: rest))
    (hfit : pageFits (k0 :: rest) = true) : ∃ fk, firstKeyAt b = some fk ∧ bytesToList fk = k0 := by
  simp only [pageFits, Bool.and_eq_true, decide_eq_true_eq, List.all_cons] at hfit
  obtain ⟨hlen, hk0, -⟩ := hfit
  have hlen' : rest.length + 1 < 4294967296 := by simpa [two32] using hlen
  have hk0' : k0.length < 4294967296 := by simpa [two32] using hk0
  have g1 := getSmallAt_spec b 0
  rw [List.drop_zero, hb] at g1
  simp only [encodePage, List.length_cons, List.append_assoc] at g1
  rw [getSmall_putSmall _ _ hlen'] at g1
  unfold firstKeyAt
  cases hg1 : getSmallAt b 0 with
  | none => rw [hg1] at g1; cases g1
  | some p1 =>
    obtain ⟨c, i1⟩ := p1
    rw [hg1] at g1
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at g1
    obtain ⟨rfl, hd1⟩ := g1
    dsimp only
    rw [if_neg (by simp)]
    have hd1' : (bytesToList b).drop i1 = putSmall k0.length ++ (k0 ++ encodeEntries k0 rest) := by
      rw [hb]; simpa [encodePage] using hd1
    have g2 := getSmallAt_spec b i1
    rw [hd1', getSmall_putSmall _ _ hk0'] at g2
    cases hg2 : getSmallAt b i1 with
    | none => rw [hg2] at g2; cases g2
    | some p2 =>
      obtain ⟨len, i2⟩ := p2
      rw [hg2] at g2
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at g2
      obtain ⟨rfl, hd2⟩ := g2
      dsimp only
      have hi2 := getSmallAt_le b _ _ _ hg2
      have hl := congrArg List.length hd2
      simp only [List.length_drop, bytesToList_length, List.length_append] at hl
      rw [if_pos (by omega)]
      refine ⟨_, rfl, ?_⟩
      rw [bytesToList_extract, Nat.add_sub_cancel_left, hd2, List.take_left' rfl]

theorem decodeEntriesAt_le (b : ByteArray) : ∀ n (prev : ByteArray) (acc : Array ByteArray) i ks j,
    i ≤ b.size → decodeEntriesAt b n prev acc i = some (ks, j) → j ≤ b.size := by
  intro n
  induction n with
  | zero => intro prev acc i ks j hi h; simp only [decodeEntriesAt, Option.some.injEq, Prod.mk.injEq] at h; omega
  | succ n ih =>
    intro prev acc i ks j hi h
    simp only [decodeEntriesAt] at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i hle
          exact ih _ _ _ _ _ hle h
        · cases h

theorem decodePageAt_le (b : ByteArray) (i : Nat) (ks : Array ByteArray) (j : Nat)
    (h : decodePageAt b i = some (ks, j)) : j ≤ b.size := by
  unfold decodePageAt at h
  split at h
  · cases h
  · rename_i c i1 hg1
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]; exact getSmallAt_le b _ _ _ hg1
    · split at h
      · cases h
      · split at h
        · rename_i hle
          exact decodeEntriesAt_le b _ _ _ _ _ _ hle h
        · cases h

theorem pageM_dict (ps : List (List Key)) (tc : Nat) (hfit : (dirEntries ps).all entryFits = true)
    (hpf : ps.all pageFits = true) (i : Nat) (hi : i < ps.length) :
    ∃ ks, pageM (m := Id) (fetchOf ⟨(gdxBytes tc (dirEntries ps)).toArray⟩) (fetchOf ⟨(gdvBytes ps).toArray⟩) i
      = pure ks ∧ ks.toList.map bytesToList = ps[i] := by
  obtain ⟨pb, hpb, hl⟩ := pageBytesM_dict ps tc hfit i hi
  have hpf' := List.all_eq_true.mp hpf ps[i] (List.getElem_mem hi)
  have hd := decodePageAt_eq pb 0
  rw [List.drop_zero, hl, ← List.append_nil (encodePage ps[i]), decodePage_encodePage _ _ hpf'] at hd
  cases hdp : decodePageAt pb 0 with
  | none => rw [hdp] at hd; cases hd
  | some q =>
    obtain ⟨ks, j⟩ := q
    rw [hdp] at hd
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
    obtain ⟨hks, hj⟩ := hd
    have hjle := decodePageAt_le pb 0 ks j hdp
    have hsz : pb.size = (encodePage ps[i] ++ []).length := by
      rw [List.append_nil, ← hl, bytesToList_length]
    have hjge : pb.size ≤ j := by
      have := congrArg List.length hj
      simp only [List.length_drop, List.length_nil] at this
      omega
    refine ⟨ks, ?_, hks⟩
    have e1 : pageM (m := Id) (fetchOf ⟨(gdxBytes tc (dirEntries ps)).toArray⟩) (fetchOf ⟨(gdvBytes ps).toArray⟩) i =
        (do
          let b ← pageBytesM (m := Id) (fetchOf ⟨(gdxBytes tc (dirEntries ps)).toArray⟩)
            (fetchOf ⟨(gdvBytes ps).toArray⟩) i
          match decodePageAt b 0 with
          | some (ks, j) => if j == b.size then pure ks else throw s!"GDV1: page {i} has trailing bytes"
          | none => throw s!"GDV1: page {i} does not decode") := rfl
    rw [e1, hpb, pure_bind, hdp]
    simp only
    rw [if_pos (by simp; omega)]

/-! ## Part 3: the page search -/

/-- The binary search over pages keeps its invariant: page `lo` (or page 0)
    has a first key not above `k`, page `hi` (or the end) one above `k`. It
    returns a page `res` with the same property towards `res + 1`. -/
theorem searchPagesM_spec (fGdx fGdv : Nat → Nat → Id ByteArray) (k : ByteArray) (pc : Nat)
    (FK : Nat → Key)
    (hpage : ∀ j, j < pc → ∃ pb fk, pageBytesM (m := Id) fGdx fGdv j = pure pb ∧
      firstKeyAt pb = some fk ∧ bytesToList fk = FK j) :
    ∀ f lo hi probes, lo < hi → hi ≤ pc → hi - lo ≤ 2 ^ f →
      (lo = 0 ∨ cmpKey (FK lo) (bytesToList k) ≠ .gt) →
      (hi = pc ∨ cmpKey (FK hi) (bytesToList k) = .gt) →
      ∃ res pr, searchPagesM (m := Id) fGdx fGdv k f lo hi probes = pure (res, pr) ∧ lo ≤ res ∧ res < hi ∧
        (res = 0 ∨ cmpKey (FK res) (bytesToList k) ≠ .gt) ∧
        (res + 1 = pc ∨ cmpKey (FK (res + 1)) (bytesToList k) = .gt) := by
  intro f
  induction f with
  | zero =>
    intro lo hi probes hlh hpc hs hlo hhi
    have : hi = lo + 1 := by simp at hs; omega
    subst this
    exact ⟨lo, probes, rfl, Nat.le_refl _, by omega, hlo, hhi⟩
  | succ f ih =>
    intro lo hi probes hlh hpc hs hlo hhi
    have hp2 : 2 ^ (f + 1) = 2 * 2 ^ f := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hstop : lo + 1 ≥ hi
    · have : hi = lo + 1 := by omega
      subst this
      refine ⟨lo, probes, ?_, Nat.le_refl _, by omega, hlo, hhi⟩
      show (if lo + 1 ≥ lo + 1 then pure (lo, probes) else _) = _
      rw [if_pos (Nat.le_refl _)]
    · obtain ⟨pb, fk, hpb, hfk, hfkl⟩ := hpage ((lo + hi) / 2) (by omega)
      have e : searchPagesM (m := Id) fGdx fGdv k (f + 1) lo hi probes =
          (do
            let b ← pageBytesM (m := Id) fGdx fGdv ((lo + hi) / 2)
            match firstKeyAt b with
            | none => throw s!"GDV1: page {(lo + hi) / 2} has no first key"
            | some fk =>
              match cmpBytesAt fk k with
              | .gt => searchPagesM fGdx fGdv k f lo ((lo + hi) / 2) (probes + 1)
              | _ => searchPagesM fGdx fGdv k f ((lo + hi) / 2) hi (probes + 1)) := by
        show (if lo + 1 ≥ hi then pure (lo, probes) else _) = _
        rw [if_neg hstop]
        rfl
      rw [e, hpb, pure_bind]
      simp only [hfk]
      rw [cmpBytesAt_eq, hfkl]
      cases hc : cmpKey (FK ((lo + hi) / 2)) (bytesToList k) with
      | gt =>
        obtain ⟨res, pr, h1, h2, h3, h4, h5⟩ := ih lo ((lo + hi) / 2) (probes + 1) (by omega) (by omega)
          (by omega) hlo (Or.inr hc)
        exact ⟨res, pr, h1, h2, by omega, h4, h5⟩
      | lt =>
        obtain ⟨res, pr, h1, h2, h3, h4, h5⟩ := ih ((lo + hi) / 2) hi (probes + 1) (by omega) hpc
          (by omega) (Or.inr (by rw [hc]; simp)) hhi
        exact ⟨res, pr, h1, by omega, h3, h4, h5⟩
      | eq =>
        obtain ⟨res, pr, h1, h2, h3, h4, h5⟩ := ih ((lo + hi) / 2) hi (probes + 1) (by omega) hpc
          (by omega) (Or.inr (by rw [hc]; simp)) hhi
        exact ⟨res, pr, h1, by omega, h3, h4, h5⟩

/-! ## Part 4: lookup -/

theorem chunk64_length {α : Type} : ∀ (n : Nat) (l : List α), l.length = n →
    (chunk pageTerms l).length = (n + 63) / 64 := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro l hl
    cases l with
    | nil => simp at hl; subst hl; rfl
    | cons x xs =>
      have hn : n = xs.length + 1 := by simp at hl; omega
      subst hn
      rw [chunk_cons pageTerms (by decide) _ (by simp), List.length_cons,
        ih ((x :: xs).drop pageTerms).length (by simp [pageTerms]; omega) _ rfl]
      simp only [List.length_drop, List.length_cons, pageTerms]
      omega

/-- Keys of a strictly sorted list at two positions, the first not after the
    second: the first is not above the second. -/
theorem sorted_le (ks : List Key) (h : strictlySorted ks = true) (a b : Nat) (ha : a < ks.length)
    (hb : b < ks.length) (hab : a ≤ b) : cmpKey ks[a] ks[b] ≠ .gt := by
  rcases Nat.lt_or_eq_of_le hab with hlt | heq
  · rw [strictlySorted_lt ks h a b ha hb hlt]; simp
  · subst heq; rw [(cmpKey_eq_iff _ _).mpr rfl]; simp

/-- A strictly sorted list has no repeated key. -/
theorem sorted_inj (ks : List Key) (h : strictlySorted ks = true) (a b : Nat) (ha : a < ks.length)
    (hb : b < ks.length) (he : ks[a] = ks[b]) : a = b := by
  rcases Nat.lt_trichotomy a b with hlt | heq | hgt
  · have := strictlySorted_lt ks h a b ha hb hlt
    rw [he, (cmpKey_eq_iff _ _).mpr rfl] at this; cases this
  · exact heq
  · have := strictlySorted_lt ks h b a hb ha hgt
    rw [he, (cmpKey_eq_iff _ _).mpr rfl] at this; cases this

/-- String-to-id over the bytes `encodeDict?` writes: the header decodes to
    the key and page counts, and `lookupM` answers, without error, `some r`
    exactly when `r` is the rank of `k` in the key list (and so `none`
    exactly when `k` is not a key). -/
theorem lookupM_encodeDict (keys : List Key) (v x : List UInt8) (h : encodeDict? keys = some (v, x))
    (k : ByteArray) :
    parseGdxHeader ⟨x.toArray⟩ = .ok ⟨keys.length, (chunk pageTerms keys).length⟩ ∧
    ∃ res probes, lookupM (m := Id) (fetchOf ⟨x.toArray⟩) (fetchOf ⟨v.toArray⟩)
        ⟨keys.length, (chunk pageTerms keys).length⟩ k = pure (res, probes) ∧
      ∀ r, res = some r ↔ keys[r]? = some (bytesToList k) := by
  unfold encodeDict? at h
  dsimp only at h
  split at h
  · rename_i hadm
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [dictAdmitted, Bool.and_eq_true, decide_eq_true_eq] at hadm
    obtain ⟨⟨⟨⟨hsorted, hmax⟩, hpcl⟩, hpf⟩, hef⟩ := hadm
    -- names
    generalize hps : chunk pageTerms keys = ps at *
    have hlen : ps.length = (keys.length + 63) / 64 := by rw [← hps]; exact chunk64_length _ keys rfl
    have hesl : (dirEntries ps).length = ps.length := by simp [dirEntries, dirEntriesGo_length]
    refine ⟨?_, ?_⟩
    · have := parseGdxHeader_gdxBytes keys.length (dirEntries ps)
        (by have hm : maxTerms = 1152921504606846976 := rfl; simp only [two64]; omega)
        (by rw [hesl]; exact hpcl)
      rw [hesl] at this
      exact this
    -- pages
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
    -- the lookup, unfolded
    have e : lookupM (m := Id) (fetchOf ⟨(gdxBytes keys.length (dirEntries ps)).toArray⟩)
        (fetchOf ⟨(gdvBytes ps).toArray⟩) ⟨keys.length, ps.length⟩ k =
        (do
          let (lo, probes) ← searchPagesM (m := Id) (fetchOf ⟨(gdxBytes keys.length (dirEntries ps)).toArray⟩)
            (fetchOf ⟨(gdvBytes ps).toArray⟩) k (Nat.log2 ps.length + 2) 0 ps.length 0
          if ps.length == 0 then return (none, probes)
          let ks ← pageM (m := Id) (fetchOf ⟨(gdxBytes keys.length (dirEntries ps)).toArray⟩)
            (fetchOf ⟨(gdvBytes ps).toArray⟩) lo
          match indexInPage ks k with
          | some i => return (some (lo * pageTerms + i), probes + 1)
          | none => return (none, probes + 1)) := rfl
    rw [e]
    by_cases hpc0 : ps.length = 0
    · -- no page: no key
      have hk0 : keys = [] := by
        apply List.eq_nil_of_length_eq_zero; rw [hpc0] at hlen; omega
      refine ⟨none, 0, ?_, ?_⟩
      · rw [hpc0]; rfl
      · intro r; subst hk0; simp
    · obtain ⟨res, pr, hs, _, hres, hP, hQ⟩ := searchPagesM_spec _ _ k ps.length FK hfirst
        (Nat.log2 ps.length + 2) 0 ps.length 0 (by omega) (Nat.le_refl _)
        (by
          have := @Nat.lt_log2_self ps.length
          have h2 : 2 ^ (Nat.log2 ps.length + 1) ≤ 2 ^ (Nat.log2 ps.length + 2) :=
            Nat.pow_le_pow_right (by omega) (by omega)
          omega)
        (Or.inl rfl) (Or.inl rfl)
      rw [hs, pure_bind]
      simp only
      rw [if_neg (by simpa using hpc0)]
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
      cases hidx : indexInPage ks k with
      | some i =>
        obtain ⟨hi, hik⟩ := indexInPage_some ks k i hidx
        rw [getElem!_pos ks i hi] at hik
        refine ⟨some (res * pageTerms + i), pr + 1, rfl, ?_⟩
        have hrank : keys[64 * res + i]'(by have := hp64 res hres; rw [hksz, hplen res hres] at hi; omega) =
            bytesToList k := by
          rw [← hik, hksel i hi, hpel res hres i (by omega)]
        intro r
        constructor
        · intro hr
          simp only [Option.some.injEq] at hr
          subst hr
          rw [show res * pageTerms + i = 64 * res + i by simp [pageTerms]; omega]
          rw [List.getElem?_eq_getElem (by have := hp64 res hres; rw [hksz, hplen res hres] at hi; omega)]
          exact congrArg some hrank
        · intro hr
          have hrl : r < keys.length := by
            rcases (List.getElem?_eq_some_iff.mp hr) with ⟨h1, _⟩; exact h1
          have hr' : keys[r] = bytesToList k := by
            rcases (List.getElem?_eq_some_iff.mp hr) with ⟨_, h2⟩; exact h2
          have := sorted_inj keys hsorted r (64 * res + i) hrl _ (by rw [hr', hrank])
          simp only [Option.some.injEq]
          rw [this]; simp [pageTerms]; omega
      | none =>
        have hnone := indexInPage_none ks k hidx
        refine ⟨none, pr + 1, rfl, ?_⟩
        intro r
        simp only [reduceCtorEq, false_iff]
        intro hr
        have hrl : r < keys.length := by
          rcases (List.getElem?_eq_some_iff.mp hr) with ⟨h1, _⟩; exact h1
        have hr' : keys[r] = bytesToList k := by
          rcases (List.getElem?_eq_some_iff.mp hr) with ⟨_, h2⟩; exact h2
        -- the page of rank r is the page the search returns
        have hpr : r / 64 < ps.length := by rw [hlen]; omega
        have hres_eq : res = r / 64 := by
          rcases Nat.lt_trichotomy res (r / 64) with hlt | heq | hgt
          · rcases hQ with hQ | hQ
            · omega
            · exfalso
              rw [hFK (res + 1) (by omega)] at hQ
              have := sorted_le keys hsorted (64 * (res + 1)) r (hp64 _ (by omega)) hrl (by omega)
              rw [hr'] at this
              exact this hQ
          · exact heq
          · rcases hP with hP | hP
            · omega
            · exfalso
              rw [hFK res hres] at hP
              apply hP
              have := strictlySorted_lt keys hsorted r (64 * res) hrl (hp64 res hres) (by omega)
              rw [hr'] at this
              exact (cmpKey_swap _ _).mp this
        subst hres_eq
        have hi : r % 64 < ks.size := by
          rw [hksz, hplen _ hres]; have := hp64 _ hres; omega
        apply hnone (r % 64) hi
        rw [getElem!_pos ks _ hi]
        apply bytesToList_inj
        rw [hksel _ hi, hpel _ hres _ (by omega)]
        rw [← hr']
        congr 1
        omega
  · cases h

end L4Factoidal.Storage.Sbm11.Dict
