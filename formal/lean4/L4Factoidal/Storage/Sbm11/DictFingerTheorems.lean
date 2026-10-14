/-
L4Factoidal.Storage.Sbm11.DictFingerTheorems — the walk over keys in byte
order (`Dict.lookupNextM`) answers as `Dict.lookupM` does (stage 5, the replay
of the delta log, https://github.com/danbri/factoidal/issues/858).

* `DictOk`, `dictOk_of_encodeDict`: what the proofs use of the bytes of a
  dictionary (sorted keys, page `j` is the `j`-th chunk of 64 keys, the head of
  a page is its first key), and that the bytes `encodeDict?` writes meet it.
* `Bracket`, `rank_of_bracket`: page `p` is the page of `k` when its first key
  is not above `k` and the first key of the next page is above `k`. The scan of
  a page that meets this (`indexInPage`) answers the rank of `k` exactly when
  `k` is a key. This is the end of `lookupM_encodeDict`, for any page.
* `findPageM_spec`, `stepPageM_spec`, `pageNextM_spec`: each gives a page that
  meets `Bracket`, with its keys, and a finger that is valid (`FingerOk`) for the
  key. The binary search and the shortcuts of the walk end on the same page.
* `lookupNextM_dictOk`, `lookupNextM_eq_lookupM`: the answer of one step of the
  walk is the answer of `lookupM` over the bytes `encodeDict?` writes, for any
  key and any finger valid for it; the finger it gives is valid for every key
  that is not below the key. `FingerOk keys none k` holds for every `k`.
* `lookupWalkM_dictOk`, `lookupWalkM_eq_lookupM`, `walkM_encodeDict`:
  `lookupWalkM` uses the finger only for a key that is not below the key before
  it, so its answer is the answer of `lookupM` for any state `WalkOk` and any
  key, and a walk over any list of keys, in any order, from no state, answers the
  rank of every key (`Answers`).

The only hypothesis is the encoder's output. No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.DictLookupTheorems
import L4Factoidal.Storage.Sbm11.DictFinger

namespace L4Factoidal.Storage.Sbm11.Dict

open L4Factoidal (two32 two64)

/-! ## What the proofs use of the bytes of a dictionary -/

/-- The three facts about a dictionary that the proofs below use: the keys
    are strictly sorted, page `j` reads as the `j`-th chunk of 64 keys, and
    the head of page `j` reads as its first key. -/
structure DictOk (keys : List Key) (fx fv : Nat → Nat → Id ByteArray) : Prop where
  sorted : strictlySorted keys = true
  pageOf : ∀ j (hj : j < (chunk pageTerms keys).length), ∃ ks,
    pageM (m := Id) fx fv j = pure ks ∧ ks.toList.map bytesToList = (chunk pageTerms keys)[j]
  firstOf : ∀ j, j < (chunk pageTerms keys).length → ∃ pb fk,
    pageBytesM (m := Id) fx fv j = pure pb ∧ firstKeyAt pb = some fk ∧
      bytesToList fk = keys.getD (64 * j) []

/-- The bytes `encodeDict?` writes meet them (the setup of
    `lookupM_encodeDict`). -/
theorem dictOk_of_encodeDict (keys : List Key) (v x : List UInt8) (h : encodeDict? keys = some (v, x)) :
    DictOk keys (fetchOf ⟨x.toArray⟩) (fetchOf ⟨v.toArray⟩) := by
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
    refine ⟨hsorted, fun j hj => ?_, fun j hj => ?_⟩
    · subst hps
      obtain ⟨ks, hks, hksl⟩ := pageM_dict _ keys.length hef hpf j hj
      exact ⟨ks, hks, hksl⟩
    · subst hps
      obtain ⟨pb, hpb, hl⟩ := pageBytesM_dict (chunk pageTerms keys) keys.length hef j hj
      have h0 : 0 < (chunk pageTerms keys)[j].length := by rw [hplen j hj]; have := hp64 j hj; omega
      obtain ⟨a, t, hat⟩ : ∃ a t, (chunk pageTerms keys)[j] = a :: t :=
        List.exists_cons_of_ne_nil (List.ne_nil_of_length_pos h0)
      have ha : a = keys[64 * j]'(hp64 j hj) := by
        have := hpel j hj 0 h0
        simp only [hat, List.getElem_cons_zero] at this
        simpa using this
      have hpf' := List.all_eq_true.mp hpf (chunk pageTerms keys)[j] (List.getElem_mem hj)
      rw [hat] at hl hpf'
      obtain ⟨fk, hfk, hfkl⟩ := firstKeyAt_page pb _ _ hl hpf'
      refine ⟨pb, fk, hpb, hfk, ?_⟩
      rw [hfkl, ha]
      simp [List.getD_eq_getElem?_getD, hp64 j hj]
  · cases h

/-! ## The pages of a key list -/

/-- The first key of page `p` (the head of the key list from `64 * p`). -/
def FKey (keys : List Key) (p : Nat) : Key := keys.getD (64 * p) []

theorem page_eq (keys : List Key) {p : Nat} (hp : p < (chunk pageTerms keys).length) :
    (chunk pageTerms keys)[p] = (keys.drop (64 * p)).take 64 :=
  chunk_getElem pageTerms (by decide) p keys hp

theorem page_start_lt (keys : List Key) {p : Nat} (hp : p < (chunk pageTerms keys).length) :
    64 * p < keys.length := by
  have := chunk64_length keys.length keys rfl
  omega

theorem page_len (keys : List Key) {p : Nat} (hp : p < (chunk pageTerms keys).length) :
    (chunk pageTerms keys)[p].length = min 64 (keys.length - 64 * p) := by
  rw [page_eq keys hp]; simp

theorem page_len_pos (keys : List Key) {p : Nat} (hp : p < (chunk pageTerms keys).length) :
    0 < (chunk pageTerms keys)[p].length := by
  rw [page_len keys hp]; have := page_start_lt keys hp; omega

theorem page_len_le (keys : List Key) {p : Nat} (hp : p < (chunk pageTerms keys).length) :
    (chunk pageTerms keys)[p].length ≤ 64 := by
  rw [page_len keys hp]; omega

/-- A page that is not the last holds 64 keys. -/
theorem page_len_full (keys : List Key) {p : Nat} (hp : p + 1 < (chunk pageTerms keys).length) :
    (chunk pageTerms keys)[p].length = 64 := by
  have hp' : p < (chunk pageTerms keys).length := by omega
  have h1 := page_start_lt keys hp
  rw [page_len keys hp']
  omega

theorem page_get (keys : List Key) {p : Nat} (hp : p < (chunk pageTerms keys).length) {j : Nat}
    (hj : j < (chunk pageTerms keys)[p].length) :
    (chunk pageTerms keys)[p][j] = keys[64 * p + j]'(by
      have := page_len keys hp; have := page_start_lt keys hp; omega) := by
  simp only [page_eq keys hp, List.getElem_take, List.getElem_drop]

theorem fkey_eq (keys : List Key) {p : Nat} (hp : p < (chunk pageTerms keys).length) :
    FKey keys p = keys[64 * p]'(page_start_lt keys hp) := by
  simp [FKey, List.getD_eq_getElem?_getD, page_start_lt keys hp]

/-- The first key of a page is the head of its keys. -/
theorem page_head (keys : List Key) {p : Nat} (hp : p < (chunk pageTerms keys).length) :
    (chunk pageTerms keys)[p][0]'(page_len_pos keys hp) = FKey keys p := by
  rw [page_get keys hp, fkey_eq keys hp]
  simp

/-- The order of two keys of a sorted list, by position. -/
theorem sorted_le' (keys : List Key) (hs : strictlySorted keys = true) {a b : Nat}
    (ha : a < keys.length) (hb : b < keys.length) (hab : a ≤ b) :
    cmpKey keys[a] keys[b] ≠ .gt := sorted_le keys hs a b ha hb hab

/-- Every key of page `p` is below the first key of page `p + 1`. -/
theorem page_lt_next (keys : List Key) (hs : strictlySorted keys = true) {p : Nat}
    (hp : p + 1 < (chunk pageTerms keys).length) {j : Nat} (hj : j < (chunk pageTerms keys)[p].length) :
    cmpKey ((chunk pageTerms keys)[p][j]) (FKey keys (p + 1)) = .lt := by
  have hp' : p < (chunk pageTerms keys).length := by omega
  have hfull := page_len_full keys hp
  rw [page_get keys hp' hj, fkey_eq keys hp]
  exact strictlySorted_lt keys hs _ _ _ _ (by omega)

theorem cmpKey_le_lt (a b c : Key) (hab : cmpKey a b ≠ .gt) (hbc : cmpKey b c = .lt) : cmpKey a c = .lt := by
  cases h : cmpKey a b with
  | lt => exact cmpKey_lt_trans _ _ _ h hbc
  | eq => rw [(cmpKey_eq_iff _ _).mp h]; exact hbc
  | gt => exact absurd h hab

theorem cmpKey_lt_le (a b c : Key) (hab : cmpKey a b = .lt) (hbc : cmpKey b c ≠ .gt) : cmpKey a c = .lt := by
  cases h : cmpKey b c with
  | lt => exact cmpKey_lt_trans _ _ _ hab h
  | eq => rw [← (cmpKey_eq_iff _ _).mp h]; exact hab
  | gt => exact absurd h hbc

/-! ## The page of a key and the scan of it -/

/-- Page `p` is the page of `k`: its first key is not above `k` (page 0 has
    no condition) and the first key of the next page is above `k` (the last
    page has no next page). -/
def Bracket (keys : List Key) (k : Key) (p : Nat) : Prop :=
  (p = 0 ∨ cmpKey (FKey keys p) k ≠ .gt) ∧
  (p + 1 = (chunk pageTerms keys).length ∨ cmpKey (FKey keys (p + 1)) k = .gt)

/-- The scan of the page of `k` finds the rank of `k` exactly when `k` is a
    key (the end of `lookupM_encodeDict`, for any page that `Bracket` names). -/
theorem rank_of_bracket (keys : List Key) (hs : strictlySorted keys = true) {res : Nat}
    (hres : res < (chunk pageTerms keys).length) (ks : Array ByteArray) (k : ByteArray)
    (hks : ks.toList.map bytesToList = (chunk pageTerms keys)[res])
    (hb : Bracket keys (bytesToList k) res) (r : Nat) :
    (match indexInPage ks k with | some i => some (res * pageTerms + i) | none => none) = some r ↔
      keys[r]? = some (bytesToList k) := by
  have hksz : ks.size = (chunk pageTerms keys)[res].length := by
    have := congrArg List.length hks; simpa using this
  have hksel : ∀ i (hi : i < ks.size), bytesToList ks[i] = (chunk pageTerms keys)[res][i]'(by omega) := by
    intro i hi
    have := congrArg (fun l => l[i]?) hks
    simp only [List.getElem?_map, Array.getElem?_toList] at this
    rw [Array.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega)] at this
    simpa using this
  have hlenres := page_len keys hres
  have hstart := page_start_lt keys hres
  cases hidx : indexInPage ks k with
  | some i =>
    obtain ⟨hi, hik⟩ := indexInPage_some ks k i hidx
    rw [getElem!_pos ks i hi] at hik
    have hbound : 64 * res + i < keys.length := by omega
    have hrank : keys[64 * res + i] = bytesToList k := by
      rw [← hik, hksel i hi, page_get keys hres (by omega)]
    simp only [Option.some.injEq]
    constructor
    · intro hr
      subst hr
      rw [show res * pageTerms + i = 64 * res + i by simp [pageTerms]; omega]
      rw [List.getElem?_eq_getElem hbound]
      exact congrArg some hrank
    · intro hr
      have hrl : r < keys.length := by
        rcases (List.getElem?_eq_some_iff.mp hr) with ⟨h1, _⟩; exact h1
      have hr' : keys[r] = bytesToList k := by
        rcases (List.getElem?_eq_some_iff.mp hr) with ⟨_, h2⟩; exact h2
      have := sorted_inj keys hs r (64 * res + i) hrl hbound (by rw [hr', hrank])
      rw [this]; simp [pageTerms]; omega
  | none =>
    have hnone := indexInPage_none ks k hidx
    simp only [reduceCtorEq, false_iff]
    intro hr
    have hrl : r < keys.length := by
      rcases (List.getElem?_eq_some_iff.mp hr) with ⟨h1, _⟩; exact h1
    have hr' : keys[r] = bytesToList k := by
      rcases (List.getElem?_eq_some_iff.mp hr) with ⟨_, h2⟩; exact h2
    have hpc := chunk64_length keys.length keys rfl
    have hpr : r / 64 < (chunk pageTerms keys).length := by omega
    have hres_eq : res = r / 64 := by
      rcases Nat.lt_trichotomy res (r / 64) with hlt | heq | hgt
      · rcases hb.2 with hQ | hQ
        · omega
        · exfalso
          have hnext : res + 1 < (chunk pageTerms keys).length := by omega
          rw [fkey_eq keys hnext] at hQ
          have := sorted_le keys hs (64 * (res + 1)) r (page_start_lt keys hnext) hrl (by omega)
          rw [hr'] at this
          exact this hQ
      · exact heq
      · rcases hb.1 with hP | hP
        · omega
        · exfalso
          rw [fkey_eq keys hres] at hP
          apply hP
          have := strictlySorted_lt keys hs r (64 * res) hrl hstart (by omega)
          rw [hr'] at this
          exact (cmpKey_swap _ _).mp this
    subst hres_eq
    have hi : r % 64 < ks.size := by omega
    apply hnone (r % 64) hi
    rw [getElem!_pos ks _ hi]
    apply bytesToList_inj
    rw [hksel _ hi, page_get keys hres (by omega)]
    rw [← hr']
    congr 1
    omega

/-! ## `findPageM` -/

theorem log2_fuel (n : Nat) : n ≤ 2 ^ (Nat.log2 n + 2) := by
  have := @Nat.lt_log2_self n
  have h2 : 2 ^ (Nat.log2 n + 1) ≤ 2 ^ (Nat.log2 n + 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

/-- The binary search over the pages from `lo` on gives the page of `k`, with
    its keys and nothing read ahead. -/
theorem findPageM_spec {keys : List Key} {fx fv : Nat → Nat → Id ByteArray} (hd : DictOk keys fx fv)
    (lo : Nat) (hlo : lo < (chunk pageTerms keys).length) (k : ByteArray)
    (hk : lo = 0 ∨ cmpKey (FKey keys lo) (bytesToList k) ≠ .gt) :
    ∃ f : Finger, findPageM (m := Id) fx fv ⟨keys.length, (chunk pageTerms keys).length⟩ lo k = pure f ∧
      lo ≤ f.page ∧ ∃ hp : f.page < (chunk pageTerms keys).length,
        f.keys.toList.map bytesToList = (chunk pageTerms keys)[f.page] ∧ f.ahead = none ∧
        Bracket keys (bytesToList k) f.page := by
  obtain ⟨res, pr, hs, h1, h2, hP, hQ⟩ := searchPagesM_spec fx fv k (chunk pageTerms keys).length (FKey keys)
    hd.firstOf (Nat.log2 ((chunk pageTerms keys).length - lo) + 2) lo (chunk pageTerms keys).length 0 hlo
    (Nat.le_refl _) (log2_fuel _) hk (Or.inl rfl)
  have e : findPageM (m := Id) fx fv ⟨keys.length, (chunk pageTerms keys).length⟩ lo k =
      (do
        let (res, _) ← searchPagesM (m := Id) fx fv k
          (Nat.log2 ((chunk pageTerms keys).length - lo) + 2) lo (chunk pageTerms keys).length 0
        let ks ← pageM (m := Id) fx fv res
        pure { page := res, keys := ks }) := rfl
  obtain ⟨ks, hks, hksl⟩ := hd.pageOf res h2
  rw [e, hs, pure_bind]
  simp only
  rw [hks, pure_bind]
  exact ⟨_, rfl, h1, h2, hksl, rfl, hP, hQ⟩

/-! ## The finger -/

/-- A finger is valid for `k` when it names a page with its keys, its first
    key is not above `k`, and the keys it holds ahead are those of the next
    page. -/
def FingerOk (keys : List Key) (fg : Option Finger) (k : Key) : Prop :=
  match fg with
  | none => True
  | some f => ∃ _ : f.page < (chunk pageTerms keys).length,
      f.keys.toList.map bytesToList = (chunk pageTerms keys)[f.page] ∧
      (f.page = 0 ∨ cmpKey (FKey keys f.page) k ≠ .gt) ∧
      (∀ a, f.ahead = some a → ∃ _ : f.page + 1 < (chunk pageTerms keys).length,
        a.toList.map bytesToList = (chunk pageTerms keys)[f.page + 1])

theorem back?_of_page (ks : Array ByteArray) (L : List Key) (hks : ks.toList.map bytesToList = L)
    (hne : 0 < L.length) :
    ∃ last, ks.back? = some last ∧ ∃ h : L.length - 1 < L.length, bytesToList last = L[L.length - 1] := by
  have hsz : ks.size = L.length := by have := congrArg List.length hks; simpa using this
  have hi : ks.size - 1 < ks.size := by omega
  refine ⟨ks[ks.size - 1], ?_, by omega, ?_⟩
  · simp [Array.back?, Array.getElem?_eq_getElem hi]
  · have := congrArg (fun l => l[ks.size - 1]?) hks
    simp only [List.getElem?_map, Array.getElem?_toList] at this
    rw [Array.getElem?_eq_getElem hi, List.getElem?_eq_getElem (by omega)] at this
    simp only [Option.map_some, Option.some.injEq] at this
    rw [this]
    congr 1
    omega

theorem head?_of_page (ks : Array ByteArray) (L : List Key) (hks : ks.toList.map bytesToList = L)
    (hne : 0 < L.length) :
    ∃ first, ks[0]? = some first ∧ ∃ h : 0 < L.length, bytesToList first = L[0] := by
  have hsz : ks.size = L.length := by have := congrArg List.length hks; simpa using this
  have hi : 0 < ks.size := by omega
  refine ⟨ks[0], ?_, hne, ?_⟩
  · simp [Array.getElem?_eq_getElem hi]
  · have := congrArg (fun l => l[0]?) hks
    simp only [List.getElem?_map, Array.getElem?_toList] at this
    rw [Array.getElem?_eq_getElem hi, List.getElem?_eq_getElem hne] at this
    simpa using this

/-! ## The step to the next page -/

/-- When `k` is not above the last key of page `p`, the first key of page
    `p + 1` is above `k` (or there is no page `p + 1`): the keys of a page lie
    below the first key of the page after it. -/
theorem bracket_next_of_le_last {keys : List Key} (hs : strictlySorted keys = true) {p : Nat}
    (hp : p < (chunk pageTerms keys).length) (k : Key)
    (hle : cmpKey k ((chunk pageTerms keys)[p][(chunk pageTerms keys)[p].length - 1]'(by
      have := page_len_pos keys hp; omega)) ≠ .gt) :
    p + 1 = (chunk pageTerms keys).length ∨ cmpKey (FKey keys (p + 1)) k = .gt := by
  by_cases hn : p + 1 < (chunk pageTerms keys).length
  · right
    have h1 := page_lt_next keys hs hn (j := (chunk pageTerms keys)[p].length - 1)
      (by have := page_len_pos keys hp; omega)
    exact (cmpKey_swap _ _).mp (cmpKey_le_lt _ _ _ hle h1)
  · left; omega

theorem stepPageM_spec {keys : List Key} {fx fv : Nat → Nat → Id ByteArray} (hd : DictOk keys fx fv)
    (f : Finger) (k : ByteArray)
    (hp : f.page < (chunk pageTerms keys).length)
    (hcont : f.keys.toList.map bytesToList = (chunk pageTerms keys)[f.page])
    (hP1 : f.page = 0 ∨ cmpKey (FKey keys f.page) (bytesToList k) ≠ .gt)
    (hahead : ∀ a, f.ahead = some a → ∃ _ : f.page + 1 < (chunk pageTerms keys).length,
      a.toList.map bytesToList = (chunk pageTerms keys)[f.page + 1])
    (hnext : f.page + 1 < (chunk pageTerms keys).length) :
    ∃ f' : Finger, stepPageM (m := Id) fx fv ⟨keys.length, (chunk pageTerms keys).length⟩ f k = pure f' ∧
      FingerOk keys (some f') (bytesToList k) ∧ Bracket keys (bytesToList k) f'.page := by
  obtain ⟨ks1, hks1c, hks1⟩ : ∃ ks1, nextPageM (m := Id) fx fv f = pure ks1 ∧
      ks1.toList.map bytesToList = (chunk pageTerms keys)[f.page + 1] := by
    cases hfa : f.ahead with
    | some a =>
      obtain ⟨_, ha⟩ := hahead a hfa
      exact ⟨a, by simp [nextPageM, hfa], ha⟩
    | none =>
      obtain ⟨ks, hk, hksl⟩ := hd.pageOf (f.page + 1) hnext
      exact ⟨ks, by simp [nextPageM, hfa, hk], hksl⟩
  obtain ⟨first1, hf1, _, hf1l⟩ := head?_of_page ks1 _ hks1 (page_len_pos keys hnext)
  obtain ⟨last1, hl1, hlt, hl1l⟩ := back?_of_page ks1 _ hks1 (page_len_pos keys hnext)
  have hfirst1 : bytesToList first1 = FKey keys (f.page + 1) := by rw [hf1l]; exact page_head keys hnext
  unfold stepPageM
  rw [hks1c, pure_bind]
  simp only [hf1, hl1, cmpBytesAt_eq, hfirst1]
  by_cases hg : cmpKey (FKey keys (f.page + 1)) (bytesToList k) = .gt
  · rw [hg]
    simp only [beq_self_eq_true, if_true]
    refine ⟨_, rfl, ⟨hp, hcont, hP1, fun a ha => ?_⟩, hP1, Or.inr hg⟩
    simp only [Option.some.injEq] at ha
    subst ha
    exact ⟨hnext, hks1⟩
  · have hne : cmpKey (FKey keys (f.page + 1)) (bytesToList k) ≠ .gt := hg
    have hb : (cmpKey (FKey keys (f.page + 1)) (bytesToList k) == Ordering.gt) = false := by
      cases h : cmpKey (FKey keys (f.page + 1)) (bytesToList k) <;> simp_all
    rw [hb]
    simp only [Bool.false_eq_true, if_false]
    by_cases hg2 : cmpKey (bytesToList k) (bytesToList last1) = .gt
    · have hb2 : (cmpKey (bytesToList k) (bytesToList last1) != Ordering.gt) = false := by
        rw [hg2]; rfl
      rw [hb2]
      simp only [Bool.false_eq_true, if_false]
      obtain ⟨f', hf', _, hp', hcont', hahead', hbr⟩ := findPageM_spec hd (f.page + 1) hnext k (Or.inr hne)
      refine ⟨f', hf', ⟨hp', hcont', hbr.1, fun a ha => ?_⟩, hbr⟩
      rw [hahead'] at ha; cases ha
    · have hne2 : cmpKey (bytesToList k) (bytesToList last1) ≠ .gt := hg2
      have hb2 : (cmpKey (bytesToList k) (bytesToList last1) != Ordering.gt) = true := by
        cases h : cmpKey (bytesToList k) (bytesToList last1) <;> simp_all
      rw [hb2]
      simp only [if_true]
      refine ⟨_, rfl, ⟨hnext, hks1, Or.inr hne, fun a ha => ?_⟩, Or.inr hne, ?_⟩
      · simp at ha
      · apply bracket_next_of_le_last hd.sorted hnext
        rw [hl1l] at hne2
        exact hne2

/-! ## The page of a key from a finger -/

/-- `pageNextM` gives the page of `k` with its keys, from a finger that is
    valid for `k`. -/
theorem pageNextM_spec {keys : List Key} {fx fv : Nat → Nat → Id ByteArray} (hd : DictOk keys fx fv)
    (hpc : 0 < (chunk pageTerms keys).length) (fg : Option Finger) (k : ByteArray)
    (hfg : FingerOk keys fg (bytesToList k)) :
    ∃ f : Finger, pageNextM (m := Id) fx fv ⟨keys.length, (chunk pageTerms keys).length⟩ fg k = pure f ∧
      FingerOk keys (some f) (bytesToList k) ∧ Bracket keys (bytesToList k) f.page := by
  cases fg with
  | none =>
    obtain ⟨f, hf, _, hp, hcont, hahead, hb⟩ := findPageM_spec hd 0 hpc k (Or.inl rfl)
    refine ⟨f, hf, ⟨hp, hcont, hb.1, fun a ha => ?_⟩, hb⟩
    rw [hahead] at ha; cases ha
  | some f =>
    obtain ⟨hp, hcont, hP1, hahead⟩ := hfg
    obtain ⟨last, hback, hlt, hlast⟩ := back?_of_page f.keys _ hcont (page_len_pos keys hp)
    unfold pageNextM
    simp only [hback, cmpBytesAt_eq]
    by_cases hc : cmpKey (bytesToList k) (bytesToList last) = .gt
    · have hb1 : (cmpKey (bytesToList k) (bytesToList last) != Ordering.gt) = false := by rw [hc]; rfl
      rw [hb1]
      simp only [Bool.false_eq_true, if_false]
      by_cases hn : f.page + 1 ≥ (chunk pageTerms keys).length
      · rw [if_pos hn]
        exact ⟨f, rfl, ⟨hp, hcont, hP1, hahead⟩, hP1, Or.inl (by omega)⟩
      · rw [if_neg hn]
        exact stepPageM_spec hd f k hp hcont hP1 hahead (by omega)
    · have hne : cmpKey (bytesToList k) (bytesToList last) ≠ .gt := hc
      have hb1 : (cmpKey (bytesToList k) (bytesToList last) != Ordering.gt) = true := by
        cases h : cmpKey (bytesToList k) (bytesToList last) <;> simp_all
      rw [hb1]
      simp only [if_true]
      refine ⟨f, rfl, ⟨hp, hcont, hP1, hahead⟩, hP1, ?_⟩
      apply bracket_next_of_le_last hd.sorted hp
      rw [hlast] at hne
      exact hne

/-! ## The lookup and the walk -/

theorem cmpKey_le_trans (a b c : Key) (hab : cmpKey a b ≠ .gt) (hbc : cmpKey b c ≠ .gt) : cmpKey a c ≠ .gt := by
  cases h1 : cmpKey a b with
  | lt =>
    cases h2 : cmpKey b c with
    | lt => rw [cmpKey_lt_trans _ _ _ h1 h2]; simp
    | eq => rw [(cmpKey_eq_iff _ _).mp h2] at h1; rw [h1]; simp
    | gt => exact absurd h2 hbc
  | eq =>
    rw [(cmpKey_eq_iff _ _).mp h1]; exact hbc
  | gt => exact absurd h1 hab

/-- A finger valid for `k` is valid for every key that is not below `k`. -/
theorem FingerOk.mono {keys : List Key} {fg : Option Finger} {k k' : Key}
    (hfg : FingerOk keys fg k) (hkk : cmpKey k k' ≠ .gt) : FingerOk keys fg k' := by
  cases fg with
  | none => trivial
  | some f =>
    obtain ⟨hp, hcont, hP1, hahead⟩ := hfg
    refine ⟨hp, hcont, ?_, hahead⟩
    rcases hP1 with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (cmpKey_le_trans _ _ _ h1 hkk)

/-- One step of a walk, over any dictionary that meets `DictOk`: the answer is
    the rank of `k` (`res = some r ↔ keys[r]? = some k`), and the finger it
    gives is valid for every key that is not below `k`. -/
theorem lookupNextM_dictOk {keys : List Key} {fx fv : Nat → Nat → Id ByteArray} (hd : DictOk keys fx fv)
    (fg : Option Finger) (k : ByteArray) (hfg : FingerOk keys fg (bytesToList k)) :
    ∃ res fg', lookupNextM (m := Id) fx fv ⟨keys.length, (chunk pageTerms keys).length⟩ fg k = pure (res, fg') ∧
      (∀ r, res = some r ↔ keys[r]? = some (bytesToList k)) ∧
      (∀ k', cmpKey (bytesToList k) k' ≠ .gt → FingerOk keys fg' k') := by
  by_cases hpc0 : (chunk pageTerms keys).length = 0
  · have hk0 : keys = [] := by
      apply List.eq_nil_of_length_eq_zero
      have := chunk64_length keys.length keys rfl
      omega
    refine ⟨none, none, ?_, ?_, fun _ _ => trivial⟩
    · unfold lookupNextM
      rw [hpc0]; rfl
    · intro r; subst hk0; simp
  · obtain ⟨f, hf, hok, hbr⟩ := pageNextM_spec hd (by omega) fg k hfg
    obtain ⟨hp, hcont, hP1, hahead⟩ := hok
    have e : lookupNextM (m := Id) fx fv ⟨keys.length, (chunk pageTerms keys).length⟩ fg k =
        (do
          let f ← pageNextM (m := Id) fx fv ⟨keys.length, (chunk pageTerms keys).length⟩ fg k
          match indexInPage f.keys k with
          | some i => return (some (f.page * pageTerms + i), some f)
          | none => return (none, some f)) := by
      unfold lookupNextM
      rw [if_neg (by simpa using hpc0)]
      rfl
    have hrank := rank_of_bracket keys hd.sorted hp f.keys k hcont hbr
    rw [e, hf, pure_bind]
    cases hidx : indexInPage f.keys k with
    | some i =>
      refine ⟨some (f.page * pageTerms + i), some f, rfl, ?_, fun k' hk' => ?_⟩
      · intro r; rw [← hrank r, hidx]
      · exact FingerOk.mono ⟨hp, hcont, hP1, hahead⟩ hk'
    | none =>
      refine ⟨none, some f, rfl, ?_, fun k' hk' => ?_⟩
      · intro r; rw [← hrank r, hidx]
      · exact FingerOk.mono ⟨hp, hcont, hP1, hahead⟩ hk'

/-- `lookupNextM` over the bytes `encodeDict?` writes answers as `lookupM`
    does: the same rank, or `none`, for any key and any finger valid for it. -/
theorem lookupNextM_eq_lookupM (keys : List Key) (v x : List UInt8) (h : encodeDict? keys = some (v, x))
    (k : ByteArray) (fg : Option Finger) (hfg : FingerOk keys fg (bytesToList k)) :
    ∃ res fg' probes,
      lookupNextM (m := Id) (fetchOf ⟨x.toArray⟩) (fetchOf ⟨v.toArray⟩)
        ⟨keys.length, (chunk pageTerms keys).length⟩ fg k = pure (res, fg') ∧
      lookupM (m := Id) (fetchOf ⟨x.toArray⟩) (fetchOf ⟨v.toArray⟩)
        ⟨keys.length, (chunk pageTerms keys).length⟩ k = pure (res, probes) ∧
      (∀ k', cmpKey (bytesToList k) k' ≠ .gt → FingerOk keys fg' k') := by
  obtain ⟨_, res0, probes, hl, hchar0⟩ := lookupM_encodeDict keys v x h k
  obtain ⟨res, fg', hn, hchar, hfin⟩ := lookupNextM_dictOk (dictOk_of_encodeDict keys v x h) fg k hfg
  have hres : res = res0 := by
    cases res with
    | none =>
      cases res0 with
      | none => rfl
      | some r0 =>
        have h1 := (hchar0 r0).mp rfl
        have h2 := (hchar r0).mpr h1
        cases h2
    | some r =>
      have h1 := (hchar r).mp rfl
      exact ((hchar0 r).mpr h1).symm
  subst hres
  exact ⟨res, fg', probes, hn, hl, hfin⟩

/-- A walk state is valid when its finger is valid for the key it was found for. -/
def WalkOk (keys : List Key) : Walk → Prop
  | none => True
  | some (p, f) => FingerOk keys (some f) (bytesToList p)

/-- One step of a walk over keys in any order, over any dictionary that meets
    `DictOk`: the answer is the rank of `k`, and the state it leaves is valid.
    The only hypothesis on the state is `WalkOk`; no hypothesis on the order of
    the keys, because `lookupWalkM` uses the finger only for a key that is not
    below the key before it. -/
theorem lookupWalkM_dictOk {keys : List Key} {fx fv : Nat → Nat → Id ByteArray} (hd : DictOk keys fx fv)
    (w : Walk) (hw : WalkOk keys w) (k : ByteArray) :
    ∃ res w', lookupWalkM (m := Id) fx fv ⟨keys.length, (chunk pageTerms keys).length⟩ w k = pure (res, w') ∧
      (∀ r, res = some r ↔ keys[r]? = some (bytesToList k)) ∧ WalkOk keys w' := by
  have hfg : FingerOk keys (w.fingerFor k) (bytesToList k) := by
    cases w with
    | none => trivial
    | some pf =>
      obtain ⟨p, f⟩ := pf
      by_cases hle : (cmpBytesAt p k != Ordering.gt) = true
      · simp only [Walk.fingerFor, hle, if_true]
        rw [cmpBytesAt_eq] at hle
        have hle' : cmpKey (bytesToList p) (bytesToList k) ≠ .gt := by simpa using hle
        exact FingerOk.mono hw hle'
      · simp only [Walk.fingerFor, hle]; trivial
  obtain ⟨res, fg', hn, hchar, hfin⟩ := lookupNextM_dictOk hd _ k hfg
  refine ⟨res, fg'.map fun f => (k, f), ?_, hchar, ?_⟩
  · unfold lookupWalkM
    rw [hn, pure_bind]
  · cases fg' with
    | none => trivial
    | some f' =>
      exact hfin (bytesToList k) (by rw [(cmpKey_eq_iff _ _).mpr rfl]; simp)

/-- `lookupWalkM` over the bytes `encodeDict?` writes answers as `lookupM`
    does, for any key and any valid state. -/
theorem lookupWalkM_eq_lookupM (keys : List Key) (v x : List UInt8) (h : encodeDict? keys = some (v, x))
    (k : ByteArray) (w : Walk) (hw : WalkOk keys w) :
    ∃ res w' probes,
      lookupWalkM (m := Id) (fetchOf ⟨x.toArray⟩) (fetchOf ⟨v.toArray⟩)
        ⟨keys.length, (chunk pageTerms keys).length⟩ w k = pure (res, w') ∧
      lookupM (m := Id) (fetchOf ⟨x.toArray⟩) (fetchOf ⟨v.toArray⟩)
        ⟨keys.length, (chunk pageTerms keys).length⟩ k = pure (res, probes) ∧ WalkOk keys w' := by
  obtain ⟨_, res0, probes, hl, hchar0⟩ := lookupM_encodeDict keys v x h k
  obtain ⟨res, w', hn, hchar, hok⟩ := lookupWalkM_dictOk (dictOk_of_encodeDict keys v x h) w hw k
  have hres : res = res0 := by
    cases res with
    | none =>
      cases res0 with
      | none => rfl
      | some r0 =>
        have h1 := (hchar0 r0).mp rfl
        have h2 := (hchar r0).mpr h1
        cases h2
    | some r =>
      have h1 := (hchar r).mp rfl
      exact ((hchar0 r).mpr h1).symm
  subst hres
  exact ⟨res, w', probes, hn, hl, hok⟩

/-- The walk of `lookupWalkM` over a list of keys: the loop of
    `Harness/Sbm11Query.lean` (`prefillBaseIds`, a `for` loop in `IO`) written as a
    recursion, the specification of that loop. It is `noncomputable` on purpose: it
    is not run (the run time loop is the `for` loop, which takes no stack frame for
    each key), and a compiled recursion over the keys would take one. -/
noncomputable def walkM {m : Type → Type} [Monad m] (fetchGdx fetchGdv : Nat → Nat → m ByteArray) (h : GdxHeader) :
    Walk → List ByteArray → ExceptT String m (List (Option Nat))
  | _, [] => pure []
  | w, k :: ks => do
    let (r, w') ← lookupWalkM fetchGdx fetchGdv h w k
    let rs ← walkM fetchGdx fetchGdv h w' ks
    pure (r :: rs)

/-- The answers `rs` of a walk over `ks` are the ranks: for each key, `res =
    some r ↔ keys[r]? = some k`. -/
def Answers (keys : List Key) : List ByteArray → List (Option Nat) → Prop
  | [], [] => True
  | k :: ks, res :: rs => (∀ r, res = some r ↔ keys[r]? = some (bytesToList k)) ∧ Answers keys ks rs
  | _, _ => False

/-- A walk over any list of keys, from no finger (`WalkOk keys none` holds),
    answers at every key the rank of the key, as an independent `lookupM` does
    (`lookupM_encodeDict`). The keys need not be in byte order. -/
theorem walkM_encodeDict (keys : List Key) (v x : List UInt8) (h : encodeDict? keys = some (v, x)) :
    ∀ (ks : List ByteArray) (w : Walk), WalkOk keys w →
      ∃ rs, walkM (m := Id) (fetchOf ⟨x.toArray⟩) (fetchOf ⟨v.toArray⟩)
          ⟨keys.length, (chunk pageTerms keys).length⟩ w ks = pure rs ∧ Answers keys ks rs := by
  intro ks
  induction ks with
  | nil => intro w _; exact ⟨[], rfl, trivial⟩
  | cons k ks ih =>
    intro w hw
    obtain ⟨res, w', hn, hchar, hok⟩ := lookupWalkM_dictOk (dictOk_of_encodeDict keys v x h) w hw k
    obtain ⟨rs, hwalk, hall⟩ := ih w' hok
    refine ⟨res :: rs, ?_, hchar, hall⟩
    show (do
        let (r, w') ← lookupWalkM (m := Id) (fetchOf ⟨x.toArray⟩) (fetchOf ⟨v.toArray⟩)
          ⟨keys.length, (chunk pageTerms keys).length⟩ w k
        let rs ← walkM (m := Id) (fetchOf ⟨x.toArray⟩) (fetchOf ⟨v.toArray⟩)
          ⟨keys.length, (chunk pageTerms keys).length⟩ w' ks
        pure (r :: rs) : ExceptT String Id _) = _
    rw [hn, pure_bind]
    simp only
    rw [hwalk, pure_bind]

#print axioms L4Factoidal.Storage.Sbm11.Dict.dictOk_of_encodeDict
#print axioms L4Factoidal.Storage.Sbm11.Dict.rank_of_bracket
#print axioms L4Factoidal.Storage.Sbm11.Dict.findPageM_spec
#print axioms L4Factoidal.Storage.Sbm11.Dict.stepPageM_spec
#print axioms L4Factoidal.Storage.Sbm11.Dict.pageNextM_spec
#print axioms L4Factoidal.Storage.Sbm11.Dict.lookupNextM_dictOk
#print axioms L4Factoidal.Storage.Sbm11.Dict.lookupNextM_eq_lookupM
#print axioms L4Factoidal.Storage.Sbm11.Dict.lookupWalkM_dictOk
#print axioms L4Factoidal.Storage.Sbm11.Dict.lookupWalkM_eq_lookupM
#print axioms L4Factoidal.Storage.Sbm11.Dict.walkM_encodeDict
