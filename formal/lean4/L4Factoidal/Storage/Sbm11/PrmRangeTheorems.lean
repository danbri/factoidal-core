/-
L4Factoidal.Storage.Sbm11.PrmRangeTheorems — the PRM1 range search of issue
805 (`PrmRange.rangeM`) returns the entries of the blocks that `blocksFor`
selects (https://github.com/danbri/factoidal/issues/805; lemmas L4a′ and
L2d′ of `docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`).

* `searchM_pure`, `searchPure_bounds`, `searchPure_spec`: the binary search
  of `rangeM` over a monotone predicate, with fuel `f` and `h - l < 2^f`,
  returns the least index of `[l, h)` where the predicate holds, or `h`.
* `searchPure_firstBlockGo`: its first search is `IdQuery.firstBlockGo`.
* `blocksForGo_upto`: the block walk of `blocksFor` from `lo` stops at the
  first block whose first row is above the key prefix.
* **`rangeM_array` (L4a′).** Over the PRM1 entries of an admitted
  permutation (`prmAdmitted`, what activation checks) held in an array,
  `rangeM` answers `IdQuery.metasFor`: the entries of the blocks that
  `blocksFor` returns, in order. With `ScanTheorems.blocksFor_complete`
  (L4a), every block that can hold a row with the key prefix is in it.
* **`rangeM_bytes` (L2d′).** Over positioned reads of a PRM1 file `b` that
  `PrmAt.decodePrmAt` decodes to `(p, ms)` (`read off len` gives
  `b.extract off (off + len)`), `openM` gives the entry count and `rangeM`
  answers `metasFor ms`: the same entries as decoding the whole file and
  selecting. The hypothesis is what activation checks (`decodePrmAt_eq`:
  `decodePrmAt` is `decodePrm`, L2d); the conclusion is not among the
  hypotheses.
* `entryAt_extract`: an entry read from a slice of the file is the entry at
  the shifted position (what one positioned read returns).
* `scanFoldM_tuples_prm`: lemma L4e (`ScanFoldTheorems.scanFoldM_tuples`)
  for a store whose block metadata comes from `rangeM` and `openM` over
  positioned reads of a PRM1 file that decodes; the admission of its entries
  follows from the decoding.

What is not proved here: that the host's `pread` and the Merkle-verified
chunk reader return the file's bytes (the I/O boundary of
`Harness/Sbm11Query.lean`; `tests/sbm11/run.sh` part (e) compares the range
search on every PRM1 file with decoding the whole file, over sampled keys).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.PrmRange
import L4Factoidal.Storage.Sbm11.PrmAtTheorems
import L4Factoidal.Storage.Sbm11.ScanTheorems
import L4Factoidal.Storage.Sbm11.ScanFoldTheorems

namespace L4Factoidal.Storage.Sbm11.PrmRangeTheorems

open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Column
open L4Factoidal.Storage.Sbm11.IdQuery (prefixCmp blocksFor blocksForGo firstBlockGo metasFor)
open L4Factoidal.Storage.Sbm11.PrmRange
open L4Factoidal.Storage.Sbm11.ScanTheorems (chain_sorted prefixCmp_gt_of_le)

/-! ## The binary search -/

/-- The pure form of `searchM`. -/
def searchPure (q : Nat → Bool) : Nat → Nat → Nat → Nat
  | 0, l, _ => l
  | f + 1, l, h =>
    if l < h then
      if q ((l + h) / 2) then searchPure q f l ((l + h) / 2) else searchPure q f ((l + h) / 2 + 1) h
    else l

/-- `searchM` with probes that answer `q` below `n` is `searchPure q`. -/
theorem searchM_pure (probe : Nat → ExceptT String Id Bool) (q : Nat → Bool) (n : Nat)
    (hq : ∀ i, i < n → probe i = pure (q i)) :
    ∀ f l h, h ≤ n → searchM probe f l h = pure (searchPure q f l h) := by
  intro f
  induction f with
  | zero => intro l h _; rfl
  | succ f ih =>
    intro l h hh
    by_cases hlh : l < h
    · simp only [searchM, searchPure, if_pos hlh]
      rw [hq _ (by omega), pure_bind]
      cases hc : q ((l + h) / 2)
      · simp only [Bool.false_eq_true, if_false]; exact ih _ _ hh
      · simp only [if_true]; exact ih _ _ (by omega)
    · simp only [searchM, searchPure, if_neg hlh]

theorem searchPure_bounds (q : Nat → Bool) :
    ∀ f l h, l ≤ h → l ≤ searchPure q f l h ∧ searchPure q f l h ≤ h := by
  intro f
  induction f with
  | zero => intro l h hlh; exact ⟨Nat.le_refl _, hlh⟩
  | succ f ih =>
    intro l h hlh
    simp only [searchPure]
    split
    · split
      · have := ih l ((l + h) / 2) (by omega); omega
      · have := ih ((l + h) / 2 + 1) h (by omega); omega
    · omega

/-- The first search of `rangeM` is `IdQuery.firstBlockGo`. -/
theorem searchPure_firstBlockGo (ms : Array BlockMeta) (key : Array UInt64) :
    ∀ f l h, searchPure (fun i => prefixCmp ms[i]!.last key != .lt) f l h = firstBlockGo ms key f l h := by
  intro f
  induction f with
  | zero => intro l h; rfl
  | succ f ih =>
    intro l h
    simp only [searchPure, firstBlockGo]
    split
    · by_cases hc : prefixCmp ms[(l + h) / 2]!.last key = .lt
      · simp [hc, ih]
      · simp [hc, ih]
    · rfl

/-- **The search is exact.** For a predicate that is monotone below `n`
    (once true, true for every larger index below `n`), with `h - l < 2^f`,
    `searchPure` returns an index `r` of `[l, h]` such that the predicate is
    false on `[l, r)` and `r = h` or the predicate holds at `r`. -/
theorem searchPure_spec (q : Nat → Bool) (n : Nat)
    (hmono : ∀ i j, i ≤ j → j < n → q i = true → q j = true) :
    ∀ f l h, l ≤ h → h ≤ n → h - l < 2 ^ f →
      (∀ i, l ≤ i → i < searchPure q f l h → q i = false) ∧
      (searchPure q f l h = h ∨ q (searchPure q f l h) = true) := by
  intro f
  induction f with
  | zero =>
    intro l h hlh _ hs
    have hl : h = l := by simp at hs; omega
    subst hl
    exact ⟨fun i h1 h2 => by simp only [searchPure] at h2; omega, Or.inl rfl⟩
  | succ f ih =>
    intro l h hlh hn hs
    have hp : 2 ^ (f + 1) = 2 * 2 ^ f := by rw [Nat.pow_succ, Nat.mul_comm]
    by_cases hlt : l < h
    · cases hq : q ((l + h) / 2) with
      | true =>
        have e : searchPure q (f + 1) l h = searchPure q f l ((l + h) / 2) := by
          simp [searchPure, hlt, hq]
        rw [e]
        obtain ⟨h1, h2⟩ := ih l ((l + h) / 2) (by omega) (by omega) (by omega)
        refine ⟨h1, Or.inr ?_⟩
        rcases h2 with h2 | h2
        · rw [h2]; exact hq
        · exact h2
      | false =>
        have e : searchPure q (f + 1) l h = searchPure q f ((l + h) / 2 + 1) h := by
          simp [searchPure, hlt, hq]
        rw [e]
        obtain ⟨h1, h2⟩ := ih ((l + h) / 2 + 1) h (by omega) hn (by omega)
        refine ⟨fun i hi1 hi2 => ?_, h2⟩
        by_cases hi : i ≤ (l + h) / 2
        · cases hqi : q i
          · rfl
          · have := hmono i ((l + h) / 2) hi (by omega) hqi
            rw [hq] at this; cases this
        · exact h1 i (by omega) hi2
    · have hl : h = l := by omega
      subst hl
      refine ⟨fun i h1 h2 => ?_, Or.inl ?_⟩
      · simp only [searchPure, Nat.lt_irrefl, if_false] at h2; omega
      · simp only [searchPure, Nat.lt_irrefl, if_false]

/-! ## The block walk of `blocksFor` -/

/-- From `i`, the walk of `blocksFor` collects the blocks up to `hi`, the
    first block whose first row is above the key prefix (or the end). -/
theorem blocksForGo_upto (metas : Array BlockMeta) (key : Array UInt64) (hi : Nat)
    (hhi : hi ≤ metas.size)
    (hstop : hi = metas.size ∨ (prefixCmp metas[hi]!.first key == .gt) = true) :
    ∀ f i (out : Array Nat), i ≤ hi → hi - i ≤ f →
      (∀ j, i ≤ j → j < hi → (prefixCmp metas[j]!.first key == .gt) = false) →
      (blocksForGo metas key f i out).toList = out.toList ++ List.range' i (hi - i) := by
  intro f
  induction f with
  | zero =>
    intro i out hi1 hi2 _
    have : hi - i = 0 := by omega
    rw [this]; simp [blocksForGo]
  | succ f ih =>
    intro i out hi1 hi2 hj
    simp only [blocksForGo]
    by_cases hie : i = hi
    · subst hie
      rcases hstop with hs | hs
      · rw [if_pos (by omega)]; simp
      · by_cases hsz : i ≥ metas.size
        · rw [if_pos hsz]; simp
        · rw [if_neg hsz, if_pos hs]; simp
    · rw [if_neg (by omega)]
      have hg := hj i (Nat.le_refl _) (by omega)
      rw [if_neg (by rw [hg]; simp)]
      rw [ih (i + 1) (out.push i) (by omega) (by omega) (fun j h1 h2 => hj j (by omega) h2)]
      rw [Array.toList_push, List.append_assoc]
      congr 1
      rw [show hi - i = (hi - (i + 1)) + 1 by omega, List.range'_succ]
      simp

/-- The entries at positions `lo .. hi - 1`, by `getElem!`, are the slice. -/
theorem map_range'_extract (A : Array BlockMeta) (lo hi : Nat) (h : hi ≤ A.size) :
    ((List.range' lo (hi - lo)).map (fun i => A[i]!)).toArray = A.extract lo hi := by
  apply Array.ext
  · simp; omega
  · intro k h1 h2
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range', Nat.one_mul,
      Array.getElem_extract]
    have hk : lo + k < A.size := by simp at h1; omega
    simp [getElem!_pos A (lo + k) hk]

/-- The "first row above the key prefix" test is monotone over the blocks
    of an admitted PRM1. -/
theorem firstGt_mono (perm : Nat) (ms : List BlockMeta) (hadm : prmAdmitted perm ms = true)
    (key : Array UInt64) :
    ∀ i j, i ≤ j → j < ms.toArray.size →
      (prefixCmp ms.toArray[i]!.first key == .gt) = true →
      (prefixCmp ms.toArray[j]!.first key == .gt) = true := by
  intro i j hij hj hi
  have hch : chainGo prbHeaderBytes ms = true := by
    simp only [prmAdmitted, Bool.and_eq_true] at hadm
    exact hadm.1.1.2
  have hsz : ms.toArray.size = ms.length := List.size_toArray
  rw [hsz] at hj
  have h1 : ms.toArray[i]! = ms[i] := by simp [getElem!_pos, show i < ms.length by omega]
  have h2 : ms.toArray[j]! = ms[j] := by simp [getElem!_pos, hj]
  rw [h1] at hi; rw [h2]
  have hle := ((chain_sorted ms _ hch i j (by omega) hj).2 hij).1
  have hgt : prefixCmp ms[i].first key = .gt := by simpa using hi
  simp [prefixCmp_gt_of_le key hle hgt]

/-! ## L4a′: the range search over an array -/

/-- The first search of `rangeM` over an array `A`. -/
def loOf (A : Array BlockMeta) (key : Array UInt64) : Nat :=
  searchPure (fun i => prefixCmp A[i]!.last key != .lt) (Nat.log2 A.size + 2) 0 A.size

/-- The second search of `rangeM` over an array `A`. -/
def hiOf (A : Array BlockMeta) (key : Array UInt64) : Nat :=
  searchPure (fun i => prefixCmp A[i]!.first key == .gt) (Nat.log2 A.size + 2) (loOf A key) A.size

/-- `rangeM` over any reader whose entries and slices are those of `A`
    computes the two searches over `A` and answers the slice between them. -/
theorem rangeM_reader (r : Reader Id) (A : Array BlockMeta) (key : Array UInt64) (hc : r.count = A.size)
    (he : ∀ i, i < A.size → r.entry i = pure A[i]!)
    (hs : ∀ lo hi, lo < hi → hi ≤ A.size → r.slice lo hi = pure (A.extract lo hi)) :
    rangeM r key = if loOf A key < hiOf A key then pure (A.extract (loOf A key) (hiOf A key)) else pure #[] := by
  have hL : ∀ i, i < A.size → (fun i => (do return prefixCmp (← r.entry i).last key != Ordering.lt :
      ExceptT String Id Bool)) i = pure (prefixCmp A[i]!.last key != .lt) := by
    intro i hi
    show (do return prefixCmp (← r.entry i).last key != Ordering.lt : ExceptT String Id Bool) = _
    rw [he i hi, pure_bind]
  have hF : ∀ i, i < A.size → (fun i => (do return prefixCmp (← r.entry i).first key == Ordering.gt :
      ExceptT String Id Bool)) i = pure (prefixCmp A[i]!.first key == .gt) := by
    intro i hi
    show (do return prefixCmp (← r.entry i).first key == Ordering.gt : ExceptT String Id Bool) = _
    rw [he i hi, pure_bind]
  have hlo : searchM (fun i => (do return prefixCmp (← r.entry i).last key != Ordering.lt :
      ExceptT String Id Bool)) (Nat.log2 A.size + 2) 0 A.size = pure (loOf A key) :=
    searchM_pure _ _ A.size hL _ 0 A.size (Nat.le_refl _)
  have hhi : searchM (fun i => (do return prefixCmp (← r.entry i).first key == Ordering.gt :
      ExceptT String Id Bool)) (Nat.log2 A.size + 2) (loOf A key) A.size = pure (hiOf A key) :=
    searchM_pure _ _ A.size hF _ (loOf A key) A.size (Nat.le_refl _)
  have hlon : loOf A key ≤ A.size := (searchPure_bounds _ _ 0 A.size (Nat.zero_le _)).2
  have hb : loOf A key ≤ hiOf A key ∧ hiOf A key ≤ A.size := searchPure_bounds _ _ _ A.size hlon
  unfold rangeM
  rw [hc]
  dsimp only
  rw [hlo, pure_bind, hhi, pure_bind]
  by_cases hlt : loOf A key < hiOf A key
  · rw [if_pos hlt, if_pos hlt, hs _ _ hlt hb.2]
  · rw [if_neg hlt, if_neg hlt]

/-- Over the PRM1 entries of an admitted permutation, `metasFor` is the
    slice between the two searches of `rangeM`. -/
theorem metasFor_search (perm : Nat) (ms : List BlockMeta) (hadm : prmAdmitted perm ms = true)
    (key : Array UInt64) :
    metasFor ms.toArray key =
      if loOf ms.toArray key < hiOf ms.toArray key then
        ms.toArray.extract (loOf ms.toArray key) (hiOf ms.toArray key)
      else #[] := by
  let A := ms.toArray
  have hlon : loOf A key ≤ A.size := (searchPure_bounds _ _ 0 A.size (Nat.zero_le _)).2
  have hb : loOf A key ≤ hiOf A key ∧ hiOf A key ≤ A.size := searchPure_bounds _ _ _ A.size hlon
  have hfuel : A.size - loOf A key < 2 ^ (Nat.log2 A.size + 2) := by
    have h1 : A.size < 2 ^ (A.size.log2 + 1) := Nat.lt_log2_self
    have h2 : 2 ^ (A.size.log2 + 1) ≤ 2 ^ (Nat.log2 A.size + 2) := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  obtain ⟨hfalse, hstop⟩ := searchPure_spec (fun i => prefixCmp A[i]!.first key == .gt) A.size
    (firstGt_mono perm ms hadm key) (Nat.log2 A.size + 2) (loOf A key) A.size hlon (Nat.le_refl _) hfuel
  have hfirst : firstBlockGo A key (Nat.log2 A.size + 2) 0 A.size = loOf A key :=
    (searchPure_firstBlockGo A key _ 0 A.size).symm
  have hwalk := blocksForGo_upto A key (hiOf A key) hb.2 hstop A.size (loOf A key) #[] hb.1 (by omega)
    (fun j h1 h2 => hfalse j h1 h2)
  have hmf : metasFor A key = A.extract (loOf A key) (hiOf A key) := by
    unfold metasFor blocksFor
    rw [hfirst]
    rw [← map_range'_extract A (loOf A key) (hiOf A key) hb.2]
    apply Array.toList_inj.mp
    rw [Array.toList_map, hwalk]
    simp
  show metasFor A key = if loOf A key < hiOf A key then A.extract (loOf A key) (hiOf A key) else #[]
  by_cases hlt : loOf A key < hiOf A key
  · rw [if_pos hlt, hmf]
  · rw [if_neg hlt, hmf, Array.extract_empty_of_stop_le_start (by omega)]

/-- **L4a′.** Over the PRM1 entries of an admitted permutation, the range
    search answers `metasFor`: the entries of the blocks `blocksFor`
    returns. -/
theorem rangeM_array (perm : Nat) (ms : List BlockMeta) (hadm : prmAdmitted perm ms = true)
    (key : Array UInt64) :
    rangeM (m := Id) (arrayReader ms.toArray) key = pure (metasFor ms.toArray key) := by
  rw [rangeM_reader (arrayReader ms.toArray) ms.toArray key rfl (fun _ _ => rfl) (fun _ _ _ _ => rfl),
    metasFor_search perm ms hadm key]
  split <;> rfl

/-! ## Reads from a slice of the file -/

/-- The 8-byte little-endian field at `i` (as `get64At` reads it). -/
def rd64 (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat + b[i + 1]!.toNat * 256 + b[i + 2]!.toNat * 65536 +
    b[i + 3]!.toNat * 16777216 + b[i + 4]!.toNat * 4294967296 +
    b[i + 5]!.toNat * 1099511627776 + b[i + 6]!.toNat * 281474976710656 +
    b[i + 7]!.toNat * 72057594037927936

/-- The 4-byte little-endian field at `i` (as `get32At` reads it). -/
def rd32 (b : ByteArray) (i : Nat) : Nat :=
  b[i]!.toNat + b[i + 1]!.toNat * 256 + b[i + 2]!.toNat * 65536 + b[i + 3]!.toNat * 16777216

theorem get64At_rd (b : ByteArray) (i : Nat) (h : i + 8 ≤ b.size) : get64At b i = some (rd64 b i, i + 8) := by
  unfold get64At rd64
  rw [dif_pos h]
  simp [getElem!_pos, show i < b.size by omega, show i + 1 < b.size by omega, show i + 2 < b.size by omega,
    show i + 3 < b.size by omega, show i + 4 < b.size by omega, show i + 5 < b.size by omega,
    show i + 6 < b.size by omega, show i + 7 < b.size by omega]

theorem get32At_rd (b : ByteArray) (i : Nat) (h : i + 4 ≤ b.size) : get32At b i = some (rd32 b i, i + 4) := by
  unfold get32At rd32
  rw [dif_pos h]
  simp [getElem!_pos, show i < b.size by omega, show i + 1 < b.size by omega, show i + 2 < b.size by omega,
    show i + 3 < b.size by omega]

theorem getElem!_extract (b : ByteArray) (s e x : Nat) (h : s + x < e) (he : e ≤ b.size) :
    (b.extract s e)[x]! = b[s + x]! := by
  have hsz : x < (b.extract s e).size := by rw [ByteArray.size_extract]; omega
  rw [getElem!_pos (b.extract s e) x hsz, getElem!_pos b (s + x) (by omega), ByteArray.getElem_extract]

theorem rd64_extract (b : ByteArray) (s e j : Nat) (h : s + j + 8 ≤ e) (he : e ≤ b.size) :
    rd64 (b.extract s e) j = rd64 b (s + j) := by
  unfold rd64
  simp (disch := omega) only [getElem!_extract, Nat.add_assoc]

theorem rd32_extract (b : ByteArray) (s e j : Nat) (h : s + j + 4 ≤ e) (he : e ≤ b.size) :
    rd32 (b.extract s e) j = rd32 b (s + j) := by
  unfold rd32
  simp (disch := omega) only [getElem!_extract, Nat.add_assoc]

/-- The entry at `i`, field by field (the order of `PrmAt.entryAt`). -/
def entryRd (b : ByteArray) (i : Nat) : BlockMeta :=
  { first := ⟨rd64 b i, rd64 b (i + 8), rd64 b (i + 8 + 8), rd64 b (i + 8 + 8 + 8)⟩,
    last := ⟨rd64 b (i + 8 + 8 + 8 + 8), rd64 b (i + 8 + 8 + 8 + 8 + 8), rd64 b (i + 8 + 8 + 8 + 8 + 8 + 8),
      rd64 b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8)⟩,
    rows := rd32 b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8),
    offset := rd64 b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 4),
    len0 := rd32 b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 4 + 8),
    len1 := rd32 b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 4 + 8 + 4),
    len2 := rd32 b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 4 + 8 + 4 + 4),
    len3 := rd32 b (i + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 8 + 4 + 8 + 4 + 4 + 4) }

theorem entryAt_rd (b : ByteArray) (i : Nat) (h : i + 92 ≤ b.size) :
    PrmAt.entryAt b i = some (entryRd b i) := by
  unfold PrmAt.entryAt
  simp (disch := omega) only [get64At_rd, get32At_rd, Option.bind_eq_bind, Option.bind_some]
  rfl

/-- An entry read from a slice of the file is the entry at the shifted
    position. -/
theorem entryAt_extract (b : ByteArray) (s e j : Nat) (h : s + j + 92 ≤ e) (he : e ≤ b.size) :
    PrmAt.entryAt (b.extract s e) j = PrmAt.entryAt b (s + j) := by
  have hsz : (b.extract s e).size = e - s := by rw [ByteArray.size_extract]; omega
  rw [entryAt_rd (b.extract s e) j (by omega), entryAt_rd b (s + j) (by omega)]
  unfold entryRd
  simp (disch := omega) only [rd64_extract b s e, rd32_extract b s e, Nat.add_assoc]

/-! ## What a decoded PRM1 file holds -/

theorem entriesGo_some (b : ByteArray) (count : Nat) :
    ∀ f k (acc res : Array BlockMeta), count - k < f → k ≤ count →
      PrmAt.entriesGo b count f k acc = some res →
      res.size = acc.size + (count - k) ∧ (∀ i, i < acc.size → res[i]! = acc[i]!) ∧
      ∀ j, k ≤ j → j < count →
        PrmAt.entryAt b (prmHeaderBytes + prmEntryBytes * j) = some res[acc.size + (j - k)]! := by
  intro f
  induction f with
  | zero => intro k acc res hf; omega
  | succ f ih =>
    intro k acc res hf hk h
    simp only [PrmAt.entriesGo] at h
    by_cases hkc : k ≥ count
    · rw [if_pos hkc] at h
      cases h
      refine ⟨by omega, fun _ _ => rfl, fun j h1 h2 => by omega⟩
    · rw [if_neg hkc] at h
      cases he : PrmAt.entryAt b (prmHeaderBytes + prmEntryBytes * k) with
      | none => rw [he] at h; cases h
      | some e =>
        rw [he] at h
        obtain ⟨h1, h2, h3⟩ := ih (k + 1) (acc.push e) res (by omega) (by omega) h
        simp only [Array.size_push] at h1 h2 h3
        refine ⟨by omega, fun i hi => ?_, fun j hj1 hj2 => ?_⟩
        · rw [h2 i (by omega), getElem!_pos (acc.push e) i (by simp; omega), getElem!_pos acc i hi,
            Array.getElem_push_lt]
        · by_cases hjk : j = k
          · subst hjk
            rw [Nat.sub_self, Nat.add_zero, h2 acc.size (by omega),
              getElem!_pos (acc.push e) acc.size (by simp), Array.getElem_push_eq, he]
          · rw [h3 j (by omega) hj2]
            congr 2
            omega

/-- `get!` is `getElem!`. -/
theorem get!_eq (b : ByteArray) (i : Nat) (h : i < b.size) : b.get! i = b[i]! := by
  rw [getElem!_pos b i h]
  simp [ByteArray.get!, ByteArray.getElem_eq_getElem_data, getElem!_pos, h]

theorem get!_extract (b : ByteArray) (s e x : Nat) (h : s + x < e) (he : e ≤ b.size) :
    (b.extract s e).get! x = b.get! (s + x) := by
  have hsz : x < (b.extract s e).size := by rw [ByteArray.size_extract]; omega
  rw [get!_eq _ x hsz, get!_eq b (s + x) (by omega), getElem!_extract b s e x h he]

/-- What `decodePrmAt` checked, when it answers: the file length, every entry
    at its position, and the header. -/
theorem decodePrmAt_some (b : ByteArray) (p : Nat) (ms : Array BlockMeta)
    (h : PrmAt.decodePrmAt b = some (p, ms)) :
    b.size = prmHeaderBytes + prmEntryBytes * ms.size ∧
    (∀ i, i < ms.size → PrmAt.entryAt b (prmHeaderBytes + prmEntryBytes * i) = some ms[i]!) ∧
    ∃ total, headerOf (b.extract 0 prmHeaderBytes) = some (p, ms.size, total) := by
  have hs : ¬ b.size < prmHeaderBytes := by
    intro hs; simp [PrmAt.decodePrmAt, hs] at h
  have hs' : 22 ≤ b.size := by simp only [prmHeaderBytes] at hs; omega
  have hc1 := get64At_rd b 6 (by omega)
  have ht1 := get64At_rd b 14 (by omega)
  have hmag : (b.get! 0 == 80 && b.get! 1 == 82 && b.get! 2 == 77 && b.get! 3 == 49 && b.get! 4 == 1) = true := by
    cases hm : (b.get! 0 == 80 && b.get! 1 == 82 && b.get! 2 == 77 && b.get! 3 == 49 && b.get! 4 == 1) with
    | false => simp [PrmAt.decodePrmAt, hs, hm] at h
    | true => rfl
  have hsz : b.size = prmHeaderBytes + prmEntryBytes * rd64 b 6 := by
    apply Classical.byContradiction
    intro hne
    simp [PrmAt.decodePrmAt, hs, hmag, hc1, ht1, hne] at h
  -- `hsz` stays out of the simp sets below: with it, `simp` did not terminate
  -- (it ran out of memory at 13.8 GB)
  cases hent : PrmAt.entriesGo b (rd64 b 6) (rd64 b 6 + 1) 0 #[] with
  | none => simp [PrmAt.decodePrmAt, hs, hmag, hc1, ht1, hent] at h
  | some ms' =>
    have hpm : (b.get! 5).toNat = p ∧ ms' = ms := by
      simp [PrmAt.decodePrmAt, hs, hmag, hc1, ht1, hent] at h
      obtain ⟨_, _, hpp, hmm⟩ := h
      exact ⟨hpp, hmm⟩
    obtain ⟨hp, rfl⟩ := hpm
    obtain ⟨h1, _, h3⟩ := entriesGo_some b (rd64 b 6) (rd64 b 6 + 1) 0 #[] ms'
      (by omega) (by omega) hent
    have hcount : ms'.size = rd64 b 6 := by rw [h1]; simp
    refine ⟨by rw [hcount]; exact hsz, fun i hi => ?_, ?_⟩
    · have := h3 i (Nat.zero_le _) (by omega)
      simpa using this
    · refine ⟨rd64 b 14, ?_⟩
      have hx : (b.extract 0 prmHeaderBytes).size = 22 := by
        rw [ByteArray.size_extract]; simp only [prmHeaderBytes]; omega
      unfold headerOf
      have g0 := get!_extract b 0 prmHeaderBytes 0 (by decide) (by simp only [prmHeaderBytes]; omega)
      have g1 := get!_extract b 0 prmHeaderBytes 1 (by decide) (by simp only [prmHeaderBytes]; omega)
      have g2 := get!_extract b 0 prmHeaderBytes 2 (by decide) (by simp only [prmHeaderBytes]; omega)
      have g3 := get!_extract b 0 prmHeaderBytes 3 (by decide) (by simp only [prmHeaderBytes]; omega)
      have g4 := get!_extract b 0 prmHeaderBytes 4 (by decide) (by simp only [prmHeaderBytes]; omega)
      have g5 := get!_extract b 0 prmHeaderBytes 5 (by decide) (by simp only [prmHeaderBytes]; omega)
      have r6 : get64At (b.extract 0 prmHeaderBytes) 6 = some (rd64 b 6, 14) := by
        rw [get64At_rd _ 6 (by omega), rd64_extract b 0 prmHeaderBytes 6 (by decide)
          (by simp only [prmHeaderBytes]; omega)]
      have r14 : get64At (b.extract 0 prmHeaderBytes) 14 = some (rd64 b 14, 22) := by
        rw [get64At_rd _ 14 (by omega), rd64_extract b 0 prmHeaderBytes 14 (by decide)
          (by simp only [prmHeaderBytes]; omega)]
      simp only [Nat.zero_add] at g0 g1 g2 g3 g4 g5
      have hmin : prmHeaderBytes ≤ min prmHeaderBytes b.size := by simp only [prmHeaderBytes]; omega
      simp [hmin, g0, g1, g2, g3, g4, g5, hmag, r6, r14, hp, hcount]

/-- A positioned read of the bytes `b` (the I/O store reads the file so). -/
def readOf (b : ByteArray) (off len : Nat) : ExceptT String Id ByteArray := pure (b.extract off (off + len))

theorem entriesFromGo_eq (b : ByteArray) (n : Nat) (E : Nat → BlockMeta)
    (hE : ∀ k, k < n → PrmAt.entryAt b (prmEntryBytes * k) = some (E k)) :
    ∀ f k (acc : Array BlockMeta), n - k < f →
      entriesFromGo b n f k acc = some (acc ++ ((List.range' k (n - k)).map E).toArray) := by
  intro f
  induction f with
  | zero => intro k acc hf; omega
  | succ f ih =>
    intro k acc hf
    simp only [entriesFromGo]
    by_cases hk : k ≥ n
    · rw [if_pos hk, show n - k = 0 by omega]; simp
    · rw [if_neg hk, hE k (by omega)]
      simp only
      rw [ih (k + 1) (acc.push (E k)) (by omega)]
      congr 1
      rw [show n - k = (n - (k + 1)) + 1 by omega, List.range'_succ]
      simp

theorem map_range'_shift (A : Array BlockMeta) (lo c : Nat) (h : lo + c ≤ A.size) :
    ((List.range' 0 c).map (fun k => A[lo + k]!)).toArray = A.extract lo (lo + c) := by
  apply Array.ext
  · simp; omega
  · intro k h1 h2
    simp only [List.getElem_toArray, List.getElem_map, List.getElem_range', Nat.one_mul, Nat.zero_add,
      Array.getElem_extract]
    have hk : lo + k < A.size := by simp at h1; omega
    simp [getElem!_pos A (lo + k) hk]

/-- **L2d′, parts.** Over positioned reads of a PRM1 file that
    `decodePrmAt` decodes: the header gives the entry count. -/
theorem openM_bytes (b : ByteArray) (p : Nat) (ms : Array BlockMeta)
    (h : PrmAt.decodePrmAt b = some (p, ms)) : openM (readOf b) b.size p = pure ms.size := by
  obtain ⟨hsz, _, total, hh⟩ := decodePrmAt_some b p ms h
  have hr : readOf b 0 prmHeaderBytes = pure (b.extract 0 prmHeaderBytes) := by
    simp [readOf]
  unfold openM
  rw [hr, pure_bind, hh]
  simp [hsz]

/-- One entry read is the decoded entry. -/
theorem entryOfM_bytes (b : ByteArray) (p : Nat) (ms : Array BlockMeta)
    (h : PrmAt.decodePrmAt b = some (p, ms)) (i : Nat) (hi : i < ms.size) :
    entryOfM (readOf b) i = pure ms[i]! := by
  obtain ⟨hsz, hent, _⟩ := decodePrmAt_some b p ms h
  have hb : 92 * i + 92 ≤ 92 * ms.size := by omega
  have hx : PrmAt.entryAt (b.extract (prmHeaderBytes + prmEntryBytes * i)
      (prmHeaderBytes + prmEntryBytes * i + prmEntryBytes)) 0 = some ms[i]! := by
    rw [entryAt_extract b _ _ 0 (by simp only [prmEntryBytes]; omega)
      (by rw [hsz]; simp only [prmHeaderBytes, prmEntryBytes]; omega), Nat.add_zero, hent i hi]
  unfold entryOfM readOf
  rw [pure_bind, hx]

/-- One range read is the decoded entries of the range. -/
theorem sliceOfM_bytes (b : ByteArray) (p : Nat) (ms : Array BlockMeta)
    (h : PrmAt.decodePrmAt b = some (p, ms)) (lo hi : Nat) (hlh : lo ≤ hi) (hhi : hi ≤ ms.size) :
    sliceOfM (readOf b) lo hi = pure (ms.extract lo hi) := by
  obtain ⟨hsz, hent, _⟩ := decodePrmAt_some b p ms h
  have hE : ∀ k, k < hi - lo → PrmAt.entryAt (b.extract (prmHeaderBytes + prmEntryBytes * lo)
      (prmHeaderBytes + prmEntryBytes * lo + prmEntryBytes * (hi - lo))) (prmEntryBytes * k) =
      some ms[lo + k]! := by
    intro k hk
    have hk' : 92 * k + 92 ≤ 92 * (hi - lo) := by omega
    have hb : 92 * hi ≤ 92 * ms.size := Nat.mul_le_mul_left 92 hhi
    have hlo : 92 * lo + 92 * (hi - lo) = 92 * hi := by rw [← Nat.mul_add]; congr 1; omega
    rw [entryAt_extract b _ _ _ (by simp only [prmHeaderBytes, prmEntryBytes]; omega)
      (by rw [hsz]; simp only [prmHeaderBytes, prmEntryBytes]; omega)]
    rw [show prmHeaderBytes + prmEntryBytes * lo + prmEntryBytes * k =
      prmHeaderBytes + prmEntryBytes * (lo + k) by simp only [prmEntryBytes]; rw [Nat.mul_add, Nat.add_assoc]]
    exact hent (lo + k) (by omega)
  have hd : entriesFrom (b.extract (prmHeaderBytes + prmEntryBytes * lo)
      (prmHeaderBytes + prmEntryBytes * lo + prmEntryBytes * (hi - lo))) (hi - lo) = some (ms.extract lo hi) := by
    unfold entriesFrom
    rw [entriesFromGo_eq _ (hi - lo) (fun k => ms[lo + k]!) hE (hi - lo + 1) 0 _ (by omega)]
    rw [Nat.sub_zero, map_range'_shift ms lo (hi - lo) (by omega), show lo + (hi - lo) = hi by omega]
    simp
  unfold sliceOfM readOf
  rw [pure_bind, hd]

/-! ## L2d′: the range search over positioned reads of the file -/

/-- **L2d′.** Over positioned reads of a PRM1 file that `decodePrmAt`
    decodes to `(p, ms)`: `openM` gives the entry count, and `rangeM` over
    the entries it reads by binary search answers `metasFor ms`, the entries
    of the blocks `blocksFor` selects among all decoded entries. -/
theorem rangeM_bytes (b : ByteArray) (p : Nat) (ms : List BlockMeta)
    (h : PrmAt.decodePrmAt b = some (p, ms.toArray)) (key : Array UInt64) :
    (do let n ← openM (readOf b) b.size p; rangeM (bytesReader (readOf b) n) key) =
      (pure (metasFor ms.toArray key) : ExceptT String Id (Array BlockMeta)) := by
  rw [openM_bytes b p ms.toArray h, pure_bind]
  have hadm := (PrmAt.decodePrmAt_admitted b p ms.toArray h).1
  rw [List.toList_toArray] at hadm
  rw [rangeM_reader (bytesReader (readOf b) ms.toArray.size) ms.toArray key rfl
      (fun i hi => entryOfM_bytes b p ms.toArray h i hi)
      (fun lo hi hlt hhi => sliceOfM_bytes b p ms.toArray h lo hi (by omega) hhi),
    metasFor_search p ms hadm key]
  split <;> rfl

/-! ## The scan over the range reads (L4e with L2d′) -/

open L4Factoidal.Storage.Sbm11.IdQuery (Store ScanSpec scanFoldM)
open L4Factoidal.Storage.Sbm11.ScanFoldTheorems (SpecOk collectWith tuples keep proj blockRows scanFoldM_tuples)

/-- **L4e over the reads of issue 805.** A store whose `blocksForRange` and
    `blockCount` are `rangeM` and `openM` over positioned reads of a PRM1
    file `prm` that `decodePrmAt` decodes to `(spec.perm, ms)`, and whose PRB1
    reads come from `prb`, scans exactly the rows of the permutation that
    carry the key prefix and pass the checks, in row order, when there is no
    delta overlay and every block is admitted (`decodeBlockAt`). The
    admission of the PRM1 entries is not a hypothesis: it follows from the
    decoding (`PrmAt.decodePrmAt_admitted`). -/
theorem scanFoldM_tuples_prm (st : Store Id) (spec : ScanSpec) (hspec : SpecOk spec) (fill : Bool)
    (prm prb : ByteArray) (ms : List BlockMeta)
    (hdec : PrmAt.decodePrmAt prm = some (spec.perm, ms.toArray))
    (hrange : st.blocksForRange spec.perm spec.key =
      (do let n ← openM (readOf prm) prm.size spec.perm; rangeM (bytesReader (readOf prm) n) spec.key))
    (hcount : st.blockCount spec.perm = openM (readOf prm) prm.size spec.perm)
    (hprb : ∀ off len, st.prb spec.perm off len = pure (prb.extract off (off + len)))
    (hovl : (st.ovl spec.perm).isEmpty = true)
    (hblocks : ∀ b ∈ ms, ∃ cols, decodeBlockAt prb b b.offset = .ok cols) :
    ∃ stats, scanFoldM st spec fill [] (collectWith tuples) =
      pure (((ms.flatMap (blockRows prb)).filter (keep spec)).map (proj spec), stats) := by
  have hadm := (PrmAt.decodePrmAt_admitted prm spec.perm ms.toArray hdec).1
  rw [List.toList_toArray] at hadm
  have hr : st.blocksForRange spec.perm spec.key = pure (metasFor ms.toArray spec.key) := by
    rw [hrange, rangeM_bytes prm spec.perm ms hdec spec.key]
  have hc : st.blockCount spec.perm = pure ms.length := by
    rw [hcount, openM_bytes prm spec.perm ms.toArray hdec, List.size_toArray]
  exact scanFoldM_tuples st spec hspec fill prb ms hr hc hprb hovl hadm hblocks

#print axioms rangeM_array
#print axioms rangeM_bytes
#print axioms scanFoldM_tuples_prm

end L4Factoidal.Storage.Sbm11.PrmRangeTheorems
