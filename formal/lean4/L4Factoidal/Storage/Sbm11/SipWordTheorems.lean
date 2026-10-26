/-
L4Factoidal.Storage.Sbm11.SipWordTheorems — the delta loops on machine words
equal the `Nat` loops (https://github.com/danbri/factoidal/issues/930).

* `deltaFindGoY_eq`: `Sip.deltaFindGoY` (row number, bounds and candidate
  pointer as `USize`, zigzag step without a branch on the sign) equals
  `Sip.deltaFindGoC` from the same state, when the bytes, `lo`, `hi` and the
  candidates are fewer than `Sip.smallBytes`.
* `deltaGatherGoY_eq`: `Sip.deltaGatherGoY` (the same, and the varint read of
  `VarintWord` at the start of a varint) equals `Sip.deltaGatherGoK` from the
  same state. `K_row` is the unfolding of the byte loop over one varint;
  `gatherFast` joins it with `VarintWordTheorems.fastRead_spec`.
* `deltaFindStart_eq`, `deltaGatherStart_eq`: the starts that `findWords` and
  `gatherWords` call equal the `Nat` loops with the fuel those used before the
  word loops, so `SipTheorems.findWords_spec` and `gatherWords_spec` hold of
  the changed scan unchanged.

No `sorry`, no `native_decide`, no `partial`, no user `axiom`.
-/
import L4Factoidal.Storage.Sbm11.SipFastTheorems
import L4Factoidal.Storage.Sbm11.VarintWordTheorems

namespace L4Factoidal.Storage.Sbm11.Sip

open L4Factoidal (two64)
open L4Factoidal.Storage.Sbm11.FrameWords (put64)
open L4Factoidal.Storage.Sbm11.VarintWord
open L4Factoidal.Prim.Bytes (getOr0)

theorem toUSize_toNat' (n : Nat) (h : n < smallBytes) : n.toUSize.toNat = n := by
  simp only [Nat.toUSize, USize.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  have : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
  have : smallBytes = 2147483648 := rfl
  omega

theorem usize_size_toNat (a : Array UInt64) (h : a.size < smallBytes) : a.usize.toNat = a.size := by
  simp only [Array.usize, USize.toNat_ofNat', Nat.toUSize]
  exact toUSize_toNat' _ h

/-- Both zigzag forms agree (`VarintWord.zz_even`, `zz_odd`). -/
theorem zz_spec (prev z : UInt64) :
    zzV prev z = (if z % 2 == 0 then prev + z / 2 else prev - (z / 2 + 1)) ∧
    (zzOk prev z (zzV prev z) = true ↔
      (if z % 2 == 0 then prev ≤ prev + z / 2 else z / 2 + 1 ≤ prev)) := by
  by_cases he : z % 2 = 0
  · have he' : (z % 2 == 0) = true := by simpa using he
    obtain ⟨h1, h2⟩ := zz_even prev z he
    rw [he', if_pos rfl, if_pos rfl]
    refine ⟨h1, ?_⟩
    rw [h2]; simp
  · have he' : (z % 2 == 0) = false := by simpa using he
    obtain ⟨h1, h2⟩ := zz_odd prev z he
    rw [he']
    simp only [Bool.false_eq_true, if_false]
    refine ⟨h1, ?_⟩
    rw [h2]; simp

theorem advGo_le (cands : Array UInt64) (w : UInt64) : ∀ f p, p ≤ cands.size → advGo cands w f p ≤ cands.size := by
  intro f
  induction f with
  | zero => intro p hp; simpa [advGo] using hp
  | succ f ih =>
    intro p hp
    rw [advGo.eq_2]
    by_cases h : (p < cands.size && cands[p]! < w) = true
    · rw [if_pos h]
      have : p < cands.size := by simpa using (Bool.and_eq_true _ _ |>.mp h).1
      exact ih (p + 1) (by omega)
    · rw [if_neg h]; exact hp

theorem probeFrom_le (cands : Array UInt64) (w : UInt64) (p : Nat) : probeFrom cands w p ≤ cands.size := by
  unfold probeFrom
  apply advGo_le
  unfold startFor
  split
  · rename_i h
    exact (Bool.and_eq_true _ _ |>.mp h).1 |> fun x => by simpa using x
  · exact Nat.zero_le _

theorem usize_succ_of_le (b : ByteArray) (hb : b.size < smallBytes) (idx i : USize)
    (h : idx.toNat ≤ i.toNat) (hi : i.toNat < b.size) : (idx + 1).toNat = idx.toNat + 1 :=
  usize_succ b idx hb (by omega)

theorem usize_eq_zero_iff (p : USize) : (p == 0) = (p.toNat == 0) := by
  by_cases h : p.toNat = 0
  · have : p = 0 := USize.toNat_inj.mp (by simpa using h)
    subst this; simp
  · have hp : p ≠ 0 := fun hh => h (by simp [hh])
    have e1 : (p == 0) = false := by simpa using hp
    have e2 : (p.toNat == 0) = false := by simpa using h
    rw [e1, e2]

theorem findBody_eq (b : ByteArray) (lo hi : Nat) (cands : Array UInt64)
    (hlo : lo < smallBytes) (hcs : cands.size < smallBytes)
    (idx : USize) (hidx1 : (idx + 1).toNat = idx.toNat + 1)
    (next : USize → UInt64 → USize → UInt64 → UInt64 → Array Nat → ByteArray → Option (Array Nat × ByteArray))
    (nextN : Nat → UInt64 → Nat → UInt64 → UInt64 → Array Nat → ByteArray → Option (Array Nat × ByteArray))
    (hnext : ∀ v' p' c' lc' pos' out', p'.toNat < smallBytes →
        next (idx + 1) v' p' c' lc' pos' out' = nextN (idx.toNat + 1) v' p'.toNat c' lc' pos' out')
    (v : UInt64) (p : USize) (hp : p.toNat < smallBytes) (c lc : UInt64) (pos : Array Nat) (out : ByteArray) :
    (if lo.toUSize ≤ idx then
        let fast := p < cands.usize && !(c < v) && (p == 0 || lc < v)
        let q := if fast then p else (probeFrom cands v p.toNat).toUSize
        let c' := if fast then c else cAt cands q.toNat
        let lc' := if fast then lc else lAt cands q.toNat
        if q < cands.usize && c' == v then
          next (idx + 1) v q c' lc' (pos.push idx.toNat) (put64 out v)
        else next (idx + 1) v q c' lc' pos out
      else next (idx + 1) v p c lc pos out) =
    (if idx.toNat ≥ lo then
        let fast := isFast cands v p.toNat c lc
        let q := if fast then p.toNat else probeFrom cands v p.toNat
        let c' := if fast then c else cAt cands q
        let lc' := if fast then lc else lAt cands q
        if q < cands.size && c' == v then
          nextN (idx.toNat + 1) v q c' lc' (pos.push idx.toNat) (put64 out v)
        else nextN (idx.toNat + 1) v q c' lc' pos out
      else nextN (idx.toNat + 1) v p.toNat c lc pos out) := by
  have ht_lo := toUSize_toNat' lo hlo
  have ht_cs := usize_size_toNat cands hcs
  have hlo_le : (lo.toUSize ≤ idx) ↔ idx.toNat ≥ lo := by rw [USize.le_iff_toNat_le, ht_lo]
  have hlt : ∀ q : USize, (q < cands.usize) ↔ q.toNat < cands.size := fun q => by
    rw [USize.lt_iff_toNat_lt, ht_cs]
  have hnext' := fun (q : USize) (v' : UInt64) c' lc' pos' out' (hq : q.toNat < smallBytes) =>
    hnext v' q c' lc' pos' out' hq
  by_cases hl : idx.toNat ≥ lo
  · rw [if_pos (hlo_le.mpr hl), if_pos hl]
    have hfast : (p < cands.usize && !(c < v) && (p == 0 || lc < v)) = isFast cands v p.toNat c lc := by
      unfold isFast
      rw [usize_eq_zero_iff]
      have : decide (p < cands.usize) = decide (p.toNat < cands.size) := decide_eq_decide.mpr (hlt p)
      rw [this]
    simp only [hfast]
    by_cases hf : isFast cands v p.toNat c lc = true
    · simp only [hf, if_true]
      have hd : decide (p < cands.usize) = decide (p.toNat < cands.size) := decide_eq_decide.mpr (hlt p)
      rw [hd]
      split
      · exact hnext' p v c lc _ _ hp
      · exact hnext' p v c lc _ _ hp
    · have hf' : isFast cands v p.toNat c lc = false := by simpa using hf
      simp only [hf', Bool.false_eq_true, if_false]
      have hq1 := probeFrom_le cands v p.toNat
      have hqn : (probeFrom cands v p.toNat).toUSize.toNat = probeFrom cands v p.toNat :=
        toUSize_toNat' _ (by omega)
      have hd : decide ((probeFrom cands v p.toNat).toUSize < cands.usize) =
          decide (probeFrom cands v p.toNat < cands.size) := by
        apply decide_eq_decide.mpr
        rw [hlt, hqn]
      rw [hd, hqn]
      split
      · rw [hnext' _ _ _ _ _ _ (by omega), hqn]
      · rw [hnext' _ _ _ _ _ _ (by omega), hqn]
  · rw [if_neg (fun h => hl (hlo_le.mp h)), if_neg hl]
    exact hnext' p v c lc pos out hp

theorem deltaFindGoY_eq (b : ByteArray) (lo hi : Nat) (cands : Array UInt64)
    (hb : b.size < smallBytes) (hlo : lo < smallBytes) (hhi : hi < smallBytes)
    (hcs : cands.size < smallBytes) :
    ∀ n (i : USize) (idx : USize) prev acc (p : USize) (c lc : UInt64) pos out,
      b.size - i.toNat ≤ n → idx.toNat ≤ i.toNat → p.toNat < smallBytes →
      deltaFindGoY b cands cands.usize lo.toUSize hi.toUSize idx prev i acc p c lc pos out =
        deltaFindGoC b lo hi cands idx.toNat prev i acc p.toNat c lc pos out := by
  have ht_lo := toUSize_toNat' lo hlo
  have ht_hi := toUSize_toNat' hi hhi
  have ht_cs := usize_size_toNat cands hcs
  have hhi_le : ∀ idx : USize, (hi.toUSize ≤ idx) ↔ idx.toNat ≥ hi := fun idx => by
    rw [USize.le_iff_toNat_le, ht_hi]
  have hlo_le : ∀ idx : USize, (lo.toUSize ≤ idx) ↔ idx.toNat ≥ lo := fun idx => by
    rw [USize.le_iff_toNat_le, ht_lo]
  intro n
  induction n with
  | zero =>
    intro i idx prev acc p c lc pos out hn hidx hp
    rw [deltaFindGoY, deltaFindGoC]
    have h1 : ¬ i < b.usize := by rw [usize_lt_iff b i hb]; omega
    by_cases hh : idx.toNat ≥ hi
    · rw [if_pos ((hhi_le idx).mpr hh), if_pos hh]
    · rw [if_neg (fun h => hh ((hhi_le idx).mp h)), if_neg hh]
      simp only [h1, dite_false]
  | succ n ih =>
    intro i idx prev acc p c lc pos out hn hidx hp
    rw [deltaFindGoY, deltaFindGoC]
    by_cases hh : idx.toNat ≥ hi
    · rw [if_pos ((hhi_le idx).mpr hh), if_pos hh]
    rw [if_neg (fun h => hh ((hhi_le idx).mp h)), if_neg hh]
    by_cases hiu : i < b.usize
    case neg => rw [dif_neg hiu, dif_neg hiu]
    rw [dif_pos hiu, dif_pos hiu]
    have hib := L4Factoidal.Prim.Bytes.usize_lt_size hiu
    have hs := L4Factoidal.Prim.Bytes.usize_succ_toNat hiu
    by_cases hacc : acc < accCap
    case neg => rw [if_neg hacc, if_neg hacc, ht_lo, ht_hi]
    rw [if_pos hacc, if_pos hacc]
    generalize b.uget i _ = x
    by_cases hx : x < 128
    case neg =>
      rw [if_neg hx, if_neg hx]
      exact ih (i + 1) idx prev _ p c lc pos out (by rw [hs]; omega) (by rw [hs]; omega) hp
    rw [if_pos hx, if_pos hx]
    generalize acc * 128 + x.toUInt64 = z
    obtain ⟨hv, hok⟩ := zz_spec prev z
    have hib' : idx.toNat < b.size := by omega
    have hidx1 := usize_succ_of_le b hb idx i hidx hib
    have key : ∀ v : UInt64,
        (if lo.toUSize ≤ idx then
          let fast := p < cands.usize && !(c < v) && (p == 0 || lc < v)
          let q := if fast then p else (probeFrom cands v p.toNat).toUSize
          let c' := if fast then c else cAt cands q.toNat
          let lc' := if fast then lc else lAt cands q.toNat
          if q < cands.usize && c' == v then
            deltaFindGoY b cands cands.usize lo.toUSize hi.toUSize (idx + 1) v (i + 1) 0 q c' lc' (pos.push idx.toNat) (put64 out v)
          else deltaFindGoY b cands cands.usize lo.toUSize hi.toUSize (idx + 1) v (i + 1) 0 q c' lc' pos out
        else deltaFindGoY b cands cands.usize lo.toUSize hi.toUSize (idx + 1) v (i + 1) 0 p c lc pos out) =
        (if idx.toNat ≥ lo then
          let fast := isFast cands v p.toNat c lc
          let q := if fast then p.toNat else probeFrom cands v p.toNat
          let c' := if fast then c else cAt cands q
          let lc' := if fast then lc else lAt cands q
          if q < cands.size && c' == v then
            deltaFindGoC b lo hi cands (idx.toNat + 1) v (i + 1) 0 q c' lc' (pos.push idx.toNat) (put64 out v)
          else deltaFindGoC b lo hi cands (idx.toNat + 1) v (i + 1) 0 q c' lc' pos out
        else deltaFindGoC b lo hi cands (idx.toNat + 1) v (i + 1) 0 p.toNat c lc pos out) := by
      intro v
      refine findBody_eq b lo hi cands hlo hcs idx hidx1
        (fun idx' v' q c' lc' pos' out' => deltaFindGoY b cands cands.usize lo.toUSize hi.toUSize idx' v' (i + 1) 0 q c' lc' pos' out')
        (fun idx' v' q c' lc' pos' out' => deltaFindGoC b lo hi cands idx' v' (i + 1) 0 q c' lc' pos' out')
        ?_ v p hp c lc pos out
      intro v' p' c' lc' pos' out' hp'
      rw [ih (i + 1) (idx + 1) v' 0 p' c' lc' pos' out' (by rw [hs]; omega) (by rw [hs]; omega) hp', hidx1]
    by_cases he : (z % 2 == 0) = true
    · simp only [he, if_true] at hv hok ⊢
      rw [← hv]
      try rw [← hv] at hok
      generalize zzV prev z = v at hok ⊢
      by_cases hk : prev ≤ v
      · rw [if_pos hk, if_pos (hok.mpr hk)]; exact key v
      · rw [if_neg hk, if_neg (fun h => hk (hok.mp h))]
    · simp only [he, Bool.false_eq_true, if_false] at hv hok ⊢
      rw [← hv]
      try rw [← hv] at hok
      generalize zzV prev z = v at hok ⊢
      by_cases hk : z / 2 + 1 ≤ prev
      · rw [if_pos hk, if_pos (hok.mpr hk)]; exact key v
      · rw [if_neg hk, if_neg (fun h => hk (hok.mp h))]

/-- The start that `findWords` calls equals the `Nat` find loop with the
    fuel it had before the word loops. -/
theorem deltaFindStart_eq (b : ByteArray) (lo hi : Nat) (cands : Array UInt64) (i p : Nat)
    (hi' : i < b.size) :
    deltaFindStart b lo hi cands i p =
      deltaFindGo b lo hi cands (b.size - i + 2) 0 0 (i + 1) 0 p #[] .empty := by
  rw [← deltaFindStartNat_eq b lo hi cands i p hi']
  unfold deltaFindStart
  by_cases hf : findFits b lo hi cands p = true
  · rw [if_pos hf]
    simp only [findFits, Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨⟨⟨⟨hb, hlo⟩, hhi⟩, hcs⟩, hp⟩ := hf
    rw [deltaFindGoY_eq b lo hi cands hb hlo hhi hcs b.size (i + 1).toUSize 0 0 0 p.toUSize _ _ #[] .empty
      (by omega) (by simp) (by rw [toUSize_toNat' p hp]; exact hp)]
    unfold deltaFindStartNat
    rw [if_pos hb, toUSize_toNat' p hp]
    simp
  · rw [if_neg hf]

/-- What `deltaGatherGoK` does after a complete varint of value `z` that
    ends before `i'`. -/
def gatherRowK (b : ByteArray) (pos : Array Nat) (idx : Nat) (prev : UInt64) (i' : USize)
    (z : UInt64) (k nk : Nat) (out : ByteArray) : Option ByteArray :=
  let h2 := if z % 2 == 0 then z / 2 else z / 2 + 1
  let v := if z % 2 == 0 then prev + h2 else prev - h2
  let ok := if z % 2 == 0 then prev ≤ v else h2 ≤ prev
  if ok then
    if idx == nk then deltaGatherGoK b pos (idx + 1) v i' 0 (k + 1) (posAt pos (k + 1)) (put64 out v)
    else deltaGatherGoK b pos (idx + 1) v i' 0 k nk out
  else none

theorem K_term (b : ByteArray) (pos : Array Nat) (idx : Nat) (prev : UInt64) (i : USize) (acc : UInt64)
    (k nk : Nat) (out : ByteArray) (hk : ¬ pos.size ≤ k) (hi : i < b.usize) (hacc : acc < accCap)
    (x : UInt8) (hx : b.uget i (L4Factoidal.Prim.Bytes.usize_lt_size hi) = x) (hx128 : x < 128) :
    deltaGatherGoK b pos idx prev i acc k nk out =
      gatherRowK b pos idx prev (i + 1) (acc * 128 + x.toUInt64) k nk out := by
  rw [deltaGatherGoK, if_neg (by omega), dif_pos hi, if_pos hacc]
  simp only [hx, hx128, if_true]
  rfl

theorem K_cont (b : ByteArray) (pos : Array Nat) (idx : Nat) (prev : UInt64) (i : USize) (acc : UInt64)
    (k nk : Nat) (out : ByteArray) (hk : ¬ pos.size ≤ k) (hi : i < b.usize) (hacc : acc < accCap)
    (x : UInt8) (hx : b.uget i (L4Factoidal.Prim.Bytes.usize_lt_size hi) = x) (hx128 : ¬ x < 128) :
    deltaGatherGoK b pos idx prev i acc k nk out =
      deltaGatherGoK b pos idx prev (i + 1) (acc * 128 + (x - 128).toUInt64) k nk out := by
  rw [deltaGatherGoK, if_neg (by omega), dif_pos hi, if_pos hacc]
  simp only [hx, hx128, if_false]

theorem usize_add_ofNat (i : USize) (m : Nat) : (i + 1) + USize.ofNat (m + 1) = i + USize.ofNat (m + 1 + 1) := by
  have h1 : USize.ofNat (m + 1 + 1) = USize.ofNat (m + 1) + 1 := USize.ofNat_add (m + 1) 1
  rw [h1, USize.add_assoc, USize.add_comm 1]

theorem K_row (b : ByteArray) (pos : Array Nat) (hb : b.size < smallBytes) (p0 : Nat) :
    ∀ (m j : Nat) (i : USize) (acc : UInt64) (idx : Nat) (prev : UInt64) (k nk : Nat) (out : ByteArray),
      i.toNat = p0 + j → ¬ pos.size ≤ k → p0 + j + m < b.size →
      (∀ t, t < m → ¬ getOr0 b (p0 + j + t) < 128) → getOr0 b (p0 + j + m) < 128 →
      m ≤ 7 → acc.toNat < 2 ^ (56 - 7 * m) →
      deltaGatherGoK b pos idx prev i acc k nk out =
        gatherRowK b pos idx prev (i + USize.ofNat (m + 1))
          (hz (fun t => getOr0 b (p0 + t)) acc j m) k nk out := by
  intro m
  induction m with
  | zero =>
    intro j i acc idx prev k nk out hi hk hlt hc ht hm hacc
    have hib : i.toNat < b.size := by omega
    have hiu : i < b.usize := (usize_lt_iff b i hb).mpr hib
    have hac : acc < accCap := by
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [accCap_toNat]
      have : 2 ^ (56 - 7 * 0) = 72057594037927936 := by decide
      omega
    have hx : b.uget i (L4Factoidal.Prim.Bytes.usize_lt_size hiu) = getOr0 b (p0 + j) := by
      rw [L4Factoidal.Prim.Bytes.uget_eq_getOr0, hi]
    rw [K_term b pos idx prev i acc k nk out hk hiu hac _ hx (by simpa using ht)]
    simp only [hz]
    rfl
  | succ m ih =>
    intro j i acc idx prev k nk out hi hk hlt hc ht hm hacc
    have hib : i.toNat < b.size := by omega
    have hiu : i < b.usize := (usize_lt_iff b i hb).mpr hib
    have hac : acc < accCap := by
      apply UInt64.lt_iff_toNat_lt.mpr
      rw [accCap_toNat]
      have : 2 ^ (56 - 7 * (m + 1)) ≤ 2 ^ 56 := Nat.pow_le_pow_right (by omega) (by omega)
      have : 2 ^ 56 < 144115188075855872 := by decide
      omega
    have hx : b.uget i (L4Factoidal.Prim.Bytes.usize_lt_size hiu) = getOr0 b (p0 + j) := by
      rw [L4Factoidal.Prim.Bytes.uget_eq_getOr0, hi]
    have hnot : ¬ getOr0 b (p0 + j) < 128 := by simpa using hc 0 (by omega)
    rw [K_cont b pos idx prev i acc k nk out hk hiu hac _ hx hnot]
    have hs := L4Factoidal.Prim.Bytes.usize_succ_toNat hiu
    have hacc' : (acc * 128 + (getOr0 b (p0 + j) - 128).toUInt64).toNat < 2 ^ (56 - 7 * m) := by
      have hxn : ¬ (getOr0 b (p0 + j)).toNat < 128 := fun h' => hnot (UInt8.lt_iff_toNat_lt.mpr (by simpa using h'))
      rw [cont_toNat acc _ hac hnot]
      have hx256 := (getOr0 b (p0 + j)).toNat_lt
      have e : 2 ^ (56 - 7 * m) = 2 ^ (56 - 7 * (m + 1)) * 128 := by
        rw [show 56 - 7 * m = (56 - 7 * (m + 1)) + 7 by omega, Nat.pow_add]
      omega
    rw [ih (j + 1) (i + 1) _ idx prev k nk out (by rw [hs]; omega) hk (by omega)
      (fun t ht' => by
        have := hc (t + 1) (by omega)
        rwa [show p0 + j + (t + 1) = p0 + (j + 1) + t by omega] at this)
      (by rwa [show p0 + j + (m + 1) = p0 + (j + 1) + m by omega] at ht) (by omega) hacc']
    simp only [hz]
    rw [usize_add_ofNat]

theorem ldSpec_bit (b : ByteArray) (j k t : Nat) (hk : k < 8) (ht : t < 8) :
    (L4Factoidal.Prim.Bytes.ldU64LESpec b j).toBitVec.getLsbD (8 * k + t) =
      (getOr0 b (j + k)).toBitVec.getLsbD t := by
  unfold L4Factoidal.Prim.Bytes.ldU64LESpec
  have : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by omega
  rcases this with h | h | h | h | h | h | h | h <;> subst h <;>
    simp (disch := omega) [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, BitVec.getLsbD_or, BitVec.shiftLeft_eq',
      BitVec.getLsbD_shiftLeft, UInt8.toBitVec_toUInt64, BitVec.getLsbD_setWidth,
      decide_eq_true, decide_eq_false, BitVec.getLsbD_of_ge]

theorem bt_ld (b : ByteArray) (j k : Nat) (hk : k < 8) :
    bt (L4Factoidal.Prim.Bytes.ldU64LESpec b j) k = getOr0 b (j + k) := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro t ht
  rw [bt_bit _ k t hk ht, ldSpec_bit b j k t hk ht]

theorem hf_congr (f g : Nat → UInt8) : ∀ (m j : Nat), (∀ t, t ≤ m → f (j + t) = g (j + t)) →
    hf f j m = hf g j m := by
  intro m
  induction m with
  | zero => intro j h; simp only [hf]; rw [show f j = g j from by simpa using h 0 (by omega)]
  | succ m ih =>
    intro j h
    simp only [hf]
    rw [show f j = g j from by simpa using h 0 (by omega)]
    rw [ih (j + 1) (fun t ht => by
      have := h (t + 1) (by omega)
      rwa [show j + (t + 1) = j + 1 + t by omega] at this)]

theorem toUSize_ofNat_small (x : Nat) (h : x < 256) : (UInt64.ofNat x).toUSize = USize.ofNat x := by
  apply USize.toNat_inj.mp
  have hs : 256 ≤ USize.size := by
    simp only [USize.size]
    have : 2 ^ 32 ≤ 2 ^ System.Platform.numBits := by
      rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
    have : 256 ≤ 2 ^ 32 := by decide
    omega
  have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [UInt64.toNat_toUSize, USize.toNat_ofNat', UInt64.toNat_ofNat', ← hsz]
  have : x % 2 ^ 64 = x := Nat.mod_eq_of_lt (by omega)
  rw [this]

theorem usize_beq_toNat (a b : USize) : (a == b) = (a.toNat == b.toNat) := by
  by_cases h : a.toNat = b.toNat
  · have : a = b := USize.toNat_inj.mp h
    subst this; simp
  · have h1 : ¬ a = b := fun hh => h (by rw [hh])
    have e1 : (a == b) = false := by simpa using h1
    have e2 : (a.toNat == b.toNat) = false := by simpa using h
    rw [e1, e2]

theorem posAtU_toNat (pos : Array Nat) (hall : ∀ r ∈ pos.toList, r < smallBytes) (k : USize) :
    (posAtU pos k).toNat = posAt pos k.toNat := by
  unfold posAtU posAt
  by_cases h : k.toNat < pos.size
  · rw [dif_pos h, dif_pos h]
    exact toUSize_toNat' _ (hall _ (by simp [Array.mem_toList_iff, Array.getElem_mem h]))
  · rw [dif_neg h, dif_neg h]; rfl

theorem gatherPost_eq (b : ByteArray) (pos : Array Nat) (hpos : pos.size < smallBytes)
    (hall : ∀ r ∈ pos.toList, r < smallBytes)
    (i' : USize) (hi' : i'.toNat < smallBytes)
    (next : USize → UInt64 → USize → USize → ByteArray → Option ByteArray)
    (hnext : ∀ idx' v k' nk' out', idx'.toNat ≤ i'.toNat → k'.toNat ≤ pos.size →
        nk'.toNat = posAt pos k'.toNat →
        next idx' v k' nk' out' = deltaGatherGoK b pos idx'.toNat v i' 0 k'.toNat nk'.toNat out')
    (idx k nk : USize) (hidx : idx.toNat < i'.toNat) (hk : k.toNat < pos.size)
    (hnk : nk.toNat = posAt pos k.toNat) (prev z : UInt64) (out : ByteArray) :
    (let v := zzV prev z
     if zzOk prev z v = true then
       (if idx == nk then next (idx + 1) v (k + 1) (posAtU pos (k + 1)) (put64 out v)
        else next (idx + 1) v k nk out)
     else none) =
    gatherRowK b pos idx.toNat prev i' z k.toNat nk.toNat out := by
  have hsm : smallBytes = 2147483648 := rfl
  have h32 : 2 ^ 32 ≤ USize.size := by
    simp only [USize.size]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
  have h32' : (4294967296 : Nat) ≤ USize.size := by simpa using h32
  have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
  have hidx1 : (idx + 1).toNat = idx.toNat + 1 := by
    simp only [USize.toNat_add, USize.toNat_one]
    apply Nat.mod_eq_of_lt
    omega
  have hk1 : (k + 1).toNat = k.toNat + 1 := by
    simp only [USize.toNat_add, USize.toNat_one]
    apply Nat.mod_eq_of_lt
    omega
  have hposU : (posAtU pos (k + 1)).toNat = posAt pos (k.toNat + 1) := by
    rw [posAtU_toNat pos hall, hk1]
  have inner : ∀ v : UInt64,
      (if idx == nk then next (idx + 1) v (k + 1) (posAtU pos (k + 1)) (put64 out v)
       else next (idx + 1) v k nk out) =
      (if idx.toNat == nk.toNat then
        deltaGatherGoK b pos (idx.toNat + 1) v i' 0 (k.toNat + 1) (posAt pos (k.toNat + 1)) (put64 out v)
       else deltaGatherGoK b pos (idx.toNat + 1) v i' 0 k.toNat nk.toNat out) := by
    intro v
    rw [usize_beq_toNat]
    split
    · rw [hnext _ _ _ _ _ (by omega) (by omega) (by rw [hposU, hk1]), hidx1, hk1, hposU]
    · rw [hnext _ _ _ _ _ (by omega) (by omega) hnk, hidx1]
  obtain ⟨hv, hok⟩ := zz_spec prev z
  unfold gatherRowK
  by_cases he : (z % 2 == 0) = true
  · simp only [he, if_true] at hv hok ⊢
    rw [← hv]
    try rw [← hv] at hok
    generalize zzV prev z = v at hok ⊢
    by_cases hk' : prev ≤ v
    · rw [if_pos hk', if_pos (hok.mpr hk')]; exact inner v
    · rw [if_neg hk', if_neg (fun h => hk' (hok.mp h))]
  · simp only [he, Bool.false_eq_true, if_false] at hv hok ⊢
    rw [← hv]
    try rw [← hv] at hok
    generalize zzV prev z = v at hok ⊢
    by_cases hk' : z / 2 + 1 ≤ prev
    · rw [if_pos hk', if_pos (hok.mpr hk')]; exact inner v
    · rw [if_neg hk', if_neg (fun h => hk' (hok.mp h))]

theorem usize_add_ofNat_toNat (i : USize) (m : Nat) (h : i.toNat + m < smallBytes) :
    (i + USize.ofNat m).toNat = i.toNat + m := by
  have hsm : smallBytes = 2147483648 := rfl
  have h32 : 2 ^ 32 ≤ USize.size := by
    simp only [USize.size]
    rcases System.Platform.numBits_eq with h | h <;> rw [h] <;> decide
  have h32' : (4294967296 : Nat) ≤ USize.size := by simpa using h32
  have hsz : USize.size = 2 ^ System.Platform.numBits := rfl
  rw [USize.toNat_add, USize.toNat_ofNat']
  rw [Nat.mod_eq_of_lt (a := m) (by omega)]
  exact Nat.mod_eq_of_lt (by omega)

theorem gatherFast (b : ByteArray) (pos : Array Nat) (hb : b.size < smallBytes)
    (hpos : pos.size < smallBytes) (hall : ∀ r ∈ pos.toList, r < smallBytes) (f : Nat)
    (hY : ∀ i' : USize, b.size - i'.toNat < f → ∀ idx' v k' nk' out',
        idx'.toNat ≤ i'.toNat → k'.toNat ≤ pos.size → nk'.toNat = posAt pos k'.toNat →
        deltaGatherGoY b pos pos.usize f idx' v i' 0 k' nk' out' =
          deltaGatherGoK b pos idx'.toNat v i' 0 k'.toNat nk'.toNat out')
    (idx : USize) (prev : UInt64) (i k nk : USize) (out : ByteArray)
    (hn : b.size - i.toNat < f + 1) (hidx : idx.toNat ≤ i.toNat) (hk : k.toNat < pos.size)
    (hnk : nk.toNat = posAt pos k.toNat)
    (hwin1 : i + 8 ≤ b.usize) (hwin2 : i < i + 8)
    (hy : (Prim.Bytes.ldU64LE b i ||| C7) ≠ allOnes) :
    (let w := Prim.Bytes.ldU64LE b i
     let y := w ||| C7
     let m := lenMask y
     let z := vVal w m
     let i' := i + (vLen m).toUSize
     let v := zzV prev z
     if zzOk prev z v = true then
       (if idx == nk then deltaGatherGoY b pos pos.usize f (idx + 1) v i' 0 (k + 1) (posAtU pos (k + 1)) (put64 out v)
        else deltaGatherGoY b pos pos.usize f (idx + 1) v i' 0 k nk out)
     else none) =
    deltaGatherGoK b pos idx.toNat prev i 0 k.toNat nk.toNat out := by
  have hwn := L4Factoidal.Prim.Bytes.window_of_test hwin1 hwin2
  have hld := L4Factoidal.Prim.Bytes.ldU64LE_eq b i
  rw [hld] at hy ⊢
  obtain ⟨n, hn8, hcn, htn⟩ := exists_term _ hy
  rw [bt_ld b i.toNat n hn8] at htn
  have hcn' : ∀ t, t < n → ¬ getOr0 b (i.toNat + t) < 128 := fun t ht => by
    have := hcn t ht
    rwa [bt_ld b i.toNat t (by omega)] at this
  have hcn2 : ∀ t, t < n → ¬ bt (L4Factoidal.Prim.Bytes.ldU64LESpec b i.toNat) t < 128 := hcn
  obtain ⟨_, hlen, hval⟩ := fastRead_spec _ n hn8 hcn2 (by rwa [bt_ld b i.toNat n hn8])
  have hrow := K_row b pos hb i.toNat n 0 i 0 idx.toNat prev k.toNat nk.toNat out
    (by omega) (by omega) (by omega) (by simpa using hcn') (by simpa using htn) (by omega)
    (by have : 2 ^ (56 - 7 * n) > 0 := Nat.two_pow_pos _; simp; omega)
  have hi'n : (i + USize.ofNat (n + 1)).toNat = i.toNat + (n + 1) :=
    usize_add_ofNat_toNat i (n + 1) (by omega)
  have hlen' : (vLen (lenMask (L4Factoidal.Prim.Bytes.ldU64LESpec b i.toNat ||| C7))).toUSize =
      USize.ofNat (n + 1) := by
    rw [hlen]; exact toUSize_ofNat_small _ (by omega)
  have hzv : hz (fun t => getOr0 b (i.toNat + t)) 0 0 n =
      hf (bt (L4Factoidal.Prim.Bytes.ldU64LESpec b i.toNat)) 0 n := by
    rw [hz_eq_hf (fun t => getOr0 b (i.toNat + t)) n 0 0 (by omega) (by simpa using hcn') (by simpa using htn)]
    have h0 : (0 : UInt64) <<< UInt64.ofNat (7 * (n + 1)) = 0 := by
      apply UInt64.eq_of_toBitVec_eq; simp [UInt64.toBitVec_shiftLeft]
    rw [h0, UInt64.zero_or]
    apply hf_congr
    intro t ht
    simp only [Nat.zero_add]
    rw [bt_ld b i.toNat t (by omega)]
  simp only [hlen', hval]
  rw [hrow, hzv]
  exact gatherPost_eq b pos hpos hall (i + USize.ofNat (n + 1)) (by omega)
    (fun idx' v k' nk' out' => deltaGatherGoY b pos pos.usize f idx' v (i + USize.ofNat (n + 1)) 0 k' nk' out')
    (fun idx' v k' nk' out' h1 h2 h3 => hY (i + USize.ofNat (n + 1)) (by omega) idx' v k' nk' out' h1 h2 h3)
    idx k nk (by omega) hk hnk prev _ out

theorem deltaGatherGoY_eq (b : ByteArray) (pos : Array Nat) (hb : b.size < smallBytes)
    (hpos : pos.size < smallBytes) (hall : ∀ r ∈ pos.toList, r < smallBytes) :
    ∀ fuel (idx : USize) prev (i : USize) acc (k nk : USize) out,
      b.size - i.toNat < fuel → idx.toNat ≤ i.toNat → k.toNat ≤ pos.size →
      nk.toNat = posAt pos k.toNat →
      deltaGatherGoY b pos pos.usize fuel idx prev i acc k nk out =
        deltaGatherGoK b pos idx.toNat prev i acc k.toNat nk.toNat out := by
  have hps : pos.usize.toNat = pos.size := by
    simp only [Array.usize, USize.toNat_ofNat', Nat.toUSize]
    exact toUSize_toNat' _ hpos
  have hpsle : ∀ k : USize, (pos.usize ≤ k) ↔ pos.size ≤ k.toNat := fun k => by
    rw [USize.le_iff_toNat_le, hps]
  intro fuel
  induction fuel with
  | zero => intro idx prev i acc k nk out hn; omega
  | succ f ih =>
    intro idx prev i acc k nk out hn hidx hk hnk
    rw [deltaGatherGoY, deltaGatherGoK]
    by_cases hk0 : pos.size ≤ k.toNat
    · rw [if_pos ((hpsle k).mpr hk0), if_pos hk0]
    rw [if_neg (fun h => hk0 ((hpsle k).mp h)), if_neg hk0]
    by_cases hiu : i < b.usize
    case neg => rw [dif_neg hiu, dif_neg hiu]
    rw [dif_pos hiu, dif_pos hiu]
    have hib := L4Factoidal.Prim.Bytes.usize_lt_size hiu
    have hs := L4Factoidal.Prim.Bytes.usize_succ_toNat hiu
    by_cases hacc : acc < accCap
    case neg => rw [if_neg hacc, if_neg hacc]
    rw [if_pos hacc, if_pos hacc]
    have hsm : smallBytes = 2147483648 := rfl
    have hnext_of : ∀ (i' : USize), b.size - i'.toNat < f → ∀ idx' v k' nk' out',
        idx'.toNat ≤ i'.toNat → k'.toNat ≤ pos.size → nk'.toNat = posAt pos k'.toNat →
        deltaGatherGoY b pos pos.usize f idx' v i' 0 k' nk' out' =
          deltaGatherGoK b pos idx'.toNat v i' 0 k'.toNat nk'.toNat out' :=
      fun i' h idx' v k' nk' out' h1 h2 h3 => ih idx' v i' 0 k' nk' out' h h1 h2 h3
    have hk' : k.toNat < pos.size := by omega
    by_cases hfast : (acc == 0 && decide (i + 8 ≤ b.usize) && decide (i < i + 8) &&
        (Prim.Bytes.ldU64LE b i ||| C7) != allOnes) = true
    · rw [if_pos hfast]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at hfast
      obtain ⟨⟨⟨hacc0, hw1⟩, hw2⟩, hy⟩ := hfast
      exact (gatherFast b pos hb hpos hall f hnext_of idx prev i k nk out hn hidx hk' hnk hw1 hw2 hy).trans
        (by subst hacc0; rw [deltaGatherGoK, if_neg hk0, dif_pos hiu, if_pos hacc])
    · rw [if_neg hfast]
      generalize hxdef : b.uget i _ = x
      by_cases hx : x < 128
      · rw [if_pos hx, if_pos hx]
        exact gatherPost_eq b pos hpos hall (i + 1) (by rw [hs]; omega)
          (fun idx' v k' nk' out' => deltaGatherGoY b pos pos.usize f idx' v (i + 1) 0 k' nk' out')
          (fun idx' v k' nk' out' h1 h2 h3 => hnext_of (i + 1) (by rw [hs]; omega) idx' v k' nk' out' h1 h2 h3)
          idx k nk (by rw [hs]; omega) hk' hnk prev (acc * 128 + x.toUInt64) out
      · rw [if_neg hx, if_neg hx]
        exact ih idx prev (i + 1) _ k nk out (by rw [hs]; omega) (by rw [hs]; omega) hk hnk

theorem deltaGatherStart_eq (b : ByteArray) (pos : Array Nat) (i : Nat) (hi' : i < b.size) :
    deltaGatherStart b pos i =
      deltaGatherGo b pos (b.size - i + 2) 0 0 (i + 1) 0 0 (ByteArray.emptyWithCapacity (8 * pos.size)) := by
  rw [← deltaGatherStartNat_eq b pos i hi']
  unfold deltaGatherStart
  by_cases hf : gatherFits b pos = true
  · rw [if_pos hf]
    simp only [gatherFits, Bool.and_eq_true, decide_eq_true_eq] at hf
    obtain ⟨⟨hb, hpos⟩, hallb⟩ := hf
    have hall : ∀ r ∈ pos.toList, r < smallBytes := by
      intro r hr
      rw [Array.all_eq_true] at hallb
      obtain ⟨idx, hidx, rfl⟩ := List.getElem_of_mem hr
      have := hallb idx (by simpa using hidx)
      simpa using this
    have hz : (0 : USize).toNat = 0 := by simp
    rw [deltaGatherGoY_eq b pos hb hpos hall (b.size + 1) 0 0 (i + 1).toUSize 0 0 (posAtU pos 0) _
      (by omega) (by simp) (by simp) (by rw [posAtU_toNat pos hall, hz])]
    unfold deltaGatherStartNat
    rw [if_pos hb, hz, posAtU_toNat pos hall, hz]
  · rw [if_neg hf]

#print axioms zz_spec
#print axioms probeFrom_le
#print axioms findBody_eq
#print axioms deltaFindGoY_eq
#print axioms deltaFindStart_eq
#print axioms K_row
#print axioms bt_ld
#print axioms gatherPost_eq
#print axioms gatherFast
#print axioms deltaGatherGoY_eq
#print axioms deltaGatherStart_eq

end L4Factoidal.Storage.Sbm11.Sip
