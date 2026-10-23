/-
L4Factoidal.Storage.Sbm11.DateKeyTheorems — `DateKey.dateCmpKey?` gives the
XSD value-space order of `Fn.Comparison.termCompare`
(https://github.com/danbri/factoidal/issues/948).

* `mono`: on valid dates with year 1 to 9999, `XSD.daysFromCivil` is strictly
  increasing in `year * 512 + month * 32 + day` (`same_year`: 144 month pairs
  with `omega`; `first_mono`: induction on the years between).
* `dateParts?_parse`: `XSD.parseDateTimeFor .xsd10 .date` of an admitted form
  is the date value with that year, month and day and no timezone (through the
  XSD 1.0 year adapter, `padYear_digits`).
* `calendarOrder_admitted`: for two admitted forms, `Fn.Comparison.calendarOrder
  .date` is `compare` of their order keys.
* `dateCmpKey_termCompare`: when `dateCmpKey? op swap kc buf a e = some r`, the
  constant `c` has `dateConst? c = some kc`, and `decodeKey?` reads the key as
  the term `t`, then `termCompare t (.literal c) op` (`swap`: `termCompare
  (.literal c) t op`) is `some r`. No premise states a comparison result.
* `dateCmpKey_sound`: then the reference FILTER value of `?v OP c` (or `c OP
  ?v`) on `t` is `r`, for `OP` one of `<`, `<=`, `>`, `>=`.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.DateKey
import L4Factoidal.Storage.Sbm11.TermKeyTheorems
import L4Factoidal.Storage.TermCodecTheorems
import L4Factoidal.XSD.Lexical

namespace L4Factoidal.Storage.Sbm11.DateKey

open L4Factoidal.RDF
open L4Factoidal.XSD

/-! ## The day number is increasing in the date -/


/-- `daysFromCivil` with Euclidean division, for a non-negative March-based year. -/
def civ (y' : Int) (mp : Nat) (d : Nat) : Int :=
  y' / 400 * 146097 + ((y' - y' / 400 * 400) * 365 + (y' - y' / 400 * 400) / 4 - (y' - y' / 400 * 400) / 100
    + ((153 * (mp : Int) + 2) / 5 + (d : Int) - 1)) - 719468

theorem dfc_eq (y : Int) (m d : Nat) (hy : 1 ≤ y) :
    daysFromCivil y m d = civ (if m ≤ 2 then y - 1 else y) ((m + 9) % 12) d := by
  have hy' : (if m ≤ 2 then y - 1 else y) ≥ 0 := by split <;> omega
  unfold daysFromCivil civ
  simp only []
  rw [if_pos hy', Int.tdiv_eq_ediv_of_nonneg hy']

theorem feb_mar (Y : Int) (hY : 1 ≤ Y) :
    daysFromCivil Y 3 1 = daysFromCivil Y 2 (daysInMonth Y 2) + 1 := by
  rw [dfc_eq _ _ _ hY, dfc_eq _ _ _ hY]
  simp only [daysInMonth, isLeapYear, civ]
  simp
  split <;> rename_i h <;> omega

theorem same_year (Y : Int) (M1 M2 D1 D2 : Nat) (h1 : 1 ≤ Y)
   (hm1 : 1 ≤ M1 ∧ M1 ≤ 12) (hm2 : 1 ≤ M2 ∧ M2 ≤ 12) (hd1 : 1 ≤ D1 ∧ D1 ≤ daysInMonth Y M1)
   (hd2 : 1 ≤ D2 ∧ D2 ≤ daysInMonth Y M2)
   (hlt : M1 * 32 + D1 < M2 * 32 + D2) :
   daysFromCivil Y M1 D1 < daysFromCivil Y M2 D2 := by
  rw [dfc_eq _ _ _ h1, dfc_eq _ _ _ h1]
  simp only [daysInMonth, isLeapYear] at hd1 hd2
  obtain ⟨a1, b1⟩ := hm1
  obtain ⟨a2, b2⟩ := hm2
  unfold civ
  have c1 : M1 = 1 ∨ M1 = 2 ∨ M1 = 3 ∨ M1 = 4 ∨ M1 = 5 ∨ M1 = 6 ∨ M1 = 7 ∨ M1 = 8 ∨ M1 = 9 ∨ M1 = 10 ∨ M1 = 11 ∨ M1 = 12 := by omega
  have c2 : M2 = 1 ∨ M2 = 2 ∨ M2 = 3 ∨ M2 = 4 ∨ M2 = 5 ∨ M2 = 6 ∨ M2 = 7 ∨ M2 = 8 ∨ M2 = 9 ∨ M2 = 10 ∨ M2 = 11 ∨ M2 = 12 := by omega
  rcases c1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  rcases c2 with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp at hd1 hd2 hlt ⊢ <;> (try split at hd1) <;> (try split at hd2) <;> omega

theorem next_year (Y : Int) (h1 : 1 ≤ Y) : daysFromCivil (Y + 1) 1 1 = daysFromCivil Y 12 31 + 1 := by
  rw [dfc_eq _ _ _ (by omega), dfc_eq _ _ _ h1]
  simp [civ]
  omega

theorem dim_ge (Y : Int) (M : Nat) : 28 ≤ daysInMonth Y M := by
  simp only [daysInMonth]; split <;> (try split) <;> (try split) <;> omega

theorem dim_le (Y : Int) (M : Nat) : daysInMonth Y M ≤ 31 := by
  simp only [daysInMonth]; split <;> (try split) <;> (try split) <;> omega

theorem dim_12 (Y : Int) : daysInMonth Y 12 = 31 := by simp [daysInMonth]
theorem dim_1 (Y : Int) : daysInMonth Y 1 = 31 := by simp [daysInMonth]

theorem le_last (Y : Int) (M D : Nat) (h1 : 1 ≤ Y) (hm : 1 ≤ M ∧ M ≤ 12)
    (hd : 1 ≤ D ∧ D ≤ daysInMonth Y M) : daysFromCivil Y M D ≤ daysFromCivil Y 12 31 := by
  by_cases h : M = 12 ∧ D = 31
  · obtain ⟨rfl, rfl⟩ := h; omega
  · have := dim_le Y M
    exact Int.le_of_lt (same_year Y M 12 D 31 h1 hm (by omega) hd (by rw [dim_12]; omega) (by omega))

theorem first_le (Y : Int) (M D : Nat) (h1 : 1 ≤ Y) (hm : 1 ≤ M ∧ M ≤ 12)
    (hd : 1 ≤ D ∧ D ≤ daysInMonth Y M) : daysFromCivil Y 1 1 ≤ daysFromCivil Y M D := by
  by_cases h : M = 1 ∧ D = 1
  · obtain ⟨rfl, rfl⟩ := h; omega
  · exact Int.le_of_lt (same_year Y 1 M 1 D h1 (by omega) hm (by rw [dim_1]; omega) hd (by omega))

theorem first_mono (Y : Int) (k : Nat) (h1 : 1 ≤ Y) :
    daysFromCivil Y 12 31 < daysFromCivil (Y + 1 + k) 1 1 := by
  induction k with
  | zero =>
    have := next_year Y h1
    have he : Y + 1 + ((0 : Nat) : Int) = Y + 1 := by omega
    rw [he]; omega
  | succ k ih =>
    have hn := next_year (Y + 1 + k) (by omega)
    have hf := first_le (Y + 1 + k) 12 31 (by omega) (by omega) (by rw [dim_12]; omega)
    have he : Y + 1 + ((k + 1 : Nat) : Int) = Y + 1 + k + 1 := by push_cast; omega
    rw [he]; omega

theorem mono (Y1 Y2 : Int) (M1 M2 D1 D2 : Nat) (h1 : 1 ≤ Y1) (h2 : 1 ≤ Y2)
   (hm1 : 1 ≤ M1 ∧ M1 ≤ 12) (hm2 : 1 ≤ M2 ∧ M2 ≤ 12) (hd1 : 1 ≤ D1 ∧ D1 ≤ daysInMonth Y1 M1)
   (hd2 : 1 ≤ D2 ∧ D2 ≤ daysInMonth Y2 M2)
   (hlt : Y1 * 512 + M1 * 32 + D1 < Y2 * 512 + M2 * 32 + D2) :
   daysFromCivil Y1 M1 D1 < daysFromCivil Y2 M2 D2 := by
  have := dim_le Y1 M1
  have := dim_le Y2 M2
  by_cases hy : Y1 = Y2
  · subst hy
    exact same_year Y1 M1 M2 D1 D2 h1 hm1 hm2 hd1 hd2 (by omega)
  · have hlt' : Y1 < Y2 := by omega
    obtain ⟨k, hk⟩ : ∃ k : Nat, Y2 = Y1 + 1 + k := ⟨(Y2 - Y1 - 1).toNat, by omega⟩
    have a := le_last Y1 M1 D1 h1 hm1 hd1
    have b := first_mono Y1 k h1
    have c := first_le Y2 M2 D2 h2 hm2 hd2
    rw [← hk] at b
    omega

/-! ## Bytes, characters and the date parse -/


/-- The character of a byte. -/
@[inline] def ch (b : UInt8) : Char := Char.ofNat b.toNat

theorem chn_facts : ∀ n, n < 128 →
    (Char.ofNat n).toNat = n ∧ (Char.ofNat n).utf8Size = 1 ∧ (Char.ofNat n).val.toUInt8.toNat = n := by decide

theorem chn_digit : ∀ n, n < 58 → 48 ≤ n → isDigitC (Char.ofNat n) = true := by decide

theorem ch_facts (b : UInt8) (h : b.toNat < 128) :
    (ch b).toNat = b.toNat ∧ (ch b).utf8Size = 1 ∧ (ch b).val.toUInt8 = b := by
  obtain ⟨h1, h2, h3⟩ := chn_facts b.toNat h
  exact ⟨h1, h2, UInt8.toNat_inj.1 h3⟩

theorem ch_digit (b : UInt8) (h1 : 48 ≤ b.toNat) (h2 : b.toNat ≤ 57) : isDigitC (ch b) = true :=
  chn_digit b.toNat (by omega) h1

theorem ascii_bytes (L : List UInt8) (h : ∀ b ∈ L, b.toNat < 128) :
    L4Factoidal.Storage.bytesOfString (String.ofList (L.map ch)) = L := by
  unfold L4Factoidal.Storage.bytesOfString
  rw [L4Factoidal.Storage.byteArray_toList_eq, String.toUTF8_eq_toByteArray, String.toByteArray_ofList]
  unfold List.utf8Encode
  simp only [List.data_toByteArray, List.toList_toArray]
  induction L with
  | nil => simp
  | cons b L ih =>
    have hb := ch_facts b (h b (by simp))
    simp only [List.map_cons, List.flatMap_cons, String.utf8EncodeChar_eq_singleton hb.2.1, hb.2.2]
    rw [ih (fun x hx => h x (by simp [hx]))]
    simp

theorem natOfDigits_eq (cs : List Char) : natOfDigits cs = Nat.ofDigitChars 10 cs 0 := by
  unfold natOfDigits Nat.ofDigitChars
  congr 1
  funext acc c
  rw [Nat.mul_comm]; rfl

theorem isDigitC_of_isDigit (c : Char) (h : c.isDigit = true) : isDigitC c = true := by
  simp only [Char.isDigit, isDigitC] at *
  simp only [Bool.and_eq_true, decide_eq_true_eq] at *
  exact ⟨h.1, h.2⟩

theorem parseYearFrag_pos (x : Char) (xs : List Char) (hx : x ≠ '-') :
    parseYearFrag (x :: xs) =
      (let ds := (x :: xs).takeWhile isDigitC
       if ds.length < 4 then none
       else if ds.length > 4 && ds.head? == some '0' then none
       else some (((natOfDigits ds : Nat) : Int), (x :: xs).drop ds.length)) := by
  unfold parseYearFrag
  split
  rename_i p neg ds heq
  revert heq
  split
  · rename_i r h
    intro _
    simp at h
    exact absurd h.1 hx
  · intro heq
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    simp

theorem yearFrag_of_digits (P r : List Char) (hP : ∀ c ∈ P, isDigitC c = true) (hlen : P.length = 4)
    (hr : r.head? = some '-') :
    parseYearFrag (P ++ r) = some (((natOfDigits P : Nat) : Int), r) := by
  obtain ⟨r', rfl⟩ : ∃ r', r = '-' :: r' := by
    cases r with
    | nil => simp at hr
    | cons x r' => simp at hr; exact ⟨r', by rw [hr]⟩
  have htw : (P ++ '-' :: r').takeWhile isDigitC = P := by
    rw [List.takeWhile_append_of_pos hP]
    simp [List.takeWhile, show isDigitC '-' = false by decide]
  match P, hlen, hP with
  | [a, b, c, d], _, hP =>
    have ha := hP a (by simp)
    have hx : a ≠ '-' := by intro h; rw [h] at ha; exact absurd ha (by decide)
    simp only [List.cons_append, List.nil_append] at htw ⊢
    rw [parseYearFrag_pos a _ hx]
    simp only [htw]
    simp

theorem padYear_digits (y : Nat) (hy : y < 10000) :
    ∃ P : List Char, (padYear (y : Int)).toList = P ∧ P.length = 4 ∧
      (∀ c ∈ P, isDigitC c = true) ∧ natOfDigits P = y := by
  have hlen : (Nat.toDigits 10 y).length ≤ 4 := (Nat.length_toDigits_le_iff (by decide) (by decide)).2 hy
  have hdig : ∀ c ∈ Nat.toDigits 10 y, isDigitC c = true := fun c hc =>
    isDigitC_of_isDigit c (Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc)
  refine ⟨List.replicate (4 - (Nat.toDigits 10 y).length) '0' ++ Nat.toDigits 10 y, ?_, ?_, ?_, ?_⟩
  · unfold padYear natToString
    have hn : ¬ ((y : Int) < 0) := by omega
    simp only [Int.natAbs_natCast, hn, if_false, String.toList_append]
    rw [Nat.toString_eq_ofList_toDigits]
    simp only [String.length_ofList]
    split
    · simp [String.toList_append, String.toList_ofList]
    · rename_i h
      have : 4 - (Nat.toDigits 10 y).length = 0 := by omega
      simp [this, String.toList_ofList]
  · simp; omega
  · intro c hc
    simp only [List.mem_append, List.mem_replicate] at hc
    rcases hc with ⟨_, rfl⟩ | hc
    · decide
    · exact hdig c hc
  · rw [natOfDigits_eq, Nat.ofDigitChars_append, Nat.ofDigitChars_replicate_zero]
    simp

theorem dateParts?_ascii (L : List UInt8) (y mo d : Nat) (h : dateParts? L = some (y, mo, d)) :
    ∀ b ∈ L, b.toNat < 128 := by
  unfold dateParts? at h
  split at h
  · rename_i y1 y2 y3 y4 h1 m1 m2 h2 d1 d2
    split at h
    · rename_i hc
      simp only [isDB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩ := hc
      subst a5 a8
      intro b hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | decide
    · cases h
  · cases h

theorem dateParts?_parse (L : List UInt8) (y mo d : Nat) (h : dateParts? L = some (y, mo, d)) :
    parseDateTimeFor .xsd10 .date (String.ofList (L.map ch)) =
      some { year := some (y : Int), month := some mo, day := some d, tz := none } := by
  unfold dateParts? at h
  split at h
  · rename_i y1 y2 y3 y4 h1 m1 m2 h2 d1 d2
    split at h
    · rename_i hc
      simp only [isDB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩ := hc
      subst a5 a8
      dsimp only at h
      split at h
      · rename_i hv
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hy, hmo, hd⟩ := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
        -- character facts
        have c1 := ch_facts y1 (by omega)
        have c2 := ch_facts y2 (by omega)
        have c3 := ch_facts y3 (by omega)
        have c4 := ch_facts y4 (by omega)
        have c6 := ch_facts m1 (by omega)
        have c7 := ch_facts m2 (by omega)
        have c9 := ch_facts d1 (by omega)
        have c10 := ch_facts d2 (by omega)
        have hdash : ch 45 = '-' := rfl
        have hY : natOfDigits [ch y1, ch y2, ch y3, ch y4] = y := by
          rw [← hy]; simp [natOfDigits, List.foldl, c1.1, c2.1, c3.1, c4.1, dv]
        have hM : natOfDigits [ch m1, ch m2] = mo := by
          rw [← hmo]; simp [natOfDigits, List.foldl, c6.1, c7.1, dv]
        have hD : natOfDigits [ch d1, ch d2] = d := by
          rw [← hd]; simp [natOfDigits, List.foldl, c9.1, c10.1, dv]
        have hy4 : y < 10000 := by rw [← hy]; simp only [dv]; omega
        obtain ⟨P, hP, hPl, hPd, hPv⟩ := padYear_digits y hy4
        have hdig : ∀ c ∈ [ch y1, ch y2, ch y3, ch y4], isDigitC c = true := by
          intro c hc
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
          rcases hc with rfl | rfl | rfl | rfl <;> exact ch_digit _ (by omega) (by omega)
        unfold parseDateTimeFor dateLexicalForEdition
        simp only [List.map_cons, List.map_nil, String.toList_ofList, hdash]
        have hyf := yearFrag_of_digits [ch y1, ch y2, ch y3, ch y4]
          ['-', ch m1, ch m2, '-', ch d1, ch d2] hdig rfl rfl
        simp only [List.cons_append, List.nil_append] at hyf
        have hy1 : 1 ≤ y := by rw [← hy]; exact hv.1.1.1.1
        have hz : ((((y : Nat) : Int)) == 0) = false := by simp; omega
        have hneg : ¬ (((y : Nat) : Int) < 0) := by omega
        have he : (Edition.xsd10 == Edition.xsd11 || DTKind.date == DTKind.time || DTKind.date == DTKind.gMonth ||
            DTKind.date == DTKind.gMonthDay || DTKind.date == DTKind.gDay) = false := by decide
        rw [hy, hmo, hd] at hv
        simp only [hyf, hY, he, Bool.false_eq_true, if_false]
        simp only [Option.bind_eq_bind, Option.bind_some, hz, hneg, if_false, Bool.false_eq_true]
        unfold parseDateTimeLex
        simp only [String.toList_append, String.toList_ofList, hP]
        rw [yearFrag_of_digits P _ hPd hPl rfl, hPv]
        have dm1 := ch_digit m1 a6.1 a6.2
        have dm2 := ch_digit m2 a7.1 a7.2
        have dd1 := ch_digit d1 a9.1 a9.2
        have dd2 := ch_digit d2 a10.1 a10.2
        have hnv : ¬ (mo < 1 ∨ mo > 12 ∨ d < 1 ∨ d > daysInMonth (y : Int) mo) := by omega
        simp [fixedNat, takeExact, allDigitsL, dm1, dm2, dd1, dd2, hM, hD, parseTimezoneFrag]
        omega
      · cases h
    · cases h
  · cases h

/-! ## The order of two admitted dates -/

theorem timeOnTimeline_date (y : Int) (mo d : Nat) :
    timeOnTimeline { year := some y, month := some mo, day := some d, tz := none } =
      ⟨daysFromCivil y mo d * 86400, 0⟩ := by
  simp [timeOnTimeline, Dec.add, Dec.ofInt, Dec.zero, Dec.norm, Dec.normFuel]

theorem dateParts?_valid (L : List UInt8) (y mo d : Nat) (h : dateParts? L = some (y, mo, d)) :
    1 ≤ y ∧ y < 10000 ∧ 1 ≤ mo ∧ mo ≤ 12 ∧ 1 ≤ d ∧ d ≤ daysInMonth (y : Int) mo := by
  unfold dateParts? at h
  split at h
  · rename_i y1 y2 y3 y4 h1 m1 m2 h2 d1 d2
    split at h
    · rename_i hc
      simp only [isDB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      dsimp only at h
      split at h
      · rename_i hv
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨hy, hmo, hd⟩ := h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
        rw [hy, hmo, hd] at hv
        have hy4 : y < 10000 := by rw [← hy]; simp only [dv]; omega
        omega
      · cases h
    · cases h
  · cases h

theorem compare_days (y1 y2 : Nat) (mo1 mo2 d1 d2 : Nat)
    (h1 : 1 ≤ y1 ∧ y1 < 10000 ∧ 1 ≤ mo1 ∧ mo1 ≤ 12 ∧ 1 ≤ d1 ∧ d1 ≤ daysInMonth (y1 : Int) mo1)
    (h2 : 1 ≤ y2 ∧ y2 < 10000 ∧ 1 ≤ mo2 ∧ mo2 ≤ 12 ∧ 1 ≤ d2 ∧ d2 ≤ daysInMonth (y2 : Int) mo2) :
    Dec.cmp ⟨daysFromCivil y1 mo1 d1 * 86400, 0⟩ ⟨daysFromCivil y2 mo2 d2 * 86400, 0⟩ =
      compare (dateOrd (y1, mo1, d1)) (dateOrd (y2, mo2, d2)) := by
  have l1 := dim_le (y1 : Int) mo1
  have l2 := dim_le (y2 : Int) mo2
  simp only [Dec.cmp, dateOrd, Nat.max_self, Nat.sub_self, Int.pow_zero, Int.mul_one]
  rcases Nat.lt_trichotomy (y1 * 512 + mo1 * 32 + d1) (y2 * 512 + mo2 * 32 + d2) with hl | he | hg
  · have m := mono y1 y2 mo1 mo2 d1 d2 (by omega) (by omega) ⟨h1.2.2.1, h1.2.2.2.1⟩
      ⟨h2.2.2.1, h2.2.2.2.1⟩ h1.2.2.2.2 h2.2.2.2.2 (by omega)
    rw [Nat.compare_eq_lt.2 hl]
    exact Int.compare_eq_lt.2 (by omega)
  · have hy : y1 = y2 := by omega
    have hm : mo1 = mo2 := by omega
    have hd : d1 = d2 := by omega
    subst hy hm hd
    simp
  · have m := mono y2 y1 mo2 mo1 d2 d1 (by omega) (by omega) ⟨h2.2.2.1, h2.2.2.2.1⟩
      ⟨h1.2.2.1, h1.2.2.2.1⟩ h2.2.2.2.2 h1.2.2.2.2 (by omega)
    rw [Nat.compare_eq_gt.2 hg]
    exact Int.compare_eq_gt.2 (by omega)

theorem calendarOrder_admitted (L1 L2 : List UInt8) (p1 p2 : Nat × Nat × Nat)
    (h1 : dateParts? L1 = some p1) (h2 : dateParts? L2 = some p2) :
    Fn.Comparison.calendarOrder .date (String.ofList (L1.map ch)) (String.ofList (L2.map ch)) =
      some (compare (dateOrd p1) (dateOrd p2)) := by
  obtain ⟨y1, mo1, d1⟩ := p1
  obtain ⟨y2, mo2, d2⟩ := p2
  unfold Fn.Comparison.calendarOrder
  rw [dateParts?_parse L1 y1 mo1 d1 h1, dateParts?_parse L2 y2 mo2 d2 h2]
  simp only [Option.bind_eq_bind, Option.bind_some, dtCompare, timeOnTimeline_date]
  rw [compare_days y1 y2 mo1 mo2 d1 d2 (dateParts?_valid L1 _ _ _ h1) (dateParts?_valid L2 _ _ _ h2)]

/-! ## The constant, the key and the decoded term -/

theorem bytesOfString_inj (s t : String)
    (h : L4Factoidal.Storage.bytesOfString s = L4Factoidal.Storage.bytesOfString t) : s = t := by
  unfold L4Factoidal.Storage.bytesOfString at h
  rw [L4Factoidal.Storage.byteArray_toList_eq, L4Factoidal.Storage.byteArray_toList_eq,
    String.toUTF8_eq_toByteArray, String.toUTF8_eq_toByteArray] at h
  apply String.toByteArray_inj.1
  apply ByteArray.ext
  exact Array.toList_inj.1 h

/-- The lexical form of an admitted string is the characters of its bytes. -/
theorem lex_of_dateParts (s : String) (p : Nat × Nat × Nat)
    (h : dateParts? (L4Factoidal.Storage.bytesOfString s) = some p) :
    s = String.ofList ((L4Factoidal.Storage.bytesOfString s).map ch) := by
  obtain ⟨y, mo, d⟩ := p
  apply bytesOfString_inj
  rw [ascii_bytes _ (dateParts?_ascii _ y mo d h)]

theorem dateConst?_spec (c : WfLiteral) (pre : ByteArray) (kc : Nat)
    (h : dateConst? c = some (pre, kc)) :
    c.val.langTag = none ∧ c.val.direction = none ∧
      XSD.builtinOfIri? c.val.datatype.val = some .date ∧ (c.val.datatype == xsdString) = false ∧
      noZero (L4Factoidal.Storage.bytesOfString c.val.datatype.val) = true ∧ pre = datePre c ∧
      ∃ p, dateParts? (L4Factoidal.Storage.bytesOfString c.val.lexicalForm) = some p ∧ kc = dateOrd p := by
  unfold dateConst? at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, beq_iff_eq, bne_iff_ne, ne_eq] at hc
    obtain ⟨⟨⟨⟨hl, hd⟩, hb⟩, hs⟩, hz⟩ := hc
    cases hp : dateParts? (L4Factoidal.Storage.bytesOfString c.val.lexicalForm) with
    | none => rw [hp] at h; cases h
    | some p =>
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      exact ⟨hl, hd, hb, beq_false_of_ne hs, hz, h.1.symm, p, rfl, h.2.symm⟩
  · cases h

theorem dateCmpKey?_some (op : Fn.Comparison.Op) (swap : Bool) (pre : ByteArray) (kc : Nat)
    (buf : ByteArray) (a e : Nat) (r : Bool) (h : dateCmpKey? op swap pre kc buf a e = some r) :
    ∃ L p, sliceList buf a e = pre.data.toList ++ L ∧ dateParts? L = some p ∧
      r = op.apply (if swap then compare kc (dateOrd p) else compare (dateOrd p) kc) := by
  unfold dateCmpKey? at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hok, hlen⟩, hpre⟩ := hc
    have hpre' : buf.extract a (a + pre.size) = pre :=
      ByteArray.ext (eq_of_beq (show ((buf.extract a (a + pre.size)).data == pre.data) = true from hpre))
    split at h
    · rename_i p hp
      simp only [Option.some.injEq] at h
      refine ⟨sliceList buf (a + pre.size) e, p, ?_, hp, h.symm⟩
      have hsplit : buf.extract a (a + pre.size) ++ buf.extract (a + pre.size) e = buf.extract a e := by
        rw [ByteArray.extract_append_extract]
        congr 1 <;> omega
      unfold sliceList
      rw [← hsplit, hpre']
      simp
    · cases h
  · cases h

/-- The literal of the datatype `dt` whose lexical form is the characters of `L`. -/
def admLit (dt : WfIri) (L : List UInt8) : Literal :=
  { lexicalForm := String.ofList (L.map ch), datatype := dt, langTag := none, direction := none }

/-- The term of an admitted key: the literal of the constant's datatype whose
    lexical form is the characters of the ten bytes. -/
theorem decode_admitted (c : WfLiteral) (pre : ByteArray) (kc : Nat)
    (hc : dateConst? c = some (pre, kc)) (L : List UInt8) (p : Nat × Nat × Nat)
    (hL : dateParts? L = some p) (buf : ByteArray) (a e : Nat)
    (hs : sliceList buf a e = pre.data.toList ++ L) (t : Term)
    (hdec : decodeKey? (sliceList buf a e) = some t) :
    ∃ hwf, t = .literal ⟨admLit c.val.datatype L, hwf⟩ := by
  obtain ⟨hl, hd, _, hs', hz, hpre, _⟩ := dateConst?_spec c pre kc hc
  obtain ⟨⟨clex, cdt, ctag, cdir⟩, cwf⟩ := c
  simp only at hl hd hs' hz hpre ⊢
  subst hl hd
  have hwf : literalWf (admLit cdt L) = true := cwf
  refine ⟨hwf, ?_⟩
  obtain ⟨y, mo, d⟩ := p
  have hb := ascii_bytes L (dateParts?_ascii L y mo d hL)
  have hlk : literalKey? (admLit cdt L) = some (sliceList buf a e) := by
    simp only [admLit, literalKey?, hs', hz, hb, Bool.false_eq_true, if_false, if_true]
    rw [hs, hpre]
    simp [datePre]
  have h2 := decodeKey?_termKey? (.literal ⟨admLit cdt L, hwf⟩) _ hlk
  rw [h2] at hdec
  exact (Option.some.inj hdec).symm

/-! ## The answer is the XSD value-space comparison -/

theorem literalCompare_admitted (dt : WfIri) (hb : XSD.builtinOfIri? dt.val = some .date)
    (L1 L2 : List UInt8) (p1 p2 : Nat × Nat × Nat)
    (h1 : dateParts? L1 = some p1) (h2 : dateParts? L2 = some p2) (op : Fn.Comparison.Op) :
    Fn.Comparison.literalCompare (admLit dt L1) (admLit dt L2) op =
      some (op.apply (compare (dateOrd p1) (dateOrd p2))) := by
  unfold Fn.Comparison.literalCompare
  simp only [admLit, hb, Option.bind_eq_bind, Option.bind_some]
  have hn : Fn.Comparison.numericType XSD.Builtin.date = false := by decide
  simp only [hn, Bool.false_and, Bool.false_eq_true, if_false]
  rw [calendarOrder_admitted L1 L2 p1 p2 h1 h2]
  rfl

/-- When `dateCmpKey?` decides a key that `decodeKey?` reads as `t`, its
    answer is `Fn.Comparison.termCompare` of `t` and the constant (in the
    order of the expression). -/
theorem dateCmpKey_termCompare (op : Fn.Comparison.Op) (swap : Bool) (c : WfLiteral)
    (pre : ByteArray) (kc : Nat) (hc : dateConst? c = some (pre, kc))
    (buf : ByteArray) (a e : Nat) (t : Term) (hdec : decodeKey? (sliceList buf a e) = some t)
    (r : Bool) (hr : dateCmpKey? op swap pre kc buf a e = some r) :
    (if swap then Fn.Comparison.termCompare (.literal c) t op
     else Fn.Comparison.termCompare t (.literal c) op) = some r := by
  obtain ⟨L, p, hs, hL, hrr⟩ := dateCmpKey?_some op swap pre kc buf a e r hr
  obtain ⟨hwf, rfl⟩ := decode_admitted c pre kc hc L p hL buf a e hs t hdec
  obtain ⟨hl, hd, hb, _, _, _, pc, hpc, hkc⟩ := dateConst?_spec c pre kc hc
  have hlex := lex_of_dateParts _ pc hpc
  obtain ⟨⟨clex, cdt, ctag, cdir⟩, cwf⟩ := c
  simp only at hl hd hb hpc hlex hkc ⊢
  subst hl hd hkc hrr
  have hcl : ({ lexicalForm := clex, datatype := cdt, langTag := none, direction := none } : Literal) =
      admLit cdt (L4Factoidal.Storage.bytesOfString clex) := by
    simp only [admLit]; rw [← hlex]
  cases swap
  · simp only [Fn.Comparison.termCompare, Bool.false_eq_true, if_false]
    rw [hcl]
    exact literalCompare_admitted cdt hb L _ p pc hL hpc op
  · simp only [Fn.Comparison.termCompare, if_true]
    rw [hcl]
    exact literalCompare_admitted cdt hb _ L pc p hpc hL op

#print axioms mono
#print axioms dateParts?_parse
#print axioms calendarOrder_admitted
#print axioms dateCmpKey_termCompare

end L4Factoidal.Storage.Sbm11.DateKey
