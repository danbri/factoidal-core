/-
L4Factoidal.Qlvr.MergeTheorems — the merge join's row pairs (lemma L5a, the
index part, of `docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md`;
https://github.com/danbri/factoidal/issues/776).

`Qlvr.mergeJoin` (used by `l4qlvr` and by the SBM11 id path) computes two
arrays of row indices with `mergeGo` and builds its output table from them
(`joinOutput`). This module proves what the indices are.

* `mergeSpec`: every pair `(x, y)` of a left row and a right row whose
  join-column values are equal and that `ok` accepts, in the order of `x`,
  then `y`.
* `mergeGo_spec`: for join columns in non-decreasing order on both sides,
  the merge loop appends exactly `mergeSpec` (the left indices and the
  right indices).
* `mergeGo_pairs`, `mergeJoin_eq`: the index arrays `mergeJoin` builds its
  output from zip to `mergeSpec` of its join columns and its test of the
  other shared columns.

Not proved here: that a row pair of the id tables is a compatible pair of
solutions exactly when the shared columns are equal (needs the denotation of
a `Table` as solutions), and so that the join output equals the reference
join.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Qlvr.Bgp

namespace L4Factoidal.Qlvr

/-- The matching row pairs from left row `i` and right row `j` on. -/
def mergeSpec (A B : Nat → UInt64) (ok : Nat → Nat → Bool) (nl nr i j : Nat) : List (Nat × Nat) :=
  (List.range' i (nl - i)).flatMap fun x =>
    ((List.range' j (nr - j)).filter fun y => A x == B y && ok x y).map fun y => (x, y)

/-- The pairs of a block of rows `[x0, ie)` × `[j, je)` that `ok` accepts. -/
def blockSpec (ok : Nat → Nat → Bool) (x0 ie j je : Nat) : List (Nat × Nat) :=
  (List.range' x0 (ie - x0)).flatMap fun x => ((List.range' j (je - j)).filter (ok x)).map fun y => (x, y)

/-! ## List lemmas -/

theorem flatMap_congr' {α β : Type} (xs : List α) (f g : α → List β) (h : ∀ x ∈ xs, f x = g x) :
    xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem flatMap_nil' {α β : Type} (xs : List α) (f : α → List β) (h : ∀ x ∈ xs, f x = []) :
    xs.flatMap f = [] := by
  rw [flatMap_congr' xs f (fun _ => []) h]
  simp

theorem range'_split (s n m : Nat) (h : m ≤ n) : List.range' s n = List.range' s m ++ List.range' (s + m) (n - m) := by
  have := @List.range'_append_1 s m (n - m)
  rw [Nat.add_sub_cancel' h] at this
  exact this.symm

/-! ## The loops -/

theorem runEnd_spec (A : Nat → UInt64) (n : Nat) (a : UInt64) : ∀ f e, n - e ≤ f →
    e ≤ runEnd A n a f e ∧ (runEnd A n a f e ≤ max e n) ∧
    (∀ x, e ≤ x → x < runEnd A n a f e → A x = a) ∧
    (runEnd A n a f e < n → A (runEnd A n a f e) ≠ a) := by
  intro f
  induction f with
  | zero =>
    intro e he
    simp only [runEnd]
    refine ⟨Nat.le_refl _, by omega, fun x h1 h2 => absurd h2 (by omega), fun h => absurd h (by omega)⟩
  | succ f ih =>
    intro e he
    simp only [runEnd]
    by_cases hc : (e < n && A e == a) = true
    · rw [if_pos hc]
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
      obtain ⟨h1, h2, h3, h4⟩ := ih (e + 1) (by omega)
      refine ⟨by omega, by omega, fun x hx1 hx2 => ?_, h4⟩
      by_cases hx : x = e
      · subst hx; exact hc.2
      · exact h3 x (by omega) hx2
    · rw [if_neg hc]
      refine ⟨Nat.le_refl _, by omega, fun x h1 h2 => absurd h2 (by omega), fun h => ?_⟩
      intro he'
      apply hc
      simp [h, he']

theorem pairsRow_spec (ok : Nat → Nat → Bool) (x je : Nat) : ∀ f y (li ri : Array Nat), je - y ≤ f →
    (pairsRow ok x je f y li ri).1.toList = li.toList ++ (((List.range' y (je - y)).filter (ok x)).map fun y => (x, y)).map Prod.fst ∧
    (pairsRow ok x je f y li ri).2.toList = ri.toList ++ (((List.range' y (je - y)).filter (ok x)).map fun y => (x, y)).map Prod.snd := by
  intro f
  induction f with
  | zero =>
    intro y li ri hf
    have : je - y = 0 := by omega
    simp [pairsRow, this]
  | succ f ih =>
    intro y li ri hf
    simp only [pairsRow]
    by_cases hy : y < je
    · rw [if_pos hy]
      have hr : List.range' y (je - y) = y :: List.range' (y + 1) (je - (y + 1)) := by
        rw [show je - y = (je - (y + 1)) + 1 by omega, List.range'_succ]
      rw [hr]
      by_cases hok : ok x y = true
      · rw [if_pos hok]
        obtain ⟨h1, h2⟩ := ih (y + 1) (li.push x) (ri.push y) (by omega)
        rw [h1, h2]
        simp [hok]
      · rw [if_neg hok]
        obtain ⟨h1, h2⟩ := ih (y + 1) li ri (by omega)
        rw [h1, h2]
        simp [hok]
    · rw [if_neg hy]
      have : je - y = 0 := by omega
      simp [this]

theorem pairsBlock_spec (ok : Nat → Nat → Bool) (ie j je : Nat) : ∀ f x (li ri : Array Nat), ie - x ≤ f →
    (pairsBlock ok ie j je f x li ri).1.toList = li.toList ++ (blockSpec ok x ie j je).map Prod.fst ∧
    (pairsBlock ok ie j je f x li ri).2.toList = ri.toList ++ (blockSpec ok x ie j je).map Prod.snd := by
  intro f
  induction f with
  | zero =>
    intro x li ri hf
    have : ie - x = 0 := by omega
    simp [pairsBlock, blockSpec, this]
  | succ f ih =>
    intro x li ri hf
    simp only [pairsBlock]
    by_cases hx : x < ie
    · rw [if_pos hx]
      obtain ⟨r1, r2⟩ := pairsRow_spec ok x je (je - j) j li ri (Nat.le_refl _)
      obtain ⟨h1, h2⟩ := ih (x + 1) (pairsRow ok x je (je - j) j li ri).1 (pairsRow ok x je (je - j) j li ri).2
        (by omega)
      rw [h1, h2, r1, r2]
      have hr : List.range' x (ie - x) = x :: List.range' (x + 1) (ie - (x + 1)) := by
        rw [show ie - x = (ie - (x + 1)) + 1 by omega, List.range'_succ]
      simp only [blockSpec, hr, List.flatMap_cons, List.map_append, List.append_assoc]
      exact ⟨trivial, trivial⟩
    · rw [if_neg hx]
      have : ie - x = 0 := by omega
      simp [blockSpec, this]

/-! ## The merge loop -/

/-- For join columns in non-decreasing order, the merge loop appends exactly
    the matching pairs from row `i` and row `j` on. -/
theorem mergeGo_spec (A B : Nat → UInt64) (ok : Nat → Nat → Bool) (nl nr : Nat)
    (hA : ∀ x y, x ≤ y → y < nl → (A x).toNat ≤ (A y).toNat)
    (hB : ∀ x y, x ≤ y → y < nr → (B x).toNat ≤ (B y).toNat) :
    ∀ f i j (li ri : Array Nat), (nl - i) + (nr - j) < f →
      (mergeGo A B ok nl nr f i j li ri).1.toList = li.toList ++ (mergeSpec A B ok nl nr i j).map Prod.fst ∧
      (mergeGo A B ok nl nr f i j li ri).2.toList = ri.toList ++ (mergeSpec A B ok nl nr i j).map Prod.snd := by
  have beq_iff : ∀ a b : UInt64, (a == b) = true ↔ a.toNat = b.toNat := by
    intro a b; rw [beq_iff_eq]; exact UInt64.toNat_inj.symm
  intro f
  induction f with
  | zero => intro i j li ri hf; omega
  | succ f ih =>
    intro i j li ri hf
    simp only [mergeGo]
    by_cases hstop : (i ≥ nl || j ≥ nr) = true
    · rw [if_pos hstop]
      simp only [Bool.or_eq_true, decide_eq_true_eq] at hstop
      have hnil : mergeSpec A B ok nl nr i j = [] := by
        unfold mergeSpec
        rcases hstop with h | h
        · rw [show nl - i = 0 by omega]; rfl
        · apply flatMap_nil'
          intro x _
          rw [show nr - j = 0 by omega]; rfl
      simp [hnil]
    · rw [if_neg hstop]
      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Nat.not_le] at hstop
      obtain ⟨hi, hj⟩ := hstop
      by_cases hab : A i < B j
      · rw [if_pos hab]
        rw [UInt64.lt_iff_toNat_lt] at hab
        obtain ⟨k1, k2⟩ := ih (i + 1) j li ri (by omega)
        rw [k1, k2]
        -- row i has no match
        have : mergeSpec A B ok nl nr i j = mergeSpec A B ok nl nr (i + 1) j := by
          unfold mergeSpec
          rw [show nl - i = (nl - (i + 1)) + 1 by omega, List.range'_succ, List.flatMap_cons]
          have hz : ((List.range' j (nr - j)).filter fun y => A i == B y && ok i y) = [] := by
            apply List.filter_eq_nil_iff.mpr
            intro y hy
            rw [List.mem_range'_1] at hy
            have := hB j y hy.1 (by omega)
            simp only [Bool.and_eq_true, not_and]
            intro he; rw [beq_iff] at he; omega
          rw [hz]; rfl
        rw [this]; exact ⟨rfl, rfl⟩
      · rw [if_neg hab]
        rw [UInt64.lt_iff_toNat_lt] at hab
        by_cases hba : B j < A i
        · rw [if_pos hba]
          rw [UInt64.lt_iff_toNat_lt] at hba
          obtain ⟨k1, k2⟩ := ih i (j + 1) li ri (by omega)
          rw [k1, k2]
          -- column j has no match
          have : mergeSpec A B ok nl nr i j = mergeSpec A B ok nl nr i (j + 1) := by
            unfold mergeSpec
            apply flatMap_congr'
            intro x hx
            rw [List.mem_range'_1] at hx
            rw [show nr - j = (nr - (j + 1)) + 1 by omega, List.range'_succ, List.filter_cons]
            have := hA i x hx.1 (by omega)
            have hne : (A x == B j && ok x j) = false := by
              cases h : (A x == B j) with
              | false => rfl
              | true => rw [beq_iff] at h; omega
            rw [hne]; rfl
          rw [this]; exact ⟨rfl, rfl⟩
        · rw [if_neg hba]
          rw [UInt64.lt_iff_toNat_lt] at hba
          have heq : (A i).toNat = (B j).toNat := by omega
          -- the runs
          obtain ⟨e1, e2, e3, e4⟩ := runEnd_spec A nl (A i) nl (i + 1) (by omega)
          obtain ⟨g1, g2, g3, g4⟩ := runEnd_spec B nr (A i) nr (j + 1) (by omega)
          generalize hie : runEnd A nl (A i) nl (i + 1) = ie at *
          generalize hje : runEnd B nr (A i) nr (j + 1) = je at *
          have hrunA : ∀ x, i ≤ x → x < ie → (A x).toNat = (A i).toNat := by
            intro x h1 h2
            by_cases hx : x = i
            · rw [hx]
            · rw [e3 x (by omega) h2]
          have hrunB : ∀ y, j ≤ y → y < je → (B y).toNat = (A i).toNat := by
            intro y h1 h2
            by_cases hy : y = j
            · rw [hy, heq]
            · rw [g3 y (by omega) h2]
          have hafterA : ∀ x, ie ≤ x → x < nl → (A i).toNat < (A x).toNat := by
            intro x h1 h2
            have hne := e4 (by omega)
            have h3 := hA i ie (by omega) (by omega)
            have h4 := hA ie x h1 h2
            have : (A ie).toNat ≠ (A i).toNat := fun h => hne (UInt64.toNat_inj.mp h)
            omega
          have hafterB : ∀ y, je ≤ y → y < nr → (A i).toNat < (B y).toNat := by
            intro y h1 h2
            have hne := g4 (by omega)
            have h3 := hB j je (by omega) (by omega)
            have h4 := hB je y h1 h2
            have : (B je).toNat ≠ (A i).toNat := fun h => hne (UInt64.toNat_inj.mp h)
            omega
          have hie : ie ≤ nl := by omega
          have hje : je ≤ nr := by omega
          obtain ⟨b1, b2⟩ := pairsBlock_spec ok ie j je (ie - i) i li ri (Nat.le_refl _)
          obtain ⟨k1, k2⟩ := ih ie je (pairsBlock ok ie j je (ie - i) i li ri).1
            (pairsBlock ok ie j je (ie - i) i li ri).2 (by omega)
          rw [k1, k2, b1, b2]
          -- the spec splits into the block and the rest
          have hsplit : mergeSpec A B ok nl nr i j = blockSpec ok i ie j je ++ mergeSpec A B ok nl nr ie je := by
            unfold mergeSpec blockSpec
            rw [range'_split i (nl - i) (ie - i) (by omega), List.flatMap_append,
              show i + (ie - i) = ie by omega, show nl - i - (ie - i) = nl - ie by omega]
            congr 1
            · apply flatMap_congr'
              intro x hx
              rw [List.mem_range'_1] at hx
              rw [range'_split j (nr - j) (je - j) (by omega), List.filter_append,
                show j + (je - j) = je by omega, show nr - j - (je - j) = nr - je by omega]
              have hz : ((List.range' je (nr - je)).filter fun y => A x == B y && ok x y) = [] := by
                apply List.filter_eq_nil_iff.mpr
                intro y hy
                rw [List.mem_range'_1] at hy
                have := hafterB y hy.1 (by omega)
                have := hrunA x hx.1 (by omega)
                simp only [Bool.and_eq_true, not_and]
                intro he; rw [beq_iff] at he; omega
              rw [hz, List.append_nil]
              congr 1
              apply List.filter_congr
              intro y hy
              rw [List.mem_range'_1] at hy
              have h1 := hrunA x hx.1 (by omega)
              have h2 := hrunB y hy.1 (by omega)
              have : (A x == B y) = true := by rw [beq_iff]; omega
              simp [this]
            · apply flatMap_congr'
              intro x hx
              rw [List.mem_range'_1] at hx
              rw [range'_split j (nr - j) (je - j) (by omega), List.filter_append,
                show j + (je - j) = je by omega, show nr - j - (je - j) = nr - je by omega]
              have hz : ((List.range' j (je - j)).filter fun y => A x == B y && ok x y) = [] := by
                apply List.filter_eq_nil_iff.mpr
                intro y hy
                rw [List.mem_range'_1] at hy
                have := hafterA x hx.1 (by omega)
                have := hrunB y hy.1 (by omega)
                simp only [Bool.and_eq_true, not_and]
                intro he; rw [beq_iff] at he; omega
              rw [hz, List.nil_append]
          rw [hsplit]
          simp

/-- The index arrays of `mergeJoin`: for join columns in non-decreasing
    order on both sides, they zip to every pair of rows whose join values
    are equal and whose other shared columns agree, in the order of the left
    row, then the right row. -/
theorem mergeGo_pairs (A B : Nat → UInt64) (ok : Nat → Nat → Bool) (nl nr : Nat)
    (hA : ∀ x y, x ≤ y → y < nl → (A x).toNat ≤ (A y).toNat)
    (hB : ∀ x y, x ≤ y → y < nr → (B x).toNat ≤ (B y).toNat) :
    (mergeGo A B ok nl nr (nl + nr + 1) 0 0 #[] #[]).1.toList.zip
        (mergeGo A B ok nl nr (nl + nr + 1) 0 0 #[] #[]).2.toList =
      mergeSpec A B ok nl nr 0 0 := by
  obtain ⟨h1, h2⟩ := mergeGo_spec A B ok nl nr hA hB (nl + nr + 1) 0 0 #[] #[] (by omega)
  rw [h1, h2]
  simp only [List.nil_append]
  rw [← List.unzip_fst, ← List.unzip_snd, List.zip_unzip]

/-- `mergeJoin` builds its output from the index arrays of `mergeGo`. -/
theorem mergeJoin_eq (l r : Table) (v : String) :
    mergeJoin l r v =
      joinOutput l r (joinVars l r).1 (joinVars l r).2
        (mergeGo (l.at ((l.idx v).getD 0)) (r.at ((r.idx v).getD 0))
          (fun x y => ((sharedCols l r).filter fun (a, _) => a != (l.idx v).getD 0).all
            (fun (p, q) => l.at p x == r.at q y))
          l.rows r.rows (l.rows + r.rows + 1) 0 0 #[] #[]).1
        (mergeGo (l.at ((l.idx v).getD 0)) (r.at ((r.idx v).getD 0))
          (fun x y => ((sharedCols l r).filter fun (a, _) => a != (l.idx v).getD 0).all
            (fun (p, q) => l.at p x == r.at q y))
          l.rows r.rows (l.rows + r.rows + 1) 0 0 #[] #[]).2 (some v) := rfl

/-! ## `mergeJoin` before the refactor, compared on samples

`mergeJoin` was one `for` loop with nested `for` loops and `break` until
2026-10-12; it is now `mergeGo` with `runEnd`, `pairsRow` and `pairsBlock`,
tail calls with fuel that take the same steps. -/

private def mergeJoinOld (l r : Table) (v : String) : Table := _root_.Id.run do
  let (vars, extra) := joinVars l r
  let shared := sharedCols l r
  let lc := (l.idx v).getD 0
  let rc := (r.idx v).getD 0
  let others := shared.filter fun (a, _) => a != lc
  let mut li : Array Nat := #[]
  let mut ri : Array Nat := #[]
  let mut i := 0
  let mut j := 0
  for _ in [0:l.rows + r.rows + 1] do
    if i ≥ l.rows || j ≥ r.rows then break
    let a := l.at lc i
    let b := r.at rc j
    if a < b then i := i + 1
    else if b < a then j := j + 1
    else
      let mut ie := i + 1
      for _ in [0:l.rows] do
        if ie < l.rows && l.at lc ie == a then ie := ie + 1 else break
      let mut je := j + 1
      for _ in [0:r.rows] do
        if je < r.rows && r.at rc je == a then je := je + 1 else break
      for x in [i:ie] do
        for y in [j:je] do
          if others.all (fun (p, q) => l.at p x == r.at q y) then
            li := li.push x
            ri := ri.push y
      i := ie
      j := je
  return joinOutput l r vars extra li ri (some v)

private def col (xs : List Nat) : ByteArray := xs.foldl (fun b x => Side.put64 b x.toUInt64) ByteArray.empty

private def tab (vars : Array String) (cs : List (List Nat)) : Table :=
  { vars, cols := (cs.map col).toArray, rows := (cs.headD []).length }

private def sameTable (a b : Table) : Bool :=
  a.vars == b.vars && a.rows == b.rows && a.cols.size == b.cols.size &&
    (List.range a.cols.size).all fun k => a.cols[k]!.data == b.cols[k]!.data

private def lefts : List Table :=
  [tab #["a", "b"] [[1, 1, 2, 3, 3, 3, 7], [5, 6, 5, 1, 2, 3, 9]],
   tab #["a", "b"] [[], []],
   tab #["a"] [[2, 2, 2]],
   tab #["a", "b"] [[0, 4, 4, 9], [1, 1, 2, 2]]]

private def rights : List Table :=
  [tab #["a", "c"] [[1, 3, 3, 4, 7, 7], [10, 11, 12, 13, 14, 15]],
   tab #["a", "b"] [[1, 2, 3, 3, 4], [5, 5, 2, 3, 1]],
   tab #["a"] [[2, 2]],
   tab #["c", "a"] [[8, 9], [4, 9]]]

#guard lefts.all fun l => rights.all fun r => ["a", "b", "c"].all fun v =>
  sameTable (mergeJoin l r v) (mergeJoinOld l r v)

end L4Factoidal.Qlvr
