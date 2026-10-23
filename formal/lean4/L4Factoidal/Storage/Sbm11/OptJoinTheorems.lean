/-
L4Factoidal.Storage.Sbm11.OptJoinTheorems — the left outer join of the SBM11
id path (OPTIONAL, https://github.com/danbri/factoidal/issues/775; lemma L5g
of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

## Over row indices

* `ljSpec nl nr cand`: for each left row `i < nl` in order, the right rows
  `j < nr` with `cand i j` in order as `(i, some j)`, or `(i, none)` when
  there is none. `innerSpec` is the same without the `none` rows.
* `outerPairs_eq`: `OptJoin.outerPairs` turns the index arrays of
  `innerSpec` into those of `ljSpec`.
* `outerPairs_merge`: with the index arrays of `Qlvr.mergeGo` (join columns
  in non-decreasing order on both sides, the condition of
  `OptJoin.innerPairs`), `outerPairs` gives `ljSpec` with `cand x y = (A x
  == B y && ok x y)`.
* (a) `ljSpec_left_row`: every left row is in the output.
  (b) `ljSpec_mem`: an output row is `(i, some j)` with `cand i j`, or
  `(i, none)` with no `j` such that `cand i j`; `ljSpec_complete`: every
  `(i, j)` with `cand i j` is in the output.
  (c) `ljSpec_count_row`: left row `i` occurs `max 1 c` times, `c` the
  number of its candidates; `ljSpec_length`: the sum of those.

## Over rows of ids, against SPARQL 1.1 section 18.5

* `IdRow`: a solution mapping over ids (variable, id), unbound variables
  absent. `idLeftJoin`: LeftJoin(Ω1, Ω2, true) with compatibility by id
  equality.
* `leftJoin_decode`: decoding the ids of `idLeftJoin L R` gives exactly
  `SPARQL.leftJoin` of the decoded `L` and `R` with condition `true`, as a
  list (same rows, same order), when `Term.eqb` of two decoded ids is id
  equality on the ids of `L` and `R` (`TermIdTheorems.toId?_eq_iff` gives
  term identity; `Term.eqb` also identifies two `rdf:XMLLiteral` forms with
  the same exclusive canonical form, so the hypothesis excludes such pairs).
* `idLeftJoin_eq_ljSpec`: `idLeftJoin` is `ljSpec` with `cand i j` the id
  compatibility of left row `i` and right row `j`, each pair mapped to the
  merged row (or the left row).
* `outerPairs_leftJoin`: the three steps together, from the index arrays
  of `outerPairs` to SPARQL 1.1 LeftJoin of the decoded rows.
* `leftJoin_filter_right`: `LeftJoin(Ω1, Ω2, c) = LeftJoin(Ω1, Filter(c2,
  Ω2), true)` when `c` on a compatible merge is `c2` on the right row: the
  id path applies an OPTIONAL group's FILTER to the group's rows before the
  join (the FILTER reads only the group's variables), which is also what the
  reference evaluator computes for `OPTIONAL { P FILTER(e) }`.

The `Table` step (lemma L5g″): the `Table` `OptJoin.leftOuterJoin` builds
(`gather`, `gatherOpt` over `ByteArray` columns) denotes the rows
`idLeftJoin` gives, and the hash path (`OptJoin.hashPairs`, `Std.HashMap`)
computes `innerSpec`: `TableOuterTheorems.leftOuterJoin_rows` and
`hashPairs_spec`. Also tested: the `#guard`s below on sample tables, and
`tests/sbm11/run.sh` part (d) against the reference engine.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.OptJoin
import L4Factoidal.Qlvr.MergeTheorems
import L4Factoidal.SPARQL.Algebra

namespace L4Factoidal.Storage.Sbm11.OptJoin

open L4Factoidal.Qlvr (Table mergeGo mergeSpec mergeGo_spec)

/-! ## List lemmas -/

theorem filterMap_congr' {α β : Type} (f g : α → Option β) :
    ∀ (xs : List α), (∀ x ∈ xs, f x = g x) → xs.filterMap f = xs.filterMap g := by
  intro xs
  induction xs with
  | nil => intro _; rfl
  | cons a rest ih =>
    intro h
    simp only [List.filterMap_cons]
    rw [h a (by simp), ih (fun y hy => h y (by simp [hy]))]

/-! ## The specification over row indices -/

/-- The right rows that left row `i` accepts. -/
def rowsOf (nr : Nat) (cand : Nat → Nat → Bool) (i : Nat) : List Nat :=
  (List.range nr).filter (cand i)

/-- The output rows of left row `i` with the right rows `js`. -/
def ljRow (i : Nat) (js : List Nat) : List (Nat × Option Nat) :=
  if js.isEmpty then [(i, none)] else js.map fun j => (i, some j)

/-- The inner pairs from left row `i` on. -/
def innerFrom (nl nr : Nat) (cand : Nat → Nat → Bool) (i : Nat) : List (Nat × Nat) :=
  (List.range' i (nl - i)).flatMap fun x => (rowsOf nr cand x).map fun j => (x, j)

/-- The left outer join's rows from left row `i` on. -/
def ljFrom (nl nr : Nat) (cand : Nat → Nat → Bool) (i : Nat) : List (Nat × Option Nat) :=
  (List.range' i (nl - i)).flatMap fun x => ljRow x (rowsOf nr cand x)

/-- Every pair `(i, j)` with `cand i j`, in the order of `i`, then `j`. -/
def innerSpec (nl nr : Nat) (cand : Nat → Nat → Bool) : List (Nat × Nat) :=
  innerFrom nl nr cand 0

/-- The left outer join over row indices. -/
def ljSpec (nl nr : Nat) (cand : Nat → Nat → Bool) : List (Nat × Option Nat) :=
  ljFrom nl nr cand 0

theorem range'_cons_of_lt {i nl : Nat} (h : i < nl) :
    List.range' i (nl - i) = i :: List.range' (i + 1) (nl - (i + 1)) := by
  have e : nl - i = (nl - (i + 1)) + 1 := by omega
  rw [e, List.range'_succ]

theorem innerFrom_cons {nl nr : Nat} {cand : Nat → Nat → Bool} {i : Nat} (h : i < nl) :
    innerFrom nl nr cand i = (rowsOf nr cand i).map (fun j => (i, j)) ++ innerFrom nl nr cand (i + 1) := by
  unfold innerFrom
  rw [range'_cons_of_lt h, List.flatMap_cons]

theorem ljFrom_cons {nl nr : Nat} {cand : Nat → Nat → Bool} {i : Nat} (h : i < nl) :
    ljFrom nl nr cand i = ljRow i (rowsOf nr cand i) ++ ljFrom nl nr cand (i + 1) := by
  unfold ljFrom
  rw [range'_cons_of_lt h, List.flatMap_cons]

theorem innerFrom_ge {nl nr : Nat} {cand : Nat → Nat → Bool} {i : Nat} (h : nl ≤ i) :
    innerFrom nl nr cand i = [] := by
  unfold innerFrom
  rw [show nl - i = 0 by omega]
  rfl

theorem ljFrom_ge {nl nr : Nat} {cand : Nat → Nat → Bool} {i : Nat} (h : nl ≤ i) :
    ljFrom nl nr cand i = [] := by
  unfold ljFrom
  rw [show nl - i = 0 by omega]
  rfl

/-- Every left index of `innerFrom ... i` is at least `i`. -/
theorem innerFrom_fst_ge {nl nr : Nat} {cand : Nat → Nat → Bool} {i : Nat} :
    ∀ x ∈ (innerFrom nl nr cand i).map Prod.fst, i ≤ x := by
  intro x hx
  simp only [innerFrom, List.map_flatMap, List.mem_flatMap, List.map_map, List.mem_range'] at hx
  obtain ⟨y, ⟨k, hk, rfl⟩, hm⟩ := hx
  simp only [Function.comp_def, List.mem_map] at hm
  obtain ⟨_, _, rfl⟩ := hm
  omega

/-! ## `runPairs` and `outerGo` -/

theorem runPairs_spec (li ri : Array Nat) (i : Nat) :
    ∀ (js : List Nat) (f p : Nat) (oi : Array Nat) (oj : Array (Option Nat)),
      js.length ≤ f →
      (∀ k, k < js.length → li[p + k]? = some i ∧ ri[p + k]? = js[k]?) →
      li[p + js.length]? ≠ some i →
      (runPairs li ri i f p oi oj).1 = p + js.length ∧
      (runPairs li ri i f p oi oj).2.1.toList = oi.toList ++ js.map (fun _ => i) ∧
      (runPairs li ri i f p oi oj).2.2.toList = oj.toList ++ js.map some := by
  intro js
  induction js with
  | nil =>
    intro f p oi oj _ _ hend
    cases f with
    | zero => simp [runPairs]
    | succ f =>
      have hc : (p < li.size && li[p]! == i) = false := by
        by_cases hp : p < li.size
        · have h1 : li[p]? = some li[p] := by simp [hp]
          have h2 : li[p] ≠ i := by
            intro he
            apply hend
            simp only [List.length_nil, Nat.add_zero]
            rw [h1, he]
          simp [hp, h2]
        · simp [hp]
      simp [runPairs, hc]
  | cons j js ih =>
    intro f p oi oj hf hk hend
    cases f with
    | zero => simp at hf
    | succ f =>
      obtain ⟨hl0, hr0⟩ := hk 0 (by simp)
      simp only [Nat.add_zero] at hl0 hr0
      have hp : p < li.size := by
        rcases Nat.lt_or_ge p li.size with h | h
        · exact h
        · rw [getElem?_neg li p (by omega)] at hl0
          simp at hl0
      have hli : li[p] = i := by
        rw [getElem?_pos li p hp] at hl0
        simpa using hl0
      have hpr : p < ri.size := by
        rcases Nat.lt_or_ge p ri.size with h | h
        · exact h
        · rw [getElem?_neg ri p (by omega)] at hr0
          simp at hr0
      have hri : ri[p]! = j := by
        rw [getElem!_pos ri p hpr]
        rw [getElem?_pos ri p hpr] at hr0
        simpa using hr0
      have hc : (p < li.size && li[p]! == i) = true := by
        simp [hp, hli]
      simp only [runPairs, hc, if_true, hri]
      have ih' := ih f (p + 1) (oi.push i) (oj.push (some j)) (by simp at hf; omega)
        (fun k hk' => by
          have := hk (k + 1) (by simp; omega)
          rw [show p + 1 + k = p + (k + 1) by omega]
          simpa using this)
        (by
          rw [show p + 1 + js.length = p + (j :: js).length by simp; omega]
          exact hend)
      obtain ⟨e1, e2, e3⟩ := ih'
      refine ⟨by rw [e1]; simp; omega, ?_, ?_⟩
      · rw [e2]; simp
      · rw [e3]; simp

theorem outerGo_spec (nl nr : Nat) (cand : Nat → Nat → Bool) (li ri : Array Nat) :
    ∀ (f i p : Nat) (oi : Array Nat) (oj : Array (Option Nat)), nl - i ≤ f →
      (∀ k, li[p + k]? = ((innerFrom nl nr cand i).map Prod.fst)[k]?) →
      (∀ k, ri[p + k]? = ((innerFrom nl nr cand i).map Prod.snd)[k]?) →
      (outerGo nl li ri f i p oi oj).1.toList = oi.toList ++ (ljFrom nl nr cand i).map Prod.fst ∧
      (outerGo nl li ri f i p oi oj).2.toList = oj.toList ++ (ljFrom nl nr cand i).map Prod.snd := by
  intro f
  induction f with
  | zero =>
    intro i p oi oj hf _ _
    rw [ljFrom_ge (by omega)]
    simp [outerGo]
  | succ f ih =>
    intro i p oi oj hf hl hr
    by_cases hi : i < nl
    · -- the run of left row `i`
      have hin := innerFrom_cons (nl := nl) (nr := nr) (cand := cand) hi
      rw [ljFrom_cons hi]
      generalize hjsd : rowsOf nr cand i = js at hin ⊢
      have hrun : ∀ k, k < js.length → li[p + k]? = some i ∧ ri[p + k]? = js[k]? := by
        intro k hk
        constructor
        · rw [hl k, hin, List.map_append, List.getElem?_append_left (by simpa using hk)]
          simp [hk]
        · rw [hr k, hin, List.map_append, List.getElem?_append_left (by simpa using hk)]
          simp [hk]
      have hend : li[p + js.length]? ≠ some i := by
        rw [hl, hin, List.map_append, List.getElem?_append_right (by simp)]
        simp only [List.length_map, Nat.sub_self]
        intro h
        have hm : i ∈ (innerFrom nl nr cand (i + 1)).map Prod.fst := List.mem_of_getElem? h
        have := innerFrom_fst_ge _ hm
        omega
      have hfuel : js.length ≤ li.size - p := by
        cases hjs : js with
        | nil => simp
        | cons j js' =>
          have h1 := (hrun js'.length (by simp [hjs])).1
          have : p + js'.length < li.size := by
            rcases Nat.lt_or_ge (p + js'.length) li.size with h | h
            · exact h
            · rw [getElem?_neg li _ (by omega)] at h1
              simp at h1
          simp
          omega
      obtain ⟨e1, e2, e3⟩ := runPairs_spec li ri i js (li.size - p) p oi oj hfuel hrun hend
      rcases hres : runPairs li ri i (li.size - p) p oi oj with ⟨p', oi', oj'⟩
      rw [hres] at e1 e2 e3
      simp only at e1 e2 e3
      by_cases hjs : js = []
      · -- no right row: the left row alone
        have hp' : p' = p := by rw [e1, hjs]; simp
        have hrow : ljRow i js = [(i, none)] := by
          rw [hjs]; rfl
        have ih' := ih (i + 1) p (oi.push i) (oj.push none) (by omega)
          (fun k => by rw [hl k, hin]; simp [hjs])
          (fun k => by rw [hr k, hin]; simp [hjs])
        simp only [outerGo, hi, if_true, hres, hp', beq_self_eq_true]
        rw [ih'.1, ih'.2, hrow]
        simp
      · -- the run of pairs
        have hp' : p' ≠ p := by
          rw [e1]
          intro h
          apply hjs
          exact List.eq_nil_of_length_eq_zero (by omega)
        have hrow : ljRow i js = js.map fun j => (i, some j) := by
          unfold ljRow
          simp [hjs]
        have ih' := ih (i + 1) p' oi' oj' (by omega)
          (fun k => by
            rw [e1, Nat.add_assoc, hl (js.length + k), hin, List.map_append,
              List.getElem?_append_right (by simp)]
            simp)
          (fun k => by
            rw [e1, Nat.add_assoc, hr (js.length + k), hin, List.map_append,
              List.getElem?_append_right (by simp)]
            simp)
        have hne : (p' == p) = false := by simpa using hp'
        simp only [outerGo, hi, if_true, hres, hne, Bool.false_eq_true, if_false]
        rw [ih'.1, ih'.2, hrow, e2, e3]
        simp [Function.comp_def]
    · rw [ljFrom_ge (by omega)]
      simp [outerGo, hi]

/-- `outerPairs` over the index arrays of the inner pairs gives the left
    outer join's rows. -/
theorem outerPairs_eq (nl nr : Nat) (cand : Nat → Nat → Bool) (li ri : Array Nat)
    (hl : li.toList = (innerSpec nl nr cand).map Prod.fst)
    (hr : ri.toList = (innerSpec nl nr cand).map Prod.snd) :
    (outerPairs nl li ri).1.toList = (ljSpec nl nr cand).map Prod.fst ∧
    (outerPairs nl li ri).2.toList = (ljSpec nl nr cand).map Prod.snd := by
  have h := outerGo_spec nl nr cand li ri nl 0 0 #[] #[] (by omega)
    (fun k => by rw [← Array.getElem?_toList, hl]; simp [innerSpec])
    (fun k => by rw [← Array.getElem?_toList, hr]; simp [innerSpec])
  simpa [outerPairs, ljSpec] using h

/-- The merge path of `OptJoin.innerPairs`: `outerPairs` over the index
    arrays of `Qlvr.mergeGo` (join columns non-decreasing on both sides)
    gives `ljSpec` with the merge's test as the candidate relation. -/
theorem outerPairs_merge (A B : Nat → UInt64) (ok : Nat → Nat → Bool) (nl nr : Nat)
    (hA : ∀ x y, x ≤ y → y < nl → (A x).toNat ≤ (A y).toNat)
    (hB : ∀ x y, x ≤ y → y < nr → (B x).toNat ≤ (B y).toNat) :
    let m := mergeGo A B ok nl nr (nl + nr + 1) 0 0 #[] #[]
    (outerPairs nl m.1 m.2).1.toList = (ljSpec nl nr fun x y => A x == B y && ok x y).map Prod.fst ∧
    (outerPairs nl m.1 m.2).2.toList = (ljSpec nl nr fun x y => A x == B y && ok x y).map Prod.snd := by
  intro m
  obtain ⟨h1, h2⟩ := mergeGo_spec A B ok nl nr hA hB (nl + nr + 1) 0 0 #[] #[] (by omega)
  have hs : mergeSpec A B ok nl nr 0 0 = innerSpec nl nr (fun x y => A x == B y && ok x y) := by
    simp [mergeSpec, innerSpec, innerFrom, rowsOf, List.range_eq_range']
  apply outerPairs_eq
  · simpa [m, hs] using h1
  · simpa [m, hs] using h2

/-! ## (a), (b), (c) of the index specification -/

theorem mem_ljRow_some {i x j : Nat} {js : List Nat} :
    (x, some j) ∈ ljRow i js ↔ x = i ∧ j ∈ js := by
  unfold ljRow
  cases js with
  | nil => simp
  | cons j0 js =>
    simp only [List.isEmpty_cons, Bool.false_eq_true, if_false, List.mem_map, Prod.mk.injEq,
      Option.some.injEq]
    constructor
    · rintro ⟨a, ha, h1, h2⟩
      subst h2
      exact ⟨h1.symm, ha⟩
    · rintro ⟨h1, ha⟩
      exact ⟨j, ha, h1.symm, rfl⟩

theorem mem_ljRow_none {i x : Nat} {js : List Nat} :
    (x, none) ∈ ljRow i js ↔ x = i ∧ js = [] := by
  unfold ljRow
  cases js with
  | nil => simp
  | cons j0 js => simp

theorem mem_rowsOf {nr : Nat} {cand : Nat → Nat → Bool} {i j : Nat} :
    j ∈ rowsOf nr cand i ↔ j < nr ∧ cand i j = true := by
  simp [rowsOf]

theorem mem_ljSpec_iff {nl nr : Nat} {cand : Nat → Nat → Bool} {r : Nat × Option Nat} :
    r ∈ ljSpec nl nr cand ↔ r.1 < nl ∧ r ∈ ljRow r.1 (rowsOf nr cand r.1) := by
  simp only [ljSpec, ljFrom, Nat.sub_zero, List.mem_flatMap, List.mem_range']
  constructor
  · rintro ⟨x, ⟨k, hk, hx⟩, hm⟩
    have h1 : r.1 = x := by
      obtain ⟨a, o⟩ := r
      cases o with
      | some j => exact (mem_ljRow_some.mp hm).1
      | none => exact (mem_ljRow_none.mp hm).1
    rw [h1]
    exact ⟨by omega, hm⟩
  · rintro ⟨h1, hm⟩
    exact ⟨r.1, ⟨r.1, h1, by simp⟩, hm⟩

theorem mem_ljSpec_some {nl nr : Nat} {cand : Nat → Nat → Bool} {i j : Nat} :
    (i, some j) ∈ ljSpec nl nr cand ↔ i < nl ∧ j < nr ∧ cand i j = true := by
  rw [mem_ljSpec_iff]
  simp only [mem_ljRow_some, mem_rowsOf, true_and]

theorem mem_ljSpec_none {nl nr : Nat} {cand : Nat → Nat → Bool} {i : Nat} :
    (i, none) ∈ ljSpec nl nr cand ↔ i < nl ∧ ∀ j, j < nr → cand i j = false := by
  rw [mem_ljSpec_iff]
  simp only [mem_ljRow_none, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun j hj => ?_⟩
    have : j ∉ rowsOf nr cand i := by rw [h2]; simp
    rw [mem_rowsOf] at this
    cases hc : cand i j
    · rfl
    · exact absurd ⟨hj, hc⟩ this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, List.eq_nil_iff_forall_not_mem.mpr fun j hj => ?_⟩
    rw [mem_rowsOf] at hj
    rw [h2 j hj.1] at hj
    simp at hj

/-- (a) Every left row is in the output. -/
theorem ljSpec_left_row {nl nr : Nat} {cand : Nat → Nat → Bool} {i : Nat} (hi : i < nl) :
    ∃ o, (i, o) ∈ ljSpec nl nr cand := by
  by_cases h : ∃ j, j < nr ∧ cand i j = true
  · obtain ⟨j, hj, hc⟩ := h
    exact ⟨some j, mem_ljSpec_some.mpr ⟨hi, hj, hc⟩⟩
  · refine ⟨none, mem_ljSpec_none.mpr ⟨hi, fun j hj => ?_⟩⟩
    cases hc : cand i j
    · rfl
    · exact absurd ⟨j, hj, hc⟩ h

/-- (b) An output row `(i, some j)` is a left row and a right row that it
    accepts. -/
theorem ljSpec_mem_some {nl nr : Nat} {cand : Nat → Nat → Bool} {i j : Nat}
    (h : (i, some j) ∈ ljSpec nl nr cand) : i < nl ∧ j < nr ∧ cand i j = true :=
  mem_ljSpec_some.mp h

/-- (b) An output row `(i, none)` is a left row that accepts no right row. -/
theorem ljSpec_mem_none {nl nr : Nat} {cand : Nat → Nat → Bool} {i : Nat}
    (h : (i, none) ∈ ljSpec nl nr cand) : i < nl ∧ ∀ j, j < nr → cand i j = false :=
  mem_ljSpec_none.mp h

/-- (b) Every accepted pair is in the output. -/
theorem ljSpec_complete {nl nr : Nat} {cand : Nat → Nat → Bool} {i j : Nat}
    (hi : i < nl) (hj : j < nr) (hc : cand i j = true) :
    (i, some j) ∈ ljSpec nl nr cand :=
  mem_ljSpec_some.mpr ⟨hi, hj, hc⟩

theorem ljRow_length (i : Nat) (js : List Nat) : (ljRow i js).length = max 1 js.length := by
  unfold ljRow
  cases js <;> simp

theorem ljRow_count (i x : Nat) (js : List Nat) :
    ((ljRow i js).filter fun r => r.1 == x).length = if i = x then max 1 js.length else 0 := by
  unfold ljRow
  by_cases hx : i = x
  · subst hx
    cases js with
    | nil => simp
    | cons j js => simp [List.filter_map, Function.comp_def]
  · cases js with
    | nil => simp [hx]
    | cons j js => simp [hx, List.filter_map, Function.comp_def]

/-- (c) Left row `i` occurs `max 1 c` times, `c` the number of right rows
    it accepts. -/
theorem ljSpec_count_row {nl nr : Nat} {cand : Nat → Nat → Bool} {i : Nat} (hi : i < nl) :
    ((ljSpec nl nr cand).filter fun r => r.1 == i).length = max 1 (rowsOf nr cand i).length := by
  simp only [ljSpec, ljFrom, Nat.sub_zero, List.filter_flatMap]
  have key : ∀ (s n : Nat), s ≤ i → i < s + n →
      (((List.range' s n).flatMap fun x => (ljRow x (rowsOf nr cand x)).filter fun r => r.1 == i)).length =
        max 1 (rowsOf nr cand i).length := by
    intro s n
    induction n generalizing s with
    | zero => intro _ h; omega
    | succ n ih =>
      intro hs hn
      rw [List.range'_succ, List.flatMap_cons, List.length_append, ljRow_count]
      by_cases he : s = i
      · subst he
        have : ((List.range' (s + 1) n).flatMap fun x => (ljRow x (rowsOf nr cand x)).filter fun r => r.1 == s).length = 0 := by
          rw [List.length_eq_zero_iff, List.flatMap_eq_nil_iff]
          intro x hx
          rw [List.mem_range'] at hx
          rw [← List.length_eq_zero_iff, ljRow_count]
          simp
          omega
        simp [this]
      · rw [if_neg he, ih (s + 1) (by omega) (by omega)]
        simp
  exact key 0 nl (Nat.zero_le _) (by omega)

/-- (c) The output length: the sum over the left rows of `max 1 c`. -/
theorem ljSpec_length (nl nr : Nat) (cand : Nat → Nat → Bool) :
    (ljSpec nl nr cand).length = ((List.range nl).map fun i => max 1 (rowsOf nr cand i).length).sum := by
  simp only [ljSpec, ljFrom, Nat.sub_zero, List.length_flatMap, ljRow_length, List.range_eq_range']

/-! ## Rows of ids against SPARQL 1.1 section 18.5 -/

open L4Factoidal.SPARQL (Binding SolutionSeq leftJoin)
open L4Factoidal.RDF (Term)

/-- A solution mapping over ids: (variable, id); an unbound variable is
    absent. -/
abbrev IdRow := List (String × UInt64)

def idLookup (v : String) : IdRow → Option UInt64
  | [] => none
  | (w, x) :: rest => if w = v then some x else idLookup v rest

/-- `Binding.compatible` with id equality. -/
def idCompatible : IdRow → IdRow → Bool
  | [], _ => true
  | (v, x) :: rest, r2 =>
    (match idLookup v r2 with
     | none => true
     | some y => x == y) && idCompatible rest r2

/-- `Binding.merge` over ids. -/
def idMerge (r1 : IdRow) : IdRow → IdRow
  | [] => r1
  | (v, x) :: rest =>
    match idLookup v r1 with
    | some _ => idMerge r1 rest
    | none => idMerge ((v, x) :: r1) rest

/-- LeftJoin(Ω1, Ω2, true) over ids. -/
def idLeftJoin (L R : List IdRow) : List IdRow :=
  L.flatMap fun r1 =>
    let ext := R.filterMap fun r2 => if idCompatible r1 r2 then some (idMerge r1 r2) else none
    if ext.isEmpty then [r1] else ext

/-- The decoded solution mapping. -/
def decRow (dec : UInt64 → Term) (r : IdRow) : Binding := r.map fun (v, x) => (v, dec x)

theorem lookup_decRow (dec : UInt64 → Term) (v : String) :
    ∀ r : IdRow, Binding.lookup v (decRow dec r) = (idLookup v r).map dec := by
  intro r
  induction r with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨w, x⟩ := a
    simp only [decRow, List.map_cons, Binding.lookup, idLookup] at ih ⊢
    by_cases h : w = v
    · simp [h]
    · simp [h, ih]

theorem idLookup_mem {v : String} : ∀ {r : IdRow} {y : UInt64}, idLookup v r = some y → (v, y) ∈ r := by
  intro r
  induction r with
  | nil => intro y h; simp [idLookup] at h
  | cons a rest ih =>
    intro y h
    obtain ⟨w, x⟩ := a
    simp only [idLookup] at h
    by_cases hw : w = v
    · rw [if_pos hw] at h
      cases h
      subst hw
      simp
    · rw [if_neg hw] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- The ids of a row satisfy `ok`. -/
def RowIds (ok : UInt64 → Prop) (r : IdRow) : Prop := ∀ a ∈ r, ok a.2

theorem compatible_decRow (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) :
    ∀ (r1 r2 : IdRow), RowIds ok r1 → RowIds ok r2 →
      Binding.compatible (decRow dec r1) (decRow dec r2) = idCompatible r1 r2 := by
  intro r1
  induction r1 with
  | nil => intro r2 _ _; rfl
  | cons a rest ih =>
    intro r2 h1 h2
    obtain ⟨v, x⟩ := a
    have hx : ok x := h1 (v, x) (by simp)
    have hrest : RowIds ok rest := fun b hb => h1 b (List.mem_cons_of_mem _ hb)
    have e : decRow dec ((v, x) :: rest) = (v, dec x) :: decRow dec rest := rfl
    rw [e]
    simp only [Binding.compatible, idCompatible]
    rw [ih r2 hrest h2, lookup_decRow]
    cases hl : idLookup v r2 with
    | none => rfl
    | some y =>
      have hy : ok y := h2 (v, y) (idLookup_mem hl)
      simp only [Option.map_some]
      rw [hdec x y hx hy]

theorem merge_decRow (dec : UInt64 → Term) :
    ∀ (r2 r1 : IdRow), Binding.merge (decRow dec r1) (decRow dec r2) = decRow dec (idMerge r1 r2) := by
  intro r2
  induction r2 with
  | nil => intro r1; rfl
  | cons a rest ih =>
    intro r1
    obtain ⟨v, x⟩ := a
    have e : decRow dec ((v, x) :: rest) = (v, dec x) :: decRow dec rest := rfl
    rw [e]
    simp only [Binding.merge, idMerge]
    rw [lookup_decRow]
    cases idLookup v r1 with
    | some _ => exact ih r1
    | none =>
      have e2 : (v, dec x) :: decRow dec r1 = decRow dec ((v, x) :: r1) := rfl
      simp only [Option.map_none]
      rw [e2]
      exact ih ((v, x) :: r1)

/-- Decoding the id-level left outer join gives SPARQL 1.1 LeftJoin(Ω1, Ω2,
    true) of the decoded solutions, row for row, when `Term.eqb` of two
    decoded ids is id equality on the ids that occur. -/
theorem leftJoin_decode (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (L R : List IdRow) (hL : ∀ r ∈ L, RowIds ok r) (hR : ∀ r ∈ R, RowIds ok r) :
    (idLeftJoin L R).map (decRow dec) =
      leftJoin (L.map (decRow dec)) (R.map (decRow dec)) (fun _ => true) := by
  unfold idLeftJoin leftJoin
  rw [List.map_flatMap, List.flatMap_map]
  apply L4Factoidal.Qlvr.flatMap_congr'
  intro r1 h1
  rw [List.filterMap_map]
  have hfm : (R.filterMap fun r2 => if idCompatible r1 r2 then some (idMerge r1 r2) else none).map (decRow dec) =
      R.filterMap ((fun mu2 => if Binding.compatible (decRow dec r1) mu2 then
          (if (fun _ => true) (Binding.merge (decRow dec r1) mu2) then some (Binding.merge (decRow dec r1) mu2) else none)
        else none) ∘ decRow dec) := by
    rw [List.map_filterMap]
    apply filterMap_congr'
    intro r2 h2
    simp only [Function.comp_def]
    rw [compatible_decRow dec ok hdec r1 r2 (hL r1 h1) (hR r2 h2), merge_decRow]
    cases idCompatible r1 r2 <;> simp
  rw [← hfm]
  cases (R.filterMap fun r2 => if idCompatible r1 r2 = true then some (idMerge r1 r2) else none) <;> simp

/-! ## `idLeftJoin` as `ljSpec` -/

theorem flatMap_range' {α β : Type} [Inhabited α] (f : α → List β) :
    ∀ (L : List α) (s : Nat) (pre : List α), pre.length = s →
      L.flatMap f = (List.range' s L.length).flatMap fun i => f (pre ++ L)[i]! := by
  intro L
  induction L with
  | nil => intro s pre _; rfl
  | cons a rest ih =>
    intro s pre hs
    rw [List.length_cons, List.range'_succ, List.flatMap_cons, List.flatMap_cons]
    have h0 : (pre ++ a :: rest)[s]! = a := by
      rw [getElem!_pos _ _ (by simp; omega)]
      rw [List.getElem_append_right (by omega)]
      simp [hs]
    rw [h0, ih (s + 1) (pre ++ [a]) (by simp [hs])]
    simp

theorem filterMap_range' {α β : Type} [Inhabited α] (c : α → Bool) (m : α → β) :
    ∀ (L : List α) (s : Nat) (pre : List α), pre.length = s →
      L.filterMap (fun x => if c x then some (m x) else none) =
        ((List.range' s L.length).filter fun j => c (pre ++ L)[j]!).map fun j => m (pre ++ L)[j]! := by
  intro L
  induction L with
  | nil => intro s pre _; rfl
  | cons a rest ih =>
    intro s pre hs
    have h0 : (pre ++ a :: rest)[s]! = a := by
      rw [getElem!_pos _ _ (by simp; omega)]
      rw [List.getElem_append_right (by omega)]
      simp [hs]
    have hrest := ih (s + 1) (pre ++ [a]) (by simp [hs])
    simp only [List.append_assoc, List.singleton_append] at hrest
    have h0' : (pre ++ a :: rest)[s]? = some a := by
      rw [List.getElem?_append_right (by omega)]
      simp [hs]
    rw [List.length_cons, List.range'_succ, List.filterMap_cons, List.filter_cons, h0, hrest]
    cases c a <;> simp [h0']

/-- `idLeftJoin` is `ljSpec` with the id compatibility of the rows, each
    output pair mapped to the merged row or to the left row. -/
theorem idLeftJoin_eq_ljSpec (L R : List IdRow) :
    idLeftJoin L R =
      (ljSpec L.length R.length fun i j => idCompatible L[i]! R[j]!).map fun
        | (i, none) => L[i]!
        | (i, some j) => idMerge L[i]! R[j]! := by
  unfold idLeftJoin ljSpec ljFrom
  rw [flatMap_range' _ L 0 [] rfl, List.map_flatMap, Nat.sub_zero]
  apply L4Factoidal.Qlvr.flatMap_congr'
  intro i _
  simp only [List.nil_append]
  have hR : (R.filterMap fun r2 => if idCompatible L[i]! r2 then some (idMerge L[i]! r2) else none) =
      (rowsOf R.length (fun i j => idCompatible L[i]! R[j]!) i).map fun j => idMerge L[i]! R[j]! := by
    have e := filterMap_range' (idCompatible L[i]!) (idMerge L[i]!) R 0 [] rfl
    simp only [List.nil_append] at e
    rw [e, rowsOf, List.range_eq_range']
  rw [hR]
  unfold ljRow
  cases hrow : rowsOf R.length (fun i j => idCompatible L[i]! R[j]!) i with
  | nil => simp
  | cons j js => simp [Function.comp_def]

/-- The three steps together: the index arrays `outerPairs` builds from the
    inner pairs of `L` and `R` (id compatibility as the candidate relation),
    each mapped to its merged row or its left row and decoded, are SPARQL 1.1
    LeftJoin(Ω1, Ω2, true) of the decoded rows, row for row. -/
theorem outerPairs_leftJoin (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (L R : List IdRow) (hL : ∀ r ∈ L, RowIds ok r) (hR : ∀ r ∈ R, RowIds ok r)
    (li ri : Array Nat)
    (hl : li.toList = (innerSpec L.length R.length fun i j => idCompatible L[i]! R[j]!).map Prod.fst)
    (hr : ri.toList = (innerSpec L.length R.length fun i j => idCompatible L[i]! R[j]!).map Prod.snd) :
    ((outerPairs L.length li ri).1.toList.zip (outerPairs L.length li ri).2.toList).map
        (fun
          | (i, none) => decRow dec L[i]!
          | (i, some j) => decRow dec (idMerge L[i]! R[j]!)) =
      leftJoin (L.map (decRow dec)) (R.map (decRow dec)) (fun _ => true) := by
  obtain ⟨h1, h2⟩ := outerPairs_eq L.length R.length _ li ri hl hr
  rw [h1, h2, ← List.unzip_fst, ← List.unzip_snd, List.zip_unzip,
    ← leftJoin_decode dec ok hdec L R hL hR, idLeftJoin_eq_ljSpec, List.map_map]
  apply List.map_congr_left
  intro r _
  obtain ⟨i, o⟩ := r
  cases o <;> rfl

/-! ## An OPTIONAL group's FILTER applied to the group's rows -/

/-- `LeftJoin(Ω1, Ω2, c)` is `LeftJoin(Ω1, Filter(c2, Ω2), true)` when `c`
    on each compatible merge is `c2` on its right row (SPARQL 1.1 sections
    18.2.2.5 and 18.5; the id path admits an OPTIONAL group's FILTER only when
    it reads the group's own variables, which every row of the group binds,
    to the same values in the merged row). -/
theorem leftJoin_filter_right (o1 o2 : SolutionSeq) (cond c2 : Binding → Bool)
    (h : ∀ mu1 ∈ o1, ∀ mu2 ∈ o2, mu1.compatible mu2 = true → cond (mu1.merge mu2) = c2 mu2) :
    leftJoin o1 o2 cond = leftJoin o1 (o2.filter c2) (fun _ => true) := by
  unfold leftJoin
  apply L4Factoidal.Qlvr.flatMap_congr'
  intro mu1 h1
  have e : (o2.filterMap fun mu2 => if mu1.compatible mu2 then
        (if cond (mu1.merge mu2) then some (mu1.merge mu2) else none) else none) =
      ((o2.filter c2).filterMap fun mu2 => if mu1.compatible mu2 then
        (if (fun _ => true) (mu1.merge mu2) then some (mu1.merge mu2) else none) else none) := by
    rw [List.filterMap_filter]
    apply filterMap_congr'
    intro mu2 h2
    by_cases hc : mu1.compatible mu2 = true
    · rw [h mu1 h1 mu2 h2 hc]
      cases c2 mu2 <;> simp [hc]
    · simp [hc]
  rw [e]

/-! ## The `Table` implementation against `idLeftJoin`, on samples

The step from `Table` columns to rows is not proved (module header). Here
`leftOuterJoin` (merge path, hash path with one and with two shared columns,
the cross product, an empty side, a left table with unbound ids from an
earlier OPTIONAL) is compared with `idLeftJoin` over the rows of the sample
tables: the same rows in the same order, each row's bindings compared as a
set. -/

private def col (xs : List Nat) : ByteArray :=
  xs.foldl (fun b x => L4Factoidal.Qlvr.Side.put64 b x.toUInt64) ByteArray.empty

private def tab (vars : Array String) (cs : List (List Nat)) (sortVar : Option String := none) : Table :=
  { vars, cols := (cs.map col).toArray, rows := (cs.headD []).length, sortVar }

private def sortRow (r : IdRow) : IdRow := r.mergeSort fun a b => decide (a.1 ≤ b.1)

/-- The rows of a table: (variable, id) for every column whose id is not
    `unbound`. -/
private def rowsOfTable (t : Table) : List IdRow :=
  (List.range t.rows).map fun i =>
    sortRow ((List.range t.vars.size).filterMap fun c =>
      let x := t.at c i
      if x == unbound then none else some (t.vars[c]!, x))

private def agrees (l r : Table) : Bool :=
  rowsOfTable (leftOuterJoin l r).1 == (idLeftJoin (rowsOfTable l) (rowsOfTable r)).map sortRow

private def how (l r : Table) : String := (leftOuterJoin l r).2

private def L1 : Table := tab #["s", "a"] [[1, 1, 2, 3, 5], [10, 11, 12, 13, 14]] (some "s")
private def R1 : Table := tab #["s", "f"] [[1, 2, 2, 4], [20, 21, 22, 23]] (some "s")
private def R1h : Table := tab #["s", "f"] [[2, 4, 1, 2], [21, 23, 20, 22]]
private def R2 : Table := tab #["s", "a", "g"] [[1, 2, 3, 1], [10, 12, 99, 11], [30, 31, 32, 33]]
private def R3 : Table := tab #["x"] [[40, 41]]
private def R4 : Table := tab #["s", "f"] [[], []] (some "s")
private def L2 : Table := tab #["s", "a"] [[], []] (some "s")
private def L3 : Table := tab #["s", "a", "f"] [[1, 2, 3, 5], [10, 12, 13, 14], [0, 21, 0, 0]] (some "s")
private def R5 : Table := tab #["s", "g"] [[1, 3, 3, 6], [50, 51, 52, 53]] (some "s")
private def R6 : Table := tab #["s", "a", "g"] [[1, 1, 2], [10, 11, 99], [60, 61, 62]] (some "s")

#guard how L1 R1 == "merge on ?s" && agrees L1 R1
#guard how L1 R1h == "hash" && agrees L1 R1h
#guard how L1 R2 == "hash" && agrees L1 R2
#guard how L1 R3 == "cross product" && agrees L1 R3
#guard agrees L1 R4 && (leftOuterJoin L1 R4).1.rows == 5
#guard agrees L2 R1 && (leftOuterJoin L2 R1).1.rows == 0
#guard how L3 R5 == "merge on ?s" && agrees L3 R5
#guard how L1 R6 == "merge on ?s" && agrees L1 R6
#guard how R1h L1 == "hash" && agrees R1h L1
-- the output keeps the left sort variable: left rows s = 1, 1, 2, 3, 5;
-- s = 1 matches f 20, s = 2 matches f 21 and 22, s = 3 and 5 match nothing:
-- 1 + 1 + 2 + 1 + 1 rows
#guard (leftOuterJoin L1 R1).1.rows == 6 && (leftOuterJoin L1 R1).1.sortVar == some "s"

end L4Factoidal.Storage.Sbm11.OptJoin
