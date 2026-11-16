import L4Factoidal.JS.Regex

/-!
# L4Factoidal.JS.RegexTheorems — step lemmas of the RegExp matcher and class sets

What is proved here (and only this):
- `readAt_fwd`, `readAt_back`: the matcher reads one or two code units, inside the subject
  (forward: the end stays at most the size; backward: never before index 0);
- `step1_fwd`, `step1_back`: a single character matcher moves the position strictly forward
  (and not past the end) or strictly backward, so a repetition of one makes progress;
- `applyMods_nil`: a modifier group that changes nothing keeps the flags;
- `CSet.mem_inter_strs`, `CSet.mem_diff_strs`: the strings of `&&` and `--` of the `v` flag
  are the intersection and difference of the strings (§22.2.2.9 CompileToCharSet).
The tables, case folding and the whole matcher are tested (JS/RegressionTests.lean, Test262).
-/

namespace L4Factoidal.JS.Re

theorem readAt_fwd (cs : Array Char) (uni : Bool) (pos : Nat) (c : Char) (w : Nat)
    (h : readAt cs uni false pos = some (c, w)) : 0 < w ∧ pos + w ≤ cs.size := by
  unfold readAt at h
  simp only [Bool.not_false, if_true, ↓reduceIte] at h
  split at h
  · rename_i hp
    split at h
    · split at h
      · rename_i d hd
        rw [Array.getElem?_eq_some_iff] at hd
        obtain ⟨hl, _⟩ := hd
        split at h <;> (simp only [Option.some.injEq, Prod.mk.injEq] at h; omega)
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
  · simp at h

theorem readAt_back (cs : Array Char) (uni : Bool) (pos : Nat) (c : Char) (w : Nat)
    (h : readAt cs uni true pos = some (c, w)) : 0 < w ∧ w ≤ pos := by
  unfold readAt at h
  simp only [Bool.not_true, Bool.false_eq_true, if_false, ↓reduceIte] at h
  by_cases hp : pos = 0
  · simp [hp] at h
  · simp only [beq_iff_eq, hp, if_false, ↓reduceIte] at h
    split at h
    · rename_i hc
      split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        omega
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega

theorem step1_fwd (cs : Array Char) (fl : Flags) (n : Node) (pos q : Nat)
    (h : step1 cs fl false n pos = some q) : pos < q ∧ q ≤ cs.size := by
  unfold step1 at h
  split at h
  · rename_i c w hr
    have := readAt_fwd cs fl.unicode pos c w hr
    split at h
    · simp only [Option.some.injEq, Bool.false_eq_true, if_false] at h; omega
    · simp at h
  · simp at h

theorem step1_back (cs : Array Char) (fl : Flags) (n : Node) (pos q : Nat)
    (h : step1 cs fl true n pos = some q) : q < pos := by
  unfold step1 at h
  split at h
  · rename_i c w hr
    have := readAt_back cs fl.unicode pos c w hr
    split at h
    · simp only [Option.some.injEq, if_true] at h; omega
    · simp at h
  · simp at h

theorem applyMods_nil (fl : Flags) : applyMods fl [] [] = fl := by
  cases fl; simp [applyMods]

theorem CSet.mem_inter_strs (a b : CSet) (s : List Char) :
    s ∈ (a.inter b).strs ↔ s ∈ a.strs ∧ s ∈ b.strs := by
  simp [CSet.inter, List.mem_filter]

theorem CSet.mem_diff_strs (a b : CSet) (s : List Char) :
    s ∈ (a.diff b).strs ↔ s ∈ a.strs ∧ s ∉ b.strs := by
  simp [CSet.diff, List.mem_filter]

end L4Factoidal.JS.Re
