import L4Factoidal.DOM.Editing.TextControl
import L4Factoidal.DOM.Range

namespace L4Factoidal.DOM.Editing

private abbrev advanceUnits (units : Nat) (c : Char) : Nat :=
  units + L4Factoidal.DOM.Range.unitsOf c

/-- Kind: UTF-16 prefix measure invariant.
Says: the unit fold cannot decrease its starting count.
Does not say: how many additional units a particular list contributes. -/
private theorem foldl_units_ge (cs : List Char) (units : Nat) :
    units ≤ cs.foldl advanceUnits units := by
  induction cs generalizing units with
  | nil => exact Nat.le_refl units
  | cons c cs ih =>
    exact Nat.le_trans (Nat.le_add_right units _) (ih (advanceUnits units c))

/-- Kind: UTF-16 prefix measure monotonicity.
Says: taking a longer prefix cannot lower its unit count.
Does not say: that extending a prefix past the input increases the count. -/
private theorem foldl_take_units_mono (cs : List Char) (units i j : Nat) (h : i ≤ j) :
    (cs.take i).foldl advanceUnits units ≤ (cs.take j).foldl advanceUnits units := by
  induction cs generalizing units i j with
  | nil => simp
  | cons c cs ih =>
    cases i with
    | zero => exact foldl_units_ge _ _
    | succ i =>
      cases j with
      | zero => omega
      | succ j => exact ih (advanceUnits units c) i j (Nat.le_of_succ_le_succ h)

/-- Kind: actual list loop invariant.
Says: given a target at the measured end of a prefix, the offset loop
increments the initial character index by precisely that prefix length.
Does not say: that a number inside a surrogate pair is such a target. -/
private theorem forIn_at_boundary (cs : List Char) (i units index : Nat) (h : i ≤ cs.length) :
    ((forIn (m := Id) cs (units, index) fun c s =>
      if s.1 ≥ (cs.take i).foldl advanceUnits units then pure (.done s)
      else pure (.yield (advanceUnits s.1 c, s.2 + 1))) : Nat × Nat).2 = index + i := by
  induction i generalizing cs units index with
  | zero =>
    cases cs with
    | nil => rfl
    | cons c cs => simp [List.forIn_cons]
  | succ i ih =>
    cases cs with
    | nil => simp at h
    | cons c cs =>
      have hin : i ≤ cs.length := Nat.le_of_succ_le_succ h
      have hmore : units < advanceUnits units c := by
        unfold advanceUnits L4Factoidal.DOM.Range.unitsOf
        split <;> omega
      have hnot : ¬ (cs.take i).foldl advanceUnits (advanceUnits units c) ≤ units :=
        Nat.not_le_of_gt (Nat.lt_of_lt_of_le hmore (foldl_units_ge _ _))
      rw [List.take_succ_cons, List.foldl_cons, List.forIn_cons, if_neg hnot]
      have htail := ih cs (advanceUnits units c) (index + 1) hin
      have hadd : index + 1 + i = index + (i + 1) := by omega
      rw [hadd] at htail
      exact htail

/-- Kind: text-control offset round trip.
Says: encoding and then decoding the UTF-16 offset of any scalar boundary
recovers the original character index.
Does not say: that an offset between the two units of a surrogate pair
survives decoding and re-encoding. -/
theorem indexOfUnits_unitsOfIndex (cs : List Char) (i : Nat) (h : i ≤ cs.length) :
    indexOfUnits cs (unitsOfIndex cs i) = i := by
  exact forIn_at_boundary cs i 0 0 h

/-- Kind: text-edit result and UTF-16 representation invariant.
Says: a successful edit on a valid selection returns UTF-16 selection offsets
in order and within the returned value, and both are exact scalar boundaries
for the actual text-control decoder.
Does not say: that host string framing, JavaScript number conversion or
operations starting at an interior surrogate offset satisfy this round trip. -/
theorem textEdit_result_utf16 (multiline : Bool) (command : String)
    (arg : List Char) (t r : TextSel) (inputType : Option String)
    (ht : t.ok) (h : textEdit multiline command arg t = some (r, inputType)) :
    unitsOfIndex r.chars r.start ≤ unitsOfIndex r.chars r.stop ∧
    unitsOfIndex r.chars r.stop ≤ L4Factoidal.DOM.Range.utf16Length (String.ofList r.chars) ∧
    indexOfUnits r.chars (unitsOfIndex r.chars r.start) = r.start ∧
    indexOfUnits r.chars (unitsOfIndex r.chars r.stop) = r.stop := by
  obtain ⟨horder, hstop⟩ := textEdit_ok multiline command arg t ht (r, inputType) h
  have hstart := Nat.le_trans horder hstop
  refine ⟨foldl_take_units_mono _ _ _ _ horder, ?_,
    indexOfUnits_unitsOfIndex _ _ hstart, indexOfUnits_unitsOfIndex _ _ hstop⟩
  have hfull := foldl_take_units_mono r.chars 0 r.stop r.chars.length hstop
  rw [List.take_of_length_le (Nat.le_refl r.chars.length)] at hfull
  simpa only [L4Factoidal.DOM.Range.utf16Length, String.foldl_eq_foldl_toList, String.toList_ofList]
    using hfull

#print axioms indexOfUnits_unitsOfIndex
#print axioms textEdit_result_utf16

end L4Factoidal.DOM.Editing
