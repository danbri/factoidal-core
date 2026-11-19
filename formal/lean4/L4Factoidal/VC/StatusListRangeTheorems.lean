import L4Factoidal.VC.StatusList

namespace L4Factoidal.VC.StatusList

open L4Factoidal.JSON

/-- Kind: accumulator bound.
Says: each Boolean digit appended to the accumulator increases its bit budget
by one.
Does not say: where the digits came from. -/
private theorem foldl_bits_lt {α : Type} (bit : α → Bool) (xs : List α)
    (acc width : Nat) (hacc : acc < 2 ^ width) :
    xs.foldl (fun n x => 2 * n + (if bit x then 1 else 0)) acc <
      2 ^ (width + xs.length) := by
  induction xs generalizing acc width with
  | nil => simpa using hacc
  | cons x xs ih =>
    have hnext : 2 * acc + (if bit x then 1 else 0) < 2 ^ (width + 1) := by
      rw [Nat.pow_succ]
      split <;> omega
    have htail := ih _ _ hnext
    have hwidth : width + 1 + xs.length = width + (xs.length + 1) := by omega
    rw [hwidth] at htail
    exact htail

/-- Kind: decoder result bound.
Says: reading a status of the given width yields a natural number representable
at that width, including a zero-width read.
Does not say: that the requested bits are present in the buffer. -/
private theorem readStatus_lt_power (bits : ByteArray) (pos width : Nat) :
    readStatus bits pos width < 2 ^ width := by
  simpa only [readStatus, List.length_range, Nat.zero_add] using
    (foldl_bits_lt (fun k => bitAt bits (pos + k)) (List.range width) 0 0 (by decide))

/-- Kind: structural status-list validation and decoder provenance.
Says: successful validation has an actual checked credential subject and a
decoded bitstring of sufficient length. The requested field is within that
bitstring, and reading it at the requested width produces the returned status.
The returned number fits that width, and the validity flag reports whether it
is zero.
Does not say: that the credential or list has an authentic proof, that it was
retrieved from the entry's URL, or that the decompressor used bounded resources. -/
theorem validate_ok_status_range {entry : Entry} {slc : Json} {result : Result}
    (h : validate entry slc = .ok result) :
    ∃ (subj : Json) (bits : ByteArray),
      checkListCredential slc = .ok subj ∧
      entry.statusPurpose ∈ purposesOf subj ∧
      expand ((subj.getString? "encodedList").getD "") = .ok bits ∧
      minimumNumberOfEntries ≤ bits.size * 8 / entry.statusSize ∧
      entry.statusListIndex * entry.statusSize + entry.statusSize ≤ bits.size * 8 ∧
      result.status = readStatus bits (entry.statusListIndex * entry.statusSize) entry.statusSize ∧
      result.status < 2 ^ entry.statusSize ∧
      result.purpose = entry.statusPurpose ∧
      result.valid = (result.status == 0) := by
  unfold validate at h
  cases hsubj : checkListCredential slc with
  | error why => simp [hsubj, bind, Except.bind] at h
  | ok subj =>
    simp only [hsubj, bind, Except.bind] at h
    by_cases hpurpose : (purposesOf subj).contains entry.statusPurpose = true
    · simp only [hpurpose, Bool.not_true, Bool.false_eq_true, if_false] at h
      cases hbits : expand ((subj.getString? "encodedList").getD "") with
      | error why => simp [hbits, bind, Except.bind] at h
      | ok bits =>
        simp only [hbits, bind, Except.bind] at h
        by_cases hshort : bits.size * 8 / entry.statusSize < minimumNumberOfEntries
        · simp only [hshort, if_true] at h
          cases h
        · simp only [hshort, if_false] at h
          by_cases hout : entry.statusListIndex * entry.statusSize + entry.statusSize > bits.size * 8
          · simp only [hout, if_true] at h
            cases h
          · simp only [hout, if_false] at h
            cases h
            exact ⟨subj, bits, by simp [hsubj], List.contains_iff_mem.mp hpurpose, hbits,
              Nat.le_of_not_gt hshort, Nat.le_of_not_gt hout, rfl,
              readStatus_lt_power bits (entry.statusListIndex * entry.statusSize) entry.statusSize,
              rfl, rfl⟩
    · have hfalse : (purposesOf subj).contains entry.statusPurpose = false :=
        Bool.eq_false_iff.mpr hpurpose
      simp only [hfalse, Bool.not_false, if_true] at h
      cases h

#print axioms validate_ok_status_range

end L4Factoidal.VC.StatusList
