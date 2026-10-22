import L4Factoidal.XSD.Datatypes

namespace L4Factoidal.XSD

/-- Timezone offsets cannot be erased by value identity. -/
theorem dt_identity_requires_timezone (a b : DTValue) (h : dtIdentical a b = true) :
    a.tz = b.tz := by
  simp only [dtIdentical, Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

/-- Equal date/time values satisfy enumeration even if not identical. -/
theorem dt_equal_enumeration (k : DTKind) (a b : DTValue)
    (h : valCompare (.dt k a) (.dt k b) = some .eq) :
    valEqualOrIdentical (.dt k a) (.dt k b) = true := by
  simp only [valEqualOrIdentical, h, BEq.rfl, Bool.or_true]

#print axioms dt_identity_requires_timezone
#print axioms dt_equal_enumeration

end L4Factoidal.XSD
