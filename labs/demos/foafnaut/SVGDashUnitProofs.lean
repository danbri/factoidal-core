import SVGDashUnits
import Std.Tactic
namespace NativeSVGDash
/-- Successful normalization preserves complete original value/unit records;
    it can only discard the all-zero pattern or repeat the input unchanged. -/
theorem normalizeLengths_structure (pattern result : List Length)
    (h : normalizeLengths pattern = .ok result) :
    result = [] ∨ result = pattern ∨ result = pattern ++ pattern := by
  simp only [normalizeLengths, bind, pure, Except.bind, Except.pure] at h
  repeat first | (split at h) | (simp_all)

/-- No surviving dash can acquire a unit category or value from another dash. -/
theorem normalizeLengths_provenance (pattern result : List Length) (item : Length)
    (h : normalizeLengths pattern = .ok result) (member : item ∈ result) :
    item ∈ pattern := by
  rcases normalizeLengths_structure pattern result h with empty | same | repeated
  · simp [empty] at member
  · simpa [same] using member
  · simpa [repeated, List.mem_append] using member

/-- Actual normalized records retain dash/gap pairing, including solid strokes. -/
theorem normalizeLengths_even (pattern result : List Length)
    (h : normalizeLengths pattern = .ok result) : result.length % 2 = 0 := by
  simp only [normalizeLengths, bind, pure, Except.bind, Except.pure] at h
  repeat first | (split at h) | (simp_all)
  all_goals try simp_all
  all_goals subst result
  all_goals try simp only [List.length_append]
  all_goals omega

#print axioms normalizeLengths_provenance
#print axioms normalizeLengths_even
end NativeSVGDash
