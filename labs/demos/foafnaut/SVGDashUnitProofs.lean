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

private theorem numeric_result_form (pattern result : List Float)
    (h : normalize pattern = .ok result) :
    result = [] ∨ result = (if pattern.length%2 == 1 then pattern++pattern else pattern) := by
  simp only [normalize, bind, pure, Except.bind, Except.pure] at h
  repeat first | (split at h) | simp_all
  all_goals simp_all

/-- Forgetting unit provenance commutes with the actual numeric normalizer,
    including its exact error strings. This prevents vacuous all-empty output. -/
theorem normalizeLengths_numeric (pattern : List Length) :
    (normalizeLengths pattern).map (List.map Length.value) =
      normalize (pattern.map Length.value) := by
  cases h : normalize (pattern.map Length.value) with
  | error message => simp [normalizeLengths, h, bind, Except.bind, Except.map]
  | ok values =>
    rcases numeric_result_form _ _ h with empty | shape
    · subst values
      simp [normalizeLengths, h, bind, pure, Except.bind, Except.pure, Except.map]
    · subst values
      by_cases odd : pattern.length % 2 = 1
      · by_cases empty : pattern = []
        · simp [empty] at odd
        · simp [normalizeLengths, h, bind, pure, Except.bind, Except.pure, Except.map, odd, empty, List.map_append]
      · by_cases empty : pattern = []
        · have hz : normalize [] = .ok [] := by simpa [empty] using h
          simp [normalizeLengths, empty, hz, bind, pure, Except.bind, Except.pure, Except.map]
        · simp [normalizeLengths, h, bind, pure, Except.bind, Except.pure, Except.map, odd, empty]

/-- Percentage distances are unchanged by every supplied calibration scale. -/
theorem Length.calibrated_percentage (length : Length) (scale : Float)
    (h : length.percentage = true) : length.calibrated scale = length.value := by
  simp [Length.calibrated, h]

#print axioms normalizeLengths_numeric
#print axioms Length.calibrated_percentage
#print axioms normalizeLengths_provenance
#print axioms normalizeLengths_even
end NativeSVGDash
