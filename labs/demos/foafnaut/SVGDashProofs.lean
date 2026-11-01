import SVGDash
import Std.Tactic

namespace NativeSVGDash
/-- The actual admitted pattern has complete dash/gap pairs, including the
    empty solid-stroke representation. This is not a numeric coverage proof. -/
theorem normalize_even (pattern result : List Float)
    (h : normalize pattern = .ok result) : result.length % 2 = 0 := by
  simp only [normalize, bind, pure, Except.bind, Except.pure] at h
  repeat first | (split at h) | (simp_all)
  all_goals try simp_all
  all_goals subst result
  all_goals simp only [List.length_append]
  all_goals omega

#print axioms normalize_even
end NativeSVGDash
