/- Local laws of ordered replacement and anchor checks. These do not establish
   parser correctness, complete matcher semantics or fuel adequacy. -/
import L4Factoidal.Regex.XPath

namespace L4Factoidal.Regex

theorem start_without_multiline (input : List Nat) (pos : Nat) :
    atStart input false pos = (pos == 0) := by simp [atStart]

theorem end_without_multiline (suffix : List Nat) :
    atEnd suffix false = suffix.isEmpty := by simp [atEnd]

theorem ordered_alternative_first (input w : List Nat) (multiline : Bool)
    (fuel pos : Nat) (a b : CRe) (accept : COut → Option COut) (result : COut)
    (h : cmatch input multiline fuel a w pos accept = some result) :
    cmatch input multiline (fuel + 1) (.alt a b) w pos accept = some result := by
  simp only [cmatch] at h ⊢
  simp [cmatchE, h]

theorem ordered_alternative_fallback (input w : List Nat) (multiline : Bool)
    (fuel pos : Nat) (a b : CRe) (accept : COut → Option COut)
    (h : cmatch input multiline fuel a w pos accept = none) :
    cmatch input multiline (fuel + 1) (.alt a b) w pos accept =
      cmatch input multiline fuel b w pos accept := by
  simp only [cmatch] at h ⊢
  simp [cmatchE, h]

#print axioms start_without_multiline
#print axioms end_without_multiline
#print axioms ordered_alternative_first
#print axioms ordered_alternative_fallback

end L4Factoidal.Regex
