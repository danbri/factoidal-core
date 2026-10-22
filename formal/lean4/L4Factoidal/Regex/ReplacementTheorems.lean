/- F&O 3.x q mode: literal replacement encoding is valid and cannot capture.
   These laws concern template encoding, not all regex matching semantics. -/
import L4Factoidal.Regex.XPath

namespace L4Factoidal.Regex
open XSDPattern

theorem quoteReplacement_valid (cs : List Nat) :
    templateValid (quoteReplacement cs) = true := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      by_cases hb : c = cpBackslash
      · simp [quoteReplacement, hb, templateValid, cpBackslash, cpDollar, ih]
      · by_cases hd : c = cpDollar
        · simp [quoteReplacement, hd, templateValid, cpBackslash, cpDollar, ih]
        · simp only [cpDollar] at hd
          simp only [quoteReplacement, cpDollar]
          cases hq : quoteReplacement cs <;> simp_all [templateValid]

theorem quoteReplacement_no_groups (cs : List Nat) :
    templateHasGroup (quoteReplacement cs) = false := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      by_cases hb : c = cpBackslash
      · simp [quoteReplacement, hb, templateHasGroup, cpBackslash, cpDollar, ih]
      · by_cases hd : c = cpDollar
        · simp [quoteReplacement, hd, templateHasGroup, cpBackslash, cpDollar, ih]
        · simp only [cpDollar] at hd
          simp only [quoteReplacement, cpDollar]
          cases hq : quoteReplacement cs <;> simp_all [templateHasGroup]

/-- Quoting preserves arbitrary literal codepoints, independently of capture
    spans or the matched input. -/
theorem expandTemplate_quoted (cs input : List Nat) (start stop : Nat) (caps : List Cap) :
    expandTemplate (quoteReplacement cs) input start stop caps = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      by_cases hb : c = cpBackslash
      · simp [quoteReplacement, hb, expandTemplate, cpBackslash, cpDollar, ih]
      · by_cases hd : c = cpDollar
        · simp [quoteReplacement, hd, expandTemplate, cpBackslash, cpDollar, ih]
        · simp only [cpDollar] at hd
          simp only [quoteReplacement, cpDollar]
          cases hq : quoteReplacement cs <;> simp_all [expandTemplate]

#print axioms expandTemplate_quoted
#print axioms quoteReplacement_valid
#print axioms quoteReplacement_no_groups

end L4Factoidal.Regex
