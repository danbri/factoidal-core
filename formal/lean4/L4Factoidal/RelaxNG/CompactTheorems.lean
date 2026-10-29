/-
L4Factoidal.RelaxNG.CompactTheorems — how the RELAX NG Compact Syntax
(OASIS Committee Specification 21 November 2002) relates to the XML syntax
of the RELAX NG Specification (OASIS Committee Specification 3 December
2001, ISO/IEC 19757-2:2008).

The names carry the version of the compact syntax (`rncc2002_`); a later
version (for example the 2008 amendment, if its translation changes) gets
new theorems.

  * `rncc2002_validator_via_xml`: §6.1. A compact schema is simplified (and
    so judged correct, and then used for validation) as the XML syntax
    schema of its translation, with every included or external compact
    schema translated too.
  * `rncc2002_applyAnnotationsGroup_unit`,
    `rncc2002_applyAnnotationsChoice_unit`: the two equations of A.1 for an
    empty annotation (no `group` or `choice` element is added).
  * `rncc2002_looseEq_refl`, `rncc2002_looseEq_start`: the §6.3 test is
    reflexive, and when it holds the two start patterns are equal up to the
    contexts of `value` patterns.
-/
import L4Factoidal.RelaxNG.Compact

namespace L4Factoidal.RelaxNG.Compact

open L4Factoidal.RelaxNG

/-- §6.1 of the 2002 compact syntax: simplification of a compact schema is
simplification (RELAX NG 2001 §4) of its translation into the XML syntax. -/
theorem rncc2002_validator_via_xml (resolve : String → Option String) (base txt : String) :
    simplifyCompact resolve base txt =
      (translate txt).bind (fun root =>
        simplifyNode (fun u => (resolve u).bind (fun t => (translateToXml t).toOption)) base root) :=
  rfl

/-- A.1, `applyAnnotationsGroup(( ), y) = y`. -/
theorem rncc2002_applyAnnotationsGroup_unit (xs : List X) : applyAnnoGroup {} xs = xs := by
  simp [applyAnnoGroup, Anno.isEmpty]

/-- A.1, `applyAnnotationsChoice(( ), y) = y`. -/
theorem rncc2002_applyAnnotationsChoice_unit (xs : List X) : applyAnnoChoice {} xs = xs := by
  simp [applyAnnoChoice, Anno.isEmpty]

/-- The §6.3 test holds of every grammar and itself. -/
theorem rncc2002_looseEq_refl (g : Grammar) : looseEq g g = true := by
  simp [looseEq]

/-- When the §6.3 test holds, the start patterns are equal once the
contexts of `value` patterns are removed. -/
theorem rncc2002_looseEq_start (g h : Grammar) (e : looseEq g h = true) :
    eraseCx g.start = eraseCx h.start := by
  simp [looseEq] at e
  exact e.1

end L4Factoidal.RelaxNG.Compact
