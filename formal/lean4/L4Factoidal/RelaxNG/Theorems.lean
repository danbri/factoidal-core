/-
L4Factoidal.RelaxNG.Theorems — properties of the RELAX NG simplifier and
validator. The prefix `rng2001_` names the specification version: RELAX NG
Specification, OASIS, 3 December 2001 (= ISO/IEC 19757-2:2008).

  * `rng2001_nullable_choice`: §6.2.2, the empty sequence matches a
    `choice` exactly when it matches one of its sides.
  * `rng2001_notAllowed_group_absorbs`, `rng2001_notAllowed_choice_unit`:
    §4.20 / §6.2.6, `notAllowed` absorbs `group` and is the unit of
    `choice` in the derivative constructors.
  * `rng2001_empty_valid`: §6.2.10 with §6.2.4, an element with no
    attributes and no children matches `element nc empty` when its name is
    in `nc`.
  * `rng2001_xsd_data_sound`, `rng2001_xsd_data_iff`: a string the XSD
    datatype library accepts is ·locally valid· for
    `XSD.SimpleType.atomic b f` (`XSD.validate`); the converse holds with
    the extra condition that a QName prefix is bound in the context.
-/
import L4Factoidal.RelaxNG.Validate

namespace L4Factoidal.RelaxNG

open L4Factoidal.XSD

theorem rng2001_nullable_choice (p q : Pattern) :
    nullable (.choice p q) = (nullable p || nullable q) := rfl

theorem rng2001_nullable_group (p q : Pattern) :
    nullable (.group p q) = (nullable p && nullable q) := rfl

theorem rng2001_notAllowed_group_absorbs (p : Pattern) :
    mkGroup .notAllowed p = .notAllowed := by
  cases p <;> rfl

theorem rng2001_notAllowed_choice_unit (p : Pattern) :
    mkChoice .notAllowed p = p := by
  cases p <;> rfl

theorem rng2001_empty_valid (defs : Defs) (cx cx' : Context) (nc : NameClass) (q : QN)
    (h : nc.contains q = true) :
    nullable (childDeriv defs cx (.element nc .empty) (.elem q cx' [] [])) = true := by
  rw [childDeriv]
  simp [startTagOpenDeriv, h, mkAfter, startTagCloseDeriv, textDeriv, textDerivWith,
    mkChoice, endTagDeriv, nullable]

theorem rng2001_xsd_data_sound (b : Builtin) (f : Facets) (cx : Context) (s : String)
    (h : xsdAllows b f cx s = true) : XSD.validate (.atomic b f) s = true := by
  unfold xsdAllows at h
  unfold XSD.validate
  cases hv : valueOf (.atomic b f) s with
  | none => rw [hv] at h; cases h
  | some v => rfl

theorem rng2001_xsd_data_iff (b : Builtin) (f : Facets) (cx : Context) (s : String) :
    xsdAllows b f cx s = true ↔
      ∃ v, valueOf (.atomic b f) s = some v ∧ qnameResolves cx v = true := by
  unfold xsdAllows
  cases hv : valueOf (.atomic b f) s with
  | none => simp
  | some v => simp

end L4Factoidal.RelaxNG
