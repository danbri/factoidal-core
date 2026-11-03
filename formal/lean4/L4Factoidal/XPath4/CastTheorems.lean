/-
L4Factoidal.XPath4.CastTheorems — bridge theorems: the XPath 4.0 cast from
a string (`castFromString`, XPath 4.0 §4.19.2 and F&O 4.0 §21.2) is the
lexical mapping of `L4Factoidal.XSD.Datatypes` (XSD 1.1 Part 2), the one
that the RDF literal code and the SHACL and SPARQL datatype checks use.

Each theorem states that a cast succeeds exactly when the XSD lexical
mapping (with the type's whiteSpace facet, `XSD.lexicalMapWs`) gives a
value, and that the cast's value is that value.
-/
import L4Factoidal.XPath4.Atomic

namespace L4Factoidal.XPath4

open L4Factoidal.XSD

/-- xs:boolean: a cast from a string succeeds exactly when the XSD lexical
    mapping gives a value, and gives that value. -/
theorem cast_boolean_xsd (s : String) (v : Bool) :
    castFromString s (.b .boolean) = .ok (Atomic.ofBool v) ↔
      lexicalMapWs .boolean s = some (.bool v) := by
  simp only [castFromString, lexicalMapWs, lexicalMap, lexicalMapFuel]
  cases h : parseBooleanLex (applyWhiteSpace Builtin.boolean.whiteSpace s) with
  | none => simp [h, err, Except.ok.injEq]
  | some b =>
    simp only [h, Option.map_some, Option.some.injEq, Val.bool.injEq]
    constructor
    · intro hc
      have := congrArg (fun x => match x with | Except.ok a => a.v | _ => .bool (!v)) hc
      simpa [Atomic.ofBool, pure, Except.pure] using this
    · intro hb; subst hb; rfl

/-- xs:decimal: the cast's value is the XSD lexical mapping's value. -/
theorem cast_decimal_xsd (s : String) (d : Dec) :
    lexicalMapWs .decimal s = some (.dec d) →
      castFromString s (.b .decimal) = .ok (Atomic.ofDec d) := by
  simp only [castFromString, lexicalMapWs, lexicalMap, lexicalMapFuel]
  cases h : parseDecimalLex (applyWhiteSpace Builtin.decimal.whiteSpace s) with
  | none => simp
  | some x =>
    simp only [Option.map_some, Option.some.injEq, Val.dec.injEq]
    intro hx; subst hx; rfl

/-- xs:decimal: a cast that succeeds has an XSD lexical value. -/
theorem cast_decimal_xsd_rev (s : String) (a : Atomic) :
    castFromString s (.b .decimal) = .ok a →
      ∃ d, lexicalMapWs .decimal s = some (.dec d) ∧ a = Atomic.ofDec d := by
  simp only [castFromString, lexicalMapWs, lexicalMap, lexicalMapFuel]
  cases h : parseDecimalLex (applyWhiteSpace Builtin.decimal.whiteSpace s) with
  | none => simp [err]
  | some x =>
    intro hc
    refine ⟨x, rfl, ?_⟩
    simp only [pure, Except.pure, Except.ok.injEq] at hc
    exact hc.symm

/-- xs:integer: the cast's value is the XSD lexical mapping's value
    (XSD represents an integer as a decimal with scale 0). -/
theorem cast_integer_xsd (s : String) (i : Int) :
    lexicalMapWs .integer s = some (.dec (Dec.ofInt i)) →
      castFromString s (.b .integer) = .ok ⟨.b .integer, .int i⟩ := by
  simp only [castFromString, lexicalMapWs, lexicalMap, lexicalMapFuel]
  cases h : parseIntegerLex (applyWhiteSpace Builtin.integer.whiteSpace s) with
  | none => simp
  | some j =>
    simp only
    cases hb : inIntBounds Builtin.integer j with
    | false => simp
    | true =>
      simp only [ite_true, Option.some.injEq, Val.dec.injEq]
      intro hj
      have : j = i := by
        have := congrArg Dec.mantissa hj
        simpa [Dec.ofInt] using this
      subst this; rfl

/-- The string-derived types (normalizedString, token, language, Name,
    NCName, NMTOKEN, ID, IDREF, ENTITY): a cast succeeds exactly when the
    XSD lexical mapping accepts the whitespace-processed string. -/
theorem cast_stringDerived_xsd (s : String) (b : Builtin)
    (hb : b ∈ [.normalizedString, .token, .language, .nmtoken, .name, .ncname, .id, .idref, .entity]) :
    (castFromString s (.b b)).toOption.isSome = (lexicalMapWs b s).isSome := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  · simp only [castFromString, lexicalMapWs]
    cases lexicalMap _ (applyWhiteSpace _ s) <;> rfl

end L4Factoidal.XPath4
