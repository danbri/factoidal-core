import L4Factoidal.XSD.ValueSpace

namespace L4Factoidal.XSD

/-- Every represented decimal value belongs to the decimal value space,
    independently of its original spelling and fractional scale. -/
theorem decimal_value_membership (d : Dec) :
    valueInBuiltin .decimal (.dec d) = some true := by
  simp [valueInBuiltin, valueMembershipSupported, Builtin.primitive, Builtin.primitive?]

/-- The day-time restriction is a value constraint, not a ban on the letter M
    in a duration's source spelling. -/
theorem dayTime_value_membership (d : DurValue) :
    valueInBuiltin .dayTimeDuration (.dur d) = some (d.months == 0) := by
  change some (false || (true && d.months == 0) || (false && _)) = _
  simp

/-- A refused source mapping cannot become a successful negative verdict. -/
theorem refused_source_membership (edition : Edition) (source target : Builtin)
    (lexical : String) (h : checkedLexicalValue edition source lexical = none) :
    lexicalValueInBuiltin edition source lexical target = none := by
  simp [lexicalValueInBuiltin, h]

#print axioms decimal_value_membership
#print axioms dayTime_value_membership
#print axioms refused_source_membership

/-- Checked integer mapping preserves exactly the parsed integer value. -/
theorem checked_integer_value (s : String) : checkedLexicalValue .xsd11 .integer s =
    (parseIntegerLex s).map (fun i => Val.dec (Dec.ofInt i)) := by
  cases hp : parseIntegerLex s <;>
    simp only [checkedLexicalValue, lexicalFor, dtKindOf?, lexicalMap, lexicalMapFuel, hp] <;> rfl

/-- Checked int mapping additionally enforces the shared signed 32-bit bounds. -/
theorem checked_int_value (s : String) : checkedLexicalValue .xsd11 .int s =
    (parseIntegerLex s).bind (fun i =>
      if inIntBounds .int i then some (Val.dec (Dec.ofInt i)) else none) := by
  cases hp : parseIntegerLex s with
  | none =>
      simp only [checkedLexicalValue, lexicalFor, dtKindOf?, lexicalMap, lexicalMapFuel, hp]
      rfl
  | some i =>
      simp only [checkedLexicalValue, lexicalFor, dtKindOf?, lexicalMap, lexicalMapFuel, hp]
      by_cases hb : inIntBounds .int i = true
      · simp only [hb, ↓reduceIte, Option.bind_some]
        change (if inIntBounds .int i then some _ else none) = some _
        simp [hb]
      · simp only [hb, Option.bind_some]
        rfl

#print axioms checked_integer_value
#print axioms checked_int_value

end L4Factoidal.XSD
