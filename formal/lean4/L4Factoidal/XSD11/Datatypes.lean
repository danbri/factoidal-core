import L4Factoidal.XSD.Version
import L4Factoidal.XSD.SimpleType

namespace L4Factoidal.XSD

/-- Convert date bounds/enumerations to the internal astronomical calendar
    before the shared facet checker compares their values. -/
def facetsForVersion (version : Version) (b : Builtin) (f : Facets) : Facets :=
  match version, dtKindOf? b with
  | .v10, some kind =>
    let convert (s : String) :=
      (dateLexicalForEdition .xsd10 kind (applyWhiteSpace b.whiteSpace s)).getD "#invalid-xsd10-date"
    { f with
      minInclusive := f.minInclusive.map convert
      maxInclusive := f.maxInclusive.map convert
      minExclusive := f.minExclusive.map convert
      maxExclusive := f.maxExclusive.map convert
      enumeration := f.enumeration.map (List.map convert) }
  | _, _ => f

def valueFacetsOkVersion (version : Version) (b : Builtin) (f : Facets) (v : Val) : Bool :=
  valueFacetsOk b (facetsForVersion version b f) v

/-- XSD 1.0 rejects 1.1 character-class syntax before the existing
    pattern matcher is used. Invalid patterns are also schema errors. -/
def patternMatches10 (groups : List (List String)) (lit : String) : Bool :=
  groups.flatten.all (fun p => Regex.XPath40.xsd10Admitted p "") && patternMatches groups lit

def lexicalMap10 (b : Builtin) (lit : String) : Option Val :=
  if builtinAvailable .v10 b then lexicalMapVersion .v10 b lit else none

/-- Both editions use the same simple-type evaluator. Only the lexical,
    value facet and pattern policies change. -/
def valueOf10Fuel (fuel : Nat) (t : SimpleType) (lit : String) : Option Val :=
  valueOfFuel fuel t lit lexicalMap10 (valueFacetsOkVersion .v10) patternMatches10

def valueOfVersion (version : Version) (t : SimpleType) (lit : String) : Option Val :=
  match version with
  | .v10 => valueOf10Fuel 8 t lit
  | .v11 => valueOf t lit

@[simp] theorem valueOfVersion_v11 (t : SimpleType) (lit : String) :
    valueOfVersion .v11 t lit = valueOf t lit := rfl

/-- On the non-calendar types, facets are the existing value facet checker. -/
theorem valueFacetsOkVersion_common (b : Builtin) (f : Facets) (v : Val)
    (hdate : dtKindOf? b = none) :
    valueFacetsOkVersion .v10 b f v = valueFacetsOk b f v := by
  simp [valueFacetsOkVersion, facetsForVersion, hdate]

/-- Atomic common types have the same lexical mapping and facets in both
    editions. Calendar types and float/double have distinct lexical spaces. -/
theorem valueOfVersion_common_atomic (b : Builtin) (f : Facets) (lit : String)
    (havail : builtinAvailable .v10 b = true)
    (hdate : dtKindOf? b = none) (hf : b ≠ .float) (hd : b ≠ .double)
    (hpatterns : f.patterns.flatten.all (fun p => Regex.XPath40.xsd10Admitted p "") = true) :
    valueOfVersion .v10 (.atomic b f) lit = valueOf (.atomic b f) lit := by
  simp only [valueOfVersion, valueOf, valueOf10Fuel, valueOfFuel]
  simp [lexicalMap10, havail, lexicalMapVersion_common b _ hdate hf hd,
    valueFacetsOkVersion_common b f _ hdate, SimpleType.whiteSpaceOf,
    SimpleType.facets, patternMatches10, hpatterns]

#print axioms lexicalMapVersion_common
#print axioms valueFacetsOkVersion_common
#print axioms valueOfVersion_common_atomic

end L4Factoidal.XSD
