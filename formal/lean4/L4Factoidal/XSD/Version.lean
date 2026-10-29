/- XML Schema edition policy. The datatype parsers, calendar, whitespace,
   patterns and value facets remain the shared XSD implementation. -/
import L4Factoidal.XSD.Lexical

namespace L4Factoidal.XSD

inductive Version where
  | v10 | v11
deriving BEq, DecidableEq, Repr, Inhabited

/-- Schema declarations available in each edition. XPath may independently
    provide the F&O duration extensions in an XSD 1.0 static context. -/
def builtinAvailable (version : Version) (b : Builtin) : Bool :=
  version == .v11 || (b != .anyAtomicType && b != .dateTimeStamp &&
    b != .yearMonthDuration && b != .dayTimeDuration)

/-- The shared lexical mapping with the XSD 1.0 calendar and lexical rules.
    This mapping also serves the duration extensions of F&O. -/
def lexicalMapVersion (version : Version) (b : Builtin) (lit : String) : Option Val :=
  match version with
  | .v10 => lexicalFor .xsd10 b lit
  | .v11 => lexicalMap b lit

def lexicalAllowed (version : Version) (b : Builtin) (lit : String) : Bool :=
  (lexicalMapVersion version b lit).isSome

@[simp] theorem lexicalMapVersion_v11 (b : Builtin) (lit : String) :
    lexicalMapVersion .v11 b lit = lexicalMap b lit := rfl

@[simp] theorem lexicalMapVersion_v10 (b : Builtin) (lit : String) :
    lexicalMapVersion .v10 b lit = lexicalFor .xsd10 b lit := rfl

/-- Every datatype with no edition-specific lexical change uses exactly
    the existing lexical mapping. -/
theorem lexicalMapVersion_common (b : Builtin) (lit : String)
    (hdate : dtKindOf? b = none) (hf : b ≠ .float) (hd : b ≠ .double) :
    lexicalMapVersion .v10 b lit = lexicalMap b lit := by
  simp [lexicalMapVersion, lexicalFor, hdate, hf, hd]


#print axioms lexicalMapVersion_common

end L4Factoidal.XSD
