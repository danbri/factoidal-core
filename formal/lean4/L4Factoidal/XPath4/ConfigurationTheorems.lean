/- XSD edition selection: preservation of the existing default and checks
   for the shared lexical route used by casts and function conversion. -/
import L4Factoidal.XPath4.Core

namespace L4Factoidal.XPath4

/-- The default processor configuration selects the existing cast. -/
theorem defaultConfiguration_cast (a : Atomic) (t : AType)
    (ns : String → Option String) :
    castAtomicVersion ({} : FeatureSettings).xsdVersion a t ns = castAtomic a t ns := rfl

/-- Default conversion of function arguments is the existing cast route. -/
theorem defaultConfiguration_coerce (t : AType) (a : Atomic) :
    coerceAtom1 t a ({} : FeatureSettings).xsdVersion = coerceAtom1 t a := rfl

/-- Default contexts retain the XSD 1.1 atomic type library. -/
theorem defaultConfiguration_atomicType (name : String) :
    atypeOfNameVersion? ({} : FeatureSettings).xsdVersion name = atypeOfName? name := by
  unfold atypeOfNameVersion?
  cases atypeOfName? name <;> rfl

private def rejected (r : M Atomic) (code : String) : Bool :=
  match r with
  | .error e => e.code == code
  | .ok _ => false

#guard rejected (castFromStringVersion .v10 "+INF" (.b .double)) "FORG0001"
#guard rejected (castFromStringVersion .v10 " +INF " (.b .float)) "FORG0001"
#guard rejected (castFromStringVersion .v10 "0000-01-01" (.b .date)) "FORG0001"
#guard rejected (castFromStringVersion .v10 "0000" (.b .gYear)) "FORG0001"
#guard rejected (castFromStringVersion .v10 "0000-05" (.b .gYearMonth)) "FORG0001"
#guard rejected (castFromStringVersion .v10 "2001-01-01T00:00:00Z" (.b .dateTimeStamp)) "XPST0051"
#guard rejected (castFromStringVersion .v10 "http://example.org/file%GF" (.b .anyURI)) "FORG0001"
#guard rejected (coerceAtom1 (.b .double) (Atomic.untypedOf "+INF") .v10) "FORG0001"
#guard (atypeOfNameVersion? .v10 "dateTimeStamp").isNone
#guard (atypeOfNameVersion? .v10 "yearMonthDuration").isSome
#guard (atypeOfNameVersion? .v10 "anyAtomicType").isSome
#guard match castFromStringVersion .v10 "-0001-01-01" (.b .date) with
  | .ok ⟨_, .x (.dt _ v)⟩ => v.year == some 0
  | _ => false
#guard match castFromStringVersion .v11 "0000-01-01" (.b .date) with
  | .ok ⟨_, .x (.dt _ v)⟩ => v.year == some 0
  | _ => false

/-- The schema context determines declared type derivation in function
    signature instance tests, including document-node nesting. -/
private def schemaForSubtype : SchemaHook := {
  derives := fun a b => a == b || b.loc == "base"
  elemDecl := fun q => some ({ uri := "urn:test", loc := "base" }, q.loc == "nullable")
  attrDecl := fun _ => some { uri := nsXS, loc := "NCName" }
  substitutionType := fun a b => a.loc == "member" && b.loc == "head" }

private def subtypeEnv : Env := { schema := schemaForSubtype }
private def testName : QN := { uri := "urn:test", loc := "member" }
private def baseType : QN := { uri := "urn:test", loc := "base" }
private def derivedType : QN := { uri := "urn:test", loc := "derived" }

#guard subtypeEnv.subtype (.elemT (some (.name testName)) derivedType false)
  (.elemT none baseType true)
#guard !subtypeEnv.subtype (.elemT none baseType true) (.elemT none baseType false)
#guard subtypeEnv.subtype (.doc (some (.elemT none derivedType false)))
  (.doc (some (.elemT none baseType false)))
#guard subtypeEnv.subtype (.schemaElem testName) (.schemaElem { uri := "urn:test", loc := "head" })
#guard !subtypeEnv.subtype (.schemaElem testName) (.elem (some (.name testName)))
#guard subtypeEnv.subtype (.schemaElem testName) (.elemT none baseType false)
#guard !subtypeEnv.subtype (.schemaElem { uri := "urn:test", loc := "nullable" })
  (.elemT none baseType false)
#guard subtypeEnv.subtype (.schemaAttr testName) (.attr (some (.loc "member")))

#print axioms subtypeWithSchema_default

#print axioms defaultConfiguration_cast
#print axioms defaultConfiguration_coerce
#print axioms defaultConfiguration_atomicType

end L4Factoidal.XPath4
