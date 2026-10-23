import L4Factoidal.RIF.Builtins
import L4Factoidal.XSD.SimpleType
import L4Factoidal.RIF.Engine

namespace L4Factoidal.RIF.IdentityTests

private def different (a : String) (atype : String) (b : String) (bt : String) : Ans :=
  evalPred "literal-not-identical" [gLit a (xsdNs ++ atype), gLit b (xsdNs ++ bt)]

#guard different "1" "integer" "1.0" "decimal" == .no
#guard different "true" "boolean" "1" "boolean" == .no
#guard different "false" "boolean" "0" "boolean" == .no
#guard different "0a" "hexBinary" "0A" "hexBinary" == .no
#guard different "P1D" "dayTimeDuration" "PT24H" "dayTimeDuration" == .no
#guard different "P0M" "yearMonthDuration" "PT0S" "dayTimeDuration" == .no
#guard different "1" "integer" "1" "string" == .yes
#guard different "1" "integer" "2" "integer" == .yes
#guard different "16777217" "float" "16777216" "float" == .no
#guard different "0" "double" "-0" "double" == .yes
#guard different "NaN" "double" "NaN" "double" == .no
#guard evalPred "literal-not-identical" [.const "hello@" (rdfNs ++ "PlainLiteral"), gStr "hello"] == .no
#guard evalPred "literal-not-identical" [.const "hello@EN" (rdfNs ++ "PlainLiteral"),
  .const "hello@en" (rdfNs ++ "PlainLiteral")] == .no
#guard evalPred "literal-not-identical" [.list [], gStr "x"] == .no
#guard evalPred "literal-not-identical" [gIri "https://example.org/a", gStr "x"] == .unknown

private def dt (s : String) : XSD.Val :=
  (XSD.lexicalFor .xsd11 .dateTime s).getD (.bool false)

private def localNoon := dt "2002-10-10T12:00:00-05:00"
private def utcEvening := dt "2002-10-10T17:00:00Z"

#guard !XSD.valIdentical localNoon utcEvening
#guard XSD.valCompare localNoon utcEvening == some .eq
#guard XSD.valueFacetsOk .dateTime { enumeration := some ["2002-10-10T12:00:00-05:00"] } utcEvening
#guard XSD.valueFacetsOk .double { enumeration := some ["-0"] }
  ((XSD.lexicalFor .xsd11 .double "0").getD (.bool false))

#guard different "1" "float" "1" "double" == .yes
#guard different "0" "integer" "-0.0" "decimal" == .no
#guard different "+INF" "double" "INF" "double" == .no
#guard different "false" "boolean" "1" "boolean" == .yes
#guard different "TQ==" "base64Binary" "T Q ==" "base64Binary" == .no
#guard different "4D" "hexBinary" "TQ==" "base64Binary" == .yes
#guard different "1.0" "integer" "1" "integer" == .unknown
#guard different "128" "byte" "128" "integer" == .unknown
#guard different "x" "QName" "y" "QName" == .unknown
#guard different "2002-10-10T12:00:00-05:00" "dateTime"
  "2002-10-10T17:00:00Z" "dateTime" == .yes
#guard different "2002-10-10T17:00:00+00:00" "dateTime"
  "2002-10-10T17:00:00Z" "dateTimeStamp" == .no
#guard different "2002-10-10T24:00:00Z" "dateTime"
  "2002-10-11T00:00:00Z" "dateTime" == .no
#guard different "17:00:00.00Z" "time" "17:00:00Z" "time" == .no
#guard different "17:00:00" "time" "17:00:00Z" "time" == .yes
#guard evalPred "literal-not-identical" [gStr "x", .list [gStr "y"]] == .no
#guard evalPred "literal-not-identical" [.const "hello@en" (rdfNs ++ "PlainLiteral"),
  .const "hello@fr" (rdfNs ++ "PlainLiteral")] == .yes
#guard evalPred "literal-not-identical" [.const "a@b@" (rdfNs ++ "PlainLiteral"), gStr "a@b"] == .no
#guard evalPred "literal-not-identical" [.const "<x/>" (rdfNs ++ "XMLLiteral"),
  .const "<x></x>" (rdfNs ++ "XMLLiteral")] == .unknown
#guard evalPred "literal-not-identical" [.const "x" localSpace, gStr "x"] == .unknown

-- Enumeration and identity deliberately disagree on these values.
#guard XSD.valEqualOrIdentical localNoon utcEvening
#guard !XSD.valIdentical (.seq [localNoon]) (.seq [utcEvening])
#guard XSD.valEqualOrIdentical (.seq [localNoon]) (.seq [utcEvening])
#guard XSD.valIdentical (.seq [.dec ⟨100, 2⟩]) (.dec ⟨1, 0⟩)
#guard XSD.valIdentical (.dec ⟨1, 0⟩) (.seq [.dec ⟨100, 2⟩])
#guard !XSD.valIdentical (.seq []) (.str .string "")
#guard !XSD.valEqualOrIdentical (.seq [.bool true]) (.seq [.bool true, .bool true])
#guard (XSD.valueOf (.list (.atomic .double {})
  { enumeration := some ["-0 NaN"] }) "0 NaN").isSome
#guard (XSD.valueOf (.union [.atomic .double {}, .atomic .string {}]
  { enumeration := some ["-0"] }) "0").isSome
#guard !(XSD.valueOf (.atomic .dateTime
  { enumeration := some ["2002-10-10T12:00:00-05:00"] }) "2002-10-10T18:00:00Z").isSome

-- Exercise the rule engine, not just the built-in dispatcher: equal-value
-- spellings must not fire a rule guarded by literal-not-identical.
private def resultAtom : Atom := .pos "https://example.org/result" iriSpace []
private def identityRule (second : String) : Rule :=
  { head := resultAtom
    body := some (.atom (.externalPred (predNs ++ "literal-not-identical")
      [.const "1" (xsdNs ++ "integer"), .const second (xsdNs ++ "decimal")])) }

#guard entails [identityRule "1.0"] [] (.atom resultAtom) 4 == .doesNotHold
#guard entails [identityRule "2.0"] [] (.atom resultAtom) 4 == .holds
#guard (match entails [identityRule "bad"] [] (.atom resultAtom) 4 with
  | .undecided _ => true | _ => false)

end L4Factoidal.RIF.IdentityTests
