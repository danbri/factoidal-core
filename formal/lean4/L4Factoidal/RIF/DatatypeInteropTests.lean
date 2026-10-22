import L4Factoidal.RIF.Builtins

namespace L4Factoidal.RIF.DatatypeInteropTests

#guard inLexicalSpace "dayTimeDuration" "P1M" == some false
#guard inLexicalSpace "dayTimeDuration" "PT1M" == some true
#guard inLexicalSpace "dayTimeDuration" "P1Y" == some false
#guard inLexicalSpace "yearMonthDuration" "P1M" == some true
#guard inLexicalSpace "yearMonthDuration" "PT1M" == some false
#guard inLexicalSpace "language" "en-US" == some true
#guard inLexicalSpace "language" "123" == some false
#guard inLexicalSpace "Name" "1bad" == some false
#guard inLexicalSpace "NCName" "a:b" == some false
#guard inLexicalSpace "NCName" "étiquette" == some true
#guard inLexicalSpace "NMTOKEN" "two words" == some false
#guard inLexicalSpace "base64Binary" "TQ==" == some true
#guard inLexicalSpace "base64Binary" "TQ=" == some false
#guard inLexicalSpace "hexBinary" "0aFF" == some true
#guard inLexicalSpace "hexBinary" "abc" == some false
#guard inLexicalSpace "byte" "128" == some false
#guard inLexicalSpace "unsignedByte" "255" == some true
#guard inLexicalSpace "unsignedByte" "256" == some false
#guard inLexicalSpace "dateTimeStamp" "2000-01-01T00:00:00" == some false
#guard inLexicalSpace "date" "0000-02-29" == some true
#guard inLexicalSpace "double" "+INF" == some true
#guard inLexicalSpace "unrecognised" "x" == none

#guard evalPred "is-literal-dayTimeDuration" [gLit "P1M" (xsdNs ++ "dayTimeDuration")] == .unknown
#guard evalPred "is-literal-base64Binary" [gLit "TQ==" (xsdNs ++ "base64Binary")] == .yes
#guard evalPred "is-literal-language" [gLit "123" (xsdNs ++ "language")] == .unknown
#guard (evalFunc "cast-dayTimeDuration" [gStr "P1M"]).isNone
#guard (evalFunc "cast-base64Binary" [gStr "TQ=="]).isSome
#guard numericLex (gLit "1.00e2" (xsdNs ++ "double")) == some "100"
#guard numericLex (gLit "128" (xsdNs ++ "byte")) == none
#guard numericLex (gLit "1.0" (xsdNs ++ "decimal")) == some "1"
#guard evalPred "numeric-equal" [gLit "1.00e2" (xsdNs ++ "double"),
  gLit "100" (xsdNs ++ "integer")] == .yes
#guard boolValue (gLit "1" (xsdNs ++ "boolean")) == some true
#guard boolValue (gLit "TRUE" (xsdNs ++ "boolean")) == none

end L4Factoidal.RIF.DatatypeInteropTests
