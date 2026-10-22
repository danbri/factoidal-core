import L4Factoidal.RIF.Builtins

namespace L4Factoidal.RIF.CastTests
private def n (s dt : String) := gLit s (xsdNs ++ dt)
private def cast (target s source : String) := evalFunc ("cast-" ++ target) [n s source]

-- Initial regressions, before the shared value-conversion migration.
#guard cast "integer" "1.9" "decimal" == some (n "1" "integer")
#guard cast "integer" "-1.9" "double" == some (n "-1" "integer")
#guard cast "boolean" "2" "integer" == some (n "true" "boolean")
#guard cast "integer" "true" "boolean" == some (n "1" "integer")
#guard cast "integer" " \t+12\n" "string" == some (n "12" "integer")
#guard cast "integer" "2008" "gYear" == none
#guard cast "integer" "128" "byte" == none
#guard cast "hexBinary" "TQ==" "base64Binary" == some (n "4D" "hexBinary")
#guard cast "date" "2008-07-22T12:34:56Z" "dateTime" == some (n "2008-07-22Z" "date")
#guard cast "string" "1" "boolean" == some (n "true" "string")

#guard cast "byte" "127.9" "decimal" == some (n "127" "byte")
#guard cast "byte" "128.1" "decimal" == none
#guard cast "unsignedInt" "-1.9" "decimal" == none
#guard cast "integer" "1.9" "string" == none
#guard cast "boolean" "NaN" "double" == some (n "false" "boolean")
#guard cast "boolean" "INF" "double" == some (n "true" "boolean")
#guard cast "boolean" "1e-50" "float" == some (n "false" "boolean")
#guard cast "integer" "INF" "double" == none
#guard cast "decimal" "NaN" "float" == none
#guard cast "integer" "16777217" "float" == some (n "16777216" "integer")
#guard cast "decimal" "0.1" "double" ==
  some (n "0.1000000000000000055511151231257827021181583404541015625" "decimal")
#guard cast "base64Binary" "4d" "hexBinary" == some (n "TQ==" "base64Binary")
#guard cast "string" "4d" "hexBinary" == some (n "4D" "string")
#guard cast "string" "01.00" "decimal" == some (n "1" "string")
#guard cast "string" "-0" "double" == some (n "-0" "string")
#guard cast "string" "1e6" "double" == some (n "1.0E6" "string")
#guard cast "string" "1.5" "double" == some (n "1.5" "string")
#guard cast "token" " \t one   two\n" "string" == some (n "one two" "token")
#guard cast "integer" "1" "anyURI" == none
#guard cast "boolean" "1" "base64Binary" == none
#guard cast "integer" "1" "unknown" == none
#guard cast "anyAtomicType" "hello" "string" == none
#guard cast "QName" "p:n" "string" == none
#guard cast "dateTime" "2008-07-22Z" "date" == some (n "2008-07-22T00:00:00Z" "dateTime")
#guard cast "dateTimeStamp" "2008-07-22" "date" == none
#guard cast "time" "2008-07-22T12:34:56+01:00" "dateTime" == some (n "12:34:56+01:00" "time")
#guard cast "gMonthDay" "2008-07-22Z" "date" == some (n "--07-22Z" "gMonthDay")
#guard cast "time" "2008-07-22Z" "date" == none
#guard cast "dateTime" "12:34:56Z" "time" == none
#guard cast "yearMonthDuration" "P2Y3M4DT5H" "duration" == some (n "P2Y3M" "yearMonthDuration")
#guard cast "dayTimeDuration" "P2Y3M4DT5H" "duration" == some (n "P4DT5H" "dayTimeDuration")
#guard cast "yearMonthDuration" "PT1S" "dayTimeDuration" == some (n "P0M" "yearMonthDuration")
#guard cast "dayTimeDuration" "P1M" "yearMonthDuration" == some (n "PT0S" "dayTimeDuration")
#guard evalFunc "cast-integer" [.const "12@" (rdfNs ++ "PlainLiteral")] == some (n "12" "integer")
#guard evalFunc "cast-integer" [.const "12@en" (rdfNs ++ "PlainLiteral")] == none

-- Narrowing is a cast operation, distinct from decimal lexical rounding.
private def value (target s source : String) := (cast target s source).bind numericValue?
#guard value "float" "16777219" "double" == numericValue? (n "16777218" "float")
#guard value "float" "16777219" "string" == numericValue? (n "16777220" "float")
#guard value "double" "16777217" "float" == numericValue? (n "16777216" "double")
#guard value "float" "-0" "double" == numericValue? (n "-0" "float")
#guard value "float" "INF" "double" == numericValue? (n "INF" "float")
#guard value "float" "1e100" "double" == numericValue? (n "INF" "float")
#guard value "float" "1e-100" "double" == numericValue? (n "0" "float")
#guard value "float" "170141183460469231731687303715884105728" "double" ==
  numericValue? (n "170141183460469231731687303715884105728" "float")
#guard value "float" "1.40129846432481707092372958328991613128026194187651577175706828388979108268586060148663818836212158203125e-45" "double" ==
  numericValue? (n "1.401298464324817e-45" "float")

end L4Factoidal.RIF.CastTests
