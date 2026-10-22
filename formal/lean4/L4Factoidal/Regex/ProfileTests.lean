import L4Factoidal.Regex.Profiles
import L4Factoidal.JSONSchema.Validate

namespace L4Factoidal.Regex.Profiles

#guard (matchWith .xsd10 "a" "" "cat").toOption == some false
#guard (matchWith .xpath20 "a" "" "cat").toOption == some true
#guard (matchWith .ecma2020 "a" "" "cat").toOption == some true
#guard (matchWith .xsd10 "^a$" "" "^a$").toOption == some true
#guard (matchWith .xsd10 "^a$" "" "a").toOption == some false
#guard (matchWith .xpath20 "^a$" "" "a").toOption == some true
#guard (matchWith .ecma2020 "\\w+" "" "_").toOption == some true
#guard (matchWith .xsd10 "\\w+" "" "_").toOption.isNone
#guard (matchWith .xpath20 "a" "q" "a").toOption.isNone
#guard (matchWith .ecma2020 "(?=a)a" "" "a").toOption.isNone
#guard (matchWith .ecma2020 "\\s" "" " ").toOption == some true
#guard (matchWith .ecma2020 "." "" "😀").toOption.isNone
#guard L4Factoidal.JSONSchema.patternMatch "(?=a)a" "a" == .unsupported
#guard L4Factoidal.JSONSchema.validate
  (.object [("patternProperties", .object [("(?=a)a", .bool false)]),
            ("additionalProperties", .bool false)]) (.object [("a", .null)]) == .unsupported
#guard (matchSparql "a?+*.{}()[]c" "q" "a?+*.{}()[]c").toOption == some true
-- A hyphen BETWEEN classes is concatenation, not XSD class subtraction.
#guard (matchWith .xpath20 "^[0-9A-F]{8}-[0-9A-F]{4}$" "i" "0123abcd-ABCD").toOption == some true
#print axioms matchWith
end L4Factoidal.Regex.Profiles
