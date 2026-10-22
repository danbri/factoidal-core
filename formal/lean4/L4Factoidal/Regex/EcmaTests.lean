import L4Factoidal.Regex.Profiles
import L4Factoidal.JSONSchema.Validate

namespace L4Factoidal.Regex.EcmaTests
open Profiles

private def ch (n : Nat) : String := String.singleton (Char.ofNat n)
private def runMatch (pat text : String) := (matchWith .ecma2020 pat "" text).toOption

#guard runMatch "^\\s$" (ch 0xA0) == some true
#guard runMatch "^\\s$" (ch 0x0B) == some true
#guard runMatch "^\\s$" (ch 0xFEFF) == some true
#guard runMatch "^\\S$" (ch 0xA0) == some false
#guard runMatch "^\\S$" (ch 0x200B) == some true
#guard runMatch "^\\v$" (ch 0x0B) == some true
#guard runMatch "^[\\s]$" (ch 0x2028) == some true
#guard runMatch "^[^\\s]$" (ch 0x2028) == some false
#guard runMatch "^[\\S]$" (ch 0x2028) == some false
#guard runMatch "^[^\\S]$" (ch 0x2028) == some true
#guard runMatch "^.$" (ch 0x2028) == some false
#guard runMatch "^.$" (ch 0x2029) == some false
#guard runMatch "^.$" (ch 0xA0) == some true
#guard runMatch "^[.]$" "." == some true
#guard runMatch "^\\.$" "." == some true
#guard runMatch "^\\\\s$" "\\s" == some true
-- ECMA-only expansion must not change XML/XPath's four whitespace characters.
#guard (matchWith .xpath20 "^\\s$" "" (ch 0x0B)).toOption == some false
#guard (matchWith .xsd10 "\\s" "" (ch 0xA0)).toOption == some false
#guard runMatch "." "😀" == none
#guard runMatch "(?=a)a" "a" == none

#guard JSONSchema.patternMatch "^\\s+$" (ch 0xA0) == .pass
#guard JSONSchema.patternMatch "^\\s+$" "x" == .fail
#guard JSONSchema.validate
  (.object [("patternProperties", .object [("^\\s$", .bool true)]),
            ("additionalProperties", .bool false)])
  (.object [(ch 0xA0, .null)]) == .pass
#guard JSONSchema.validate
  (.object [("patternProperties", .object [("^\\s$", .bool false)]),
            ("additionalProperties", .bool true)])
  (.object [(ch 0xA0, .null)]) == .fail

end L4Factoidal.Regex.EcmaTests
