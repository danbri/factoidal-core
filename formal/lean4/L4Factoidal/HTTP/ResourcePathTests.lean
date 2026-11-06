import L4Factoidal.HTTP.ResourcePath
import L4Factoidal.LWS.Binding

namespace L4Factoidal.HTTP.ResourcePath.Tests
open L4Factoidal.HTTP.ResourcePath

#guard normalizeText "/" == some "/"
#guard normalizeText "/folder/" == some "/folder/"
#guard normalizeText "/%61/%7e/%41/%2d/%2Ehidden" == some "/a/~/A/-/.hidden"
#guard normalizeText "/colon%3aname/%c3%a9" == some "/colon%3Aname/%C3%A9"
#guard normalizeText "/colon:name" == some "/colon:name"
#guard normalizeText "/%253A/%252e%252e/%252f" == some "/%253A/%252e%252e/%252f"
#guard normalizeText "/a+b;v=x:@!$&'()*," == some "/a+b;v=x:@!$&'()*,"
#guard ["", "relative", "//host", "/a//b", "/.", "/..", "/a/../b", "/%2e", "/%2e%2e/",
  "/.%2E/", "/%2f", "/%2F", "/%5c", "/%5C", "/%00", "/a\\b", "/%", "/%0", "/%gg",
  "/%FF", "/%C0%AF", "/%ED%A0%80", "/%F4%90%80%80", "/a?query", "/a#fragment",
  "/raw space", "/été", "/a\n"].all fun s => (normalizeText s).isNone
#guard ["/", "/a", "/folder/", "/colon%3aname", "/%61", "/%252f", "/%C3%A9"].all fun s =>
  match normalizeText s with
  | some out => L4Factoidal.LWS.validTarget out && normalizeText out == some out
  | none => false

-- Exhaustive one-byte escape classes: canonicalization is tested for every
-- ASCII byte that forms a valid non-dot single path segment.
#guard (List.range 128).all fun n =>
  let escaped := "/%" ++ String.ofList [L4Factoidal.Syntax.upperHexDigit (n/16),L4Factoidal.Syntax.upperHexDigit (n%16)]
  if n == 0 || n == 47 || n == 92 || n == 46 then (normalizeText escaped).isNone else
  let expected := if unreserved (Char.ofNat n) then "/" ++ String.singleton (Char.ofNat n) else escaped
  normalizeText escaped == some expected

example (input output : String) (h : normalizeText input = some output) :
    normalizeText output = some output := normalizeText_idempotent input output h
#print axioms normalizeText_idempotent
#print axioms unreserved_a_identity
#print axioms escaped_colon_case_identity
#print axioms reserved_colon_distinct
#print axioms escaped_percent_distinct
end L4Factoidal.HTTP.ResourcePath.Tests
