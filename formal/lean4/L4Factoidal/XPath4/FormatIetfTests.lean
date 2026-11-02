import L4Factoidal.XPath4.Format

/- F&O 3.1/4.0 fn:parse-ietf-date: omitted seconds default to zero.
   The native stderr regression is tests/xpath4/parse-ietf-date-native.test.mjs:
   value checks alone do not catch a toNat! panic followed by fallback zero. -/
namespace L4Factoidal.XPath4.FormatIetfTests

private def parsed (input : String) : Option String :=
  match parseIetf input with
  | .ok value => some value.str
  | .error _ => none

#guard (decDigits L4Factoidal.XSD.Dec.zero).1.isEmpty
#guard parsed "Wed, 20 Aug 2014 19:36 GMT" == some "2014-08-20T19:36:00Z"
#guard parsed "Wed, 20 Aug 2014 19:36:00 GMT" == some "2014-08-20T19:36:00Z"
#guard parsed "Wed, 20 Aug 2014 19:36:00.25 GMT" == some "2014-08-20T19:36:00.25Z"
#guard parsed "Wed, 20 Aug 2014 19:36:01 GMT" == some "2014-08-20T19:36:01Z"
#guard parsed "Aug 20 24:00 2014" == some "2014-08-21T00:00:00Z"
end L4Factoidal.XPath4.FormatIetfTests
