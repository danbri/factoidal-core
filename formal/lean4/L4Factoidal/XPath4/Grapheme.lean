/-
L4Factoidal.XPath4.Grapheme — F&O 4.0 fn:graphemes over the shared
Unicode 18.0.0 extended grapheme cluster implementation (UAX #29 rev49).
-/
import L4Factoidal.Unicode.Segmentation

namespace L4Factoidal.XPath4.Grapheme

/-- The extended grapheme clusters of a string (UAX #29 §3.1.1). -/
def graphemes (str : String) : List String :=
  L4Factoidal.Unicode.Segmentation.graphemes str

#guard graphemes "abc" == ["a", "b", "c"]
#guard graphemes "\r\n" == ["\r\n"]
#guard graphemes "éx" == ["é", "x"]

end L4Factoidal.XPath4.Grapheme
