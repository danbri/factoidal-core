import L4Factoidal.HTML.CodePointTokenizer

namespace L4Factoidal.HTML

private def characterResult (r : Except String CodePointTokens) : Option (List Nat × List String) := do
  let .ok value := r | none
  let chars ← value.tokens.toList.mapM fun token => match token with
    | .character cp => some cp
    | .other _ => none
  return (chars, value.errors.toList)

#guard decodeUtf16Units [0xD83D, 0xDE00] == [0x1F600]
#guard decodeUtf16Units [0xD800, 97, 0xDFFF] == [0xD800, 97, 0xDFFF]
#guard characterResult (tokenizeUtf16 [0xDFFF]) ==
  some ([0xDFFF], ["surrogate-in-input-stream"])
#guard characterResult (tokenizeUtf16 [0xD800]) ==
  some ([0xD800], ["surrogate-in-input-stream"])
#guard characterResult (tokenizeUtf16 [97, 0xDFFF]) ==
  some ([97, 0xDFFF], ["surrogate-in-input-stream"])
#guard characterResult (tokenizeUtf16 [0xD800, 97]) ==
  some ([0xD800, 97], ["surrogate-in-input-stream"])
#guard characterResult (tokenizeUtf16 [0xD83D, 0xDE00]) == some ([0x1F600], [])
#guard characterResult (tokenizeUtf16 [0xFFFD]) == some ([0xFFFD], [])
#guard characterResult (tokenizeUtf16 [13, 10, 0xD800, 13, 97]) ==
  some ([10, 0xD800, 10, 97], ["surrogate-in-input-stream"])
-- A numeric reference to a surrogate is replaced, unlike a literal surrogate.
#guard characterResult (tokenizeCodePoints ("&#xD800;".toList.map Char.toNat).toArray) ==
  some ([0xFFFD], ["surrogate-character-reference"])
-- Do not silently place a surrogate into a scalar-only attribute value.
#guard (match tokenizeUtf16 [60,112,32,120,61,34,0xD800,34,62] with
  | .error _ => true | .ok _ => false)
#guard (match tokenizeCodePoints #[0x110000] with
  | .error _ => true | .ok _ => false)

#print axioms decodeUtf16Units_single
#print axioms decodeUtf16Units_eq_TR
end L4Factoidal.HTML
