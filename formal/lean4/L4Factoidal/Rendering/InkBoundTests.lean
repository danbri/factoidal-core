import L4Factoidal.Rendering.InkBound

/-! Checks of the Stream-Safe Text Format and the ink boxes (`InkBound`). -/
namespace L4Factoidal.Rendering.InkBoundTests
open L4Factoidal.Rendering InkBound

private def marks (n : Nat) : List Char := 'n' :: List.replicate n '̈'

-- Up to 30 marks: unchanged.
#guard streamSafe (marks 30) == marks 30
-- 31 marks: one joiner before the 31st.
#guard streamSafe (marks 31) == 'n' :: (List.replicate 30 '̈' ++ [cgj,'̈'])
-- 10,000 marks: a joiner after each 30, and every run bounded.
#guard (streamSafe (marks 10000)).length == 10001 + 9999/30
#guard bounded 0 (streamSafe (marks 10000))
#guard (streamSafe (marks 10000)).filter (· != cgj) == marks 10000
-- Starters reset the count.
#guard streamSafe ("áb́".toList) == "áb́".toList
-- The source index of each output character.
#guard (sourceIndex (marks 31)).size == 33
#guard (sourceIndex (marks 31))[31]! == 31
#guard (sourceIndex (marks 31))[32]! == 31
#guard (sourceIndex (marks 31))[30]! == 30

-- Ink boxes.
private def box : Box := clusterBox 1000 1000 (-300) 0 500
#guard box == ⟨-31000,-31300,31500,32000⟩
-- Ordinary ink stays where the shaper put it.
#guard place box ⟨0,0,400,700⟩ 10 1200 == some (10,1200)
-- A mark stacked 40 em up comes down to the box.
#guard place box ⟨0,0,400,300⟩ 0 40000 == some (0,31700)
-- Ink larger than the box is not drawn.
#guard place box ⟨0,0,100000,10⟩ 0 0 == none
#guard unionAll [⟨0,0,1,1⟩,⟨-5,2,3,9⟩] == some ⟨-5,0,3,9⟩

end L4Factoidal.Rendering.InkBoundTests
