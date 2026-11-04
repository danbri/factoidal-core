import Geometry

namespace NativeGeometry.Tests
open NativeGraphics NativeGeometry
private def black : RGB := ⟨0,0,0⟩
private def rect (x y w h : Nat) : Shape := .rectangle ⟨x,y⟩ ⟨w,h⟩ black
private def blank : GlyphRows := ⟨0,0,0,0,0,0,0⟩
private def dot : GlyphRows := ⟨16,0,0,0,0,0,1⟩
#guard (Box.mk (-2) (-3) 4 5).area == 48
#guard (Box.mk 5 5 1 1).area == 0
#guard (Box.mk 0 0 4 5).contains 0 0
#guard !(Box.mk 0 0 4 5).contains 4 0
#guard ((Box.mk 0 0 4 4).intersection ⟨4,0,6,4⟩).area == 0
#guard ((Box.mk 0 0 4 4).union ⟨10,10,12,12⟩).area == 144
#guard hit (.circle ⟨3,3⟩ 5 black) 6 7 == some true
#guard hit (.circle ⟨3,3⟩ 5 black) 7 7 == some false
#guard hit (rect 2 3 4 5) 6 8 == some true
#guard hit (rect 2 3 4 5) 7 8 == some false
#guard hit (.segment ⟨0,0⟩ ⟨10,0⟩ 3 black) 5 1 == some true
#guard hit (.segment ⟨0,0⟩ ⟨10,0⟩ 3 black) 5 2 == some false
#guard hit (.segment ⟨10,0⟩ ⟨0,0⟩ 3 black) 5 1 == some true
#guard hit (.segment ⟨0,0⟩ ⟨0,0⟩ 4 black) (-2) 0 == some true
#guard hit (.segment ⟨0,0⟩ ⟨10,10⟩ 2 black) 5 6 == some true
#guard hit (.segment ⟨0,0⟩ ⟨10,10⟩ 2 black) 5 7 == some false
#guard hit (.quadratic ⟨0,0⟩ ⟨5,5⟩ ⟨10,0⟩ 2 black) 5 2 == none
#guard hit (.glyph ⟨10,10⟩ 2 dot black) 10 10 == some true
#guard hit (.glyph ⟨10,10⟩ 2 dot black) 12 10 == some false
#guard hit (.glyph ⟨10,10⟩ 2 dot black) 19 23 == some true
#guard hit (.glyph ⟨10,10⟩ 2 dot black) 20 23 == some false
#guard hit (.glyph ⟨10,10⟩ 0 dot black) 10 10 == some false
#guard footprint [.glyph ⟨1000,1000⟩ 2 blank black] == none
#guard footprint [.glyph ⟨1000,1000⟩ 0 dot black, rect 1 2 3 4] == some ⟨1,2,5,7⟩
#guard bounds (.circle ⟨0,0⟩ 3 black) == ⟨-3,-3,4,4⟩
#guard bounds (.cubic ⟨0,0⟩ ⟨20,30⟩ ⟨40,10⟩ ⟨5,5⟩ 3 black) == ⟨-2,-2,43,33⟩
#guard withinBudget 100 5
#guard !withinBudget 100 6
#guard !withinBudget 0 0
-- Three identical boxes: the pairwise sum is 200, although the union is 100.
#guard overlapSum ⟨0,0,10,10⟩ [⟨0,0,10,10⟩,⟨0,0,10,10⟩] == 200
#guard (checkLayout [[rect 0 0 9 9],[rect 30 0 9 9]]).all (·.accepted)
#guard !(checkLayout [[rect 0 0 9 9],[rect 0 0 9 9]]).any (·.accepted)
#guard !(checkLayout [[]]).any (·.accepted)
#guard (checkLayout [[rect 0 0 9 9]]).all (·.accepted)
-- Actual layout threshold, not only the arithmetic helper: 5% passes, 6% fails.
#guard ((checkLayout [[rect 0 0 9 9],[rect 9 0 0 4]]).head?.map (·.accepted)) == some true
#guard ((checkLayout [[rect 0 0 9 9],[rect 9 0 0 5]]).head?.map (·.accepted)) == some false
-- A distant painted glyph participates; a distant blank glyph does not.
#guard footprint [rect 0 0 9 9,.glyph ⟨20,0⟩ 2 dot black] == some ⟨0,0,30,14⟩
#guard footprint [rect 0 0 9 9,.glyph ⟨20,0⟩ 2 blank black] == some ⟨0,0,10,10⟩
private def viewport : Box := ⟨0,0,10,10⟩
#guard (checkLayoutIn viewport [[rect 20 20 9 9]]).map (·.area) == [0]
#guard !(checkLayoutIn viewport [[rect 20 20 9 9]]).any (·.accepted)
#guard (checkLayoutIn viewport [[rect 8 0 9 9]]).map (·.footprint) == [some ⟨8,0,10,10⟩]
#guard (checkLayoutIn viewport [[rect 8 0 9 9]]).map (·.area) == [20]
#guard (checkLayoutIn viewport [[rect 8 0 9 9]]).all (·.accepted)
-- Two boxes overlap only outside the viewport; clipped overlap is zero.
#guard (checkLayoutIn viewport [[rect 8 0 9 9],[rect 12 0 9 9]]).map (·.overlapSum) == [0,0]
#guard (checkLayoutIn viewport [[],[rect 8 0 9 9],[rect 20 0 9 9]]).map (·.index) == [0,1,2]
#guard (checkLayoutIn viewport [[rect 0 0 9 9],[rect 9 0 0 4]]).map (·.accepted) == [true,false]
example (v : Box) (nodes : List (List Shape)) : (checkLayoutIn v nodes).length = nodes.length :=
  checkLayoutIn_length v nodes
example (v : Box) (nodes : List (List Shape)) (r : NodeCheck) (h : r ∈ checkLayoutIn v nodes) :
    r.accepted = true ↔ 0 < r.area ∧ 20*r.overlapSum ≤ r.area :=
  checkLayoutIn_accepted_iff v nodes r h
example (area sum : Nat) (h : withinBudget area sum = true) : 20*sum ≤ area :=
  ((withinBudget_iff area sum).mp h).2
example (a b : Box) (x y : Int) (h : (a.intersection b).Contains x y) : a.Contains x y :=
  ((Box.intersection_contains a b x y).mp h).1
end NativeGeometry.Tests
