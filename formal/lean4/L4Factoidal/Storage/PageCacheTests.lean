import L4Factoidal.Storage.PageCache

namespace L4Factoidal.Storage.PageCache

private def pages : List (Nat × Array Nat) :=
  [(4, #[40, 41]), (1, #[10]), (4, #[400]), (2 ^ 64, #[99])]

#guard lookup (ofList pages) 4 == some #[40, 41]
#guard lookup (ofList pages) (2 ^ 64) == some #[99]
#guard lookup (ofList pages) 3 == none
#guard term? (ofList pages) 2 9 == some 41
#guard term? (ofList pages) 2 3 == none
#guard term? (ofList pages) 2 6 == none
#guard term? (ofList pages) 0 9 == none
#guard (List.range 15).all fun id => term? (ofList pages) 2 id == termFromList? pages 2 id
#guard lookup (insert (ofList pages) 4 #[7]) 4 == some #[7]
#guard lookup (insert (ofList pages) 4 #[7]) 1 == some #[10]

end L4Factoidal.Storage.PageCache
