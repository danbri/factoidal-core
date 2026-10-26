/- Batch SRI2/OLI2 page selection. Share the directory array across probes
   and deduplicate exact page references before sorting them for reading. -/
import L4Factoidal.Storage.SubjectRowIndexWireV2

namespace L4Factoidal.Storage.SubjectRowIndexWireV2

def distinctPageRefsGo : List (Nat × PageRef) → Std.HashSet (Nat × PageRef) →
    List (Nat × PageRef) → List (Nat × PageRef)
  | [], _, reversed => reversed.reverse
  | page :: rest, seen, reversed =>
      if seen.contains page then distinctPageRefsGo rest seen reversed
      else distinctPageRefsGo rest (seen.insert page) (page :: reversed)

def distinctPageRefs (pages : List (Nat × PageRef)) : List (Nat × PageRef) :=
  distinctPageRefsGo pages ∅ []

def candidatePages (refs : List PageRef) (ids : List Nat) : List (Nat × PageRef) :=
  let directory := refs.toArray
  ((distinctPageRefs (ids.flatMap (pagesForArray directory))).toArray.qsort
    (fun left right => left.1 < right.1)).toList

end L4Factoidal.Storage.SubjectRowIndexWireV2
