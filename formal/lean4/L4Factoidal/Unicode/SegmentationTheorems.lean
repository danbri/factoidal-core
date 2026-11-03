/-
L4Factoidal.Unicode.SegmentationTheorems — the segments that
`Unicode.Segmentation` produces for a text are a partition of it
(https://github.com/danbri/factoidal/issues/1167, milestone 4).

Generic statement (`cutAt_flatten`): for any list `xs` and any boundary
array `bs`, cutting `xs` at `bs` gives pieces whose concatenation is `xs`.
It needs no hypothesis on `bs`: the pieces are sized by the differences of
consecutive boundaries, and what remains after the last piece is kept as a
final piece. The instances (`graphemes_join`, `words_join`,
`sentences_join`) say that the concatenation of the grapheme clusters, the
words and the sentences of a string is the string.

What is not proved here: that the boundaries are the ones the UAX #29
rules give. That is checked by the conformance files
(`tests/unicode/run.sh`).
-/
import L4Factoidal.Unicode.Segmentation

namespace L4Factoidal.Unicode.Segmentation

theorem cutSizesAux_flatten {α : Type} (ss : List Nat) :
    ∀ (xs : List α) (acc : List (List α)),
      (cutSizesAux ss xs acc).flatten = acc.reverse.flatten ++ xs := by
  induction ss with
  | nil =>
    intro xs acc
    cases xs with
    | nil => simp [cutSizesAux]
    | cons x xs => simp [cutSizesAux]
  | cons s ss ih =>
    intro xs acc
    simp only [cutSizesAux]
    rw [ih]
    simp [List.append_assoc]

/-- Cutting by sizes loses and adds nothing. -/
theorem cutSizes_flatten {α : Type} (ss : List Nat) (xs : List α) :
    (cutSizes ss xs).flatten = xs := by
  simp [cutSizes, cutSizesAux_flatten]

/-- Cutting at any boundary array gives a partition of the list. -/
theorem cutAt_flatten {α : Type} (xs : List α) (bs : Array Nat) :
    (cutAt xs bs).flatten = xs :=
  cutSizes_flatten _ _

/-- The pieces of `segmentsBy f s` concatenate to `s`, for any boundary
function `f`. -/
theorem segmentsBy_join (f : Array Char → Array Nat) (s : String) :
    ((segmentsBy f s).map String.toList).flatten = s.toList := by
  unfold segmentsBy
  rw [List.map_map]
  have h : (String.toList ∘ String.ofList) = (id : List Char → List Char) := by
    funext l
    simp
  rw [h, List.map_id]
  exact cutAt_flatten _ _

theorem graphemes_join (s : String) :
    ((graphemes s).map String.toList).flatten = s.toList :=
  segmentsBy_join _ _

theorem words_join (s : String) :
    ((words s).map String.toList).flatten = s.toList :=
  segmentsBy_join _ _

theorem sentences_join (s : String) :
    ((sentences s).map String.toList).flatten = s.toList :=
  segmentsBy_join _ _

-- `#print axioms` (checked 2026-10-29): cutAt_flatten uses propext and Quot.sound;
-- the three instances use propext, Classical.choice and Quot.sound.

end L4Factoidal.Unicode.Segmentation
