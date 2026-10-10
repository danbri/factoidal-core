import L4Factoidal.Syntax.Turtle

/-!
Streaming underscore scans preserve the original Turtle blank-node prefix.
These results concern character-list accumulation and parser-state initialization,
not UTF-8 decoding or the correctness of the Turtle grammar.
-/

namespace L4Factoidal.Syntax

#guard ((({} : UnderscoreRun).feedChars "a__".toList).feedChars "__b_".toList).longest == 4
#guard freshBnodePrefixOfLongest
  ((({} : UnderscoreRun).feedChars "a__".toList).feedChars "__b_".toList).longest == "anon_____"
#guard freshBnodePrefix "a____b_" == "anon_____"

namespace UnderscoreRun

theorem feedChar_current_le_longest (state : UnderscoreRun) (character : Char) :
    (state.feedChar character).current ≤ (state.feedChar character).longest := by
  simp only [feedChar]
  split
  · exact Nat.le_max_left _ _
  · exact Nat.zero_le _

theorem feedChars_longest_eq_maxUnderscoreRun (state : UnderscoreRun)
    (characters : List Char) (bounded : state.current ≤ state.longest) :
    (state.feedChars characters).longest =
      maxUnderscoreRun characters state.current state.longest := by
  induction characters generalizing state with
  | nil => simp only [feedChars, maxUnderscoreRun, Nat.max_eq_right bounded]
  | cons character rest inductionHypothesis =>
      rw [feedChars]
      rw [inductionHypothesis (state.feedChar character) (feedChar_current_le_longest state character)]
      simp only [maxUnderscoreRun, feedChar]
      split <;> rfl

theorem feedChars_append (state : UnderscoreRun) (first second : List Char) :
    state.feedChars (first ++ second) = (state.feedChars first).feedChars second := by
  induction first generalizing state with
  | nil => rfl
  | cons character rest inductionHypothesis =>
      simp only [List.cons_append, feedChars]
      exact inductionHypothesis (state.feedChar character)

theorem feedChars_chunks (state : UnderscoreRun) (chunks : List (List Char)) :
    chunks.foldl feedChars state = state.feedChars chunks.flatten := by
  induction chunks generalizing state with
  | nil => rfl
  | cons first rest inductionHypothesis =>
      simp only [List.foldl_cons, List.flatten_cons, feedChars_append]
      exact inductionHypothesis (state.feedChars first)

end UnderscoreRun

theorem freshBnodePrefixOfLongest_feedChars (text : String) :
    freshBnodePrefixOfLongest (({} : UnderscoreRun).feedChars text.toList).longest =
      freshBnodePrefix text := by
  rw [UnderscoreRun.feedChars_longest_eq_maxUnderscoreRun _ _ (Nat.le_refl 0)]
  rfl

theorem TurtleState.initWithBnodePrefix_feedChars (text : String) (base : Option String)
    (mode : Mode) :
    TurtleState.initWithBnodePrefix
      (freshBnodePrefixOfLongest (({} : UnderscoreRun).feedChars text.toList).longest) base mode =
      TurtleState.init text base mode := by
  rw [freshBnodePrefixOfLongest_feedChars]
  rfl

theorem freshBnodePrefixOfLongest_feedChunks (text : String) (chunks : List (List Char))
    (partition : chunks.flatten = text.toList) :
    freshBnodePrefixOfLongest (chunks.foldl UnderscoreRun.feedChars {}).longest =
      freshBnodePrefix text := by
  rw [UnderscoreRun.feedChars_chunks, partition]
  exact freshBnodePrefixOfLongest_feedChars text

#print axioms UnderscoreRun.feedChar_current_le_longest
#print axioms UnderscoreRun.feedChars_longest_eq_maxUnderscoreRun
#print axioms UnderscoreRun.feedChars_append
#print axioms UnderscoreRun.feedChars_chunks
#print axioms freshBnodePrefixOfLongest_feedChars
#print axioms freshBnodePrefixOfLongest_feedChunks
#print axioms TurtleState.initWithBnodePrefix_feedChars

end L4Factoidal.Syntax
