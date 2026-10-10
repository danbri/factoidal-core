/-
L4Factoidal.OWL.DirectCertTests — the certificate checker on small
ontologies, one positive and one negative case per rule, and the axiom
audit of the soundness theorems.

A negative case is the positive case with the axiom or assertion the
rule needs removed. A checker that accepted every certificate would
fail every negative guard.
-/
import L4Factoidal.OWL.DirectCert

namespace L4Factoidal.OWL

private def cA : Concept := .atom "A"
private def cB : Concept := .atom "B"
private def cC : Concept := .atom "C"

/-! ### Complement clash (leaf) -/
#guard checkCert { abox := [.inst "a" cA, .inst "a" (.neg cA)] } .close
#guard !checkCert { abox := [.inst "a" cA, .inst "a" (.neg cB)] } .close

/-! ### `owl:Nothing` (leaf) -/
#guard checkCert { abox := [.inst "a" .bot] } .close
#guard !checkCert { abox := [.inst "a" .top] } .close

/-! ### `tboxE`: `A ⊑ B`, `a : A`, `a : ¬B` -/
#guard checkCert { tbox := [(cA, cB)], abox := [.inst "a" cA, .inst "a" (.neg cB)] } .close
#guard !checkCert { tbox := [], abox := [.inst "a" cA, .inst "a" (.neg cB)] } .close

/-! ### The contrapositive: `A ⊑ B` gives `¬B ⊑ ¬A`, and `¬A ⊑ C` -/
#guard checkCert { tbox := [(cA, cB), (.neg cA, cC)],
                   abox := [.inst "a" (.neg cB), .inst "a" (.neg cC)] } .close
#guard !checkCert { tbox := [(cA, cB)],
                    abox := [.inst "a" (.neg cB), .inst "a" (.neg cC)] } .close

/-! ### The negation normal form of a TBox axiom: `A ⊑ ¬(B ⊔ C)` -/
#guard checkCert { tbox := [(cA, .neg (.disj cB cC))],
                   abox := [.inst "a" cA, .inst "a" cC] } .close
#guard !checkCert { tbox := [(cA, .neg (.disj cB cC))],
                    abox := [.inst "a" cC] } .close

/-! ### `conjI`: `A ⊓ B ⊑ C`, `a : A`, `a : B`, `a : ¬C` -/
#guard checkCert { tbox := [(.conj cA cB, cC)], abox := [.inst "a" cA, .inst "a" cB, .inst "a" (.neg cC)] }
  .close
#guard !checkCert { tbox := [(.conj cA cB, cC)], abox := [.inst "a" cA, .inst "a" (.neg cC)] }
  .close

/-! ### `disjI`: `A ⊔ B ⊑ C`, `a : B`, `a : ¬C` -/
#guard checkCert { tbox := [(.disj cA cB, cC)], abox := [.inst "a" cB, .inst "a" (.neg cC)] } .close
#guard !checkCert { tbox := [(.disj cA cB, cC)], abox := [.inst "a" (.neg cB), .inst "a" (.neg cC)] }
  .close

/-! ### `split`: `a : C ⊔ D`, `a : ¬C`, `a : ¬D` -/
#guard checkCert { abox := [.inst "a" (.disj cC cB), .inst "a" (.neg cC), .inst "a" (.neg cB)] }
  (.split "a" cC cB .close .close)
#guard !checkCert { abox := [.inst "a" (.disj cC cB), .inst "a" (.neg cC)] }
  (.split "a" cC cB .close .close)
-- A split on a union that is not derivable is rejected.
#guard !checkCert { abox := [.inst "a" (.neg cC), .inst "a" (.neg cB)] }
  (.split "a" cC cB .close .close)

/-! ### `exWit`: `a : ∃r.C ⊓ ∀r.¬C` -/
#guard checkCert { abox := [.inst "a" (.conj (.ex "r" cC) (.all "r" (.neg cC)))] }
  (.exWit "a" "r" cC "x" .close)
#guard !checkCert { abox := [.inst "a" (.ex "r" cC)] } (.exWit "a" "r" cC "x" .close)
-- A witness name already in use is rejected.
#guard !checkCert { abox := [.inst "a" (.conj (.ex "r" cC) (.all "r" (.neg cC)))] }
  (.exWit "a" "r" cC "a" .close)

/-! ### `exI` and a domain axiom: `∃r.⊤ ⊑ A`, `r(a, b)`, `a : ¬A` -/
#guard checkCert { tbox := [(.ex "r" .top, cA)], abox := [.rel "r" "a" "b", .inst "a" (.neg cA)] }
  .close
#guard !checkCert { tbox := [(.ex "r" .top, cA)], abox := [.rel "r" "b" "a", .inst "a" (.neg cA)] }
  .close

/-! ### A range axiom: `⊤ ⊑ ∀r.A`, `r(a, b)`, `b : ¬A` -/
#guard checkCert { tbox := [(.top, .all "r" cA)], abox := [.rel "r" "a" "b", .inst "b" (.neg cA)] }
  .close
#guard !checkCert { tbox := [(.top, .all "r" cA)], abox := [.rel "r" "b" "a", .inst "b" (.neg cA)] }
  .close

/-! ### Role box: `r ⊑ s`, transitivity -/
#guard checkCert { rbox := ⟨[("r", "s")], []⟩,
                   abox := [.rel "r" "a" "b", .inst "a" (.all "s" .bot)] } .close
#guard !checkCert { rbox := ⟨[("s", "r")], []⟩,
                    abox := [.rel "r" "a" "b", .inst "a" (.all "s" .bot)] } .close
#guard checkCert { rbox := ⟨[], ["r"]⟩,
                   abox := [.rel "r" "a" "b", .rel "r" "b" "c",
                            .inst "a" (.all "r" (.neg cC)), .inst "c" cC] } .close
#guard !checkCert { rbox := ⟨[], []⟩,
                    abox := [.rel "r" "a" "b", .rel "r" "b" "c",
                             .inst "a" (.all "r" (.neg cC)), .inst "c" cC] } .close

/-! ### `invE`: `InverseObjectProperties(r s)`, `r(a, b)`, `b : ∀s.⊥` -/
#guard checkCert { inv := [("r", "s")], abox := [.rel "r" "a" "b", .inst "b" (.all "s" .bot)] }
  .close
#guard !checkCert { abox := [.rel "r" "a" "b", .inst "b" (.all "s" .bot)] } .close
#guard checkCert { inv := [("s", "r")], abox := [.rel "r" "a" "b", .inst "b" (.all "s" .bot)] }
  .close

/-! ### Cardinality bounds (leaf): `≥ 2 r` against `≤ 1 r`; `∃r.C` against `≤ 0 r.C` -/
#guard checkCert { abox := [.inst "a" (.atLeast 2 "r"), .inst "a" (.atMost 1 "r")] } .close
#guard !checkCert { abox := [.inst "a" (.atLeast 2 "r"), .inst "a" (.atMost 2 "r")] } .close
#guard checkCert { abox := [.inst "a" (.ex "r" cC), .inst "a" (.atMostQ 0 "r" cC)] } .close
#guard !checkCert { abox := [.inst "a" (.ex "r" cB), .inst "a" (.atMostQ 0 "r" cC)] } .close

/-! ### Named successors (leaf): `≤ 1 r` with two `r`-successors that are `diff` -/
#guard checkCert { abox := [.inst "a" (.atMost 1 "r"), .rel "r" "a" "b", .rel "r" "a" "c",
                            .diff "b" "c"] } .close
#guard !checkCert { abox := [.inst "a" (.atMost 1 "r"), .rel "r" "a" "b", .rel "r" "a" "c"] }
  .close

/-! ### Named successors kept apart by complementary memberships (leaf) -/
#guard checkCert { abox := [.inst "a" (.atMost 1 "r"), .rel "r" "a" "b", .rel "r" "a" "c",
                            .inst "b" cC, .inst "c" (.neg cC)] } .close
#guard !checkCert { abox := [.inst "a" (.atMost 1 "r"), .rel "r" "a" "b", .rel "r" "a" "c",
                             .inst "b" cC] } .close

/-! ### `geWit`: `≥ 2 p`, `≥ 2 q`, `p, q ⊑ r`, `∀p.C`, `∀q.¬C` against `≤ 3 r` -/
private def minSumAbox : List Assertion :=
  [.inst "a" (.atLeast 2 "p"), .inst "a" (.atLeast 2 "q"), .inst "a" (.atMost 3 "r"),
   .inst "a" (.all "p" cC), .inst "a" (.all "q" (.neg cC))]
#guard checkCert { rbox := ⟨[("p", "r"), ("q", "r")], []⟩, abox := minSumAbox }
  (.geWit "a" "p" .top ["x1", "x2"] (.geWit "a" "q" .top ["y1", "y2"] .close))
-- Without `∀q.¬C` the two groups may overlap: four names, possibly three elements.
#guard !checkCert { rbox := ⟨[("p", "r"), ("q", "r")], []⟩, abox := minSumAbox.take 4 }
  (.geWit "a" "p" .top ["x1", "x2"] (.geWit "a" "q" .top ["y1", "y2"] .close))
-- More witnesses than the bound licenses are rejected.
#guard !checkCert { rbox := ⟨[("p", "r"), ("q", "r")], []⟩, abox := minSumAbox }
  (.geWit "a" "p" .top ["x1", "x2", "x3"] (.geWit "a" "q" .top ["y1", "y2"] .close))
-- A witness name already in use is rejected.
#guard !checkCert { rbox := ⟨[("p", "r"), ("q", "r")], []⟩, abox := minSumAbox }
  (.geWit "a" "p" .top ["a", "x2"] (.geWit "a" "q" .top ["y1", "y2"] .close))

/-! ### `merge`: a functional role (`⊤ ⊑ ≤ 1 r`) identifies `b` and `c` -/
#guard checkCert { tbox := [(.top, .atMost 1 "r")],
                   abox := [.rel "r" "a" "b", .rel "r" "a" "c", .inst "b" cC, .inst "c" (.neg cC)] }
  (.merge "a" 1 "r" ["b", "c"] (.cons "b" "c" .close .nil))
#guard !checkCert { tbox := [(.top, .atMost 1 "r")],
                    abox := [.rel "r" "a" "b", .rel "r" "a" "c", .inst "b" cC] }
  (.merge "a" 1 "r" ["b", "c"] (.cons "b" "c" .close .nil))
-- A qualified bound `≤ 1 r.C` licenses the merge of two successors in `C`.
#guard checkCert { abox := [.inst "a" (.atMostQ 1 "r" cB), .rel "r" "a" "b", .rel "r" "a" "c",
                            .inst "b" cB, .inst "c" cB, .inst "b" cC, .inst "c" (.neg cC)] }
  (.merge "a" 1 "r" ["b", "c"] (.cons "b" "c" .close .nil))
#guard !checkCert { abox := [.inst "a" (.atMostQ 1 "r" cB), .rel "r" "a" "b", .rel "r" "a" "c",
                             .inst "b" cB, .inst "b" cC, .inst "c" (.neg cC)] }
  (.merge "a" 1 "r" ["b", "c"] (.cons "b" "c" .close .nil))
-- Without the bound the merge is not licensed.
#guard !checkCert { abox := [.rel "r" "a" "b", .rel "r" "a" "c", .inst "b" cC, .inst "c" (.neg cC)] }
  (.merge "a" 1 "r" ["b", "c"] (.cons "b" "c" .close .nil))

/-! ### `SameIndividual` as a renaming: `DifferentIndividuals(a b)` with `a = b` -/
#guard checkCert { same := [("a", "b")], abox := [.diff "a" "b"] } .close
#guard !checkCert { abox := [.diff "a" "b"] } .close
#guard checkCert { same := [("b", "a")], abox := [.inst "a" cC, .inst "b" (.neg cC)] } .close
#guard !checkCert { same := [("b", "c")], abox := [.inst "a" cC, .inst "b" (.neg cC)] } .close

/-! ### Axiom audit -/
/-- info: 'L4Factoidal.OWL.checkCert_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms checkCert_sound
/-- info: 'L4Factoidal.OWL.sem_nnfP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms sem_nnfP

end L4Factoidal.OWL
