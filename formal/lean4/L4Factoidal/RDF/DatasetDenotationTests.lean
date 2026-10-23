/-
L4Factoidal.RDF.DatasetDenotationTests — checks of `RDF/DatasetDenotation.lean`,
evaluated during `lake build` (https://github.com/danbri/factoidal/issues/975,
phase A1).

* A dataset with a repeated triple and the same set without the repeat have
  one denotation.
* An empty named graph is in the names of the denotation (RDF 1.1 Concepts
  section 4: a named graph can be empty).
* A triple whose object is an RDF 1.2 triple term is a member.
* Language tags: `"chat"@EN` and `"chat"@en` are different structurally
  (`DecidableEq Triple`), and one member of the denotation (RDF 1.1 Concepts
  section 3.3: "the value space of language tags is always in lower case").
* Negative cases: a triple that is not stated is not a member; a graph name
  that is not declared is not a name; a triple of the default graph is not a
  member of a named graph.

No executable imports this module.
-/
import L4Factoidal.RDF.DatasetDenotation

namespace L4Factoidal.RDF.DatasetDenotationTests

open L4Factoidal.RDF

private def a : WfIri := ⟨"http://example.org/a", by simp [isIri]⟩
private def b : WfIri := ⟨"http://example.org/b", by simp [isIri]⟩
private def p : WfIri := ⟨"http://example.org/p", by simp [isIri]⟩
private def g : Subject := .iri ⟨"http://example.org/g", by simp [isIri]⟩
private def h : Subject := .iri ⟨"http://example.org/h", by simp [isIri]⟩

private def t1 : Triple := ⟨.iri a, p, .iri b⟩
private def t2 : Triple := ⟨.iri b, p, .iri a⟩
private def tEN : Triple := ⟨.iri a, p, .literal (Literal.langString "chat" "EN")⟩
private def ten : Triple := ⟨.iri a, p, .literal (Literal.langString "chat" "en")⟩
/-- RDF 1.2: the object is the triple term `<<( a p b )>>`. -/
private def tTT : Triple := ⟨.iri a, p, .tripleTerm (.iri a) p (.iri b)⟩

private def withRepeat : Dataset := { default := [t1, t2, t1], named := [⟨g, [t2, t2]⟩] }
private def withoutRepeat : Dataset := { default := [t2, t1], named := [⟨g, [t2]⟩] }

/-! ## Repeated triples and order -/

#guard Dataset.SameB withRepeat withoutRepeat
#guard !withRepeat.IsSetB
#guard withoutRepeat.IsSetB

example : withRepeat.den = withoutRepeat.den :=
  Dataset.den_eq_of_sameB withRepeat withoutRepeat (by decide)

example : withRepeat.den = withRepeat.toSet.den := (Dataset.den_toSet withRepeat).symm

/-! ## An empty named graph -/

private def emptyNamed : Dataset := { default := [t1], named := [⟨g, []⟩] }

example : emptyNamed.den.names g := by decide
example : ¬ emptyNamed.den.names h := by decide
example : ¬ emptyNamed.den.graph (some g) t1 := by decide
example : emptyNamed.den.graph none t1 := by decide
-- The empty named graph is kept: the denotation differs from the one without it.
example : emptyNamed.den ≠ ({ default := [t1], named := [] } : Dataset).den := by
  intro e
  have hn : emptyNamed.den.names g := by decide
  rw [e] at hn
  exact absurd hn (by decide)

/-! ## RDF 1.2 triple terms -/

private def withTT : Dataset := { default := [], named := [⟨h, [tTT]⟩] }

example : withTT.den.graph (some h) tTT := by decide
example : ¬ withTT.den.graph none tTT := by decide
example : withTT.den.mem (some h, tTT) := by decide

/-! ## Language tags (RDF 1.1 Concepts section 3.3) -/

example : tEN ≠ ten := by decide
-- `String.toLower` does not reduce in the elaborator's `decide`; the kernel
-- evaluates it (`decide +kernel`, no `Lean.ofReduceBool`, see the axiom line).
private theorem tEN_eqb_ten : tEN.eqb ten = true := by decide +kernel
private theorem tEN_den_ten : ({ default := [tEN], named := [] } : Dataset).den.graph none ten := by
  decide +kernel
example : ({ default := [tEN], named := [] } : Dataset).den =
    ({ default := [ten], named := [] } : Dataset).den :=
  Dataset.den_eq_of_sameB _ _ (by decide +kernel)

#print axioms tEN_eqb_ten
#print axioms tEN_den_ten

/-! ## Negative cases -/

example : ¬ withoutRepeat.den.graph none tEN := by decide
example : ¬ withoutRepeat.den.graph (some g) t1 := by decide

end L4Factoidal.RDF.DatasetDenotationTests
