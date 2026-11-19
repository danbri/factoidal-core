/-
# Lookup in a built TLI1 term index

The index records the original PTD1 dictionary positions before sorting by
serialised bytes. A successful search checks both the key and the RDF term.
https://github.com/danbri/factoidal-core/issues/634
-/
import L4Factoidal.Storage.TermLocalIndex

namespace L4Factoidal.Storage

open L4Factoidal.RDF

/-- Kind: canonical term identity.
    Says: the storage fold leaves each typed RDF term unchanged, including
    the object of a nested triple term.
    Does not say: an unchecked language-tag spelling is already canonical. -/
theorem TermFold.foldTerm_eq_self (t : Term) : TermFold.foldTerm t = t := by
  induction t with
  | iri _ => rfl
  | bnode _ => rfl
  | tripleTerm s p o ih => exact congrArg (Term.tripleTerm s p) ih
  | literal l =>
    change Sbm11.normalizeLit l = .literal l
    rw [Sbm11.normalizeLit_eq_fast]
    cases tag : l.val.langTag with
    | none => simp [Sbm11.normalizeLitFast, tag]
    | some lang =>
      have eqTag := congrArg Literal.langTag (Literal.joinKey_eq_self_of_wf l.property)
      have lower : lang.toLower = lang := by
        simpa only [Literal.joinKey, tag, Option.map_some, Option.some.injEq] using eqTag
      simp [Sbm11.normalizeLitFast, tag, lower]

namespace TermLocalIndex

/-- Kind: lookup soundness.
    Says: every successful lookup in the built index returns the original
    dictionary position of the requested RDF term, for any dictionary.
    Does not say: every present term is found, duplicate terms receive their
    first position, or a file reader selected the correct page. -/
theorem lookup_entriesOf_sound (terms : Array Term) (wanted : Term) (id : Nat)
    (found : lookup? (entriesOf terms) wanted = some id) :
    terms[id]? = some wanted := by
  simp only [lookup?] at found
  split at found <;> try contradiction
  rename_i entry selected
  have member : entry ∈ entriesOf terms := Array.mem_of_getElem? selected
  split at found <;> try contradiction
  rename_i matched
  have same : entry.term = TermFold.foldTerm wanted :=
    beq_iff_eq.mp (Bool.and_eq_true.mp matched).2
  rw [← Option.some.inj found, ← same.trans (TermFold.foldTerm_eq_self wanted)]
  exact ((mem_entriesOf_iff terms entry).mp member).1

#print axioms mem_entriesOf_iff
#print axioms TermFold.foldTerm_eq_self
#print axioms lookup_entriesOf_sound

end TermLocalIndex
end L4Factoidal.Storage
