/- RDF 1.1 Concepts §3.3 literal term equality, extended recursively to
   RDF 1.2 triple terms. Separate from the store's historical XML-canonical
   `Term.eqb`: RDF term identity preserves XMLLiteral lexical spelling. -/
import L4Factoidal.RDF.Core

namespace L4Factoidal.RDF

/-- Literal identity retains lexical form and datatype, compares language tags
    case-insensitively, and retains RDF 1.2 base direction. -/
def Literal.sameTerm (a b : Literal) : Bool :=
  a.lexicalForm == b.lexicalForm && a.datatype == b.datatype &&
  langTagOptionEq a.langTag b.langTag && a.direction == b.direction

/-- RDF term identity, without datatype value conversion or XML canonicalization. -/
def Term.sameTerm : Term → Term → Bool
  | .iri a, .iri b => a == b
  | .bnode a, .bnode b => a == b
  | .literal a, .literal b => a.val.sameTerm b.val
  | .tripleTerm sa pa oa, .tripleTerm sb pb ob =>
      sa.eqb sb && pa == pb && oa.sameTerm ob
  | _, _ => false

@[simp] theorem Literal.sameTerm_refl (l : Literal) : l.sameTerm l = true := by
  simp [Literal.sameTerm]

/-- A well-formed untagged literal cannot carry a base direction. -/
theorem noDirection_of_noTag (l : WfLiteral) (h : l.val.langTag = none) :
    l.val.direction = none := by
  have hw := l.property
  cases hd : l.val.direction with
  | none => rfl
  | some d => simp [literalWf, h, hd] at hw

end L4Factoidal.RDF
