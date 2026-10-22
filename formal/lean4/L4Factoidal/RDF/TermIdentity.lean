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

/-- Strict RDF identity implies the historical coarse engine equality.
The converse is false for differently spelled XMLLiteral terms. -/
theorem Literal.eqb_of_sameTerm {a b : Literal} (h : a.sameTerm b = true) :
    a.eqb b = true := by
  simp only [Literal.sameTerm, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hl, hd⟩, ht⟩, hr⟩ := h
  simp [Literal.eqb, hl, hd, ht, hr]

theorem Term.eqb_of_sameTerm : ∀ {a b : Term}, a.sameTerm b = true → a.eqb b = true
  | .iri _, .iri _, h => h
  | .bnode _, .bnode _, h => h
  | .literal _, .literal _, h => Literal.eqb_of_sameTerm h
  | .tripleTerm _ _ _, .tripleTerm _ _ _, h => by
      simp only [Term.sameTerm, Bool.and_eq_true] at h
      simp only [Term.eqb, Bool.and_eq_true]
      exact ⟨h.1, Term.eqb_of_sameTerm h.2⟩
  | .iri _, .bnode _, h | .iri _, .literal _, h | .iri _, .tripleTerm _ _ _, h
  | .bnode _, .iri _, h | .bnode _, .literal _, h | .bnode _, .tripleTerm _ _ _, h
  | .literal _, .iri _, h | .literal _, .bnode _, h | .literal _, .tripleTerm _ _ _, h
  | .tripleTerm _ _ _, .iri _, h | .tripleTerm _ _ _, .bnode _, h
  | .tripleTerm _ _ _, .literal _, h => by simp [Term.sameTerm] at h

/-- Existing coarse hash buckets remain sound for strict identity, provided
bucket membership itself uses strict identity. -/
theorem Term.joinKey_eq_of_sameTerm {a b : Term} (h : a.sameTerm b = true) :
    a.joinKey = b.joinKey := Term.joinKey_eq_of_eqb (Term.eqb_of_sameTerm h)

/-- A well-formed untagged literal cannot carry a base direction. -/
theorem noDirection_of_noTag (l : WfLiteral) (h : l.val.langTag = none) :
    l.val.direction = none := by
  have hw := l.property
  cases hd : l.val.direction with
  | none => rfl
  | some d => simp [literalWf, h, hd] at hw

end L4Factoidal.RDF
