import L4Factoidal.SPARQL.StoreBackend

namespace L4Factoidal.SPARQL.IndexedSearch

open L4Factoidal.RDF

/-- SPARQL 1.1 §18.3: an admitted exact object key cannot omit an
    engine-equal term in a different structural bucket. -/
theorem exactObjectKey_eq_of_eqb {key stored : Term}
    (safe : exactObjectIndexKeySafe key = true)
    (matched : key.eqb stored = true) : key = stored := by
  cases key with
  | iri name =>
      cases stored <;> simp_all [Term.eqb]
  | bnode name =>
      cases stored <;> simp_all [Term.eqb]
  | tripleTerm subject predicate object =>
      simp [exactObjectIndexKeySafe] at safe
  | literal literal =>
      cases stored with
      | iri name => simp [Term.eqb] at matched
      | bnode name => simp [Term.eqb] at matched
      | tripleTerm subject predicate object => simp [Term.eqb] at matched
      | literal other =>
          apply congrArg Term.literal
          apply Subtype.ext
          rcases literal with ⟨⟨lexical, datatype, language, direction⟩, wellFormed⟩
          rcases other with ⟨⟨otherLexical, otherDatatype, otherLanguage, otherDirection⟩,
            otherWellFormed⟩
          simp only [exactObjectIndexKeySafe, Bool.and_eq_true, bne_iff_ne] at safe
          have noLanguage : language = none := by
            cases language <;> simp_all
          simp only [Term.eqb, Literal.eqb, Bool.and_eq_true, beq_iff_eq] at matched
          obtain ⟨⟨⟨sameLexical, sameDatatype⟩, sameLanguage⟩, sameDirection⟩ := matched
          have sameText : lexical = otherLexical := by
            simpa [safe.2] using sameLexical
          have otherNoLanguage : otherLanguage = none := by
            cases otherLanguage <;> simp_all [langTagOptionEq]
          simp [sameText, sameDatatype, noLanguage, otherNoLanguage, sameDirection]

private theorem matching_subject {bound : PatternBound} {triple : Triple}
    {subject : Subject} (position : bound.s = some subject)
    (matched : boundMatches bound triple = true) : subject = triple.s := by
  unfold boundMatches at matched
  rw [position] at matched
  exact Subject.eqb_eq (Bool.and_eq_true.mp (Bool.and_eq_true.mp matched).1).1

private theorem matching_predicate {bound : PatternBound} {triple : Triple}
    {predicate : WfIri} (position : bound.p = some predicate)
    (matched : boundMatches bound triple = true) : predicate = triple.p := by
  unfold boundMatches at matched
  rw [position] at matched
  exact eq_of_beq (Bool.and_eq_true.mp (Bool.and_eq_true.mp matched).1).2

private theorem matching_object {bound : PatternBound} {triple : Triple}
    {object : Term} (position : bound.o = some object)
    (matched : boundMatches bound triple = true) : object.eqb triple.o = true := by
  unfold boundMatches at matched
  rw [position] at matched
  exact (Bool.and_eq_true.mp matched).2

private theorem filter_matches (graph : Graph) (bound : PatternBound)
    (keep : Triple → Bool)
    (retained : ∀ triple, boundMatches bound triple = true → keep triple = true) :
    tripleMatchesBound bound (graph.filter keep) = tripleMatchesBound bound graph := by
  induction graph with
  | nil => rfl
  | cons triple rest inductionHypothesis =>
      cases matched : boundMatches bound triple with
      | false =>
          cases kept : keep triple <;>
            simp [tripleMatchesBound, matched, kept, inductionHypothesis]
      | true =>
          have kept := retained triple matched
          simp [tripleMatchesBound, matched, kept, inductionHypothesis]

/-- SPARQL 1.1 §18.3: every well-formed index search is the ordered
    bound filter of its graph, including duplicate triples. -/
theorem igSearch_eq_filter (source : OWL.RL.Index) (graph : Graph)
    (valid : source.Wf graph) (bound : PatternBound) :
    igSearch source bound = tripleMatchesBound bound graph := by
  cases subject : bound.s with
  | some subjectValue =>
      cases predicate : bound.p with
      | some predicateValue =>
          simp only [igSearch, subject, predicate]
          rw [valid.withSubjPred_eq]
          unfold OWL.RL.withSubjPred
          apply filter_matches
          intro triple matched
          simp [matching_subject subject matched, matching_predicate predicate matched]
      | none =>
          simp only [igSearch, subject, predicate]
          rw [valid.withSubj_eq]
          unfold OWL.RL.withSubj
          apply filter_matches
          intro triple matched
          simp [matching_subject subject matched]
  | none =>
      cases predicate : bound.p with
      | some predicateValue =>
          cases object : bound.o with
          | none =>
              simp only [igSearch, subject, predicate, object]
              rw [valid.withPred_eq]
              unfold OWL.RL.withPred
              apply filter_matches
              intro triple matched
              simp [matching_predicate predicate matched]
          | some objectValue =>
              simp only [igSearch, subject, predicate, object]
              split
              next safe =>
                rw [valid.withPredObj_eq]
                unfold OWL.RL.withPredObj
                apply filter_matches
                intro triple matched
                have objectEqual := exactObjectKey_eq_of_eqb safe (matching_object object matched)
                simp [matching_predicate predicate matched, objectEqual]
              next =>
                rw [valid.withPred_eq]
                unfold OWL.RL.withPred
                apply filter_matches
                intro triple matched
                simp [matching_predicate predicate matched]
      | none =>
          cases object : bound.o with
          | none => simp only [igSearch, subject, predicate, object, OWL.RL.Index.toGraph, valid.all]
          | some objectValue =>
              simp only [igSearch, subject, predicate, object]
              split
              next safe =>
                rw [valid.withObj_eq]
                unfold OWL.RL.withObj
                apply filter_matches
                intro triple matched
                have objectEqual := exactObjectKey_eq_of_eqb safe (matching_object object matched)
                simp [objectEqual]
              next => simp only [OWL.RL.Index.toGraph, valid.all]

#print axioms exactObjectKey_eq_of_eqb
#print axioms igSearch_eq_filter

end L4Factoidal.SPARQL.IndexedSearch
