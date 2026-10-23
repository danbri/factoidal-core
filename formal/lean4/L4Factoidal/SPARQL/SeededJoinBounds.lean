import L4Factoidal.SPARQL.BgpRefinement
import L4Factoidal.SPARQL.IndexedEvalRefinement
import L4Factoidal.SPARQL.Invariants
import L4Factoidal.SPARQL.StorePlan

/-!
SPARQL 1.1 §§18.3 and 18.5: constraints used by a selective JOIN probe
must retain every reference match that can survive the original JOIN.
Lookup compatibility is deliberately weaker than solution compatibility:
it also describes a reference mapping extended during a planned BGP walk.
These lemmas concern admission of probes, not BGP planner reordering.
-/

namespace L4Factoidal.SPARQL.SeededJoin

open L4Factoidal.RDF L4Factoidal.SPARQL.StorePlan

def LookupCompatible (seed reference : Binding) : Prop :=
  ∀ {name : VarName} {left right : Term},
    seed.lookup name = some left → reference.lookup name = some right → left.eqb right = true

theorem lookupCompatible_of_extends (before after : Binding) (extends : Extends before after) :
    LookupCompatible before after := by
  intro name left right leftRead rightRead
  have same := (extends name left leftRead).symm.trans rightRead
  cases Option.some.inj same
  exact Term.eqb_refl _

theorem lookupCompatible_merge (shadow seed reference : Binding)
    (extends : Extends shadow reference) (compatible : seed.compatible reference = true) :
    LookupCompatible (shadow.merge seed) reference := by
  intro name left right leftRead rightRead
  rw [Binding.lookup_merge] at leftRead
  cases shadowRead : shadow.lookup name with
  | none =>
      rw [shadowRead] at leftRead
      exact Binding.compatible_lookup compatible leftRead rightRead
  | some value =>
      rw [shadowRead] at leftRead
      cases leftRead
      exact lookupCompatible_of_extends shadow reference extends shadowRead rightRead

private theorem subject_equal_of_terms {left right : Term} {leftSubject rightSubject : Subject}
    (equal : left.eqb right = true)
    (leftRead : left.toSubject? = some leftSubject)
    (rightRead : right.toSubject? = some rightSubject) : leftSubject = rightSubject := by
  have terms := Term.eqb_eq_of_toSubject equal rightRead
  subst terms
  exact Option.some.inj (leftRead.symm.trans rightRead)

theorem compatible_instObject (seed reference : Binding)
    (compatible : LookupCompatible seed reference) :
    ∀ (pattern : PatternTerm) {left right : Term},
      instObject id seed pattern = some left →
      instObject id reference pattern = some right → left.eqb right = true := by
  intro pattern
  induction pattern with
  | iri name =>
      intro left right leftRead rightRead
      simp only [instObject, Option.some.injEq] at leftRead rightRead
      subst left; subst right
      exact Term.eqb_refl _
  | bnode name =>
      intro left right leftRead rightRead
      simp only [instObject, id_eq, Option.some.injEq] at leftRead rightRead
      subst left; subst right
      exact Term.eqb_refl _
  | literal value =>
      intro left right leftRead rightRead
      simp only [instObject, Option.some.injEq] at leftRead rightRead
      subst left; subst right
      exact Term.eqb_refl _
  | var name =>
      intro left right leftRead rightRead
      exact compatible leftRead rightRead
  | tripleTerm subject predicate object subjectInduction predicateInduction objectInduction =>
      intro left right leftRead rightRead
      cases leftSubjectTermRead : instObject id seed subject with
      | none => simp [instObject, leftSubjectTermRead] at leftRead
      | some leftSubjectTerm =>
          cases leftSubjectRead : leftSubjectTerm.toSubject? with
          | none => simp [instObject, leftSubjectTermRead, leftSubjectRead] at leftRead
          | some leftSubject =>
              cases leftPredicateRead : instObject id seed predicate with
              | none => simp [instObject, leftSubjectTermRead, leftSubjectRead, leftPredicateRead] at leftRead
              | some leftPredicate =>
                  cases leftPredicate <;>
                    simp only [instObject, leftSubjectTermRead, leftSubjectRead, leftPredicateRead] at leftRead
                  all_goals try contradiction
                  rename_i leftPredicate
                  cases leftObjectRead : instObject id seed object with
                  | none => simp [leftObjectRead] at leftRead
                  | some leftObject =>
                      simp only [leftObjectRead, Option.some.injEq] at leftRead
                      subst left
                      cases rightSubjectTermRead : instObject id reference subject with
                      | none => simp [instObject, rightSubjectTermRead] at rightRead
                      | some rightSubjectTerm =>
                          cases rightSubjectRead : rightSubjectTerm.toSubject? with
                          | none => simp [instObject, rightSubjectTermRead, rightSubjectRead] at rightRead
                          | some rightSubject =>
                              cases rightPredicateRead : instObject id reference predicate with
                              | none => simp [instObject, rightSubjectTermRead, rightSubjectRead, rightPredicateRead] at rightRead
                              | some rightPredicate =>
                                  cases rightPredicate <;>
                                    simp only [instObject, rightSubjectTermRead, rightSubjectRead, rightPredicateRead] at rightRead
                                  all_goals try contradiction
                                  rename_i rightPredicate
                                  cases rightObjectRead : instObject id reference object with
                                  | none => simp [rightObjectRead] at rightRead
                                  | some rightObject =>
                                      simp only [rightObjectRead, Option.some.injEq] at rightRead
                                      subst right
                                      have subjects := subject_equal_of_terms
                                        (subjectInduction leftSubjectTermRead rightSubjectTermRead)
                                        leftSubjectRead rightSubjectRead
                                      have predicates := Term.eqb_iri
                                        (predicateInduction leftPredicateRead rightPredicateRead)
                                      simp only [Term.iri.injEq] at predicates
                                      subst subjects; subst predicates
                                      simpa [Term.eqb] using objectInduction leftObjectRead rightObjectRead

private theorem subject_variable_lookup (row : Binding) (name : VarName) (subject : Subject)
    (matched : instSubject id row (.var name) = some subject) :
    row.lookup name = some subject.toTerm := by
  cases lookup : row.lookup name with
  | none => simp [instSubject, lookup] at matched
  | some value =>
      cases value <;> simp_all [instSubject, Subject.toTerm]

theorem compatible_instSubject (seed reference : Binding)
    (compatible : LookupCompatible seed reference) (pattern : PatternSubject)
    {left right : Subject}
    (leftRead : instSubject id seed pattern = some left)
    (rightRead : instSubject id reference pattern = some right) : left = right := by
  cases pattern with
  | iri name => simpa [instSubject] using leftRead.symm.trans rightRead
  | bnode name => simpa [instSubject] using leftRead.symm.trans rightRead
  | tripleTerm _ _ _ => simp [instSubject] at leftRead
  | var name =>
      have terms := compatible
        (subject_variable_lookup seed name left leftRead)
        (subject_variable_lookup reference name right rightRead)
      have equal := Term.eqb_eq_of_toSubject terms (toTerm_toSubject? right)
      cases left <;> cases right <;> simpa [Subject.toTerm] using equal

private theorem predicate_variable_lookup (row : Binding) (name : VarName) (predicate : WfIri)
    (matched : constructPredicate (.var name) row = some predicate) :
    row.lookup name = some (.iri predicate) := by
  cases lookup : row.lookup name with
  | none => simp [constructPredicate, lookup] at matched
  | some value =>
      cases value <;> simp_all [constructPredicate]

theorem compatible_constructPredicate (seed reference : Binding)
    (compatible : LookupCompatible seed reference) (pattern : PatternTerm)
    {left right : WfIri}
    (leftRead : constructPredicate pattern seed = some left)
    (rightRead : constructPredicate pattern reference = some right) : left = right := by
  cases pattern with
  | iri name => simpa [constructPredicate] using leftRead.symm.trans rightRead
  | var name =>
      have terms := compatible
        (predicate_variable_lookup seed name left leftRead)
        (predicate_variable_lookup reference name right rightRead)
      simpa using Term.eqb_iri terms
  | _ => simp [constructPredicate] at leftRead

theorem boundSubject_eq_instSubject (pattern : PatternSubject) (row : Binding) :
    boundSubjectOfPattern pattern row = instSubject id row pattern := by
  cases pattern <;> rfl

theorem boundPredicate_eq_constructPredicate (pattern : PatternTerm) (row : Binding) :
    boundPredicateOfPattern pattern row = constructPredicate pattern row := by
  cases pattern <;> rfl

theorem boundObject_eq_instObject (pattern : PatternTerm) (row : Binding) :
    boundObjectOfPattern pattern row = instObject id row pattern := by
  induction pattern with
  | tripleTerm subject predicate object subjectInduction predicateInduction objectInduction =>
      simp only [boundObjectOfPattern, instObject, subjectInduction, predicateInduction, objectInduction]
  | _ => rfl

theorem instantiated_lookup_bound (seed reference : Binding) (pattern : TriplePattern)
    (compatible : LookupCompatible seed reference) (triple : Triple)
    (instantiated : instTriple id reference pattern = some triple) :
    boundMatches (patternBoundFor pattern seed) triple = true := by
  cases subjectRead : instSubject id reference pattern.s with
  | none => simp [instTriple, subjectRead] at instantiated
  | some subject =>
      cases predicateRead : constructPredicate pattern.p reference with
      | none => simp [instTriple, subjectRead, predicateRead] at instantiated
      | some predicate =>
          cases objectRead : instObject id reference pattern.o with
          | none => simp [instTriple, subjectRead, predicateRead, objectRead] at instantiated
          | some object =>
              simp only [instTriple, subjectRead, predicateRead, objectRead, Option.some.injEq] at instantiated
              subst triple
              have subjectKept : (match instSubject id seed pattern.s with
                  | none => true
                  | some candidate => candidate.eqb subject) = true := by
                cases seedRead : instSubject id seed pattern.s with
                | none => rfl
                | some candidate =>
                    simp [compatible_instSubject seed reference compatible pattern.s seedRead subjectRead]
              have predicateKept : (match constructPredicate pattern.p seed with
                  | none => true
                  | some candidate => candidate == predicate) = true := by
                cases seedRead : constructPredicate pattern.p seed with
                | none => rfl
                | some candidate =>
                    simp [compatible_constructPredicate seed reference compatible pattern.p seedRead predicateRead]
              have objectKept : (match instObject id seed pattern.o with
                  | none => true
                  | some candidate => candidate.eqb object) = true := by
                cases seedRead : instObject id seed pattern.o with
                | none => rfl
                | some candidate =>
                    exact compatible_instObject seed reference compatible pattern.o seedRead objectRead
              simp only [boundMatches, patternBoundFor, boundSubject_eq_instSubject,
                boundPredicate_eq_constructPredicate, boundObject_eq_instObject]
              rw [subjectKept, predicateKept, objectKept]
              rfl

theorem match_lookup_bound (probe initial : Binding) (pattern : TriplePattern) (triple : Triple)
    (reference : Binding) (matched : tpMatch pattern triple initial = some reference)
    (compatible : LookupCompatible probe reference) :
    boundMatches (patternBoundFor pattern probe) triple = true := by
  obtain ⟨instantiated, reads, equivalent⟩ := tpMatch_inst matched
  have kept := instantiated_lookup_bound probe reference pattern compatible instantiated reads
  exact (boundMatches_congr (patternBoundFor pattern probe) instantiated triple equivalent).symm.trans kept

theorem match_seed_bound (seed : Binding) (pattern : TriplePattern) (triple : Triple)
    (reference : Binding) (matched : tpMatch pattern triple [] = some reference)
    (compatible : seed.compatible reference = true) :
    boundMatches (patternBoundFor pattern seed) triple = true :=
  match_lookup_bound seed [] pattern triple reference matched
    (fun leftRead rightRead => Binding.compatible_lookup compatible leftRead rightRead)

#print axioms lookupCompatible_merge
#print axioms compatible_instObject
#print axioms match_lookup_bound

end L4Factoidal.SPARQL.SeededJoin
