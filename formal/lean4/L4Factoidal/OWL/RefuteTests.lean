/-
L4Factoidal.OWL.RefuteTests — build-time checks for the refutation
calculus.

Two kinds of check, and the second kind is the one that matters:

* a graph that HAS no model is refuted;
* a graph that HAS a model is NOT refuted.

The second kind is what a refuter gets wrong. `refute` answers
`some false` or `none`, so a consistent graph must come back `none`;
anything else is a fabricated contradiction, and a fabricated
contradiction turns a passing consistency test into a failing one
while looking exactly like progress.
-/
import L4Factoidal.OWL.Refute
import L4Factoidal.OWL.NegationGoals
import L4Factoidal.OWL.Tableau

namespace L4Factoidal.OWL.Refute

open L4Factoidal.RDF
open L4Factoidal.OWL
open L4Factoidal.OWL.RL

private def exC : WfIri := ⟨"http://e/C", rfl⟩
private def exD : WfIri := ⟨"http://e/D", rfl⟩
private def exP : WfIri := ⟨"http://e/P", rfl⟩
private def exQ : WfIri := ⟨"http://e/Q", rfl⟩
private def exI : WfIri := ⟨"http://e/i", rfl⟩
private def exY : WfIri := ⟨"http://e/y", rfl⟩
private def exZ : WfIri := ⟨"http://e/z", rfl⟩

private def indI : Subject := .iri exI
private def bn (b : String) : Subject := .bnode b
private def bnT (b : String) : Term := .bnode b

private def fuel : Nat := 40

private def refuted (g : Graph) : Bool := refute g fuel == some false

/-! ## Negation normal form -/

#guard ClassExpr.beq (nnf (.complement (.complement (.named exC)))) (.named exC)
#guard ClassExpr.beq (nnf (.complement (.intersection [.named exC, .named exD])))
                     (.union [.complement (.named exC), .complement (.named exD)])
#guard ClassExpr.beq (nnf (.complement (.someOf exP (.named exC))))
                     (.allOf exP (.complement (.named exC)))
#guard ClassExpr.beq (nnf (.complement (.minCard 2 exP))) (.maxCard 1 exP)
#guard ClassExpr.beq (nnf (.complement (.maxCard 2 exP))) (.minCard 3 exP)

/-! `¬(≥ 0 p)` is `⊥`, not `≤ -1 p`: every individual has at least
zero successors in every model, so the negation is unsatisfiable. -/
#guard ClassExpr.beq (nnf (.complement (.minCard 0 exP))) (.named owlNothing)

/-! `= 0 p` normalises to `≤ 0 p` ALONE. Keeping the tautological
`≥ 0 p` conjunct would put a label in the set that no axiom
left-hand side written `≤ 0 p` could ever match. -/
#guard ClassExpr.beq (nnf (.exactCard 0 exP)) (.maxCard 0 exP)
#guard ClassExpr.beq (nnf (.exactCard 2 exP))
                     (.intersection [.minCard 2 exP, .maxCard 2 exP])

/-! The negation of an unreadable expression DROPS the constraint.
Dropping one loses clashes; it never invents one. -/
#guard ClassExpr.beq (nnfNeg .unknown) .unknown

/-! ## Clashes on the label set -/

/-! `owl:Nothing` is empty in every model. -/
#guard refuted [⟨indI, rdfType, .iri owlNothing⟩]

/-! `C` and `¬C` on one individual. -/
private def gComplement : Graph :=
  [ ⟨indI, rdfType, .iri exC⟩,
    ⟨indI, rdfType, bnT "n"⟩,
    ⟨bn "n", owlComplementOf, .iri exC⟩ ]

#guard refuted gComplement

/-! Two disjoint classes on one individual. The disjointness axiom
gives `C ⊑ ¬D`, and the unfolding puts `¬D` beside `D`. -/
private def gDisjoint : Graph :=
  [ ⟨indI, rdfType, .iri exC⟩, ⟨indI, rdfType, .iri exD⟩,
    ⟨.iri exC, owlDisjointWith, .iri exD⟩ ]

#guard refuted gDisjoint

/-! `≥ 2 p` beside `≤ 1 p`. No successors need to exist for this: the
two bounds contradict each other outright. -/
/-! ## `≤ 0 p` with an asserted successor -/

private def cardLit (v : String) : Term :=
  .literal ⟨{ lexicalForm := v,
              datatype := ⟨"http://www.w3.org/2001/XMLSchema#nonNegativeInteger", rfl⟩,
              langTag := none, direction := none },
            by simp [literalWf, rdfLangString, rdfDirLangString, Subtype.ext_iff]⟩

private def gMaxZero : Graph :=
  [ ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlMaxCardinality, cardLit "0"⟩,
    ⟨indI, exP, .iri exY⟩ ]

#guard refuted gMaxZero

/-! ## `≤ 1 p` with two PROVABLY distinct successors

Two different IRIs are not enough — without `owl:differentFrom` they
may denote one individual, and a refuter that assumed otherwise would
be applying a unique-name assumption OWL does not make. -/

private def gMaxOneBase : Graph :=
  [ ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlMaxCardinality, cardLit "1"⟩,
    ⟨indI, exP, .iri exY⟩, ⟨indI, exP, .iri exZ⟩ ]

#guard !(refuted gMaxOneBase)
#guard refuted (gMaxOneBase ++ [⟨.iri exY, owlDifferentFrom, .iri exZ⟩])

/-! ## The `∀` rule pushes across successors -/

private def gAllValues : Graph :=
  [ ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlAllValuesFrom, .iri owlNothing⟩,
    ⟨indI, exP, .iri exY⟩ ]

#guard refuted gAllValues

/-! Without the successor there is nothing to push onto, and `∀` is
vacuously satisfiable. -/
#guard !(refuted (gAllValues.filter (fun t => t.p != exP)))

/-! ## An existential witness carries the filler

`∃ p.⊥` has no model: the witness would have to be in the empty
class. This needs the witness to be MINTED — the graph asserts no
`p`-successor at all. -/

private def gSomeBottom : Graph :=
  [ ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri owlNothing⟩ ]

#guard refuted gSomeBottom

/-! A witness is NOT counted against a cardinality bound: it may
coincide with an existing successor in some model. `∃ p.C` beside
`≤ 1 p` with one asserted successor is satisfiable, and a refuter
that counted the witness would say otherwise. -/

private def gWitnessNotCounted : Graph :=
  [ ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri exC⟩,
    ⟨indI, rdfType, bnT "m"⟩,
    ⟨bn "m", owlOnProperty, .iri exP⟩,
    ⟨bn "m", owlMaxCardinality, cardLit "1"⟩,
    ⟨indI, exP, .iri exY⟩ ]

#guard !(refuted gWitnessNotCounted)

/-! ## Union branching

`C ⊔ D` refutes the node only when BOTH disjuncts clash. -/

private def gUnionBothBad : Graph :=
  [ ⟨indI, rdfType, bnT "u"⟩,
    ⟨bn "u", owlUnionOf, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, .iri owlNothing⟩,
    ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, .iri owlNothing⟩,
    ⟨bn "l2", rdfRest, .iri rdfNil⟩ ]

#guard refuted gUnionBothBad

private def gUnionOneGood : Graph :=
  [ ⟨indI, rdfType, bnT "u"⟩,
    ⟨bn "u", owlUnionOf, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, .iri owlNothing⟩,
    ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, .iri exC⟩,
    ⟨bn "l2", rdfRest, .iri rdfNil⟩ ]

#guard !(refuted gUnionOneGood)

/-! ## `owl:FunctionalProperty` is a global `≤ 1 p` -/

private def gFunctional : Graph :=
  [ ⟨.iri exP, rdfType, .iri owlFunctionalProperty⟩,
    ⟨indI, rdfType, .iri exC⟩,
    ⟨indI, exP, .iri exY⟩, ⟨indI, exP, .iri exZ⟩,
    ⟨.iri exY, owlDifferentFrom, .iri exZ⟩ ]

#guard refuted gFunctional

/-! ## The role hierarchy makes a subproperty edge count

`q rdfs:subPropertyOf p` gives `EXT(q) ⊆ EXT(p)` in every model, so a
`q`-edge is a `p`-successor wherever one is counted. -/

private def gSubProperty : Graph :=
  [ ⟨.iri exQ, rdfsSubPropertyOf, .iri exP⟩,
    ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlMaxCardinality, cardLit "0"⟩,
    ⟨indI, exQ, .iri exY⟩ ]

#guard refuted gSubProperty

/-! ## Graph-level violations -/

/-! G1: an `owl:AllDifferent` list naming one member twice. -/
private def gAllDifferent : Graph :=
  [ ⟨bn "ad", rdfType, .iri owlAllDifferent⟩,
    ⟨bn "ad", owlMembers, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, .iri exY⟩,
    ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, .iri exY⟩,
    ⟨bn "l2", rdfRest, .iri rdfNil⟩ ]

#guard refuted gAllDifferent

/-! The same list with two members and no `owl:sameAs` between them is
fine: distinct NAMES are not distinct individuals, but a list may
name whatever it likes. -/
private def gAllDifferentOk : Graph :=
  [ ⟨bn "ad", rdfType, .iri owlAllDifferent⟩,
    ⟨bn "ad", owlMembers, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, .iri exY⟩,
    ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, .iri exZ⟩,
    ⟨bn "l2", rdfRest, .iri rdfNil⟩ ]

#guard !(refuted gAllDifferentOk)

/-! G3: `p owl:propertyDisjointWith p` makes `EXT(p)` empty, so any
triple using `p` is false in every model. The RL marker misses this
because it wants two DIFFERENT predicates. -/
#guard refuted [⟨.iri exP, owlPropertyDisjointWith, .iri exP⟩,
                ⟨indI, exP, .iri exY⟩]

/-! Declared but unused, the same axiom is satisfiable — `EXT(p)` is
simply empty. -/
#guard !(refuted [⟨.iri exP, owlPropertyDisjointWith, .iri exP⟩])

/-! G4: `rdf:nil` is the empty list and carries no `rdf:first`. -/
#guard refuted [⟨.iri rdfNil, rdfFirst, .iri exY⟩]

/-! ## Consistent graphs stay unrefuted

The check a refuter fails. Every graph here has a model, and every
one must come back `none`. -/

#guard !(refuted [])
#guard !(refuted [⟨indI, rdfType, .iri exC⟩])
#guard !(refuted [⟨indI, rdfType, .iri exC⟩, ⟨indI, rdfType, .iri exD⟩])
#guard !(refuted [⟨.iri exC, owlDisjointWith, .iri exD⟩,
                  ⟨indI, rdfType, .iri exC⟩,
                  ⟨.iri exY, rdfType, .iri exD⟩])
#guard !(refuted gWitnessNotCounted)
#guard !(refuted [⟨.iri exP, rdfType, .iri owlTransitiveProperty⟩,
                  ⟨indI, exP, .iri exY⟩, ⟨.iri exY, exP, .iri exZ⟩])

/-! An unreadable class expression constrains nothing. A refuter that
guessed at one would answer a question it had not read. -/
#guard !(refuted [⟨indI, rdfType, bnT "mystery"⟩,
                  ⟨bn "mystery", exP, .iri exC⟩])

/-! ## There is no `some true`

A quiet, clash-free expansion is `none`, not a claim of consistency:
this calculus is incomplete, so an open branch proves nothing. -/
#guard refute [⟨indI, rdfType, .iri exC⟩] fuel == none
#guard refute [] fuel == none

/-! ## The ≤-rule: identifying witness successors

`f1`, `f2` and `f3` are functional with `f3 ⊑ f1` and `f3 ⊑ f2`, and
`U ≡ ∃f1.p1 ⊓ ∃f2.¬p1 ⊓ ∃f3.p2`. An individual in `U` has an
`f1`-witness in `p1`, an `f2`-witness in `¬p1`, and an `f3`-witness
in `p2`. Functionality forces the `f3`-witness to BE the `f1`-witness
and BE the `f2`-witness, so one element is in `p1` and in `¬p1`.

No clash rule sees this without the ≤-rule: `clashForLabel`'s
`maxCard` case counts only PROVABLY DISTINCT successors and never
counts witnesses at all. Seventeen `WebOnt-description-logic`
inconsistency fixtures are this shape. -/

private def exU : WfIri := ⟨"http://e/U", rfl⟩
private def exP1 : WfIri := ⟨"http://e/p1", rfl⟩
private def exP2 : WfIri := ⟨"http://e/p2", rfl⟩
private def exF1 : WfIri := ⟨"http://e/f1", rfl⟩
private def exF2 : WfIri := ⟨"http://e/f2", rfl⟩
private def exF3 : WfIri := ⟨"http://e/f3", rfl⟩

private def gFunctionalMerge : Graph :=
  [ ⟨.iri exU, owlEquivalentClass, bnT "i"⟩,
    ⟨bn "i", owlIntersectionOf, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, bnT "r1"⟩, ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, bnT "r2"⟩, ⟨bn "l2", rdfRest, bnT "l3"⟩,
    ⟨bn "l3", rdfFirst, bnT "r3"⟩, ⟨bn "l3", rdfRest, .iri rdfNil⟩,
    ⟨bn "r1", owlOnProperty, .iri exF1⟩, ⟨bn "r1", owlSomeValuesFrom, .iri exP1⟩,
    ⟨bn "r2", owlOnProperty, .iri exF2⟩, ⟨bn "r2", owlSomeValuesFrom, bnT "nc"⟩,
    ⟨bn "nc", owlComplementOf, .iri exP1⟩,
    ⟨bn "r3", owlOnProperty, .iri exF3⟩, ⟨bn "r3", owlSomeValuesFrom, .iri exP2⟩,
    ⟨.iri exF1, rdfType, .iri owlFunctionalProperty⟩,
    ⟨.iri exF2, rdfType, .iri owlFunctionalProperty⟩,
    ⟨.iri exF3, rdfType, .iri owlFunctionalProperty⟩,
    ⟨.iri exF3, rdfsSubPropertyOf, .iri exF1⟩,
    ⟨.iri exF3, rdfsSubPropertyOf, .iri exF2⟩,
    ⟨bn "x", rdfType, .iri exU⟩ ]

#guard refuted gFunctionalMerge

/-! Drop the subproperty axioms and the same graph is satisfiable:
three separate successors on three unrelated functional properties
breach nothing. A refuter that merged them anyway would refute an
ontology with a model. -/

private def gNoSubProperty : Graph :=
  gFunctionalMerge.filter (fun t => t.p != rdfsSubPropertyOf)

#guard !(refuted gNoSubProperty)

/-! A named individual IS a merge candidate since 2026-09-07. The
merge records an identification and `labelsOf` / `successorsOf` pool
the group, so no state is half-rewritten; and offering only blank
nodes left every successor pair involving a named individual outside
the `≤`-rule's branch cover, which is what makes "every offered merge
closes" an argument at all (design record § 11.6).

A LITERAL is never a candidate: a literal and an IRI denote in
disjoint domains under OWL 2 Direct Semantics § 2.2, and two literals
with different values are already `provablyDistinct`. -/
#guard isMergeableTerm (.iri exP1)
#guard isMergeableTerm (bnT "w")
#guard !(isMergeableTerm (cardLit "1"))

/-! ## Closure scaffolding is inert

The OWL RL closure materialises `__rl_`-prefixed blank nodes as
support triples, with an encoding that is deliberately looser than
the class expression they resemble. Reading one literally
MANUFACTURES refutations of consistent premises. -/
#guard isScaffoldBNode (bnT "__rl_comp__http://e/C")
#guard !(isScaffoldBNode (bnT "ordinary"))

/-! ## `∃p.C` is discharged by a successor CARRYING `C`

Not by any successor at all. An existential whose filler is
anonymous gets an edge from the materialisation pass but no type, so
counting successors said "discharged", no witness was minted, and the
filler was never put on any node — the ≤-rule then pooled labels that
did not include it and every branch stayed open
(`WebOnt-description-logic-003` and its family; seven cases turned on
this one line). -/

private def gExistingSuccessorWrongClass : Graph :=
  [ ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri owlNothing⟩,
    ⟨indI, rdfType, bnT "r"⟩,
    -- An asserted p-successor that is NOT in the filler. The
    -- obligation is still open, so a witness must be minted and the
    -- filler put on it — which refutes, since the filler is empty.
    ⟨indI, exP, .iri exY⟩ ]

#guard refuted gExistingSuccessorWrongClass

/-! With the successor already in the filler the obligation IS
discharged and nothing is minted. -/

private def gExistingSuccessorRightClass : Graph :=
  [ ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri exC⟩,
    ⟨indI, rdfType, bnT "r"⟩,
    ⟨indI, exP, .iri exY⟩,
    ⟨.iri exY, rdfType, .iri exC⟩ ]

#guard !(refuted gExistingSuccessorRightClass)

/-! ## Four more graph-level violations

Each is a shape that has no model without any expansion at all, and
each is paired with the nearest SATISFIABLE graph — the pairing is
the check, because either half alone can be passed by an engine that
has the rule backwards. -/

/-! G6: OWL 2 Direct Semantics requires a NON-EMPTY domain and
interprets `owl:Thing` as the whole of it, so equating it with the
empty class has no model. -/
#guard refuted [⟨.iri owlThing, owlEquivalentClass, .iri owlNothing⟩]
#guard refuted [⟨.iri owlNothing, owlEquivalentClass, .iri owlThing⟩]
#guard !(refuted [⟨.iri exC, owlEquivalentClass, .iri owlNothing⟩])

/-! G7: two DIFFERENT properties declared disjoint, sharing a pair.
The RL marker wants two distinct predicates and so does this. -/
#guard refuted [⟨.iri exP, owlPropertyDisjointWith, .iri exQ⟩,
                ⟨indI, exP, .iri exY⟩, ⟨indI, exQ, .iri exY⟩]
/-! Different pairs on the same two properties are fine. -/
#guard !(refuted [⟨.iri exP, owlPropertyDisjointWith, .iri exQ⟩,
                  ⟨indI, exP, .iri exY⟩, ⟨indI, exQ, .iri exZ⟩])

/-! G8: `owl:AllDisjointProperties` asserts PAIRWISE disjointness. -/
private def gAllDisjointProps (o1 o2 : Term) : Graph :=
  [ ⟨bn "ad", rdfType, .iri owlAllDisjointProperties⟩,
    ⟨bn "ad", owlMembers, bnT "m1"⟩,
    ⟨bn "m1", rdfFirst, .iri exP⟩, ⟨bn "m1", rdfRest, bnT "m2"⟩,
    ⟨bn "m2", rdfFirst, .iri exQ⟩, ⟨bn "m2", rdfRest, .iri rdfNil⟩,
    ⟨indI, exP, o1⟩, ⟨indI, exQ, o2⟩ ]

#guard refuted (gAllDisjointProps (.iri exY) (.iri exY))
#guard !(refuted (gAllDisjointProps (.iri exY) (.iri exZ)))

/-! G9: asymmetry says `(x,y) ∈ EXT(p)` implies `(y,x) ∉ EXT(p)`;
irreflexivity says no pair `(x,x)` is in it. -/
#guard refuted [⟨.iri exP, rdfType, .iri owlAsymmetricProperty⟩,
                ⟨indI, exP, .iri exY⟩, ⟨.iri exY, exP, .iri exI⟩]
#guard !(refuted [⟨.iri exP, rdfType, .iri owlAsymmetricProperty⟩,
                  ⟨indI, exP, .iri exY⟩])
#guard refuted [⟨.iri exP, rdfType, .iri owlIrreflexiveProperty⟩,
                ⟨indI, exP, .iri exI⟩]
#guard !(refuted [⟨.iri exP, rdfType, .iri owlIrreflexiveProperty⟩,
                  ⟨indI, exP, .iri exY⟩])

/-! ## The three-valued verdict (issue 586)

`tableauConsistent` mirrors F* `tableau_consistent` meaning for
meaning: `some false` = clash, `some true` = quiescence, `none` =
budget out. `refute` is its refutation-only projection
(`refute_eq_false_iff`). -/

/-! Quiescence with no clash answers `some true` where `refute`
answers `none`. -/
#guard tableauConsistent [⟨indI, rdfType, .iri exC⟩] fuel == some true
#guard refute [⟨indI, rdfType, .iri exC⟩] fuel == none

/-! A clash answers `some false` through BOTH views. -/
#guard tableauConsistent gComplement fuel == some false
#guard refute gComplement fuel == some false

/-! A cyclic TBox (`A ⊑ ∃P.A`) keeps the expansion changing: budget 1
is exhausted mid-search and the verdict is `none` — indeterminate,
never collapsed into either Boolean. The SAME input at a working
budget saturates under the witness-depth cap and answers
`some true`. -/
private def gCyclicExists : Graph :=
  [ ⟨indI, rdfType, .iri exC⟩,
    ⟨.iri exC, rdfsSubClassOf, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exP⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri exC⟩ ]

#guard tableauConsistent gCyclicExists 1 == none
#guard tableauConsistent gCyclicExists fuel == some true
#guard refute gCyclicExists 1 == none

/-! ## Paired witness: procedural clash ↔ declarative `Refuted`

The same contradiction — `C` and `¬C` at one individual — refuted by
this module's search (the `#guard` above on `gComplement`) and by an
explicit derivation in the declarative calculus of
`OWL/Tableau.lean`. The pairing is the instance-level form of the
correspondence the module header states; the general abstraction is
the certificate-checker rung
(https://github.com/danbri/factoidal/issues/586 follow-up 6). -/
example : Refuted .empty [.inst "i" (.atom "C"), .inst "i" (.neg (.atom "C"))] :=
  .clash (.hyp (.head _)) (.hyp (.tail _ (.head _)))

/-! ## Negation goals (PE-via-refutation, issue 586)

Shape checks first, then two end-to-end verdicts. -/

/-! A class membership negates to ONE goal carrying the complement
pair. -/
#guard (negationGoals [⟨indI, rdfType, .iri exD⟩]).map List.length == some 1

/-! A subsumption negates to one goal; an equivalence to two (C ⊑ D
and D ⊑ C, both required). -/
#guard (negationGoals [⟨.iri exC, rdfsSubClassOf, .iri exD⟩]).map List.length
       == some 1
#guard (negationGoals [⟨.iri exC, owlEquivalentClass, .iri exD⟩]).map List.length
       == some 2

/-! A plain property assertion negates through the `≤0 p.{y}`
encoding — ten triples, no base. -/
#guard (negationGoals [⟨indI, exP, .iri exY⟩]).map (·.map List.length)
       == some [10]

/-! A property assertion with a LITERAL object has no `≤0 p.{y}`
negation (`owl:oneOf` of a literal is a data range). Since 2026-10-10
it negates to the negative property assertion instead — three triples,
`owl:sourceIndividual` / `owl:assertionProperty` / `owl:targetValue`
(this guard said `none` before that builder existed). A purely
structural conclusion has no content assertion to negate: `none`. -/
#guard (negationGoals
        [⟨indI, exP, .literal ⟨{ lexicalForm := "v", datatype := xsdString,
                                 langTag := none, direction := none }, rfl⟩⟩]).map
         (·.map List.length) == some [3]
#guard negationGoals [⟨bn "r", owlOnProperty, .iri exP⟩] == none

/-! End to end, entailed: `i ∈ C, C ⊑ D ⊨ i ∈ D`. The negated
conclusion (`i ∈ ¬D`) clashes with the derived `D`: every goal
refutes. -/
private def gPremiseSub : Graph :=
  [ ⟨indI, rdfType, .iri exC⟩, ⟨.iri exC, rdfsSubClassOf, .iri exD⟩ ]

#guard (negationGoals [⟨indI, rdfType, .iri exD⟩]).map
         (·.all (fun neg => tableauConsistent (gPremiseSub ++ neg) fuel
                            == some false))
       == some true

/-! End to end, NOT entailed: `i ∈ C ⊭ i ∈ D`. The augmented graph
has a model (quiescence, `some true`) — a countermodel, reported as
`entailed: false`, never as a silent miss. -/
#guard (negationGoals [⟨indI, rdfType, .iri exD⟩]).map
         (·.any (fun neg => tableauConsistent ([⟨indI, rdfType, .iri exC⟩] ++ neg)
                              fuel == some true))
       == some true


/-! ## Literal distinctness is decided on VALUES

`provablyDistinct` used to compare LEXICAL forms and only for
`xsd:string`. These checks pin both directions of the value-level
replacement: a `true` is a licence to clash and must hold in every
model; a `false` is a withholding and must be kept wherever the value
question is open. -/

private def lit (lex : String) (dt : WfIri) : Literal :=
  { lexicalForm := lex, datatype := dt, langTag := none, direction := none }

/-! Different integers, and the lexical mapping of the integer family
    is not injective, so this needs the VALUE. -/
#guard literalValuesDistinct (lit "18" xsdInteger) (lit "19" xsdInteger)
#guard literalValuesDistinct (lit "18" xsdInteger) (lit "19" XSD.xsdInt)

/-! One integer written two ways is ONE value. `"1"` and `"01"` are
    the case the lexical predicate got wrong in the other direction. -/
#guard !literalValuesDistinct (lit "1" xsdInteger) (lit "01" xsdInteger)
#guard !literalValuesDistinct (lit "1" xsdInteger) (lit "1.0" xsdDecimal)

/-! XSD Datatypes §3.2.4: `positiveZero` and `negativeZero` are two
    distinct members of the `xsd:float` value space. -/
#guard literalValuesDistinct (lit "+0.0" XSD.xsdFloat) (lit "-0.0" XSD.xsdFloat)
#guard !literalValuesDistinct (lit "+0.0" XSD.xsdFloat) (lit "0" XSD.xsdFloat)

/-! Two finite non-zero floats WITHHOLD: the lexical-to-value map
    rounds to the grid, so unequal lexical forms can be one value. -/
#guard !literalValuesDistinct (lit "1.5" XSD.xsdFloat) (lit "1.6" XSD.xsdFloat)

/-! OWL 2 Syntax §4: the value spaces of the datatype-map families are
    pairwise disjoint. -/
#guard literalValuesDistinct (lit "1" xsdInteger) (lit "1" xsdString)
#guard literalValuesDistinct (lit "true" xsdBoolean) (lit "true" xsdString)

/-! `xsd:boolean` has two values and four lexical forms. -/
#guard !literalValuesDistinct (lit "1" xsdBoolean) (lit "true" xsdBoolean)
#guard literalValuesDistinct (lit "0" xsdBoolean) (lit "true" xsdBoolean)

/-! A datatype outside every family withholds. -/
#guard !literalValuesDistinct (lit "2026-09-04T00:00:00Z" XSD.xsdDateTime)
                              (lit "2026-09-05T00:00:00Z" XSD.xsdDateTime)

/-! `rdf:XMLLiteral` by exclusive canonical XML, RDF 1.1 Concepts
    §5.1. The first pair is `WebOnt-miscellaneous-202`, asserted
    CONSISTENT: insignificant whitespace, one value, no clash. The
    second is the `-203` shape: leading text is significant, two
    values, clash. -/
#guard !literalValuesDistinct (lit "<br></br>" rdfXMLLiteral)
                              (lit "<br\n></br>" rdfXMLLiteral)
#guard literalValuesDistinct (lit "\n<br></br>" rdfXMLLiteral)
                             (lit "<br></br>" rdfXMLLiteral)


/-! ## Pairwise-different subsets, decided structurally

`existsDistinctSubsetBy d ts n` answers whether `n` members of `ts`
are pairwise related by `d`. The relation here is "different
numbers"; the second list repeats a member, so it has only two. -/

private def numDiff (a b : Term) : Bool := a != b

#guard existsDistinctSubsetBy numDiff [.iri exC, .iri exD, .iri exY] 3
#guard !existsDistinctSubsetBy numDiff [.iri exC, .iri exD, .iri exC] 3
#guard existsDistinctSubsetBy numDiff [.iri exC, .iri exD, .iri exC] 2
#guard existsDistinctSubsetBy numDiff [] 0
#guard !existsDistinctSubsetBy numDiff [] 1

/-! Every unordered pair once: three members give three pairs, not
six. -/
#guard (unorderedPairs [.iri exC, .iri exD, .iri exY]).length == 3

/-! ## The spy point: `∃p.{a}` is an edge TO `a`

`WebOnt-description-logic-035`'s shape. Every individual has a
`p`-edge to `spy` (`owl:Thing ⊑ ∃p.{spy}`), so every individual is an
`invP`-successor of `spy`. The `≥ 3 r` generating rule mints three
pairwise different witnesses, each of them gets its edge to `spy`, and
`spy`'s `≤ 2 invP` sees three different successors. With `≤ 3 invP`
the same graph has a model (the domain `{w1, w2, w3}`, with `i` and
`spy` among them), so it must not be refuted. -/

private def exR : WfIri := ⟨"http://e/R", rfl⟩
private def exInvP : WfIri := ⟨"http://e/invP", rfl⟩
private def exSpy : WfIri := ⟨"http://e/spy", rfl⟩

private def gSpy (bound : String) : Graph :=
  [ ⟨.iri exP, owlInverseOf, .iri exInvP⟩,
    ⟨.iri owlThing, rdfsSubClassOf, bnT "s"⟩,
    ⟨bn "s", owlOnProperty, .iri exP⟩,
    ⟨bn "s", owlSomeValuesFrom, bnT "o"⟩,
    ⟨bn "o", owlOneOf, bnT "ol"⟩,
    ⟨bn "ol", rdfFirst, .iri exSpy⟩, ⟨bn "ol", rdfRest, .iri rdfNil⟩,
    ⟨.iri exSpy, rdfType, bnT "m"⟩,
    ⟨bn "m", owlOnProperty, .iri exInvP⟩,
    ⟨bn "m", owlMaxCardinality, cardLit bound⟩,
    ⟨indI, rdfType, bnT "n"⟩,
    ⟨bn "n", owlOnProperty, .iri exR⟩,
    ⟨bn "n", owlMinCardinality, cardLit "3"⟩ ]

#guard refuted (gSpy "2")
#guard !(refuted (gSpy "3"))

/-! ## The generating rule's witnesses are pairwise different

`≥ 2 q` with `q ⊑ p` and `≤ 1 p`: the two `q`-successors are two
different `p`-successors. With `≤ 2 p` there is a model. -/

private def gGenDistinct (bound : String) : Graph :=
  [ ⟨.iri exQ, rdfsSubPropertyOf, .iri exP⟩,
    ⟨indI, rdfType, bnT "n"⟩,
    ⟨bn "n", owlOnProperty, .iri exQ⟩,
    ⟨bn "n", owlMinCardinality, cardLit "2"⟩,
    ⟨indI, rdfType, bnT "m"⟩,
    ⟨bn "m", owlOnProperty, .iri exP⟩,
    ⟨bn "m", owlMaxCardinality, cardLit bound⟩ ]

#guard refuted (gGenDistinct "1")
#guard !(refuted (gGenDistinct "2"))

/-! ## `≤ 1 p` identifies every `p`-successor, with no branching

`WebOnt-description-logic-108`'s shape, two levels deep. `x` has
`≤ 1 r` and three existentials on sub-roles of `r`; their witnesses
are one element, which then has `≤ 1 t` and three existentials on
sub-roles of `t` with pairwise disjoint fillers. Those witnesses are
one element too, in three disjoint classes. Without the outer bound
the three inner obligations sit on three different elements and the
graph has a model. -/

private def exT : WfIri := ⟨"http://e/T", rfl⟩
private def exE : WfIri := ⟨"http://e/E", rfl⟩
private def exR1 : WfIri := ⟨"http://e/r1", rfl⟩
private def exR2 : WfIri := ⟨"http://e/r2", rfl⟩
private def exR3 : WfIri := ⟨"http://e/r3", rfl⟩
private def exT1 : WfIri := ⟨"http://e/t1", rfl⟩
private def exT2 : WfIri := ⟨"http://e/t2", rfl⟩
private def exT3 : WfIri := ⟨"http://e/t3", rfl⟩

/-- `x : ∃rk.(≤ 1 t ⊓ ∃tk.filler)`, written with blank nodes tagged
    by `k`. -/
private def heinsohnLeg (k : String) (rk tk filler : WfIri) : Graph :=
  [ ⟨indI, rdfType, bnT s!"e{k}"⟩,
    ⟨bn s!"e{k}", owlOnProperty, .iri rk⟩,
    ⟨bn s!"e{k}", owlSomeValuesFrom, bnT s!"c{k}"⟩,
    ⟨bn s!"c{k}", owlIntersectionOf, bnT s!"l{k}"⟩,
    ⟨bn s!"l{k}", rdfFirst, bnT s!"mx{k}"⟩, ⟨bn s!"l{k}", rdfRest, bnT s!"l{k}b"⟩,
    ⟨bn s!"l{k}b", rdfFirst, bnT s!"ex{k}"⟩, ⟨bn s!"l{k}b", rdfRest, .iri rdfNil⟩,
    ⟨bn s!"mx{k}", owlOnProperty, .iri exT⟩,
    ⟨bn s!"mx{k}", owlMaxCardinality, cardLit "1"⟩,
    ⟨bn s!"ex{k}", owlOnProperty, .iri tk⟩,
    ⟨bn s!"ex{k}", owlSomeValuesFrom, .iri filler⟩,
    ⟨.iri rk, rdfsSubPropertyOf, .iri exR⟩,
    ⟨.iri tk, rdfsSubPropertyOf, .iri exT⟩ ]

private def gHeinsohn (outer : Bool) : Graph :=
  heinsohnLeg "1" exR1 exT1 exC ++ heinsohnLeg "2" exR2 exT2 exD ++
  heinsohnLeg "3" exR3 exT3 exE ++
  [ ⟨.iri exC, owlDisjointWith, .iri exD⟩,
    ⟨.iri exC, owlDisjointWith, .iri exE⟩,
    ⟨.iri exD, owlDisjointWith, .iri exE⟩ ] ++
  (if outer then
    [ ⟨indI, rdfType, bnT "outer"⟩,
      ⟨bn "outer", owlOnProperty, .iri exR⟩,
      ⟨bn "outer", owlMaxCardinality, cardLit "1"⟩ ]
  else [])

#guard refuted (gHeinsohn true)
#guard !(refuted (gHeinsohn false))

/-! ## A qualified bound merges only successors PROVABLY in its filler

`≤ 1 r.E` with `∃r.C` and `∃r.D`, `C` and `D` disjoint, and nothing
putting either witness in `E`: a model gives `x` two different
`r`-successors outside `E`. Offering the merge of the two witnesses
(as the ≤-rule did over all successors until 2026-10-10) and finding
that it clashes proved nothing, because no model has to make it. -/

private def gQualOutsideFiller (inFiller : Bool) : Graph :=
  [ ⟨indI, rdfType, bnT "a"⟩,
    ⟨bn "a", owlOnProperty, .iri exR⟩,
    ⟨bn "a", owlSomeValuesFrom, .iri exC⟩,
    ⟨indI, rdfType, bnT "b"⟩,
    ⟨bn "b", owlOnProperty, .iri exR⟩,
    ⟨bn "b", owlSomeValuesFrom, .iri exD⟩,
    ⟨.iri exC, owlDisjointWith, .iri exD⟩,
    ⟨indI, rdfType, bnT "q"⟩,
    ⟨bn "q", owlOnProperty, .iri exR⟩,
    ⟨bn "q", owlMaxQualifiedCardinality, cardLit "1"⟩,
    ⟨bn "q", owlOnClass, .iri exE⟩ ] ++
  (if inFiller then
    [ ⟨.iri exC, rdfsSubClassOf, .iri exE⟩, ⟨.iri exD, rdfsSubClassOf, .iri exE⟩ ]
  else [])

#guard !(refuted (gQualOutsideFiller false))
#guard refuted (gQualOutsideFiller true)

/-! ## A singleton nominal identifies its node with the member

`x : {a}` makes `x` and `a` one element, so `x : C` and `a : ¬C`
contradict each other. -/

private def gNominalIdent (negate : Bool) : Graph :=
  [ ⟨indI, rdfType, bnT "o"⟩,
    ⟨bn "o", owlOneOf, bnT "ol"⟩,
    ⟨bn "ol", rdfFirst, .iri exY⟩, ⟨bn "ol", rdfRest, .iri rdfNil⟩,
    ⟨indI, rdfType, .iri exC⟩ ] ++
  (if negate then
    [ ⟨.iri exY, rdfType, bnT "nc"⟩, ⟨bn "nc", owlComplementOf, .iri exC⟩ ]
  else [ ⟨.iri exY, rdfType, .iri exD⟩ ])

#guard refuted (gNominalIdent true)
#guard !(refuted (gNominalIdent false))



/-! ## The propositional clash on one node

Four clauses over `A` and `B` that no assignment satisfies, as four
disjunction labels on one node: a clash. Any three of them have a
model. `owl:Nothing` in a disjunct is a literal that is never true,
and `owl:Thing` one that always is. -/

private def lA : ClassExpr := .named exC
private def lB : ClassExpr := .named exD
private def nA : ClassExpr := .complement (.named exC)
private def nB : ClassExpr := .complement (.named exD)

#guard propositionalClashLabels []
  [.union [lA, lB], .union [lA, nB], .union [nA, lB], .union [nA, nB]]
#guard !propositionalClashLabels []
  [.union [lA, lB], .union [lA, nB], .union [nA, lB]]
#guard propositionalClashLabels []
  [.union [.named owlNothing, lA], .union [.named owlNothing, nA]]
#guard !propositionalClashLabels []
  [.union [.named owlThing, lA], .union [.named owlNothing, nA], .union [lB, nA]]

/-! Axioms enter as clauses about the same element. `P` with
`P ⊑ ¬M` (a disjointness), `M ⊔ N` and `M ⊔ O` force `N` and `O`;
`N ⊑ ¬O` then closes. Without that last axiom there is a model. -/

private def cP : ClassExpr := .named ⟨"http://e/P1", rfl⟩
private def cM : ClassExpr := .named ⟨"http://e/M1", rfl⟩
private def cN : ClassExpr := .named ⟨"http://e/N1", rfl⟩
private def cO : ClassExpr := .named ⟨"http://e/O1", rfl⟩

private def tbPM : List (ClassExpr × ClassExpr) :=
  [(cP, .complement cM), (cM, .complement cP)]

#guard propositionalClashLabels (tbPM ++ [(cN, .complement cO)])
  [cP, .union [cM, cN], .union [cM, cO]]
#guard !propositionalClashLabels tbPM
  [cP, .union [cM, cN], .union [cM, cO]]

-- The indexed clause growth (`nodeClausesIx`, what `propositionalClash`
-- runs) builds the same clause set and gives the same answers.
#guard propositionalClashLabelsIx (LhsAtomIndex.build (tbPM ++ [(cN, .complement cO)]))
  [cP, .union [cM, cN], .union [cM, cO]]
#guard !propositionalClashLabelsIx (LhsAtomIndex.build tbPM)
  [cP, .union [cM, cN], .union [cM, cO]]
-- The axiom keyed on the label `P` (`P ⊑ ¬M`) is not pulled in: the
-- label fixes `P`, and on a saturated node that axiom has fired. The
-- other two axioms are keyed on `M` and `N`, which no label fixes.
#guard (nodeClausesIx (LhsAtomIndex.build (tbPM ++ [(cN, .complement cO)]))
          [cP, .union [cM, cN], .union [cM, cO]] 3).length == 5
#guard (nodeClauses (tbPM ++ [(cN, .complement cO)])
          [cP, .union [cM, cN], .union [cM, cO]] 3).length == 6

/-! The same shape through the whole refuter: one individual, the
four clauses as `rdf:type` unions. -/

private def unionOf2 (tag : String) (a b : Term) : Graph :=
  [ ⟨bn s!"u{tag}", owlUnionOf, bnT s!"ul{tag}"⟩,
    ⟨bn s!"ul{tag}", rdfFirst, a⟩, ⟨bn s!"ul{tag}", rdfRest, bnT s!"ul{tag}b"⟩,
    ⟨bn s!"ul{tag}b", rdfFirst, b⟩, ⟨bn s!"ul{tag}b", rdfRest, .iri rdfNil⟩,
    ⟨indI, rdfType, bnT s!"u{tag}"⟩ ]

private def gFourClauses (all4 : Bool) : Graph :=
  [ ⟨bn "notC", owlComplementOf, .iri exC⟩, ⟨bn "notD", owlComplementOf, .iri exD⟩ ] ++
  unionOf2 "1" (.iri exC) (.iri exD) ++ unionOf2 "2" (.iri exC) (bnT "notD") ++
  unionOf2 "3" (bnT "notC") (.iri exD) ++
  (if all4 then unionOf2 "4" (bnT "notC") (bnT "notD") else [])

#guard refuted (gFourClauses true)
#guard !(refuted (gFourClauses false))


/-! ## Values a node cannot have on a property

Three shapes from `type-inconsistency.rdf`, each with a sibling that
has a model.

* `Inconsistent Disjoint Dataproperties`: `a dp1 10`, `dp1` disjoint
  from `dp2`, and `a : ∃dp2.xsd:integer[≥ 10, ≤ 10]`. The only
  `dp2`-value `a` may have is `10`, which the disjointness forbids.
  With `a dp1 11` the value `10` is free.
* `Inconsistent String Pattern with Disjoint Dataproperties`: the
  pattern `a(b|c)` admits `"ab"` and `"ac"`, and `a` has both on the
  disjoint property. With only `"ab"` there, `"ac"` is free.
* `Minus Infinity is not in owl:real`: `∃dp.{"-INF"^^xsd:float,
  "-0"^^xsd:integer}` with `∀dp.owl:real` leaves `0`, and the negative
  assertion `¬dp(a, "0"^^xsd:unsignedInt)` takes it. Without the
  negative assertion `0` is a model. -/

private def intT (lex : String) : Term :=
  .literal ⟨{ lexicalForm := lex, datatype := xsdInteger, langTag := none, direction := none },
            by simp [literalWf, rdfLangString, rdfDirLangString, Subtype.ext_iff, xsdInteger]⟩
private def strT (lex : String) : Term :=
  .literal ⟨{ lexicalForm := lex, datatype := xsdString, langTag := none, direction := none },
            by simp [literalWf, rdfLangString, rdfDirLangString, Subtype.ext_iff, xsdString]⟩
private def floatT (lex : String) : Term :=
  .literal ⟨{ lexicalForm := lex, datatype := XSD.xsdFloat, langTag := none, direction := none },
            by simp [literalWf, rdfLangString, rdfDirLangString, Subtype.ext_iff, XSD.xsdFloat]⟩
private def uintT (lex : String) : Term :=
  .literal ⟨{ lexicalForm := lex, datatype := XSD.xsdUnsignedInt, langTag := none,
              direction := none },
            by simp [literalWf, rdfLangString, rdfDirLangString, Subtype.ext_iff,
                     XSD.xsdUnsignedInt]⟩

private def exDp1 : WfIri := ⟨"http://e/dp1", rfl⟩
private def exDp2 : WfIri := ⟨"http://e/dp2", rfl⟩

private def gDisjointDataInt (v : String) : Graph :=
  [ ⟨.iri exDp1, owlPropertyDisjointWith, .iri exDp2⟩,
    ⟨indI, exDp1, intT v⟩,
    ⟨indI, rdfType, bnT "s"⟩,
    ⟨bn "s", owlOnProperty, .iri exDp2⟩,
    ⟨bn "s", owlSomeValuesFrom, bnT "dr"⟩,
    ⟨bn "dr", owlOnDatatype, .iri xsdInteger⟩,
    ⟨bn "dr", owlWithRestrictions, bnT "f1"⟩,
    ⟨bn "f1", rdfFirst, bnT "fa"⟩, ⟨bn "f1", rdfRest, bnT "f2"⟩,
    ⟨bn "f2", rdfFirst, bnT "fb"⟩, ⟨bn "f2", rdfRest, .iri rdfNil⟩,
    ⟨bn "fa", facetMinInclusive, intT "10"⟩,
    ⟨bn "fb", facetMaxInclusive, intT "10"⟩ ]

#guard refuted (gDisjointDataInt "10")
#guard !(refuted (gDisjointDataInt "11"))

private def gDisjointDataPattern (both : Bool) : Graph :=
  [ ⟨.iri exDp1, owlPropertyDisjointWith, .iri exDp2⟩,
    ⟨indI, exDp1, strT "ab"⟩,
    ⟨indI, rdfType, bnT "s"⟩,
    ⟨bn "s", owlOnProperty, .iri exDp2⟩,
    ⟨bn "s", owlSomeValuesFrom, bnT "dr"⟩,
    ⟨bn "dr", owlOnDatatype, .iri xsdString⟩,
    ⟨bn "dr", owlWithRestrictions, bnT "f1"⟩,
    ⟨bn "f1", rdfFirst, bnT "fa"⟩, ⟨bn "f1", rdfRest, .iri rdfNil⟩,
    ⟨bn "fa", facetPatternIri, strT "a(b|c)"⟩ ] ++
  (if both then [⟨indI, exDp1, strT "ac"⟩] else [])

#guard refuted (gDisjointDataPattern true)
#guard !(refuted (gDisjointDataPattern false))

/-! The pattern facet is part of the parse, so two restrictions that
differ only in their pattern are two expressions. -/
#guard (match parseClassExpr (Store.ofGraph (gDisjointDataPattern false)) (bnT "dr") 8 with
        | .dataRestriction dt fs => dt == xsdString && fs.any (·.1 == facetPatternIri)
        | _ => false)

private def gMinusInf (negative : Bool) : Graph :=
  [ ⟨indI, rdfType, bnT "av"⟩,
    ⟨bn "av", owlOnProperty, .iri exDp1⟩,
    ⟨bn "av", owlAllValuesFrom, .iri XSD.owlReal⟩,
    ⟨indI, rdfType, bnT "sv"⟩,
    ⟨bn "sv", owlOnProperty, .iri exDp1⟩,
    ⟨bn "sv", owlSomeValuesFrom, bnT "one"⟩,
    ⟨bn "one", owlOneOf, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, floatT "-INF"⟩, ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, intT "-0"⟩, ⟨bn "l2", rdfRest, .iri rdfNil⟩ ] ++
  (if negative then
    [ ⟨bn "npa", owlSourceIndividual, .iri exI⟩,
      ⟨bn "npa", owlAssertionProperty, .iri exDp1⟩,
      ⟨bn "npa", owlTargetValue, uintT "0"⟩ ]
  else [])

#guard refuted (gMinusInf true)
#guard !(refuted (gMinusInf false))


/-! ## A conclusion with blank-node individuals is rolled up

`WebOnt-someValuesFrom-003`: `person ≡ ∃parent.person` and
`fred : person` entail `fred parent _:a . _:a parent _:b`, read as
`fred : ∃parent.∃parent.⊤`. The goal is `fred : ¬∃parent.∃parent.⊤`,
and the tableau refutes it. With only `person ⊑ ∃parent.⊤` the
premise gives `fred` a parent and nothing gives that parent one, so
the same goal has a model and must not be refuted. A cycle of blank
nodes is not a tree and gets no goal. -/

private def exParent : WfIri := ⟨"http://e/parent", rfl⟩
private def exPerson : WfIri := ⟨"http://e/person", rfl⟩
private def exFred : WfIri := ⟨"http://e/fred", rfl⟩

private def gPersonLoop (recursive : Bool) : Graph :=
  [ ⟨.iri exPerson, owlEquivalentClass, bnT "pr"⟩,
    ⟨bn "pr", owlOnProperty, .iri exParent⟩,
    ⟨bn "pr", owlSomeValuesFrom, .iri (if recursive then exPerson else owlThing)⟩,
    ⟨.iri exFred, rdfType, .iri exPerson⟩ ]

private def cTwoParents : Graph :=
  [ ⟨.iri exFred, exParent, bnT "ca"⟩,
    ⟨bn "ca", exParent, bnT "cb"⟩,
    ⟨bn "ca", rdfType, .iri owlThing⟩ ]

private def entailedByRefutation (prem concl : Graph) : Bool :=
  match negationGoals concl with
  | none => false
  | some gs => gs.all (fun goal => tableauConsistent (prem ++ goal) fuel == some false)

#guard (negationGoals cTwoParents).isSome
#guard entailedByRefutation (gPersonLoop true) cTwoParents
#guard !entailedByRefutation (gPersonLoop false) cTwoParents
/-! One level is entailed by both premises. -/
#guard entailedByRefutation (gPersonLoop false) [⟨.iri exFred, exParent, bnT "ca"⟩]

#guard (negationGoals [⟨bn "ca", exParent, bnT "cb"⟩, ⟨bn "cb", exParent, bnT "ca"⟩]).isNone
/-! A blank node with two parents is not a tree either. -/
#guard (negationGoals [⟨.iri exFred, exParent, bnT "ca"⟩,
                       ⟨.iri exI, exParent, bnT "ca"⟩]).isNone


/-! ## Identity reasoning over nominals

`WebOnt-description-logic-502` in two variables. `TorF` is `{T, F}`,
`{p1, m1}` and `{p2, m2}` at once, and `T ≠ F`, so `p1`/`m1` and
`p2`/`m2` are the two truth values of two variables, and a label
`T : {a, b}` is the clause "`a` is true or `b` is true". All four
clauses over the two variables have no model; any three have one. -/

private def nT : WfIri := ⟨"http://e/T", rfl⟩
private def nF : WfIri := ⟨"http://e/F", rfl⟩
private def nP1 : WfIri := ⟨"http://e/p1", rfl⟩
private def nM1 : WfIri := ⟨"http://e/m1", rfl⟩
private def nP2 : WfIri := ⟨"http://e/p2", rfl⟩
private def nM2 : WfIri := ⟨"http://e/m2", rfl⟩
private def nTorF : WfIri := ⟨"http://e/TorF", rfl⟩

/-- `subj owl:oneOf (a b)` with list cells tagged `tag`. -/
private def oneOf2 (tag : String) (subj : Subject) (a b : WfIri) : Graph :=
  [ ⟨subj, owlOneOf, bnT s!"o{tag}"⟩,
    ⟨bn s!"o{tag}", rdfFirst, .iri a⟩, ⟨bn s!"o{tag}", rdfRest, bnT s!"o{tag}b"⟩,
    ⟨bn s!"o{tag}b", rdfFirst, .iri b⟩, ⟨bn s!"o{tag}b", rdfRest, .iri rdfNil⟩ ]

/-- `T rdf:type {a, b}`. -/
private def clause (tag : String) (a b : WfIri) : Graph :=
  ⟨.iri nT, rdfType, bnT s!"k{tag}"⟩ :: oneOf2 s!"k{tag}" (bn s!"k{tag}") a b

private def gTwoVarSat (all4 : Bool) : Graph :=
  oneOf2 "t" (.iri nTorF) nT nF ++ oneOf2 "1" (.iri nTorF) nP1 nM1 ++
  oneOf2 "2" (.iri nTorF) nP2 nM2 ++
  [ ⟨.iri nT, owlDifferentFrom, .iri nF⟩,
    ⟨.iri nT, rdfType, .iri nTorF⟩, ⟨.iri nF, rdfType, .iri nTorF⟩ ] ++
  clause "a" nP1 nP2 ++ clause "b" nM1 nP2 ++ clause "c" nP1 nM2 ++
  (if all4 then clause "d" nM1 nM2 else [])

#guard refuted (gTwoVarSat true)
#guard !(refuted (gTwoVarSat false))


/-! ## The class-size counting rung

`WebOnt-description-logic-910` in miniature. `p` and `q` are
functional with domain `D`, every `D` has a `p`- and a `q`-successor in
`O = {o}`, and `o` has exactly two `p`-predecessors and exactly `k`
`q`-predecessors. The fibre rows give `|D| = 2·|O|` and
`|D| = k·|O|` with `|O| ≥ 1`: no integer solution for `k = 3`, and the
two-element model for `k = 2`. -/

private def kD : WfIri := ⟨"http://e/D", rfl⟩
private def kO : WfIri := ⟨"http://e/O", rfl⟩
private def iO : WfIri := ⟨"http://e/o", rfl⟩
private def pIp : WfIri := ⟨"http://e/ip", rfl⟩
private def pIq : WfIri := ⟨"http://e/iq", rfl⟩

private def gFibres (k : String) : Graph :=
  [ ⟨.iri exP, rdfType, .iri owlFunctionalProperty⟩,
    ⟨.iri exP, owlInverseOf, .iri pIp⟩,
    ⟨.iri exP, rdfsDomain, .iri kD⟩,
    ⟨.iri exQ, rdfType, .iri owlFunctionalProperty⟩,
    ⟨.iri exQ, owlInverseOf, .iri pIq⟩,
    ⟨.iri exQ, rdfsDomain, .iri kD⟩,
    ⟨.iri kD, rdfsSubClassOf, bnT "s1"⟩,
    ⟨bn "s1", owlOnProperty, .iri exP⟩, ⟨bn "s1", owlSomeValuesFrom, .iri kO⟩,
    ⟨.iri kD, rdfsSubClassOf, bnT "s2"⟩,
    ⟨bn "s2", owlOnProperty, .iri exQ⟩, ⟨bn "s2", owlSomeValuesFrom, .iri kO⟩,
    ⟨.iri kO, owlOneOf, bnT "ol"⟩,
    ⟨bn "ol", rdfFirst, .iri iO⟩, ⟨bn "ol", rdfRest, .iri rdfNil⟩,
    ⟨.iri kO, rdfsSubClassOf, bnT "c1"⟩,
    ⟨bn "c1", owlOnProperty, .iri pIp⟩, ⟨bn "c1", owlCardinality, cardLit "2"⟩,
    ⟨.iri kO, rdfsSubClassOf, bnT "c2"⟩,
    ⟨bn "c2", owlOnProperty, .iri pIq⟩, ⟨bn "c2", owlCardinality, cardLit k⟩ ]

#guard countingRefutes (gFibres "3")
#guard !countingRefutes (gFibres "2")
#guard refuted (gFibres "3")
#guard !(refuted (gFibres "2"))


/-! ## Property axioms in a conclusion are claims, with goals of their own

`WebOnt-FunctionalProperty-004`: `prop`'s range is a one-element
class, so `prop` is functional. The goal is a fresh `a` with two
different `prop`-successors; the range axiom puts both in the
singleton. Without the range there is a model with two successors.
`-InverseFunctionalProperty-004` is the same through the domain. -/

private def exSingle : WfIri := ⟨"http://e/Singleton", rfl⟩

private def gSingletonRange (withAxiom : Bool) (onDomain : Bool) : Graph :=
  [ ⟨.iri exSingle, owlOneOf, bnT "sl"⟩,
    ⟨bn "sl", rdfFirst, bnT "only"⟩, ⟨bn "sl", rdfRest, .iri rdfNil⟩,
    ⟨bn "only", rdfType, .iri exSingle⟩ ] ++
  (if withAxiom then
    [⟨.iri exP, if onDomain then rdfsDomain else rdfsRange, .iri exSingle⟩] else [])

#guard entailedByRefutation (gSingletonRange true false)
  [⟨.iri exP, rdfType, .iri owlFunctionalProperty⟩]
#guard !entailedByRefutation (gSingletonRange false false)
  [⟨.iri exP, rdfType, .iri owlFunctionalProperty⟩]
#guard entailedByRefutation (gSingletonRange true true)
  [⟨.iri exP, rdfType, .iri owlInverseFunctionalProperty⟩]
#guard !entailedByRefutation (gSingletonRange true true)
  [⟨.iri exP, rdfType, .iri owlFunctionalProperty⟩]

/-! A characteristic in the conclusion is not kept as scaffolding: with
it in every goal, `p` would be ASSUMED functional while the other
conjunct is proved. Here the premise has the membership and nothing
about `p`, so the conclusion is not entailed. -/
#guard !entailedByRefutation [⟨indI, rdfType, .iri exC⟩]
  [⟨.iri exP, rdfType, .iri owlFunctionalProperty⟩, ⟨indI, rdfType, .iri exC⟩]
#guard entailedByRefutation [⟨indI, rdfType, .iri exC⟩] [⟨indI, rdfType, .iri exC⟩]

/-! `WebOnt-I5.8-010`: `∃p.xsd:nonPositiveInteger` with range
`xsd:nonNegativeInteger` leaves the value `0`, so `john p "0"` is
entailed; the goal is the negative assertion. Without the range the
value may be `-1`. -/

private def nonNegT : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#nonNegativeInteger", rfl⟩
private def nonPosT : WfIri := ⟨"http://www.w3.org/2001/XMLSchema#nonPositiveInteger", rfl⟩

private def gJohnZero (range : Bool) : Graph :=
  [ ⟨indI, rdfType, bnT "sv"⟩,
    ⟨bn "sv", owlOnProperty, .iri exDp1⟩,
    ⟨bn "sv", owlSomeValuesFrom, .iri nonPosT⟩ ] ++
  (if range then [⟨.iri exDp1, rdfsRange, .iri nonNegT⟩] else [])

#guard entailedByRefutation (gJohnZero true) [⟨indI, exDp1, intT "0"⟩]
#guard !entailedByRefutation (gJohnZero false) [⟨indI, exDp1, intT "0"⟩]

/-! A label holding `unknown` is stored once: the second add reports
no change, or the expansion would never stop. -/
#guard
  let l : ClassExpr := .allOf exP .unknown
  let st1 := (addLabel {} indI l).1
  !(addLabel st1 indI l).2


/-! ## Named-subject class markers are equivalences

`A owl:complementOf B` with `A` an IRI makes `A` exactly the complement
of `B`: disjoint from it AND covering what `B` misses
(`WebOnt-complementOf-001`). An individual in neither is refuted; with
the marker on a blank node (an anonymous complement, no claim about
`A`) it is not. -/

private def gNamedComplement (named : Bool) : Graph :=
  (if named then [⟨.iri exC, owlComplementOf, .iri exD⟩]
   else [⟨bn "anon", owlComplementOf, .iri exD⟩]) ++
  [ ⟨indI, rdfType, bnT "nc"⟩, ⟨bn "nc", owlComplementOf, .iri exC⟩,
    ⟨indI, rdfType, bnT "nd"⟩, ⟨bn "nd", owlComplementOf, .iri exD⟩ ]

#guard refuted (gNamedComplement true)
#guard !(refuted (gNamedComplement false))

/-! `c owl:disjointUnionOf (B G)` (`New-Feature-DisjointUnion-001`):
a `c` that is not `G` is `B`. Without the axiom it need not be. -/

private def exBoy : WfIri := ⟨"http://e/Boy", rfl⟩
private def exGirl : WfIri := ⟨"http://e/Girl", rfl⟩

private def gDisjointUnion (withAxiom : Bool) : Graph :=
  (if withAxiom then
    [ ⟨.iri exC, owlDisjointUnionOf, bnT "du"⟩,
      ⟨bn "du", rdfFirst, .iri exBoy⟩, ⟨bn "du", rdfRest, bnT "du2"⟩,
      ⟨bn "du2", rdfFirst, .iri exGirl⟩, ⟨bn "du2", rdfRest, .iri rdfNil⟩ ] else []) ++
  [ ⟨indI, rdfType, .iri exC⟩,
    ⟨indI, rdfType, bnT "ng"⟩, ⟨bn "ng", owlComplementOf, .iri exGirl⟩ ]

#guard entailedByRefutation (gDisjointUnion true) [⟨indI, rdfType, .iri exBoy⟩]
#guard !entailedByRefutation (gDisjointUnion false) [⟨indI, rdfType, .iri exBoy⟩]

/-! A union antecedent fires on each disjunct (`WebOnt-unionOf-002`). -/
#guard (splitUnionAntecedents [(.union [.named exC, .named exD], .named exE)]).length == 3

/-! `i : ¬{a, b}` beside `i` identified with `a` is a clash. -/
private def gNegNominal (member : Bool) : Graph :=
  [ ⟨indI, rdfType, bnT "o1"⟩, ⟨bn "o1", owlOneOf, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, .iri exY⟩, ⟨bn "l1", rdfRest, .iri rdfNil⟩,
    ⟨indI, rdfType, bnT "neg"⟩, ⟨bn "neg", owlComplementOf, bnT "o2"⟩,
    ⟨bn "o2", owlOneOf, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, .iri (if member then exY else exZ)⟩,
    ⟨bn "l2", rdfRest, .iri rdfNil⟩ ]

#guard refuted (gNegNominal true)
#guard !(refuted (gNegNominal false))

/-! ## The min-sum counting clash (`WebOnt-description-logic-903`)

`≥ 2 p` and `≥ 3 q` with `p, q ⊑ r` and disjoint ranges give five
different `r`-successors: `≤ 4 r` clashes, `≤ 5 r` does not. Without
the disjointness the successors may overlap. -/

private def gMinSum (bound : String) (disjoint : Bool) : Graph :=
  [ ⟨.iri exP, rdfsSubPropertyOf, .iri exR⟩, ⟨.iri exQ, rdfsSubPropertyOf, .iri exR⟩,
    ⟨.iri exP, rdfsRange, .iri exC⟩, ⟨.iri exQ, rdfsRange, .iri exD⟩,
    ⟨indI, rdfType, bnT "a"⟩, ⟨bn "a", owlOnProperty, .iri exP⟩,
    ⟨bn "a", owlMinCardinality, cardLit "2"⟩,
    ⟨indI, rdfType, bnT "b"⟩, ⟨bn "b", owlOnProperty, .iri exQ⟩,
    ⟨bn "b", owlMinCardinality, cardLit "3"⟩,
    ⟨indI, rdfType, bnT "m"⟩, ⟨bn "m", owlOnProperty, .iri exR⟩,
    ⟨bn "m", owlMaxCardinality, cardLit bound⟩ ] ++
  (if disjoint then [⟨.iri exC, owlDisjointWith, .iri exD⟩] else [])

#guard refuted (gMinSum "4" true)
#guard !(refuted (gMinSum "5" true))
#guard !(refuted (gMinSum "4" false))

/-! A named-subject `owl:oneOf` in a CONCLUSION is a claim
(`c ≡ {a, b}`), not scaffolding: it gets two goals. -/
#guard (negationGoals [⟨.iri exC, owlOneOf, bnT "ol"⟩,
                       ⟨bn "ol", rdfFirst, .iri exY⟩, ⟨bn "ol", rdfRest, .iri rdfNil⟩]).map
         List.length == some 2


/-! ## Inverse-functional properties identify predecessors

`p` inverse-functional with `x p a` and `y p a`: `x` and `y` are one
element, so `x : C` and `y : ¬C` contradict each other; and two
provably different predecessors are a clash outright. Without the
declaration neither holds. -/

private def exX : WfIri := ⟨"http://e/x", rfl⟩
private def exA : WfIri := ⟨"http://e/a", rfl⟩
private def exB : WfIri := ⟨"http://e/b", rfl⟩

private def gIfp (declared : Bool) (different : Bool) : Graph :=
  (if declared then [⟨.iri exP, rdfType, .iri owlInverseFunctionalProperty⟩] else []) ++
  [ ⟨.iri exX, exP, .iri exA⟩, ⟨.iri exY, exP, .iri exA⟩ ] ++
  (if different then [⟨.iri exX, owlDifferentFrom, .iri exY⟩]
   else [ ⟨.iri exX, rdfType, .iri exC⟩,
          ⟨.iri exY, rdfType, bnT "nc"⟩, ⟨bn "nc", owlComplementOf, .iri exC⟩ ])

#guard refuted (gIfp true false)
#guard refuted (gIfp true true)
#guard !(refuted (gIfp false false))
#guard !(refuted (gIfp false true))

/-! ## A symmetric property is read in both directions

`a p b` with `p` symmetric gives `b p a`, so `b : ∀p.⊥` clashes. -/

private def gSymmetric (declared : Bool) : Graph :=
  (if declared then [⟨.iri exP, rdfType, .iri owlSymmetricProperty⟩] else []) ++
  [ ⟨.iri exA, exP, .iri exB⟩,
    ⟨.iri exB, rdfType, bnT "av"⟩, ⟨bn "av", owlOnProperty, .iri exP⟩,
    ⟨bn "av", owlAllValuesFrom, .iri owlNothing⟩ ]

#guard refuted (gSymmetric true)
#guard !(refuted (gSymmetric false))

/-! ## The nominal choice branches over the members

`x : {a, b}` with `a : C` and `b : C` puts `x` in `C` whichever member
it is, so `x : ¬C` is refuted on both branches. With `b : D` instead,
the branch `x = b` stays open. -/

private def gNominalChoice (bothC : Bool) : Graph :=
  [ ⟨.iri exX, rdfType, bnT "o"⟩, ⟨bn "o", owlOneOf, bnT "l1"⟩,
    ⟨bn "l1", rdfFirst, .iri exA⟩, ⟨bn "l1", rdfRest, bnT "l2"⟩,
    ⟨bn "l2", rdfFirst, .iri exB⟩, ⟨bn "l2", rdfRest, .iri rdfNil⟩,
    ⟨.iri exA, rdfType, .iri exC⟩,
    ⟨.iri exB, rdfType, .iri (if bothC then exC else exD)⟩,
    ⟨.iri exX, rdfType, bnT "nc"⟩, ⟨bn "nc", owlComplementOf, .iri exC⟩ ]

#guard refuted (gNominalChoice true)
#guard !(refuted (gNominalChoice false))

/-! ## The TBox index keeps every axiom a rule can fire

`onePass` reads the TBox through `TBoxIndex`. A label meets the
axioms in its `ceIndexKey` bucket (`ceIndexKey_of_beq`), an
edge-provable antecedent is filed under its property, and the
intersection and `owl:Thing` antecedents have their own lists. -/

private def ixSample : List (ClassExpr × ClassExpr) :=
  [ (.named exA, .named exB),
    (.someOf exP (.named exC), .named exD),
    (.intersection [.named exA, .named exB], .named exC),
    (.named owlThing, .named exD),
    (.complement (.named exA), .named exC),
    (.maxCard 1 exP, .named exB) ]

#guard ((TBoxIndex.build ixSample).byKey.getD (ceIndexKey (.named exA)) []).length == 1
#guard ((TBoxIndex.build ixSample).byKey.getD (ceIndexKey (.named exB)) []).isEmpty
#guard ((TBoxIndex.build ixSample).byKey.getD (ceIndexKey (.complement (.named exA))) []).length == 1
#guard ((TBoxIndex.build ixSample).byKey.getD (ceIndexKey (.complement (.named exB))) []).isEmpty
#guard (TBoxIndex.build ixSample).edgeProps.length == 1
#guard ((TBoxIndex.build ixSample).edgeByProp.getD exP.val []).length == 1
#guard ((TBoxIndex.build ixSample).conjByKey.getD (ceIndexKey (.named exA)) []).length == 1
#guard ((TBoxIndex.build ixSample).conjByKey.getD (ceIndexKey (.named exB)) []).isEmpty
#guard (TBoxIndex.build ixSample).top.length == 1
-- `≤ 1 p` is not edge-provable: no edge proves an upper bound.
#guard ((TBoxIndex.build [(.maxCard 1 exP, .named exB)]).edgeProps).isEmpty


/-! ## Range axioms applied where there is an edge (https://github.com/danbri/factoidal/issues/760)

`p rdfs:range C` is `⊤ ⊑ ∀p.C`. `injectLazyRanges` puts `∀p.C` on a node
only when the node has a possible `p`-successor (`successorPropsAt`), so
each refutation below needs the range to reach the object of an edge: an
asserted edge, an edge the expansion made, an edge read through an
inverse property, and an edge on a sub-property. Each has a twin with a
model that must not be refuted. -/

private def exRgE : WfIri := ⟨"http://e/rgE", rfl⟩
private def exRgS : WfIri := ⟨"http://e/rgS", rfl⟩

/-- `i P y`, `P rdfs:range C`, `C` disjoint from `D`; `y : D` when
    `clash`. -/
private def gRangeEdge (clash : Bool) : Graph :=
  [ ⟨indI, exP, .iri exY⟩,
    ⟨.iri exP, rdfsRange, .iri exC⟩,
    ⟨.iri exC, owlDisjointWith, .iri exD⟩ ] ++
  (if clash then [⟨.iri exY, rdfType, .iri exD⟩] else [⟨.iri exY, rdfType, .iri exRgE⟩])

#guard refuted (gRangeEdge true)
#guard !(refuted (gRangeEdge false))
#guard tableauConsistent (gRangeEdge false) fuel == some true

/-- `i : E`, `E ⊑ ∃P.D` (or `∃Q.D`), `P rdfs:range C`, `C` disjoint from
    `D`: the witness the expansion makes for `∃P.D` is in `C` and `D`. -/
private def gRangeWitness (onP : Bool) : Graph :=
  [ ⟨indI, rdfType, .iri exRgE⟩,
    ⟨.iri exRgE, rdfsSubClassOf, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri (if onP then exP else exQ)⟩,
    ⟨bn "r", owlSomeValuesFrom, .iri exD⟩,
    ⟨.iri exP, rdfsRange, .iri exC⟩,
    ⟨.iri exC, owlDisjointWith, .iri exD⟩ ]

#guard refuted (gRangeWitness true)
#guard !(refuted (gRangeWitness false))

/-- `y Q i` with `Q owl:inverseOf P`, so `i P y`; `P rdfs:range C`, `C`
    disjoint from `D`, `y : D` (or `y : E`). -/
private def gRangeInverse (clash : Bool) : Graph :=
  [ ⟨.iri exY, exQ, .iri exI⟩,
    ⟨.iri exQ, owlInverseOf, .iri exP⟩,
    ⟨.iri exP, rdfsRange, .iri exC⟩,
    ⟨.iri exC, owlDisjointWith, .iri exD⟩,
    ⟨.iri exY, rdfType, .iri (if clash then exD else exRgE)⟩ ]

#guard refuted (gRangeInverse true)
#guard !(refuted (gRangeInverse false))

/-- `i S y` with `S rdfs:subPropertyOf P`; `P rdfs:range C`, `C` disjoint
    from `D`, `y : D` (or `y : E`). -/
private def gRangeSub (clash : Bool) : Graph :=
  [ ⟨indI, exRgS, .iri exY⟩,
    ⟨.iri exRgS, rdfsSubPropertyOf, .iri exP⟩,
    ⟨.iri exP, rdfsRange, .iri exC⟩,
    ⟨.iri exC, owlDisjointWith, .iri exD⟩,
    ⟨.iri exY, rdfType, .iri (if clash then exD else exRgE)⟩ ]

#guard refuted (gRangeSub true)
#guard !(refuted (gRangeSub false))

/-- The domain half reads the sub-property edge too (`applyAxiomsEdges`
    asks only the properties `successorPropsAt` names): `i S y`,
    `S ⊑ P`, `P rdfs:domain C`, `C` disjoint from `D`, `i : D`. -/
private def gDomainSub (clash : Bool) : Graph :=
  [ ⟨indI, exRgS, .iri exY⟩,
    ⟨.iri exRgS, rdfsSubPropertyOf, .iri exP⟩,
    ⟨.iri exP, rdfsDomain, .iri exC⟩,
    ⟨.iri exC, owlDisjointWith, .iri exD⟩,
    ⟨indI, rdfType, .iri (if clash then exD else exRgE)⟩ ]

#guard refuted (gDomainSub true)
#guard !(refuted (gDomainSub false))

/-! The range consequent is put on the subject of the edge and on no
other node: `y` has no `P`-successor. -/
#guard
  let g := gRangeEdge false
  let tb := collectAxioms g
  let st := { initState g with tbox := tb }
  let ix := TBoxIndex.buildLazy tb (lazyOccurrences tb st)
  (lazyRangeLabels ix st indI).length == 1 && (lazyRangeLabels ix st (.iri exY)).isEmpty

/-! Which range axioms are applied this way (`lazyRangeAxiom`): a class
filler is; a datatype filler, a complement filler and a `∀p.C` that
occurs in another axiom are not, and stay on every node. -/
private def rangeAx (c : ClassExpr) : ClassExpr × ClassExpr := (.named owlThing, .allOf exP c)

#guard ((TBoxIndex.buildLazy [rangeAx (.named exC)] {}).lazyByProp.getD exP []).length == 1
#guard (TBoxIndex.buildLazy [rangeAx (.named exC)] {}).top.isEmpty
#guard (TBoxIndex.buildLazy [rangeAx (.named xsdInteger)] {}).top.length == 1
#guard (TBoxIndex.buildLazy [rangeAx (.complement (.named exC))] {}).top.length == 1
#guard
  let tb := [rangeAx (.named exC), (.allOf exP (.named exC), .named exD)]
  let ix := TBoxIndex.buildLazy tb (lazyOccurrences tb {})
  ix.top.length == 1 && ix.lazyByProp.isEmpty
-- `owl:topObjectProperty` is never applied this way: `∀top.C` puts `C` on the node itself.
#guard (TBoxIndex.buildLazy [(.named owlThing, .allOf owlTopObjectProperty (.named exC))] {}).top.length == 1

/-! ## Qualified cardinality over a data range (`owl:onDataRange`)

OWL 2 Mapping to RDF Graphs, Table 1: `DataMaxCardinality(n DPE DR)`
is a restriction with `owl:maxQualifiedCardinality` and
`owl:onDataRange T(DR)`. Until 2026-10-10 the parser read only
`owl:onClass`, so the restriction below parsed as the UNQUALIFIED
`≤ 1 dp`, and an individual with the two integer values `1` and `2` on
`dp` was refuted. It has a model: neither value is an `xsd:string`.

The second pair puts the same bound beside `≥ 2 dp.xsd:string`, which
contradicts it, and beside `≥ 2 dp.xsd:integer`, which does not. Read
unqualified, both pairs were `≥ 2 dp ⊓ ≤ 1 dp` and both were refuted. -/

private def gMaxQualData : Graph :=
  [ ⟨indI, rdfType, bnT "mq"⟩,
    ⟨bn "mq", owlOnProperty, .iri exDp1⟩,
    ⟨bn "mq", owlMaxQualifiedCardinality, cardLit "1"⟩,
    ⟨bn "mq", owlOnDataRange, .iri xsdString⟩,
    ⟨indI, exDp1, intT "1"⟩, ⟨indI, exDp1, intT "2"⟩ ]

#guard (match parseClassExpr (Store.ofGraph gMaxQualData) (bnT "mq") 8 with
        | .maxQualCard 1 p (.named d) => p == exDp1 && d == xsdString
        | _ => false)
#guard !(refuted gMaxQualData)

private def gMinMaxQualData (minFiller : WfIri) : Graph :=
  [ ⟨indI, rdfType, bnT "mq"⟩,
    ⟨bn "mq", owlOnProperty, .iri exDp1⟩,
    ⟨bn "mq", owlMaxQualifiedCardinality, cardLit "1"⟩,
    ⟨bn "mq", owlOnDataRange, .iri xsdString⟩,
    ⟨indI, rdfType, bnT "nq"⟩,
    ⟨bn "nq", owlOnProperty, .iri exDp1⟩,
    ⟨bn "nq", owlMinQualifiedCardinality, cardLit "2"⟩,
    ⟨bn "nq", owlOnDataRange, .iri minFiller⟩ ]

#guard refuted (gMinMaxQualData xsdString)
#guard !(refuted (gMinMaxQualData xsdInteger))

/-! `Qualified-cardinality-boolean` and `-restricted-int`
(https://github.com/danbri/factoidal/issues/709). `= 2 dp.xsd:boolean`
needs both boolean values, so each is entailed; the negation goal is the
negative assertion, and `xsd:boolean` less the excluded value holds one
value, fewer than two. `= 1 dp.xsd:boolean` does not force `true`.
`= 3 dp.xsd:integer[≥ 1, ≤ 3]` forces `1`, `2` and `3`;
`= 2 dp.xsd:integer[≥ 1, ≤ 3]` forces none of them. -/

private def boolT (lex : String) : Term :=
  .literal ⟨{ lexicalForm := lex, datatype := xsdBoolean, langTag := none, direction := none },
            by simp [literalWf, rdfLangString, rdfDirLangString, Subtype.ext_iff, xsdBoolean]⟩

private def gExactQualBool (k : String) : Graph :=
  [ ⟨indI, rdfType, bnT "eq"⟩,
    ⟨bn "eq", owlOnProperty, .iri exDp1⟩,
    ⟨bn "eq", owlQualifiedCardinality, cardLit k⟩,
    ⟨bn "eq", owlOnDataRange, .iri xsdBoolean⟩ ]

#guard entailedByRefutation (gExactQualBool "2") [⟨indI, exDp1, boolT "true"⟩]
#guard entailedByRefutation (gExactQualBool "2") [⟨indI, exDp1, boolT "false"⟩]
#guard !entailedByRefutation (gExactQualBool "1") [⟨indI, exDp1, boolT "true"⟩]
/-! Three boolean values do not exist: `= 3 dp.xsd:boolean` has no
model, and `= 2` has one. -/
#guard refuted (gExactQualBool "3")
#guard !(refuted (gExactQualBool "2"))

private def gExactQualRange (k : String) : Graph :=
  [ ⟨indI, rdfType, bnT "eq"⟩,
    ⟨bn "eq", owlOnProperty, .iri exDp1⟩,
    ⟨bn "eq", owlQualifiedCardinality, cardLit k⟩,
    ⟨bn "eq", owlOnDataRange, bnT "dr"⟩,
    ⟨bn "dr", owlOnDatatype, .iri xsdInteger⟩,
    ⟨bn "dr", owlWithRestrictions, bnT "f1"⟩,
    ⟨bn "f1", rdfFirst, bnT "fa"⟩, ⟨bn "f1", rdfRest, bnT "f2"⟩,
    ⟨bn "f2", rdfFirst, bnT "fb"⟩, ⟨bn "f2", rdfRest, .iri rdfNil⟩,
    ⟨bn "fa", facetMinInclusive, intT "1"⟩,
    ⟨bn "fb", facetMaxInclusive, intT "3"⟩ ]

#guard entailedByRefutation (gExactQualRange "3") [⟨indI, exDp1, intT "2"⟩]
#guard !entailedByRefutation (gExactQualRange "2") [⟨indI, exDp1, intT "2"⟩]
#guard refuted (gExactQualRange "4")
#guard !(refuted (gExactQualRange "3"))

/-! ## The ≤-rule does not branch where a literal could be identified

`a : ≤ 2 dp`, `a dp 1`, `a dp "x"`, `a : ∃dp.xsd:integer`,
`a : ∃dp.¬xsd:integer` has a model: the two existentials are met by
`1` and `"x"`. The witnesses for them cannot be merged with a literal,
so the rule offers no branch rather than only the witness pair. With
`≤ 1 dp` the two provably different values violate the bound outright.
-/

private def gLiteralMerge (k : String) : Graph :=
  [ ⟨indI, rdfType, bnT "r"⟩,
    ⟨bn "r", owlOnProperty, .iri exDp1⟩,
    ⟨bn "r", owlMaxCardinality, cardLit k⟩,
    ⟨indI, exDp1, intT "1"⟩, ⟨indI, exDp1, strT "x"⟩,
    ⟨indI, rdfType, bnT "s1"⟩,
    ⟨bn "s1", owlOnProperty, .iri exDp1⟩,
    ⟨bn "s1", owlSomeValuesFrom, .iri xsdInteger⟩,
    ⟨indI, rdfType, bnT "s2"⟩,
    ⟨bn "s2", owlOnProperty, .iri exDp1⟩,
    ⟨bn "s2", owlSomeValuesFrom, bnT "c2"⟩,
    ⟨bn "c2", L4Factoidal.OWL.owlDatatypeComplementOf, .iri xsdInteger⟩ ]

#guard !(refuted (gLiteralMerge "2"))
#guard refuted (gLiteralMerge "1")

/-! ## A literal successor counts against `≤ k p.DR` (`New-Feature-DataQCR-001`)

Two different `xsd:string` values entail `≥ 2 hasName.xsd:string`: the
negation `≤ 1 hasName.xsd:string` is violated by the two literals, which
are provably in the data range. One string and one integer do not
entail it. -/

private def gTwoNames (second : Term) : Graph :=
  [ ⟨indI, exDp1, strT "Meg Griffin"⟩, ⟨indI, exDp1, second⟩ ]

private def cMinTwoStrings : Graph :=
  [ ⟨indI, rdfType, bnT "q"⟩,
    ⟨bn "q", owlOnProperty, .iri exDp1⟩,
    ⟨bn "q", owlMinQualifiedCardinality, cardLit "2"⟩,
    ⟨bn "q", owlOnDataRange, .iri xsdString⟩ ]

#guard entailedByRefutation (gTwoNames (strT "Megan Griffin")) cMinTwoStrings
#guard !entailedByRefutation (gTwoNames (intT "2")) cMinTwoStrings
#guard !entailedByRefutation (gTwoNames (strT "Meg Griffin")) cMinTwoStrings

end L4Factoidal.OWL.Refute
