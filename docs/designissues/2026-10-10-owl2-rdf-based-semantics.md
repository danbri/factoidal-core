# OWL 2 RDF-Based Semantics in the Lean tree (2026-10-10)

Tracking issue: <https://github.com/danbri/factoidal/issues/721>.
Owner decision, 2026-10-10, verbatim: "721 Add an OWL 2 RDF-Based
Semantics". Recorded in `CLAUDE.md`, "OWL 2 test scoring".

Specification: OWL 2 Web Ontology Language RDF-Based Semantics (Second
Edition), W3C Recommendation 11 December 2012,
<https://www.w3.org/TR/owl2-rdf-based-semantics/>. Section and table
numbers below are that document's unless another document is named.

## 0. Result

* `l4owl-probe --rdf-based` judges the 699 units (case, test type) of
  the 482 cases of `all.rdf` annotated `test:semantics RDF-BASED`. The
  12 PositiveEntailmentTests of issue 721 (DIRECT, species FULL only)
  are among them.
* Scores and the per-unit comparison with the other OWL lines: § 6.
* Lean: `L4Factoidal/OWL/RdfBased/Spec.lean` (36 interpretation
  conditions, entailment, a satisfiability witness), `Rules.lean` (17
  rule constructors, each proved sound), `Witness.lean` (existential
  successors for `owl:someValuesFrom`, proved sound over an extended
  blank-node assignment), `Engine.lean` (executable rules, each output
  proved to be a rule application), `Clash.lean` (5 clash rows, each
  proved: no interpretation that meets the conditions satisfies a graph
  the row fires on; § 4.5), `Tests.lean` (145 `#guard` cases, positive
  and negative per rule and per clash row). No `sorry`, no `axiom`, no
  `native_decide`, no `partial`.
* PositiveEntailmentTest: 147 pass, 54 fail (out of 201). The 12 cases
  of issue 721: 7 pass, 5 fail. The two soundness cells
  (NegativeEntailmentTest and ConsistencyTest `fail`) are 0.
* InconsistencyTest: 55 pass, 73 fail (out of 128). The clash rows and
  the two rules of § 4.5 moved 11 units from fail to pass (44 pass
  before them), among them `WebOnt-Thing-005` of
  https://github.com/danbri/factoidal/issues/733.
* One method the task brief proposed, "the DL refuter's entailments
  carry over" under the correspondence theorem, does not follow from
  the text of Theorem 7.1 and is not used. § 4.2 gives the text and
  the condition under which it would hold.

## 1. What the RDF-Based Semantics is

An OWL 2 RDF-Based interpretation (Definition 4.2) is a D-interpretation
`I = (IR, IP, IEXT, IS, IL, LV)` of the RDF Semantics that meets every
semantic condition of § 5. IR is the universe; IEXT maps each property
to a set of pairs; the class extension of a class `c` is
`ICEXT(c) = { x | (x, c) ∈ IEXT(I(rdf:type)) }` (§ 4.5). The parts of
the universe (§ 4.4, Table 4.1) are class extensions of vocabulary
classes: IC = `ICEXT(I(rdfs:Class))`, IP = `ICEXT(I(rdf:Property))`,
IX = `ICEXT(I(owl:Ontology))`, and so on.

Satisfaction (Definition 4.3) is satisfaction of the RDF graph as a
D-interpretation, by an interpretation that meets the § 5 conditions.
Entailment (Definition 4.5): `S1` entails `S2` when every OWL 2
RDF-Based interpretation that satisfies `S1` satisfies `S2`.

Two properties of the semantics decide most of what the regime can
and cannot do.

1. Every triple has a meaning. Classes, properties and ontologies are
   individuals of IR. A class expression in a conclusion (a blank node
   with `owl:someValuesFrom`, `owl:unionOf`, ...) asks for an
   individual of IR that carries those triples.
2. The conditions for class EXPRESSIONS are "if-then" conditions (§ 5,
   "Notes on the Form of Semantic Conditions"). They constrain an
   expression that exists; they do not make one exist. The conditions
   that would (the "comprehension conditions", § 8) are informative
   only. § 9 says why: "combining the comprehension conditions with the
   normative set of semantic conditions in Section 5 would lead to
   formal inconsistency of the resulting semantics (Issue 119)."

So `a p b` does not RDF-Based-entail `a rdf:type [owl:onProperty p;
owl:someValuesFrom owl:Thing]`: no condition makes the restriction
exist. Under OWL 1, whose RDF-compatible semantics had normative
comprehension conditions, it did. Several WebOnt cases still carry the
OWL 1 expectation (§ 7).

## 2. What the regime proves, and what it cannot

OWL 2 Profiles, Table 10, gives ontology consistency, class expression
satisfiability and subsumption, instance checking and conjunctive query
answering under the RDF-Based Semantics as "Undecidable" in every
complexity measure. No procedure decides entailment, so this regime
does not try to. It PROVES entailments (a derivation from sound rules)
and PROVES inconsistency (a clash row). It never proves that an
entailment does not hold or that a graph is consistent.

OWL 2 Conformance § 2.2.1 has the vocabulary for this: an entailment
checker returns True, False, Unknown or Error; True "indicates that the
relevant entailment holds", Unknown "indicates that the algorithm used
by the checker is not able to determine if the entailment holds". This
regime returns True or Unknown, never False.

## 3. Verdict buckets

| test type | `pass` | `not-refuted` | `fail` |
|---|---|---|---|
| PositiveEntailmentTest | entailment PROVED (one blank-node mapping of the conclusion into the derived graph, RDF 1.1 Semantics interpolation lemma) | — | not proved |
| InconsistencyTest | inconsistency PROVED (a clash row fired) | — | not proved |
| NegativeEntailmentTest | — (never) | the engine derived no instance of the non-conclusion | the engine derived it: it claims an entailment the catalog denies |
| ConsistencyTest | — (never) | no clash row fired | a clash row fired on a premise the catalog calls consistent |

`not-refuted` is never counted as proved. A NegativeEntailmentTest or
ConsistencyTest that "passes by deriving nothing" (skill
`measuring-inference` § 3) lands in `not-refuted`, where it says what
was measured: the engine did not contradict the catalog. The `fail`
cells of those two rows are the soundness check of the regime: a sound
engine cannot fill them unless the catalog is wrong.

The score line grammar is `N pass, M fail, K not-refuted, U
unsupported (out of T)`; `tools/lean-scoreboard.sh` counts
`not-refuted` as "other".

## 4. The inference method

The regime (`Harness/OwlProbe.lean`, `rbClosureIO`; pure counterpart
`RdfBased.rbSaturate`) computes the OWL 2 RL/RDF closure of the
premise, then up to three rounds of (the RDF-Based rules of § 4.3 and
the existential witnesses of § 4.4, the RL closure again), under one
wall-clock cap per unit. The triples that mention a comprehension
witness are removed (§ 4.1) from each closure before the next round
reads it. Then the conclusion is matched or the clash rows are checked.

Each step is an entailment: if some blank-node assignment makes the
input graph true in an interpretation that meets the bundle, some
assignment makes the output graph true in that interpretation. The
steps compose, so a conclusion graph matched into the last graph is
entailed by the premise.

### 4.1 The OWL 2 RL/RDF closure as a sound base

OWL 2 Profiles § 4.3: "This section presents a partial axiomatization
of the OWL 2 RDF-Based Semantics in the form of first-order
implications; this axiomatization is called the OWL 2 RL/RDF rules."
§ 4: an implementation of these rules "can also be used with arbitrary
RDF graphs ... Such an implementation will, however, still produce only
correct entailments". So the W3C rule rows are sound for the RDF-Based
Semantics on any graph.

A correction to the task brief and to issue 721's comment: Theorem PR1
is NOT the soundness statement. PR1 is about OWL 2 RL ontologies under
the DIRECT Semantics ("O1 entails O2 under the OWL 2 Direct Semantics
if and only if FO(RDF(O1)) ∪ R entails FO(RDF(O2))"), a completeness
result for a fragment. Soundness for the RDF-Based Semantics is the
"partial axiomatization" statement above.

In this tree, `OWL/RLSemantics.lean` proves `rl_derives_holds`: every
triple the rule relation derives is true in every interpretation that
meets `RlConditions`, each of whose fields cites the table row it
transcribes. Two things stand between that theorem and "sound for the
RDF-Based Semantics", and the regime handles both:

1. **Three `[ext]` rows read the § 8 comprehension conditions.**
   `caxDwToComplement`, `clsMaxqc1ToComplement` and
   `minCard1Comprehension` mint blank nodes standing for class
   expressions (labels `__rl_comp__…`, `__rl_minc1__…`). Their conditions
   (`RlCondCompDw`, `RlCondCompMqc`, `RlCondMinc1`) are not normative.
   The regime removes every triple that mentions such a label
   (`RdfBased.withoutCompWitness`) before any judgement. The runner
   prints how many closures contained one
   (`closures_with_comprehension_witness`; 699 of 699, because
   `minCard1Comprehension` fires for every `owl:ObjectProperty`).
   What this does not exclude: a triple about named resources that the
   RL closure derived THROUGH a witness. § 8 states the gap.
2. **No Lean theorem states `RdfBasedConditions i → RlConditions i`.**
   `RlConditions` also constrains two reserved helper predicates of the
   unified layer (`urn:cl:def:listMember`, `…typedAllMembers`), which no
   RDF-Based interpretation interprets; a bridge must extend the
   interpretation at those IRIs. The per-row citations are checked by
   reading, not by proof. § 8 states the gap.

The PositiveEntailmentTest-only comprehension layer of the RL and DL
regimes (`OWL/Comprehension.lean`) is not used: it is § 8 by its own
header. Neither is the class-expression materialisation pass of `--dl`
(`OWL/Materialise.lean`), which is argued for the Direct Semantics.

### 4.2 The DL refuter: what Theorem 7.1 says, and why it is not used

Theorem 7.1 (OWL 2 Correspondence Theorem), § 7.2, for RDF graphs
`G1*`, `G2*` that are OWL 2 DL ontologies in RDF graph form and
mutually meet the restrictions of OWL 2 Structural Specification § 3:
"there exist RDF graphs G1 and G2 that are OWL 2 DL ontologies in RDF
graph form, such that ... F(G1) OWL 2 Direct entails F(G1*) ..., and
F(G1*) OWL 2 Direct entails F(G1) ...; [the same for G2, G2*]; If
F(G1) OWL 2 Direct entails F(G2) with respect to F(D), then G1 OWL 2
RDF-Based entails G2 with respect to D."

The theorem is about the SUBSTITUTE pair `(G1, G2)`, not about the
original pair. § 7.1 works an example in which `F(G1*)` Direct-entails
`F(G2*)` and `G1*` does not RDF-Based-entail `G2*`, for four reasons
(an annotation, a declaration, an ontology IRI, a class expression in
the conclusion). The proof in § 7.3 builds `G1` from `G1*` by ADDING
declarations, annotations and tautologies that embed `G2*`'s class
expressions ("balancing"). A Direct Semantics entailment of `G2*` from
`G1*` therefore carries over to the original pair only when the pair is
already balanced (§ 7.3, Definition (Balanced): every non-built-in IRI
declared for each entity type; every literal of `G2` in `G1`; `G2` has a
single header triple with a blank node; no annotations, ontology
properties or deprecations in `G2`; every declaration, property
expression, class expression, data range and sequence of `G2` also a
subgraph of `G1`).

That condition is checkable, but the regime does not use it, because
two links of the argument are not proofs in this tree: the § 7.3 text is
itself a proof SKETCH ("some technical aspects of the theorem are only
coarsely treated"), and the tableau refuter (`OWL/Refute.lean`, `partial
def`) has no soundness theorem for the Direct Semantics either. The
task's rule "a rule without a proof does not ship" excludes it.
Issue-ready text for a separately labelled line, the way `--dl` prints
`[closure or refutation]`: § 8.

### 4.3 Rules taken from the § 5 conditions

Each rule is a constructor of `RdfBased.RbDerives`; `rbDerives_sound`
proves its conclusion true in every interpretation that meets
`RdfBasedConditions`, under the blank-node assignment that makes the
premise graph true. No `RbDerives` rule mints a blank node; the
existential witnesses of § 4.4 do, under their own theorem.

| rule | derives | conditions read |
|---|---|---|
| `ax` (goal-directed) | the premise-free triples: `E rdf:type rdfs:Class` (Table 5.2 col. 2), `E1 rdfs:subClassOf E2` and `owl:equivalentClass` for the inclusions of Table 5.2 col. 3 and Table 5.1, the part, domain and range of 48 rows of Table 5.3, `owl:Nothing owl:oneOf rdf:nil` | 5.1, 5.2, 5.3, 5.5, 5.8, 5.9 |
| `vocabType` | `x rdf:type E2` from `x rdf:type E1` when `ICEXT(E1) ⊆ ICEXT(E2)` by Table 5.1/5.2 | 5.1, 5.2 |
| `universal` (goal-directed) | `x rdf:type owl:Thing`, `x rdf:type rdfs:Resource` | 5.2 |
| `compSym` | `b owl:complementOf a` from `a owl:complementOf b` | 5.4 |
| `allDiff` | `aj owl:differentFrom ak`, `j ≠ k`, from `z rdf:type owl:AllDifferent` and `owl:members` or `owl:distinctMembers` | 5.9, 5.10 |
| `funSingleton` | `p rdf:type owl:FunctionalProperty` when `p rdfs:range c` and `c owl:oneOf (a)` | 5.5, 5.8, 5.13 |
| `ifpSingleton` | `p rdf:type owl:InverseFunctionalProperty`, the domain dual | 5.5, 5.8, 5.13 |
| `typeDomainSub` | `x rdfs:subClassOf y` from `rdf:type rdfs:domain y` and `x rdf:type rdfs:Class` | 5.8 |
| `avfRange` | `p rdfs:range c` from `owl:Thing rdfs:subClassOf r`, `r owl:onProperty p`, `r owl:allValuesFrom c` | 5.2, 5.3, 5.6, 5.8 |
| `svfDomain` | `p rdfs:domain c` from `r owl:someValuesFrom owl:Thing`, `r owl:onProperty p`, `r rdfs:subClassOf c` | 5.2, 5.3, 5.6, 5.8 |
| `emptySubProp` | `p rdfs:subPropertyOf q` when two ranges of `p` are datatypes with disjoint value spaces and `q rdf:type rdf:Property` | 5.8; the datatype map (§ 4.1; RDF 1.1 Semantics § 9) |
| `oneOfSub` | `c1 rdfs:subClassOf c2` when every member of `c1`'s `owl:oneOf` list is a member of `c2`'s | 5.5, 5.8 |
| `unionSub` | `c1 rdfs:subClassOf c2` when every operand of `c1`'s `owl:unionOf` list is an operand of `c2`'s; both lists non-empty | 5.4, 5.8 |
| `interSub` | `c1 rdfs:subClassOf c2` when every operand of `c2`'s `owl:intersectionOf` list is an operand of `c1`'s; both lists non-empty | 5.4, 5.8 |
| `literalValue` | `s p "s2"^^d` from `s p "s1"^^u` when `u` is `d` or `u owl:sameAs d`, `d` is `xsd:decimal` or `xsd:integer`, and `s1`, `s2` are lexical forms of `d` with one value | § 4.2 (`IL`), 5.9 (`owl:sameAs`), § 3.3 (datatype map) |
| `hvEqProp` | `p owl:equivalentProperty q` from: `p` and `q` functional, both with domain `d`, `d rdfs:subClassOf r1`, `d rdfs:subClassOf r2`, `r1` (`r2`) an `owl:hasValue v` restriction on `p` (`q`) | 5.6, 5.8, 5.9, 5.13 |
| `minCardSucc` | `x rdf:type z` from `z owl:minCardinality n` with n = 0 or 1 (an integer literal), `z owl:onProperty p`, `x p y`; a restriction minted by the RL closure's comprehension rows is not read (§ 4.5) | 5.6, § 4.2 |
| `universal`, premise-directed (`universalForKeys`) | `x rdf:type owl:Thing` for every subject `x` of a key property of `owl:Thing owl:hasKey (…)`, which the RL row `prp-key` reads | 5.2 |

Table 5.4 does not say what `owl:unionOf ()` or `owl:intersectionOf ()`
means; its conditions name `c1, ..., cn` with no case for n = 0. The
bundle states the two conditions for non-empty lists only, and the two
rules read only non-empty lists (`#guard` cases on `rdf:nil` operands in
`Tests.lean`).

### 4.4 Existential witnesses (Table 5.6, `owl:someValuesFrom`)

Table 5.6: if `(z, c) ∈ IEXT(I(owl:someValuesFrom))` and
`(z, p) ∈ IEXT(I(owl:onProperty))` then
`ICEXT(z) = {x | ∃ y : (x, y) ∈ IEXT(p) and y ∈ ICEXT(c)}`. So
`x rdf:type r`, `r owl:someValuesFrom c`, `r owl:onProperty p` entail
`x p _:w`, `_:w rdf:type c`: the condition makes the successor exist,
and a blank node asks only that some element be assigned to it (RDF 1.1
Semantics § 5.2). This condition is normative, in § 5; it is different
from the § 8 comprehension conditions, which make a CLASS EXPRESSION
exist.

`Witness.lean`, `svfWits_sound`: for a list of witnesses whose labels
are fresh for the graph and name one (subject, property, class) each,
every assignment that makes the graph true extends, at those labels
only, to one that makes the graph and every witness triple true. The
executable side (`svfWitsFor`) checks freshness and naming at run time
and drops a candidate that fails; `svfWitsFor_ok` proves the output
meets the theorem's premise. So the theorem needs no proof that the
label encoding is injective. Witnesses are goal-directed: the regime
adds them only for properties that the conclusion graph uses with a
blank-node object. Three rounds bound the depth of witness chains.

"Goal-directed": the two premise-free families add only what the
conclusion graph names (`axiomsFor`: rows whose subject IRI the goal
mentions; `universalFor`: only for a goal `rdf:type owl:Thing` or
`rdfs:Resource`). Adding them to every graph would put Table 6's
axiomatic triples, with their cyclic `rdfs:subClassOf` lattice, into
every closure; `measuring-inference` § 10 records that cost. The other
rules read the closure alone, one pass with at most two nested lookups.

### 4.5 Clash rows (`Clash.lean`)

The regime's inconsistency check is the OWL 2 RL/RDF clash rows
(`detectClashPlusI`) OR the rows below (`RdfBased.rbClashAny`). Each row
is a constructor of `RdfBased.RbClash`; `rbClash_sound` proves that no
blank-node assignment makes the graph true in an interpretation that
meets `RdfBasedConditions`, so the graph is OWL 2 RDF-Based
inconsistent (Definition 4.4). `rbClashAny_spec` proves that the
executable check answers `true` only on a graph `RbClash` holds of. The
harness prints `CLASH-BY-RDF-BASED-ROWS <id>` when one of these rows,
and no RL row, decided a unit.

| row | premise | conditions read |
|---|---|---|
| `thingEnum` | `c owl:oneOf (a)` or `c owl:oneOf ()`, with `c` = `owl:Thing`, `rdfs:Resource`, or `owl:Thing rdfs:subClassOf c` | 5.1, 5.2, 5.5, 5.8 |
| `svfAvfDt` | `x rdf:type r1`, `r1 owl:someValuesFrom d1`, `x rdf:type r2`, `r2 owl:allValuesFrom d2`, both on one property, `d1` and `d2` datatypes with disjoint value spaces | 5.6, the datatype map |
| `litSucc` | the successor that `x`'s `owl:someValuesFrom` restriction asks for is a member of the filler and of every `owl:allValuesFrom` filler and range on that property; one of those classes is an enumeration of literals; each listed literal is excluded by one of those classes, or as a value of `x` for that property | 5.4, 5.5, 5.6, 5.7, 5.8, 5.9, 5.15, § 4.2 |
| `intSucc` | the same successor, where one class is an integer datatype restriction and another class excludes every integer within its bounds | 5.6, 5.7, 5.8, § 4.2 |
| `intOneSucc` | the same successor, where one class is an integer datatype restriction whose bounds hold one integer `k`, and `k` is excluded as a value of `x` for that property | 5.6, 5.7, 5.9, 5.15, § 4.2 |

A literal is excluded from a class (`LitOut`) when the class is a
datatype whose value space does not hold the literal's value, an
enumeration whose literals all have other values, an integer
restriction whose bounds exclude the value, or the datatype complement
(Table 5.4, `owl:datatypeComplementOf`) of an enumeration that lists the
value. A literal is excluded as a value of `x` for `p` (`PairOut`) by an
`owl:NegativePropertyAssertion` with source `x`, property `p` and a
target value with the literal's value (Table 5.15), or by a property `q`
with `p owl:propertyDisjointWith q` (either way round) and a triple
`x q m` where `m` has the literal's value (Table 5.9).

**Issue 733, checked against the text.** The argument in the issue is
correct. Table 5.5: `(z, s) ∈ IEXT(I(owl:oneOf))` iff `z ∈ IC` and
`ICEXT(z) = {a1, …, an}`; Table 5.2: `ICEXT(I(owl:Thing)) = IR`,
`ICEXT(I(owl:Nothing)) = ∅`. With `owl:Thing owl:oneOf ( s )`, IR =
`{I(s)}`, so `I(owl:Thing) = I(owl:Nothing) = I(s)`, and `I(s)` is in
`ICEXT(I(owl:Thing))` and not in `ICEXT(I(owl:Nothing))`: a
contradiction. One correction to the wording: the issue cites "RDF 1.1
Semantics § 4" for IR ≠ ∅; the RDF-Based Semantics refers to the 2004
RDF Semantics and states the condition itself (§ 4.2, "a nonempty set";
Table 5.1, "IR: S ≠ ∅"). The contradiction above does not need it; the
row's `owl:oneOf ()` case does.

**Nine conditions added to the bundle.** Each is true in every OWL 2
RDF-Based interpretation; the witness of § 5 meets each one.

* `CondLitOutsideDt` (§ 4.2 with the RDF Semantics' general conditions
  for datatypes): a literal whose value is outside the value space of a
  datatype `e`, or that is ill-typed (IL not in LV), is not in
  `ICEXT(I(e))`. `litOutsideDt` decides it for the 13 integer datatypes
  of § 3.3 (value against the bounds of XSD 1.1 Part 2 § 3.4), across
  the value-space families of `RL.xsdValueSpacesDisjoint`, and for an
  `xsd:float` or `xsd:double` literal against `owl:real`,
  `owl:rational`, `xsd:decimal` and the integer datatypes (OWL 2
  Structural Specification § 4.2: "the value spaces of xsd:double,
  xsd:float, and xsd:decimal are pairwise disjoint … the value space of
  owl:real is defined as being disjoint with the value spaces of
  xsd:double and xsd:float").
* `CondOneOfLitExcl` (Table 5.5 with § 4.2): a literal whose value
  differs from that of every literal of an enumeration is not a member.
* `CondLitSame` (§ 4.2): two literals with one value denote one element
  (equal integers of two integer datatypes are one value; OWL 2
  Structural Specification § 4.2).
* `CondDatatypeComplementSub` (Table 5.4): a member of the datatype
  complement of `d` is not a member of `d`.
* `CondIntRestrMembers` and `CondIntRestrExcl` (Table 5.7 with XSD 1.1
  Part 2 § 4.3.7 – § 4.3.10): the members of an integer datatype
  restriction are integers within the bounds `intRestrBounds` computes
  from the facet pairs (`xsd:minInclusive`, `minExclusive`,
  `maxInclusive`, `maxExclusive` with integer values; any other pair
  leaves the bounds as they are, so the bounds contain the value space).
* `CondMinCardLe1Sup` (Table 5.6, `owl:minCardinality`, the ⊇ half for
  n = 0 and n = 1): a subject with a successor is a member.
* `CondPropertyDisjointOnly` (Table 5.9, `owl:propertyDisjointWith`,
  left to right): the two extensions share no pair.
* `CondNpaTargetValue` (Table 5.15, the `owl:targetValue` form): the
  source is not related to the target value by the assertion property.

Two readings these conditions do not take. Distinctness of two literals
(`litDistinct`) is claimed only for well-typed integers and for
`xsd:string` lexical forms in the `xsd:string` lexical space: an
ill-typed literal denotes an element outside LV, and nothing says which.
Table 5.7 reads "(z1, v1) ∈ IEXT(f1), …, (zn, vn) ∈ IEXT(fn)", one pair
per member of the facet list; the conditions apply only when every
member of the list carries at least one pair that the graph states, so
every pair read is part of such a choice.

The witness interpretation changed in five places, each because it
related every pair at a property a new condition constrains:
`owl:datatypeComplementOf` relates `x` to `y` only when no element is in
both extensions; `owl:minCardinality` and `owl:targetValue` relate
nothing to the element the witness's literals denote; and
`owl:propertyDisjointWith` relates only pairs with `rdf:first` (whose
extension is empty) on one side. `owl:real` and `owl:rational` get the
numeric family, so their extensions do not hold the literals' element.
The other conditions hold in the witness as it was: literals denote one
element outside every datatype extension, and the witness has no
sequence other than `rdf:nil`, so the enumeration and restriction
premises are never met.

**A rule that reads the raw closure can read a § 8 witness (found
2026-10-10).** The regime applies the rules to the RL closure before
`withoutCompWitness` removes the witnesses (§ 4.1, gap A). The RL row
`minCard1Comprehension` mints a restriction `__rl_minc1__p` with
`owl:minCardinality 1` for every property. The first version of
`minCardSucc` read it, typed every subject with it, and the closure's
`__rl_minc1__p rdfs:subClassOf owl:Thing` gave `x rdf:type owl:Thing`;
`New-Feature-Keys-002` passed through that path. The conclusion was
true (Table 5.2 puts every element in `owl:Thing`), but the derivation
read a non-normative condition. `minCardSucc` now skips a restriction
that is a comprehension witness (`subjIsCompWitness`, a `#guard` case),
and the unit passes through `universalForKeys` instead. The 16 older
rules still read the raw closure; gap A
(https://github.com/danbri/factoidal/issues/731) covers them.

## 5. The Lean files

* `L4Factoidal/OWL/RdfBased/Spec.lean`. `RdfBasedConditions`, 36
  fields, each a transcription of a table row or of § 4.2 (or, where a
  rule reads one half of an "iff", that half; § 4.5 lists the nine added
  for the clash rows). The bundle admits every
  OWL 2 RDF-Based interpretation, so `RbEntails` (entailment over the
  bundle) implies Definition 4.5 entailment. `witness_conditions`: an
  interpretation that meets all 36; `rbEntails_not_everything`:
  `RbEntails [] [owl:Thing rdfs:subClassOf owl:Nothing]` is false. The
  witness exists because a bundle no interpretation meets would make
  every entailment statement true (`measuring-inference` § 4).
* `Rules.lean`. `RbDerives`, `rbDerives_sound`, `rbDerives_entailed`.
  Anti-pattern 29 check: no rule hypothesis contains its conclusion;
  each conclusion is reached through a condition of the bundle (the
  proof terms end in `hc.<field>`, never in a premise).
* `Witness.lean`. `SvfWit`, `WitsOk`, `svfWits_sound`,
  `svfWits_entailed`, the executable `svfWitsFor` and `svfWitsFor_ok`.
  Anti-pattern 29 check: the premise `WitsOk` states membership,
  freshness and naming; the successor comes from
  `hc.someValuesFromSub`.
* `Engine.lean`. The executable rules, `rbConclusions_derives` (every
  output is an `RbDerives` application), `rbConclusions_entailed`,
  `withoutCompWitness`, `rbRound` (rules, then witnesses), `rbSaturate`.
* `Clash.lean`. `RbClash` (5 rows), `rbClash_sound`, `rbClash_unsat`,
  `rbClash_entails`, the executable `rbClashAny` and `rbClashAny_spec`.
  Anti-pattern 29 check: no row premise states that a class is empty,
  that an element is outside a class or that a pair is outside a
  property; each contradiction is reached through conditions of the
  bundle (`hc.nothing`, `hc.disjointDatatypes`, `hc.litOutsideDt`,
  `hc.oneOfLitExcl`, `hc.intRestrExcl`, `hc.datatypeComplementSub`,
  `hc.npaTargetValue`, `hc.propertyDisjointOnly`).
* `Tests.lean`. 145 `#guard` cases: for each rule and each clash row a
  positive and a negative case, the literal-value functions, and
  end-to-end cases on the shapes of
  `WebOnt-Class-003`, `WebOnt-imports-010`, `WebOnt-I5.3-015` and
  `WebOnt-someValuesFrom-003` (a two-step witness chain).

## 6. Scores

Measured 2026-10-10 with `formal/lean4/.lake/build/bin/l4owl-probe
--rdf-based --dir third_party/testing/owl all.rdf`, one process, other
agents on the same four CPUs: 114 s and 126 s wall clock in two runs, `cap_hits=0`,
`parse_failures=0`, `rule_triples=53360`.

| test type | pass | fail | not-refuted | total |
|---|---|---|---|---|
| PositiveEntailmentTest | 147 | 54 | 0 | 201 |
| NegativeEntailmentTest | 0 | 0 | 23 | 23 |
| ConsistencyTest | 0 | 0 | 347 | 347 |
| InconsistencyTest | 55 | 73 | 0 | 128 |
| all units | 202 | 127 | 370 | 699 |

Score lines: PositiveEntailmentTest 147 pass, 54 fail (out of 201);
InconsistencyTest 55 pass, 73 fail (out of 128); NegativeEntailmentTest
0 pass, 0 fail, 23 not-refuted (out of 23); ConsistencyTest 0 pass, 0
fail, 347 not-refuted (out of 347); all units 202 pass, 127 fail, 370
not-refuted, 0 unsupported (out of 699).

The clash rows and rules of § 4.5 (measured 2026-10-10 on the same
command; 133 s wall clock with other agents' runs on the four shared
CPUs, `cap_hits=0`, `rule_triples=53555`, `proved_by_rules=24`):
before them, InconsistencyTest 44 pass, 84 fail (out of 128) and all
units 191 pass, 138 fail, 370 not-refuted (out of 699). Units moved from
fail to pass, with the row (`CLASH-BY-RDF-BASED-ROWS` lines):

* `WebOnt-Thing-005` — `thingEnum`;
* `inconsistent_datatypes` — `svfAvfDt` (`xsd:integer` and `xsd:string`);
* `Inconsistent Byte Filler` — `litSucc`, `6542145` outside `xsd:byte`;
* `Contradicting datatype Restrictions` — `litSucc`, the enumeration
  `{2, 3}` against the restriction `xsd:integer ≥ 4`;
* `Different types in Datatype Restrictions and Complement` and
  `Inconsistent Data Complement with the Restrictions` — `litSucc`,
  `3` against the complement of `{3}`, `4` against `{2, 3}`;
* `datatype-restriction-min-max-inconsistency` — `intSucc`, `≥ 18`
  against `≤ 10`;
* `Inconsistent Disjoint Dataproperties` — `intOneSucc`, `[10, 10]`
  against `dp1 owl:propertyDisjointWith dp2` with `a dp1 10`;
* `Minus Infinity is not in owl:real` — `litSucc`, `-INF`^^`xsd:float`
  outside `owl:real`, `-0`^^`xsd:integer` against the negative assertion
  with target value `0`^^`xsd:unsignedInt`;
* `WebOnt-disjointWith-010` — the rule `minCardSucc` types `_:x` with the
  restriction `_:n` (`owl:minCardinality 1`), then the RL row `cax-dw`
  reads `_:n owl:disjointWith _:n`;
* `New-Feature-Keys-002` — the rule `universalForKeys` types `Peter` and
  `Peter_Griffin` with `owl:Thing`, then the RL rows `prp-key` and
  `eq-diff1`.

The last two are decided by RL rows after the new rules, so the harness
prints no `CLASH-BY-RDF-BASED-ROWS` line for them; the first nine are.

No unit went from pass to fail; the two soundness cells stay 0.

* The two soundness cells (NegativeEntailmentTest `fail`,
  ConsistencyTest `fail`) are 0.
* `proved_by_rules=24`: PositiveEntailmentTest units the RL closure
  alone does not prove and the § 4.3 rules or § 4.4 witnesses do
  (`PROVED-BY-RDF-BASED-RULES` lines): `New-Feature-Keys-001`,
  `somevaluesfrom2bnode`, `WebOnt-AllDifferent-001`,
  `-AnnotationProperty-002`, `-Class-001`, `-Class-003`,
  `-FunctionalProperty-004`, `-I5.24-004`, `-I5.3-014`, `-I5.3-015`,
  `-I5.8-017`, `-InverseFunctionalProperty-004`, `-Nothing-002`,
  `-SymmetricProperty-003`, `-complementOf-001`, `-differentFrom-002`,
  `-distinctMembers-001`, `-equivalentProperty-004`,
  `-equivalentProperty-005`, `-imports-010`, `-oneOf-003`,
  `-someValuesFrom-001`, `-someValuesFrom-003`, `-unionOf-002`.
* The 12 cases of issue 721: 7 pass (`WebOnt-Class-001`, `-Class-003`,
  `-I5.3-015`, `-I5.8-017`, `-Nothing-002`, `-equivalentProperty-005`,
  `-imports-010`), 5 fail (`WebOnt-extra-credit-002`, `-003`, `-004`,
  `-I5.5-001`, `-I5.5-002`; § 7).
* Against the RL regime on the same 201 units (which uses the § 8
  comprehension layer): 10 units the RL line passes are not proved here
  (`bnode2somevaluesfrom`, `DisjointClasses-001`, `-003`,
  `New-Feature-DisjointDataProperties-002`,
  `-DisjointObjectProperties-002`, `-ObjectPropertyChain-BJP-002`,
  `-ObjectQCR-002`, `-SelfRestriction-002`, `WebOnt-I5.26-010`,
  `WebOnt-I5.5-005`). Each conclusion asks for an individual (a class
  expression, a list or an `owl:AllDifferent` node) that the
  comprehension layer mints; § 7, group 1.

### 6.1 The other OWL lines, before and after this work

One binary per state, one catalog per process, `--dl --refute-ms 3000`
for the DL regime; "before" is the tip this branch started from
(d4278a35), "after" is this work. Per-unit comparison of the FAIL lines:
no unit went from pass to fail on any line. The one change on every
line that judges it is `FS2RDF-literals-ar` [ConsistencyTest], fail to
pass, from the functional-syntax premise fallback (§ 9).

| line | before | after |
|---|---|---|
| species, `all.rdf` | 487 pass, 2 fail (out of 489) | 488 pass, 0 fail, 1 local-override (out of 489) |
| default run TOTAL, RL regime | 1233 pass, 222 fail, 2 skip (out of 1457) | 1234 pass, 221 fail, 2 skip (out of 1457) |
| type-negative-entailment, syntax-dl, semantics-direct, RL regime | 907 pass, 271 fail, 2 skip (out of 1180) | 909 pass, 269 fail, 2 skip (out of 1180) |
| fs-input, `[rdfxml-input]` | 83 pass, 20 fail (out of 103) | 84 pass, 19 fail (out of 103) |
| fs-input, `[fs-input]` | 84 pass, 19 fail (out of 103) | unchanged |
| type-inconsistency, `--dl` | 126 pass, 1 fail, 1 skip (out of 128) | unchanged |
| type-positive-entailment, `--dl`, all units | 400 pass, 12 fail (out of 412) | unchanged |
| type-consistency, `--dl`, all units | 570 pass, 13 fail (out of 583) | 571 pass, 12 fail (out of 583); ConsistencyTest 354 pass, 0 fail (out of 354) |
| syntax-dl, `--dl`, all units | 421 pass, 2 fail, 1 skip (out of 424) | 422 pass, 1 fail, 1 skip (out of 424) |
| type-negative-entailment, `--dl` | 46 pass, 0 fail (out of 46), `ne_refuter_checked=11` | unchanged |

## 7. Left failing, with the reason

PositiveEntailmentTest, 54 units, in four groups (30 + 19 + 3 + 2):

1. **The conclusion asks for an individual that no § 5 condition makes
   exist** (30): `bnode2somevaluesfrom`, `DisjointClasses-001`, `-003`,
   `New-Feature-DataQCR-001`, `-DisjointDataProperties-002`,
   `-DisjointObjectProperties-002`, `-ObjectPropertyChain-BJP-002`,
   `-ObjectQCR-001`, `-ObjectQCR-002`, `-SelfRestriction-002`,
   `WebOnt-Class-006`, `-FunctionalProperty-005`, `-I5.2-006`,
   `-I5.24-002`, `-I5.24-003`, `-I5.26-009`, `-I5.26-010`, `-I5.5-005`,
   `-Restriction-006`, `-cardinality-001`, `-002`, `-003`, `-004`,
   `-006`, `-description-logic-901`, `-903`, `-equivalentClass-006`,
   `-007`, `-unionOf-003`, `-unionOf-004`. A class expression, list or
   axiom node in the conclusion must denote an individual of IR (§ 1
   above); only the informative § 8 comprehension conditions would
   supply it. Not proved here; whether each one is entailed under the
   normative semantics is not decided by this regime.
2. **Reasoning by cases, by counting, or over datatype value spaces**
   (19): `Consistent-but-all-unsat`, `New-Feature-DisjointUnion-001`,
   `Qualified-cardinality-boolean`, `Qualified-cardinality-restricted-int`,
   `rdfbased-sem-restrict-maxqcr-inst-obj-one`, `WebOnt-I5.2-002`,
   `-I5.2-004`, `-I5.21-002`, `-I5.8-004`, `-I5.8-010`,
   `-description-logic-201`, `-202`, `-205`, `-206`, `-208`,
   `-equivalentClass-004`, `-oneOf-004`, `-SymmetricProperty-002`,
   `-TransitiveProperty-002`. The DL regime decides most of these with
   the tableau refuter under the Direct Semantics; § 4.2 says why that
   is not used here.
3. **Arithmetic over cardinalities** (3, all issue 721):
   `WebOnt-extra-credit-002`, `-003`, `-004`. "This test shows a
   relationship between integer multiplication and OWL Full" (the
   catalog's description). No rule here counts.
4. **The catalog's expectation has no § 5 condition behind it** (2,
   issue 721): `WebOnt-I5.5-001` ("rdf:first is a FunctionalProperty"),
   `-I5.5-002` (`rdf:rest`). § 5, "Sequence expressions": "there are no
   semantic constraints that enforce "well-formed" sequence structures.
   So, for example, it is possible for a sequence head s to refer to
   more than one sequence." An interpretation in which one node has two
   `rdf:first` values meets § 5, so these are not entailments of the
   2012 semantics; they are OWL 1 era expectations. 🧭 Owner question
   in § 8.

InconsistencyTest, 73 units: no RL clash row and no row of § 4.5 fires
on the closure (84 before § 4.5; § 6 lists the 11 that moved).

1. **Counting** (4): `one=two` (a 1:1 and a 2:1 correspondence between
   the members of a three-element enumeration), `WebOnt-maxCardinality-001`
   (three pairwise `owl:differentFrom` successors against
   `owl:maxCardinality 2`), `WebOnt-I5.8-001` (`owl:cardinality 257`
   against the 256 values of `xsd:byte`), `WebOnt-I5.8-003`
   (`owl:cardinality 129` against the 128 values of `xsd:byte ∩
   xsd:unsignedInt`). Each needs the number of elements of a set; no
   row here counts.
2. **Value spaces not modelled** (3): `Datatype-Float-Discrete-001`
   (no `xsd:float` value lies strictly between 0 and the smallest
   positive subnormal; needs the float lexical mapping),
   `Inconsistent String Pattern with Disjoint Dataproperties` (the
   language of the `xsd:pattern` `a(b|c)` is `{ab, ac}`),
   `Contradicting-dateTime-restrictions` (the order of `xsd:dateTime`
   values with time zones).
3. **Not analysed for this regime** (66): the 60
   `WebOnt-description-logic-*` cases, `New-Feature-Rational-002`,
   `-TopObjectProperty-001`, `WebOnt-I5.5-003`, `-I5.5-004`,
   `-miscellaneous-203`, `-miscellaneous-204`. The DL
   regime decides most of them with the tableau refuter (unions,
   nominals, cardinalities); § 4.2 says why that is not used here.

## 8. Gaps, with issue-ready text

The coordinator files these; each names the units above that stay
failing until it closes.

**A. Title: OWL RDF-Based regime: prove the OWL 2 RL/RDF base sound against
`RdfBasedConditions`.** Body: `rl_derives_holds` proves the RL rule
relation sound against `RlConditions`. The RDF-Based regime relies on it
without a theorem `RdfBasedConditions i → RlConditions i'` for an
interpretation `i'` that agrees with `i` off the reserved helper IRIs
`urn:cl:def:listMember` and `urn:cl:def:typedAllMembers`. Three `[ext]`
rows (`caxDwToComplement`, `clsMaxqc1ToComplement`,
`minCard1Comprehension`) read the informative § 8 comprehension
conditions; the regime drops every triple that mentions their witness
labels, but a triple about named resources derived THROUGH a witness is
not excluded. Repair: run the regime's closure without those three rows
(a closure variant with a proved relation to `Derives` minus those
constructors), and prove the bridge. Design record:
`docs/designissues/2026-10-10-owl2-rdf-based-semantics.md` § 4.1.

**B. Title: OWL RDF-Based regime: a separately labelled line for Direct
Semantics refutations on balanced pairs (Theorem 7.1).** Body: Theorem
7.1 carries a Direct Semantics entailment to the RDF-Based Semantics for
the substitute pair it constructs, not for the input pair. For an input
pair that is already balanced (§ 7.3, Definition (Balanced)), the two
coincide. Implement the balanced-pair check over `OWL/SyntaxDL.lean`'s
reverse mapping and print a second line, `[rdf-based or balanced
refutation]`, the way `--dl` prints `[closure or refutation]`. It cannot
be counted as proved until the refuter has a soundness theorem for the
Direct Semantics and § 7.3's sketch is checked for the constructs the
refuter reads. Units it would address: most of § 7 group 2 and the 83
InconsistencyTest units that need the refuter.

**C. Filed as https://github.com/danbri/factoidal/issues/733; closed by
the `thingEnum` row of § 4.5.** `WebOnt-Thing-005` [InconsistencyTest]
passes. § 4.5 records the one correction to the issue's wording.

Closed during this work, so not filed: existential witnesses (§ 4.4),
literal denotations through a datatype IRI alias (`literalValue`), and
`owl:hasValue` with functional properties giving
`owl:equivalentProperty` (`hvEqProp`).

**🧭 Owner question. Title: OWL 2 catalog: `WebOnt-I5.5-001` and `-002`
expect `rdf:first` / `rdf:rest` to be functional; § 5 of the RDF-Based
Semantics has no such condition.** Body: both cases are
PositiveEntailmentTests annotated DIRECT and RDF-BASED with species
FULL. § 5, "Sequence expressions": "there are no semantic constraints
that enforce "well-formed" sequence structures. So, for example, it is
possible for a sequence head s to refer to more than one sequence."
Options: (1) leave them failing (current); (2) record them as disputed
fixtures (local overrides naming the issue, counted apart, stale if they
ever pass), as for https://github.com/danbri/factoidal/issues/711.
Recommendation: (2); the specification text is explicit.

## 9. Two runner changes of item 0

* **Species local overrides** (owner, 2026-10-10, verbatim: "711 accept
  your recommendation"). `l4owl-probe --species` reads
  `tests/local-overrides/*.json` with `"suite": "owl-species"` (keys
  `test_id`, `issue`), the convention of the XML and JSON-LD runners. A
  failing verdict on a named case goes to a `local-override` bucket; a
  passing one is STALE and the run exits 1; an override that names no
  scored case also exits 1. File:
  `tests/local-overrides/owl-species__WebOnt-I5.5-005.json`,
  https://github.com/danbri/factoidal/issues/711.
* **Functional-syntax premise fallback** (coordinator default, issue 721).
  When the RDF/XML premise does not parse and the case names the
  functional syntax as normative (`test:normativeSyntax FUNCTIONAL`), the
  case is judged from the functional-syntax premise (`premiseGraph`,
  `speciesDocs`) and the run prints `FIXTURE-DEFECT <id>: the RDF/XML
  premise does not parse (...)`. Case: `FS2RDF-literals-ar`
  (`rdf:datatype` on a property element with element content; RDF 1.1
  XML Syntax § 7.2.16 allows only text there).
