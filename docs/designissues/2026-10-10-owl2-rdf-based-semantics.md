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
* Lean: `L4Factoidal/OWL/RdfBased/Spec.lean` (interpretation conditions,
  entailment, a satisfiability witness), `Rules.lean` (eleven rule
  families, each proved sound), `Engine.lean` (executable rules, each
  output proved to be a rule application), `Tests.lean` (`#guard`
  cases, positive and negative per rule). No `sorry`, no `axiom`, no
  `native_decide`, no `partial`.
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
premise, then up to three rounds of (the RDF-Based rules of § 4.3,
the RL closure again), under one wall-clock cap per unit. Then the
triples that mention a comprehension witness are removed (§ 4.1), and
the conclusion is matched or the clash rows are checked.

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
premise graph true. No rule mints a blank node.

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

"Goal-directed": the two premise-free families add only what the
conclusion graph names (`axiomsFor`: rows whose subject IRI the goal
mentions; `universalFor`: only for a goal `rdf:type owl:Thing` or
`rdfs:Resource`). Adding them to every graph would put Table 6's
axiomatic triples, with their cyclic `rdfs:subClassOf` lattice, into
every closure; `measuring-inference` § 10 records that cost. The other
rules read the closure alone, one pass with at most two nested lookups.

## 5. The Lean files

* `L4Factoidal/OWL/RdfBased/Spec.lean`. `RdfBasedConditions`, nineteen
  fields, each a transcription of a table row (or, where a rule reads
  one half of an "iff", that half). The bundle admits every OWL 2
  RDF-Based interpretation, so `RbEntails` (entailment over the bundle)
  implies Definition 4.5 entailment. `witness_conditions`: an
  interpretation that meets all nineteen; `rbEntails_not_everything`:
  `RbEntails [] [owl:Thing rdfs:subClassOf owl:Nothing]` is false. The
  witness exists because a bundle no interpretation meets would make
  every entailment statement true (`measuring-inference` § 4).
* `Rules.lean`. `RbDerives`, `rbDerives_sound`, `rbDerives_entailed`.
  Anti-pattern 29 check: no rule hypothesis contains its conclusion;
  each conclusion is reached through a condition of the bundle (the
  proof terms end in `hc.<field>`, never in a premise).
* `Engine.lean`. The executable rules, `rbConclusions_derives` (every
  output is an `RbDerives` application), `withoutCompWitness`,
  `rbSaturate`.
* `Tests.lean`. For each rule a positive and a negative `#guard` case,
  and end-to-end cases on the shapes of `WebOnt-Class-003`,
  `WebOnt-imports-010` and `WebOnt-I5.3-015`.

## 6. Scores

PLACEHOLDER — filled from the measurement of § 6.1.

## 7. Left failing, with the reason

PLACEHOLDER.

## 8. Gaps, with issue-ready text

PLACEHOLDER.
