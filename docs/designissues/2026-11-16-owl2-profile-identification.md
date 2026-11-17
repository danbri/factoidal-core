# OWL 2 profile identification (EL, QL, RL) and the state of the OWL populations (2026-11-16)

This record covers the OWL 2 profile checkers added on 2026-11-16, what they decide, what is proved, the
measured result on the W3C OWL 2 Test Cases, and the cause of every OWL population that is still below its
full count.

## 1. What was missing

The W3C OWL 2 Test Cases (`third_party/testing/owl/all.rdf`, 489 cases) type 418 cases
`ProfileIdentificationTest`. Each asks, for each of the profiles OWL 2 EL, QL and RL, whether the case's
ontology is in the profile; the answer is yes exactly when the case carries `test:profile` for it (113 cases
name at least one profile, 305 name none). The tree had no profile checker, so the three populations
`l4-owl2-profile-el|ql|rl` were recorded with their size and nothing run.

## 2. The method

A profile is a syntactic subset of OWL 2 DL
([OWL 2 Profiles](https://www.w3.org/TR/owl2-profiles/), sections 2.2, 3.2, 4.2 and the grammars of section
6): a restriction of the functional-style grammar, plus, for OWL 2 EL, one more global restriction (section
2.2.6). The verdict for a case and a profile is the conjunction of three things.

1. **The case is an OWL 2 DL ontology.** `OWL/SyntaxDL.lean`, the verdict that `l4owl-probe --species`
   scores (488 of 489 against `test:species`). A case that is not OWL 2 DL is in no profile.
2. **The axioms are read back from the RDF graph.** `OWL/StructureFromRdf.lean` (`ontologyOfGraph`) is the
   reverse mapping of [OWL 2 Mapping to RDF Graphs](https://www.w3.org/TR/owl2-mapping-to-rdf/) section 3 for
   declarations, property expressions, data ranges, class expressions and axioms. It gives
   `Struct.Ontology`, the type the functional-style parser already produces. Annotations are not read. A
   triple the reader cannot place is an error that names the triple; the probe reports the case as
   `undecided` for all three profiles and never as a verdict.
3. **Every axiom is in the profile's grammar.** `OWL/Profiles.lean`: `inEL`, `inQL`, `inRL` over
   `Struct.Ontology`. They check the class expressions allowed in each position (subclass, superclass,
   equivalent class), the property expressions, the individuals (no anonymous individuals in EL and QL), the
   axiom kinds, the supported datatypes (in data ranges and on literals), and for EL the restriction on range
   axioms with property chains.

The documents checked are the premise with its imports and the conclusion (or non-conclusion), as for the
species verdict.

Two readings of the specification text are stated in `Profiles.lean` so they can be changed in one place:
OWL 2 QL accepts `IrreflexiveObjectProperty` (section 3.1 lists it; the grammar of 3.2.5 omits the
production), and `DatatypeDefinition` is accepted when its data range is in the profile while a use of the
defined datatype is a datatype outside the profile's list.

## 3. What is proved, and what is tested

Proved in `OWL/Profiles.lean` (no `sorry`, no axioms):

- The OWL 2 RL grammar of section 4.2 is written a second time as inductive relations, one constructor per
  alternative of each production: `RL.Sub`, `RL.Super`, `RL.Equiv` (the three kinds of class expression),
  `RL.MaxFiller` and `RL.AxiomOk`. The checker accepts exactly that grammar: `rlSub_iff`, `rlSuper_iff`,
  `rlEquiv_iff`, `rlAxiom_iff`, and for an ontology `inRL_iff : inRL o = true ↔ ∀ a ∈ o.axioms, RL.AxiomOk a`.
- The same for the class expressions of QL (`qlSub_iff`, `qlSuper_iff`) and EL (`elCE_iff`), and
  `inEL_subClassOf`, `inQL_subClassOf` for `SubClassOf` axioms of an accepted ontology.
- `disjointUnion_in_no_profile`: an ontology with a `DisjointUnion` axiom is rejected by all three.

Tested, not proved:

- The reverse mapping. `OWL/ProfilesTests.lean` reads 40 small ontologies twice, as parsed from the
  functional-style syntax and through their RDF graph, and requires the same axiom kinds and the same three
  verdicts. The probe does the same for every W3C case that has a functional-style premise and prints
  `PROFILE-SYNTAX-DISAGREE` for a difference.
- The OWL 2 DL verdict of step 1 (`SyntaxDL`), which is a port validated against the corpus.
- The EL range restriction (`elRangeRestrictionOk`): three guards.

## 4. Use

```
l4owl-probe --profile-id --dir third_party/testing/owl all.rdf
```

prints one `FAIL` or `UNDECIDED` line per differing unit and, per profile, the lines

```
all.rdf ProfileIdentificationTest EL [annotated in]: N pass, M fail, K undecided (out of T)
all.rdf ProfileIdentificationTest EL [annotated out]: ...
all.rdf ProfileIdentificationTest EL: ...
```

`release-tests/owl-populations.py` (factoidal-builds) runs it over the catalog split by status and records
`l4-owl2-profile-el`, `-ql`, `-rl`.

## 5. Result (2026-11-16, `all.rdf`, 418 cases per profile)

| Population | Before | After | Annotated in: pass of total | Annotated out: pass of total |
|---|---|---|---|---|
| ProfileIdentificationTest, EL | not run | 403 pass, 15 fail, 0 undecided | 78 of 87 | 325 of 331 |
| ProfileIdentificationTest, QL | not run | 408 pass, 10 fail, 0 undecided | 55 of 65 | 353 of 353 |
| ProfileIdentificationTest, RL | not run | 412 pass, 6 fail, 0 undecided | 88 of 91 | 324 of 327 |

The run takes 0.4 s for the three profiles together (macOS arm64). For the 83 cases with a functional-style
premise the verdicts from the RDF graph and from the functional-style documents agree on 82; the one
difference is a defect of the test data (below).

### The 31 failing units, each with its cause

In every one the checker follows the text of OWL 2 Profiles and the catalog's `test:profile` annotation says
otherwise, or the test data is defective. None is a unit the reader could not decide.

**Anonymous individuals in a case annotated EL or QL (10 units).** Sections 2.2.1 and 3.2.1: "OWL 2 EL does
not support anonymous individuals", "OWL 2 QL does not support anonymous individuals"
(`Individual := NamedIndividual`). These cases assert something of a blank node and are annotated as in the
profile: `bnode2somevaluesfrom`, `somevaluesfrom2bnode`, `WebOnt-someValuesFrom-003` (EL);
`WebOnt-I5.26-001`, `WebOnt-I5.26-002`, `WebOnt-Nothing-001` (EL and QL); `WebOnt-description-logic-104`
(QL). The catalog's annotations never apply the restriction.

**A construct the profile's grammar excludes, annotated as in (6 units).**
`Plus and Minus Zero are Distinct` (EL): literals of `xsd:float`, which section 2.2.1 says "MUST NOT be used
in OWL 2 EL". `FS2RDF-propertychain-2-ar` and `FS2RDF-propertychain-2-annotated-ar` (QL): a property chain,
which section 3.2.5 disallows. `FS2RDF-same-individual-2-annotation-ar` and `-3-annotation-ar` (QL):
`SameIndividual`, which section 3.2.5 disallows. `New-Feature-ReflexiveProperty-001` (RL):
`ReflexiveObjectProperty`, which section 4.2.5 disallows.

**Every axiom is in the profile's grammar, annotated as out (9 units).** EL:
`FS2RDF-same-individual-2-annotation-ar`, `-3-annotation-ar` (`SameIndividual` of two named individuals),
`Footnote-not-about-self` (`DisjointClasses` with `ObjectHasSelf`, a class assertion, a property assertion),
`functionality-clash` (`FunctionalDataProperty`, two `DataHasValue` class assertions with `xsd:integer`),
`WebOnt-I4.6-003`, `WebOnt-I4.6-004` (`owl:sameAs` between two IRIs). RL: `consistent-integer-filler`
(`SubClassOf( A DataHasValue )`, `ClassAssertion( DataAllValuesFrom( dp xsd:integer ) a )`),
`inconsistent-integer-filler` (`SubClassOf( DataHasValue A )`, `ClassAssertion( ObjectComplementOf( A ) a )`),
`FS2RDF-negative-property-assertion-ar` (negative property assertions, with `ObjectInverseOf`).

**Defective test data (3 units).** `FS2RDF-domain-range-simple-ar` (EL, QL, RL): the RDF/XML premise is not
the functional-style premise. The functional-style document has `ObjectPropertyRange( :p3 :c3 )` on a
property it declares as a data property; the RDF/XML document types `p3` as `owl:DatatypeProperty` with
`rdfs:range c3`, a class where a data range is required. The functional-style reading is in all three
profiles, the RDF/XML reading in none.

**The species dispute of issue 711 (3 units).** `WebOnt-I5.5-005` (EL, QL, RL): its conclusion document has
no ontology header, so `SyntaxDL` says it is not an OWL 2 DL ontology (the local override
`tests/local-overrides` of the species suite, https://github.com/danbri/factoidal/issues/711).

(10 + 6 + 9 + 3 + 3 = 31: EL 15, QL 10, RL 6.)

Two corrections were made to the reader and the QL checker after the first run, each for a stated reason and
not to match the catalog: a one-element `owl:intersectionOf` reads as its element (the structural
specification has no one-operand intersection; 8 QL units), and QL follows the
`ObjectPropertyAxiom` production for `IrreflexiveObjectProperty` (1 unit). `New-Feature-Rational-002` and
`-003` have an RDF/XML list that ends in the RDF namespace IRI where `rdf:nil` is meant; they are judged from
their functional-style documents (6 units).

## 6. The other OWL populations: what is below the full count, and why

Measured the same day with the same probe (`release-tests/owl-populations.py`), unchanged by this work.

| Population | Pass of total | Cause of the rest |
|---|---|---|
| PositiveEntailmentTest, Direct | 193 of 205 (Approved 143 of 143) | The 12 are status Proposed and species FULL only: `WebOnt-Class-001`, `-Class-003`, `-equivalentProperty-005`, `-I5.3-015`, `-I5.5-001`, `-I5.5-002`, `-I5.8-017`, `-imports-010`, `-Nothing-002`, `-extra-credit-002`, `-003`, `-004`. They are not OWL 2 DL ontologies, so the Direct Semantics does not apply to them; the catalog annotates them DIRECT as well as RDF-BASED. Seven of them pass in the RDF-Based regime; `WebOnt-I5.5-001` and `-002` expect `rdf:first` and `rdf:rest` to be functional (local overrides there); the three `extra-credit` cases need integer multiplication over cardinalities. |
| InconsistencyTest, Direct | 126 of 127 | `WebOnt-description-logic-909` (Extracredit): a counting argument over qualified cardinalities that the refuter does not finish in its budget (`docs/designissues/2026-07-16-owl2-per-node-algebraic-tableau-909.md`). |
| species, all | 488 of 489 | `WebOnt-I5.5-005`, the local override of issue 711. |
| PositiveEntailmentTest, RDF-Based | 147 of 201 | 30 need an individual that only the informative comprehension conditions supply (not entailments of the normative semantics); 19 need reasoning by cases, counting or datatype value spaces; 3 need arithmetic; 2 expect `rdf:first` and `rdf:rest` to be functional, which the semantics does not say (`2026-10-10-owl2-rdf-based-semantics.md`, section 7). |
| InconsistencyTest, RDF-Based | 55 of 128 | No proved clash row fires. On the separately labelled line that uses Theorem 7.1 of the RDF-Based Semantics for balanced pairs, 115 of 128 pass; that line is not counted because the theorem's proof in the specification is a sketch and the refuter's answers are certified for only part of them (48 certificates check). |
| ConsistencyTest, RDF-Based | 0 of 347 (no verdicts) | A consistency verdict needs a model of the whole RDF-Based Semantics. See section 7. |
| NegativeEntailmentTest, RDF-Based | 0 of 23 (no verdicts) | The same: a non-entailment needs a model of the premise in which the conclusion is false. |

## 7. Consistency and non-entailment under the RDF-Based Semantics: what a sound verdict needs

Later, not done here. The engine has never claimed consistency for this semantics, and it should not until
it can show a model.

- The conditions formalised in `OWL/RdfBased/Spec.lean` (`RdfBasedConditions`) are a subset of section 5 of
  the RDF-Based Semantics, chosen because each one has a proved rule. Every interpretation of the semantics
  meets them, so an entailment proved from them is an entailment. The converse does not hold: a model of the
  subset need not be a model of the semantics, so a model of the subset proves nothing about consistency.
- The Direct Semantics does not help. A graph can be consistent under the Direct Semantics and inconsistent
  under the RDF-Based Semantics (two classes stated `owl:sameAs`, one with a member the other excludes), and
  Theorem 7.1 carries entailments from Direct to RDF-Based, not consistency.
- The clash-free OWL 2 RL/RDF closure does not help either: Theorem PR1 of OWL 2 Profiles relates the rules
  to the Direct Semantics of an OWL 2 RL ontology.
- What is needed: (1) all the semantic conditions of section 5 as one Lean structure, with the "if and only
  if" conditions in both directions and the OWL 2 datatype map with its value spaces and facets; (2) a
  checker for a finite description of an interpretation (the finite part as tables, the datatype values and
  the container membership properties described symbolically) with a theorem that an accepted description
  is an interpretation meeting (1) and satisfying the graph; (3) a search that builds such a description for
  the small graphs of the corpus. Until (2) is proved, the two populations stay at no verdict.

## 8. Timings

`l4owl-probe --profile-id all.rdf`: 0.42 s (new). `owl-populations.py run` (both semantics, then the
profiles): 3 min 54 s, against 3 min 27 s before on the same machine in the same hour (the two semantics
runs dominate and vary by tens of seconds between runs). The other modes of the probe do not call the new
code.
