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
