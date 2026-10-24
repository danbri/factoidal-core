# OWL model certificates, someValuesFrom, fuel and countermodels

Date: 2026-10-24. Issue: https://github.com/danbri/factoidal/issues/960.
Status: current. Earlier records: [OWL PR reconciliation](../20261022-owl-pr-reconciliation.md),
[certified OWL boundary](../20261021-certified-owl-boundary.md).

## Result

`owlIsConsistent` (`factoidal owl-consistent`) answers `true` again, but only
with a checked finite model. `owlEntails` (`factoidal owl-entails`) answers
`false` only with a checked countermodel. The reader admits
`owl:someValuesFrom`. `fuel` bounds the search and the checker.

| Answer | Evidence | Theorem |
| --- | --- | --- |
| consistent `true` | a `FinModel` that `checkModel` accepts | `AtomicModel.checkModel_sound` |
| consistent `false` | a `Cert` that `checkCertFuel` accepts | `DirectCert.checkCertFuel_sound` |
| entailed `false` | a `FinModel` that `checkCountermodel` accepts | `AtomicModel.checkCountermodel_sound` |
| any `null` | none | `decideFuel_sound`, `entailsFuel_sound`: `null` claims nothing |

## The model checker

File: `formal/lean4/L4Factoidal/OWL/AtomicModel.lean`.

1. A `FinModel` is a finite interpretation over `Nat`: a label (class names)
   and an edge list (role, element) for each element `0 … n-1`, and a map from
   individual names to elements. An element `x ≥ n` behaves as element 0
   (`norm`), so the domain is all of `Nat` and the checker visits `n`
   elements only.
2. `checkModel graph M` reads the ORIGINAL RDF graph. For each triple it
   checks every axiom the triple can map to (`candidates`, an
   over-approximation of the source contract `AtomicDirect.MapsTo`). It
   does not read the compiled `DlOntology`.
3. Subclass axioms are checked per element through an untrusted index
   (`sub`, `topSub`). The checker verifies that every source axiom is in the
   index (`covered`), then that every element satisfies the indexed axioms
   of its label (`elementsOk`).
4. `checkModel_sound : checkModel graph M = true → SourceModel M.interp
   M.assign graph`. The conclusion is "is a model". No premise mentions
   `SourceModel`, `Satisfiable` or `axiomHolds` (anti-pattern 29 checked by
   reading the statement).

## The search, the tableau rule and the blocking rule

The search (`search`) is not trusted. A wrong search gives `null`.

- Equality: union-find over the `SameIndividual` pairs; one element for
  each class. Element 0 is the anonymous `owl:Thing` member `""` of
  `AtomicDirect.initialOntology`.
- Labels: the atomic-subsumption closure of the asserted classes and of the
  `owl:Thing ⊑ X` axioms.
- ∃-rule: an element whose label gives `∃p.C` gets an edge `(p, w_C)`.
- Blocking rule (by filler): there is at most one witness element `w_C` for
  each filler `C`. An element that needs a successor in `C` reuses `w_C`.
  The fillers are a finite set, so the search ends.
- The blocking rule is not a premise of any theorem. The checker reads the
  final interpretation; if blocking made a wrong model, the checker rejects
  it. For this fragment (no conjunction or ∃ on a left-hand side, no ∀, no
  number restriction) the model with blocking by filler satisfies every
  axiom: each element's label is closed, and `w_C` has every class that `C`
  forces.
- Clash: `owl:Nothing` in a label, a `DifferentIndividuals` pair in one
  element, or an ∃ with filler `owl:Nothing`. The search then gives a
  refutation certificate: `.close` for a clash of a named individual, and a
  chain of `.exWit` steps (one fresh name `_:factoidal-witness-k` for each
  step) for a clash of a witness. `checkCertFuel` checks it.

## Fuel

`fuel` (default 20000, `opts.fuel`, `--fuel`) is a number of rounds.

- Search: one round expands one layer of new elements. The cyclic input
  `e:i a e:A . e:A ⊑ ∃e:p.e:A` needs two rounds, so fuel 1 gives
  `null` with the reason `budget-out: … fuel 1 rounds …`.
- Checker: `checkCertFuel O fuel c` saturates `fuel` rounds at each
  certificate node. `checkCert` is `checkCertFuel O certFuel`.
- A refutation that does not check at `fuel` but checks at 20000 is
  reported as `budget-out`.

## Reader extension

File: `formal/lean4/L4Factoidal/OWL/AtomicDirect.lean`.

- New axioms: `subClassSome` (`A ⊑ ∃p.C`) and `assertSome` (`a : ∃p.C`),
  with their Direct Semantics conditions (Table 4 `ObjectSomeValuesFrom`,
  Table 5, Table 10).
- New `MapsTo` rules: the subclass or type triple whose object is a
  restriction node; the node's `owl:onProperty`, `owl:someValuesFrom` and
  `rdf:type owl:Restriction` triples (no effect of their own); the
  `owl:ObjectProperty` declaration.
- `readOntology_preserves_models` still holds (the compile step adds
  `(A, ∃p.C)` to the TBox).
- Two readings are wider than OWL 2 Mapping Table 13: the
  `rdf:type owl:Restriction` triple is optional, and the property needs no
  declaration (the reader admits no data property).
- `restrictionsWellFormed` refuses a restriction node without exactly one
  `owl:onProperty` and one `owl:someValuesFrom` triple, and an IRI that is
  both an annotation property and an object property. This check is not a
  soundness premise.

## Limits

- Fragment: atomic classes, Thing/Nothing, `SubClassOf`, `ClassAssertion`,
  `SameIndividual`, `DifferentIndividuals`, `ObjectSomeValuesFrom` on the
  right of `SubClassOf` and in `ClassAssertion`. Everything else is
  `unsupported-syntax`.
- `owlEntails` `true` answers still come from the RL closure and the legacy
  refuter, with no source-to-verdict proof. A countermodel is tried first,
  so a `true` answer never contradicts a checked countermodel.
- The reader looks up a restriction node's triples by a scan of the graph
  (`findProperty`, `findFiller`), and `isAnnotation` scans the graph: time
  grows with (triples × restriction uses) and (triples × annotation
  triples).
- `tests/stack/lean_scaling.py` row `owl-consistent-cl` (issue 960 item 5)
  still answers `null`: the sorted prefixes of the Cell Ontology hold
  annotation properties with no declaration in the prefix and
  `rdfs:subClassOf` triples whose restriction node is not in the prefix. The
  strict reader refuses both. The row stays an expected failure.
