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
  right of `SubClassOf` and in `ClassAssertion`, `TransitiveObjectProperty`
  (since 2026-10-24, item 5 below), declarations and annotations. Everything
  else is `unsupported-syntax`.
- `owlEntails` `true` answers still come from the RL closure and the legacy
  refuter, with no source-to-verdict proof. A countermodel is tried first,
  so a `true` answer never contradicts a checked countermodel.
- The reader looks up a restriction node's triples through a proof-carrying
  blank-node index, and annotation properties through a proof-carrying hash
  index (`annotationIndex`, `knownAnnotation`). Until 2026-10-24
  `isAnnotation` scanned the graph for each annotation triple: time grew with
  (triples × annotation triples).

## Item 5: the Cell Ontology scaling row (2026-10-24)

`tests/stack/lean_scaling.py` row `owl-consistent-cl` answered `null` on the
sorted prefixes of the Cell Ontology basic edition. Two questions, decided from
the specifications.

### (a) Annotation properties with no declaration in the prefix

OWL 2 Mapping to RDF Graphs section 3.1.1 to 3.1.3: the reverse mapping types
each IRI from the declaration triples (`*:x rdf:type owl:AnnotationProperty`,
Table 7) and the built-in vocabulary, before it reads any axiom or annotation.
An IRI used only as the predicate of a triple, with no declaration and not
built-in, has no type, so the triple matches no pattern of Tables 10 to 17 and
the graph is not an OWL 2 DL ontology. The reader is right to refuse it.

The full file declares every annotation property it uses (123 `rdf:type
owl:AnnotationProperty` triples; 0 predicates used without a declaration,
measured with a Python count over the 78,835 distinct triples). The line cut
of the sorted file put a declaration after the cut when its subject sorts
after its users (for example `oboInOwl:hasDbXref` after the `obo:CL_…`
subjects). So the defect was in the fixture, not in the reader.

### (b) Restriction nodes outside the prefix

A `rdfs:subClassOf` triple whose `owl:Restriction` node is after the cut is
half of the axiom `SubClassOf(C ObjectSomeValuesFrom(p D))` (Table 13 needs
the node's `owl:onProperty` and `owl:someValuesFrom` triples). A graph with
half an axiom is not the ontology. Rule now in `cl_units` and `cl_prefix`:
cut the sorted triples on subject blocks; a unit is the triples of one IRI
subject, the full subtree of each blank node that its triples have as
object, and the `owl:Axiom` nodes whose annotated triple is in the unit; the
prefix takes units until it has n lines, then adds the `rdf:type` lines of
every IRI it uses as predicate, as `owl:onProperty` value or as
`rdfs:subPropertyOf` value.

### Constructors the whole-axiom prefixes need

With whole axioms, the reader still refused the prefixes and the full file.
A count of the refused triples of the full file (47,078 of 78,835) gave five
constructors. Each is now admitted:

| Constructor | Source | Logical effect | Admission rule |
| --- | --- | --- | --- |
| `rdfs:seeAlso`, `owl:deprecated` (and the other built-in annotation properties) | Structural Specification §5.5 (nine built-ins) | none | `builtinAnnotation` lists all nine |
| Annotated axioms: `_:x rdf:type owl:Axiom`, `owl:annotatedSource`, `owl:annotatedProperty`, `owl:annotatedTarget`, annotations on `_:x` (45,941 triples with a blank subject, 7,910 `owl:Axiom` nodes) | Mapping §3.2.5, Table 17 | none (Direct Semantics §1); the axiom is its own triple | each `owl:Axiom` node has one source, property and target, and the annotated triple is in the graph (`annotationsWellFormed`) |
| `rdfs:subPropertyOf` between annotation properties (16) | Mapping Table 16, `SubAnnotationPropertyOf` | none | both sides are known annotation properties |
| `owl:versionIRI` (1) | Mapping Table 4, ontology header | none | its subject is typed `owl:Ontology` |
| `owl:TransitiveProperty` (`BFO_0000050` part of, `RO_0002202` develops from) | Mapping Table 16, Direct Semantics Table 6 | `TransitiveObjectProperty(p)` | the property is not also an annotation property |

`TransitiveObjectProperty`: the axiom compiles into the role box
(`rbox.trans`) that `DirectCert.checkCertFuel` already uses, so refutations
stay sound with no change. In the model, a transitive role is the total
relation (`FinModel.full`): every pair of elements. A total relation is
transitive, so the checker tests only that the role is in `full` (`transOk`,
theorem `transOk_sound`). In this fragment (no ∀, no number restriction, no
∃ on a left-hand side, no role disjointness) more pairs falsify no axiom, so
the model is still a model when every filler has a witness. For a total role,
`rhsHoldsB` reads an edge first, then any element of the filler;
`rhsHoldsB_iff` is still an equivalence, so countermodels stay sound.
`clauseFails` claims no countermodel from a transitivity axiom.

The first form closed the role's edges after the ∃-expansion and checked the
closure. On the generated chain of `owl-consistent-svf` with a transitive
`p` (n witnesses, each needing the next) the closure has n² pairs and its
check n³ steps: 134.7 s at n = 500, measured 2026-10-24 before landing. Row
`owl-consistent-svf-transitive` now measures that input: 0.11 s, 0.26 s and
0.59 s at 2,000, 4,000 and 8,000 units.

A blank node that is a restriction node has no other triple, and an
`owl:annotatedSource`/`Property`/`Target` triple belongs to an `owl:Axiom`
node; both are fidelity checks, not soundness premises.

### Result

- Full file: `owl-consistent` answers `true` in 1.30 s CPU, 460 MB peak RSS.
- Row `owl-consistent-cl`: 0.148 s, 0.300 s, 0.642 s CPU at about 10,000,
  20,000 and 40,000 lines (ratios 2.0 and 2.1 per doubling, bound 3.0; 4.3 for
  4x, bound 9.0). Not an expected failure now.
- Row `owlrl-closure-cl` keeps the line cut (`cl_line_prefix`): the OWL 2 RL
  closure is defined on every RDF graph. On the whole-axiom prefixes its
  inferred triples grow 2.4 to 2.5 times per doubling (longer
  `rdfs:subClassOf` chains) and its time ratios were 2.6 to 3.2.
- W3C OWL 2 `tools/check-atomic-direct-corpus.py` (Approved, DIRECT, DL
  consistency units): before 20 correct definitive, 0 wrong, 226
  unsupported; after 22 correct definitive, 0 wrong, 224 unsupported (246
  executed, 20 without RDF/XML, out of 266).
- `tools/check-owl-reader-contracts.py`: 70 cases (was 54; the six built-in
  cases flipped from unsupported to supported), 8 mutations rejected.
