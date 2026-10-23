# OWL public verdict repair

Current PR status: [2026-10-22 reconciliation and evidence](20261022-owl-pr-reconciliation.md).
The dated checkpoint below is retained as historical evidence.

Follow-up: [the checked consistency boundary](20261021-owl-public-boundary.md)
supersedes this draft's consistency route. This note preserves the original
RL/refuter repair and its annotation failure; entailment remains unfinished.

Date: 2026-10-21. Baseline: published `@factoidal/core@0.11.0`, core
`d83100e6ec038328a71a245e9fd10fbd768a38a5`.

Status: draft source repair with regressions. No repaired npm package has
been built or published at the time of this note. This change does not
establish complete OWL DL support or universal Direct Semantics soundness.

## Behavior changed

`owlIsConsistent` now runs the existing `OWL.RL.detectClashPlus` on the
closure before the tableau. The native OWL harness already uses its
indexed equivalent. This catches sameAs/differentFrom contradictions that
the published public API reported as consistent.

The operation now returns `false` for detected contradictions and `null`
otherwise. Its refuter has no checked model constructor, so quiescence no
longer becomes `consistent: true`. `owlEntails` retains positive closure
and refutation answers, but absence from the closure and unrefuted goals
now return `null`. The operation has no checked countermodel constructor
and therefore no longer returns `entailed: false`.

Reasons distinguish `budget-out`, `incomplete-search`,
`unsupported-conclusion` and `unsupported-punning`. Increasing fuel need
not resolve an incomplete or unsupported case. Existing callers that
assumed `null` meant only budget exhaustion must change. The TypeScript
return type remains `boolean | null` for API compatibility, while its
comments state the values this implementation can produce.

## Additional wrong verdict found during repair

The published API reports `consistent: false` for this graph:

```turtle
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix ex: <urn:> .
ex:C a owl:Class, owl:NamedIndividual;
     owl:sameAs ex:D;
     owl:disjointWith ex:D .
ex:D a owl:Class, owl:NamedIndividual .
ex:x a owl:NamedIndividual, ex:C .
```

It has a Direct Semantics model. Choose a nonempty object domain with an
element `u`, interpret the individuals C, D and x as `u`, interpret class C
as `{u}`, and class D as empty. The individual equality and disjoint class
axiom both hold. OWL 2 interprets a punned name's class and individual
roles independently; see [Structural Specification §5.9](https://www.w3.org/TR/owl2-syntax/#Metamodeling)
and [Direct Semantics §2.2](https://www.w3.org/TR/owl2-direct-semantics/#Interpretations).
The model construction here is a mathematical counterexample, not a new
machine-checked theorem. Removing the disjointness axiom makes the
published API report `true`; the disputed inference is the closure's
substitution of individual equality into class positions.

The draft refuses detected class/property-versus-individual punning before
any consistency or entailment closure. It returns `null` with
`unsupported-punning`. The check also reads the combined premise and
conclusion so a role first stated in the conclusion does not bypass it.

The detector is deliberately limited. It recognizes explicit schema
declarations, predicates, selected class/property axiom endpoints,
restriction fillers, sameAs/differentFrom endpoints, class assertions and
ordinary property assertions. It does not traverse RDF lists or implement
the whole OWL reverse mapping. It can conservatively withhold results for
additional inputs, and it can miss other unsupported uses. Passing this
check is not evidence of OWL DL conformance or of the remaining pipeline's
soundness. A complete repair needs role-aware Direct Semantics processing
or a justified supported-fragment boundary.

A second false Direct inconsistency remains outside this detector:

```turtle
@prefix owl: <http://www.w3.org/2002/07/owl#> .
@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .
@prefix ex: <urn:> .
ex:p a owl:AnnotationProperty; rdfs:domain owl:Nothing .
ex:a ex:p "note" .
```

The published API returns `false`; removing the domain statement makes it
return `true`. The RDF closure treats the annotation assertion as a
property assertion and derives `ex:a rdf:type owl:Nothing`. Under Direct
Semantics, the annotation property domain is an annotation axiom rather
than a class-membership constraint; see
[Structural Specification §10.2](https://www.w3.org/TR/owl2-syntax/#Annotation_Axioms)
and [Direct Semantics §1](https://www.w3.org/TR/owl2-direct-semantics/#Introduction).
There is no syntactic class/individual overlap for the limited detector to
refuse. The draft still follows that closure path and therefore does not
fix this case. The release remains blocked on a sound supported-domain
boundary or role-aware annotation handling; the new RL clash call cannot
by itself resolve the mismatch between RDF-based and Direct Semantics.
The published reproduction and its control are retained in
`.claude-runs/20261021-owl-annotation-before.json`.

## Implementation and assurance

- Edited Lean implementation: `formal/lean4/Wasm/Ops/ReasonDl.lean`.
  The partial role analysis is in the semantic library module
  `formal/lean4/L4Factoidal/OWL/DirectProfile.lean`, imported by both the
  wrapper and `L4Factoidal.lean`. The move preserves the detector's
  behavior. No semantic workaround was placed in JavaScript.
- Reused Lean decisions: `L4Factoidal/OWL/RLClosure.lean` and
  `L4Factoidal/OWL/Refute.lean`. The internal refuter and native harness
  contracts are unchanged.
- Existing theorem: `RLTheorems.detectClashPlus_sound` establishes
  `Clash g ∨ ExtClash g`. `RLClosureIndexed.detectClashPlusI_eq` relates
  the indexed decision to this decision under its index invariant.
  These statements do not establish arbitrary OWL Direct Semantics
  soundness after the RDF-based closure. The interpretation theorems have
  explicit RL semantic conditions.
- Existing public dataset/text equivalence theorems remain in ReasonDl.
  No new universal theorem, model validator, completeness result or
  profile recognition theorem is claimed. The new `#guard`s are concrete
  regression examples.
- F* lineage: `formal/fstar/Tableau.Refute.fst` and
  `bin/npm-entry/entry_jsoo.ml`. This repair deliberately narrows the
  old wire verdicts; it does not preserve their model/countermodel claim.
- Tests: `npm/factoidal/test/owl-verdict-regression.test.mjs`, and the
  existing OWL sections of `test/l4-core.test.js`. API comments are updated
  in `npm/factoidal/API.md` and `index.d.ts`.

## Validation record

Before the Lean edit, the public regression used source wrappers with
`FACTOIDAL_L4_ASSETS` explicitly selecting the published package's engine:

```sh
FACTOIDAL_L4_ASSETS=/absolute/path/to/published/package/l4-assets \
  node --test npm/factoidal/test/owl-verdict-regression.test.mjs
```

Result: 15 tests, 2 pass, 13 fail, 0 skipped. The passing controls are a
positive subclass entailment and budget exhaustion. Failure output is
retained in `.claude-runs/20261021-owl-verdict-before.tap`.

The focused build command, from `formal/lean4`, is:

```sh
lake build Wasm.Ops.ReasonDl
```

The focused build passed (51 jobs), including the old RDF 1.2 refusal
guards and the new contradiction, open-search, punning and unsupported
conclusion guards. Log: `.claude-runs/20261021-owl-verdict-build.log`.

After moving the detector into the semantic library, the focused build
passed again (52 jobs), with all ReasonDl guards retained. Full
`lake build L4Factoidal` also passed (805 jobs). Logs:
`.claude-runs/20261021-owl-direct-profile-focused.log` and
`.claude-runs/20261021-owl-direct-profile-library.log`.

Rebuilt Wasm tests, the public OWL catalog and counterexample coverage
remain required before release. The annotation-domain counterexample also
requires a semantic repair. The published engine still has the defects;
the red public regression is not a green test of the repaired Wasm. Do not
count new `null` results as conformance passes.
