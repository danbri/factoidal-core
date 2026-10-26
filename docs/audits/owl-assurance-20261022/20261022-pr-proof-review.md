# OWL draft PR proof review

Date: 2026-10-22. Reviewer: preserve_evidence agent.

The restricted consistency proof chain has no newly identified false-verdict
gap in this review. It is suitable for a focused draft PR, with the capability
reduction explicit. This is not approval to release or evidence of complete
OWL reasoning. Main-branch integration checks must pass on the proposed PR
tree; previous dirty-checkout artifact results cannot substitute for that.

## Trees and review scope

Initial review read `repair-core`, based on
`d83100e6ec038328a71a245e9fd10fbd768a38a5`, against fetched main
`dfecea9733904462cb98b111acf47f57e19ffaa4`. The OWL originals
`DirectCert.lean`, `RefuteCert.lean` and `Wasm/Ops/ReasonDl.lean` did not change
between those commits. Dependencies and public error handling did change.
The follow-up review uses `pr-core`, whose HEAD is that fetched main.

Reviewed the actual source mapping and satisfaction relation, admission and
coverage proof, model-preserving compilation, checker use, equality merging,
JSON producer, schema/unique-key proofs, producer wiring, relevant fixtures,
gate code, current-main error model, and package-facing scope statements.
This was not a fresh audit of the entire pre-existing OWL checker.

## Concrete integration findings

1. **Current-main error ABI needed reconciliation.** The original public
   fixture equated `L4Wasm.call` bytes to the raw ReasonDl result. Main now
   applies `ErrorModel.attachCode`. The original artifact gate also required
   only `ok/error` keys and the old `ParseError` class. Those checks would
   reject a correct integration. Main's error model must be preserved.
   The parent authorized two test-only edits in `pr-core`: the fixture now
   reports both raw `response` and actual `dispatchResponse`; the Python
   checker validates each separately. Expectations do not call `attachCode`,
   `classify`, `specOfCode`, or `positionJson` to generate expected metadata.
   The parent owns the corresponding artifact-runner update.

   RDF 1.2 refusals must carry code `owl.unsupported-rdf12`, spec
   `https://www.w3.org/TR/owl2-mapping-to-rdf/#Mapping_from_RDF_Graphs_to_the_Structural_Specification`,
   and no position. The raw OWL text parser refusal currently receives
   `reason.failed`, without spec or position: `owlIsConsistent` is absent
   from `opTextArg`, and its family is reasoning. This is an existing main
   diagnostic limitation, not a new semantic classification claim. The
   public facade's preliminary parser is a separate `FactoidalError` path
   with its own parser code/spec/position. Keep those expectations distinct.

   The revised Python source checker passed syntax and whitespace checks.
   A synthetic valid inventory was accepted; eleven forged or malformed
   inventories were rejected: missing code, wrong code, wrong spec,
   unexpected position, unexpected spec, missing dispatch observation,
   numeric `ok`, numeric `consistent`, missing explicit null, changed verdict,
   and duplicate dispatch field. These are report-validator controls, not
   new engine observations. The parent is running the actual source gate;
   this reviewer did not start a competing Lake process.

2. **The package landing-page claim needed narrowing.** The old README
   advertised unqualified OWL DL consistency and showed historical DL
   results without identifying the new restricted API. The parent has now
   corrected `pr-core/npm/factoidal/README.md`: the capability list names
   restricted checked consistency; the results section separates legacy
   harness measurements from the new API and describes unsupported syntax,
   unknown results, fixed bound, and separate legacy entailment. Preserve
   that correction in the PR rather than relying on a repository-only note.

No remaining code-soundness blocker was found for a draft PR. Successful
current-main source and packed-artifact checks are still required before
describing the reconciled tree as verified. Existing broader failures must
remain visible and must not be changed into expected passes.

## Why the source proof is substantive

- Source `MapsTo` and axiom denotation do not invoke `readTriple`, the
  compiler, or target `HasModel`. Annotation roles use declarative original
  graph membership. The executable lookup has a separate soundness proof.
- Source satisfaction alone is deliberately partial on unsupported RDF.
  Both definitive constructors additionally require whole-input `Accepted`.
  The unsupported equivalentClass contradiction and its vacuous partial
  model are retained as controls; that model is not called an OWL model.
- `accepted_covers_triples` uses successful execution of the real `mapM`
  traversal to give a mapping witness for every original triple. It prevents
  the reader-returning-empty mutation from retaining the same admission
  guarantee; one-way model preservation alone would not prevent that edit.
- Compilation preserves each source interpretation in actual `DirectModel`.
  The true Top seed requires no fresh name and supplies the nonempty-domain
  witness needed for a TBox-only contradiction. No caller supplies a missing
  reader-preservation premise to `decide_sound`.
- The checker consumes the ontology read from the original default graph,
  with no RL fallback. Arbitrary certificate proposals remain untrusted.
  Rejection is unknown. No checked-model route is exposed by this producer.
- JSON meaning, explicit field presence/types, and unique keys are proved
  separately. Unique keys close the first-match versus last-match ambiguity.
  The raw string producer demonstrably serializes this checked object.
- The equality repair renames both ABox assertions and remaining equality
  endpoints. `respectsSame_subst` justifies the transformed equalities;
  `satAll_mergeAll` preserves the model invariant. `checkCert_sound` keeps
  its statement. Existing direction/order controls exercise both refuting
  and satisfiable equality inputs.

## Limits and follow-up work

- The independent RDF mapping/denotation is a manually reviewed fragment of
  the cited W3C conditions, not a full mechanized OWL reverse-mapping theorem.
  Admission allows implicit declarations and zero/multiple ontology headers.
  Do not describe it as full OWL DL validity checking.
- The theorem starts at the RDF graph returned by the actual parser.
  Parser adequacy, normalization of Dataset inputs, JSON serialization and
  parsing, dispatch enrichment, extraction, and JavaScript handling are
  separate assurance boundaries. The raw-producer semantic theorem does
  not become a universal theorem about all those layers merely because
  finite adapter tests pass.
- Named graphs contribute neither axioms nor annotation declarations to
  default-graph reasoning. Whole-dataset RDF 1.2 preflight is intentionally
  retained, including RDF 1.2 terms in named graphs.
- The fixed `.close`/64-round policy materially reduces definitive answers;
  no completeness claim follows from soundness or an all-unknown corpus.
  The compatibility `fuel` argument no longer controls this consistency
  policy. Preserve the recorded broader regressions and release limitations.
- `RefuteCert.applyRen` still folds raw equality pairs. With
  `[(b,c),(a,b)]`, it maps `a` to `b`, while repaired `mergeAll` maps an ABox
  occurrence to `c`. A nontrivial legacy emitted certificate can therefore
  use a different representative and be rejected. This is a coverage risk,
  not a false-acceptance gap: the actual checker revalidates certificates.
  AtomicDirect's `.close` path is unaffected. Before integrating broader
  emitted search, reconcile its representative policy and add an emitter
  regression with a nontrivial certificate and reordered equality chain.
- Legacy entailment and tableau diagnostic exports retain their separate
  outstanding reader/preprocessing/goal obligations. This PR must not claim
  to certify all ReasonDl operations or repair all npm audit findings.

## Reviewed source identities

SHA-256 values in `pr-core` at review time:

| File | SHA-256 |
| --- | --- |
| AtomicDirect.lean | `ae32a22e2de44fe669ee8851735ca7f94ea2728f8d39f11cb3325d7cfde3b870` |
| CertifiedDecision.lean | `c5a22041197561d815685cb1ccd7595a721ed25147a53e1e8277ed8b639cd81b` |
| ReasonDlCertified.lean | `66ba21125cacaf45d2a56e5c83026621a0da41407a3059864ff95acfb2d28970` |
| DirectCert.lean | `6b5080ff8507b9910cae76cf27c6483076a847d6ce077f68f8246716ba1f5a25` |
| ErrorModel.lean (main dependency) | `b5167f09a3fabe149d2f584af1ead49089fcc052792ff7922315d602b4184ee9` |
| OwlPublicBoundary.lean (reconciled fixture) | `e282c736a38296cc3f08dc7ac7440a9eb8e7608053f50be4abfa6b88c982406a` |
| check-owl-public-boundary.py (reconciled checker) | `9fb012ff56e2ff92fddb4e43b5b9f4c6e3944b7d7e980e92aebfb8e0407e42fd` |

Only the two explicitly authorized test files and this report were written
by this reviewer during the PR review. No commit, push, PR creation, source
proof edit, or artifact rebuild was performed by this reviewer.
