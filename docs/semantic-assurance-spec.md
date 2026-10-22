# Semantic assurance and release evidence specification

Status: repair requirements and local tooling, 2026-10-21. The npm 0.11.0
audit is the incident baseline. This document specifies acceptance
obligations; it does not assert that the implementation meets them.

The user requested that the failures, their causes and the standards
reasoning survive in specifications, skills and tools. This is the
maintained integration contract for that work. The broader source-to-Lean
requirements are preserved in the audit's `source-materials` snapshot;
their proposed extraction/review system is not implemented by this file.

## 1. Evidence and identity of the implementation

**EVID-1.** Every conformance result must identify the package version,
artifact digest, recorded source commit, runtime, backend, entry point,
suite revision, fixture license, command, comparator and raw results.
Source tests and tests of a published artifact are different evidence.
The audit's original baseline is source
`d83100e6ec038328a71a245e9fd10fbd768a38a5` and npm `0.11.0`.

**EVID-2.** Preserve original results, including failing attempts and their
corrections. Superseding a result requires a new record explaining why.
The tool `tools/snapshot-npm-audit.py` captures allowed evidence files with
SHA-256 and verifies their bytes. Hash verification establishes snapshot
integrity, not correctness of the claims or trust in the capture process.
Downloaded suite trees, installed dependencies and release binaries are
excluded; the provenance records identify how to obtain them.

**EVID-3.** Every claim must distinguish specification requirement,
formalized definition, checked theorem and its assumptions, implementation
refinement, finite test evidence, and release-artifact evidence. A kernel
check does not establish that the encoded definition matches the standard.
A passing example does not establish a universal theorem. A native proof
or test does not establish that the npm wrapper reaches the same operation.

**EVID-4.** Keep normative dependencies explicit. Start RDF semantic review
at the dated [RDF 1.1 Semantics Recommendation](https://www.w3.org/TR/2014/REC-rdf11-mt-20140225/).
Its §4 imports syntax definitions from Concepts. Track those definitions
as dependencies of the mathematical claims; do not treat them as an
optional primer or silently presume them. Record ambiguities and reviewer
decisions rather than replacing uncertain text with an unstated assumption.

## 2. Identity, graph sets and observations

**RDF-ID-1.** Model term identity separately from datatype-value identity,
heap identity, source occurrence identity and blank-node scope. Equality
of a literal's complete defining content determines one abstract literal.
An equality test based on denotation is unsuitable for graph membership:
an interpretation's literal map need not be injective.

**RDF-SET-1.** In one graph, two records denoting the same subject,
predicate and object denote one triple. If `t₁ = t₂`, then
`(G ∪ {t₁}) ∪ {t₂} = G ∪ {t₁}`. The graph representation may use a list,
but every exposed enumeration, cardinality, index and basic graph-pattern
evaluation must refine the abstract set. No duplicate-removing comparator
may be the sole test of these observations.

**RDF-SET-2.** Proving unchanged truth under repetition does not discharge
RDF-SET-1. Conjunction over `[t,t]` and `[t]` has the same truth conditions
while their list lengths differ. Preserve this counterexample in the
formalization review. The isolated audit proof demonstrates these separate
facts and explicitly does not prove a product refinement.

**RDF-ID-2.** Preserve distinct lexical forms even when their datatype
values coincide. Required controls include integer `1` versus `01`, equal
lexical strings with different datatype IRIs or language tags, and distinct
XMLLiteral lexical forms with equivalent XML values. Escape processing in
a surface syntax is separate from equality of the resulting literal.

**RDF-SCOPE-1.** Uniqueness applies within each constituent graph. The same
triple in different named graphs is permitted. Maintain default/named graph
identity, blank-node sharing rules and empty named graphs. Repeating an
assertion must not accidentally create another graph. Document graph routing
for every API that omits a graph name.

**RDF-SCOPE-2.** Document-level blank-node renaming must traverse nested
RDF 1.2 triple terms consistently and preserve intended co-reference.
Keep RDF 1.1 and RDF 1.2 source requirements and regression results distinct.

**QUERY-1.** Preserve legitimate SPARQL solution multiplicity, including
UNION and projection. Repair graph enumeration without applying blanket
DISTINCT to query results. Use controls for both graph uniqueness and
solution bags.

## 3. Reasoning verdicts

**OWL-1.** A consistency `true` requires an established model or a checked
decision procedure within its documented, mechanically recognized scope.
A refuter that stops without a clash, drops an unknown constraint or reaches
a witness-depth cap has not thereby established consistency. Report an
indeterminate verdict and its cause.

**OWL-2.** Non-entailment requires a justified countermodel or complete
decision in the applicable scope. Absence from a partial closure, inability
to negate a conclusion and an unverified open tableau branch yield unknown.
Budget exhaustion must remain distinct from an unsupported fragment.

**OWL-3.** Separate OWL Direct Semantics from RDF-Based and RL rule semantics.
No theorem about one regime may silently justify a verdict in another.
Class/individual punning is a required counterexample: individual equality
does not require equality of the interpretations of the same IRIs as classes.
A conservative refusal for detected punning does not establish complete
recognition of valid or invalid OWL DL ontologies.

**OWL-4.** The public API and corpus harness must use a shared semantic
decision path, or have explicit parity tests and a tracked unification
obligation. The 0.11.0 native harness applies RL clash detection before
tableau refutation; its public consistency operation omits that step.
Preserve the minimal sameAs/differentFrom contradiction, reverse orientation,
self-difference and equality-chain cases alongside satisfiable controls.

**OWL-5.** Inconsistency requires a proof of no model in the claimed
semantics of the original accepted input. A checked certificate about a
translated fragment is insufficient until the reader and preprocessing
preserve source satisfiability. Entailment by refutation also requires a
proof that the generated goals cover every countermodel. These are the
existing certificate design's unfinished O1, O2 and O3 obligations.

**PROOF-API-1.** Each exported definitive verdict must come from an
evidence-bearing result indexed by its input and semantics, or have a
closed soundness theorem on the actual public producer. Prove the wire
conversion preserves that meaning. Unknown is a distinct outcome; never
reinterpret an unchecked search verdict as certified evidence.

**PROOF-API-2.** A result for one OWL regime or role cannot authorize
another without an explicit conversion theorem. Keep Direct Semantics
roles and RDF-Based reasoning separate. Generated names require tagged
constructors or proved freshness. Validate the declarative semantics using
reviewed definitions and model witnesses; axiom hygiene alone does not
validate its adequacy to the standard.

**PROOF-QA-1.** Audit exported claims, transformation theorems and their
discharged assumptions, not theorem counts. CI must reject bypass of the
certified producer. Include invalid-construction and regime-substitution
checks, model-preserving tests and exact-artifact tests. Soundness and
coverage have separate acceptance criteria.

**PROOF-SPEC-1.** Source satisfaction must not be defined as satisfaction
of the implementation's output, nor reuse an operational role index as
its meaning. State source vocabulary membership and structural mapping
independently; prove lookup and compilation against them. Review the
formalized relation against the cited W3C clauses. A theorem about that
relation does not itself prove the transcription matches the standard.

**PROOF-SCOPE-1.** Both model and no-model verdict constructors require
whole-input admission evidence when their source semantics covers only a
fragment. A model of the recognized clauses of an unsupported graph can
be vacuous; it is not a consistency certificate for that graph. Preserve
the `C equivalentClass Thing` / `C equivalentClass Nothing` counterexample.
Keep admission separate from source meaning and expose it in wire soundness.

**PROOF-SCOPE-2.** For a reader that claims to reject unsupported input,
prove that successful admission gives a structural mapping witness for
every original triple. Model preservation alone permits dropping axioms;
it does not prove whole-input coverage. Mutation-test a reader that returns
an empty axiom list regardless of input. The coverage proof must fail,
even when existing one-way preservation proofs still type-check.

**PROOF-QA-2.** Mutation-test the actual production definitions and require
failure in the relevant proof, not merely an example guard or syntax error.
Required controls include annotation-role misclassification, reversed
subclass compilation, dropped input clauses, name-constructor collision, checker bypass and
inverted verdict output. A failed process with no executed inventory is
an infrastructure failure, not a semantic test result.

**PROOF-API-3.** Connect the exact exported producer to the certified result;
an unused safe helper does not close the API contract. Prove JSON-field
meaning and response schema separately: a lookup that maps missing fields
to unknown cannot establish that an explicit null was returned.
Prove unique response keys when external parsers can choose a different
duplicate-key convention from the formal field lookup. Test text,
parsed-dataset, dispatch and rebuilt public-package paths. State the selected
graph in the theorem; default-graph reasoning is not whole-dataset semantics.

**PROOF-QA-3.** Reject resource exhaustion as proof-mutation evidence,
including Lean heartbeat/recursion limits as well as process timeouts.
Require complete expected-result fields even when the expectation is null,
and reject duplicate JSON keys. Test these gate failures themselves.

**PROOF-QA-4.** Test each public adapter's actual refusal contract. A loader
may throw an error that retains the ABI envelope; an API may parse input
before invoking the reasoner. Validate the retained envelope and the specific
public parse-error fields. A generic runtime exception, returned error where
a throw is required, or unrelated exception message must fail the gate.
Preserve failed runner iterations and test the corrected runner with invalid
refusal controls. Do not change product expectations to hide a runner error.
For a synchronous native/Wasm child, use a termination signal it cannot ignore
when a timeout expires. Node's default SIGTERM can be caught, leaving
`spawnSync` waiting indefinitely despite its timeout. Test the hard-kill path.

The [public consistency boundary](20261021-owl-public-boundary.md) connects
the restricted producer to the existing operation in the local draft. It
also records a transitive-equality coverage defect that passed the old
model-preservation proof. General coverage/completeness needs its own
invariants and tests; it does not follow from no-false-positive soundness.

Detailed requirements and current-source probes:
[semantic proof boundaries](designissues/2026-10-21-semantic-proof-boundaries.md).

Implementation progress: [Certified OWL decisions](20261021-certified-owl-boundary.md)
provides a proved boundary for the existing checker fragment and an actual
model-preservation acceptance gate. The reader/preprocessing proof and
public API obligations remain unfinished; the legacy annotation/closure
acceptance case still fails. The [restricted RDF reader and name repair](20261021-owl-reader-preservation.md)
adds a proved bridge for an explicit atomic fragment and removes the
legacy generated-name collision. It does not discharge the general
reader, preprocessing, entailment or public-adapter obligations.

## 3a. Shared semantics and specification adequacy

**CONVERSION-1.** Preserve source datatype information whenever the specified
operation depends on it. A value-space projection sufficient for equality
need not suffice for casting. For the dated F&O 2007 conversion contract,
zero yearMonthDuration casts to string `P0M`, including from lexical `P0Y`;
zero dayTimeDuration and generic duration cast to `PT0S`. State and test
the source-to-result relation, including derived string targets and callers.
Returning the original lexical form is not a canonicalization proof.

**CONVERSION-2.** Target membership proves only that a result inhabits the
target datatype. It does not prove the required conversion: both the wrong
and correct duration strings are valid strings. State which independent
specification predicate the theorem connects to the actual producer; retain
separate membership, conversion, caller and artifact obligations.

**PROFILE-1.** A restricted profile must either implement admitted constructs
correctly or refuse them explicitly. Test the admission boundary as well as
the underlying engine. Repeated or grouped zero-width assertions must not
become consuming characters. Keep independent reference vectors and laws
such as repeated-anchor idempotence; a production comparator cannot be its
own sole oracle. A host implementation is a valid oracle only for the same
dated semantic contract and admitted scope.

**PROFILE-2.** Preserve the caller's specification edition when selecting a
shared profile. XSD 1.1 name escapes must not accidentally use an XSD 1.0
admission policy. Record recovered and excluded test counts separately;
zero failures with additional exclusions is not unchanged coverage.

**RANGES-1.** Establish the representation preconditions of each operation.
Membership in a union of intervals can tolerate unsorted input; a complement
algorithm may require sorted, disjoint intervals. Normalize or prove that
invariant before calling it. New character-class admission must test both
positive and complement classes with non-ASCII boundary witnesses. The
integration exposed `\c` and `\C` both accepting U+00B7 because the name
table appended extra intervals out of order. A correct membership result did
not establish correctness of its complement.

**QA-RECONCILE-1.** When a public contract narrows, record each changed test
expectation and the lost decision coverage. A test for an explicit unknown
is an API-contract test; it is not a conformance pass for the unresolved
semantic question. Retain the earlier failed evidence and specification
expectation. A known contradiction rejected as unsupported remains a
reasoning capability gap.

These requirements follow the [PR1 independent review](audits/pr1-review-20261022/REVIEW-PR-1.md)
and [integration record](20261022-pr-integration.md). They do not assert that
the full shared semantics or every caller has been proved adequate.

## 4. API transport, validation and refusal

**API-1.** Options that choose output format must preserve the evaluation
environment: registered SERVICE endpoints, extension functions, clock and
graph/version selection. Entailment options may deliberately change the
reasoning regime, but must preserve unrelated environment inputs.

**API-2.** Version selection must survive the whole operation, including
SPARQL parsing, update execution, graph-result reparsing and type declarations.
Test runtime objects against the shipped TypeScript contract.

**API-3.** A converter must invoke required metadata validation itself.
Validation performed only by a native test harness does not validate the
public conversion API. Serialization must produce legal terms and preserve
the intended identity, including generated blank-node labels and base IRIs.

**API-4.** Unsupported constructs must produce a documented refusal when
silently ignoring them changes the requested result. Feature labels and
scores must identify supported scope and selected corpus subsets.

**AUTH-1.** The Solid library and CLI must have an explicit, aligned
authorization policy. Omitting an insecure-mode option or setting it false
must not silently authorize anonymous writes. Test defaults and overrides
through the public library, not only the CLI.

**RESOURCE-1.** State resource policy separately from semantic correctness.
Expose or document canonicalization budgets and refusal behavior. A process
timeout is an observation, not proof of nontermination or a wrong algorithm.
For synchronous Wasm, enforce test deadlines outside its blocked event loop.

## 5. Release acceptance and repair lifecycle

**GATE-1.** Execute semantic regressions against the exact packed artifact
that will be published. `tools/npm-semantic-gate.mjs --package DIR --json FILE`
is a finite incident regression gate. It must fail on missing capabilities,
missing fixtures, zero discovery, wrong answers, errors or timeouts. Record
discovered, pass, fail, error, timeout and skipped counts separately.

**GATE-2.** Expected failures remain defects. They may be useful in a
development suite but cannot count as verified behavior in release claims.
An unimplemented gate obligation remains open even if the implemented subset
passes. Missing browser/network permissions are environment limitations;
they do not establish either product success or product failure.

**GATE-3.** Release CI must enforce these gates with failure propagation;
recording a failing native scoreboard as a nonblocking measurement is
insufficient. The local gate does not become an enforced publish condition
until `factoidal-builds` calls it on the packed artifact. That workflow
integration is an explicit remaining requirement.
The local `repair-builds` workflow patch now runs the gate on the exact
tarball and additionally rejects any report with unimplemented audit
obligations. It has rejected the original tarball in a local execution.
The patch is not merged or active in GitHub Actions.

**GATE-4.** Each fix needs a failing-before reproducer, the corrected source,
focused proof/build checks, passing-after tests against a rebuilt artifact,
and relevant external suite runs. Verify that an intentional wrong answer
or missing artifact makes the gate fail. Preserve the semantic distinction
the test protects; do not simply change expected results to match the code.

**GATE-5.** A repair moves through: confirmed → source draft → checked source
→ rebuilt artifact verified → integrated → published → installed release
verified. Record exact evidence at each transition. No transition is implied
by editing a status table or by a different backend passing.

## 6. Incident obligation register

All entries remain open until their acceptance evidence is recorded.

| ID | Failure or gap | Required acceptance evidence |
| --- | --- | --- |
| R01 | Published npm test discovers zero tests | Nonzero, identified packed-artifact corpus; missing-tests negative control |
| R02 | Duplicates within one graph inflate counts | Per-ingestion identity/count/index tests, named-graph and solution-bag controls, refined set invariant |
| R03 | SERVICE lost with formatting/entailment options | Shared environment transport; all option combinations agree on results |
| R04 | Variable SERVICE loses solutions | Product interoperability test; retain qualification that spec section is informative |
| R05 | XSLT silently drops attribute sets; selected corpus overstates coverage | Construct-specific correctness or explicit refusal; full/subset score labels |
| R06 | Solid library anonymous write default | Library/CLI policy controls, explicit insecure opt-in |
| R07 | RDFC poison work has no exposed budget policy | Bounded operational tests, budget interface/policy, distinguish correctness from cost |
| R08 | RDF 1.2 nested blank-node scope splits identity | Recursive renaming invariant and public identity regressions |
| R09 | SPARQL 1.2 graph results/update lose version | CONSTRUCT result and positive update tests through installed API |
| R10 | OWL contradiction accepted and assurance overstated | Correct contradictions, unknown discipline, regime/punning controls, artifact/corpus parity |
| R11 | CSVW invalid metadata accepted; illegal blank labels emitted | Public negative metadata fixtures and independent output syntax validation |
| R12 | RDF 1.2 runtime/type declarations disagree | Strict consumer compilation plus runtime triple-term/direction checks |
| R13 | RML output IRIs fail base resolution | Four external fixture regressions and documented base propagation |
| R14 | Distinct XMLLiteral terms collapsed | Preserve both lexical terms through N-Quads, mutation, enumeration and query |

The original report also records suite mismatches and untested areas that
are not individually confirmed defects. Preserve their detailed results;
do not relabel every mismatch as a product bug or discard them because the
short register has fourteen rows.

## 7. Maintained entry points

- [Release cause investigation](20261021-npm-audit-release-causes.md): verified
  mechanisms, inference and missing release-job history.
- [Semantic assurance skill](../skills/semantic-assurance/SKILL.md): operational
  guidance for a semantic repair or release claim.
- [Test suites skill](../skills/test-suites/SKILL.md) and
  [npm release skill](../skills/npm-release/SKILL.md): required invocation points.
- [Preserved audit evidence](audits/npm-0.11.0/): original findings, commands,
  results, provenance, mathematical argument and broader spec2lean inputs.

Do not claim that these controls prevent every future defect. Their purpose
is to make the documented failures reproducible, block their recurrence at
the tested boundary, and expose what remains unproved or untested.
