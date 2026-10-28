---
name: semantic-assurance
description: Trace Factoidal semantic correctness and release claims from standards through Lean and public artifacts; use for semantic repairs, conformance reviews, reasoning verdict changes, or release assurance after the npm 0.11.0 audit.
---

# Semantic assurance

Use [the assurance specification](../../docs/semantic-assurance-spec.md) as
the obligation register. Keep its R01–R14 findings and the original audit
evidence reachable. This skill governs evidence for correctness claims;
it does not authorize publishing, messaging, or changes outside the task.

## Before changing semantics

- Start at the relevant dated standard and trace imported definitions.
  For RDF 1.1 Semantics, §4's syntax dependencies are part of the argument.
  Do not infer literal/triple identity from equality of denotations.
- Write the precise proposition and its scope: graph versus dataset,
  term versus value equality, RDF version, and OWL semantic regime.
- Separate a definition's intended meaning, a theorem over that definition,
  implementation refinement and artifact behavior. Record missing links.
- For a definitive semantic API, read the
  [proof-boundary design](../../docs/designissues/2026-10-21-semantic-proof-boundaries.md).
  State a soundness theorem on the exact exported producer. Require its
  concrete callers to discharge every hypothesis. A checker sound for its
  own input does not validate the reader or preprocessing that chose it.
- Establish the failing public observation before fixing it. A normalized
  graph comparator can conceal duplicate enumeration and wrong COUNT.

## Required distinctions

- Repeated identical triples in one graph are one member. Identical SPO in
  two named graphs is permitted. Preserve legitimate SPARQL solution bags.
- Literal lexical identity differs from datatype value equality, including
  XMLLiteral values. Test both duplicate retention and accidental collapse.
  When a fast path and the reference engine disagree, check which one the
  specification supports before you make one match the other. 2026-10-23: the
  SBM11 id path refused `rdf:XMLLiteral` local terms so that the reference
  answered, but the reference was the defective side (it joined by canonical
  XML; SPARQL 1.1 18.3 joins by RDF term equality). The refusal sent correct
  queries to an incorrect answer until
  https://github.com/danbri/factoidal/issues/963 repaired `Term.eqb`.
- A search without refutation is not automatically a model. A missing
  consequence is not automatically non-entailment. Preserve unknown, caps,
  unsupported scope, and checked model/countermodel evidence separately.
- OWL RL/RDF-Based results cannot silently justify Direct Semantics verdicts;
  include class/individual punning and annotation controls. Use evidence-bearing
  results indexed by input and semantics, or an equivalent closed producer
  theorem; wrappers must not bypass that boundary.
- Refuting a weakened fragment requires source-model preservation; asserting
  consistency requires the reverse model-lifting direction. Do not reuse
  a one-direction proof as equivalence. Negation goals must cover all
  countermodels, including when the produced goal list is empty.
- Review `Sat`/`Entails` definitions independently of the implementation.
  Exhibit models of satisfiable controls in those same definitions. A
  clean axiom list or a theorem with undischarged correctness hypotheses
  does not close the public contract. Generated identifiers require tagged
  constructors or a proved freshness condition, not a reserved-looking prefix.
- Keep source role membership independent of the operational lookup/index.
  Prove the lookup sound for original-graph declaration membership. A
  shared buggy index in both semantics and implementation defeats review.
- Require whole-input admission on both definitive verdict constructors.
  A model of only recognized clauses can ignore an unsupported contradiction.
  Pin the equivalentClass(Thing/Nothing) counterexample; do not call its
  vacuous partial-source model an OWL consistency certificate.
- Prove admission covers every original triple when the reader promises
  whole-input rejection. A one-way model-preservation theorem still permits
  dropping all clauses. Test the actual reader-returning-empty mutation
  against its coverage proof, separately from decision coverage tests.
- Output formatting must preserve SERVICE/extension/clock inputs. A native
  harness's validation does not establish validation in the public API.
- Preserve source datatype distinctions needed by later operations. A
  value-space projection can be correct for equality and wrong for casting.
  Pin zero yearMonthDuration (`P0Y` and `P0M` to `P0M`) against zero generic
  duration and dayTimeDuration (to `PT0S`), including derived string targets.
  A target-membership theorem cannot distinguish two different valid strings;
  require a separate source-to-result conversion proposition and caller tests.
- Test profile admission against an independent reference for the same dated
  contract. An inherited engine defect becomes an admitted-profile defect if
  the profile returns a wrong decided answer. Include repeated and grouped
  zero-width assertions, and keep refusals separate from matches and failures.
  Do not use the production comparison layer as its sole test oracle.
- Check the caller's specification edition before choosing a shared profile.
  When admitting legacy character tables, test positive and complement classes
  at non-ASCII boundaries. Check sorted/disjoint preconditions before interval
  complement: the XSD name table's unsorted union made both `\c` and `\C`
  accept U+00B7. Correct union membership does not prove correct complement.
  Report additional exclusions as lost coverage, even when failures stay zero.
  See [regex profile and interval preconditions](../../docs/designissues/2026-10-22-regex-profiles-and-range-invariants.md).
- When reconciling stale tests with a narrowed API, retain the normative
  expectation and original failures. Label an unsupported known contradiction
  as a decision-coverage gap even when its explicit-refusal contract test
  passes. Record the reason for each changed expectation in the worknote.
  See [the PR integration record](../../docs/20261022-pr-integration.md) and
  [preserved independent review](../../docs/audits/pr1-review-20261022/REVIEW-PR-1.md).

## Before reporting a repair or release

Run focused source checks, then the affected public tests with a rebuilt
engine. For artifact validation run:

```sh
node tools/npm-semantic-gate.mjs --package /absolute/path/to/unpacked/package --json /absolute/path/to/results.json
```

Inspect all counts and uncovered obligations. Zero discovery, missing
artifacts and timeouts are failures, never green skips. Do not fold XFAIL
into correctness passes. Some Node harnesses implement XFAIL as an ordinary
passing test: inspect individual case names and diagnostics, not just the TAP
footer. Report those separately (the 2026-10-22 npm replay had 588 runner
passes, comprising 571 ordinary passes and 17 expected-failure checks).
The finite gate does not replace external suites.
When updating the gate, verify that it rejects a missing package and a
known defective artifact; enforce synchronous Wasm deadlines out of process.

A check that no CI job runs goes out of date with no signal. On 2026-10-24
commit `a701bef1` (https://github.com/danbri/factoidal/issues/960) changed
the OWL consistency verdicts (a checked finite model gives `true` with no
`reason`) and added 3 cases to `tools/check-owl-public-boundary.py`, which core
CI runs. It did not update `tools/check-owl-public-artifact.mjs` and
`tools/test-owl-public-artifact.mjs`, which only the unmerged
https://github.com/danbri/factoidal-builds/pull/1 runs. On 2026-10-28 both
tools stopped with "23 !== 20" before they checked any case, and once
repaired they found a public-API defect in the 0.20.0 package
(https://github.com/danbri/factoidal/issues/1118). Rules: when you change a
case list or a verdict contract, grep `tools/` and `tests/` for every copy of
it in the same landing; a checker belongs in a CI job of this repository or of
factoidal-builds before its results are cited.

When changing verdict architecture, try an invalid proof-free verdict,
regime substitution and checker bypass. Record which proof or test rejects
each. A type-level example demonstrates the interface pattern only until
the actual public path uses it. Keep unknown counts separate from supported
decision coverage; returning unknown everywhere is not complete reasoning.

The checked interface example and its mutation controls are runnable with
`python3 tools/check-semantic-verdict-contract.py --lean /path/to/lean`.
Use it when designing or reviewing verdict boundaries. Passing this example
does not establish that the product has adopted the boundary or discharged
its semantic assumptions; verify the actual export separately.

For the actual OWL checker, use `OWL/CertifiedDecision.lean` and read the
[implementation record](../../docs/20261021-certified-owl-boundary.md).
`checkCert_rejects_model` covers every certificate for a modelled fragment
ontology. Its source-lifting functions still require the reader/preprocessing
proof; do not describe those conditional lemmas as completed O1/O2.
Run `python3 tools/check-owl-model-preservation.py --json /new/report.json`
when changing those transformations. Its remaining annotation/closure failure
is an acceptance failure, not an expected-failure pass. The generated-name
case now passes. Passing it is finite QA, not a
universal reader proof or evidence that the public adapter uses the boundary.

For the restricted RDF bridge, use `OWL/AtomicDirect.lean` and the
[reader preservation record](../../docs/20261021-owl-reader-preservation.md).
The pattern is independent `MapsTo`/axiom denotation, proof-bearing syntax
decoding, a compilation/model theorem, admission evidence, then the actual
checker and wire producer. Its admitted syntax is narrower than full OWL;
header/declaration validation is not the complete W3C reverse mapping.

A definite OWL answer needs a checked certificate of its own kind: `true`
needs a finite model accepted by `AtomicModel.checkModel` (theorem
`checkModel_sound`, conclusion `SourceModel` of the original graph);
`false` needs a refutation accepted by `checkCertFuel`; an entailment
`false` needs a countermodel accepted by `checkCountermodel`. The search
that builds them is untrusted; never add a premise about it to a soundness
theorem. Record:
[OWL model certificates](../../docs/designissues/2026-10-24-owl-model-certificates.md)
(https://github.com/danbri/factoidal/issues/960).

Run `python3 tools/check-owl-reader-contracts.py --json /new/contracts.json`
for adversarial cases, independent original-graph model witnesses, axiom
audits and real-definition proof mutations. Keep the unsupported
equivalentClass model/admission counterexample in that gate.
Run `python3 tools/check-atomic-direct-corpus.py --json /new/w3c.json` for
the unchanged W3C catalog. The latter's zero exit means a complete run
without observed wrong definitive answers, not conformance: retain
unsupported, unknown, missing serialization and definitive counts separately.
Keep the old failing path in its own gate; a new safe path does not repair
callers that still use the old one. Workflow drafts are not live enforcement.

For public consistency integration, run
`python3 tools/check-owl-public-boundary.py --json /new/public.json` and read
the [public boundary record](../../docs/20261021-owl-public-boundary.md).
Require the exact exported function to serialize the checked result, with
separate field-meaning and schema proofs. A missing field is not an explicit
unknown. Prove response keys unique so first-match and last-match JSON lookups
cannot disagree. Preserve the documented graph selection; named graphs must not leak
axioms or declarations into default-graph reasoning. State any narrowing of
supported syntax and budget behavior as a compatibility change.

Reject heartbeat/recursion/OOM failures as mutation evidence, not just outer
timeouts. Require null expectation fields and reject duplicate response keys.
Replay the passing source inventory with
`node tools/check-owl-public-artifact.mjs --package DIR --cases REPORT --json NEW_REPORT`.
This tests a named artifact with child-process deadlines; source proofs alone
do not certify the package. Keep broader decision regressions visible when
the restricted path returns unknown. The consistency proof does not certify
the separate entailment or tableau-diagnostic APIs.

Inspect the shipped adapter before asserting its error shape. The loader's
`call` throws on `ok:false` and preserves `.envelope`; current main enriches
dispatch errors with code/spec/position and the public API may raise a
`FactoidalError` before the reasoner runs (older artifacts used `ParseError`).
Check each contract independently of the raw producer schema. Never count
arbitrary runtime exceptions as expected refusals.
Mutation-test the runner with missing/wrong envelopes and unrelated public
exceptions; retain earlier failed runs when correcting the runner.
Use an uncatchable timeout signal for synchronous child processes; SIGTERM
can be trapped and defeat `spawnSync`'s timeout. Run the durable gate-parser
controls with `python3 -m unittest discover -s tests/assurance -p 'test_*.py'`.

Record source commit, artifact hash, runtime, suite revision, command,
expected/observed output and comparator limitations. Preserve new evidence
with `tools/snapshot-npm-audit.py`; use `--verify` to check a captured snapshot.
Keep source-draft, checked-source, rebuilt-artifact, integrated and published
states distinct. A local script is not an enforced release gate until the
publishing workflow calls it and propagates failure.

Update the dated repair note, assurance register, affected skills and
worknote index when new evidence changes a claim. Preserve contrary evidence
and unresolved interpretation questions. Link them rather than hiding them
behind an aggregate conformance percentage.
