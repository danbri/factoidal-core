# npm 0.11.0 audit: release causes and repair gates

Current PR status: [2026-10-22 reconciliation and evidence](20261022-owl-pr-reconciliation.md).
The dated checkpoint below is retained as historical evidence.

Date: 2026-10-21. This report concerns published `@factoidal/core@0.11.0`.
It records the baseline investigation and a same-day follow-up using the
actual GitHub build logs. Source line references name the baseline unless
another revision is stated.

The observed failures reached users because the release checks did not
exercise the same semantic paths as the native conformance harnesses. The
OWL case also has a contract error: a search that did not find a
contradiction is exposed as a constructed model. Build provenance and
successful theorem checking do not establish that contract.

## Evidence boundary

- Core baseline: `d83100e6ec038328a71a245e9fd10fbd768a38a5`, as recorded in
  the published Wasm stamp and the independent audit. The repair checkout
  started at this commit. Shell network resolution failed, but subsequent
  read-only GitHub connector calls resolved current main to
  `5e52ce0e916d7fb44dd133d63e3293229ccb0c6b`, ten commits ahead and zero
  behind this baseline. The current-head check is separate from the
  published-artifact review and local repair build.
- Build-workflow checkout examined:
  `danbri/factoidal-builds@6d9d989414c4e8c228ffd3db01d9367f68ac87f4`.
  References to `build.yml`, `npm-publish.yml` and `scripts/publish.sh`
  below refer to that repository at that revision.
- The package stamp names release `build-d83100e6ec03-web` and
  [build run 39574221615](https://github.com/danbri/factoidal-builds/actions/runs/39574221615).
  Its Linux Lean and web-gates job logs were retrieved through the GitHub
  connector. The Linux job checked out builds commit
  `86f55dfbb53a13c99aa60bee3f287a3a04ea2ab1`; its `build.yml` matches the
  inspected workflow. The one intervening commit to `6d9d9894` changes
  only `latest/*.json` release pointers. The logs confirm that both jobs
  checked out core `d83100e6`.
- Independent observations and runnable reproductions are retained beside
  this checkout in `REVIEW-0.11.0.md`, `audit/`, and `logs/`. Finding IDs
  R01–R13 below refer to that report. This document adds source and CI-log
  inspection; separate repair notes record local builds. It does not claim
  a repaired package or integration with current main.

## OWL: two separate failures

The public call below returned `{consistent:true}` from the published
package:

```js
await owlIsConsistent(`
  @prefix owl: <http://www.w3.org/2002/07/owl#> .
  <urn:a> owl:sameAs <urn:b>; owl:differentFrom <urn:b> .
`);
```

1. **The public pipeline omits the native harness's clash decision.**
   `formal/lean4/Harness/OwlProbe.lean:1455–1475` checks
   `detectClashPlusI r.index` and also consults the refuter. By contrast,
   `formal/lean4/Wasm/Ops/ReasonDl.lean:86–102` computes `closureFix` and
   calls only `tableauConsistent`. Closure adds consequences; it is not
   itself the Boolean clash decision. The two entry points do not execute
   the same consistency procedure. This omission explains why a native
   inconsistency score cannot establish the npm verdict. Confirm the
   individual clash row with a regression before claiming this omission
   explains every OWL failure.

2. **The public Boolean contract is stronger than the search result.**
   `formal/lean4/L4Factoidal/OWL/Refute.lean:21–27` explicitly says an
   unsatisfiable graph outside the calculus's reach can return
   `some true`. Lines 37–42 preserve that value to match an earlier wire
   contract. The npm declaration instead says `true` means “a model
   built” (`npm/factoidal/index.d.ts:629–631`). The Wasm entailment path
   similarly describes a quiescent refutation goal as a constructed model
   (`ReasonDl.lean:132–141`). Adding the missing clash call fixes a class
   of wrong answers; it does not make this general positive contract true.

The npm regression at `npm/factoidal/test/l4-core.test.js:314–330` checks
one false case, `rdf:type owl:Nothing`, along with a simple true case and
budget exhaustion. It contains no sameAs/differentFrom contradiction.
The native harness deliberately consumes the refuter's `some false`
result (`OwlProbe.lean:1432–1435`, `1463–1466`); its consistency scoring
does not certify a model for every surviving graph. Thus both tests can
be green while the public model claim is false.

The first repair attempt added that native clash decision. Further tests
show why this is insufficient: an annotation property with domain
`owl:Nothing`, used in an annotation assertion, is satisfiable under Direct
Semantics but is reported inconsistent by that path. Class/individual
punning provides another counterexample to unrestricted RDF-based
`sameAs` substitution. These are distinct from the original false
consistency verdict. See the explicit models in the
[OWL repair record](20261021-owl-public-verdict-repair.md).

Repair the shared Lean decision pipeline with an explicit semantics and
supported fragment. A clash over RDF-based consequences is a Direct
Semantics refutation only when the intervening mapping and rules preserve
that semantics. A blacklist of observed counterexamples does not establish
this. Outside a justified fragment, return indeterminate. Also return
indeterminate when no contradiction was found unless a supported-fragment
decision procedure or checked model justifies `true`. Apply the same rule
to negative entailment answers and to unsupported conclusion forms. Add
ordinary regression assertions through the public npm entry, including
satisfiable annotation and punning controls, sameAs/differentFrom,
negative property assertions, budget exhaustion and unsupported forms.
Do not turn the new wrong-verdict cases into XFAILs.

## What the release checks actually require

| Check in inspected workflow source | What it establishes | What it leaves open |
| --- | --- | --- |
| `build.yml:150–160`, native dispatch and CLI smoke | Smoke scripts succeed | Complete public npm behavior |
| `build.yml:162–177`, native conformance scoreboard | JSON report exists; exit status is retained | Failing conformance cases are explicitly nonblocking |
| `build.yml:540–549`, npm suite | Source-tree tests succeed with installed build artifacts | Cases the suite does not assert |
| `build.yml:550–566`, engine comparison | Selected comparison tests agree or have expected failures | Independent semantic correctness; this comparison contains no OWL consistency test |
| `build.yml:571–591`, SPARQL differential | Diagnostic result and exit status are retained | Disagreement is explicitly nonblocking |
| `build.yml:592–614`, known-defect suite | Recorded XFAIL/XPASS policy is followed | Defects marked expected can remain present |
| `scripts/publish.sh:21–41` | A `web-gates` artifact exists before web release | Semantics beyond those gates |
| `npm-publish.yml:141–150` | The selected build's `web-gates` job succeeded | New conformance execution during publication |
| `npm-publish.yml:215–260` | Tarball contains the expected engine and a matching version/hash stamp | Behavioral parity across native, Wasm and wrapper entry points |

There is already a useful packed-artifact smoke test:
`npm/factoidal/test/pack-integrity.test.js:29–54,57–82` packs, extracts,
parses, queries and opens a small store. It deliberately excludes tests
from the tarball (lines 72–73). The omission is normal packaging practice;
the R01 finding is that the retained `npm test` command can report success
with zero tests in that installed artifact. Do not infer that CI ran zero
tests: the inspected web-gates job runs the source suite.

The release skill still mixes the active builds workflow with historical
F* publishing instructions. For example,
`skills/npm-release/SKILL.md:215–239` describes the old re-extract/publish
sequence, while its later prose says `prepublishOnly` repeats the suite.
The inspected current workflow packs with `--ignore-scripts` and publishes
a tarball (`npm-publish.yml:217,269`). The actual source job is the reliable
test gate. Update this skill to describe one current path and keep the old
path in a clearly dated historical note.

## Actual release build: failures did not block the jobs

The [Linux Lean job](https://github.com/danbri/factoidal-builds/actions/runs/39574221615/job/119135665313)
and [web-gates job](https://github.com/danbri/factoidal-builds/actions/runs/39574221615/job/119150639442)
both concluded `success`, according to the Jobs API. The logs show what
that status permits:

- The native scoreboard exited **3** at 09:21:44 UTC. Its summary reports
  176 numeric rows, of which 29 have failures, plus one ERROR/TIMEOUT/
  UNPARSED row. These are overlapping report rows, not 29 independent
  failing suites or a count of unique failed tests. The one error row was
  the SPARQL differential: the F* binary was not installed in that job.
  The script captured the nonzero status and continued, exactly as the
  checked-in workflow says. This is now observed release behavior.
- In the native DL regime, the broad inconsistency catalog reported
  **126 pass, 1 fail, 1 other (128)**; positive entailment reported
  **194 pass, 12 fail (206)**. The separately scoped Approved + DL + DIRECT
  subsets reported **97 pass, 0 fail** for inconsistency and **150 pass,
  0 fail** for positive entailment. Thus the broad red numbers alone do
  not show a failure of those narrower conformance claims. They still do
  not validate the distinct npm reasoning pipeline.
- The actual npm suite reported **494 pass, 0 fail, 1 skip (495)**. Of
  those passes, **17 are explicit `xfail:` assertions**, leaving 477
  ordinary reported passes. The skip names an unavailable local Jena
  installation. Both existing OWL verdict tests passed; neither tests
  the audit's sameAs/differentFrom contradiction. These are CI-run counts,
  separate from the independent audit's local test inventory.
- The seven-case engine comparison passed, including one explicit
  expected-failure assertion. The later SPARQL differential ran with both
  binaries and reported **234 agree, 18 disagree, 6 F* errors, 0 Lean
  errors, 392 skipped (650)**, then exited **1**. The web-gates job still
  continued to the known-defect suite and succeeded. An engine
  disagreement is diagnostic evidence, not a verdict that Lean is wrong.
- The separate known-defect suite reported **22 expected failures still
  present, 0 unexpected passes, 0 probe errors**. Its green status means
  those recorded defects remained reproducible. It is not evidence that
  the defects were repaired.

Retained evidence in the audit workspace's `logs/` directory:

- `github-review-2.json`: job/step status metadata.
- `github-release-lean-job-119135665313.log`: checkout revision at line
  109; scoreboard failure policy at 6415–6426; OWL DL rows at 6632–6636;
  row summary at 6786; exit status at 6869.
- `github-release-web-gates-job-119150639442.log`: OWL npm assertions at
  2003–2010; npm totals at 3427–3433; differential totals and exit status
  at 3587–3589; expected-defect totals at 3641.
- `github-release-86f55dfb-build.yml`: workflow fetched at the job's
  builds checkout commit, text-identical to the inspected local copy.

The failures were visible in logs and deliberately nonblocking. That
distinction matters: the verified escape mechanism is the gate policy
plus incomplete public-API coverage, not suppression of all evidence.

## Repeated causes across the findings

| Findings | Verified source or observation | Repair boundary |
| --- | --- | --- |
| R02, same-graph duplicate triples | `RDF/Graph.lean:8–24` uses `List Triple`; set semantics depend on operations. Public producer paths admit repeated identical triples, while `add` and `fromQuads` controls deduplicate. | Establish the graph invariant at all producers and test observable size, iteration and basic-pattern count before any canonicalization or isomorphism comparison. |
| R08, nested blank-node identity | `RDF/DatasetMerge.lean:43–45` renames only immediate blank-node terms. `RDF/Graph.lean:63` has a separate recursive renamer. Public scoping uses the former (`Wasm/Ops/Parse.lean:343–344`). | Use one recursive renamer and test identity shared between an asserted triple and nested triple terms. |
| R09, RDF 1.2 wrappers | The audit separates successful engine evaluation from graph-result reparsing and missing update version options. | Carry the RDF/SPARQL version through input, execution and result conversion; test the full public call. |
| R11, CSVW validation | Native negatives call `CSVW.validate` (`Harness/CsvwRdfRun.lean:365–383`). `Wasm/Ops/Formats.lean:436–456` decodes metadata and calls `convert` without that validation step. | Share a validated conversion pipeline; exercise negative metadata through the converter users call. |
| R05, XSLT claim scope | `skills/test-suites/SKILL.md:119` calls the 88-case subset a regression pin whose selection excludes unimplemented features. The full 1,690-case Xalan corpus is documented on line 120. The npm README labels the short score only “XSLT 1.0” (`README.md:119`). | Publish the full-corpus disposition and implement or explicitly reject unsupported constructs; silent omission needs an ordinary regression. |
| R06, Solid defaults | `Wasm/Ops/Solid.lean:51–54,75–96` preserves a legacy no-auth path and defaults WAC to false when no OIDC configuration exists. The audited CLI and library have different defaults. | Require the explicit development option for anonymous writes and test the bare library configuration. |
| R03, R04, R07, R12, R13 | Audit reproductions distinguish result options, variable endpoints, resource budgets, declarations and output-base handling. | Treat each public option and overload as an entry-point contract; native scores do not cover missing wrapper arguments. |

For R02, the invariant is per graph. Equal subject, predicate and RDF
term-equal object in the same graph form one triple. The same triple may
occur in two named graphs. Literal term equality is not datatype value
equality: for example, distinct lexical forms of an integer can denote the
same value while remaining distinct RDF terms. The existing minimal
duplicate uses exactly the same literal spelling. Also audit the engine's
literal comparator separately: `Graph.lean:28–30` explicitly mentions its
language-tag/XMLLiteral rules. A fix must not merge merely value-equal
literals.

The audit's graph comparisons first deduplicate representations, as graph
comparison normally requires. Such a check can establish graph content and
still miss an API exposing duplicate rows or a wrong size. Add direct
invariant checks beside graph-isomorphism tests.

## Proposed release gates, in repair order

1. Run the small R02–R13 regressions against a freshly packed artifact,
   with asset-path overrides cleared. Start with wrong OWL verdicts,
   same-graph duplicates, nested blank-node identity and Solid defaults.
   Zero discovered tests, missing fixtures and unexpected skips must fail.
2. Run every applicable OWL inconsistency fixture through the same public
   API that ships. Report wrong booleans separately from indeterminate,
   unsupported, parse error and timeout. Require zero known false claims
   of consistency; retain satisfiable controls to detect false refutations.
3. Share semantic decision functions between harnesses and public ops.
   Keep fixture I/O in the harness, but remove extra clash/validation
   steps that exist only there. Record intentional configuration
   differences, including budgets, resolvers and version flags.
4. Maintain a machine-readable result by suite, engine, entry point and
   options. Preserve ordinary pass, fail, XFAIL, skip and timeout counts.
   The current helper catches any exception as an expected failure
   (`npm/factoidal/test/helpers.js:21–31`); match the intended failure so a
   missing fixture or unrelated crash cannot satisfy it. XFAIL counts must
   not contribute to a conformance pass claim.
5. Require no regressions against explicit per-case baselines for broad
   suites that still have gaps. Treat the new wrong-answer/data-integrity
   regressions as blocking. Keep failures and unsupported features visible
   beside the corresponding public capability; a green build is not a
   conformance percentage.
6. Compile representative TypeScript consumers, reparse emitted RDF with
   an independent implementation, and test option combinations that change
   paths: SERVICE plus JSON/CSV output or entailment, RDF 1.2 CONSTRUCT and
   UPDATE, CSVW invalid metadata and RML output bases. Run real browser and
   network tests in a CI environment that permits those operations.

## Current main and integration boundary

The connector resolved main to
[5e52ce0e916d7fb44dd133d63e3293229ccb0c6b](https://github.com/danbri/factoidal-core/commit/5e52ce0e916d7fb44dd133d63e3293229ccb0c6b),
created at 11:59:45 UTC on 2026-10-21. The immutable comparison from the
published commit confirms ten newer commits. They include LWS changes,
structured-error handling and npm module refactoring, so the local repair
must be integrated with that work before any release claim.

Read-only inspection at that head found overlapping files without the
specific repairs checked here:

- `Wasm/Ops/Handles.lean:165–171` still snapshots services for ordinary
  queries, while `datasetQueryRaw` at 393–399 still takes only the clock
  and calls `queryRawParsed` without services. R03's path mismatch remains
  in source. `datasetUpdate` at 191–194 still has no version parameter.
- `npm/factoidal/lib/api.mjs:650–681` still sends entailment/output calls
  through that raw path. Current main also adds centralized option and
  error handling; those changes must be preserved when integrating the
  draft. This inspection is not a runtime test of a rebuilt current main.
- The comparison lists no change to `Wasm/Ops/ReasonDl.lean` or the
  `OWL/Refute` implementation. The baseline OWL source causes therefore
  remain at this inspected head. The current TypeScript declarations were
  also separately checked by the coordinator and still lack R12's RDF 1.2
  members.

Evidence: `github-core-main-commit-20261021.json`,
`github-core-main-compare-20261021.json`,
`github-main-5e52ce0e-Handles.lean` and `github-main-5e52ce0e-api.mjs` in
the audit workspace's `logs/`. No remote changes were made.

## History still to establish

Trace when the stronger OWL model wording and separate native clash path
entered the tree. The npm publication job and any human review/approval
history have not been inspected. Do not assign responsibility from git
author names: the repository's own `CLAUDE.md` warns that agent commits use
the owner's identity. Source and build logs support the mechanical causes
above; they do not establish who reviewed or approved this release.
