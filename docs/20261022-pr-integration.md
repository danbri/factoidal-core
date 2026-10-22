# Integrate core PRs 1–3 on current main

Status: integration in progress, 22 October 2026.
[Draft integration PR4](https://github.com/danbri/factoidal-core/pull/4) is open.
No remote merge or npm release is claimed by this record. The user authorized integration of
[PR1](https://github.com/danbri/factoidal-core/pull/1),
[PR2](https://github.com/danbri/factoidal-core/pull/2) and
[PR3](https://github.com/danbri/factoidal-core/pull/3) onto current main.

## Source identity and reconciliation

The integration started at main `dac8e98`. PR1 head
`ed19f0905781008d12275c6fbbff257cb77f044a` has no common ancestor with that
main: apply its changes while preserving main's newer XML, numeric, RIF,
SPARQL, Authz and LWS work. A wholesale source replacement is not acceptable.
PR2 head `25bdeaf597bc9f91acd6a980861fb0d20eaf5927` applied as `65b2471`,
`87fd052`, `87af61c`; the worknote-index conflict retained both sets of notes.
PR3 head `87d1009df1842a64669530e3d1f1875e2b2c8e22` was reconciled as
`7501907`, with dispatch and CLI additions kept alongside Authz/LWS.
`6b2c847` adds the reviewed host lifecycle repairs and evidence described in
[the XMPP integration note](20261022-xmpp-pr3-integration.md).
Original branches and dirty audit worktrees are preserved. Main `d36c993c`
was merged as `96ac91dc` after PR2+PR3 artifact validation; the later combined
source requires its own build and tests.

PR1's [independent review and raw evidence](audits/pr1-review-20261022/README.md)
are retained unchanged. The introduced zero yearMonthDuration string-cast
regression and inherited repeated-anchor regex defect need integration tests.
Those original native results do not establish the behavior of the combined
source or of a rebuilt package.

## OWL contract reconciliation

On PR2 applied to main: the library plus public OWL producer built in 855
jobs. The reader gate passed 45 cases and rejected 7 proof mutations; the
public producer gate passed 20 cases and rejected 3 proof mutations. The
20 Python gate-parser controls passed. These are source results only.
[Raw source-gate evidence](audits/pr-integration-20261022/manifest.json) is retained
with hashes, including native probes used to reconcile the npm expectations.

Four npm test expectations came from an earlier draft and disagreed with the
restricted checked reader. Reconcile them explicitly:

- A positive property assertion plus its negative assertion is inconsistent
  in OWL. Negative property assertions are outside the checked reader. The
  contract test now requires explicit unknown/unsupported-syntax. This is a
  remaining decision-coverage gap, not a passed OWL inconsistency test.
- An unproved data assertion goes through refutation and returns unknown
  with incomplete-search; it is no longer refused as unsupported negation.
- An existential restriction is rejected by admission before consistency
  search. It must report unsupported-syntax, not a legacy fuel diagnostic.
- A punned example containing disjointWith is outside the checked syntax;
  consistency rejects its syntax. The separate entailment punning test stays.

Add two tests to preserve the distinction: consistency checks an admitted
contradiction at compatibility fuel 0/1/20000; entailment at fuel 0 reports
budget exhaustion, separately from incomplete search. Native producer probes
confirmed these diagnostics. The rebuilt PR2+PR3 artifact passed all 17
public OWL regression tests and all 20 packaged producer-gate cases.
Do not change the old failed logs: they show how these expectations arose.

The consistency producer can return a checked inconsistency or unknown; it
cannot certify satisfiability. Its fixed 64-round certificate search and
syntax restriction are compatibility limits. The old entailment path does
not acquire a soundness proof from the new consistency theorem.

The full npm run found two further obsolete expectations in `l4-core.test.js`:
a satisfiable subclass example expected `true` without a model certificate,
and a non-entailment example expected `false` without a countermodel. They
now require explicit unknown/incomplete-search. The existential example
also requires unsupported-syntax at both budgets. These are refusal-contract
tests; the underlying satisfiability/non-entailment decision gaps remain.

## PR2+PR3 artifact validation, before PR1 and latest main

[Raw evidence and hashes](audits/pr23-integration-20261022/manifest.json)
identify source `6b2c847e9ad5dc0e44f181bdee690eb6e3fbb53f`, Node 22.22.2,
Lean 4.33.1 and the normal Wasm build. Full Wasm SHA-256 is
`64ec60e2c52ab0f8c871e2147d553dad1a9326185fb90f282bb1615fbf280fd9`.
The npm tarball SHA-256 is
`0a7b3dfeefefe57c47dfd08994fc44080c5a86982f7afc02c84886c5f60d9366`.
These identify local test artifacts, not an npm publication.

- OWL/XMPP public regression run: 30 passed, including real TCP sessions.
- Independent `@xmpp/client` interoperability: 7 passed.
- Extracted tarball OWL producer gate: 20 passed.
- Full npm suite: 579 total, 575 passed, 3 failed, 1 skipped. The skip needs
  an external Jena installation. The original failed log is retained.
- Repaired test files: 41 passed. Besides the two OWL expectations above,
  the packaging test compared `/var/...` with canonical `/private/var/...`
  on macOS after successful extracted-package parse/query/store operations.
  It now checks exact real-file equality. It also accepts both npm pack JSON
  output shapes. The same packaging test passed under Node 26/npm as well.

The first redirected TCP test run was denied local socket access by the
execution environment; its log remains alongside the successful direct run.
This is not classified as an engine conformance failure.

Native comparison baselines on PR2+PR3 source `eef88c3` are retained with
fixture inventories and binary hashes: XSD datatypes 18,955 passed, 0 failed,
7,402 excluded (26,357 instance tests accounted for); schema-structure tests
were inventoried but not validated. RIF: 45 passed, 0 failed, 0 undecided,
0 unread, 1 existing local override, including all 6 import-rejection cases.
Runner exit status alone is insufficient: their printed counts were checked.

The live hub inference page also advertised obsolete positive consistency
verdicts. Its two pipeline examples both return unsupported-syntax; the
second is still semantically inconsistent. The page and tests now state
that distinction. Archived posts 30 and 40 retain their original examples
and prose with dated behavior notices; eight old verdict assertions become
explicit refusal-contract assertions. This does not count their OWL cases
as solved. The historical test run before correction records 18 pass/8 fail.

## Acceptance and evidence still required

Finish reconciling PR1, inspect its commits, then build the combined library
and Wasm with the normal build script. Run native suites with failure,
unknown, missing-fixture and comparator counts separately; run public OWL,
XMPP real TCP/interop, npm, hub and relevant newer-main host tests on that
artifact. Record source identity, runtime, commands and artifact digests.
Fetch current main before push and reconcile any further mainline changes.
Source proof success is not artifact validation or a merge receipt.

The existing F* scope qualifier remains: parser and algebra spec verified in
F*; on-disk backend has unverified OCaml-side optimization layers being
migrated back to F* (see fstar-purity-unwind.md). This integration is not a new
F* audit or an npm publication.
