# Integrate core PRs 1–3 on current main

Status: integration in progress, 22 October 2026. No remote merge or npm
release is claimed by this record. The user authorized integration of
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
PR3 head `87d1009df1842a64669530e3d1f1875e2b2c8e22` is being reconciled
separately, with its dispatch and CLI additions kept alongside Authz/LWS.
Original branches and dirty audit worktrees are preserved.

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
confirmed these diagnostics. Public rebuilt-artifact execution remains pending.
Do not change the old failed logs: they show how these expectations arose.

The consistency producer can return a checked inconsistency or unknown; it
cannot certify satisfiability. Its fixed 64-round certificate search and
syntax restriction are compatibility limits. The old entailment path does
not acquire a soundness proof from the new consistency theorem.

## Acceptance and evidence still required

Reconcile PR1 and PR3, inspect their commits, then build the combined library
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
