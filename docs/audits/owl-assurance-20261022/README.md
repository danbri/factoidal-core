# OWL PR assurance evidence, 2026-10-22

Read [the reconciliation record](../../20261022-owl-pr-reconciliation.md) for scope,
final reports, and remaining failures. This directory preserves raw reports,
including superseded/red runs and errors in test tooling. An exit-zero W3C
measurement with unsupported/unknown outcomes is not conformance.

`pr-rebased-public.json` and `pr-rebased-reader.json` are the final source
reports after rebase onto main 5a40d08. `pr-owl-artifact-node22.json` tests
the packed artifact built before that rebase; it is not a build of the final
head. Both stages remain explicit in the reconciliation note.
The independent reviewer notes predate the final corrected artifact run; their
pending items are resolved only where the later evidence records it.
`pr-npm-semantic-final.json` and `pr-owl-broader-regressions-final.log` retain
the broader failing results. `pr-npm-errors-after-fix.log` is an intermediate
failed test expectation; `pr-npm-errors-final.log` is its corrected43-test run.

Paths inside raw reports refer to the original review workspace. No build
products or copied external suite trees are included. The original broader
audit snapshot remains in the archive identified at
[the incident index](../npm-0.11.0/README.md).

MANIFEST.json hashes each file except itself. It checks integrity, not the
truth of the claims or the trustworthiness of the compiler/runtime.
