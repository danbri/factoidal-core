# Native RIF Core baseline — 2026-10-22

Clean source `eef88c3ac775e8f831ffeaf880f7f1cf5dda5b42`
(main + PR2 + PR3) reports **45 passes, 0 failures, 0 undecided, 0 not read
and 1 local override**, accounting for all 46 Approved Core cases. All six
import-rejection cases pass. There are no skipped import-rejection cases or
stale overrides. This is a current-main comparison baseline for PR1, not a
claim that every RIF built-in or every formal semantic condition is proved.

## Commands and runtime

Build, working directory `integrate-pr3/formal/lean4`:

```sh
/Users/danbri/.elan/bin/lake build l4rif
```

Build succeeded: 123 jobs in 85.10 seconds. Run, working directory
`integrate-pr3`:

```sh
formal/lean4/.lake/build/bin/l4rif   /Users/danbri/working/sandbox/october/tpac/codex-npm-review/integrate-pr1/third_party/testing/rif-core-suite/Core_v1.22/Approved   --verbose
```

The native run completed in 0.406 seconds; peak child RSS was 8,044,544 bytes
on macOS arm64 with Lean 4.33.1. This is one run, not a performance gate.
No product source was changed. Binary SHA-256:
`b19a1fafcdb08e865e05ba795b363642d705528219decca19c7f7b7d4c5aa348`.

## Fixture identity and accounting

The vendored W3C Core_v1.22 Approved corpus contains 29 positive entailment,
5 negative entailment, 3 positive syntax, 3 negative syntax and 6 import
rejection cases. The fixture subtree has no diff from the baseline source.
Its root Git tree is `0100089be2e91df87fda0c8bf739b934d52aca06`; the
[fixture inventory](pr3-baseline-rif-inventory.json) records the 246 files
under Approved and their SHA-256 hashes, including repository-supplied
presentation-syntax companions. License/provenance are stated in the
vendored README: W3C Document License, official Core_v1.22 distribution.

The single override is `RDF_Combination_Constant_Equivalence_4`. The engine
reports **not entailed**, while the published fixture expects entailment;
the repository documents malformed datatype IRIs in its import companions.
This result is recorded separately, not counted as a pass. The override
file's hash and observed disagreement are in the run metadata. This run
uses the existing override; it does not independently re-audit its rationale.

The runner parses presentation syntax for Core syntax/entailment cases,
uses XML import closure for import-rejection cases, and supports RDF-only
conclusions. The entailment profile can select main's OWL-Direct adapter.
The round limit is 24. No case was undecided or unreadable in this run.
These are the existing comparator/admission policies, unchanged here.

The runner returns exit zero even when scored failures exist, so counts
and raw outcomes must be inspected. This baseline excludes the separate
four SPARQL-manifest RIF tests and the BLD/PRD suites. It makes no claim
about test cases outside the Approved Core corpus.

## Retained evidence

- [Raw run output](pr3-baseline-rif-run.log).
- [Run metadata](pr3-baseline-rif-run.json): command, hashes, timing/RSS,
  every accounting bucket, import-rejection results and observed override.
- [Fixture inventory](pr3-baseline-rif-inventory.json).
- [Build output](pr3-baseline-rif-build.log) and [metadata](pr3-baseline-rif-build.json).
- Environment is shared with the [XSD baseline record](pr3-baseline-xsd-environment.json).

PR1's final comparison should explain each lost decision, distinguishing a
necessary semantic correction from an omitted newer-main capability. A
pass count alone cannot make that distinction.
