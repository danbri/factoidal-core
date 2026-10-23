# Native W3C XSD datatype baseline — 2026-10-22

On clean source `eef88c3ac775e8f831ffeaf880f7f1cf5dda5b42`
(main + PR2 + PR3), the runner reports **18,955 passes and 0 failures out of
18,955 scored instance tests**. It excludes 7,402 instances. All 26,357
instances in the 93 manifest-referenced test sets are accounted for, with no
missing or unreadable test-set manifests. This is the comparison baseline
for PR1's datatype changes, not a full XML Schema conformance result.

Fixture: exact main gitlink `7bc3365c652a322f3d762021b3879eb92dae7e30` from
W3C `xsdtests`, unmodified. [Fixture identity](integration-xsd-fixture.json)
records archive SHA-256, location and the unchanged W3C Document Notice and
License. Independent manifest enumeration found 26,357 instance tests and
15,378 schema tests; the latter are counted but not scored by this runner.

## Commands and runtime

Build, working directory `integrate-pr3/formal/lean4`:

```sh
/Users/danbri/.elan/bin/lake build l4xsd-datatypes
```

Build succeeded: 61 jobs in 47.52 seconds. Run, working directory
`integrate-pr3`:

```sh
formal/lean4/.lake/build/bin/l4xsd-datatypes   /private/tmp/xsdtests-7bc3365c652a322f3d762021b3879eb92dae7e30 --verbose
```

The run completed in 33.28 seconds; peak child RSS was 150,044,672 bytes
on macOS arm64 with Lean 4.33.1. This is one run, not a performance gate.
No suite filter or limit was supplied. Product sources remain unchanged.

Binary SHA-256:
`2c06cf8b92fa4c6eec70536a08f263ef7e54b30852f896febfd91b0aa428b999`.

## Comparator and exclusions

`Harness/XsdDatatypesRun.lean` compares library `validate`'s Boolean with
manifest expected validity after choosing an applicable expected result and
a governing simple type. The scorer covers datatype instance validity,
not expected canonical values, diagnostics, or Part 1 structures. It uses
XSD 1.1 behavior; it excludes groups marked exclusively version 1.0.
Schema classification/admission belongs to the existing runner and was not
changed for this baseline. The runner returns exit zero even when scored
failures exist: the parsed counts, not exit status alone, establish the
reported result.

| Excluded category | Instances |
| --- | ---: |
| structures | 7052 |
| mixed | 0 |
| schema-invalid | 1 |
| version-1.0 | 8 |
| unreadable | 139 |
| not-simple | 8 |
| assertion | 33 |
| unreadable-pattern | 105 |
| nilled | 3 |
| value-constraint | 53 |

Additional limits: unreadable includes parsing/encoding/declaration/type
resolution failures; assertion and unsupported-pattern cases are excluded;
value constraints and nilled instances are not datatype-scored. These are
coverage exclusions, not passing tests. The 15,378 schema tests seen are
not a schema-validity score. The separate `extra-suite.xml` is outside the
runner's `suite.xml` inventory.

## Retained evidence

- [Raw run log](pr3-baseline-xsd-run.log), including per-set and per-type counts.
- [Run metadata](pr3-baseline-xsd-run.json): command, source/binary/runner/log
  hashes, fixture identity, counts, exclusions, wall time and RSS.
- [Independent manifest inventory](pr3-baseline-xsd-inventory.json).
- [Per-datatype comparison counts](pr3-baseline-xsd-datatype-counts.json).
- [Build log](pr3-baseline-xsd-build.log) and [build metadata](pr3-baseline-xsd-build.json).
- [Environment](pr3-baseline-xsd-environment.json).

PR1 should run the same fixture with the same unfiltered command and compare
both scored results and the exclusion inventory. A changed denominator is
not automatically an improvement.
