# Standards reuse: progress and draft PR review

Recorded 22 October 2026. The recent work is recorded in the 21–22 October
updates of [the standards survey](w3c-survey.md). It was uncommitted work;
these dates are the work ledger, not a claim derived from a 24-hour Git log.

## What changed

The survey now connects normative specification dependencies to actual Lean
imports and observable reuse defects. XML namespace resolution is substantive
shared code used by XML consumers. Shared XSD values distinguish lexical
recognition, value membership, value equality, identity and casting. RIF,
SPARQL, SHACL and RDF now use these distinctions in more of their operations.

The recent numeric work centralizes comparison, IEEE arithmetic, unary
operations and numeric casts. This repairs integer-only decimal arithmetic,
negative quotient/remainder handling, float precision loss and casts that
checked only the source spelling. RIF matching and RDF conversion share the
same decoded values. Declared imports and saturation flags prevent incomplete
reasoning from being reported as a decided query answer.

Regex work adds explicit dialect boundaries, shared replacement selection and
an ECMA profile used by JSON Schema and CSVW. CSVW conversion retains warnings,
invalid-cell information and unsupported outcomes instead of silently losing
format constraints. Shared hexadecimal decoding and XML namespace adapters
remove smaller repeated implementations across additional families.

The reuse scanner records candidate helper names, selected semantic identifiers
and direct imports. Its groups are review leads, not proven duplicate code.
The survey retains remaining gaps and previous measurements by dated pass.

## Current evidence

The completed cast pass in the original working checkout passed all 937 full
build jobs, including the kernel-checked laws and executable guards. Its native
RDF/SPARQL manifests passed 924/924, with no skips or unsupported cases. The
eight RIF import/completeness regressions and five scanner tests passed.

RIF Core reports 26 pass, one fail and 12 undecided; one case is unread and six
import-rejection cases are not attempted. The numeric built-in case newly
passes. A former import failure became undecided after its invalid assumption
was exposed; that change is not a new pass. `EBusiness_Contract` is still the
decided failure in this checkout.

Earlier completed passes in this work also measured CSVW RDF and JSON at
270/270 each and JSON Schema draft-07 at 770/770. These are dated measurements
in the survey, not fresh reruns of every suite after every later change.
The new cast pass adds 73 guards and four laws. Finite suite results and these
specific laws do not establish complete standards conformance.

## PR scope and mainline integration

The review branch starts at `906527bae7a741780bb4bab8ccb0f8eb890c85ad`, on
`claude/autoexec-scratchpad-assess-37oeok`. It contains the standards/reuse work
and its supporting tests and documentation. Separate hash-grouping performance
work, benchmark drivers/results, README and owner-instruction edits are excluded.
The original dirty workspace is preserved.

The mainline fetched on 22 October is
`dfecea9733904462cb98b111acf47f57e19ffaa4`. Git reports no merge base between it
and this checkout; this is not a shallow clone. Main has substantial independent
changes, including broader RIF built-ins and F&O modules. The draft PR therefore
targets the existing working branch. It is a review checkpoint, not a mainline
integration or release-ready PR. Its local test counts describe this branch.

Before moving this work to main:

1. Reconcile this branch's `Fn.Numeric`, `Fn.Arithmetic` and `Fn.Cast` with
   main's `Fn.Numeric` and `Fn.Casting`; do not keep duplicate semantic kernels.
   Main's casting adapter currently covers temporal lexical checks; this branch
   adds value conversions. Main also has date/time, duration, Boolean and list
   modules that this checkout lacks.
2. Preserve main's additional RIF functions and engine behavior while moving
   datatype membership, identity, arithmetic, casting and completeness handling
   onto the agreed shared interfaces. Mainline RIF results must be measured
   separately; the older checkout's remaining failures are not mainline findings.
3. Integrate namespace, regex and RDF identity changes with main's newer parser,
   XML and SPARQL implementations using the regressions and specification
   references as evidence. File replacement would lose newer functionality.
4. Run the full mainline build and relevant manifests after each reconciled
   area. Review public API migrations, especially CSVW conversion results and
   `RIF.Saturate.Result`, against all mainline consumers.

Unresolved semantic work also includes complete regex dialect support,
namespace-context casts, wider subnormal/string conversion checks, import
profiles, XMLLiteral identity, and legacy store/join identity policies.


## Isolated PR validation

The selected snapshot passed a separate full `lake build`: **932 jobs**. The
five-job difference from the original checkout excludes the separate grouping
work; it does not remove any standards/reuse tests. Using the snapshot's native
executables with the original checkout's same local fixtures, RDF/SPARQL passed
**924/924**, and RIF remained **26 pass / 1 fail / 12 undecided**, with one unread
and six unattempted import-rejection cases.

All four Python scripts passed in the isolated worktree: reuse scanner **5/5**,
RIF boundary **8/8**, CSVW diagnostics **1/1**, SHACL diagnostics **3/3**.
The snapshot's audit counts **438 runtime modules / 64 candidate groups** and
records both RIF and SPARQL as direct consumers of `Fn.Cast`. The original
checkout's extra runtime module is the excluded `SPARQL.HashGrouping`.
The complete staged diff passes `git diff --cached --check`.

Reproduction from a checkout with the same test fixtures available:

```sh
cd formal/lean4
lake build
cd ../..
formal/lean4/.lake/build/bin/l4w3c --quiet \
  third_party/testing/w3c/rdf/rdf11/rdf-mt/manifest.ttl \
  third_party/testing/w3c/sparql/sparql11/manifest-all.ttl \
  third_party/testing/w3c/sparql/sparql12/manifest.ttl
formal/lean4/.lake/build/bin/l4rif --verbose
python3 tools/lean-reuse-audit-test.py
python3 tools/lean-rif-boundary-test.py
python3 tools/lean-csvw-harness-test.py
python3 tools/lean-shacl-harness-test.py
python3 tools/lean-reuse-audit.py --include-harness --output /tmp/lean-reuse.json
```

Inspect RIF's printed counts, not only its exit code: the runner currently
returns success even with a decided conformance failure. Run the Python files
directly; `unittest discover` skips these hyphenated filenames.

Local logs: `/tmp/factoidal-standards-pr-build.log`,
`/tmp/factoidal-standards-pr-wide.log`, `/tmp/factoidal-standards-pr-rif.log`;
inventory: `/tmp/factoidal-standards-pr-audit.json`.

## Rescue branches (assessed 2026-10-24)

- `claude/standards-reuse-20261022` (`ed19f090`): landed in reconciled form
  by `f1f78d98`. Nothing more to take.
- `claude/hash-grouping-wip-20261022` (`521ab1c1`): not landed. Main has its
  own proved hash grouping in the reference evaluator (`bbc31432`,
  `groupSolutionsFast` with `groupSolutionsFast_eq` in
  `SPARQL/GroupFastTheorems.lean`, used by `groupWhere`). The branch's
  `HashGrouping.selectPostFast` does the same work a second way, and groups by
  RDF term identity (`StableGrouping.ExactEncoder`) where main groups by
  `keysEqual`. Its 5.81 s to 148 ms figure was measured on 2026-10-11 against
  the list grouping that `bbc31432` replaced. The branch stays as the record.
- `claude/values-seeded-join-wip-20261023` (`9024e86b`): the VALUES leaf
  landed; the rest is https://github.com/danbri/factoidal/issues/985.

