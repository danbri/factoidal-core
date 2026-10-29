# XSD 1.0 configuration worknote

Date: 2026-10-29.

Implemented the configuration requested by `CONFIG-BRIEF.md`, using the
73 cases in `TARGETS.txt` as the target set. The
[design note](designissues/2026-10-29-xsd10-configuration.md) records the
configuration, reuse and proof boundaries. The
[report](../REPORT.md) records the final validation and unresolved cases.

The initial checkout had only the two untracked instruction files. All
work stays in this worktree. There are no commits, pushes, network calls
or changes to the Lean library root.

The baseline `lake build l4qt4` passed. Before-change target sets and the
`fn`, `xs`, `prod` and `misc` families were measured in both XPath and
XQuery modes with a separate temporary directory for every run. Explicit
`--family xs` is required for the `xs` target sets, and `--family misc`
is required to measure that family in XPath mode.

The general `tools/ensure-test-env.sh --check` reports missing unrelated
fixtures and published binaries in this checkout. The qt4tests catalog
and all 73 named target cases were checked directly and are present. No
result from an empty selection is used as a score.

Compare case names as well as family totals. The first full after-change
run gained passes overall, but four existing
namespace tests became failures. They distinguished directly nested
constructors from nodes inserted through enclosed expressions. Aggregate
scores alone did not expose that regression.

The final implementation preserves that distinction. The final build of
`l4qt4` passed, as did all compiled guards and bridge proofs. The target
run has 62 passes, no failures and 11 unsupported cases in XQuery mode;
XPath mode has 2 passes, no failures and 71 unsupported cases. The 11
remaining targets require pre-4.0 language profiles. Their dependencies
were retained, and unsupported cases were not counted as passes.

All nine complete target sets and the four complete affected families
were rerun in both modes. No family lost passes, and comparison of failure
names found no new failures. XQuery family passes increased by 6 in `fn`,
35 in `prod` and 58 in `misc`; `xs` was unchanged. XPath gained 2 in `fn`,
with the other families unchanged. Existing failures remain; the complete
counts and all 73 target outcomes are in
[the measurement record](20261029-xsd10-results.json).

The final source build log is `/tmp/cfg-s3-build-11.log`; before/after
test logs are `/tmp/cfg-s3-results/before-*.log` and
`/tmp/cfg-s3-results/verified-*.log`. `git diff --check` passed. The final
audit found no new proof holes, axioms, `native_decide` or partial
definitions, and no edit to `formal/lean4/L4Factoidal.lean`.
