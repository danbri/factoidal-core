# PR1 CSVW and streaming aggregate integration review — 2026-10-22

This is evidence from the in-progress `integrate-pr1` worktree, based on main plus PR2. It is not a statement about a published package. The integration agent owns the remaining Query changes, final full build and commit.

CSVW's data validation now preserves unsupported formats as `validationDecision? = none`. `Harness/CsvwValidateRun.lean` records that result separately from positive and negative passes. Its negative tests do not turn unsupported data into a successful invalidity decision. `CsvwJsonRun` and `CsvwRdfRun` still use Boolean `passes(validate metadata)` in metadata-only branches; inspection found that this structural validator currently emits errors/warnings, not unsupported findings. No current false-green input was established for those branches.

A concrete public integration gap was found in `Wasm/Ops/Formats.lean`: the old adapter assigned the newly diagnostic-bearing `CSVW.convert` result directly to `Dataset.default`. The integration agent has reconciled this with `csvwDatasetResult`, an explicit unsupported error for absent conversion output, and diagnostics on the public conversion response. That adapter's final build/test belongs to the integration run.

The namespace reconciliation retains main's one-pass `splitQNameShapeFast` implementation and its compiler-replacement equality. The strict `splitQName` wrapper validates prefix and local NCNames. The new guards cover malformed prefixed names, namespace declarations, XML 1.0 versus 1.1 undeclarations, duplicate expanded attribute names, and DTD normalization. This review did not independently run those guards.

## Streaming aggregation

Only `SPARQL/AggStream.lean` and the new `SPARQL/AggStreamTests.lean` were edited by this reviewer. Query remains owned by the integration agent.

SUM/AVG now retain a shared-arithmetic `EvalResult` and a count. Each step computes `evalArithmetic .add value accumulator`, matching Query's chosen reverse enumeration. No buffered input list or floating-point reassociation is used. [SPARQL 1.1 ToList](https://www.w3.org/TR/sparql11-query/#defn_ToList) permits a multiset enumeration in any order; [the Sum definition](https://www.w3.org/TR/sparql11-query/#defn_aggSum) nests numeric addition to the right. Query's `sumNumeric_reverse_enumeration` proves the selected fold equals the right fold on the reversed list.

Original RDF terms survive `varView`. Shared arithmetic validates and promotes them, preserving source float types and non-finite values. MIN/MAX now use the same original-value ordering call as the reference. The obsolete scaled-number and numeric-view caches were removed. The number of aggregate fields is constant; arbitrary-precision values can grow. Shared arithmetic parses lexical operands per step. No throughput claim is made; any cached value-space optimization needs its own refinement proof and measurements.

The complete source `AggStream.lean` check passed. `evalAggregate_stream`, `selectPost_aggPlan` and the other existing headline theorem audits report only `propext`, `Classical.choice`, and `Quot.sound`. This proves equality to the actual reference computation. It does not prove that the shared arithmetic/order implementation satisfies all W3C semantics, nor the existing unproved id-grouping relation.

The targeted build ran 70 jobs in 34.470 seconds. Existing `Storage/Sbm11/IdAggTests` passed. Of 29 new finite guard expressions, 27 passed and two failed:

- `MIN([float("16777217"), double("16777217")])` must retain the float, whose binary32 value is 16777216. It chose the double.
- `MAX([double("16777217"), float("16777217")])` must retain the double. It chose the float.

Both failures are in shared reference ordering: Query's legacy promotion/scaled comparator loses the source binary32 rounding distinction. The refinement proof passes while these semantic controls fail. The guards remain unchanged. The Query owner is applying a narrow numeric-value comparator repair and will rerun them. Do not report this initial 27/29 run as green.

## Proof mutation and evidence

The real `AggAcc.stepNum` was temporarily changed to retain the prior total and discard every input operand. The source check exited 1 at `num_stream` (`AggStream.lean:253`) with `omega could not prove the goal`. This was neither an import failure nor a heartbeat/recursion/OOM failure. The original source was restored byte-for-byte, SHA-256 `0bc70b1b168f185e743032da24c40b35d378bdf7dffbefc648222fa4cd50a333`.

The first mutation-report parser expected the wording `error: unsolved goals` and marked its detection false. The raw report is retained; the separate reviewed report records the observed tactic rejection. Automatic `sorryAx` entries in failed elaboration logs are artifacts of failed proofs, not accepted-source proof assumptions.

Evidence:

- [Initial reconciliation proof failure](pr1-aggstream-first-check.log): old MIN/MAX numeric-view mismatch.
- [Successful complete source check](pr1-aggstream-source-green.log): theorem axiom audits.
- [Targeted build log](pr1-aggstream-targeted-build.log) and [command/runtime metadata](pr1-aggstream-targeted-build.json): 27/29 new guards and passing existing IdAggTests.
- [Actual mutation rejection](pr1-aggstream-drop-operand-mutation.log), [original matcher report](pr1-aggstream-drop-operand-mutation.json), and [reviewed report](pr1-aggstream-drop-operand-mutation-reviewed.json).

All Lake commands used `integrate-pr1/formal/lean4` as their explicit working directory and respected the shared build-cache handoff. No source commit, push or Wasm build was performed by this reviewer for this increment.
