# Bounded consumers of fn:generate

The candidate on `claude/qt4-generate-bounds`, based on main
`48b8a34a88379fd3cf4893fbede429beee92e6f0`, fixes two QT4 failures without
changing the generator's 100,000-state implementation limit or fixture scoring.

[F&O 4.0 §2.5.10](https://qt4cg.org/specifications/xpath-functions-40/Overview.html#func-generate)
expects incremental evaluation of bounded subsequences, including `fn:slice`
with a defined endpoint. The deployed specification snapshot already present at
`/private/tmp/qt4-fo4-unicode-policy.html` supplies this text and the inclusive,
length-relative slicing rules in
[§2.1.12](https://qt4cg.org/specifications/xpath-functions-40/Overview.html#func-slice).

`XPath4.Eval` now recognizes integer comparisons that bound `position()` and
uses the existing `genPull` evaluator. Slice recognition runs after ordinary
signature binding, so keyword placement, defaults, duplicate errors and partial
application keep their existing handling. Nonnegative start and positive end
allow a bounded prefix when a reverse slice does not default its start to the
input length. Negative offsets, omitted endpoints and reverse omitted starts
retain full evaluation and input-length semantics. Final selection still uses
the existing predicate/slice implementation. This is a targeted evaluation
strategy, not a general streaming-sequence representation.

Seventeen reachable `GenerateTests` guards cover named and positional slice
arguments, defaults, positive and negative strides, reverse ordering, finite
short input, length-relative fallback, invalid arguments, duplicate arguments,
and bounded positional comparisons, including an `index-where` consumer.
`XPath4.FeatureTests` imports the module.

Validation on macOS arm64, with the existing tracked QT4 fixture root:

- `lake build L4Factoidal.XPath4.GenerateTests l4qt4` passed (375 jobs).
- `fn-generate`: **13 pass / 3 fail / 0 unsupported** before; **15 / 1 / 0**
  after. Cases `generate-09` and `generate-16` now pass.
- `fn-slice`: **104 / 0 / 0**; `fn-subsequence`: **122 / 0 / 0**;
  `fn-index-where`: **22 / 0 / 0**; `fn-index-of`: **61 / 0 / 7**.
- Compiled recursion and csimp reachability gates, scoped to the regenerated
  `XPath4/Eval.c`, pass with the existing allowance files unchanged.

`generate-08` remains a visible failure: distinct constructed nodes from a
zero-argument callback collapse to one identity (expected count 20, actual 1).
This change does not repair constructor identity or claim the whole set passes.
The seven older-language unsupported `fn-index-of` cases remain outstanding.
The unchanged `fn/generate.xml` has 16 cases (`generate-01` through
`generate-16`), SHA-256
`eead9e4782f8a782887739832c868c20e1bcdee99ece98f4b4e07ea89e2b5ec8`.
No tests were excluded or reclassified. No new axioms, `sorry`, `native_decide`,
partial definitions, dependencies or allowance entries were introduced.

Logs: `/private/tmp/qt4-generate-{build-final,after,slice,subsequence,index-where,index-of}.log`,
`/private/tmp/qt4-generate-{tail,csimp}-audit.log`. The first build attempt omitted
tracked HACL files from the sparse checkout; including `third_party/hacl`
resolved those missing-file errors before the successful named build. The
independent APFS cache clone preserves the other worktrees' caches.

The obsolescence sweep updated the two evaluator comments describing supported
consumers. Dated catalogue baseline measurements remain historical.
