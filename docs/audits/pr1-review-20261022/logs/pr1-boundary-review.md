# PR #1 boundary review — 2026-10-22

Reviewed exact head `ed19f0905781008d12275c6fbbff257cb77f044a` against its parent `906527bae7a741780bb4bab8ccb0f8eb890c85ad`, in `review-pr-1`. This review is of that branch only; it is not a review of current main or a mainline integration. No checkout files were edited and no builds were launched by this reviewer.

**No concrete introduced correctness bug was confirmed in the assigned RIF import/saturation/query-completeness and harness-accounting changes.** This is a bounded review, not a complete standards-conformance or release approval. Namespace/XPath/XSLT and regex review remained with the parent reviewer.

## Checked behavior

- `formal/lean4/Harness/RifImport.lean:25–49` returns explicit missing, unreadable and parse errors. It uses the declared import URL as the RDF parser base. Its direct Turtle `parseStatements` call has the same initial state, fuel and parsing call as the public `parseTurtle` wrapper (`Syntax/Turtle.lean:1666–1671`); retaining parser state does not bypass an extra validation step in that wrapper.
- `formal/lean4/Harness/RifRun.lean:111–129` loads declared imports only. Failed imports increase `notRead` and prevent the entailment decision. They no longer supply an empty graph that can make a negative entailment test pass. Prefix inheritance is labelled as a test-suite convention, not a RIF semantic rule.
- `formal/lean4/L4Factoidal/RIF/Engine.lean:129–143` retains unknown results from datatype matching and equality binding. Unsupported equality/external-predicate heads now set the blocked flag (`:213`). The unchanged `closure` and `entails` code propagates blockage and round caps (`:235–264`).
- `formal/lean4/L4Factoidal/RIF/Saturate.lean:48–88` retains blocked, capped, unsupported-input and unsupported-output flags. `completeGraph?` rejects any flagged result. Positional atoms are deliberately excluded from RDF projection. Derived frame/member/subclass atoms with no RDF form set `unsupportedOutput`; they are not silently accepted as a complete RDF graph.
- `formal/lean4/Harness/Run.lean:371–381` now requires `completeGraph?` before returning the dataset for SPARQL evaluation. `Unified/RifEmbed.lean:755–760` also refuses agreement on incomplete saturation. Searches of the changed callers did not find a remaining caller treating the new result as an unconditional complete graph.
- `formal/lean4/Harness/ShaclNodeExprRun.lean:136–161` preserves missing included paths and counts missing, malformed and empty leaf manifests as failures. `Harness/ShaclRulesRun.lean:149–164` does the same for its four manifests. Their unchanged main functions propagate a nonzero failure count to exit status.
- CSVW harness changes keep unsupported conversion separate from pass/fail/skip and include it in the reported denominator. Numeric result comparison now uses the shared value comparator; the comparator documentation explicitly states that this is not an independent arithmetic oracle.

## Independent executable probe

[pr1-rif-boundary-probes.lean](pr1-rif-boundary-probes.lean) is a standalone probe outside the checkout. It imports the actual PR modules and checks seven conditions through engine/saturation entry points:

1. An integer/decimal value-alias join derives the goal.
2. An invalid numeric mapping yields an undecided verdict.
3. An equality-producing head sets the blocked flag.
4. That blocked result supplies no complete graph.
5. A zero-round result supplies no complete graph.
6. A derived frame with a non-RDF function-term object sets unsupported output.
7. That unmappable result supplies no complete graph.

All seven guards passed. [Raw log](pr1-rif-boundary-probes.log). The modules had already been built by the parent; this command performed no build:

```sh
# Working directory: review-pr-1/formal/lean4
/Users/danbri/.elan/bin/lake env lean \
  /Users/danbri/working/sandbox/october/tpac/codex-npm-review/logs/pr1-rif-boundary-probes.lean
```

This checks the implementation paths above; it is not a universal engine-adequacy proof or an external conformance suite. The parent's full build, eight RIF boundary regressions and W3C results are separate evidence and were not rerun here.

## Pre-existing or expressly limited behavior

These are **not new PR findings**:

- `Harness/RifRun.lean:189` returns zero even with decided failures, unread cases or no discovered cases. `HEAD^` has the same unconditional return. `docs/20261022-standards-reuse-review.md:121` expressly tells consumers to inspect counts. It remains unsuitable as a release gate if only its exit code is read.
- Native RIF refuses OWL import regimes (`Harness/RifRun.lean:143–160`), while SPARQL/RIF uses the existing OWL RL approximation (`Harness/Run.lean:347–356`). The PR leaves that split in place and documents it. The new shared loader does not establish complete import-profile semantics.
- The saturation flags express known operational incompleteness. They do not prove RIF semantic adequacy, parser soundness, or complete import handling. The new boundary theorems establish the result selector's behavior under flags, not such an adequacy theorem. This limit is explicit in `PORT_NOTES.md:14975–15002`.
- Missing SHACL per-test input files and unrecognized per-test forms can still be reported as skip/unsupported (`ShaclRulesRun.lean:107–147`; `ShaclNodeExprRun.lean:163–170`). Those branches precede this PR. The new manifest checks do not establish a release requirement that every discovered case is decided.
- Local basename resolution, incomplete profile checking, XMLLiteral identity and language-tag validity assumptions remain stated limitations. No network-import, full-RIF or all-backend claim is established by this review.

The existing failure and unknown counts should remain visible when this draft moves toward mainline integration. Do not reclassify those limits as new regressions merely because the new result type makes them easier to observe.
