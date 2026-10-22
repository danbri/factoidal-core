# OWL QA gate PR review — 2026-10-22

**Suitable for a draft PR, with the limited claim stated below. This is not merge or release approval.** The reviewed workflows propagate source and artifact gate failures. The selected source tests and the previous rebuilt artifact provide useful evidence for a restricted consistency API. They do not establish complete OWL behavior, repair the separate entailment path, or certify the rebased package before it is built and tested.

The review began against `repair-core` and the workflow draft in `repair-builds`. It then checked the rebased tooling in `pr-core`, based on `dfecea9733904462cb98b111acf47f57e19ffaa4`. Selected review input hashes are in [20261022-pr-gate-review-inputs.json](20261022-pr-gate-review-inputs.json). The worktrees contain local changes; a base SHA is not a hash of those changes. No source semantics or workflows were changed by this reviewer. After review, the parent authorized changes to the reader report parser and one new unittest file only.

## Findings and disposition

1. **Artifact child deadlines needed a hard kill. Fixed in the PR draft by the parent.** `repair-core/tools/check-owl-public-artifact.mjs:147` used `spawnSync` with a timeout and the default SIGTERM. A synthetic Node 22 child installed a SIGTERM handler and then entered a synchronous loop. Its parent remained blocked after the requested 100 ms timeout; an independent 2 s safety deadline had to kill the process group. The same probe with `killSignal: 'SIGKILL'` returned `ETIMEDOUT` in 0.208 s. Evidence: [original control](20261022-pr-gate-sigterm-control.json), [fixed-setting control](20261022-pr-gate-sigkill-control.json). The current `pr-core/tools/check-owl-public-artifact.mjs:156` supplies SIGKILL. This was a deadline robustness defect; it is not evidence that the current imported package installs a SIGTERM handler or that its engine hung.

2. **Reader JSON report validation accepted missing and duplicate fields. Fixed in the PR draft by this reviewer.** The old `acceptance_cases` used ordinary `json.loads` and `.get("expectedConsistent")`. A missing expected-null field was treated as an explicit null. Conflicting duplicate fields used the last value. Extra case fields were silently accepted. [The synthetic parser probe](20261022-pr-reader-parser-controls.json) records these observations. `pr-core/tools/check-owl-reader-contracts.py:138` now rejects duplicate keys at every object depth and requires the exact five case fields, including explicit null. The 45 case IDs and their expected results are unchanged. This was a parser-boundary gap, **not a demonstrated whole-gate false pass**: the real gate also compiles the Lean fixture and checks its guards and proofs.

3. **Current-main error ABI changes require new artifact evidence. Still a validation dependency.** The original artifact runner asserted `ParseError` and a two-field low-level error envelope. Current main exposes `FactoidalError` and enriches dispatch errors. The parent has reconciled the runner, while the source fixture and parser now distinguish raw producer output from dispatched output. The prior artifact pass does not test those edits. Rebuild from the final PR tree and rerun the full 20-case artifact inventory and refusal controls. Keep the original failure evidence rather than treating incompatible old adapter expectations as engine defects.

4. **Provenance is operationally bound by the workflow, not fully attested by an individual JSON report.** Source reports hash selected files before execution and explicitly exclude the transitive build closure (`check-owl-reader-contracts.py:197` and `check-owl-public-boundary.py`, `source_hashes`/`hash_scope`). They do not record a clean tree, complete dependency closure, post-run hashes or all toolchain inputs. The artifact runner hashes the supplied source report and selected package files, but does not independently prove that the package was compiled from that report's source. This is an acceptable stated limit for the draft. Do not present a copied report as evidence for another checkout. For release evidence, retain the exact source commit, workflow run, whole tarball digest and toolchain/build manifest together.

5. **The W3C catalog run has no definitive decisions in this fragment.** [The rebased catalog report](pr-owl-corpus-final.json) selected 266 cases: 246 executed, 232 unsupported, 14 supported but unknown, and 20 without the required RDF/XML serialization. It observed no wrong definitive answer because this run made no definitive answer. Its status, `complete-no-wrong-verdict-observed`, and separate counts are appropriate. This is useful coverage measurement, not a conformance pass. The smaller adversarial corpus exercises definitive contradictions; the catalog currently does not give broad decision evidence for this implementation.

## Parser controls added and executed

The new [test_owl_gate_parsers.py](../pr-core/tests/assurance/test_owl_gate_parsers.py) uses only the Python standard library. It exercises both report parsers with synthetic reports. It checks exact nonempty inventories, missing/null/extra/duplicate fields, strict Boolean types, nested response keys, dispatch error contracts, mismatched summaries, and preservation of honest failed cases. It also checks that resource/infrastructure failures cannot count as proof-mutation rejection and that missing/duplicate/unapproved axiom reports fail.

Command, from `pr-core`:

```sh
python3 -m unittest discover -s tests/assurance -p test_owl_gate_parsers.py -v
```

Before hardening, the run recorded five failing assertions. After hardening, all 20 tests passed, with zero failures or errors. The logs are [red](20261022-pr-parser-unittest-red.log) and [green](20261022-pr-parser-unittest-green.log). These are gate-tool tests, not Lean compilation, model proofs or package conformance tests. The parent will rerun the real reader gate after the parser change. Add the unittest command to CI so future parser edits cannot silently remove these checks.

## Reviewed gate behavior

- The source reader gate requires the exact 45-case inventory, checks the actual fixture exit status, audits named theorem axioms, checks independent source-model witnesses, and requires seven mutations to fail inside the relevant proof. The shared exclusion rejects heartbeat, recursion, OOM, syntax and missing-dependency failures as mutation evidence.
- The public source gate requires the exact 20-case inventory, explicit expected-null values, unique JSON keys, exact response fields, strict Boolean types, and agreement with the actual dispatch adapter. It requires the fixture to exit successfully and three real-definition mutations to fail at the selected proof boundary. Zero discovery does not pass.
- The artifact gate requires a passing source inventory, uses a separate child for each case, checks low-level and public-facade results, and rejects unrelated runtime exceptions as refusals. Nineteen cases exercise both paths. Malformed raw options text has no public options-object equivalent and is explicitly marked inapplicable only on the facade path. The six earlier refusal runner controls remain recorded in `logs/owl-artifact-refusal-controls.*`.
- [The prior source report](owl-public-boundary-unique-final.json) and [prior rebuilt artifact report](owl-public-artifact-rebuilt-final.json) passed all 20 cases for the older repair tree. The artifact runner hash and source report digest matched that evidence when inspected. They are retained as historical evidence, not relabelled as a pass for current main's error ABI.
- [The rebased reader report](pr-owl-reader-final.json) passed 45 cases and seven proof mutations before the parser-only hardening above. Its selected source hashes match the rebased semantic sources; its parser hash now differs, as expected. The older [first rebased public run](pr-owl-public-boundary-first.json) is a failure and is not the latest passing evidence reported by the parent.

## CI and release conditions

The reviewed `repair-core/.github/workflows/verify-lean4.yml:78–85` runs the reader, catalog measurement and public source checks as ordinary required steps in the job. Its `always()` upload preserves evidence; it does not turn a failed test into a successful job. The path filters include assurance tests, the relevant gate scripts and Lean sources. This workflow tests source, not an npm artifact.

The builds draft checks out one resolved core SHA in the native, Wasm and web jobs. `repair-builds/.github/workflows/build.yml:541` makes `web-gates` depend on source and engine jobs. Lines 570–600 download the source report from that same workflow run, pack and extract the package, record the whole tarball digest, and replay the inventory through that package. The npm tests remain required afterwards. `always()` evidence uploads do not bypass these tests. The web release needs the successful web-gates artifact; the npm publishing workflow independently checks the build job result.

The draft npm publish step at `repair-builds/.github/workflows/npm-publish.yml:262–315` tests the actual publish tarball, records its SHA and source commit, clears loader-affecting environment overrides, requires a nonempty entirely passing regression report, and refuses unimplemented release obligations. Existing broader failures and unsupported obligations therefore remain release blockers rather than becoming expected passes.

Before promoting the draft:

1. Run the rebased reader gate after parser hardening and the rebased public gate after all adapter edits; retain immutable reports for the final source tree.
2. Run the rebuilt package inventory and negative refusal controls with the final adapter and deadline code. Record the full package digest and exact core/build commit pair.
3. Wire the new parser unittest into both applicable CI paths. Run the dependent workflow changes against the actual core PR commit; do not infer remote enforcement from a local YAML review.
4. Verify repository branch/ruleset required checks separately. Workflow comments that call a job “required” do not establish a GitHub branch rule. This review did not verify those rules.
5. Keep the capability reduction and unresolved entailment/legacy-path failures visible in the PR and release criteria. Resolve or explicitly scope the broader release obligations before publishing; these small gates cannot discharge them.

## Handoff update

After the review snapshot, the parent supplied [the rebased public source report](pr-owl-public-final.json): 20 cases passed and all three proof mutations were rejected. This report was read and its counts checked. The parent also wired the parser unittest into the core and builds workflows. [The hardened real reader gate](pr-owl-reader-hardened.json) passed all 45 cases and rejected all seven proof mutations; this report was read and its counts checked.

The first artifact run on the rebased tree exposed a separate error-code defect: a positioned “expected object” message containing IRIREF as one alternative was classified as `term.invalid-iri` instead of `parse.syntax`. The parent reproduced it in a public error regression and is rebuilding after the fix. This change occurred after the review input snapshot. The final package result and refreshed source report remain pending at this handoff; the earlier 20-case artifact pass is not substituted for them.
