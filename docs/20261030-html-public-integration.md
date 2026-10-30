# HTML parser integration with current main

This integration combines
https://github.com/danbri/factoidal-core/pull/269 (HTML tokenizer and tree builder),
head `2ee929c8b1d788a5d38ac1d3dc61dec2950df637`, with main
`a9bd50c3b28b3d42c5071cc8c3e74a5ede8706db` without changing release versions.
The implementation retains the parser changes and adds public API regressions.

## Merge and public regression coverage

There were no production Lean conflicts. The workflow merged automatically;
append conflicts in the worknote index and recursion allowlist retain both
sides. A line-set check confirms that every original line of both conflicting
inputs is retained. The merged workflow parses and retains both the HTML
corpus step and the QT4 resource-base step. The original HTML runner and
expected-failure file are unchanged.

The HTML corpus measures parser arenas and tokens. Its results do not alone
establish the XPath XDM mapping or public npm/CLI behavior. The official QT4
parse-html set has 22 cases and no processing-instruction case.

`npm/factoidal/test/qt4-public.test.mjs` now checks:

- Processing instruction type, target name and data after fn:parse-html,
  through the public XPath/XQuery APIs, dataflow node and CLI helper.
- SVG element namespace and template content through those public adapters.
- The FODC0011 error code and namespace when fail-on-error is true.
- The actual CLI subprocess PI result on the default fresh-WASM test path.

The PI regression was run before the integration using a temporary copy with
imports redirected to the existing package. Two selected groups gave one
pass and one failure: the PI count was zero instead of one; the namespace,
template and error controls passed. The refreshed native driver gives 11
public test groups pass, zero fail and zero skipped. CLI success retains
`ok: true`; the API unwraps that transport field, which the test handles
explicitly while comparing the complete remaining result.

## Validation

Named warm builds passed: `L4Factoidal.XPath4.Html`,
`L4Factoidal.HTML.XmlAgreement`, `l4html5lib`, `l4wasm-cli` and `l4qt4`.
One existing PR warning is String.trim deprecation in Harness.Html5lib.
No full Lake or local WASM build was run. Cache growth was approximately
10.5 MiB, below the 120 MiB budget.

With the existing corpus commands and a 1024 KiB process stack:

- Tree construction: 1963 pass, zero fail (out of 1963), ten expected failures,
  zero defective exclusions, zero stale entries.
- Tokenizer: 7043 pass, zero fail (out of 7043), three expected failures,
  three defective exclusions, zero stale entries; four lone-surrogate cases
  not run. Tokens and error-code counts remain separately reported.
- XHTML/HTML comparison: 5000 agree, zero disagree; no generated document
  rejected by either admission condition. This is a measurement, not the
  whole-tree agreement theorem.
- QT4 fn-parse-html: 22 pass, zero fail, zero unsupported (out of 22) in
  XPath and separately in XQuery mode.
- Public API/node/CLI helper tests using the fresh native dispatch driver:
  11 pass, zero fail, zero skipped.
- Node syntax, conflict-marker/whitespace checks and merged YAML checks pass.

The corpus limitations retain their existing issue links in
`tests/html5lib/expected-failures.txt` and
`docs/designissues/2026-10-29-html-parser.md`. No fixture, exclusion, score or
recursion classification was changed during integration.

A runner invocation with `--help` unexpectedly ran the default XPath corpus
because unknown flags are ignored. It completed with 29430 pass, 51 fail,
9193 unsupported and five defective exclusions (out of 38674), including
Format.parseIetf panic diagnostics. There is no matching current-main baseline
for that unplanned run; it is not evidence of a regression or a passing gate.
Subsequent scoped invocations used flags checked in the runner source.

Evidence is under `/private/tmp/html269-public-regressions/`: html-build.log,
native-dispatch-build.log, qt4-build.log, tree.log, tokenizer.log,
agreement.log, native-red.log, native-green.log and the two scoped QT4 logs.
Fresh-WASM npm tests, including the actual operational CLI PI subprocess,
and the refreshed exact-head package/core CI gates remain required. The local
native test mode does not claim those different backend checks passed.
