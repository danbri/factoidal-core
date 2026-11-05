# Browser WPT baseline and native provenance

3 November 2026. The owner requested credible WPT measurement within 30
minutes, followed by cleanup of disposable Lean/Lake caches. This side
conversation started the pass at 12:17 UTC. It added local test runners,
ran them against existing artifacts, and removed only checked old build
caches. It did not implement or publish a browser release.

## Measured results

The [machine-readable baseline](../tests/browser-wpt/baseline-20261103.json)
records exact artifact/report hashes. Full output is in
`/private/tmp/factoidal-wpt-20261103-1217/`. Reproduction instructions are
in [tests/browser-wpt](../tests/browser-wpt/README.md).

| Evaluated path | Original scope | Fresh result |
| --- | --- | --- |
| Lean HTML tree construction | 62 WPT `.dat` files, 1,973 cases | 1,963 pass; 10 fail |
| Lean HTML through DOM arena | The same 1,973 cases through `DOM.ofTreeBuilder` | 1,963 pass; 10 fail |
| Lean tokenizer | 14 html5lib files | 7,043 pass; 6 fail; 4 surrogate-input cases not run |
| QuickJS and production guest DOM | All 784 script-test documents in the pinned SVG subtree | 0 complete passing documents; 103 passing and 1,342 failing assertions |
| Native HTML/embedded-SVG CPU pixels | All 279 HTML reference relations in the SVG inventory | 2 pass; 1 fail; 175 unsupported; 97 unavailable; 4 timeouts |
| Additional original DOM/CSSOM View documents | 3 DOM documents and 2 layout-query documents | 4 script errors; 1 failing assertion document; no passes |

These denominators must not be added into a single browser conformance
score. Direct parser and DOM rows intentionally exercise the same fixtures.
The parser reports another distinct result: document parse-error counts
agree in 1,321 cases and differ in 446. Passing tree shape does not erase
that discrepancy. Tokenizer total is 7,053 including the four not-run
cases; 7,049 were executed. No expected-failure or exclusion file was used.

The final QuickJS document classification is 367 ERROR, 136 FAIL,
27 INCOMPLETE, 229 UNAVAILABLE, 23 HARNESS_ERROR and 2 UNSUPPORTED.
The 23 harness errors comprise failed setup/no-test completion and one
unavailable `invalid:` dependency. The shell transport cannot run the
whole browser event loop. Its 103 passing assertions are not 103 fully
passing WPT documents. An earlier intermediate report did not capture
harness completion; use `quickjs-final/quickjs-wpt.json` as authoritative.

The native exact image matches are:

- `svg/linking/reftests/href-use-element.html`
- `svg/render/reftests/overflow-clip.html`

`svg/coordinate-systems/viewBox-fractional-valid.html` differs in 628 pixels
with maximum channel difference 56. Four operations exceeded five seconds:
`use-descendant-combinator-001.html`, `use-nested-symbol-001.html`,
`negative-dashoffset-odd-dasharray.html`, and `visibility-collapse-001.html`.
Timeouts are retained, not retried until they disappear from the score.
Common admission blockers include images, borders, background images,
external stylesheets and CSS rules targeting embedded SVG descendants.

The extra documents are the original `dom/nodes/Node-textContent.html`,
`Document-getElementById.html`, `Node-contains.html`, and
`css/cssom-view/cssom-getBoundingClientRect-001.html` and
`cssom-getClientRects.html`. They were fetched at the same WPT pin, with
`dom/common.js` supplied unchanged. The layout-query tests encounter
missing APIs; the `getClientRects` assertion fails. Their separate report
is `extra-quickjs-final/quickjs-wpt.json`; their fetched bytes and manifest
are under `extra-upstream/` in the result directory.

## Provenance and the existing-engine question

The candidate render process was the ARM64 Mach-O CLI
`labs/demos/foafnaut/.build/web-render/web-render-native`, SHA-256
`ee90a9317456104a6104f9219cfe536774fad9aa6888f94cfa18e6a1e7e3c7de`.
Its source witness identifies renderer commit
`63a73ff4af77abb41ca9d423171da1ecd635be33`. Host checkout was
`b578816b0f31ac1f34d75a0a052d19262e9c6a8c`.

The audit checked 125 current source/generated-C files against that witness,
checked the native digest, and confirmed the witness identifies a binary
produced after the recorded generated C. `otool -L` lists C++ and system
libraries. A fresh original WPT input produced 480,000 pixels with
`DYLD_PRINT_LIBRARIES=1` and `PATH=/nonexistent`; its loader log contains no
WebKit, JavaScriptCore, Blink, Chromium, Gecko or Firefox marker. The full
log and pixel-output hash are in `provenance/native-provenance.json`.

No browser was launched to generate the candidate images. Original Chrome
images from the earlier pinned capture were reused as independent expected
results, with source, inventory and image hashes verified. That is an
oracle comparison, not rendering delegated to Chrome. It also means this
is not a fresh full GPU/WPT run. The existing capture harness's 3 GiB
free-space guard was preserved; the laptop had about 1.4 GiB free, and a
fresh Chrome launch in this environment failed with permission/SIGABRT
errors. Neither blocker was converted into a pass.

QuickJS-NG is deliberately reused as a separate WASM JavaScript engine.
Its reactor hash is
`8afa5d73287af5573613e15d5e633e91d8e096b40676f424f104087bc1416678`.
The WPT harness and page assertions execute there, with actual production
guest bindings and Lean-native document snapshots. Node supplies transport
and the WebAssembly host. QuickJS is not claimed to be Lean-verified.
The existing ten QuickJS session/watchdog/validation tests also passed.

This is source/artifact and runtime evidence, not an independent native
rebuild or formal machine-code proof. The parser probes use recorded cached
Lean production modules plus freshly compiled harness modules; their
results must not be described as a fresh native parser rebuild.

## Fixture integrity and failure sensitivity

- Full SVG fixture integrity passed: 2,492 original files; 601 reference
  relations. Standalone SVG/XML accounts for the 322 relations outside the
  new HTML runner. The old full-corpus scores are not fresh results here.
- SVG/script WPT pin: `70dae60789ef6220d9b4e60c92c5b2107b4e2b93`.
- Parser WPT pin: `ce5ca39646886a9349fc42913f843ec6e1c8a36f`.
- html5lib tokenizer pin: `c777c408b61078ea2eb4acefc2535f54dbc8b28a`.
- The 62 parser and 14 tokenizer file bytes were checked against Git blob
  IDs fetched from those upstream revisions. The repeatable parser runner
  now enforces that exact complete inventory before running.
- Both exact native image passes reject a one-pixel corruption. QuickJS
  correctly distinguishes a passing assertion from an intentional failure.
- Wrong native digest, wrong upstream harness digest and a truncated
  oracle inventory were each rejected in separate negative controls.

## Cache cleanup

Removed 171 generated `.olean`, object and associated hash/cache files:
154 from `source/factoidal-foafnaut/labs/demos/foafnaut/.build/{olean,obj}`
and 17 from its `foaf/.build/olean` subdirectory. Total: 91,678,378 logical
bytes, about 87.4 MiB. That checkout's HEAD
`bf0565d3702b7996f3cf895d6e05792733803b25` was confirmed an ancestor of its
`origin/main` at `7204a8776556dd02d260bb9debee714a360609f6`. Files were
untracked, older than twelve hours, and checked for changes before removal.
The manifests and hashes are in `cache-cleanup.json` and
`cache-cleanup-foaf.json` in the result directory.

The separate 2.1 GiB Lean cache under `/Users/danbri/working/factoidal-core`
was written during this run and was left intact. Current engine bundles,
native binaries, source, official corpora, runtime caches and reports were
preserved. There is no disk-usage baseline proving what consumed the
20 GiB the owner freed yesterday; do not attribute that growth to a guessed
directory.

At 12:36–12:37 UTC, free space had fallen to about 203 MiB despite this
cleanup. `/System/Volumes/VM` used 9.5 GiB: `swapfile10` was 1 GiB with a
12:32 modification time and `swapfile11` was 256 MiB with a 12:36 time.
Those new swap allocations account for roughly the recent 1.25 GiB drop,
not the entire unexplained 20 GiB since yesterday. The main Lean cache
remained about 2.1 GiB; this pass's complete report directory used about
14 MiB. System-managed swap was not deleted. Memory pressure, including
potential contributions from test execution, is distinct from output-file
growth; per-process attribution was unavailable. All test processes
started by this pass had finished before handoff.

## Next implementation work

Use these results as the baseline for the main thread. First repair the
[same-turn guest DOM defect](https://github.com/danbri/factoidal/issues/1232)
and define layout-query behavior, then extend the WPT adapter with the
actual browser event loop and document-loading contract. Keep synchronous
shell probes visibly separate from full Window tests. Add fresh GPU image
results when disk and browser-launch access permit, preserving the complete
601-relation denominator and upstream expected results. No CI or release
gate was added in this timed side pass.
