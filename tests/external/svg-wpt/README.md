# Whole WPT SVG subtree

This is an original-byte inventory and executable static reftest transport. It is
not a statement that the engine implements the inventory. The independent
38-case suite in `../svg/` remains unchanged and separately runnable.

Pinned WPT commit: `70dae60789ef6220d9b4e60c92c5b2107b4e2b93`; SVG tree:
`e719d1b7247635648362bbbe8611e713db30f3f0`. All 2,452 SVG-subtree files
(12,660,017 bytes) are present, including 1,327 SVG and 1,042 HTML files.
`source.json` records original modes, Git blob IDs, lengths and SHA-256 for
2,492 files, including discovered outside dependencies and licenses.
`git-proof.json` binds dependencies and originally absent URLs to the pinned
commit. No fixture or reference was edited.

Metadata classification reads document links, scripts, event attributes, test
harness declarations, manual flags, animation, fonts and resource requirements.
It records 601 original relations: 595 matches and 6 mismatches; 462 static and
139 dynamic. There are also 784 testharness documents, 512 manual documents,
474 support/unclassified documents, and 17 JS inputs (one generated script
test). These inventory classes are not renderer passes. All 601 rows remain in
every report, including selected diagnostics. Existing upstream dependencies
are all fetched; 150 dependency URLs were already absent at this commit.

## Run with installed tools

No download or build occurs during execution. Supply an existing built SVG lab
and optionally the native HTML producer and its source witness. The HTML CLI
accepts the original file path and `800 600`, emitting one scene artifact JSON
or an explicit unsupported error; the host does not extract SVG or layout from
the browser DOM.

```sh
python3 tests/external/svg-wpt/corpus.py --check
python3 -m unittest discover -s tests/external/svg-wpt -p 'test_*.py'
NODE=/opt/homebrew/opt/node@22/bin/node
"$NODE" tests/external/svg-wpt/run.mjs \
  --output /tmp/svg-whole-wpt-new \
  --browser '/Applications/Google Chrome.app/Contents/MacOS/Google Chrome' \
  --playwright /absolute/path/to/playwright-core/index.mjs \
  --svg-lab /absolute/path/to/labs/demos/foafnaut \
  --html-engine /absolute/path/to/web-render-native \
  --html-witness /absolute/path/to/source-witness.json \
  --controls
```

Output must be empty. `--svg-witness JSON` attaches a feature build witness;
the actual TS, JS and WASM bytes are independently frozen and hashed.
`--case svg/path.svg` or `--cases diagnostics/use-symbol.json` selects a
diagnostic while retaining explicit unavailable rows for every unselected case.
Do not describe a selected diagnostic as the full suite.

Alternatively, replace `--html-engine CLI` with `--html-lab WEB_LAB` to run the
browser-shipped Lean HTML WASM. This requires `--html-witness FILE` and freezes
the original `web-render/engine.mjs`, generated MJS/WASM, and exact witness.
Engine hashes must match the witness. The entry wrapper is copied unchanged;
the host calls its existing `compile(originalHTML,800,600)` and supplies no font
data or markup rewrite. The two HTML producer selectors are mutually exclusive.
Native executable hashes are also checked against a supplied witness when it
declares a native hash. All runtime assets and supplied witnesses are archived
with the capture. Compare native/default, WASM/default and future supplied-font
profiles separately; a runtime that exports a font API has not exercised it
through the default path.

Exit 0 requires all 601 qualified image matches. Exit 1 means incomplete
conformance, including unsupported/unavailable cases. Exit 2 means harness,
identity or control failure. `run.json` preserves individual command statuses;
`capture/report.json` separates producer states, original browser relation
availability, full image results, negative relations and fault controls.

The browser loads original files at original root paths, including `/svg/` and
`/fonts/`, with original local response headers. A prefix mount such as `/wpt/`
breaks absolute resource URLs and must not be used. Each test and reference is
captured independently in the same browser at 800x600. Static screenshots wait
for load and `document.fonts.ready`; screenshot itself flushes painting. Do not
wait on `requestAnimationFrame` for headless macOS readiness: CVDisplayLink can
stall despite a paintable document. Scripted, animated, testdriver,
reftest-wait, server-template, print and unresolved XML base contexts remain
explicitly unavailable in this static transport. HTML uses the first valid
base element. Unresolved `xml:base` reference contexts are not guessed.

SVG compiles intrinsic dimensions first, preserving such roots as 310x170.
Only exact known missing/percentage-root errors on inventoried full-viewport
roots permit the recorded 800x600 retry. No browser geometry is fed back into
the candidate. The artifact's WGSL alone renders the candidate in WebGPU; the
host pads/crops its intrinsic image on white into the original 800x600 output.

Full PNG pixels are compared with only the original upstream fuzzy ranges,
including their lower bounds. Original Chrome test/reference relation must
hold before scoring. For mismatch relations, inequality alone is reported
`negative-only`; a qualified match additionally requires exact candidate/test
image agreement. A blank wrong image therefore cannot become a useful pass
merely by differing from a reference. No new tolerance or fixture exclusion
based on engine support is permitted.

For exact accepted test baselines, unchanged replay must agree; an injected
magenta GPU shader and a modified unsampled readback pixel must be detected.
These controls are separate from the standards denominator. Images are
lossless PNG, accepted artifacts are gzip, and differences remain on failures.
Source/fixture/runtime/browser/artifact/submitted-shader hashes and capture
tool snapshots are retained. The capture refuses heavy work below 3 GiB free.
GPU sample rejection retains the original generated artifact and actual
submitted-shader hash; it remains a rejected case.

`math_controls.mjs --directory NATIVE_CONTROLS --output EMPTY_DIR` accepts the
same browser/Playwright/SVG-lab flags for separate native-artifact controls.
Its producer manifest declares original SVG inputs (when present), artifacts
and independent full expected RGBA rasters. Every declared file is hash-checked
and frozen before rendering, including the original inputs; helper hashes are
recorded. These analytic diagnostics never change the WPT denominator.

## Reconstruct the pinned snapshot

The vendored originals make execution offline. For a fresh audit, clone only
the pinned SVG subtree and the dependency paths in `source.json`, using a
filtered sparse checkout rather than a full WPT archive. Fetch the exact commit
above, set those sparse paths, and detach at that commit. GitHub's API endpoint
`repos/web-platform-tests/wpt/git/trees/e719d1b7247635648362bbbe8611e713db30f3f0?recursive=1`
must report `truncated: false`; save its JSON as the tree argument below.

```sh
python3 tests/external/svg-wpt/corpus.py \
  --snapshot /absolute/path/to/pinned-sparse-checkout \
  --tree /absolute/path/to/svg-tree.json
python3 tests/external/svg-wpt/corpus.py --check
```

The checker recomputes the complete Git SVG tree and every byte hash, then
rederives all relations, fuzzy values, requirements, baseline overlap, resource
closure and summaries. Removing a case or editing a fuzzy limit fails just as
editing an original resource does. Tests inject these metadata corruptions.

The dated measurement and environment limits are in
[`docs/20261102-svg-whole-wpt-corpus.md`](../../../docs/20261102-svg-whole-wpt-corpus.md).
The later browser-shipped HTML WASM profile and separate SVG diagnostics are in
[`docs/20261103-svg-html-wasm-corpus.md`](../../../docs/20261103-svg-html-wasm-corpus.md).
