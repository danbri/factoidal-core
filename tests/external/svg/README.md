# Official SVG reftests for the experimental native renderer

This is a pinned WPT corpus, not a full SVG conformance claim. It contains
all **38 standalone SVG `rel=match` reftests** directly in these categories:

- `svg/shapes/reftests`: 6 tests.
- `svg/painting/reftests`: 32 tests.

Coverage tracking: https://github.com/danbri/factoidal/issues/1209.

The pin is [WPT 70dae60789ef6220d9b4e60c92c5b2107b4e2b93](https://github.com/web-platform-tests/wpt/tree/70dae60789ef6220d9b4e60c92c5b2107b4e2b93/svg).
All 67 SVG documents directly in those directories and all four SVG files
in their support/reference subdirectories are retained, plus two reference
SVGs from adjacent categories. With the license and upstream SVG README,
there are **75 pinned files**. Test and reference documents are unchanged:
no metadata removal, style rewriting, geometry extraction, or feature filter.

`source.json` also inventories all **54 HTML documents** in these two
directories, including eight with scripts. They require a browser document
runner and are outside this SVG-file command's 38-test denominator. There
are no `-manual` files in these directory listings. One selected SVG test
uses scripts/reftest-wait; five declare web fonts. They remain in the
38-test denominator. `manifest.json` lists additional resource/runtime
requirements; these are visible unsupported results if the static command
accepts the document without supplying those requirements. The complete
WPT SVG tree, DOM APIs, browser layout, and older SVG 1.1 manual tests are
outside this slice.

## Offline source checks

From the repository root, with Python 3:

```sh
python3 tests/external/svg/suite.py --check-fixtures
python3 tests/external/svg/suite.py --inventory
python3 -m unittest discover -s tests/external/svg -p test_suite.py -v
```

The fixture check verifies SHA-256, upstream Git blob IDs, every selected
`rel=match` pair, and its reference's presence. Missing or changed files
fail with exit 2. The test dispatcher manifest runs **fixture integrity**,
not rendering conformance; it does not turn current unsupported features
into source CI failures or conformance passes. The original six local runner tests
use synthetic process/image data and are not counted as WPT tests.

The files are checked in, so CI needs no network. To restore missing or
corrupt fixtures from the exact pin:

```sh
python3 tests/external/svg/suite.py --fetch
```

Downloads have a size limit, timeout and SHA-256 check. Network failures
are explicit failures. No archive, font package, browser or runtime is
installed by this command. See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

## Measure the renderer

Use the native executable built/published through factoidal-builds:

```sh
python3 tests/external/svg/suite.py --engine /path/to/native-webgpu-svg-darwin-arm64 --report /tmp/svg-acceptance.json
python3 tests/external/svg/suite.py --engine /path/to/native-webgpu-svg-darwin-arm64 --render --report /tmp/svg-render.json
```

Without `--render`, the command asks the real Lean SVG compiler for an
artifact. `accepted` means compiled but visually **unverified**; it is never
an image match. With `--render`, test and upstream reference must both
produce valid 800×600 P6 RGB images. The runner compares every pixel and
honors each test's upstream `fuzzy` maximum-channel-difference and differing-
pixel ranges. No local tolerance is added. This is a same-renderer reftest,
not an independent raster oracle; shared defects can escape the comparison.
The two shapes' renderings test an upstream visual-equivalence assertion.

Each result is one of:

- `accepted`: compiler acceptance only, with no visual result.
- `rejected`: process/compiler failure without an explicit profile limitation.
- `unsupported`: an explicit profile limitation, or an unsupplied script/font/resource requirement.
- `match`: actual test/reference images satisfy the upstream relation.
- `mismatch`: actual images violate that relation.
- `unavailable`: missing engine/output, timeout, unusable image, or blocked GPU.

Counts always sum to 38. Missing fixture data fails before running, rather
than reducing the denominator. Acceptance-only and incomplete rendering
runs exit 1. Only a complete rendering run with 38 matches exits 0. This
score is not the source-CI threshold. Current unsupported cases stay visible;
the integration has no fixture exclusions or success baseline override.

## Initial measurement, 2026-10-30

The development Darwin arm64 CLI with SHA-256
`037c77d5ddd3a01611eee627b80958cb64cba06281c9303515f1559d334dba3d`
reports **0 accepted, 0 rejected, 38 unsupported, 0 matches,
0 mismatches, 0 unavailable** in acceptance-only mode. The render command
also stops at those 38 profile limitations, before requesting GPU output.
The current parser rejects reftest metadata/foreign elements and several
SVG features. No official visual pass is claimed. A separate missing-engine
control reports 38 unavailable, not zero tests. The tool environment has
no usable GPU adapter, so desktop rendering still needs a user GPU run.
The measured development executable is not included in this source tree;
released binaries are separate build artifacts.
The per-test diagnostic snapshot is in
[baseline-2026-10-30.json](baseline-2026-10-30.json); it is not a gate override.

## Independent browser reference images

`capture_reference.mjs` uses an already installed Chrome and Playwright Core;
no browser or package is downloaded. It verifies every pinned fixture first,
serves only the fixture tree on a temporary loopback port, blocks requests to
other origins and disables JavaScript. Original test/reference bytes remain
unchanged. Capture is 800×600 CSS pixels, device scale 1, with the browser's
white canvas. Cases with the manifest's script/font/resource requirements stay
unavailable. Animation-bearing inputs are also refused. This restricted capture
is not a general secure-static oracle: system fonts are not independently
enumerated and browser processing modes need further validation for more cases.

```sh
node tests/external/svg/capture_reference.mjs --output /tmp/svg-oracle \
  --browser /path/to/installed/chrome --playwright /path/to/playwright-core/index.mjs
python3 tests/external/svg/oracle.py --oracle /tmp/svg-oracle \
  --engine /path/to/native-webgpu-svg-darwin-arm64 --output /tmp/svg-comparison
python3 -m unittest discover -s tests/external/svg -p 'test*.py' -v
```

Capture records browser version/executable hash, host facts, source/image hashes,
viewport and restrictions in `oracle.json`. The comparator verifies source/image
hashes and the exact 38-case inventory. It first checks the independently
captured original test/reference relation using the unchanged upstream fuzzy
ranges. A browser disagreement remains unavailable for candidate scoring and
needs triage. It then compares candidate GPU PPM against the independent
reference, also recording candidate-versus-independent-test metrics. Actual and
difference PPMs are retained. Missing GPU, oracle or runtime output remains
unavailable; acceptance is never an image match. No local tolerance is added.

The initial installed Chrome 156.0.8078.76 capture retained all 38 cases: 29 pairs
captured, nine unavailable for original runtime/resource requirements. Of the
29 independent relations, 25 matched and four disagreed (`marker-path-022`,
`marker-path-023`, `paint-context-003`, `paint-context-006`). No candidate GPU
command was supplied, so the candidate score was **38 unavailable and zero
visual matches**. These measurements do not replace the original same-renderer
baseline or narrow its denominator. Images are external build artifacts, not
new source fixtures.

After the paint-fallback change, actual candidate CLI comparison reports 23 unsupported, 15 unavailable and zero visual matches: nine runtime/resource cases, four oracle disagreements and two GPU-adapter failures. Acceptance alone reports two accepted and 36 unsupported. These are separate tracks.


## Actual browser-host raw WebGPU comparison

The browser candidate uses the same Lean SVG/WGSL compiler, Lean render plan
and existing WebGPU/byte bridge as the native screenshot path. It never asks
the browser's SVG renderer to draw the candidate. TypeScript is transpiled by
an already installed compiler solely for this test transport; no dependency
or browser is downloaded.

```sh
node tests/external/svg/browser_gpu.mjs --output /tmp/svg-browser-gpu \
  --browser /path/to/installed/chrome --playwright /path/to/playwright-core/index.mjs \
  --typescript /path/to/typescript/lib/typescript.js
python3 tests/external/svg/oracle.py --oracle /tmp/svg-oracle \
  --candidate /tmp/svg-browser-gpu --output /tmp/svg-browser-comparison
```

Current actual result: **2 match, 23 unsupported, 13 unavailable, zero mismatch
or rejection**, all 38 retained. `fallback-001` and `fallback-002` each have zero
maximum channel difference and zero differing pixels against the independent
reference. Unavailable remains nine original runtime/resource cases plus four
independent-browser disagreements. Candidate data includes browser/executable,
actual adapter and source/WASM hashes. Hardware was Apple `metal-3`, fallback
false, Chrome156.0.8078.76, 800×600, device scale1; driver version is not exposed
by the WebGPU info API. This browser transport evidence does not repair the
native Deno adapter lookup or establish native window presentation.

For an additional local SVG regression, supply `--fixture INPUT.svg`; its report
has a separate local scope and no WPT revision, so it cannot enter the pinned
38-case score. Captures/readbacks/differences remain generated artifacts outside
source control. The full-feature goal is tracked in the
[project checklist](../../../docs/designissues/2026-10-31-svg2-static-feature-target.md).

`browser_gpu.mjs --fixture INPUT.svg --repeat 20` measures a resident session with setup and frame/readback times separated. It creates one shader module/pipeline and uploads once; each frame still reads back and validates pixels. These are host round-trip timings, not GPU-only or CPU/GPU kernel comparisons. See [measured limitations](../../../docs/20261031-svg-resident-rendering.md).
