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

Previous full artifact-backed result (2026-10-31): **2 match, 23 unsupported, 13 unavailable, zero mismatch
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


## Newer source diagnostics (2026-11-01)

The full artifact-backed result above predates the current Lean source changes.
Four individual source-exported GPU comparisons now match their independent
browser images exactly: fallback-001, fallback-002, percentage and
percentage-attribute. These are targeted diagnostics, not a new full-suite or
published-binary score. See [dash and coverage evidence](../../../docs/20261101-svg-dashed-strokes.md).

Positive `pathLength` calibration for rectangle/line dashes is also checked in
source. Its official pathlength-001 input now compiles, but the current 2×2 GPU
sampler differs from the independent browser image at 1,512 edge pixels.
[Coverage diagnostics](../../../docs/20261101-svg-coverage-diagnostics.md)
compare sample grids against both browser pixels and exact area of the decoded
scene. No tolerance was changed. [Shared linear stroking](../../../docs/20261101-svg-linear-strokes.md) now
admits its original path reference too: the test/reference GPU images match
exactly within Solving. This single source-artifact pair is separate from the
independent browser mismatch and the last complete artifact-backed run.

Source export via `SVGArtifact.lean` and `browser_gpu.mjs --artifact FILE
--fixture INPUT.svg` permits diagnosis without a full WASM rebuild. That route
is labelled local: the supplied artifact is not independently certified by the
runner as having been generated from the fixture or this checkout. Record the
export command, checked source, input hash, artifact hash and comparison scope.
It must not silently replace the normal WASM-producer path or its 38-case score.

## Browser sensitivity controls and provenance, 2026-11-02

The rebuilt and corrected browser run retains all 38 inputs: **4 match,
2 mismatch, 1 rejected, 18 unsupported, 13 unavailable**. Both fallback and
percentage pairs match exactly. The two pathlength cases each differ at 1,512
pixels (maximum channel difference 64); the negative-rectangle case remains
rejected. Each sensitivity control separately reports 4 pass, 0 fail and
34 unavailable. The viewer smoke with required retained-tree data also passes.
The [worknote](../../../docs/20261102-svg-browser-harness.md) records exact
artifact hashes, the runtime failure found and repaired, and the viewport
transport error found and corrected. This is not full SVG conformance.

Run capture, actual GPU rendering, comparison and sensitivity controls in one
command, using installed tools only and a new output directory:

```sh
node tests/external/svg/run_browser.mjs --output /tmp/svg-browser-run \
  --browser /path/to/installed/chrome \
  --playwright /path/to/playwright-core/index.mjs
```

`--python /path/to/python3` and `--typescript /path/to/typescript.js` are optional.
The default uses the current Node executable, its TypeScript stripping, and
`python3` on PATH. `run.json` separates image results from each command's exit
status and records exact arguments. Exit 0 requires the complete 38-image match;
exit 1 reports incomplete conformance, which is expected for the current slice.
Exit 2 means a harness failure or a failed/unavailable sensitivity control on
an actually matching baseline. Unsupported cases retain unavailable controls.
The wrapper refuses nonempty output directories so stale files cannot be reused.

The candidate first asks Lean to retain the SVG's intrinsic viewport (`0,0`),
then places its pixels at the top left of the unchanged 800×600 white capture.
It does not stretch a declared SVG viewport to fill the page. For this exact
WPT pin, the complete root-dimension inventory is 22 `100%`/`100%`, 13 omitted-
both, two `310`×`170`, and one `200`×`200`. Only exact Lean errors requesting
host dimensions for the first two classes permit an 800×600 retry. This retry
is limited to the verified pinned manifest; it is not a general CSS root-sizing
implementation. Arbitrary local inputs without an intrinsic viewport remain
unavailable. Each candidate row records the policy and produced viewport.

The runner also reports a viewport regression for the two existing 310×170
percentage inputs: they must retain their declared dimensions and match the
original oracle exactly. This does not add test cases or WPT passes. The
previous forced-800×600 transport gave 48,552 differing pixels on those inputs;
the intrinsic-size GPU diagnostic gave zero. See the dated worknote for the
unchanged historical reports and the corrected full-slice measurement.

Add `--controls` to the normal `browser_gpu.mjs` command to capture three
separate diagnostics for every input the actual WASM producer accepts:

- `unchangedReplay`: a fresh GPU session with the unchanged artifact.
- `gpuFlatMagenta`: a real GPU render with a changed fragment shader. A bounded
  storage read preserves the required bind-group layout. Its contribution is
  below one 8-bit channel step. Lean sample checks are disabled for this
  deliberate shader fault and this fact is recorded.
- `unsampledReadbackPixel`: one changed RGB byte after GPU readback, at a pixel
  outside all Lean sample locations. The runner confirms that the original
  sample checks still pass. This tests the whole-image comparator's sensitivity.

The comparator reports these controls separately from the unchanged 38-case
score. A control can pass only when the unmodified candidate matches the
independent reference. Replay must retain identical pixels; both faults must
change pixels and fail the original upstream image relation. A rejected shader,
missing image or unmatched baseline gives an unavailable control. A fault that
escapes detection gives a failed control. These controls do not add WPT passes.

Browser candidate/oracle comparison requires the same Chrome version and
executable SHA-256. The capture freezes runtime bytes before launch and checks
that they stayed stable during the snapshot. It records source and served
hashes separately for TypeScript, all runtime artifacts, generated artifact and
shader hashes, and the current source import closure. Git HEAD, dirty status,
tracked-diff hash and harness hashes identify the measured checkout. External
Lean toolchain imports remain listed. These records identify inputs; they do
not certify that warm WASM was built from current source.

The local viewer smoke accepts `--report FILE` to retain JSON and
`--require-tree` to require the rebuilt Lean scene-tree inspector. It checks
browser-preview source bytes, the submitted GPU shader, desktop comparison
alignment, narrow-screen stacking, real manual shader faults, error cleanup,
and restoration of the original full image. It records every loaded asset hash
and whole-image browser/GPU metrics. Viewer image differences remain diagnostics,
not additional WPT results. See the
[measurement worknote](../../../docs/20261102-svg-browser-harness.md).

The subsequent shared-linear-stroke source replay admits six of all 38 inputs,
with 32 still unsupported. Targeted same-renderer GPU comparisons now match
both pathlength-001 (rectangles versus paths) and pathlength-004a (polygons
versus paths) exactly. These results retain their separate source-diagnostic
scope; the last full artifact-backed score above has not been replaced.
