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
into source CI failures or conformance passes. The six local runner tests
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
