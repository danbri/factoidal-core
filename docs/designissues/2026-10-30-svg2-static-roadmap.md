# SVG 2 secure static rendering: coverage and image-comparison roadmap

This is a planning record prepared before the release. The owner has now
resumed SVG work. No SVG compiler, fixture, runner, or packaging source changed
for the measurements recorded in this audit.

## Target and denominator

The target is [SVG 2 secure static mode](https://www.w3.org/TR/SVG2/conform.html#secure-static-mode):
scripts, animation, interaction, and external resource fetching are disabled.
Same-document and data-URL references remain allowed. Disabled animations must
not apply, which differs from pausing an animation at time zero. This mode
does not remove static CSS, paths, text, paint servers, filters, clipping,
images, or permitted resource references from the implementation goal.

The [current upstream corpus](../../tests/external/svg/README.md) is a small
inventory, not a denominator for all modern SVG. At WPT commit
[`70dae60789ef6220d9b4e60c92c5b2107b4e2b93`](https://github.com/web-platform-tests/wpt/tree/70dae60789ef6220d9b4e60c92c5b2107b4e2b93/svg),
it includes every direct-child standalone SVG `rel=match` test in
`svg/shapes/reftests` and `svg/painting/reftests`: **38 tests**, comprising
6 shape and 32 painting cases. There are **75 pinned files**: 73 SVG documents
including references/support, plus the license and SVG README. The adjacent
54 HTML documents remain inventoried separately, including eight with scripts.
They are not silently counted as supported by the SVG-file CLI.

Keep all 38 original cases and every original input byte. Broader coverage
needs an expanded, separately pinned inventory across the WPT SVG tree and
the SVG 2 static feature requirements. Do not substitute a hand-selected
passing subset for the existing score or call 38 matches full SVG coverage.

## Measured compiler boundary

An acceptance-only audit of the current packaged Darwin ARM64 CLI returned
**0 accepted, 0 rejected, 38 unsupported, 0 matches, 0 mismatches, 0 unavailable**.
Executable SHA-256:
`c08286d975ad284066f3ce9281c1f81d1b2408415d22b0fb10c988f51e2f943f`.
The inspected `SVG.lean` SHA-256 was
`5bf3634a86cf0aef16f23560179dae89752f22eb917754948ffe60abe1ea484b`.
This reproduces the first-error distribution in the checked-in
[earlier baseline](../../tests/external/svg/baseline-2026-10-30.json):

| First reported limitation | Cases |
| --- | ---: |
| Root dimension `100%` rejected by the number/unit reader | 21 |
| Foreign-namespace `link` rejected | 14 |
| SVG `metadata` rejected | 1 |
| Root `class` rejected | 1 |
| Foreign-namespace `meta` rejected | 1 |
| Total | 38 |

These are first blockers, not mutually exclusive feature requirements.
All 38 test documents contain a metadata `link`; passing that node does not
make their graphics supported. A source inventory of the 38 test documents
found `style` attributes in 24, `style` elements in 7, transforms in 10,
paths in 18, `defs` in 22, markers in 19, `use` in 11, text in 4, gradients
in 2, patterns in 2, and a mask in 1. These categories overlap. Seven cases
have nonzero upstream fuzzy limits; the other 31 require exact comparison.

Relevant implementation boundaries are the
[attribute/style reader](../../labs/demos/foafnaut/SVG.lean#L120),
[element reader](../../labs/demos/foafnaut/SVG.lean#L216),
[root viewport reader](../../labs/demos/foafnaut/SVG.lean#L288), and
[binary-coverage shader](../../labs/demos/foafnaut/SVG.lean#L428).
The current implementation has no edge antialiasing and rejects unsupported
content explicitly. Its sparse Lean CPU samples check CPU/GPU agreement;
they are not an upstream visual oracle.

## Processing-mode mismatch in the original cases

Nine selected cases have explicit runtime/resource requirements:

- `pathlength-004b.svg` runs script after a frame to set `pathLength`, then
  completes `reftest-wait`. Secure static rendering must not run that script.
- `gradient-external-reference.svg`, `marker-external-reference.svg`, and
  `pattern-external-reference.svg` expect a fetched support paint resource.
  Secure static rendering instead takes the resource-failure path. For
  example, the gradient case has red/orange fallback paints but its original
  reference is green.
- `pathlength-003.svg`, `markers-orient-001.svg`, `paint-context-001.svg`,
  `paint-context-002.svg`, and `paint-order-001.svg` declare the unvendored
  external `FreeSans.woff`. Font loading/failure and fallback metrics matter.

The remaining 29 cases have no `requiredRuntime` entries in the current
manifest. That is an inventory result, not proof that their complete semantics
are implemented. The original 38-case score must remain intact. Add a separate
mode-aware result track with explicit provenance and reasons for incompatible
original relations. Do not fetch disabled resources or run setup scripts merely
to report a secure-static pass. Do not rewrite tests to remove those features.
For each mode-sensitive case, retain the original WPT outcome and separately
test its required secure-static behavior against an independent oracle.

## Comparison harness: retain and extend

The [existing runner](../../tests/external/svg/suite.py#L108) already compares
every RGB pixel of actual 800×600 P6 test/reference images and checks both
inclusive fuzzy ranges. It keeps unsupported/unavailable cases visible and
does not turn artifact acceptance into a visual match. Fixture hashes and
the selected `rel=match` inventory are checked before execution.

Its current limits are material:

- Both images come from the candidate renderer, so shared errors can pass.
- There is no independent reference-PNG provider, browser/font provenance,
  PNG decoder, mode declaration, or mode-conditioned reference track.
- Temporary actual/reference images are deleted; no persisted pixel-difference
  image or visual triage artifact is emitted.
- `requiredRuntime` is an unconditional original-runtime gate. It is not an
  implementation of secure-static resource failure or script suppression.
- `--width 800 --height 600` currently replaces the root dimensions used for
  viewBox mapping. Distinguish the screenshot canvas from SVG root sizing,
  percentages, intrinsic dimensions, and nested viewports before trusting
  cross-renderer screenshots. Verify this against browser captures, not an
  assumed interpretation of the CLI flag.
- The manifest represents the current single-match slice. Expansion needs
  full WPT multiple-reference, mismatch, resource and wait semantics. WPT
  requires at least one match and all mismatch relations where both exist.

After release, add an independent PNG artifact job. Use an installed/pinned
browser or a CI-provisioned independent renderer; do not download a browser
or a second renderer as part of the native renderer's normal build. Record
WPT/source hashes, browser/renderer build, OS, fonts, viewport, device scale,
white backdrop and color policy beside every PNG. Store generated images in
build/release artifacts, not as unlabelled source fixtures.

For the first 29 cases, capture both the unchanged upstream test and its
reference independently with 800×600 CSS pixels and device scale 1, and verify
the original relation there. Capture candidate output through the actual GPU
CLI and compare the complete image against the independent reference. Also
retain candidate-versus-independent-test differences for diagnosis. An oracle
disagreement is a triage result, not permission to select the easier browser.
Use a second engine to investigate disputed reference images where practical.

Apply precisely the upstream fuzzy maximum-channel and differing-pixel ranges
as documented by [WPT](https://web-platform-tests.org/writing-tests/reftests.html#fuzzy-matching).
Do not add local tolerances, crop borders, shift pixels, or call successful
compilation a match. Save actual, independent expected, difference image,
measured metrics, permitted ranges, GPU/device facts and executable hash for
each result. Missing oracle/GPU/resource output stays unavailable.

Browser image embedding normally has secure-animated behavior, not necessarily
secure-static behavior. Disabling scripts or freezing playback alone is not
a general static-mode oracle. The first 29 cases contain no animation/script
setup in the selected documents; still record the capture conditions. Broader
coverage needs a documented static-mode oracle and controls proving that
time-zero animations are not applied, forbidden fetches fail, and same-document
and data-URL resources still work. HTML wrappers or direct SVG navigation must
not silently change the sizing contract or processing mode.

## Small implementation slices after release

Each slice must add semantic tests in Lean, keep unsupported cases visible,
and end with actual upstream full-image comparisons. The targets below are
dependency candidates, not predicted passing counts.

1. **Document semantics and paint fallback.** Preserve metadata in the XML
   tree while excluding it from rendering. Handle foreign metadata and HTML
   metadata according to [SVG structure](https://www.w3.org/TR/SVG2/struct.html#ForeignNamespaces),
   rather than stripping input or treating all foreign content as graphics.
   Implement missing paint-server resolution and optional fallback paint.
   The smallest useful targets are unchanged `fallback-001.svg` and
   `fallback-002.svg` and their simple green reference. Metadata alone unlocks
   no demonstrated visual pass.
2. **Viewport, CSS and reference semantics.** Separate raster canvas/root
   viewport sizes; resolve percentages against the correct axes/normalized
   diagonal. Implement presentation attributes, inline declarations and the
   needed stylesheet selectors/cascade with normal invalid-declaration recovery.
   Add affine transform stacks and same-document `defs`/`use` resolution,
   including nested SVG viewports and cycle handling. `paint-context-003.svg`
   is a useful small reference-instancing target once context paint and
   `currentColor` retain their proper context. Do not resolve inherited paint
   too early.
3. **Stroke metrics before broad marker work.** Implement joins/caps, dashed
   strokes, `pathLength` scaling and percentage stroke dimensions in Lean.
   Targets include `pathlength-001.svg`, `pathlength-002.svg`,
   `pathlength-004a.svg`, and the two percentage-stroke tests. The disabled
   shapes case also needs CSS geometry, `calc()`, missing/auto dimensions,
   and per-element invalid-value behavior; rejecting the entire document on
   a negative geometry value cannot satisfy it.
4. **Paths, transforms and markers.** Build a typed path/segment representation
   with relative/absolute commands, smooth controls, elliptical arcs, closepath,
   lengths and tangents. Drive fill/stroke coverage and marker placement from
   it. Start comparisons at `marker-path-001/002/003`, then degenerate vertices,
   marker units/orientation, non-scaling stroke and the remaining marker cases.
   A few line commands are not a complete path implementation.
5. **Compositing, paint servers and text.** Add `use` context paint, paint-order,
   gradients/patterns, clipping/masking/filter surfaces and correct group
   opacity. Text requires real glyph outlines, font selection/metrics, shaping
   and text-path placement; the UI's bitmap alphabet is not SVG text. Data URLs
   and same-document references remain required even when external fetch is
   disabled. Add edge coverage/antialiasing and validate premultiplied alpha
   and color conversion against the independent images.
6. **Expand the inventory.** Add unchanged, pinned static tests across SVG/CSS
   categories and a feature-to-case matrix, including currently absent filters,
   clipping, images/data URLs, units, nested viewports, text and error handling.
   Keep the original 38-case results alongside the expanded score. Report
   secure-static applicability and missing implementation separately, with
   no quiet denominator reduction.

The release work and native UI are unchanged by this record. No independent
PNGs, GPU comparisons, new official passes, or broader conformance results
were produced in this planning lane.
