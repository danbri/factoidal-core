# SVG independent images and paint fallback

Tracking: <https://github.com/danbri/factoidal/issues/1209>.
The existing 38-case WPT denominator is unchanged. It is six standalone
shape and 32 painting reftests, not SVG Tiny or the whole SVG specification.
Secure-static mode restricts capabilities; it does not select a feature profile.

## Independent image track

The new `tests/external/svg/capture_reference.mjs` uses already installed
Chrome/Playwright, serves the unchanged pinned tree on loopback, blocks external
requests, disables script, and records browser/source/image hashes and capture
conditions. Animation-bearing or explicitly resource/runtime-dependent cases
remain unavailable. System fonts are not independently enumerated. This is a
restricted independent browser track, not a general secure-static oracle.

Chrome 156.0.8078.76 captured 29 unchanged test/reference pairs at 800×600 CSS
pixels and device scale 1; nine cases retained their original runtime/resource
limitations. Twenty-five independent relations match upstream fuzzy ranges.
Four disagree and remain triage results:

| Case | Maximum channel difference | Different pixels |
| --- | ---: | ---: |
| marker-path-022 | 255 | 480 |
| marker-path-023 | 255 | 2412 |
| paint-context-003 | 1 | 334 |
| paint-context-006 | 1 | 66 |

`oracle.py` verifies pinned source/image hashes and capture settings, decodes
bounded PNG RGB/RGBA rasters including all five filters, and compares complete
candidate images using precisely the upstream fuzzy ranges. It retains actual
and difference images, logs and candidate executable hash. Candidate results
are unavailable if the independent relation disagrees. No new tolerance,
cropping, shifting or fixture rewriting is used. Its ten Python tests include
the six original runner tests and four decoder/comparison/boundary tests.

## Lean prerequisite slice

The actual XML namespace tree now treats SVG metadata as non-rendering and
recognizes XHTML `link rel=match` as metadata. Stylesheet links and other HTML
relations remain unsupported. Unresolved simple local paint fragments select
specified color/none fallback, or no paint without a fallback. `currentColor`
remains symbolic through inheritance. Existing target IDs, external URLs,
percent-encoded/escaped/non-simple fragment syntax remain explicit refusals;
this does not implement paint servers. Identifier collection uses an iterative
worklist, with the existing bounded nesting/input policy after XML parsing.

The original missing-URL rejection regression is replaced by correct no-paint
semantics plus refusal tests for existing/unsupported targets. The unchanged
upstream `fallback-001.svg` and `fallback-002.svg` compile and produce expected
known green/white CPU samples. Full acceptance audit through the actual source
CLI: **2 accepted, 36 unsupported, zero rejected, zero visual matches**.

After targeted cached SVG C/WASM relinking, 65 Deno tests and 12 C coordinate
checks pass, with all entrypoints/tests typechecked. The named Lean prerequisite
test passes and is included in the warm engine build. No full runtime/engine
build or executable/package/release was made. The two known cached runtime
`lean_io_create_tempfile/tempdir` linker warnings remain unchanged.

A reference lookup scaling probe compiled 2,048/4,096/8,192 distinct-ID shapes
in 395/738/1,557 milliseconds (134,127/269,295/539,631 characters) on this host.
These are measured bounded probes, not a complexity theorem.

Actual independent candidate comparison attempted the GPU CLI: **23 unsupported,
15 unavailable, zero matches/mismatches**. The 15 consist of nine runtime/resource
cases, four independent-oracle disagreements, and the two newly accepted cases
whose adapter lookup returned unavailable. Their CLI explicitly reported no
image written. Images/reports remain in `/private/tmp/foafnaut-svg-oracle`; they
are generated artifacts, not committed fixtures. Desktop GPU comparison remains
required. Paths/transforms, styling, viewports and the broader static feature
checklist remain implementation work.
