# HTML, SVG, text and portable rendering

Owner questions: how close is the lab to a Tiny 1.1-sized static SVG 2
subset; can the HTML parser drive it; can non-WebGPU devices reuse the Lean
code and theorems? Graphics tracking:
<https://github.com/danbri/factoidal/issues/1209>.

## Current boundary

The SVG input parser supports a restricted set of rectangles, circles,
ellipses, lines and polygons, inherited paint, and root viewBox mapping.
Paths, transforms, CSS, reuse, images and general text are missing. The
FOAFNaut scene is constructed directly in Lean, so its visible capabilities
do not measure the SVG input language. Its temporary font emits geometry;
this is not SVG text support. The exact restrictions are in
[SVG_README.md](../../labs/demos/foafnaut/SVG_README.md).

[SVG Tiny 1.1](https://www.w3.org/TR/2003/REC-SVGMobile-20030114/) includes
paths, transformations, images, text and reuse, as well as nonstatic
features. A Tiny-inspired static SVG 2 subset needs an explicit feature
matrix; it is not itself a W3C conformance profile. SVG 2 secure static mode
also retains the full static graphics feature set: disabling script and
animation does not remove paths, text, CSS, filters or paint servers.

The lab contains 38 pinned WPT SVG reftests. The recorded acceptance audit
has 38 unsupported and no visual matches. Metadata/percentage dimensions
are often the first refusal, with deeper missing features behind them.
The local gallery is not an official suite result. See the
[unchanged upstream corpus and baseline](../../tests/external/svg/README.md).
Same-renderer test/reference comparisons can share defects. Independent
browser reference images, font/version provenance, retained outputs and
pixel difference images remain needed.

## Proposed shared pipeline

1. Lean HTML or XML parsing builds the document representation.
2. Lean style resolution and layout produce boxes and positioned graphics.
3. Font services return shaped glyphs and their geometry.
4. Lean constructs the authoritative scene, hit targets and policy footprints.
5. The shared admission controller approves the scene under an application
   configuration. A renderer consumes that approved scene.

The HTML tokenizer/tree builder is merged in
<https://github.com/danbri/factoidal-core/pull/269>. It is not yet connected
to the graphics frontend. A parser alone supplies neither CSS layout nor
a complete browser DOM, event system or scripting engine.

[HarfBuzz](https://harfbuzz.github.io/what-harfbuzz-doesnt-do.html) shapes
individual text runs. Font fallback, bidirectional processing, line
breaking and paragraph layout still need implementations.
[FreeType](https://freetype.org/) can supply outlines or glyph bitmaps.
Layout decisions and drawing commands should stay in Lean; the font
services have explicit external contracts, not assumed Lean proofs.

The same positioned glyph extents must feed painting, hit testing and
policy footprints. A font, scale or layout change invalidates prior
approval. A browser backend must not silently substitute different font
metrics. Outlines can preserve geometry when browser shaping cannot be
bound to the same inputs/results, at a separate accessibility/selection
cost that needs explicit treatment.

## Backends and theorem scope

The scene/policy layer is independent of WebGPU. Planned consumers include
generated SVG, WebGPU, and a Lean CPU rasterizer with a thin pixel-transfer
adapter. Existing Lean CPU sampling functions are reference semantics,
not yet an optimized tiled software renderer.

A Linux Raspberry Pi CPU backend is a useful first portability experiment.
An ESP32 port first needs a measured runtime and memory feasibility study
for the selected board/display. Lean-generated C still uses Lean runtime
services; the current Deno/WASM desktop executable is not an embedded
firmware image. Tiling or strip buffers can bound image memory. Espressif's
[esp_lcd](https://docs.espressif.com/projects/esp-idf/en/stable/esp32/api-reference/peripherals/lcd/index.html)
can transfer the produced pixels without owning layout or policy.

Scene-level geometry and admission theorems can be reused across backends.
Each backend still needs a contract for transforms, clipping, glyph
extents, numeric rounding and rasterization. A theorem about the scene
does not establish driver correctness or equality of displayed pixels.
The current overlap metric uses viewport-clipped node bounding boxes and
sums pairwise intersections; it is not a painted-ink area ratio.

The experimental 3–7 percent / 12–24 Hz graph-browser profile is not a
universal embedded-device policy. Other profiles need explicit bounded
parameters and corresponding assumptions. A slow device must not silently
weaken an application's assurance. A requested checking cadence does not
prove host scheduling or frame completion deadlines.

The next backend experiment should preserve these boundaries while making
an actual CPU image, comparing it with independent SVG references, and
measuring memory/time before promising an embedded target.
