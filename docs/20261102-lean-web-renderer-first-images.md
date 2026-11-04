# First HTML/CSS → Lean WASM → WebGPU images

Tracking: https://github.com/danbri/factoidal/issues/1230 (shared Lean web
renderer). Architecture and admitted scope:
[design record](designissues/2026-11-02-lean-web-rendering.md).

The working demo now accepts original HTML and CSS. Existing Lean HTML
parsing and DOM construction feed Lean cascade, block/inline layout and the
common Float retained geometry. The explicit SVG adapter feeds the existing
Lean WGSL backend. The browser executes the new HTML/DOM/layout WASM closure
and the existing raw WebGPU transport. The candidate does not use browser DOM
layout or an HTML-to-SVG string conversion.

The default document contains a CSS-sized padded main box, two font sizes,
colored inline text, word wrapping and embedded SVG rectangles. It produces
1,579 paint items and 28 source-mapped glyph runs. Editing source, CSS or
viewport inputs recompiles and changes actual GPU pixels. The font is still
the explicitly labeled ASCII bitmap profile; real-font shaping is not
claimed complete.

## Actual checks

`web-render/check-browser.mjs` completed with exit 0 at 2026-11-02 23:07 UTC
on Chrome 156.0.8078.80. Its five named checks passed:

- The default original HTML/CSS ran through the actual Lean WASM and browser
  WebGPU path, with visible nonempty text and embedded SVG output.
- The full 96 by 80 box/percentage/padding/embedded-SVG image matched the CPU
  reference exactly and matched independently rendered original HTML in Chrome:
  0 different pixels out of 7,680, maximum channel difference 0.
- Changing CSS color or content width changed whole GPU image hashes.
- Changing text changed glyph paint; changing width changed source-mapped
  glyph positions and the GPU image.
- An unsupported Ahem font request refused output.

These are local profile checks, not additional WPT passes. The independent
Chrome reference receives the original HTML fixture unchanged. Source files
and engine hashes are recorded by the local source witness and browser report.
The full CPU/WASM box artifact also compared equal before browser rendering.

The box fixture SHA-256 is
`3889db336fe5854ad0e0b481e26e1726f4e1b985393d4d9a8c98b91794a6fcca`.
Its GPU RGBA SHA-256 is
`cd6cc9e3dfac4326576b6cc16272d598d9b4cc3be7c960e31a8718c0969a7b41`.
The CPU RGB SHA-256 is
`cd50bbf9020f9ae05617b563b1f5f94b4df2124f24fea28058c307c798067ca9`.
The native executable SHA-256 is
`0e5e98e05e456ba5f5f3bda5884d6437d2c38e79f46db58add5d2b9dbf69944b`.
Full local evidence: `/tmp/factoidal-web-first-gpu-20261102/report.json` and
`/tmp/factoidal-web-first-gpu-20261102/viewer.png`.

## Build and assurance limits

Only the targeted HTML/DOM/CSS/layout/vector-rendering import closure was
compiled. All C and engine artifacts are ignored local products. The existing
Lean 4.33.1 runtime/standard-library WASM cache was reused read only after the
version and string-list patch witness checks. A first link attempt failed
because Emscripten tried to write its global Homebrew cache. A separate pinned
50 MiB tool cache in the owned build directory fixed the link; only the fresh
objects were relinked. The two known unused runtime temp-file/temp-directory
signature warnings remain, as in the existing lab build.

Core source verification passed 16 guards. Lossless Float SVG geometry, style,
primitive and complete retained-scene roundtrips are checked by Lean. Common
retained lowering has checked reverse-accumulator twins. These structural
proofs do not prove Float32 raster equivalence, host upload, WGSL execution or
driver behavior.

A separate native scaling run measured 1,000, 2,000 and 4,000 painted block
children, three repeats each: minimum whole-artifact wall times 0.376, 0.810
and 2.102 seconds; peak RSS at most 11.7, 13.6 and 18.7 MB. The fourfold-size
time ratio was 5.58. No linear-performance or speedup claim follows. The
accumulator and parser costs need separate profiling. Evidence:
`/tmp/factoidal-web-scaling.json`. RSS came from per-child `wait4`; macOS
`time -l` was unavailable under the process sandbox.

The central build root now imports `Rendering.Tests`. The unbuilt-module
gate still reports three pre-existing unrelated modules, and is not reported
as passing. SVG clipping, broader HTML/CSS, real shaped fonts, Unicode/bidi,
selection, scripting, incremental invalidation and performance improvements
remain work. The independent native
[HarfBuzz/FreeType font-data adapter](../labs/demos/foafnaut/tools/FONT_DATA.md)
is available for the next typed Lean integration; it does not perform layout.
