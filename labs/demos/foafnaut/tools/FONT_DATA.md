# Native font data adapter

This adapter supplies font data to the Lean rendering work tracked at
https://github.com/danbri/factoidal/issues/1230 . HarfBuzz shapes one run;
FreeType supplies outlines and grayscale glyph coverage. Lean remains
responsible for DOM, CSS, line breaking, paragraph bidi, layout and scene
construction. The adapter is not an HTML renderer or a complete text engine.

Build and exercise installed libraries and a font you have permission to use:

```sh
bash labs/demos/foafnaut/build-font-adapter.sh
labs/demos/foafnaut/.build/font-shape /path/to/font.ttf 'office' 20
FACTOIDAL_TEST_FONT=/path/to/font.ttf python3 labs/demos/foafnaut/tools/test-font-adapter.py
```

The test defaults to the local macOS Arial font. No system font is copied or
distributed. `pkg-config` must find HarfBuzz and FreeType; non-macOS builds
also use OpenSSL for SHA-256. macOS uses CommonCrypto. No package downloads
or global configuration changes occur in the build script.

The CLI takes `FONT_FILE UTF8_TEXT INTEGER_PIXEL_SIZE [FACE_INDEX]`.
Success is exit0 with one `factoidal-font-data-v1` JSON object. A caller
must check the exit status and discard stdout on any error. Diagnostics
go to stderr; consumers must not treat partial output as valid font data.

- `fontSha256` hashes the exact memory blob shared by HarfBuzz and FreeType.
  Identity includes `faceIndex`; family/style names are descriptive only.
- `unitsPerEm`, `ascender`, `descender`, `lineGap`, glyph advances, offsets
  and outline coordinates are integer font units with positive y upward.
  Lean performs scaling to CSS coordinates and baseline placement.
- `glyphs` retain HarfBuzz visual order, glyph IDs, advances, offsets and
  clusters as UTF-8 byte offsets. Clusters may repeat and RTL clusters may
  descend. They are not character indexes or a one-glyph-per-character map.
  Default HarfBuzz grapheme cluster merging and OpenType features apply;
  guessed direction/script/language and library versions are recorded.
- `outlines` contain one entry per distinct used glyph ID. Commands are
  `M x y`, `L x y`, `Q cx cy x y`, `C c1x c1y c2x c2y x y`, and `Z`.
  Each contour closes explicitly, preserving order and direction. Outline
  loading disables scaling, hinting and embedded bitmaps.
- `bitmaps` contain the same glyph IDs at `bitmapPixelSize`, with integer
  `left`/`top` bearings, row-major `width*height` coverage bytes `alpha` in
  0..255. FreeType normal grayscale rasterization disables hinting and
  embedded bitmaps. Coverage is font raster data, not a browser screenshot
  and not evidence of CoreText raster equivalence.

One run is not paragraph itemization. Font fallback, line breaking,
variation selection, CSS font matching, variable-font axes, color fonts,
vertical-text policy and fractional pixel raster sizes remain outside this
adapter. Missing characters may produce glyph0; the Lean consumer must
resolve fallback or report that limitation. Do not call the supplied data
complete font support until it is actually consumed into rendered scenes.

Resource refusals are explicit: UTF-8 input at most65,536 bytes; scalable
font blob at most128MiB; pixel sizes1..512; face indexes0..65,535; at most
65,536 shaped glyphs,1,048,576 distinct outline points and16,777,216 bitmap
pixels. The adapter does not change existing scene storage limits.

The seven adapter tests compare actual shaped IDs/advances/offsets/clusters
with the separate `hb-shape` CLI for Latin, Greek, Arabic, combining text
and ZWJ. Other checks cover exact font identity, empty runs, RTL byte
clusters, closed curved contours, true grayscale coverage and size changes,
and invalid input. These are adapter checks, not WPT or text conformance.

The Lean consumer is `L4Factoidal.Rendering.FontData`. It uses the existing
Factoidal JSON parser and rejects ambiguous duplicate fields, invalid integer
coordinates, broken contour structure, missing/duplicate glyph resources,
invalid grayscale coverage and mismatched bitmap sizes. It checks clusters
against the actual UTF-8 scalar boundaries and preserves visual glyph order.
Decoded glyphs carry source character start/end spans; repeated clusters and
RTL runs are retained. Default decoding refuses missing glyph0, with an
explicit policy option for a caller implementing fallback. The font identity
is a checked SHA-256 string supplied by the native producer; this decoder
does not independently reopen/hash the font or prove HarfBuzz correctness.

From `formal/lean4`:

```sh
LEAN_NUM_THREADS=2 lake build L4Factoidal.Rendering.FontDataTests
LEAN_NUM_THREADS=2 lake env lean --run ../../labs/demos/foafnaut/tools/check-font-data.lean /path/to/font-data.json
```

There are37 compiled protocol guards, including malformed-data mutations,
UTF-8 boundaries, merged source clusters, RTL order and missing-glyph policy.
The runtime driver additionally checks actual local HB/FT data through Lean.
This is data transport validation; RTL paragraph layout and font rendering
remain separate integration work. The decoder's JSON transport bound is16MiB.

The v1 outline data has an implicit nonzero fill rule. The native producer
refuses `FT_OUTLINE_EVEN_ODD_FILL` before writing JSON. An instrumented test build
loads an actual font through FreeType and sets that flag to exercise the refusal;
it is not evidence that the tested font requires even-odd filling. A future
schema may transport the rule for direct admission into the shared scene.
