# Typed shaped words into common font geometry

Tracking: https://github.com/danbri/factoidal/issues/1230 .

`Rendering.FontProvider` consumes the checked `FontData.ShapedWord` transport.
It retains actual glyph IDs, advances, offsets, font metrics, font identity
and source cluster spans. A ligature remains one glyph spanning multiple
source characters; a mark can have a zero advance and a positioned offset.
Font points are converted from font-unit positive-y-up coordinates into the
common scene's metric-top, positive-y-down convention. Closed M/L/Z outlines
become actual shared path geometry. Quadratic/cubic outlines are explicitly
refused pending the checked canonical curve compiler; they are not replaced
by chords or bitmap glyphs. Horizontal LTR is the initial direction scope.

Seventeen targeted guards passed for metrics, glyph identity and positioning,
ligature spans, actual common path coordinates, and named curve/direction/
missing-resource/invalid-cluster refusals. The test module is reachable from
the central Lean build root. Only its targeted import closure was built.

An actual-font runtime probe used pinned upstream Ahem bytes, SHA-256
`b719ecb31c5b21fc573c03f6421c74ac63c271a5a3ff841e34f9705fb94b8448`.
The existing native HarfBuzz/FreeType adapter shaped `fi A` at 20 pixels.
The Lean decoder/provider retained glyph IDs `[72,75,3,35]`, a 4,000-font-unit
advance and three nonempty glyph outlines. Those actual outlines produced
three common-scene paint items. CPU samples checked all three black glyph
boxes and the empty space between them. The emitted existing-backend artifact
is `/tmp/factoidal-web-ahem-provider-artifact.json`; source font-data and probe
logs are `/tmp/factoidal-web-ahem-font-data.json` and
`/tmp/factoidal-web-ahem-provider-probe.log`. This is font-data consumption,
not an authored Ahem substitute.
The reproducible Lean driver is
`labs/demos/foafnaut/FontProviderAhemProbe.lean FONT_DATA_JSON OUTPUT_ARTIFACT_JSON`
under `lean --run`, with the fresh lab and project oleans on `LEAN_PATH`.

This independent module is deliberately not yet imported by the frozen HTML
engine. The HTML profile still uses and labels its ASCII bitmap font, and
continues refusing Ahem. The next integration replaces per-character width
arithmetic with a typed word-shaping lookup in line breaking, consumes these
actual glyph geometries at the shared baseline, and exposes a bounded font-
data transport. Font family selection must require supplied matching font
identity rather than silently mapping names to the bitmap profile. The shared
canonical curve adapter will then admit Q/C font outlines without changing
host layout responsibilities. Real default fonts, UA paragraph metrics,
margin collapse, bidi, fallback and full shaping conformance remain open.

## Exact face lookup, 2026-11-03

`Rendering.FontFace` adds a bounded single-face dictionary keyed by the exact
word text and supplied pixel size. It checks consistent font SHA, family,
face index, style and metrics across runs, and rejects differing outline
commands for the same glyph identity. Missing text/size data is an error,
without character substitution or a width estimate. The transport is a
bounded JSON array of unchanged native font-data-v1 records. Budgets apply
across all words, not just individually decoded runs.

The provider now retains pixel size. Eighteen provider guards and fourteen
face guards pass, including size mismatch, inconsistent resource identity,
duplicate text/size, missing data and schema failures. The actual pinned Ahem
probe also passes through the face decoder and exact `fi A`, 20px lookup.
These modules remain outside the frozen HTML engine's import closure until
the coordinated word-shaping callback integration.
