# Web fonts, marks across fonts, paint-only transforms, SVG animation, bounded ink

Date: 2026-11-09. Author: showoff, a subagent of session depmap-0e.
Related: https://github.com/danbri/factoidal/issues/1268 (responsiveness), https://github.com/danbri/factoidal/issues/1233 (fonts in Lean).

## 1. CSS `@font-face` (CSS Fonts 4 §4 and §5)

- `Rendering/Style.lean`: `font-family` takes a list (`familyNames`; the computed value is
  the names joined by ", "). `fontFaceBlocks` gives the blocks of `@font-face` rules, also
  in an `@media` block that holds.
- `Rendering/FontFaceRule.lean`: the descriptors `font-family`, `src` (`url()` with
  `format()`; `local()` never matches; WOFF, WOFF 2, SVG and EOT are passed over: the
  engine has no decoder for them), `font-weight`, `font-style`, `unicode-range`; the
  matching of §5.2 (style, then weight, then the last defined face whose range holds the
  character); `usedFaces`, the faces that rendered text uses (HTML text by its computed
  family, SVG text by its own `font-family`).
- `WebDocument`: op `fontFaces` answers the used faces with their URLs in order. The
  host fetches each from the page's own origin (8 MiB a face, 16 MiB a page) and gives the
  bytes with `fontLoad` mode 2 (`web_document_font_load_bin`, `fallback` 2). Lean reads the
  file with the font policy (`SfntProfile.Font.read`) and holds it by SHA-256, apart from
  the fallback list, at most 16. A render names its faces in `webFonts` (`[{url,sha256}]`,
  a layout field). A face that does not come, or that the policy refuses, is not used: its
  text falls back to the next family.
- HTML text: `Layout.FontProfile.familyWord` shapes a word of an element whose family
  names a web font with that face first, in the primary font's units and metrics
  (`SfntProfile.wordWith`). SVG text: the held web fonts go to the SVG text reader with
  their CSS family, which puts the named one first.
- Pages with no `@font-face` pay one substring search of their sheets; the host makes no
  call for them.
- `document.fonts` (prelude, `node_query` op 20): the faces of the page with their status
  (`loaded` when held for this page). The host loads the used faces before the scripts
  start, so `ready` is resolved. `load(font, text)` and `check(font, text)` match the
  families of a font shorthand. No `FontFace` constructor.

The demonstration font is Fruktur (OFL; `third_party/fonts/fruktur/PROVENANCE.md`): it
has every letter of "Spın̈al Tap" and "Foafnaut", U+0131, U+0308 and GPOS mark anchors
for U+0308 on n and ı.

## 2. A combining mark of one font on a base of another

- `SfntProfile.runsOf`: a base followed by a combining mark takes the first font that has
  both, when one does (as browsers fall back by cluster).
- Otherwise `SfntProfile.wordWith` places the mark run on the last base glyph of the run
  before it with HarfBuzz's fallback rule (`SfntFallback.positionMark`): the base's
  advance box across, its ink above and below, a gap of 1/16 em; the mark takes no
  advance.
- `Rendering/SfntMarkTheorems.lean`: `positionMark_inside` (a mark no wider than its base
  lies in the base's box across) and `positionMark_centre` (any mark: the centres agree to
  one unit).

## 3. Paint-only transforms and SVG animation (`WebPaint`)

- A script's `setAttribute('transform')` on an SVG `g`, `text`, shape or `image` is a slot:
  the layout key keeps that the attribute was set, not its value (`WebPaint.slotKey`); the
  layout is made with the identity there and keeps a plan of the slots. Each frame puts the
  values on the kept scene (`WebPaint.patch`): the group of a `g` or `text` (by id; one
  with none gets an id no page can write, in the layout's copy only), or the primitive of
  a shape. An element named by an `href` or `url(#)` of the page, or under `defs`,
  `symbol`, `clipPath` and such, is not a slot: its change is laid out as before.
- SVG animation, in Lean on the page clock: `Rendering/Smil.lean` (clock values, begin
  lists with offsets and clicks, phases, active duration, the animation function over
  numbers, `animateTransform` matrices) and `WebPaint.state`. `animateTransform` (any
  type) of a paintable element and `animate` of `opacity` of a shape run; others are
  logged and show their base value. Animation elements are comments in the layout's copy
  of the arena. The host sends `animationTime` (ms since the page's first frame) and
  `animationClicks`; the layers answer says `animating` (draw the next frame) and
  `animations` (send the clicks).
- Theorems: `Smil.phase_before`, `phase_active_lt`, `phase_after_end`;
  `FrameCost.paint_never_layouts` and `run_paints_never_layout` (a paint-only change costs
  no layout from a warm session). The engine counts painted frames (`frameWork.paintOnly`);
  `showoff_test.ts` checks that 40 transform frames and 125 animation frames lay out 0
  times, and that a painted frame equals the page with that transform written in it.
- Text stays vectors at every scale: glyphs are outline paths; the backend flattens them
  in screen space. `WebPaint.cull` turns curves whose control points are all off the
  band into lines (the same pixels: the region between a curve and its chord lies in the
  hull of its points), so a group at scale 40 does not cost its unseen ink.

## 4. Ink bounds for hostile text ("Zalgo")

- Security: `FrameCost.composite_chrome` (a chrome row of the window comes from the chrome
  layer only, whatever the page draws) and `WebShell.compose_page_clipped` (in one frame,
  every page primitive carries the page's part of the window as a clip).
- `overflow: hidden` and `clip` clip the content to the padding box, not the border box;
  the box's background and border are not clipped (`Layout.clipContent`,
  `ClipTheorems.clipContent_clips`, `lower_clipped`).
- `Rendering/InkBound.lean`: the Stream-Safe Text Format of UAX #15 §13 (a CGJ before the
  31st non-starter; `streamSafe_bounded`, `streamSafe_erase`), used by `Font.word` before
  shaping; each glyph's ink is kept in its cluster's advance box and line widened by
  `clusterBound` = 31 em (`place_inside`; ink already inside is not moved, `place_keep`);
  `unionAll_contains`: the union of ink boxes contains each one.
- Not proved: that the backend's clip rows encode `ClipRect.contains` exactly
  (`labs/demos/foafnaut/SVG.lean`), and the same bounds in `Float` pixels (no order lemmas
  for `Float`); the pixel tests check them.

## 5. Measurements (2026-11-09, Apple silicon laptop, native library)

- `zoom_bench.ts` (a group with "Spın̈al Tap" in Fruktur, 80 px, scale 1 → 40 → 1 over
  120 frames, engine time per frame): a script's `setAttribute('transform')`: before p50
  11 to 18 ms, p95 14 to 24 ms, max 15 to 27 ms, 117 layouts; after p50 2.5, p95 3.3,
  max 6.0 ms, 0 layouts, 120 paint-only frames. `<animateTransform>`: before, the page
  was refused ("unsupported attribute on animateTransform"); after p50 2.5, p95 3.3,
  max 3.4 ms, 0 layouts.
- Scene data at scale 1, 40 and 200: 5,228, 2,284 and 2,680 floats (`WebPaint.cull`).
- Timers and clicks (scripted transforms of 12 circles): engine time per frame p50 13.4
  → 12.2 ms. Layout is gone from these frames; the band compile of the whole page is what
  is left. A compile of only the primitives that changed (damage rectangles from the ink
  bounds of section 4) is the next step.
- Hostile text: the Zalgo fixture draws; 10,000 marks on one base shape in linear time.
