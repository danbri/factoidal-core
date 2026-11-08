# Fonts

Open-licence fonts that the Foafnaut browser engine reads. The Lean code reads,
shapes and draws them; no font library runs.

| Directory | Font | Version | Licence | Source |
|---|---|---|---|---|
| `noto-sans/` | Noto Sans Regular, unhinted | 2.015 | SIL OFL 1.1 (`OFL.txt`) | https://github.com/notofonts/notofonts.github.io/tree/main/fonts/NotoSans/unhinted/ttf |
| `noto-sans-armenian/` | Noto Sans Armenian Regular, unhinted | 2.008 | SIL OFL 1.1 (`OFL.txt`) | https://github.com/notofonts/notofonts.github.io/tree/main/fonts/NotoSansArmenian/unhinted/ttf (commit 1aaeb679c581) |
| `noto-sans-georgian/`, `-ethiopic/`, `-hebrew/`, `-arabic/`, `-devanagari/`, `-bengali/`, `-tamil/`, `-thai/`, `-math/` | Noto Sans Georgian, Ethiopic, Hebrew, Arabic, Devanagari, Bengali, Tamil, Thai and Math Regular, unhinted, unchanged | as published at the commit | SIL OFL 1.1 (`OFL.txt` of each script repository) | https://github.com/notofonts/notofonts.github.io/tree/86ce02c0fe7890f5936c5dffb26fca0797d1be64/fonts |
| `noto-sans-cjk/` | Slices of Noto Sans CJK JP, SC and KR Regular (SubsetOTF), cut with fontTools pyftsubset | 2.004 (SC, JP, KR SubsetOTF) | SIL OFL 1.1 (`OFL.txt`) | https://github.com/notofonts/noto-cjk/tree/f8d157532fbfaeda587e826d4cd5b21a49186f7c/Sans/SubsetOTF |
| `noto-emoji/` | Noto Emoji, monochrome outlines, instanced at weight 400 and subset with fontTools | 3.002 (`NotoEmoji[wght].ttf`) | SIL OFL 1.1 (`OFL.txt` of the google/fonts family) | https://github.com/google/fonts/tree/8b0a1d0f5983c89bc2b93f1b5fb55f9e252744b5/ofl/notoemoji |

`NotoSans-Regular.ttf` SHA-256:
`f3961a9cde016d41a4879aecda1474d3a36d6bf54fa0e4643de029cc2248b0e8`.

`NotoSansArmenian-Regular.ttf` SHA-256:
`73bde9f3c63aa5ed39236e8a2837224605210a98b54d65724676c0119fcaa24c`.
It is the first fallback font: the engine draws Armenian with it, after Noto Sans,
which has no Armenian. The fallback tests in `labs/demos/foafnaut` use it.

The files are not changed. OFL 1.1 lets us copy and bundle them with software
if the licence stays with them, and it does not let us sell a font on its own.

## Fallback fonts on the Hub

`labs/demos/foafnaut/fallback_fonts.py` fetches the files above at the pinned commits,
cuts the CJK slices and writes `docs/web/hub/foafnaut/fallback-fonts.mjs`, the table of
fonts after Noto Sans with the characters each adds. The Hub worker fetches a font only
for a page with one of those characters (`font-coverage.mjs`), so a page of Latin text
fetches none of them. The sizes and SHA-256 of every file are in that table, and
`labs/demos/foafnaut/fallback_fonts_test.ts` checks them.

The CJK slices, in the order the engine holds them:

| File | Characters | Bytes |
|---|---|---|
| `NotoSansJP-Kana.otf` | kana, CJK punctuation, full-width forms | 179,008 |
| `NotoSansJP-HanCommon.otf` | Han of JIS X 0208 level 1 and GB 2312 level 1 that the JP font has | 922,096 |
| `NotoSansSC-HanCommon.otf` | the rest of GB 2312 Han, from the SC font | 515,064 |
| `NotoSansKR-Hangul.otf` | the 2,350 Hangul syllables of KS X 1001, and jamo | 437,424 |
| `NotoSansJP-HanMore.otf` | the rest of the JP font's Han | 2,378,516 |
| `NotoSansSC-HanMore.otf` | the SC font's Han that the JP font lacks | 3,253,764 |
| `NotoSansKR-HangulMore.otf` | the other Hangul syllables | 917,184 |

A page of Japanese or Chinese usually needs the kana slice and one or two common Han
slices (1.1 to 1.6 MB); the larger slices come only for a rarer character, whose
blocks send the worker to `noto-sans-cjk/coverage.json` first. Han characters take
the JP font's forms where it has them, Chinese text included.

## Emoji

`noto-emoji/NotoEmoji-Regular.ttf` (863,016 bytes, SHA-256
`7856a372a8de8a7fccb27dee654a237b7438a16df7354adfb394d4fb14931a97`) is made by
`fallback_fonts.py` from `NotoEmoji[wght].ttf` of google/fonts at commit 8b0a1d0f5983
(Noto Emoji 3.002, 1,982,596 bytes, SHA-256
`de6c18832938afc99caf132b39d6a30a19bac7f2e812e28db2535b4608d27551`, OFL 1.1). The
source is a variable font (weight 300 to 700) whose `gvar` deltas are about half of
it; the engine reads no variations, so the script instances it at the default weight,
400 (fontTools `varLib.instancer`), and subsets it with the options of the CJK slices.
All 1,489 characters stay, and so do the `ccmp` ligatures that make one glyph of a ZWJ
sequence, a skin tone sequence (drawn as its base: the font has one form), a flag, a
subdivision tag sequence and a keycap. It is the last fallback font: symbols that
Noto Sans or Noto Sans Math has keep their text forms unless U+FE0F follows them.

Why this font: OFL, outlines in `glyf` that the Lean reader draws as it draws any
glyph, GSUB lookups of types the Lean shaper has (1, 2, 4, 5, 6), 0.86 MB. The colour
emoji fonts were checked and left out for now: Noto Color Emoji is OFL but its glyphs
are CBDT bitmaps or COLRv1 paint graphs (gradients, transforms, composites), which the
engine does not read; Twemoji's graphics are CC BY 4.0, which the owner decides case by
case; OpenMoji is CC BY-SA 4.0, a share-alike licence.

### Towards colour

The engine draws glyph outlines with one fill. A colour emoji font of the simplest kind,
COLR version 0 with CPAL, is a list of layers for each base glyph: each layer is an
outline glyph of the same font and a palette index. That maps onto what the engine has:

1. `SfntColr` (Lean): read `COLR` v0 (base glyph records, sorted by glyph id; layer
   records) and `CPAL` (palette 0, BGRA), with the bounds checks of the other table
   readers. Index 0xFFFF is the text colour.
2. `SfntProfile.Font.word`: for a glyph with a base record, give the layers in order,
   each as `SfntOutline.outline` of its glyph with a fill colour, instead of one outline.
   `FontProvider.Glyph` gains an optional colour per geometry; layout is unchanged,
   since a colour glyph has the advance of its base glyph.
3. `WebRender`: draw a glyph's layers in order, each in its colour, through the same
   vector fill pipeline as SVG paths (the hand-drawn faces on the emoji page are drawn
   that way today).

A test font for this can be made with fontTools from outlines of Noto Emoji (OFL), so
nothing with another licence is needed. The open question is the font for the Hub:
no OFL or CC0 COLRv0 emoji font as broad as Noto Emoji was found. COLRv1, which Noto
Color Emoji uses, needs gradients, affine transforms and composite modes in the scene
as well, and is the larger step.
