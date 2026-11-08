# Fonts

Open-licence fonts that the Foafnaut browser engine reads. The Lean code reads,
shapes and draws them; no font library runs.

| Directory | Font | Version | Licence | Source |
|---|---|---|---|---|
| `noto-sans/` | Noto Sans Regular, unhinted | 2.015 | SIL OFL 1.1 (`OFL.txt`) | https://github.com/notofonts/notofonts.github.io/tree/main/fonts/NotoSans/unhinted/ttf |
| `noto-sans-armenian/` | Noto Sans Armenian Regular, unhinted | 2.008 | SIL OFL 1.1 (`OFL.txt`) | https://github.com/notofonts/notofonts.github.io/tree/main/fonts/NotoSansArmenian/unhinted/ttf (commit 1aaeb679c581) |
| `noto-sans-georgian/`, `-ethiopic/`, `-hebrew/`, `-arabic/`, `-devanagari/`, `-bengali/`, `-tamil/`, `-thai/`, `-math/` | Noto Sans Georgian, Ethiopic, Hebrew, Arabic, Devanagari, Bengali, Tamil, Thai and Math Regular, unhinted, unchanged | as published at the commit | SIL OFL 1.1 (`OFL.txt` of each script repository) | https://github.com/notofonts/notofonts.github.io/tree/86ce02c0fe7890f5936c5dffb26fca0797d1be64/fonts |
| `noto-sans-cjk/` | Slices of Noto Sans CJK JP, SC and KR Regular (SubsetOTF), cut with fontTools pyftsubset | 2.004 (SC, JP, KR SubsetOTF) | SIL OFL 1.1 (`OFL.txt`) | https://github.com/notofonts/noto-cjk/tree/f8d157532fbfaeda587e826d4cd5b21a49186f7c/Sans/SubsetOTF |

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
