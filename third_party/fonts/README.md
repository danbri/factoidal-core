# Fonts

Open-licence fonts that the Foafnaut browser engine reads. The Lean code reads,
shapes and draws them; no font library runs.

| Directory | Font | Version | Licence | Source |
|---|---|---|---|---|
| `noto-sans/` | Noto Sans Regular, unhinted | 2.015 | SIL OFL 1.1 (`OFL.txt`) | https://github.com/notofonts/notofonts.github.io/tree/main/fonts/NotoSans/unhinted/ttf |
| `noto-sans-armenian/` | Noto Sans Armenian Regular, unhinted | 2.008 | SIL OFL 1.1 (`OFL.txt`) | https://github.com/notofonts/notofonts.github.io/tree/main/fonts/NotoSansArmenian/unhinted/ttf (commit 1aaeb679c581) |
| `noto-sans-georgian/`, `-ethiopic/`, `-hebrew/`, `-arabic/`, `-devanagari/`, `-bengali/`, `-tamil/`, `-thai/`, `-math/` | Noto Sans Georgian, Ethiopic, Hebrew, Arabic, Devanagari, Bengali, Tamil, Thai and Math Regular, unhinted, unchanged | as published at the commit | SIL OFL 1.1 (`OFL.txt` of each script repository) | https://github.com/notofonts/notofonts.github.io/tree/86ce02c0fe7890f5936c5dffb26fca0797d1be64/fonts |
| `noto-sans-cjk/` | Slices of Noto Sans CJK JP, SC and KR Regular (SubsetOTF), cut with fontTools pyftsubset | 2.004 (SC, JP, KR SubsetOTF) | SIL OFL 1.1 (`OFL.txt`) | https://github.com/notofonts/noto-cjk/tree/f8d157532fbfaeda587e826d4cd5b21a49186f7c/Sans/SubsetOTF |
| `fruktur/` | Fruktur Regular, a blackletter display font: an asset of the web font demonstration, not a fallback font (`PROVENANCE.md`) | 1.008 | SIL OFL 1.1 (`OFL.txt`) | https://github.com/google/fonts/tree/a60a77e14f28abd4ef243a1b5dfc48df0cec5205/ofl/fruktur |
| `noto-color-emoji/` | Slices of Noto Color Emoji (the COLRv1 build of googlefonts/noto-emoji, `Noto-COLRv1.ttf`), its SVG table and vertical metrics dropped, cut with fontTools pyftsubset | as published at the commit (`NotoColorEmoji-Regular.ttf`, 25,332,736 bytes, SHA-256 `4d82a18d8d95f60ba883ce242bbadbf84a576e987745dd7ba38d71c67cff2d73`) | SIL OFL 1.1 (`OFL.txt` of the google/fonts family) | https://github.com/google/fonts/tree/c08cd288696d8ca30bf0296dc214d80d33a65d8f/ofl/notocoloremoji |
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
subdivision tag sequence and a keycap. It is the last fallback font, and since colour
(below) it draws text presentation: an emoji with U+FE0E, or a symbol whose default is text
when no colour slice is held.

Why Noto Color Emoji for colour: OFL, glyphs in COLR version 1 that the engine now draws,
GSUB lookups of the types the Lean shaper has (1, 2, 4, 5, 6). Twemoji's graphics are CC BY
4.0, which the owner decides case by case; OpenMoji is CC BY-SA 4.0, a share-alike licence.
The bitmap forms (CBDT, sbix) are not read.

### Colour (issue 1276)

`noto-color-emoji/` holds Noto Color Emoji in 17 slices, 5.6 MB in all, made by
`fallback_fonts.py --colour-only` from `NotoColorEmoji-Regular.ttf` of google/fonts at
commit c08cd288696d (the COLRv1 build of googlefonts/noto-emoji, OFL 1.1). Of its 25.3 MB,
20.3 MB is an `SVG ` table, which the engine does not read (the font policy has no SVG glyph
implementation), and 0.25 MB vertical metrics; without them the font is 4.97 MB: `glyf`
3.46 MB, `COLR` 1.09 MB, `CPAL` 26 KB (one palette of 6,394 colours), `GSUB` 31 KB (`ccmp`
ligatures of the sequences).

The engine reads `COLR` (versions 0 and 1) and `CPAL` and draws the colour glyphs itself
(`formal/lean4/L4Factoidal/Rendering/SfntColr.lean`, `ColrRaster.lean`). Noto Color Emoji
uses layers, solid colours, linear and radial gradients (pad only), affine transforms,
translations and scales, glyph clips, and composites in two modes (SRC_IN 313 times,
SOFT_LIGHT 262 times, mostly the shading of flags); no sweep gradient and no variations. A
paint graph is at most 10 deep and 6,665 nodes.

The slices follow the groups of Unicode's `emoji-test.txt` (UTS #51 version 18.0,
`third_party/unicode-18.0.0/emoji-test.txt`). Each slice holds the glyphs of its sequences
and only their ligatures (HarfBuzz, through uharfbuzz, gives the glyph of each sequence;
pyftsubset runs with no layout closure), and the script checks that every sequence shapes to
one glyph of its slice. People are cut three ways and flags by the first letter of their
regional indicator pair, so a page with one smiley fetches 156 KB and a page with one flag
about 350 KB:

| Slice | What | Bytes |
|---|---|---|
| `NotoColorEmoji-Smileys.ttf` | Smileys & Emotion | 155,784 |
| `NotoColorEmoji-People.ttf` | single people, hands and body parts, with their skin tones; the components | 583,572 |
| `NotoColorEmoji-PeopleZWJ.ttf` | ZWJ sequences of people (families, professions, couples), no skin tone | 555,456 |
| `NotoColorEmoji-PeopleZWJTones.ttf` | the same with skin tones | 845,744 |
| `NotoColorEmoji-Animals.ttf` | Animals & Nature | 384,444 |
| `NotoColorEmoji-Food.ttf` | Food & Drink | 245,996 |
| `NotoColorEmoji-Travel.ttf` | Travel & Places | 364,600 |
| `NotoColorEmoji-Activities.ttf` | Activities | 147,368 |
| `NotoColorEmoji-Objects.ttf` | Objects | 378,024 |
| `NotoColorEmoji-Symbols.ttf` | Symbols, keycaps | 101,752 |
| `NotoColorEmoji-Flags.ttf` | the other flags: chequered, white, black, tag sequences (England, Scotland, Wales), rainbow, pirate | 30,484 |
| `NotoColorEmoji-FlagsAB.ttf` ... `FlagsTZ.ttf` | flags of regional indicator pairs from A-B, C-E, F-K, L-P, Q-S and T-Z | 279,504 to 366,528 each |

The Hub's table (`fallback-fonts.mjs`) gives each slice the characters that send a page to
it: `adds` (an emoji, or a symbol that no text font has), `vs16` (a symbol that a text font
has, when U+FE0F follows it), `needs` (the ZWJ slices also need U+200D, and skin tones for the
last), `regional` (the first letters of a flag slice's pairs). Noto Emoji comes after the
slices and is fetched only for U+FE0E, text presentation.

A smaller choice of slices is the owner's to make: the People slices could be one (1.24 MB),
and flags fewer and larger.
