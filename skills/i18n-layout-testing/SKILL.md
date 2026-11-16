---
name: i18n-layout-testing
description: How to test Foafnaut's text layout and rendering for languages and scripts the people reviewing it cannot read (Arabic, Hebrew, Devanagari, Bengali, Tamil, Thai, CJK, Mongolian, emoji sequences, mixed scripts). Machine checks against independent references come first: the Unicode conformance files, the WPT css-text, css-writing-modes, css-fonts and i18n directories and their reftests, HarfBuzz shaping differentials, and glyph-position and pixel comparison with Chrome and Firefox. Where those suites are too coarse, we write small original test pages of our own, one script and one feature each, with stored reference renderings and recorded licences. Covers what exists in the tree, how to add a case, how cases are run and how results are reported. Use before changing shaping, bidi, line breaking, fonts, font fallback, writing modes or text painting, before claiming a script "works", and when adding test text or fonts.
---

# Testing text in scripts we cannot read

A reviewer who cannot read Thai cannot tell a correct Thai line break from a wrong one, and a reviewer who
cannot read Arabic cannot tell joined letters from isolated ones at a glance. So correctness for these scripts
is decided by machines against independent references, never by someone looking at a screenshot and finding it
plausible. Looking is still useful for finding gross faults (boxes, missing text, overlapping lines), and a
screenshot belongs in a hand-back, but it is not evidence that a script is right.

Two kinds of reference, used together:

- **Specifications with test data**: the Unicode algorithms (UAX #9 bidi, #14 line breaking, #29
  segmentation, #15 normalisation) ship conformance files; OpenType shaping has HarfBuzz as the reference
  implementation.
- **Other engines**: Chrome and Firefox, given the same fonts and the same page. Where they agree, we should
  agree with them. Where they differ, the case is contested: record both and accept either within tolerance.

Non-Latin layout is part of the whole, not an extra: see [`scope-and-sequencing`](../scope-and-sequencing/SKILL.md).

## 1. What exists (2026-11-16)

| Layer | Where | Checked by |
|---|---|---|
| Unicode algorithms in Lean (Unicode 18.0.0): bidi, line breaking, grapheme/word/sentence segmentation, normalisation, with theorems | `formal/lean4/L4Factoidal/Unicode/` (`Bidi.lean`, `LineBreak.lean`, `Segmentation.lean`, `Normalization.lean`, `*Theorems.lean`; data tables `BidiData`, `LineBreakData`, `SegmentData`, `JoiningData`, `ScriptData`, `ScriptDirection`, `EmojiData`); design record `docs/designissues/2026-10-29-unicode-algorithms.md` | `l4unicode` (`formal/lean4/Harness/UnicodeConformance.lean`, `tests/unicode/run.sh`) over the official test files in `third_party/testing/unicode-18.0.0` |
| Unicode data files | `third_party/unicode-18.0.0/` (`ArabicShaping.txt`, `LineBreak.txt`, `Scripts.txt`, emoji files, ...) | provenance in `PROVENANCE.md` there |
| OpenType reading and shaping in Lean | `formal/lean4/L4Factoidal/Rendering/SfntShape.lean`, `SfntArabic.lean`, `LeanFontShape.lean`, `SfntOutline.lean`, font selection and fallback in `Font*.lean` | `labs/demos/foafnaut/tools/check-lean-shaper.py`: the Lean shaper's glyph records against HarfBuzz (`tools/font-shape.c`). Its text list is Latin, Greek and Cyrillic only today: extend it per script (section 3) |
| Fonts | `third_party/fonts/` (`README.md`): Noto Sans and Noto Sans Arabic, Hebrew, Devanagari, Bengali, Tamil, Thai, Armenian, Georgian, Ethiopic, Math, CJK slices (JP, SC, KR), Noto Emoji and Noto Color Emoji slices; all SIL OFL 1.1 | `fallback_fonts_test.ts` (sizes, hashes) |
| Pixel references from an independent renderer | colour emoji: `labs/demos/foafnaut/emoji_reference.py` writes `fixtures/emoji-reference/manifest.json` (Skia via blackrenderer, HarfBuzz for the glyph); `emoji_pixels_test.ts` compares the engine's pixels | the model to copy for script cases (section 3) |
| WPT reftests | `tests/browser-wpt/native-reftests.py` (fresh native images against hash-checked cached browser oracles); a full WPT reftest runner is on branch `wip/reftests` (core PR 496) | [`wpt-runs`](../wpt-runs/SKILL.md) sections 5 and 8 |
| Real pages | the survey's `layout_similarity` (SSIM against headless Chrome) | [`realpages-survey`](../realpages-survey/SKILL.md) |

Known gaps: no Mongolian font is vendored (Noto Sans Mongolian, OFL, would be the one); no vertical writing in
SVG (`danbri/factoidal` issue 1285); Thai, Lao, Khmer and Myanmar line breaking needs a dictionary or
equivalent beyond UAX #14 (their characters are class SA, which `LineBreakTest.txt` leaves to the
implementation), so the Unicode files cannot check it and only engine comparison can.

## 2. Automated checks first

Run these before writing anything new; they are cheap and independent.

1. **Unicode conformance**: `tests/unicode/run.sh` (needs `l4unicode` built, through the build lock). Every
   file must be 0 failures; a change to `L4Factoidal/Unicode/` that adds a failure is a regression.
2. **WPT directories**, from the per-directory table of the newest valid full run ([`wpt-runs`](../wpt-runs/SKILL.md)
   section 4): `css/css-text/`, `css/css-writing-modes/`, `css/css-fonts/`, `css/css-text-decor/`,
   `css/css-ruby/`, `i18n/`, and `svg/text/`. Compare subtests passed with Chrome's per directory. For a branch,
   a cloud check of just those prefixes (`names=/css/css-text/,/css/css-writing-modes/,...`, section 8).
3. **Shaping differential**: `check-lean-shaper.py` with the vendored script fonts and per-script strings; any
   record that differs from HarfBuzz (glyph ids, advances, offsets, clusters) is a failure, and a Lean
   refusal is counted apart.
4. **Engine comparison on our own cases** (section 3).

## 3. Our own refined cases

WPT tests of text often test many things at once, depend on fonts we do not have (Ahem aside), or test only
that something does not crash. Where a suite is too coarse to say which part of a script is wrong, write
smaller tests ourselves.

**Shape of a case.** One small original HTML page per script and feature, under
`labs/demos/foafnaut/fixtures/i18n/<script>-<feature>.html`, with `manifest.json` beside them (the same layout
as `fixtures/emoji-reference/`). Each page:

- sets its fonts by `@font-face` from `third_party/fonts/` (relative URL), so every engine draws with the same
  font; a case that falls back to a system font compares nothing;
- uses a fixed viewport (400 x 300 CSS px at device pixel ratio 1), fixed font size, no animation, no script
  unless the feature is scripted;
- tests one thing: one joining context, one bidi run order, one break opportunity, one orientation;
- marks each run it wants measured with a `span` and an `id`, so glyph positions can be read by id.

**Starting matrix** (add rows, don't remove them):

| Script | Features |
|---|---|
| Arabic | joining forms (isolated, initial, medial, final) incl. lam-alef; tashkil placement; bidi with Latin and digits; mirrored brackets |
| Hebrew | bidi with numbers and punctuation; niqqud placement |
| Devanagari, Bengali, Tamil | conjuncts, reph, pre-base matras, line breaks only at grapheme cluster boundaries |
| Thai | line breaking without spaces (dictionary breaks), tone mark stacking |
| CJK (JP, SC, KR) | line breaking and kinsoku (no break before small kana or closing punctuation), `writing-mode: vertical-rl` with upright and rotated runs, `text-combine-upright` |
| Mongolian | vertical writing, joining (needs a vendored font first) |
| Emoji | ZWJ sequences, skin tones, flags, keycaps, VS15/VS16; no break inside a sequence |
| Mixed | Latin + Arabic + digits in one paragraph; CJK + Latin spacing; an emoji inside RTL text; a line break across a script change |

**Text and licences.** Test text is either constructed (code-point sequences, word lists made for the test)
or taken from a source whose licence allows it, recorded per case in the manifest (`text_source`,
`text_licence`). Don't copy text from a web page. Fonts come only from `third_party/fonts/`; a new font is
vendored there first with its licence and provenance (see `third_party/fonts/README.md`), OFL or CC0 by
preference.

**References.** For each case, `i18n_reference.py` (to be written with the first case, on the pattern of
`emoji_reference.py`) loads the page in headless Chrome, and Firefox where available, and stores per engine:

- the box of every marked span and of every character in it (`Range.getClientRects()` per grapheme), as JSON;
- a PNG of the page area, Base64 in the manifest or a file beside it with its SHA-256;
- the browser name and version, the date and the font hashes.

Firefox is not installed on the shared Mac (2026-11-16): capture Firefox references on a CI runner, or ask
before installing it. A case with Chrome only is marked `references: ["chrome"]`.

**Comparison** (`i18n_layout_test.ts`, a deno test in `labs/demos/foafnaut`): the engine renders each case
(`run_html.ts --offscreen --offscreen-size 400x300@1 --shot`) and reports its boxes; the test checks

- the order and line of every character box (bidi order and break positions must match exactly);
- box positions within 1 px of the reference, and widths within 2%;
- pixels: mean difference and the share of pixels differing by more than 32 in a channel, bounded as in
  `emoji_pixels_test.ts`.

A case passes when it matches every reference engine, is **contested** when the reference engines disagree
with each other beyond tolerance (it then passes if it matches either, and the manifest says so), and fails
otherwise.

**Adding a case**: write the page; add its manifest entry (script, feature, what is tested in one sentence,
text source and licence, fonts); run the reference script for that case only; run the test; commit the page,
the manifest entry and the references together. When the engine fails a new case, commit it with
`expected: "fail"` and a link to the plan issue, so the failure is counted, not hidden.

## 4. Running

- Locally: `tests/unicode/run.sh`; `check-lean-shaper.py`; `deno test ... labs/demos/foafnaut/i18n_layout_test.ts`
  (needs the native engine, `.build/web-render/web-render-native`); WPT directories per
  [`wpt-runs`](../wpt-runs/SKILL.md). Timing runs and WPT runs follow the machine rules in the agent brief.
- In CI: the i18n cases join `labs/demos/foafnaut/test.sh` once the runner exists, so every engine change runs
  them; the WPT directories run in every full WPT run; the real-page survey runs on each release.

## 5. Reporting

- Per script and feature: cases passed, contested, failed; for failures, the largest box offset and which
  characters are out of order or on the wrong line.
- Next to the WPT numbers for the text directories, never folded into the WPT score: our cases are reported
  separately and say so.
- Unicode conformance: pass and fail counts per file, with the Unicode version.
- Shaping differential: records identical, differing, refused, per font.
- In a hand-back: before and after counts for every check above that the change could affect, plus a
  screenshot for orientation only.
