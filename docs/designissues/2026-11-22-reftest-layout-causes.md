# Why Foafnaut fails CSS and SVG reftests: causes, counts and evidence (2026-11-22)

Owner, 2026-11-22, verbatim: "Please go deep on reftests for css and svg, and any wpt areas
for css and html that may be messing with our visual layout".

This record gives the causes of the reftests that Foafnaut fails, with the count of tests
that each cause touches, the evidence for each cause, and the method, so that the next
session can repeat the counts. Tracking issue: https://github.com/danbri/factoidal-core/issues/747.

## 1. Results

- CSS reftests (`wpt-reftest-css`), newest valid record, 2026-11-16, engine `0ccd896a`, WPT
  `fa649586`: 9,472 pass of 25,759 (36.77%). Chrome 22,658 (87.96%). 13,610 tests pass in
  Chrome and do not pass in Foafnaut. Run:
  https://github.com/danbri/factoidal-builds/actions/runs/43820777162.
- SVG reftests (`wpt-reftest-svg`), 2026-11-22, engine `e0666850`, WPT `4b26db89`: 328 pass of
  693 (47.33%); 296 pass in Chrome and not in Foafnaut. The count has been 328 on every run
  since 2026-11-16 07:40 (about 60 runs).
- The CSS reftests ran twice, both on 2026-11-16. `reftests.yml` runs `svg` only unless a
  person asks for `css` (input `suites`, default `'svg'`). So no CSS reftest number existed
  for the engine of the six days after 2026-11-16.
- CSS reftests, run for this record, 2026-11-22, engine `e0666850`, WPT `4b26db89`: 9,559
  pass of 25,813 (37.03%). Against 2026-11-16: 204 newly pass, 128 newly fail (css-break 24,
  css-multicol 22, css-backgrounds 11, css-fonts 8, css-images 8, CSS2 7). The WPT commit
  also changed, so this list mixes engine changes and test changes; section 1.1 separates
  the engine changes for the CSS2 directories at one WPT commit. Run:
  https://github.com/danbri/factoidal-builds/actions/runs/45028286099.
- Local runs on engine `e0666850` (release `build-e0666850902b-foafnaut-linux-x86_64`, WPT
  `fa649586`), section 6 gives the method:

  | Directory | Pass | Tests | 2026-11-16 CI |
  |---|---:|---:|---:|
  | css/CSS2/normal-flow | 419 | 792 | 416 |
  | css/CSS2/margin-padding-clear | 383 | 683 | 383 |
  | css/CSS2/positioning | 249 | 520 | 247 |
  | css/CSS2/text | 153 | 410 | 153 |
  | css/CSS2/borders | 148 | 506 | 148 |
  | css/CSS2/tables | 136 | 373 | 136 |
  | css/CSS2/selectors | 88 | 479 | 88 |
  | css/CSS2/floats-clear | 65 | 214 | 65 |
  | css/CSS2/linebox | 30 | 191 | 34 |
  | svg/ | 328 | 685 | 328 |

### 1.1 Regressions since 2026-11-16 that no run reported

At the same WPT commit, against the 2026-11-16 CI record (engine `0ccd896a`), engine
`e0666850` newly fails 4 tests and newly passes 5 in the directories above:

- `css/CSS2/linebox/inline-formatting-context-001.xht`: the space between two inline elements
  is drawn twice ("Filler Text  Filler Text"); white space no longer collapses across an
  inline element boundary.
- `css/CSS2/linebox/vertical-align-sub-001.xht` and `vertical-align-super-001.xht`:
  `vertical-align: sub` and `super` no longer move the text.
- `css/CSS2/linebox/iframe-in-block-in-inline.html`: the iframe is about 20 px lower.
- Newly passing: `normal-flow/block-replaced-height-004`, `-005`, `-007`;
  `positioning/absolute-replaced-height-004`, `-005`.

The rule of `skills/wpt-runs` section 10 calls more than 3 newly failing tests a drop. The
drop was not seen, because the CSS reftests did not run on any of the releases between.
The commit that caused it is not yet found (bisect over the releases of 2026-11-16 to
2026-11-22).

## 2. Two defects in the measurement

### 2.1 The "Partial page" note is drawn into the reftest pictures

When the engine skips something in liberal mode, `WebDocument.partialNote`
(`labs/demos/foafnaut/WebDocument.lean`, about line 2022) puts an `<a>` element with the text
"Partial page — see console" at the start of `body`. The reftest renderer loads pages in
liberal mode, so the note is part of the test picture. It is 34 px high and moves the whole
page down, so the test cannot match its reference, even when the skipped item has no effect
on the drawing.

- svg/: 92 of the 322 failing tests have the note in the test picture (local run).
- css/CSS2/normal-flow: 14 of 373.
- Example: `css/CSS2/normal-flow/inline-replaced-width-009.xht` gets the note only because the
  inline SVG has `baseProfile`, an attribute that SVG 2 removed and browsers ignore.

The same note moves the content of real pages in the window (gov.uk, BBC, MDN:
`docs/designissues/2026-11-14-real-pages.md`).

### 2.2 A pass can compare two empty pictures

`css/css-paint-api/`: 100 of 115 tests pass, where Firefox and Safari pass 1. The engine has no
`registerPaint` and no `CSS.paintWorklet`. In 93 of the 100 passes the test picture is fully
white: the test draws with `paint()`, which the engine ignores, and the reference draws with
`<canvas>`, which the reftest renderer draws as nothing (probe in section 4). The WPT rule
counts two equal pictures as a pass, so these are passes of the harness rule and not of the
feature. The CSS run has 424 passes where Chrome does not pass; the largest groups are
css-images (71), css-text (62) and css-grid (57). Those were not checked one by one.

## 3. CSS reftests: causes and counts

### 3.1 Method

A cause enters this list only after a probe page shows the defect on engine `e0666850`
(section 4). Then each of the 13,610 tests that Chrome passes and Foafnaut fails is matched
against the cause in its source (its `<style>`, `style` attributes and local linked sheets).
"Test, not reference" counts tests where the test uses the feature and its first reference
does not: the feature is then part of what the test draws differently. A test can have more
than one cause. 4,722 of the 13,610 (35%) have at least one cause of this list in the test and
not in the reference; with the border width cause of 3.2, about 5,377 (40%).

### 3.2 Confirmed causes

| Cause (measured by a probe) | Fail, uses it | Fail, test not reference | Pass, uses it |
|---|---:|---:|---:|
| Multi-column layout puts whole child boxes in columns; it never splits a line box or a block between columns (`Layout.lean`, comment "A child is never cut"). A paragraph in `column-count: 3` stays one column. | 1,869 | 1,494 | 461 |
| Vertical writing modes: "Block and inline layout are horizontal in this profile; flex containers read it for their axes" (`BoxPosition.lean`, line 25). | 1,443 | 912 | 255 |
| `background-image: url(...)` (PNG and SVG) is not drawn; only `linear-gradient()` is (`Style.lean` line 115). Issue https://github.com/danbri/factoidal-core/issues/704 (raster CSS background images). | 927 | 876 | 146 |
| `border-*-width` accepts `px` only. `in`, `cm`, `mm`, `pt`, `pc`, `em`, `ex`, `rem`, `vw`, `Q` give the initial 3 px (`Style.pixels`: "box edges require px in this CSS profile"). `width`, `margin`, `padding`, `left` accept every unit. | 846 | (655 not in other rows) | 106 |
| `::first-letter` and `::first-line` are not applied. | 535 | 495 | 59 |
| `background-size`, `-position`, `-repeat`, `-origin`, `-clip` are not applied. | 485 | 425 | 97 |
| Counters (`counter()` draws nothing) and quotes (`<q>` and `quotes` draw no marks). | 345 | 316 | 37 |
| `opacity` is not applied. | 359 | 233 | 46 |
| `letter-spacing`, `word-spacing`, `text-indent` are not applied. | 234 | 184 | 141 |
| `filter`, `backdrop-filter`, `mix-blend-mode` are not applied. | 203 | 149 | 134 |
| `<col>` and `<colgroup>` backgrounds are not drawn. | 194 | 144 | 11 |
| Generic families: `serif` and `monospace` draw with Noto Sans. | 759 | 121 | 549 |
| `<canvas>` draws nothing in the reftest renderer. | 126 | 99 | 44 |
| `outline` is not drawn. | 141 | 88 | 188 |
| `border-radius` is not applied. | 184 | 50 | 96 |
| `box-shadow` is not drawn. | 65 | 47 | 25 |
| `double`, `groove`, `ridge`, `inset`, `outset`, `dashed`, `dotted` borders draw as `solid`. | 203 | 40 | 163 |
| `radial-gradient()` and `conic-gradient()` are not drawn. | 45 | 31 | 25 |
| `text-shadow` is not drawn. | 35 | 11 | 14 |
| `list-style-image` is not drawn. | 11 | 7 | 25 |
| `font-variant: small-caps` is not applied. | 35 | 4 | 24 |

Code check: outside `getComputedStyle` (`ComputedGeneric.lean`) no layout or paint module reads
`border-radius`, `opacity`, `letter-spacing`, `text-indent`, `box-shadow`, `outline-width`,
`text-shadow`, `font-variant`, `counter-increment` or `background-size`. `Style.appliedName`
lists the properties that the style model applies; it refuses every other property and
gives no diagnostic. Of the 13,610 failing tests, 472 have any engine diagnostic, and all of
those are from the inline SVG reader. So 13,138 failures (97%) have no message that says what
was not applied.

### 3.3 Text metrics: the line box uses the metrics of the default font

Probe (section 4): a block `font: 20px/1 Ahem` with the WPT Ahem web font.

| font-size | Block rows | Glyph rows | Glyph offset |
|---|---|---|---:|
| 10px | 100..109 | 101..109 | 1 |
| 20px | 100..119 | 102..120 | 2 |
| 50px | 100..149 | 105..153 | 5 |
| 100px | 100..199 | 109..207 | 9 |

The glyph is 0.09 em too low and 1 px short. With Noto Sans metrics (ascent 1.069 em, descent
0.293 em) and `line-height: 1`, the baseline is at 0.888 em; Ahem's ascent is 0.8 em; the
difference is 0.088 em. This agrees with the measured offset to the pixel, so the inference is
that the line box takes the ascent and descent of the default font profile and not of the font
that draws the run (`Layout.lineLeading` takes one `FontProfile`). This is an inference from
the numbers; the code path was not traced.

Also measured:

- `line-height: normal` is 1.2 em for every font (`Style.lean` line 1272); Ahem gives 1.0 em.
- `line-height: 0`, `0px` and `-0ex` give `normal`: issue
  https://github.com/danbri/factoidal-core/issues/657 (accept zero values for line-height).

Many CSS tests use Ahem to draw exact squares (2,765 of the 13,610 failing tests use Ahem;
of the Chrome-passing tests that use Ahem, 82% fail here, against 60% of all Chrome-passing
tests). A 2 px offset fails such a test with no fuzzy
annotation. `css/CSS2/linebox` (30 of 191 pass) is the directory where this shows most.

### 3.4 Other causes seen in pictures, not yet counted

- Blocks inserted into an inline by script leave empty line boxes with borders
  (`css/CSS2/normal-flow/block-in-inline-insert-*`, 38 tests).
- Inline-block shrink-to-fit width is too large
  (`inline-block-non-replaced-width-003.xht`).
- Tables: collapsed borders with conflict resolution draw nothing
  (`tables/border-conflict-element-*`); `table-layout: fixed` column widths are wrong
  (`fixed-table-layout-003*`); `table-anonymous-objects-*` (74 tests).
- Floats: the top of a float after a line box is too low (`floats-clear/floats-030.xht`).
- `vw` resolves against 800 px for `padding`, `margin`, `font-size` and `line-height`, and
  against the real viewport for `width` and `left`. Reftests use 800 x 600, so the reftests
  do not see this; a window of another width does.
- Groups by test name in the uncounted 8,888 failures: `css3-counter-styles` 151,
  `table-anonymous-objects` 74, `svg-matrix` 69, `grid-gap-decorations` 68, `line-height` 64,
  `flex-gap-decorations` 64, `vertical-align` 51, `white-space-processing` 48, `floats` 47.

## 4. Probes

Each probe is a small page drawn by `tests/browser-wpt/reftest-render.ts` on the release's
engine library, as the reftest runner draws a page. Results on engine `e0666850`:

| Feature | Result |
|---|---|
| Ahem through `/fonts/ahem.css` or `@font-face` | drawn, offset as in 3.3 |
| `font-family: Ahem` with no web font | Noto Sans (8 failing tests use this; not a cause) |
| `background-image` PNG, SVG | nothing |
| `<canvas>` 2D `fillRect` | nothing |
| `<col>` background | nothing |
| `::first-letter` | ignored |
| `column-count: 3` on one paragraph | one column |
| `writing-mode: vertical-rl` | horizontal |
| `outline`, `box-shadow` | nothing |
| `border: double`, `groove`, `dashed`, `dotted` | solid |
| `border-radius`, `opacity`, `filter: blur()`, `text-shadow` | ignored |
| `letter-spacing`, `word-spacing`, `text-indent` | ignored |
| `counter()`, `quotes`, `<q>` | empty |
| `font-variant: small-caps`, `font-family: serif`, `monospace` | ignored, Noto Sans |
| `background-size`, `no-repeat` with a gradient; `radial-gradient()` | ignored; nothing |
| `transform: scale()` on an inline-block | ignored (rotate on a block works) |
| `position: fixed`, `overflow: hidden`, `z-index`, margin collapsing, `dir=rtl`, `white-space: pre`, `text-transform` | correct |

## 5. SVG reftests

Local run on engine `e0666850`, WPT `fa649586` (685 tests): 288 tests pass in Chrome and fail
here. 184 of the 322 failures have an engine diagnostic (the SVG reader names what it skipped);
110 of the 288 have neither a diagnostic nor a script error.

| Cause | Tests (runner clusters, `wpt-reftests.py clusters`) |
|---|---:|
| Scripted pages that never end `reftest-wait`: SMIL API (`pauseAnimations`, `beginElement`), image load events, `getTotalLength` | 33 |
| `svgView(...)` and media fragments (`#xywh=`) in `img` and CSS image URLs; the image is not drawn | 32 |
| Linked parameters | 22 |
| `foreignObject` (`x`, `y`, `width` refused) | 18 |
| `transform` on the outer `svg`, CSS `transform` on SVG elements | 17 |
| Masking, clipping, filters, blending | 17 |
| Text: `dominant-baseline` (`hanging`, `text-before-edge`, `text-after-edge`), `text-shadow`, `lang` glyph selection | 16 |
| CSS values in SVG: `calc()`, `var()`, strings | 15 |
| Markers (`marker-start` attribute, `orient`, `context-fill`) | 14 |
| External `<use>` references | 14 |
| SVG images and `data:` URLs ("data URI is not baseN") | 14 |
| Other | 107 |

Seen in pictures and not in a diagnostic: `vector-effect: non-scaling-stroke` (5 tests), an
empty `gradientTransform=""` and a removed `gradientTransform` are not the identity.

92 SVG failures have the "Partial page" note (2.1).

## 6. CSS and HTML testharness tests that measure layout

Full WPT run of 2026-11-22 (engine `e0666850`, WPT `4b26db89`,
https://github.com/danbri/factoidal-builds/actions/runs/45019596682). Subtests that Chrome
passes and Foafnaut does not, in the directories that read layout results
(`offsetWidth`, `getBoundingClientRect`, `check-layout-th.js`):

| Directory | Lost | Chrome | In files with no pass |
|---|---:|---:|---:|
| css/css-grid | 4,860 | 16,018 | about 3,401 |
| css/css-text | 1,626 | 5,863 | about 1,216 |
| html/rendering | 1,624 | 11,717 | about 879 |
| css/css-sizing | 1,605 | 6,743 | about 497 |
| css/cssom-view | 1,439 | 2,722 | about 488 |
| css/css-flexbox | 1,134 | 4,933 | about 649 |
| css/css-align | 1,020 | 5,473 | about 289 |
| css/css-overflow | 489 | 1,215 | about 228 |
| css/css-tables | 417 | 951 | about 95 |
| css/css-inline | 232 | 869 | about 65 |
| css/css-position | 230 | 1,605 | about 72 |

Of the 2,456 layout testharness files in these directories, 691 have no passing subtest. In
those files, compared with the files that pass some subtests: `grid-lanes` 84% have no pass,
`contain-intrinsic-size` 67%, `scroll*` APIs 60%, orthogonal flows 59%, `subgrid` 56%, vertical
writing modes 42%, multi-column 37% (base rate 28%). In `css/css-grid/alignment`, 107 files
have no pass and 76 of them use a vertical writing mode. So vertical writing modes and
multi-column fragmentation are the two causes that the reftests and the testharness tests
share. The CSSOM causes (interpolation, `CSS.supports`, serialization) are in
https://github.com/danbri/factoidal-core/issues/429.

## 7. Proposed order

By count of failing tests that Chrome passes, and by cost:

1. Stop drawing the "Partial page" note into the page (2.1): draw it outside the page or not
   in the reftest renderer. About 100 SVG and CSS tests; it also moves real pages.
2. Border widths in every length unit and `thin`, `medium`, `thick` (846 tests). One value
   parser.
3. Line box metrics from the font that draws the run, and `line-height: normal` from the font
   (all Ahem tests; `css/CSS2/linebox`). With https://github.com/danbri/factoidal-core/issues/657.
4. Background images and the background sub-properties (876 + 425): https://github.com/danbri/factoidal-core/issues/704.
5. Paint: `opacity`, `outline`, `box-shadow`, `border-radius`, border styles, `<col>`
   backgrounds, `<canvas>` in the CPU raster (about 700 tests).
6. Text: `letter-spacing`, `word-spacing`, `text-indent`, `::first-letter`, `::first-line`,
   counters and quotes (about 1,000 tests).
7. Multi-column fragmentation of line boxes and blocks (1,494), and vertical writing modes in
   block and inline layout (912). These are the largest, and they are layout algorithms, not
   value parsers.
8. A diagnostic for each property that the style model does not apply, so that the 97% of
   failures with no message get one (`Style.appliedName`).
9. Run `css` reftests on every release, as `svg` runs (`reftests.yml`, input `suites`).

## 7a. Done on 2026-11-22 (local measurements, Linux, WPT `fa649586`)

- Items 1 to 3 of section 7, commits `ff19ccd1`, `25539a26`, `0c8eeb99`: border widths in every
  unit; line boxes with the metrics of the text's own font; no note in the reftest pictures
  (`"partialNote": false`; the window and the Hub still show it). `css/CSS2/`: 2,583 to 3,254 of
  6,243 pass (676 newly pass, 5 newly fail). `svg/`: 328 to 327 of 685 (the note is gone from all
  92 pictures; none of those tests passes yet; two mismatch tests against a blank page passed
  only because of the note).
- Before that, commits `05a5f192` to `a11b4bce`: Liberation Mono for `monospace`; a quoted
  generic family name is a family name; the reftest renderer gives the serif and monospace
  faces as the window does.
- Open, found while measuring: `line-height: normal` is a fixed 1.2 em, where browsers use the
  font's ascent, descent and line gap. With per-font metrics, a line that mixes fonts can grow,
  and `css/CSS2/fonts/font-family-013`, `fonts-013` and `font-applies-to-017` fail. Coptic
  letters are not case-mapped (`css/CSS2/text/text-transform-bicameral-009`, `-010`).

## 8. How to repeat

- Records: branch `wpt-scores` of `danbri/factoidal-builds`: `runs.csv`,
  `runs/<run_id>/results.tsv(.gz)` (status, Chrome, Firefox, Safari, Edge, maxDifference,
  totalPixels, engine diagnostics in `skipped`).
- Engine: release `build-<sha12>-foafnaut-linux-x86_64` (`libweb-render.so`, needs only the C
  library); host modules from `build-<sha12>-foafnaut-web` (`docs/web/hub/html-webgpu/runtime/`
  copied to `labs/demos/foafnaut/.build/native-html/runtime/` and `.build/engines/`, as
  `reftests.yml` does); core checked out at the same commit.
- Manifest: `https://wpt.fyi/api/manifest?sha=<wpt commit>`; WPT sparse checkout of `css/`,
  `svg/`, `fonts/`, `images/`, `common/`, `resources/`, `html/`.
- Run a directory: `python3 tests/browser-wpt/wpt-reftests.py run --manifest M --wpt-root WPT
  --native-engine libweb-render.so --prefix css/CSS2/linebox/ --out OUT --jobs 4` (Deno 2.9.4).
  A 4-CPU machine draws about 10 pages a second; all of `css/` is 38,133 pages.
- A probe: write a page under the WPT root, serve the root with `python3 -m http.server`, and
  give `reftest-render.ts --list JOBS.jsonl --out DIR` one line
  `{"url":...,"width":400,"height":260,"file":"x.png"}`.
- Cause counts: match each test's source and its first reference's source against the
  feature, for the tests with `chrome` P and `status` not PASS in `results.tsv`.
