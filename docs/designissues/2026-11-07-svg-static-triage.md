# Static W3C SVG Tiny 1.2 files that stay in MISMATCH

Owner, 2026-11-07, verbatim: "let's get svg drawing basics nailed down". Candidate key
result, not yet approved: all static W3C SVG Tiny 1.2 files at CLOSE or better.

Data: `tests/browser-wpt/svg-tiny-pixels-20261107d.json`, first frame, real WebGPU pixels
against the W3C PNGs, our bands, unchanged.

"Static" here is a file with no `script`, `handler`, `listener`, `animate`,
`animateColor`, `animateMotion`, `animateTransform`, `set`, `animation`, `video` or `audio`
line in the drop log of `svg-tiny-pixels-20261107c.json`, in a text or not. This gives
209 files; the 213 of the brief could not be reproduced with these rules.

| | close | mismatch | refused | not read |
|---|---|---|---|---|
| all 496, before (`20261107c`) | 118 | 375 | 2 | 1 |
| all 496, after (`20261107d`) | 157 | 336 | 2 | 1 |
| static 209, before | 102 | 104 | 2 | 1 |
| static 209, after | 131 | 75 | 2 | 1 |

No file moved from CLOSE to a lower band. GPU readback agrees with the Lean probes on 493
of 493 drawn files.

So the candidate key result is not met. Most of what stays is classes R1 to R4 below, and
no engine fix moves them unless the engine copies the reference, which the brief forbids.
The key result needs another definition for such files, and that is for the owner.

## Classes

**R1, reference difference: strokes and glyph edges on the pixel grid.** Every element is
present and at the right place, and the pixels that differ are edge pixels. Named pixels:
in `coords-coord-01-t.svg` and `shapes-line-01-t.svg`, the frame `x="1"` with stroke width
1. At row 200 the PNG has pixel 0 clear, pixel 1 black, pixel 2 clear; this engine has
grey 128 in pixels 0 and 1. §11.4 says a stroke is painted "along the outline of the given
graphics element", and it gives no rule that moves the outline to a pixel. The frame alone
is 1,672 pixels of the PNG's ink and two pixels of difference for each of them. Glyphs: the
text of `struct-use-recursion-01-t.svg` differs in 366 pixels here and in 99 when moved
down 0.25 pixel; `$Revision` of `struct-use-01-t.svg` needs 0.375 pixel. §10.4 gives `y` as
the absolute coordinate and §10.6.1 places the alignment point "exactly at the current text
position", so the PNG is off by a part of a pixel that changes from text to text. A scratch test
moved each actual image by the best shift of up to 0.5 pixel on each axis: only
`shapes-line-01-t.svg` (0.5 in x) and `paint-stroke-07-t.svg` (0.25 in y) then reach CLOSE,
so the PNGs have no single offset. The brief forbids a copy of the stroke snap.

**R2, reference difference: a system font.** `font-family` names `serif`, `monospace`,
Arial, `Haettenschweiler` and others, or the text has characters outside `SVGFreeSans`. The
PNG has a font of the machine that made it. CSS leaves generic families to the user agent.
The pixel run gives no such font: https://github.com/danbri/factoidal/issues/1263 is the
shortfall. In `struct-cond-204-t.svg` the PNG draws `$Revision` wider than the named font
does, and the row of Yes and No now agrees.

**R3, reference difference: `textArea` spacing.** Recorded in
`docs/designissues/2026-11-07-svg-images-text.md`: §10.11.7 gives another line spacing and
first baseline than the PNGs, and the brief forbids a copy.

**R4, the PNG is not the first frame of the static document.** `linking-*` PNGs show the
state after the link is followed, or a `view` fragment is applied; `struct-discard-206-t.svg`
and `media-video-216-t.svg` show later or video content.

**T, this engine states another true value.** `struct-cond-205-t.svg`: the PNG says Yes for
animation, media and scripting features that this engine does not have. It says No.
`paint-color-04-t.svg`: §11.14.1 leaves system paint to the user agent, and the PNG has a
blue where `AppWorkspace` is grey here.

**F, engine faults with an issue and an expected failure.**
F1258: https://github.com/danbri/factoidal/issues/1258 (`image` of an SVG document).
F1262: https://github.com/danbri/factoidal/issues/1262 (bold and italic of a font with one
face). F1265: https://github.com/danbri/factoidal/issues/1265 (inherited `currentColor`:
a decision for the owner). F1266: https://github.com/danbri/factoidal/issues/1266 (baseline
values of `font-face`). F1267: https://github.com/danbri/factoidal/issues/1267 (a stylesheet of an imported document).

**X, not drawn.** `intro-compat-201-t.svg` is not valid UTF-8 and the runner can not pass
it; `script-listener-201-t.svg` is not namespace well-formed; `struct-svg-204-t.svg` has
negative root dimensions, which is a refusal.

## Fixed in this work

Files that moved to CLOSE, by cause: sample rule of
`docs/designissues/2026-11-07-svg-strokes.md` (+26 in all 496); `use` of another document
(`struct-use-206`, `-207`, `-208`, `linking-refs-202`, `-203`, `-205`); `xml:space` and
`rotate` (`text-ws-02`, `text-text-07`); SVG fonts (`fonts-glyph-02`, `fonts-elem-03`);
`font-face-uri`, which also repaired the text of `paths-data-*`; `requiredFeatures`
(`struct-cond-03`). In `paths-data-12-t.svg` the digits "1.11" first looked like a reference
fault: the file names `SVGFreeSans-ISO-8859-1.svg`, whose kerning differs, and the fault was
here.

## Table

differentShare and inkRecall from `20261107d`, for the static files of that run that are
not CLOSE. Three files joined the static set because a `switch` now drops their media.

| File | differentShare | inkRecall | Class |
|---|---|---|---|
| coords-coord-01-t | 0.017963 | 0.6343 | R1 |
| fonts-desc-02-t | 0.021331 | 0.5283 | R2 |
| fonts-elem-06-t | 0.025995 | 0.6982 | R1 |
| fonts-glyph-03-t | 0.02136 | 0.5246 | R2 |
| fonts-glyph-04-t | 0.019971 | 0.6924 | R1 |
| fonts-kern-01-t | 0.085289 | 0.8141 | R1 |
| interact-zoom-01-t | 0.022112 | 0.5986 | R1 |
| interact-zoom-02-t | 0.022124 | 0.5994 | R1 |
| intro-compat-201-t | - | - | X |
| linking-a-03-t | 0.209109 | 0.0253 | R4 |
| linking-a-08-t | 0.077737 | 0.0256 | R4 |
| linking-frag-203-t | 0.43588 | 0.9505 | R4 |
| linking-frag-204-t | 0.250498 | 0.0007 | R4 |
| linking-uri-03-t | 0.14787 | 0.023 | R4 |
| media-video-216-t | 0.401001 | 0.0483 | R4 |
| paint-color-04-t | 0.361863 | 0.4972 | T |
| paint-color-05-t | 0.149751 | 0.075 | F1265 |
| paint-grad-17-t | 0.053461 | 0.4949 | R1 |
| paint-stroke-06-t | 0.067859 | 0.706 | R1 |
| paint-stroke-07-t | 0.050284 | 0.8215 | R1 |
| paths-data-02-t | 0.056846 | 0.8411 | R1 |
| paths-data-12-t | 0.033079 | 0.5524 | R1 |
| paths-data-13-t | 0.028814 | 0.6003 | R1 |
| paths-data-15-t | 0.033432 | 0.5803 | R1 |
| script-listener-201-t | - | - | X |
| shapes-intro-01-t | 0.057616 | 0.3632 | R1 |
| shapes-line-01-t | 0.042992 | 0.6654 | R1 |
| shapes-line-02-t | 0.052448 | 0.505 | R1 |
| shapes-polygon-02-t | 0.054456 | 0.6827 | R1 |
| shapes-polyline-02-t | 0.055451 | 0.6661 | R1 |
| struct-cond-02-t | 0.035984 | 0.4728 | R1 |
| struct-cond-204-t | 0.072095 | 0.4091 | R2 |
| struct-cond-205-t | 0.148183 | 0.3739 | T |
| struct-cond-209-t | 0.019589 | 0.6794 | R1 |
| struct-discard-206-t | 0.259612 | 0.0315 | R4 |
| struct-group-03-t | 0.094057 | 0.6227 | F1262 |
| struct-progressive-201-t | 0.134265 | 0.4443 | R1 |
| struct-progressive-202-t | 0.134601 | 0.4573 | R1 |
| struct-progressive-203-t | 0.106209 | 0.4911 | R1 |
| struct-progressive-204-t | 0.106128 | 0.4876 | R1 |
| struct-svg-203-t | 0.025428 | 0.4843 | R1 |
| struct-svg-204-t | - | - | X |
| struct-use-01-t | 0.043825 | 0.4821 | F1262 |
| struct-use-09-t | 0.047309 | 0.6217 | R1 |
| struct-use-201-t | 0.056811 | 0.4914 | R1 |
| struct-use-203-t | 0.050394 | 0.8651 | F1267 |
| struct-use-204-t | 0.050394 | 0.8651 | F1267 |
| struct-use-209-t | 0.085052 | 0.7819 | F1258 |
| struct-use-recursion-01-t | 0.030642 | 0.4202 | R1 |
| struct-use-recursion-02-t | 0.03724 | 0.3302 | R1 |
| struct-use-recursion-03-t | 0.034346 | 0.3506 | R1 |
| text-align-01-t | 0.057951 | 0.5768 | R2 |
| text-align-07-t | 0.037674 | 0.3499 | R2 |
| text-align-08-t | 0.170208 | 0.4401 | F1266 |
| text-align-201-t | 0.105266 | 0.2498 | R2 |
| text-align-202-t | 0.082657 | 0.4992 | R2 |
| text-area-201-t | 0.18044 | 0.3556 | R3 |
| text-area-202-t | 0.13467 | 0.3821 | R3 |
| text-area-205-t | 0.235666 | 0.2492 | R3 |
| text-area-206-t | 0.17691 | 0.2322 | R3 |
| text-area-207-t | 0.166765 | 0.2882 | R3 |
| text-area-208-t | 0.216632 | 0.1885 | R3 |
| text-area-209-t | 0.244907 | 0.2834 | R3 |
| text-area-210-t | 0.12048 | 0.2967 | R3 |
| text-area-220-t | 0.188177 | 0.2253 | R3 |
| text-area-221-t | 0.117564 | 0.278 | R3 |
| text-fonts-01-t | 0.085041 | 0.3338 | R2 |
| text-fonts-02-t | 0.0943 | 0.3229 | F1262 |
| text-fonts-04-t | 0.049683 | 0.5186 | R2 |
| text-fonts-202-t | 0.107135 | 0.3023 | R2 |
| text-intro-01-t | 0.098374 | 0.2616 | R2 |
| text-intro-04-t | 0.10055 | 0.2927 | R2 |
| text-intro-05-t | 0.058374 | 0.2059 | R2 |
| text-intro-06-t | 0.145231 | 0.2207 | R2 |
| text-intro-201-t | 0.060984 | 0.6115 | F1262 |
| text-text-08-t | 0.053628 | 0.7267 | R1 |
| text-text-09-t | 0.040064 | 0.3975 | R1 |
