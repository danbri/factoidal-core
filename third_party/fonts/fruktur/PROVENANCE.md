# Fruktur

A blackletter (Fraktur) display font, used by the Foafnaut demonstration of web fonts
(`@font-face`). It is a page asset, not an engine fallback font: a page names it and the
browser loads it like any other web font.

| Item | Value |
|---|---|
| File | `Fruktur-Regular.ttf`, unchanged |
| Designers | Viktoriya Grabowska, Eben Sorkin |
| Version | 1.008 |
| Licence | SIL Open Font License 1.1 (`OFL.txt`); `FONTLOG.txt` goes with the font |
| Source | https://github.com/google/fonts/tree/a60a77e14f28abd4ef243a1b5dfc48df0cec5205/ofl/fruktur |
| Upstream | https://github.com/SorkinType/Fruktur (commit 0f8b79b91438420d4c158890cb28bcb1eef407a0) |
| Bytes | 211,180 |
| SHA-256 | `dcba901b5fe11c0b6c3e8d5eb1003339b2dd020e2fc3949014ed0d8ff87715e7` |

Coverage checked for the demonstration titles "Spın̈al Tap" and "Foafnaut": S p ı (U+0131)
i n a l T F o f u t, space, U+0308 COMBINING DIAERESIS, and ä ö ü precomposed are all in
the font, so both words draw from it alone; no glyph comes from a fallback font.

Tables: `glyf` outlines (2048 units per em, 809 glyphs), `GSUB`, `GPOS` with `kern`,
`mark`, `mkmk` and `cpsp`, `GDEF`, and the hinting program `fpgm` (ttfautohint 1.8.4),
which the engine's font policy does not run: the font is drawn without hinting. The
`mark` feature has a mark-to-base lookup whose marks hold U+0308 and whose bases hold
`n` and `dotlessi`, so "n̈" takes the font's own anchor placement.

Chosen over UnifrakturMaguntia (no U+0131), UnifrakturCook (no U+0131), Pirata One,
New Rocker and Germania One (no U+0308), and the variable Texturina and Grenze Gotisch
(the engine reads no variations; Fruktur is a static font with the same coverage).
