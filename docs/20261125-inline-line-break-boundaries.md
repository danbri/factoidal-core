# Line breaks across inline elements

At 480 CSS pixels, the W3C homepage in Foafnaut put the comma after the
linked word “internationalization” at the start of the following line. A
reduced native fixture also put the three text fragments in WPT
`line-breaking-015` on separate lines.

CSS Text 3 §1.5 treats inline box boundaries and out-of-flow boxes as
transparent when determining text adjacency. Run the existing UAX 14
rules over uninterrupted text across sources and project the resulting
cuts back to the original styled fragments. Line fitting measures the
fragments that must travel together, and balancing uses the same groups.

The existing whitespace and atomic-box handling ends a text run. A
text run from a single source keeps its current segmentation. The
patch retains source positions for painting and selection as text
fragments cross style boundaries.

Local Lean 4.33.1 checks compiled the segmentation helper with the
production Unicode tables and a small model of the inline item types.
Integrated layout checks and comparisons with WPT and the W3C capture
are separate steps.

- [CSS Text 3 text processing](https://www.w3.org/TR/css-text-3/#text-processing)
- [Web Platform Test](https://github.com/web-platform-tests/wpt/blob/master/css/css-text/line-breaking/line-breaking-015.html)
- [W3C Mac replay](https://github.com/danbri/factoidal-builds/actions/runs/45518580148)
