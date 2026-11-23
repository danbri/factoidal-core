# Apply relative insets to inline fragments

The pinned CSS Break fixture relpos-inline-hit-testing revealed that a
fragmented span still received hits at its anonymous line's pre-offset
position. The block renderer already applies relative offsets, while the
inline renderer emitted geometry from the unshifted wrapping extents.

Resolve the physical offsets in the containing inline formatting context.
Use the paint source's DOM ancestors so a line's bidi reordering does not
change which positioning applies to its pieces. Translate glyphs, decoration
and hit boxes together, while leaving line widths, line breaks and baselines
in flow coordinates. Ordinary horizontal block flow and the inline-only
multicolumn path use the same calculation. Definite sequential columns supply
a block-axis percentage basis. Balanced columns lack that basis at this stage.

The exact extracted offset functions passed four Lean 4.33.1 guards with
minimal host types. The checked start-edge theorem uses `propext`, `Classical.choice` and `Quot.sound`. The
full engine and pinned CSS Break, Multicol and positioning checks will test
the integrated paint, geometry and hit behaviour.

[CSS Positioned Layout, relative insets](https://drafts.csswg.org/css-position-3/#relpos-insets) · [CSS Fragmentation, transforms and positioning](https://drafts.csswg.org/css-break-3/#transforms)
