# Logical CSS anchor edges

The physical inset axis determines which logical edge is used. The containing block supplies its writing mode for start, end and percentage values. The positioned element supplies its own writing mode for self-start and self-end. Anchor insets now reuse the same axis-direction convention as ordinary absolute self-alignment.

The pinned `anchor-position-writing-modes-002.html` exercises this change. In the preceding full run it passed 32 of 48 cases. The separate 001 fixture tests the physical positions of anchors in vertical normal flow and needs that layout algorithm.

[CSS Anchor Positioning Level 1 §3.2](https://drafts.csswg.org/css-anchor-position-1/#anchor-pos)
