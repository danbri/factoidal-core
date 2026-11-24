# 2026-11-24 — Block descendants of nested inline-blocks

The BBC News secondary navigation puts two successive inline-block levels around
ordinary blocks. The line-only collector flattened the inner block boxes and dropped
the anchors' padding from the outer shrink-to-fit width.

Follow the existing block-layout path through chains of inline-block children when
one requires it. During intrinsic sizing, put the min-content and max-content
contributions of those children into their respective lines as atomic measurements.
The actual block-layout path then retains the descendant geometry and padding.

The regression fixtures cover an unpadded row, a padded row, and a narrow available
width that wraps between the inner items. The layout fix applies independently of
the archived BBC stylesheet. Issue #950 records the reduced browser comparison.
