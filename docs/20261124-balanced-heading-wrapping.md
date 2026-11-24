# Balanced heading wrapping

The GOV.UK homepage hero specifies `text-wrap: balance`. The existing cascade
reports that value but the layout keeps the same greedy breaks as ordinary text.

Use the existing font measurements and wrapping inputs to choose a breaking
width for an eligible inline run. Keep the original number of lines and require
a reduction in the variance of their widths. The chosen width only limits the
soft wrap decision. Placement, alignment, and the block's width still use its
ordinary geometry. The default path remains the existing greedy algorithm.

The search is bounded and applies to short horizontal text runs with uniform
line boxes. The ordinary path still handles floats, bidirectional items,
indentation, preserved breaks, and nonzero inline edges. The change does not
extend ordinary `text-wrap-mode` behavior. It only suppresses balancing when
the computed mode is nowrap.

Issue #957 has the paired real-page screenshots and the reduced Chrome and
Foafnaut measurements.
