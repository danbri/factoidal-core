# Normal flow for definite vertical block containers

A vertical block container progresses along the physical x-axis. Its direction
sets the inline start, on the y-axis. Previously the block loop always stacked
its children on the y-axis. Anchors in the second column therefore supplied
wrong physical rectangles even when the anchor inset correctly named a
physical side.

For a vertical formatting root with definite dimensions and sized block
children, place the children with Logical.Frame and pass the resulting physical
border boxes to the ordinary child renderer. Collapse adjacent block margins
along the column axis. Place auto inline margins using the container's
direction. Keep out-of-flow positions for the existing absolute-placement step.
Vertical blocks do not collapse their own physical top or bottom margin with
their contents.

This pass covers independent sized blocks. Inline vertical text, floats,
zero-sized collapsing blocks, and intrinsic sizing in orthogonal contexts
need additional layout work.

Lean 4.33.1 compiled the real LogicalAxes and LayoutUnit modules and the
extracted placement code with warnings treated as errors. Three rectangle
guards and four two-block placement probes passed, including mixed positive
and negative block margins. These check the placement kernel. The native
browser-layout check uses the pinned CSS anchor and writing-modes suites.
