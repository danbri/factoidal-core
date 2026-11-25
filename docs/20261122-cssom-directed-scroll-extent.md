# CSSOM View directional scroll extents

The full Linux WPT run at `b9f6c92bd022` passed 310 of 600 subtests in `scrollWidthHeight-negative-margin-002.html`. The geometry query formerly extended every element to the right and bottom, even when its scroll origin was at another edge. This change computes reachable directions from the writing mode and direction while accounting for reversal of the flex main and cross axes. The existing extent fold still starts at the client size. The root viewport keeps its current geometry behavior.

The change covers the element size query. It does not implement scroll offsets, new layout modes, CSS Overflow's containing-block filtering, or overflow clipping propagation. The pinned negative-margin tests exercise flex, grid, and flow-root with multiple axes and overflow values. Compare exact before-and-after native engines and adjacent root read cases before attributing gains.

- [CSSOM View scrolling area](https://drafts.csswg.org/cssom-view/#scrolling-area)
- [CSS Overflow scroll origin](https://drafts.csswg.org/css-overflow-3/#scrolling)
- [Pinned full run](https://github.com/danbri/factoidal-builds/actions/runs/45051599967)
