# Size and repeat the first raster background layer

Build on the landed raster fetch, decode and paint path from 89ab7d93144e. The new
computed properties use the CSS declaration cascade, including resets through the
background shorthand. The painter resolves lengths and percentages against the
padding box, supports cover, contain and intrinsic proportions, and clips the
scaled tiles to the border box. Repeat and no-repeat are supported on each axis.
The existing 4,096-tile cap applies, and an opaque 1×1 image only uses the whole-box
colour shortcut if it tiles on both axes.

The four focused Lean geometry guards compiled locally with the cached CSS length
interface. Whole-engine compilation and pinned pixel comparisons are pending.
Author position, origin, and clip values, repeat space and round, and multiple
layers need follow-up. The existing main loader and both browser hosts are reused.

[CSS Backgrounds and Borders §2](https://www.w3.org/TR/css-backgrounds-3/#backgrounds)
