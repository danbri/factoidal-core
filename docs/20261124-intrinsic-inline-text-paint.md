# Avoid building text paint while measuring intrinsic widths

The frozen W3C Flexbox specification is slow in the Mac browser. A sampled layout stack goes from Grid column contribution through intrinsic inline layout into bitmap glyph outline construction. The intrinsic caller reads only the extents of its line boxes. This patch builds the same word boxes while deferring glyph runs and paint to draws. Normal line rendering still constructs both in its original order.

The Lean statement covers exact equality of the word-box projection of the append operation for either paint setting. The whole-page layout and performance require separate comparison against the same frozen inputs. This patch does not change script startup.
