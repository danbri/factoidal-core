# Paint transforms on inline-block boxes

The GOV.UK menu icon is an inline-block pseudo-element. Its border is painted
without the CSS transform because the inline framing path never calls the
fragment transform used by block layout.

Apply the transform about the inline-block's border-box origin, with the
fragment's existing paint, hit boxes and glyph positions moved together.
Keep its line width and baselines. Before transforming, record its laid-out
right edge separately from its painted boxes. Auto-sized inline ancestors
can then measure their contents without counting transform overflow as width.
Lines without transformed inline-blocks use their normal box extents.

Lean checks the preservation of the right edge and baselines. Layout guards
exercise translation, scale and an overflowing transform inside an
auto-sized inline-block.
