# Preserve inline SVG that carries category metadata

The frozen BBC News homepage markup has 31 SVG elements with a plain category attribute, including logos, playback controls and arrows. The desktop replay rejected 30 SVGs for that attribute. The native reader now accepts the metadata on SVG viewport elements. The attribute remains in the caller's DOM and other attribute validation still runs.

The Lean theorem covers the validator with a category attribute prepended to any attribute list. The DOM-fragment guard compares the complete rendered artifact with and without the attribute. A desktop screenshot replay is needed to measure how much of the missing BBC artwork this restores. The page also requests WebP photos, which need independent decoder work.

Related to [desktop acceptance](https://github.com/danbri/factoidal-core/issues/712).
