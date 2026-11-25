# Preserve inline SVG elements carrying category and icon metadata

The frozen BBC News homepage contains 31 SVG elements with unqualified category and icon attributes. The desktop replay reported 30 SVG skips at category. In isolated renders of those same nodes the reader reached a second unsupported attribute, icon, when category was absent. Removing both labels from the input allowed all 31 nodes through without an SVG diagnostic. The reader now recognizes both attributes as inert metadata on SVG viewport elements. The attributes remain in the DOM.

The Lean theorem states that either unqualified metadata attribute leaves validation of the remaining attributes unchanged. A reduced DOM test compares the rendered artifact with and without both labels. The captured artwork needs a separate replay against the candidate to verify pixels. BBC WebP photos require decoding support.

Related to [desktop acceptance](https://github.com/danbri/factoidal-core/issues/712).
