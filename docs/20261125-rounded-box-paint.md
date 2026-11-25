# Rounded box paint

The W3C Flexbox spec uses a 140px circular white badge around a 120px image. The engine previously painted both as rectangles. CSS Backgrounds and Borders §4 defines the border-box percentage bases, common overlap scale, and clipping to the selected box edge.

This change carries physical corner radii into layout and uses the existing path painter for solid, gradient, and bitmap backgrounds and for bitmap replaced content. The existing rectangle clip bounds the path at the paint box and preserves the tile or fitted image extent. Border strokes, overflow descendants, and SVG replaced content still need curved geometry.

Lean 4.33.1 checked normalization bounds and stability when all sides fit, zero insets, square-corner elision, and the adjacent-square condition for asymmetric overrun in the geometry model. These results concern integer layout units and scene geometry. The integrated native build, Web Platform reftests, and archived W3C replay check the production path.

[CSS Backgrounds and Borders Level 3](https://www.w3.org/TR/css-backgrounds-3/#corners) · [Issue #973](https://github.com/danbri/factoidal-core/issues/973)
