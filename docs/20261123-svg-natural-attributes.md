# Preserve natural SVG dimensions under CSS auto sizing

The pinned SVG intrinsic-size harness exercises width and height attributes
under an author rule with CSS width and height set to auto. Cascading auto
previously removed any way to use the SVG's own absolute dimensions.

Read the SVG's natural lengths through the existing CSS tokenizer and
absolute unit conversion. Use those dimensions in the same calculation for
inline and block SVG. When both natural dimensions are positive, they
supply the intrinsic ratio. Otherwise a positive viewBox can supply it.
An author-specified pair of CSS dimensions still takes precedence. A zero
viewport dimension disables content drawing while keeping the outer layout
box and its borders.

Lean 4.33.1 checked the natural-length parser and non-negativity theorem
with the pinned production tokenizer and numeric modules. The guards
exercise case-insensitive absolute units, exponent notation, zero and
several rejected units and token forms. Native sizing comparisons and
rendering checks are independent of that proof.

[SVG sizing](https://svgwg.org/svg2-draft/coords.html#IntrinsicSizing) · [CSS Images default sizing](https://drafts.csswg.org/css-images-3/#default-sizing) · [CSSWG attribute issue](https://github.com/w3c/csswg-drafts/issues/14117)
