# Outside list markers beside floats

The three CSS2 list-style applicability reftests use an empty list item beside a float and compare it with a reference item whose inline start is shifted by a matching margin. The document engine used the box's inline start even when the float shifted the first line. Use the existing line-band placement for the marker and keep the principal box unchanged. The fixtures cover an empty item beside an inline-start float and an inline-end float.

CSS Lists 3 leaves exact outside marker positioning beside floats undefined. This behavior follows the reftest convention and the browser's existing float-aware first line. The image case follows the same marker placement; rendering the authored marker image is a separate behavior to check.

[CSS Lists 3 marker positioning](https://www.w3.org/TR/css-lists-3/#list-style-position-property) · [Regression issue](https://github.com/danbri/factoidal-core/issues/982)
