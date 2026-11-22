# Raster background positioning

The first raster layer now reads the computed horizontal and vertical offsets from the shared CSS property table. Tile placement uses the padding box minus the sized image as the percentage basis. The shorthand shares the two axis properties' place in the cascade and resets them when omitted from `background`.

The Lean guards exercise far-edge offsets and first-layer selection with a negative percentage basis. Pixel checks will compare both engines at the same WPT revision. This change covers the first raster layer in the existing padding-box position area. Additional layers, gradient placement, and custom positioning areas need separate coverage.

[CSS Backgrounds and Borders Level 3 §2.6](https://www.w3.org/TR/css-backgrounds-3/#background-position)
