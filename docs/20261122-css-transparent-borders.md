# Transparent CSS borders

A border can occupy space even when its paint is transparent. The computed border colour holds current colour, transparent or an explicit opaque colour. Layout still uses the existing effective widths, painting skips transparent borders, and changing border visibility invalidates colour-only repaint.

The regression fixture places two visible children at offsets reserved by transparent borders set through the shorthand and longhand. The Lean guards exercise both declarations. Native compilation and a paired visual run provide separate evidence.

[CSS Backgrounds and Borders Level 3 §4](https://www.w3.org/TR/css-backgrounds-3/#borders)
