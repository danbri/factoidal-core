# Outside CSS list marker placement

The four remaining regressions in [issue 982](https://github.com/danbri/factoidal-core/issues/982) differ only in the pixels used by their outside markers. The padding fixture keeps the same border edge and moves the content edge. The text fixtures express the same content through different indentation and spacing properties.

Anchor the outside marker to the border edge and use that area's available band beside a float. Lay out the marker with its own unindented line. Omit the generated separator from outside markers because the surrounding layout already supplies a gap. A single generated symbol has no inter-character spacing. Number labels use their inherited spacing.

The guards check marker and content locations independently. The WPT pixel comparisons check the four reported cases and the previously repaired outside-marker cases alongside floats. [CSS Lists §3](https://drafts.csswg.org/css-lists-3/#markers)
