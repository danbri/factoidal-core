# Generic monospace font sizing

A plain pre or code element inherits the medium size keyword and uses the
generic monospace family. With a 13 px fixed-font default, ten characters in
Liberation Mono occupy about 78 px. The previous cascade had already resolved
the keyword to the 16 px proportional default, so the row occupied about 96 px.

Keep the size's basis through inheritance. Resolve a keyword from the fixed
table when the only family is the unquoted monospace keyword. When a relative
size crosses between fixed and proportional families, use the ratio of the
two default sizes. Explicit lengths such as pixels and rem fix the size.
Finish family selection before computing unitless line height and em-based
properties.

Lean 4.33.1 ran the extracted declaration and size resolution against the CSS
value parser. The guards cover keywords, two family changes, absolute lengths,
em, rem, percentages and both unitless and fixed line heights. The native CPU
pixel test replaces the expected-failure record and checks actual advances
for five cases.

References: [WebKit's strict font size table](https://fuchsia.googlesource.com/third_party/webkit/+/refs/heads/main/Source/WebCore/style/StyleFontSizeFunctions.cpp),
[Chromium's generic-family selection](https://chromium.googlesource.com/chromium/src/third_party/+/1459a260288a5a0eead07491beaf3c77005ad8c0/blink/renderer/platform/fonts/font_description.h).
