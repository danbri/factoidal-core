# Decode percent-encoded inline image URLs

The native image store can decode SVG images but used to reject every `data:` URL without a base64 marker. The archived W3C site stylesheet uses percent-encoded SVGs for the select arrow and search-field icon. Pinned WPT cases also contain percent-encoded SVG images.

The image store now takes the URL body up to the fragment and uses the existing WHATWG byte decoder before checking for optional base64. CSS backgrounds, HTML images and embedded SVG images use this store. The format decoder and pixel budgets are shared with other image sources. No host request is needed for a `data:` image.

Eleven guards cover encoded and mixed text, UTF-8, malformed escapes, literal plus and comma, URL fragments, and both valid and invalid base64. Eight of those fail on the previous decoder. A separate renderer guard checks that a decoded SVG paints green inside its box and leaves the outside white.

[Fetch data URL processor](https://fetch.spec.whatwg.org/#data-url-processor) · [Pinned WPT example](https://github.com/web-platform-tests/wpt/blob/94e2796a2aa59a232e4e43e8a218ae967e9fac77/css/css-images/object-fit-fill-svg-with-natural-size-and-viewbox.html)
