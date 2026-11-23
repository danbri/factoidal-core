# Static images in object and embed

The document image inventory now recognizes image resources in HTML object and embed elements. A supported explicit media type takes precedence. When the type is absent, typed image data URLs and supported filename extensions identify the resources. After successful decoding, both elements reuse the ordinary replaced-image layout and paint path. An object with missing or failed image bytes continues to lay out its fallback content.

The first supported set is PNG, JPEG, GIF and static SVG. SVG uses the existing image-only renderer. Child documents, plugins, and the object and embed loading-event model are outside this patch. The Lean guards cover URL discovery, decoded images and fallback. Pinned pixel tests provide independent comparisons of the normal browser path.

[HTML Standard on object and embed](https://html.spec.whatwg.org/multipage/iframe-embed-object.html)
